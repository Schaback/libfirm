/*
 * Author:      Daniel Grund, Sebastian Hack, Matthias Braun
 * Date:		29.09.2005
 * Copyright:   (c) Universitaet Karlsruhe
 * Licence:     This file protected by GPL -  GNU GENERAL PUBLIC LICENSE.
 */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <stdlib.h>

#include "pset.h"
#include "irnode_t.h"
#include "ircons_t.h"
#include "iredges_t.h"
#include "irprintf.h"
#include "ident_t.h"
#include "type_t.h"
#include "entity_t.h"
#include "debug.h"
#include "irgwalk.h"
#include "array.h"
#include "pdeq.h"
#include "unionfind.h"
#include "execfreq.h"

#include "belive_t.h"
#include "besched_t.h"
#include "bespill.h"
#include "belive_t.h"
#include "benode_t.h"
#include "bechordal_t.h"
#include "bejavacoal.h"

// only rematerialise when costs are less than REMAT_COST_LIMIT
// TODO determine a good value here...
#define REMAT_COST_LIMIT	20

typedef struct _reloader_t reloader_t;

struct _reloader_t {
	reloader_t *next;
	ir_node *reloader;
};

typedef struct _spill_info_t {
	/** the value that should get spilled */
	ir_node *spilled_node;
	/** list of places where the value should get reloaded */
	reloader_t *reloaders;

	/** the spill node, or a PhiM node */
	ir_node *spill;
	/** if we had the value of a phi spilled before but not the phi itself then
	 * this field contains the spill for the phi value */
	ir_node *old_spill;
} spill_info_t;

struct _spill_env_t {
	const arch_register_class_t *cls;
	const arch_env_t *arch_env;
	const be_chordal_env_t *chordal_env;
	struct obstack obst;
	set *spills;				/**< all spill_info_t's, which must be placed */
	pset *mem_phis;				/**< set of all special spilled phis. allocated and freed separately */

	DEBUG_ONLY(firm_dbg_module_t *dbg;)
};

/**
 * Compare two spill infos.
 */
static int cmp_spillinfo(const void *x, const void *y, size_t size) {
	const spill_info_t *xx = x;
	const spill_info_t *yy = y;
	return xx->spilled_node != yy->spilled_node;
}

/**
 * Returns spill info for a specific value (the value that is to be spilled)
 */
static spill_info_t *get_spillinfo(const spill_env_t *env, ir_node *value) {
	spill_info_t info, *res;
	int hash = HASH_PTR(value);

	info.spilled_node = value;
	res = set_find(env->spills, &info, sizeof(info), hash);

	if (res == NULL) {
		info.reloaders = NULL;
		info.spill = NULL;
		info.old_spill = NULL;
		res = set_insert(env->spills, &info, sizeof(info), hash);
	}

	return res;
}

DEBUG_ONLY(
/* Sets the debug module of a spill environment. */
void be_set_spill_env_dbg_module(spill_env_t *env, firm_dbg_module_t *dbg) {
	env->dbg = dbg;
}
)

/* Creates a new spill environment. */
spill_env_t *be_new_spill_env(const be_chordal_env_t *chordal_env) {
	spill_env_t *env	= xmalloc(sizeof(env[0]));
	env->spills			= new_set(cmp_spillinfo, 1024);
	env->cls			= chordal_env->cls;
	env->chordal_env	= chordal_env;
	env->arch_env       = env->chordal_env->birg->main_env->arch_env;
	env->mem_phis		= pset_new_ptr_default();
	obstack_init(&env->obst);
	return env;
}

/* Deletes a spill environment. */
void be_delete_spill_env(spill_env_t *env) {
	del_set(env->spills);
	del_pset(env->mem_phis);
	obstack_free(&env->obst, NULL);
	free(env);
}

/**
 *  ____  _                  ____      _                 _
 * |  _ \| | __ _  ___ ___  |  _ \ ___| | ___   __ _  __| |___
 * | |_) | |/ _` |/ __/ _ \ | |_) / _ \ |/ _ \ / _` |/ _` / __|
 * |  __/| | (_| | (_|  __/ |  _ <  __/ | (_) | (_| | (_| \__ \
 * |_|   |_|\__,_|\___\___| |_| \_\___|_|\___/ \__,_|\__,_|___/
 *
 */

void be_add_reload(spill_env_t *env, ir_node *to_spill, ir_node *before) {
	spill_info_t *info;
	reloader_t *rel;

	assert(sched_is_scheduled(before));
	assert(arch_irn_consider_in_reg_alloc(env->arch_env, env->cls, to_spill));

	info = get_spillinfo(env, to_spill);

	if(is_Phi(to_spill)) {
		int i, arity;
		// create spillinfos for the phi arguments
		for(i = 0, arity = get_irn_arity(to_spill); i < arity; ++i) {
			ir_node *arg = get_irn_n(to_spill, i);
			get_spillinfo(env, arg);
		}
	}

	rel           = obstack_alloc(&env->obst, sizeof(rel[0]));
	rel->reloader = before;
	rel->next     = info->reloaders;
	info->reloaders = rel;
}

void be_add_reload_on_edge(spill_env_t *env, ir_node *to_spill, ir_node *block, int pos) {
	ir_node *predblock, *last;

	/* simply add the reload to the beginning of the block if we only have 1 predecessor
	 * (we don't need to check for phis as there can't be any in a block with only 1 pred)
	 */
	if(get_Block_n_cfgpreds(block) == 1) {
		assert(!is_Phi(sched_first(block)));
		be_add_reload(env, to_spill, sched_first(block));
		return;
	}

	/* We have to reload the value in pred-block */
	predblock = get_Block_cfgpred_block(block, pos);
	last = sched_last(predblock);

	/* we might have projs and keepanys behind the jump... */
	while(is_Proj(last) || be_is_Keep(last)) {
		last = sched_prev(last);
		assert(!sched_is_end(last));
	}
	assert(is_cfop(last));

	// add the reload before the (cond-)jump
	be_add_reload(env, to_spill, last);
}

void be_spill_phi(spill_env_t *env, ir_node *node) {
	spill_info_t* spill;
	int i, arity;

	assert(is_Phi(node));

	pset_insert_ptr(env->mem_phis, node);

	// create spillinfos for the phi arguments
	spill = get_spillinfo(env, node);
	for(i = 0, arity = get_irn_arity(node); i < arity; ++i) {
		ir_node *arg = get_irn_n(node, i);
		get_spillinfo(env, arg);
	}

	// if we had a spill for the phi value before, then remove this spill from
	// schedule, as we will remove it in the insert spill/reload phase
	if(spill->spill != NULL && !is_Phi(spill->spill)) {
		//sched_remove(spill->spill);
		spill->old_spill = spill->spill;
		spill->spill = NULL;
	}
}

/*
 *   ____                _         ____        _ _ _
 *  / ___|_ __ ___  __ _| |_ ___  / ___| _ __ (_) | |___
 * | |   | '__/ _ \/ _` | __/ _ \ \___ \| '_ \| | | / __|
 * | |___| | |  __/ (_| | ||  __/  ___) | |_) | | | \__ \
 *  \____|_|  \___|\__,_|\__\___| |____/| .__/|_|_|_|___/
 *                                      |_|
 */

/**
 * Schedules a node after an instruction. (That is the place after all projs and phis
 * that are scheduled after the instruction)
 * This function also skips phi nodes at the beginning of a block
 */
static void sched_add_after_insn(ir_node *sched_after, ir_node *node) {
	ir_node *next = sched_next(sched_after);
	while(is_Proj(next) || is_Phi(next)) {
		next = sched_next(next);
	}
	assert(next != NULL);

	if(sched_is_end(next)) {
		sched_add_after(sched_last(get_nodes_block(sched_after)), node);
	} else {
		sched_add_before(next, node);
	}
}

/**
 * Creates a spill.
 *
 * @param senv      the spill environment
 * @param irn       the node that should be spilled
 * @param ctx_irn   an user of the spilled node
 *
 * @return a be_Spill node
 */
static void spill_irn(spill_env_t *env, spill_info_t *spillinfo) {
	ir_node *to_spill = spillinfo->spilled_node;

	DBG((env->dbg, LEVEL_1, "%+F\n", to_spill));

	/* Trying to spill an already spilled value, no need for a new spill
	 * node then, we can simply connect to the same one for this reload
	 *
	 * (although rematerialization code should handle most of these cases
	 * this can still happen when spilling Phis)
	 */
	if(be_is_Reload(to_spill)) {
		spillinfo->spill = get_irn_n(to_spill, be_pos_Reload_mem);
		return;
	}

	if (arch_irn_is(env->arch_env, to_spill, dont_spill)) {
		if (env->chordal_env->opts->vrfy_option == BE_CH_VRFY_WARN)
			ir_fprintf(stderr, "Verify warning: spilling 'dont_spill' node %+F\n", to_spill);
		else if (env->chordal_env->opts->vrfy_option == BE_CH_VRFY_ASSERT)
			assert(0 && "Attempt to spill a node marked 'dont_spill'");
	}

	spillinfo->spill = be_spill(env->arch_env, to_spill);
	sched_add_after_insn(to_spill, spillinfo->spill);
}

static void spill_node(spill_env_t *env, spill_info_t *spillinfo);

/**
 * If the first usage of a Phi result would be out of memory
 * there is no sense in allocating a register for it.
 * Thus we spill it and all its operands to the same spill slot.
 * Therefore the phi/dataB becomes a phi/Memory
 *
 * @param senv      the spill environment
 * @param phi       the Phi node that should be spilled
 * @param ctx_irn   an user of the spilled node
 */
static void spill_phi(spill_env_t *env, spill_info_t *spillinfo) {
	ir_node *phi = spillinfo->spilled_node;
	int i;
	int arity = get_irn_arity(phi);
	ir_node     *block    = get_nodes_block(phi);
	ir_node     **ins;

	assert(is_Phi(phi));

	/* build a new PhiM */
	ins = alloca(sizeof(ir_node*) * arity);
	for(i = 0; i < arity; ++i) {
		ins[i] = get_irg_bad(env->chordal_env->irg);
	}
	spillinfo->spill = new_r_Phi(env->chordal_env->irg, block, arity, ins, mode_M);

	for(i = 0; i < arity; ++i) {
		ir_node *arg = get_irn_n(phi, i);
		spill_info_t *arg_info = get_spillinfo(env, arg);

		spill_node(env, arg_info);

		set_irn_n(spillinfo->spill, i, arg_info->spill);
	}

	// rewire reloads from old_spill to phi
	if(spillinfo->old_spill != NULL) {
		const ir_edge_t *edge, *next;
		foreach_out_edge_safe(spillinfo->old_spill, edge, next) {
			ir_node* reload = get_edge_src_irn(edge);
			assert(be_is_Reload(reload) || is_Phi(reload));
			set_irn_n(reload, get_edge_src_pos(edge), spillinfo->spill);
		}
		spillinfo->old_spill = NULL;
	}
}

/**
 * Spill a node.
 *
 * @param senv      the spill environment
 * @param to_spill  the node that should be spilled
 */
static void spill_node(spill_env_t *env, spill_info_t *spillinfo) {
	ir_node *to_spill;

	// the node should be tagged for spilling already...
	if(spillinfo->spill != NULL)
		return;

	to_spill = spillinfo->spilled_node;
	if (is_Phi(to_spill) && pset_find_ptr(env->mem_phis, spillinfo->spilled_node)) {
		spill_phi(env, spillinfo);
	} else {
		spill_irn(env, spillinfo);
	}
}

/*
 *
 *  ____                      _            _       _ _
 * |  _ \ ___ _ __ ___   __ _| |_ ___ _ __(_) __ _| (_)_______
 * | |_) / _ \ '_ ` _ \ / _` | __/ _ \ '__| |/ _` | | |_  / _ \
 * |  _ <  __/ | | | | | (_| | ||  __/ |  | | (_| | | |/ /  __/
 * |_| \_\___|_| |_| |_|\__,_|\__\___|_|  |_|\__,_|_|_/___\___|
 *
 */

/**
 * Tests whether value @p arg is available before node @p reloader
 * @returns 1 if value is available, 0 otherwise
 */
static int is_value_available(spill_env_t *env, ir_node *arg, ir_node *reloader) {
	if(is_Unknown(arg) || arg == new_NoMem())
		return 1;

	if(be_is_Spill(arg))
		return 1;

	if(arg == get_irg_frame(env->chordal_env->irg))
		return 1;

 	/* the following test does not work while spilling,
	 * because the liveness info is not adapted yet to the effects of the
	 * additional spills/reloads.
	 *
	 * So we can only do this test for ignore registers (of our register class)
	 */
	if(arch_get_irn_reg_class(env->arch_env, arg, -1) == env->chordal_env->cls
	   && arch_irn_is(env->arch_env, arg, ignore)) {
		int i, arity;

		/* we want to remat before the insn reloader
		 * thus an arguments is alive if
		 *   - it interferes with the reloaders result
		 *   - or it is (last-) used by reloader itself
		 */
		if (values_interfere(env->chordal_env->lv, reloader, arg)) {
			return 1;
		}

		arity = get_irn_arity(reloader);
		for (i = 0; i < arity; ++i) {
			ir_node *rel_arg = get_irn_n(reloader, i);
			if (rel_arg == arg)
				return 1;
		}
	}

 	return 0;
}

/**
 * Checks whether the node can principally be rematerialized
 */
static int is_remat_node(spill_env_t *env, ir_node *node) {
	const arch_env_t *arch_env = env->arch_env;

	assert(!be_is_Spill(node));

	if(arch_irn_is(arch_env, node, rematerializable)) {
		return 1;
	}

	if(be_is_StackParam(node))
		return 1;

	return 0;
}

/**
 * Check if a node is rematerializable. This tests for the following conditions:
 *
 * - The node itself is rematerializable
 * - All arguments of the node are available or also rematerialisable
 * - The costs for the rematerialisation operation is less or equal a limit
 *
 * Returns the costs needed for rematerialisation or something
 * > REMAT_COST_LIMIT if remat is not possible.
 */
static int check_remat_conditions_costs(spill_env_t *env, ir_node *spilled, ir_node *reloader, int parentcosts) {
	int i, arity;
	int argremats;
	int costs = 0;

	if(!is_remat_node(env, spilled))
		return REMAT_COST_LIMIT;

	if(be_is_Reload(spilled)) {
		costs += 2;
	} else {
		costs += arch_get_op_estimated_cost(env->arch_env, spilled);
	}
	if(parentcosts + costs >= REMAT_COST_LIMIT) {
		return REMAT_COST_LIMIT;
	}

	argremats = 0;
	for(i = 0, arity = get_irn_arity(spilled); i < arity; ++i) {
		ir_node *arg = get_irn_n(spilled, i);

		if(is_value_available(env, arg, reloader))
			continue;

		// we have to rematerialize the argument as well...
		if(argremats >= 1) {
			/* we only support rematerializing 1 argument at the moment,
			 * so that we don't have to care about register pressure
			 */
			return REMAT_COST_LIMIT;
		}
		argremats++;

		costs += check_remat_conditions_costs(env, arg, reloader, parentcosts + costs);
		if(parentcosts + costs >= REMAT_COST_LIMIT)
			return REMAT_COST_LIMIT;
	}

	return costs;
}

static int check_remat_conditions(spill_env_t *env, ir_node *spilled, ir_node *reloader) {
	int costs = check_remat_conditions_costs(env, spilled, reloader, 1);

	return costs < REMAT_COST_LIMIT;
}

/**
 * Re-materialize a node.
 *
 * @param senv      the spill environment
 * @param spilled   the node that was spilled
 * @param reloader  a irn that requires a reload
 */
static ir_node *do_remat(spill_env_t *env, ir_node *spilled, ir_node *reloader) {
	int i, arity;
	ir_node *res;
	ir_node *bl = get_nodes_block(reloader);
	ir_node **ins;

	ins = alloca(get_irn_arity(spilled) * sizeof(ins[0]));
	for(i = 0, arity = get_irn_arity(spilled); i < arity; ++i) {
		ir_node *arg = get_irn_n(spilled, i);

		if(is_value_available(env, arg, reloader)) {
			ins[i] = arg;
		} else {
			ins[i] = do_remat(env, arg, reloader);
		}
	}

	/* create a copy of the node */
	res = new_ir_node(get_irn_dbg_info(spilled), env->chordal_env->irg, bl,
		get_irn_op(spilled),
		get_irn_mode(spilled),
		get_irn_arity(spilled),
		ins);
	copy_node_attr(spilled, res);

	DBG((env->dbg, LEVEL_1, "Insert remat %+F before reloader %+F\n", res, reloader));

	/* insert in schedule */
	assert(!is_Block(reloader));
	sched_add_before(reloader, res);

	return res;
}

/*
 *  ___                     _     ____      _                 _
 * |_ _|_ __  ___  ___ _ __| |_  |  _ \ ___| | ___   __ _  __| |___
 *  | || '_ \/ __|/ _ \ '__| __| | |_) / _ \ |/ _ \ / _` |/ _` / __|
 *  | || | | \__ \  __/ |  | |_  |  _ <  __/ | (_) | (_| | (_| \__ \
 * |___|_| |_|___/\___|_|   \__| |_| \_\___|_|\___/ \__,_|\__,_|___/
 *
 */

void be_insert_spills_reloads(spill_env_t *env) {
	const arch_env_t *arch_env = env->arch_env;
	spill_info_t *si;

	/* process each spilled node */
	DBG((env->dbg, LEVEL_1, "Insert spills and reloads:\n"));
	for(si = set_first(env->spills); si; si = set_next(env->spills)) {
		reloader_t *rld;
		ir_mode *mode = get_irn_mode(si->spilled_node);
		pset *values = pset_new_ptr(16);

		/* go through all reloads for this spill */
		for(rld = si->reloaders; rld; rld = rld->next) {
			ir_node *new_val;

			if (check_remat_conditions(env, si->spilled_node, rld->reloader)) {
				new_val = do_remat(env, si->spilled_node, rld->reloader);
			} else {
				/* make sure we have a spill */
				spill_node(env, si);

				/* do a reload */
				new_val = be_reload(arch_env, env->cls, rld->reloader, mode, si->spill);
			}

			DBG((env->dbg, LEVEL_1, " %+F of %+F before %+F\n", new_val, si->spilled_node, rld->reloader));
			pset_insert_ptr(values, new_val);
		}

		if(pset_count(values) > 0) {
			/* introduce copies, rewire the uses */
			pset_insert_ptr(values, si->spilled_node);
			be_ssa_constr_set_ignore(env->chordal_env->dom_front, env->chordal_env->lv, values, env->mem_phis);
		}

		del_pset(values);

		si->reloaders = NULL;
	}

	be_remove_dead_nodes_from_schedule(env->chordal_env->irg);
	be_liveness_recompute(env->chordal_env->lv);
}
