/*
 * This file is part of libFirm.
 * Copyright (C) 2019 University of Karlsruhe.
 */

/**
 * @file
 * @brief       Sparc-specific node schedueling.
 * @author      Philipp Schaback
 * @date        22.10.19
 */
#include "be_types.h"
#include "bearch.h"
#include "belistsched.h"
#include "bemodule.h"
#include "debug.h"
#include "besched.h"
#include "firm_types.h"
#include "gen_sparc_regalloc_if.h"
#include "irdom.h"
#include "irgwalk.h"
#include "irnode.h"
#include "irnode_t.h"
#include "irnodeset.h"
#include "irouts_t.h"
#include "sparc_new_nodes.h"


#define GRN "\x1B[32m"
#define RED "\x1B[31m"
#define YEL "\x1B[33m"
#define BLU "\x1B[34m"
#define MAG "\x1B[35m"
#define CYN "\x1B[36m"
#define RST "\033[0m"

#define SIZE_CHECK true

DEBUG_ONLY(static firm_dbg_module_t *dbg = NULL;)
static ir_node* last_load = NULL;
static ir_node* last_muldiv = NULL;

typedef struct choice {
	ir_node* node;
	int score;
} choice;

typedef struct block_meta {
	ir_nodeset_t branch_candidates;
	ir_node* last_conditional;
	int sched_nodes;
	int total_nodes;
} block_meta;

static char score_load(ir_node* node) {
	if (is_sparc_Ld(node))
		return 3;
	if (last_load == NULL)
		return 0;
	foreach_irn_in(node, i, pred) {
		if (i == 0 && is_sparc_St(node))
			continue; // Only check adress calc. registers
		if (pred == last_load) {
			DB((dbg, LEVEL_1, GRN "\tLoad dependency found at %ld\n" RST, 
							node->node_nr));
			DB((dbg, LEVEL_1, GRN "\t...without Proj\n" RST));
			return -3;
		}
		if (!is_Proj(pred))
			continue;
		foreach_irn_in(pred, j, pred2) {
			if (pred2 == last_load) {
				DB((dbg, LEVEL_1, GRN "\tLoad dependency found at %ld\n" RST, 
							node->node_nr));
				return -3;
			}
		}
	}
	return 0;
}
/*
static bool score_branch(ir_node* node) {
	if (node == last_icci)	
		DB((dbg, LEVEL_1, BLU "\tBranch predecessor found: %ld\n" RST, 
				node->node_nr));
	return (node == last_icci) ? 1 : 0;
}
*/
inline static bool _is_MulDiv(const ir_node* node) {
	return is_sparc_SMul(node)  || is_sparc_SMulCCZero(node) 
		|| is_sparc_SMulh(node) || is_sparc_UMulh(node) 
		|| is_sparc_SDiv(node)  || is_sparc_UDiv(node);
}

static char score_muldiv(ir_node* node) {
	if (_is_MulDiv(node))
		return 3;
	if (last_muldiv == NULL)
		return 0;
	DB((dbg, LEVEL_1, BLU "\tChecking Mul/Div\n" RST)); 
	foreach_irn_in(node, i, pred) {
		if (pred == last_muldiv) {
			if (i == 0 && is_sparc_St(node))
				continue; // Only check adress calc. registers
			DB((dbg, LEVEL_1, YEL "\tMul/Div dependency found at %ld\n" RST, 
							node->node_nr));
			return -3;
		}
	}
	return 0;
}

static char score_icc(ir_node* node) {
	be_foreach_out(node, o) {
		const arch_register_req_t *req = arch_get_irn_register_req_out(node, o);
		if (req->cls->index == CLASS_sparc_flags) {
			DB((dbg, LEVEL_2, YEL "flag-mod instr found: %lu\n" RST, 
						node->node_nr));
			return 2;
		}
	}
	return 0;
}

#define DUMP_NODES(x) \
	DB((dbg, LEVEL_1, "[")); \
	foreach_ir_nodeset(x, __irn, __iter) \
		DB((dbg, LEVEL_1, "%lu,", __irn->node_nr)); \
	DB((dbg, LEVEL_1, "]\n"));

static ir_node *sparc_select(ir_nodeset_t *ready_set, block_meta* meta)
{
	int n = ir_nodeset_size(ready_set);
	DB((dbg, LEVEL_1, "\tready_set contains %i node(s): ", n));
	DUMP_NODES(ready_set);

	choice best_choice;
	best_choice.node  = ir_nodeset_first(ready_set);
	best_choice.score = -100;

	if (SIZE_CHECK && n == 1) { 
		// Branches are the only option most of the time (always?)
		// No schedueling betweeen blocks...
		DB((dbg, LEVEL_1, "\tOnly one node found\n"));
	} else {
		int num_nodes = ir_nodeset_size(&meta->branch_candidates) + 2;
		if (meta->last_conditional != NULL 
				&& ir_nodeset_contains(ready_set, meta->last_conditional) 
				&& meta->total_nodes - meta->sched_nodes <= num_nodes) {
			if (meta->total_nodes - meta->sched_nodes == num_nodes) {
				assert(ir_nodeset_contains(ready_set, meta->last_conditional));
				return meta->last_conditional;
			} else {
				ir_node* node = ir_nodeset_first(&meta->branch_candidates);
				ir_nodeset_remove(&meta->branch_candidates, node);
				assert(ir_nodeset_contains(ready_set, node));
				return node;
			}
		}
		foreach_ir_nodeset(ready_set, irn, iter) {
			if (ir_nodeset_contains(&meta->branch_candidates, irn))
				continue;
			if (meta->last_conditional == irn)
				continue;
			int current_score = 0;
			current_score += score_load(irn);
			current_score += score_icc(irn);
			current_score += score_muldiv(irn);
			DB((dbg, LEVEL_1, "\tnode %ld scored %i ", irn->node_nr, current_score));
			if (current_score > best_choice.score) {
				DB((dbg, LEVEL_1, "(current best)\n"));
				best_choice.node = irn;
				best_choice.score = current_score;
			} else {
				DB((dbg, LEVEL_1, "\n"));
			}
		}
	}
	last_load     = is_sparc_Ld(best_choice.node) ? best_choice.node : NULL;
	last_muldiv   = _is_MulDiv( best_choice.node) ? best_choice.node : NULL;
	DB((dbg, LEVEL_1, "\tselected node %ld\n", best_choice.node->node_nr));
	return best_choice.node;
}

// DFS upwards from irn to end of block
static void dfs_from(ir_node* irn) {
	if (irn_visited_else_mark(irn))
		return;
	if (is_Proj(irn)) {
		dfs_from(get_Proj_pred(irn));
	} else {
		ir_node* current_block = get_nodes_block(irn);
		foreach_irn_in(irn, i, pred) {
			if (get_nodes_block(pred) == current_block) {
				dfs_from(pred);
			} else {
				DB((dbg, LEVEL_1, RED "edge node found %+F\n" RST, pred));
			}
		}
	}
}

static inline bool is_end_node_for_block(ir_node* node) {
	ir_node* block = get_nodes_block(node);
	foreach_irn_out(node, i, succ) {
		if (!arch_is_irn_not_scheduled(succ) && get_nodes_block(succ) == block)
			return false; // Has dependants in current block
	}
	return true;
}

static inline bool modifies_flags(ir_node* node) {
	be_foreach_out(node, o) {
		const arch_register_req_t *req = arch_get_irn_register_req_out(node, o);
		if (req->cls->index == CLASS_sparc_flags) {
			return true;
		}
	}
	return false;
}

static void sched_block(ir_node *block, void *data)
{
	(void)data;
	block_meta meta; 
	meta.last_conditional = NULL;
	meta.total_nodes = 0;
	meta.sched_nodes = 0;
	ir_nodeset_init_size(&meta.branch_candidates, 3);

	DB((dbg, LEVEL_1, "Scheduling new block: %lu\n", block->node_nr));
	ir_nodeset_t *cands = be_list_sched_begin_block(block);
	if (get_Block_n_cfg_outs(block) >= 2) {
		ir_node* successor_block = get_Block_cfg_out(block, 0);
		ir_node* branch = get_irn_in(get_irn_in(successor_block)[0])[0];
		if (is_sparc_Bicc(branch)) {
			//DB((dbg, LEVEL_2, YEL "conditional branch found: %lu\n" RST, 
			//			branch->node_nr));
			assert(get_irn_arity(branch) == 1); // why should there be multiple?
			meta.last_conditional = get_irn_in(branch)[0];	

			ir_graph* irg = get_irn_irg(block);
			ir_reserve_resources(irg, IR_RESOURCE_IRN_VISITED);
			inc_irg_visited(irg);
			dfs_from(branch);
			ir_free_resources(irg, IR_RESOURCE_IRN_VISITED);

			DB((dbg, LEVEL_1, "Branch predecessor is: %lu\n", meta.last_conditional->node_nr));
		
			meta.total_nodes = 0;
			foreach_irn_out(block, i, succ) {
				if (!arch_is_irn_not_scheduled(succ) && !arch_irn_is(succ, schedule_first)) {
					// Scheduelable node
					meta.total_nodes++;
					if (ir_nodeset_size(&meta.branch_candidates) >= 3)
						continue;
					if (!irn_visited(succ) 
							//&& is_end_node_for_block(succ)
							&& !modifies_flags(succ)) {
						// Placeable between cmp and branch
						ir_nodeset_insert(&meta.branch_candidates, succ);
					}
				}
			}
			DB((dbg, LEVEL_1, "Branch cands contains %i node(s): ", ir_nodeset_size(&meta.branch_candidates)));
			DUMP_NODES(&meta.branch_candidates);
		} else {
			DB((dbg, LEVEL_2, YEL "non-bicc branch found: %lu\nskipping" RST, 
				branch->node_nr));
			meta.last_conditional = NULL;
		}

	} else {
		meta.last_conditional = NULL;
	}
	while (ir_nodeset_size(cands) > 0) {
		ir_node *node = sparc_select(cands, &meta);
		be_list_sched_schedule(node);
		meta.sched_nodes++;
	}
	be_list_sched_end_block();
	ir_nodeset_destroy(&meta.branch_candidates);
}

static void sched_sparc(ir_graph *irg)
{
	DB((dbg, LEVEL_1, "Starting SPARC scheduling\n"));
	DB((dbg, LEVEL_1, "Scheduling graph \"%s\"\n", irg->ent->name));
	//TODO: is this right? do I need to free_irg_outs?
	assure_irg_outs(irg);
	
	be_list_sched_begin(irg);
	irg_block_walk_graph(irg, sched_block, NULL, NULL);
	be_list_sched_finish();

	DB((dbg, LEVEL_1, "Done SPARC schedueling\n"));
}

BE_REGISTER_MODULE_CONSTRUCTOR(be_init_sched_sparc)
void be_init_sched_sparc(void)
{
	be_register_scheduler("sparc", sched_sparc);
	FIRM_DBG_REGISTER(dbg, "firm.be.sched.sparc");
}
