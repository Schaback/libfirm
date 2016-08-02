#include "call_sites.h"
#include "debug.h"
#include "important_args.h"
#include "ircons.h"
#include "irgmod.h"
#include "irnode_t.h"
#include "iroptimize.h"
#include "irouts_t.h"
#include "irprog_t.h"
#include "irtools.h"
#include "panic.h"
#include "callgraph.h"
#include "cgana.h"
#include "cloning_vector_t.h"
#include "cvhashmap.h"

struct obstack obst;

static void clone_set_new(ir_entity *clone)
{
	set_entity_link(clone, (void *)true);
}

static void clone_unset_new(ir_entity *clone)
{
	set_entity_link(clone, (void *)false);
}

static bool is_new_clone(const ir_entity *clone)
{
	return (bool)get_entity_link(clone);
}

static void update_irg_args(ir_graph *irg, const cloning_vector_t cv)
{
	/* Call algorithm that computes the out edges */
	assure_irg_outs(irg);

	ir_node *irg_args = get_irg_args(irg);
	foreach_irn_out (irg_args, i, arg) {
		size_t pos               = get_Proj_num(arg);
		ir_node *const const_arg = cv_get(cv, pos);

		if (const_arg) {
			assert(get_irn_arity(const_arg) == 0);
			ir_node *const block           = get_nodes_block(arg);
			ir_node *const const_arg_clone = irn_copy_into_irg(const_arg, irg);
			exchange(arg, const_arg_clone);
			set_nodes_block(const_arg_clone, block);
		} else {
			size_t new_pos = cv_get_new_idx(cv, pos);
			set_Proj_num(arg, new_pos);
		}
	}
}

static void update_frame(ir_type *const frame, const cloning_vector_t cv)
{
	for (size_t i = 0, n = get_compound_n_members(frame); i < n; ++i) {
		ir_entity *const ent = get_compound_member(frame, i);
		if (!is_parameter_entity(ent)) continue;

		size_t const pos = get_entity_parameter_number(ent);
		if (cv_get(cv, pos)) {
			panic("specializing parameter with entity not handled yet");
		} else {
			set_entity_parameter_number(ent, cv_get_new_idx(cv, pos));
		}
	}
}

/**
 * Create a new graph for the clone of the method,
 * that we want to clone.
 *
 * @param ent The entity of the method that must be cloned.
 * @param q   Our quadruplet.
 */
static ir_graph *get_clone_irg(ir_graph *irg, const cloning_vector_t cv)
{
	ir_graph *const clone_irg = create_irg_copy(irg);
	update_frame(get_irg_frame_type(clone_irg), cv);

	update_irg_args(clone_irg, cv);

	/* The "cloned" graph must be matured. */
	irg_finalize_cons(clone_irg);

	return clone_irg;
}

/**
 * The function create a new entity type
 * for our clone and set it to clone entity.
 *
 * @param q   Contains information for the method to clone.
 * @param ent The entity of the clone.
 **/
static ir_type *get_clone_type(const ir_type *mtp, const cloning_vector_t cv)
{
	size_t const n_params     = get_method_n_params(mtp);
	size_t const n_new_params = n_params - cv_get_size(cv);
	size_t const n_ress       = get_method_n_ress(mtp);
	bool const is_variadic    = is_method_variadic(mtp);
	unsigned const cc_mask    = get_method_calling_convention(mtp);
	mtp_additional_properties const property_mask =
	    get_method_additional_properties(mtp);

	/* Create the new type for our clone. */
	ir_type *const new_mtp = new_type_method(n_new_params, n_ress, is_variadic,
	                                         cc_mask, property_mask);

	/* We must set the type of the methods parameters.*/
	for (size_t i = 0, j = 0; i < n_params; ++i) {
		if (cv_get(cv, i)) continue;
		ir_type *const tp = get_method_param_type(mtp, i);
		set_method_param_type(new_mtp, j++, tp);
	}
	/* Copy the methods result types. */
	for (size_t i = 0; i < n_ress; ++i) {
		ir_type *const tp = get_method_res_type(mtp, i);
		set_method_res_type(new_mtp, i, tp);
	}
	return new_mtp;
}

static ir_entity *create_proc_clone(const ir_entity *src,
                                 const cloning_vector_t cv)
{
	// Generate a unique identifier for the clone
	ident *const clone_ident = id_unique(get_entity_ident(src));
	// Create the entity for the clone
	ir_type *const owner        = get_entity_owner(src);
	ir_entity *const new_entity = clone_entity(src, clone_ident, owner);

	// A cloned entity is always local
	set_entity_visibility(new_entity, ir_visibility_local);

	// Create the prototype for the clone
	ir_type *mtp = get_clone_type(get_entity_type(src), cv);
	set_entity_type(new_entity, mtp);

	// Create the ir_graph for the clone
	ir_graph *const irg = get_clone_irg(get_entity_linktime_irg(src), cv);

	// Insert clone into the program
	set_irg_entity(irg, new_entity);
	set_entity_irg(new_entity, irg);
	add_irp_irg(irg);

	// Mark the clone as freshly generated
	clone_set_new(new_entity);

	return new_entity;
}

static pmap *clone_map = NULL;

static ir_entity *get_proc_clone(const ir_entity *src,
                                 const cloning_vector_t cv)
{
	cv_hashmap_t *const cv2clone_map = pmap_get(cv_hashmap_t, clone_map, src);
	if (cv2clone_map == NULL) return NULL;
	return cv_hashmap_get(ir_entity, cv2clone_map, cv);
}

static void cache_proc_clone(const ir_entity *src, const cloning_vector_t cv,
                             ir_entity *clone)
{
	cv_hashmap_t *cv2clone_map = pmap_get(cv_hashmap_t, clone_map, src);
	if (cv2clone_map == NULL) {
		cv2clone_map = obstack_alloc(&obst, sizeof *cv2clone_map);
		cv_hashmap_init(cv2clone_map);
		pmap_insert(clone_map, src, cv2clone_map);
	}
	cv_hashmap_insert(cv2clone_map, cv, clone);
}

static ir_entity *get_or_create_proc_clone(const ir_entity *src,
                                           const cloning_vector_t cv)
{
	ir_entity *clone = get_proc_clone(src, cv);
	if (clone == NULL) {
		clone = create_proc_clone(src, cv);
		cache_proc_clone(src, cv, clone);
	}
	return clone;
}

/**
 * Update the given `call` so that it calls `clone` with the arguments
 * determined by `used_args`
 *
 * @param call         The call node that should be updated
 * @param clone        The new call target
 * @param used_args    Indices of the arguments of the old call that should
 * be used in the updated call
 */
static void update_call(ir_node *call, ir_entity *clone,
                        const cloning_vector_t cv)
{
	// Actually we would only need to update the ptr and the arguments, but
	// there is no public interface to do that, so we create a new call
	const bitset_t *const used_args = cv_get_undef(cv, &obst);
	size_t const n_args             = bitset_popcount(used_args);
	ir_node **const in              = ALLOCAN(ir_node *, n_args);

	size_t new_idx = 0;
	bitset_foreach (used_args, i) {
		in[new_idx++] = get_Call_param(call, i);
	}

	ir_node *const block      = get_nodes_block(call);
	ir_node *const mem        = get_Call_mem(call);
	ir_node *const ptr        = new_r_Address(get_irn_irg(call), clone);
	ir_type *const type       = get_clone_type(get_Call_type(call), cv);
	ir_node *const clone_call = new_r_Call(block, mem, ptr, n_args, in, type);

	exchange(call, clone_call);

	// TODO do anything to remove possibly unused nodes?
}

typedef struct order_t {
	ir_graph **irgs;
	size_t last;
} order_t;


static void build_topo_order(ir_graph *g, void *env)
{
	assert(g != NULL);

	order_t *order             = (order_t *)env;
	order->irgs[--order->last] = g;
}

void proc_cloning(float threshold)
{
	(void)threshold;

	// register a debug mask
	DEBUG_ONLY(firm_dbg_module_t *dbg = NULL);
	FIRM_DBG_REGISTER(dbg, "ir.opt.proc_cloning");

	obstack_init(&obst);
	pmap *const vip_map = important_args_get();

	// Get call site info
	call_sites_t call_sites;
	call_sites_init(&call_sites);

	// Create reverse postorder of the call graph
	size_t n_irgs = get_irp_n_irgs();
	order_t order = {NEW_ARR_DZ(ir_graph *, &obst, n_irgs), n_irgs};
	callgraph_walk(NULL, build_topo_order, &order);
	assert(order.last == 0);

	// Initialize clone map
	clone_map = pmap_create_ex(n_irgs);

	ARR_FOREACH_ITEM (order.irgs, ir_graph *, irg) {
		ir_entity *const ent = get_irg_entity(irg);
		bitset_t *vips       = pmap_get(bitset_t, vip_map, irg);

		if (is_method_variadic(get_entity_type(ent))) {
			// We cannot remove the last fixed parameter of procedures with
			// variadic arguments since it is used to access the var args.
			bitset_clear(vips, bitset_size(vips) - 1);
		}

		DB((dbg, LEVEL_2, "Analyzing calls to %s\n", get_entity_name(ent)));

		// call_sites_get_n_calls_to has to be called every time, since we
		// might update the calls below when we have a direct recursion
		for (size_t i = 0; i < call_sites_get_n_calls_to(&call_sites, irg); i++) {
			ir_node *const call = call_sites_get_call_to(&call_sites, irg, i);

			DB((dbg, LEVEL_2, "Analyzing call %p from %s\n", call,
			    get_entity_name(get_irg_entity(get_irn_irg(call)))));

			cloning_vector_t cv = cv_new(call, vips, &obst);
			if (cv_get_size(cv) == 0) continue;

			ir_entity *const clone = get_or_create_proc_clone(ent, cv);
			DB((dbg, LEVEL_1, "Created clone %s\n", get_entity_name(clone)));

			// Even if we invalidate the call_sites here, we do not have to
			// update them, since we don't come back to already handled calls.
			// At least not as long as we do not deal with recursion.
			update_call(call, clone, cv);

			if (is_new_clone(clone)) {
				ir_graph *const clone_irg = get_entity_linktime_irg(clone);
				call_sites_register_irg_calls(&call_sites, clone_irg);
				clone_unset_new(clone);
			}
		}
	}
	// Invalidate call graph & co
	free_irp_callee_info();
	free_callgraph();

	call_sites_destroy(&call_sites);
	obstack_free(&obst, 0);
	pmap_destroy(vip_map);
	pmap_destroy(clone_map);
}
