/*
 * This file is part of libFirm.
 * Copyright (C) 2012 University of Karlsruhe.
 */

/**
 * @file
 * @brief   Write text representation of firm to file.
 * @author  Martin Trapp, Christian Schaefer, Goetz Lindenmaier, Hubert Schmidt,
 *          Matthias Braun
 */
#include <stdlib.h>
#include <stdarg.h>
#include <stdbool.h>

#include "irdump_t.h"
#include "irgraph_t.h"
#include "irnode_t.h"

#include "irprog_t.h"
#include "entity_t.h"
#include "trouts.h"
#include "irgwalk.h"
#include "tv_t.h"
#include "irprintf.h"
#include "error.h"
#include "cgana.h"

#include "irdom.h"

typedef struct bitflag_name_t {
	unsigned    flag;
	const char *name;
} bitflag_name_t;

static const bitflag_name_t ir_linkage_names[] = {
	{ IR_LINKAGE_CONSTANT,        "constant"        },
	{ IR_LINKAGE_WEAK,            "weak"            },
	{ IR_LINKAGE_GARBAGE_COLLECT, "garbage_collect" },
	{ IR_LINKAGE_MERGE,           "merge"           },
	{ IR_LINKAGE_HIDDEN_USER,     "hidden_user"     },
	{ 0,                          NULL              },
};
static const bitflag_name_t mtp_property_names[] = {
	{ mtp_property_const,              "const"              },
	{ mtp_property_pure,               "pure"               },
	{ mtp_property_noreturn,           "noreturn"           },
	{ mtp_property_nothrow,            "nothrow"            },
	{ mtp_property_naked,              "naked"              },
	{ mtp_property_malloc,             "malloc"             },
	{ mtp_property_returns_twice,      "returns_twice"      },
	{ mtp_property_private,            "private"            },
	{ mtp_property_has_loop,           "has_loop"           },
	{ mtp_property_always_inline,      "always_inline"      },
	{ mtp_property_noinline,           "noinline"           },
	{ mtp_property_inline_recommended, "inline_recommended" },
	{ mtp_temporary,                   "temporary"          },
	{ 0,                               NULL                 },
};
static const bitflag_name_t cc_names[] = {
	{ cc_reg_param,           "reg_param"           },
	{ cc_last_on_top,         "last_on_top"         },
	{ cc_callee_clear_stk,    "callee_clear_stk"    },
	{ cc_this_call,           "this_call"           },
	{ cc_compound_ret,        "compound_ret"        },
	{ cc_frame_on_caller_stk, "frame_on_caller_stk" },
	{ cc_fpreg_param,         "fpreg_param"         },
	{ 0,                      NULL                  },
};

static void print_bitflags(FILE *const F, const bitflag_name_t names[],
                           unsigned const bitset)
{
	for (size_t i = 0; names[i].name != 0; ++i) {
		if ((bitset & names[i].flag) != 0) {
			fputc(' ', F);
			fputs(names[i].name, F);
		}
	}
}

static ir_dump_verbosity_t verbosity = dump_verbosity_max;

void ir_set_dump_verbosity(ir_dump_verbosity_t new_verbosity)
{
	verbosity = new_verbosity;
}

ir_dump_verbosity_t ir_get_dump_verbosity(void)
{
	return verbosity;
}

void dump_irnode_to_file(FILE *const F, const ir_node *const n)
{
	dump_node_opcode(F, n);
	fprintf(F, " %ld\n", get_irn_node_nr(n));

	fprintf(F, "  index: %u\n", get_irn_idx(n));
	fprintf(F, "  mode:    %s\n", get_mode_name(get_irn_mode(n)));
	fprintf(F, "  visited: %lu\n", get_irn_visited(n));
	ir_graph *irg = get_irn_irg(n);
	if (irg != get_const_code_irg())
		fprintf (F, "  irg:     %s\n", get_ent_dump_name(get_irg_entity(irg)));

	if (get_irn_pinned(n) == op_pin_state_floats &&
		get_irg_pinned(get_irn_irg(n)) == op_pin_state_floats) {
		fprintf(F, "  node was pinned in ");
		ir_node *const block = get_nodes_block(n);
		dump_node_opcode(F, block);
		fprintf(F, " %ld\n", get_irn_node_nr(block));
	}

	fprintf(F, "  arity:   %d\n", get_irn_arity(n));
	/* show all predecessor nodes */
	fprintf(F, "  pred nodes:\n");
	if (!is_Block(n)) {
		fprintf(F, "    -1:    ");
		ir_node *const block = get_nodes_block(n);
		dump_node_opcode(F, block);
		fprintf(F, " %ld\n", get_irn_node_nr(block));
	}

	for (int i = 0, arity = get_irn_arity(n); i < arity; ++i) {
		fprintf(F, "     %d: %s ", i, is_backedge(n, i) ? "be" : "  ");
		dump_node_opcode(F, get_irn_n(n, i));
		fprintf(F, " %ld\n", get_irn_node_nr(get_irn_n(n, i)));
	}

	fprintf(F, "  Private Attributes:\n");

	if (is_Proj(n)) {
		const ir_node *pred = get_Proj_pred(n);
		long           pn   = get_Proj_proj(n);
		fprintf(F, "  proj nr: %ld\n", pn);
		if (is_Switch(pred)) {
			const ir_switch_table *table = get_Switch_table(pred);
			for (size_t i = 0, n_entries = ir_switch_table_get_n_entries(table);
			     i < n_entries; ++i) {
				const ir_switch_table_entry *entry
					= ir_switch_table_get_entry_const(table, i);
				if (entry->pn == pn && entry->min != NULL && entry->max != NULL) {
					ir_tarval *min = entry->min;
					ir_tarval *max = entry->max;
					if (min != max) {
						ir_fprintf(F, "  switch case %+F .. %+F\n", min, max);
					} else {
						ir_fprintf(F, "  switch case %+F\n", min);
					}
				}
			}
		}
	}

	if (is_fragile_op(n)) {
		fprintf(F, "  pinned state: %s\n", get_op_pin_state_name(get_irn_pinned(n)));
		/* not dumped: frag array */
	}

	/* This is not nice, output it as a marker in the predecessor list. */
	if (is_Block(n) || is_Phi(n)) {
		fprintf(F, "  backedges:");
		char comma = ' ';
		for (int i = 0, arity = get_irn_arity(n); i < arity; i++) {
			if (is_backedge(n, i)) {
				fprintf(F, "%c %d", comma, i);
				comma = ',';
			}
			fprintf(F, "\n");
		}
	}

	/* Loop node.   Someone else please tell me what's wrong ... */
	if (irg_has_properties(irg, IR_GRAPH_PROPERTY_CONSISTENT_LOOPINFO)) {
		const ir_loop *loop = get_irn_loop(n);
		if (loop != NULL) {
			fprintf(F, "  in loop %ld with depth %u\n",
			        get_loop_loop_nr(loop), get_loop_depth(loop));
		}
	}

	/* Source types */
	switch ((ir_opcode)get_irn_opcode(n)) {
	case iro_Block: {
		const ir_entity *const entity = get_Block_entity(n);
		if (entity != NULL)
			fprintf(F, "  Label: %lu\n", get_entity_label(entity));
		fprintf(F, "  block visited: %lu\n", get_Block_block_visited(n));
		fprintf(F, "  block marked: %u\n", get_Block_mark(n));
		if (irg_has_properties(get_irn_irg(n), IR_GRAPH_PROPERTY_CONSISTENT_DOMINANCE)) {
			fprintf(F, "  dom depth %d\n", get_Block_dom_depth(n));
			fprintf(F, "  domtree pre num %u\n", get_Block_dom_tree_pre_num(n));
			fprintf(F, "  max subtree pre num %u\n", get_Block_dom_max_subtree_pre_num(n));
		}
		if (irg_has_properties(get_irn_irg(n), IR_GRAPH_PROPERTY_CONSISTENT_POSTDOMINANCE)) {
			fprintf(F, "  pdom depth %d\n", get_Block_postdom_depth(n));
			fprintf(F, "  pdomtree pre num %u\n", get_Block_pdom_tree_pre_num(n));
			fprintf(F, "  max pdomsubtree pre num %u\n", get_Block_pdom_max_subtree_pre_num(n));
		}

		/* not dumped: graph_arr */
		/* not dumped: mature    */
		break;
	}
	case iro_Start: {
		const ir_type *tp = get_entity_type(get_irg_entity(get_irn_irg(n)));
		ir_fprintf(F, "  start of method of type %+F\n", tp);
		for (size_t i = 0, n_params = get_method_n_params(tp);
		     i < n_params; ++i) {
			ir_fprintf(F, "    param %d type: %+F\n", i, get_method_param_type(tp, i));
		}
		break;
	}
	case iro_Cond:
		if (get_Cond_jmp_pred(n) != COND_JMP_PRED_NONE) {
			fprintf(F, "  jump prediction: %s\n",
			        get_cond_jmp_predicate_name(get_Cond_jmp_pred(n)));
		}
		break;
	case iro_Alloc:
		ir_fprintf(F, "  alignment: %u\n", get_Alloc_alignment(n));
		break;
	case iro_Sel: {
		const ir_entity *ent = get_Sel_entity(n);
		if (ent != NULL) {
			fprintf(F, "  Selecting entity %s (%ld)\n", get_entity_name(ent), get_entity_nr(ent));
			ir_fprintf(F, "    of type    %+F\n",  get_entity_type(ent));
			ir_fprintf(F, "    with owner %+F.\n", get_entity_owner(ent));
		} else {
			fprintf(F, "  <NULL entity>\n");
		}
		break;
	}
	case iro_Call: {
		const ir_type *tp = get_Call_type(n);
		ir_fprintf(F, "  calling method of type %+F\n", tp);
		if (get_unknown_type() != tp) {
			for (size_t i = 0, n_params = get_method_n_params(tp);
			     i < n_params; ++i) {
			    const ir_type *param_type = get_method_param_type(tp, i);
				ir_fprintf(F, "    param %d type: %+F\n", i, param_type);
			}
			for (size_t i = 0, n_ress = get_method_n_ress(tp);
			     i < n_ress; ++i) {
			    const ir_type *res_type = get_method_res_type(tp, i);
				ir_fprintf(F, "    result %d type: %+F\n", i, res_type);
			}
		}
		if (cg_call_has_callees(n)) {
			fprintf(F, "  possible callees:\n");
			for (size_t i = 0, n_callees = cg_get_call_n_callees(n);
			     i < n_callees; i++) {
				const ir_entity *callee = cg_get_call_callee(n, i);
				ir_fprintf(F, "    %zu: %s\n", i, get_ent_dump_name(callee));
			}
		}
		break;
	}
	case iro_Cmp: {
		ir_relation relation = get_Cmp_relation(n);
		ir_fprintf(F, "  relation: %s\n", get_relation_string(relation));
		break;
	}
	case iro_Return: {
		const ir_type *tp = get_entity_type(get_irg_entity(get_irn_irg(n)));
		ir_fprintf(F, "  return in method of type %+F\n", tp);
		for (size_t i = 0, n_ress = get_method_n_ress(tp); i < n_ress; ++i) {
			const ir_type *res_type = get_method_res_type(tp, i);
			ir_fprintf(F, "    result %d type: %+F\n", i, res_type);
		}
		break;
	}

	case iro_Address:
		fprintf(F, "  entity: ");
		dump_entity_to_file(F, get_Address_entity(n));
		break;

	case iro_Offset:
		fprintf(F, "  entity: ");
		dump_entity_to_file(F, get_Offset_entity(n));
		break;

	case iro_Align:
		fprintf(F, "  type: ");
		dump_type_to_file(F, get_Align_type(n));
		break;

	case iro_Size:
		fprintf(F, "  type: ");
		dump_type_to_file(F, get_Size_type(n));
		break;

	case iro_Load:
		fprintf(F, "  mode of loaded value: %s\n", get_mode_name(get_Load_mode(n)));
		fprintf(F, "  volatility: %s\n", get_volatility_name(get_Load_volatility(n)));
		fprintf(F, "  align: %s\n", get_align_name(get_Load_unaligned(n)));
		break;
	case iro_Store:
		fprintf(F, "  volatility: %s\n", get_volatility_name(get_Store_volatility(n)));
		fprintf(F, "  align: %s\n", get_align_name(get_Store_unaligned(n)));
		break;
	case iro_Confirm:
		fprintf(F, "  compare operation: %s\n", get_relation_string(get_Confirm_relation(n)));
		break;
	case iro_ASM: {
		fprintf(F, "  assembler text: %s", get_id_str(get_ASM_text(n)));
		fprintf(F, "\n  inputs:  ");
		const ir_asm_constraint *in_cons = get_ASM_input_constraints(n);
		for (int i = 0, n_inputs = get_ASM_n_inputs(n); i < n_inputs; ++i) {
			fprintf(F, "%%%u %s ", in_cons[i].pos,
			        get_id_str(in_cons[i].constraint));
		}
		fprintf(F, "\n  outputs: ");
		const ir_asm_constraint *out_cons = get_ASM_output_constraints(n);
		for (int i = 0, n_outputs = get_ASM_n_output_constraints(n);
		     i < n_outputs; ++i) {
			fprintf(F, "%%%u %s ", out_cons[i].pos,
			        get_id_str(out_cons[i].constraint));
		}

		fprintf(F, "\n  clobber: ");
		ident **clobber = get_ASM_clobbers(n);
		for (int i = 0, n_clobbers = get_ASM_n_clobbers(n); i < n_clobbers; ++i)
			fprintf(F, "%s ", get_id_str(clobber[i]));
		if (get_irn_pinned(n) != op_pin_state_floats)
			fprintf(F, "\n  volatile");
		fprintf(F, "\n");
		break;
	}

	default:
		break;
	}
}

void dump_graph_as_text(FILE *const out, const ir_graph *const irg)
{
	fprintf(out, "graph %s\n", get_irg_dump_name(irg));
}

static bool need_nl = true;

static bool is_init_string(ir_initializer_t const* const init,
                           ir_type const* const type)
{
	const ir_type *const element_type = get_array_element_type(type);
	if (!is_Primitive_type(element_type))
		return false;

	const ir_mode *mode = get_type_mode(element_type);
	if (!mode_is_int(mode) || get_mode_size_bits(mode) != 8)
		return false;

	for (size_t i = 0, n = get_initializer_compound_n_entries(init);
	     i != n; ++i) {
		ir_initializer_t const* const val = get_initializer_compound_value(init, i);
		if (get_initializer_kind(val) != IR_INITIALIZER_TARVAL)
			return false;
		ir_tarval *tv = get_initializer_tarval_value(val);

		if (!tarval_is_constant(tv))
			return false;

		long v = get_tarval_long(tv);
		if (v != 0 && (v < 0x07 || 0x0D < v) && v != 0x1B && (v < 0x20 || 0x80 <= v) && (v < 0xA0 || 0x100 <= v))
			return false;
	}

	return true;
}

/**
 * Dump initializers.
 */
static void dump_ir_initializers_to_file(FILE *const F,
		const char *const prefix, const ir_initializer_t *const initializer,
		const ir_type *const type)
{
	if (need_nl) {
		fprintf(F, "\n%s    ", prefix);
		need_nl = false;
	}
	switch (get_initializer_kind(initializer)) {
	case IR_INITIALIZER_NULL:
		fprintf(F, "\t = <NOT_SET>");
		break;
	case IR_INITIALIZER_TARVAL: {
		ir_tarval *tv = get_initializer_tarval_value(initializer);
		ir_fprintf(F, "\t = <TV>%F", tv);
		break;
	}
	case IR_INITIALIZER_CONST: {
		ir_node *value = get_initializer_const_value(initializer);
		ir_fprintf(F, "\t = %F", value);
		break;
	}
	case IR_INITIALIZER_COMPOUND:
		if (is_Array_type(type)) {
			size_t const n = get_initializer_compound_n_entries(initializer);

			if (is_init_string(initializer, type)) {
				fprintf(F, "\t[0...%u] = '", (unsigned)n - 1);
				for (size_t i = 0; i != n; ++i) {
					ir_initializer_t const* const val = get_initializer_compound_value(initializer, i);
					ir_tarval*              const tv  = get_initializer_tarval_value(val);
					long                    const v   = get_tarval_long(tv);

					switch (v) {
						case 0x00: fprintf(F, "\\\\000");  break;
						case 0x07: fprintf(F, "\\\\a");    break;
						case 0x08: fprintf(F, "\\\\b");    break;
						case 0x09: fprintf(F, "\\\\t");    break;
						case 0x0A: fprintf(F, "\\\\n");    break;
						case 0x0B: fprintf(F, "\\\\v");    break;
						case 0x0C: fprintf(F, "\\\\f");    break;
						case 0x0D: fprintf(F, "\\\\r");    break;
						case 0x1B: fprintf(F, "\\\\033");  break;
						case 0x22: fprintf(F, "\\\\\\\""); break;
						case 0x5C: fprintf(F, "\\\\\\\\"); break;
						default:   fprintf(F, "%c", (unsigned char)v); break;
					}
				}
				fprintf(F, "'");
			} else {
				const ir_type *const element_type = get_array_element_type(type);

				for (size_t i = 0; i < n; ++i) {
					const ir_initializer_t *sub_initializer
						= get_initializer_compound_value(initializer, i);

					if (need_nl) {
						fprintf(F, "\n%s    ", prefix);
						need_nl = false;
					}
					fprintf(F, "[%d]", (int) i);
					dump_ir_initializers_to_file(F, prefix, sub_initializer, element_type);
				}
			}
		} else {
			assert(is_compound_type(type));
			for (size_t i = 0, n = get_compound_n_members(type); i < n; ++i) {
				const ir_entity *member  = get_compound_member(type, i);
				const ir_type   *subtype = get_entity_type(member);
				assert(i < get_initializer_compound_n_entries(initializer));
				const ir_initializer_t *sub_initializer
					= get_initializer_compound_value(initializer, i);

				if (need_nl) {
					fprintf(F, "\n%s    ", prefix);
					need_nl = false;
				}
				ir_fprintf(F, ".%F", member);
				dump_ir_initializers_to_file(F, prefix, sub_initializer, subtype);
			}
		}
		break;
	default:
		panic("invalid ir_initializer kind found");
	}
	need_nl = true;
}

static void dump_entity_linkage(FILE *const F, const ir_entity *const entity)
{
	ir_linkage linkage = get_entity_linkage(entity);
	if (linkage == IR_LINKAGE_DEFAULT) {
		fprintf(F, " default");
		return;
	}
	print_bitflags(F, ir_linkage_names, (unsigned)linkage);
}

static void dump_entity_to_file_prefix(FILE *const F,
                                       const ir_entity *const ent,
                                       const char *const prefix)
{
	const ir_type *owner = get_entity_owner(ent);
	const ir_type *type  = get_entity_type(ent);
	if (verbosity & dump_verbosity_onlynames) {
		fprintf(F, "%sentity %s.%s (%ld)\n", prefix,
		        get_compound_name(owner), get_entity_name(ent),
		        get_entity_nr(ent));
		return;
	}

	if (verbosity & dump_verbosity_entattrs) {
		fprintf(F, "%sentity %s (%ld)\n", prefix, get_entity_name(ent),
		        get_entity_nr(ent));
		ir_fprintf(F, "%s  type:  %+F\n", prefix, type);
		ir_fprintf(F, "%s  owner: %+F\n", prefix, owner);

		if (is_Class_type(get_entity_owner(ent))) {
			if (get_entity_n_overwrites(ent) > 0) {
				fprintf(F, "%s  overwrites:\n", prefix);
				for (size_t i = 0; i < get_entity_n_overwrites(ent); ++i) {
					const ir_entity *ov = get_entity_overwrites(ent, i);
					ir_fprintf(F, "%s    %d: %s of class %+F\n", prefix, i,
					        get_entity_name(ov), get_entity_owner(ov));
				}
			} else {
				fprintf(F, "%s  Does not overwrite other entities.\n", prefix);
			}
			if (get_entity_n_overwrittenby(ent) > 0) {
				fprintf(F, "%s  overwritten by:\n", prefix);
				for (size_t i = 0; i < get_entity_n_overwrittenby(ent); ++i) {
					const ir_entity *ov = get_entity_overwrittenby(ent, i);
					ir_fprintf(F, "%s    %d: %s of class %+F\n", prefix, i,
					           get_entity_name(ov), get_entity_owner(ov));
				}
			} else {
				fprintf(F, "%s  Is not overwritten by other entities.\n",
				        prefix);
			}

			if (get_irp_inh_transitive_closure_state() != inh_transitive_closure_none) {
				fprintf(F, "%s  transitive overwrites:\n", prefix);
				for (const ir_entity *ov = get_entity_trans_overwrites_first(ent);
				     ov != NULL; ov = get_entity_trans_overwrites_next(ent)) {
					ir_fprintf(F, "%s    : %s of class %+F\n", prefix,
					           get_entity_name(ov), get_entity_owner(ov));
				}
				fprintf(F, "%s  transitive overwritten by:\n", prefix);
				for (const ir_entity *ov = get_entity_trans_overwrittenby_first(ent);
				     ov != NULL; ov = get_entity_trans_overwrittenby_next(ent)) {
					ir_fprintf(F, "%s    : %s of class %+F\n", prefix,
					           get_entity_name(ov), get_entity_owner(ov));
				}
			}
		}

		if (is_Method_type(type)) {
			const unsigned mask = get_entity_additional_properties(ent);
			const unsigned cc   = get_method_calling_convention(type);

			if (is_method_entity(ent)) {
				const ir_graph *const irg = get_entity_irg(ent);

				if (irg != NULL) {
					fprintf(F, "%s  maximum node index:   %u\n", prefix,
					        get_irg_last_idx(irg));
				}
			}

			fprintf(F, "%s  additional prop: ", prefix);
			print_bitflags(F, mtp_property_names, (unsigned)mask);
			fputc('\n', F);

			fprintf(F, "%s  calling convention: ", prefix);
			print_bitflags(F, cc_names, (unsigned)cc);

			if (is_method_entity(ent)) {
				fprintf(F, "\n%s  vtable number:        %u\n", prefix,
					get_entity_vtable_number(ent));
			}
		}
	} else {  /* no entattrs */
		ir_fprintf(F, "%s %+F: %s", prefix, type, get_entity_name(ent));
		if (is_Method_type(type))
			fputs("(...)", F);
		if (is_entity_compound_member(ent)) {
			ir_fprintf(F, " offset: %d", get_entity_offset(ent));
			unsigned bitfield_size = get_entity_bitfield_size(ent);
			if (bitfield_size > 0) {
				unsigned bitfield_offset = get_entity_bitfield_offset(ent);
				ir_fprintf(F, " bitfield offs %u size %u", bitfield_offset,
				           bitfield_size);
			}
		}

		if (verbosity & dump_verbosity_accessStats) {
			dump_entity_linkage(F, ent);
		}
		fputc('\n', F);
	}

	if (verbosity & dump_verbosity_entconsts) {
		if (ent->initializer != NULL) {
			const ir_initializer_t *initializer = get_entity_initializer(ent);
			fprintf(F, "\n%s  Initializers:", prefix);
			need_nl = true;
			dump_ir_initializers_to_file(F, prefix, initializer, get_entity_type(ent));
			fputc('\n', F);
		}
	}

	if (verbosity & dump_verbosity_entattrs) {
		fprintf(F, "%s  linkage:", prefix);
		dump_entity_linkage(F, ent);
		fprintf(F, "\n%s  volatility:  %s", prefix, get_volatility_name(get_entity_volatility(ent)));
		fprintf(F, "\n%s  aligned:  %s", prefix, get_align_name(get_entity_aligned(ent)));
		fprintf(F, "\n%s  alignment:  %u", prefix, get_entity_alignment(ent));
		fprintf(F, "\n%s  ld_name: %s", prefix, ent->ld_name ? get_entity_ld_name(ent) : "no yet set");
		if (is_entity_compound_member(ent)) {
			fprintf(F, "\n%s  offset:  %d bytes", prefix, get_entity_offset(ent));
			unsigned bitfield_size   = get_entity_bitfield_size(ent);
			if (bitfield_size > 0) {
				unsigned bitfield_offset = get_entity_bitfield_offset(ent);
				fprintf(F, "\n%s  bitfield offset: %u", prefix, bitfield_offset);
				fprintf(F, "\n%s  bitfield size: %u", prefix, bitfield_size);
			}
		}
		if (is_Method_type(type) && is_method_entity(ent)) {
			const ir_graph *irg = get_entity_irg(ent);
			if (irg != NULL) {
				fprintf(F, "\n%s  irg = %ld", prefix, get_irg_graph_nr(irg));
			} else {
				fprintf(F, "\n%s  irg = NULL", prefix);
			}
		}
		fputc('\n', F);
	}
}

void dump_entity_to_file(FILE *const out, const ir_entity *const ent)
{
	dump_entity_to_file_prefix(out, ent, "");
	fprintf(out, "\n");
}

void dump_type_to_file(FILE *const F, const ir_type *const tp)
{
	ir_fprintf(F, "%+F", tp);
	if (verbosity & dump_verbosity_onlynames) { fprintf(F, "\n"); return; }

	switch (get_type_tpop_code(tp)) {
	case tpo_class:
		if ((verbosity & dump_verbosity_methods) || (verbosity & dump_verbosity_fields)) {
			fprintf(F, "\n  members:\n");
		}
		for (size_t i = 0; i < get_class_n_members(tp); ++i) {
			const ir_entity *mem = get_class_member(tp, i);
			if (((verbosity & dump_verbosity_methods) &&  is_Method_type(get_entity_type(mem))) ||
				((verbosity & dump_verbosity_fields)  && !is_Method_type(get_entity_type(mem)))   ) {
				if (!(verbosity & dump_verbosity_nostatic)) {
					dump_entity_to_file_prefix(F, mem, "    ");
				}
			}
		}
		if (verbosity & dump_verbosity_typeattrs) {
			fprintf(F, "  supertypes: ");
			for (size_t i = 0; i < get_class_n_supertypes(tp); ++i) {
				const ir_type *stp = get_class_supertype(tp, i);
				ir_fprintf(F, "\n    %d %+F", i, stp);
			}
			fprintf(F, "\n  subtypes: ");
			for (size_t i = 0; i < get_class_n_subtypes(tp); ++i) {
				const ir_type *stp = get_class_subtype(tp, i);
				ir_fprintf(F, "\n    %d %+F", i, stp);
			}

			if (get_irp_inh_transitive_closure_state() != inh_transitive_closure_none) {
				fprintf(F, "\n  transitive supertypes: ");
				for (const ir_type *stp = get_class_trans_supertype_first(tp);
				     stp != NULL; stp = get_class_trans_supertype_next(tp)) {
					ir_fprintf(F, "\n    %+F", stp);
				}
				fprintf(F, "\n  transitive subtypes: ");
				for (const ir_type *stp = get_class_trans_subtype_first(tp);
				     stp != NULL; stp = get_class_trans_subtype_next(tp)) {
					ir_fprintf(F, "\n    %+F", stp);
				}
			}

			fprintf(F, "\n  flags:       ");
			if (is_class_final(tp))
				fprintf(F, "final, ");
			if (is_class_interface(tp))
				fprintf(F, "interface, ");
			if (is_class_abstract(tp))
				fprintf(F, "abstract, ");
			fprintf(F, "\n");
		}
		break;

	case tpo_union:
	case tpo_struct:
		if (verbosity & dump_verbosity_fields)
			fprintf(F, "\n  members: ");
		for (size_t i = 0; i < get_compound_n_members(tp); ++i) {
			const ir_entity *mem = get_compound_member(tp, i);
			if (verbosity & dump_verbosity_fields) {
				dump_entity_to_file_prefix(F, mem, "    ");
			}
		}
		break;

	case tpo_array:
		if (verbosity & dump_verbosity_typeattrs) {
			fprintf(F, "\n  array ");

			const ir_type *elem_tp = get_array_element_type(tp);
			size_t         n_dim   = get_array_n_dimensions(tp);
			for (size_t i = 0; i < n_dim; ++i) {
				fprintf(F, "[");

				const ir_node *lower = get_array_lower_bound(tp, i);
				if (is_Const(lower)) {
					fprintf(F, "%ld .. ", get_tarval_long(get_Const_tarval(lower)));
				} else {
					dump_node_opcode(F, lower);
					fprintf(F, " %ld .. ", get_irn_node_nr(lower));
				}

				const ir_node *upper = get_array_upper_bound(tp, i);
				if (is_Const(upper)) {
					fprintf(F, "%ld]", get_tarval_long(get_Const_tarval(lower)));
				} else {
					dump_node_opcode(F, upper);
					fprintf(F, " %ld]", get_irn_node_nr(upper));
				}
			}
			ir_fprintf(F, " of <%+F>", elem_tp);

			fprintf(F, "\n  order: ");
			for (size_t i = 0; i < n_dim; ++i)
				fprintf(F, "<%zu>", get_array_order(tp, i));

			fprintf(F, "\n");

			if (verbosity & dump_verbosity_fields) {
				dump_entity_to_file_prefix(F, get_array_element_entity(tp),
				                           "    ");
			}
		}
		break;

	case tpo_pointer:
		if (verbosity & dump_verbosity_typeattrs) {
			const ir_type *tt = get_pointer_points_to_type(tp);
			ir_fprintf(F, "\n  points to %+F\n", tt);
		}
		break;

	case tpo_method:
		if (verbosity & dump_verbosity_typeattrs) {
			mtp_additional_properties mtp = get_method_additional_properties(tp);
			unsigned cconv = get_method_calling_convention(tp);
			fprintf(F, "\n  variadicity: %s", get_variadicity_name(get_method_variadicity(tp)));
			fprintf(F, "\n  return types: %lu",
			        (unsigned long) get_method_n_ress(tp));
			for (size_t i = 0; i < get_method_n_ress(tp); ++i) {
				const ir_type *rtp = get_method_res_type(tp, i);
				ir_fprintf(F, "\n    %+F", rtp);
			}

			fprintf(F, "\n  parameter types: %lu",
			        (unsigned long) get_method_n_params(tp));
			for (size_t i = 0; i < get_method_n_params(tp); ++i) {
				const ir_type *ptp = get_method_param_type(tp, i);
				ir_fprintf(F, "\n    %+F", ptp);
			}
			fprintf(F, "\n  properties:");
			print_bitflags(F, mtp_property_names, (unsigned)mtp);

			fprintf(F, "\n  calling convention:");
			print_bitflags(F, cc_names, (unsigned)cconv);
			if (get_method_variadicity(tp)) {
				fprintf(F, "\n    ...");
			}
			fprintf(F, "\n");
		}
		break;

	case tpo_primitive:
	case tpo_unknown:
		fprintf(F, "\n");
		break;

	default:
		if (verbosity & dump_verbosity_typeattrs) {
			fprintf(F, ": details not implemented\n");
		}
	}

	fprintf(F, "  state:      %s,\n", get_type_state_name(get_type_state(tp)));
	fprintf(F, "  size:       %2u Bytes,\n", get_type_size_bytes(tp));
	fprintf(F, "  alignment:  %2u Bytes,\n", get_type_alignment_bytes((ir_type*)tp));
	if (is_atomic_type(tp) || is_Method_type(tp))
		fprintf(F, "  mode:       %s,\n",  get_mode_name(get_type_mode(tp)));

	fprintf(F, "\n\n");
}

void dump_types_as_text(FILE *const out)
{
	for (size_t i = 0, n_types = get_irp_n_types(); i < n_types; ++i) {
		const ir_type *type = get_irp_type(i);
		dump_type_to_file(out, type);
	}
}

void dump_globals_as_text(FILE *const out)
{
	const ir_type *global_type = get_glob_type();
	for (size_t i = 0, n_members = get_class_n_members(global_type);
	     i < n_members; ++i) {
		const ir_entity *entity = get_class_member(global_type, i);
		dump_entity_to_file(out, entity);
	}
}
