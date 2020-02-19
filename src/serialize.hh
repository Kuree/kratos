#ifndef KRATOS_SERIALIZE_HH
#define KRATOS_SERIALIZE_HH

#include <cereal/types/common.hpp>
#include <cereal/types/map.hpp>
#include <cereal/types/memory.hpp>
#include <cereal/types/set.hpp>
#include <cereal/types/tuple.hpp>
#include <cereal/types/unordered_map.hpp>
#include <cereal/types/unordered_set.hpp>
#include <cereal/types/utility.hpp>
#include <cereal/types/vector.hpp>
#include <istream>
#include <memory>
#include <ostream>

#include "context.hh"
#include "fsm.hh"
#include "generator.hh"
#include "interface.hh"
#include "port.hh"
#include "tb.hh"

namespace kratos {

void serialize(std::ostream &ostream, std::shared_ptr<Context> context);

void serialize(std::ostream &ostream, std::shared_ptr<Generator> generator);

std::shared_ptr<Generator> load_generator(std::istream &stream);

}  // namespace kratos

template <class Archive>
void serialize(Archive &ar, kratos::Generator &gen) {
    ar(cereal::base_class<kratos::IRNode>(&gen), gen.get_lib_files(),
       cereal::defer(gen.get_context_ptr()), gen.get_vars_ptr(), gen.get_port_names(),
       gen.get_params(), gen.get_exprs(), gen.get_port_bundle_mapping(), gen.get_stmst(),
       gen.get_children(), gen.get_children_names(), gen.get_children_debug(),
       gen.get_children_comments(), gen.get_parent_generator_ptr(), gen.is_stub(), gen.external(),
       gen.get_clones(), gen.is_cloned(), gen.has_instantiated(), gen.get_named_blocks(),
       gen.get_enums(),
       /* TODO add fsms */
       gen.functions(), gen.get_func_index(), gen.get_call_vars(),
       cereal::defer(gen.get_def_instance_ptr()), gen.get_auxiliary_vars(), gen.interfaces(),
       gen.properties());
}

template <class Archive>
void serialize(Archive &ar, kratos::Context &context, const uint32_t) {
    ar(context.get_modules());
    ar(context.get_generator_hash());
    ar(context.max_instance_id());
    ar(context.max_stmt_id());
    ar(context.enum_defs());
}

template <class Archive>
void serialize(Archive &ar, kratos::Var &var) {
    ar(cereal::base_class<kratos::IRNode>(&var), var.var_width(), var.size(), var.is_signed(),
       var.sinks(), var.sources(), var.type(), var.get_concat_vars(), var.get_slices(),
       var.before_var_str(), var.after_var_str(), var.explicit_array(),
       cereal::defer(var.get_param_ptr()), var.is_packed(), cereal::defer(var.get_generator_ptr()),
       var.get_casted(), var.get_extended());
}

#endif  // KRATOS_SERIALIZE_HH
