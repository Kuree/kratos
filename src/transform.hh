#ifndef KRATOS_TRANSFORM_HH
#define KRATOS_TRANSFORM_HH

#include "generator.hh"

namespace kratos {
void fix_assignment_type(Generator* top);

void zero_out_stubs(Generator* top);

void zero_generator_inputs(Generator* top);

void create_module_instantiation(Generator* top);

void create_interface_instantiation(Generator *top);

void decouple_generator_ports(Generator* top);

void change_property_into_stmt(Generator *top);

void remove_event_stmts(Generator *top);

void lift_genvar_instances(Generator *top);

void port_legality_fix(Generator *top);

void change_port_bundle_struct(Generator* top);

void realize_fsm(Generator* top);

void sort_stmts(Generator* top);

void ssa_transform_fix(Generator *top);


}  // namespace kratos

#endif  // KRATOS_TRANSFORM_HH
