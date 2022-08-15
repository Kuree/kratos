#ifndef KRATOS_OPTIMIZE_HH
#define KRATOS_OPTIMIZE_HH
#include "generator.hh"

namespace kratos {

// These code below are optional passes that make the code more readable
void transform_if_to_case(Generator* top);

void merge_if_block(Generator* top);

void remove_fanout_one_wires(Generator* top);

void remove_pass_through_modules(Generator* top);

void merge_wire_assignments(Generator* top);

void insert_pipeline_stages(Generator* top);

void auto_insert_clock_enable(Generator *top);

void auto_insert_sync_reset(Generator *top);

}  // namespace kratos

#endif  // KRATOS_OPTIMIZE_HH
