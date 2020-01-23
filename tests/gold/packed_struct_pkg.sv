`include "packed_struct_pkg.svh"

import packed_struct_pkg::*;
module packed_struct (
  input config_data in,
  output config_data out
);

config_data v;
assign out = in;
assign v = in;
endmodule   // packed_struct
