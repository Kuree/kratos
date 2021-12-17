typedef struct packed {
    logic [31:0] value1;
} struct1;

typedef struct packed {
struct1 value2;
} struct0;

module mod (
);

struct0 v;
struct0 [3:0] v_array;
assign v.value2.value1 = 32'h1;
assign v_array[0].value2.value1 = 32'h1;
endmodule   // mod

