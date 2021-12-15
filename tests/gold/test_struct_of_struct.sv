typedef struct packed {
    logic [31:0] value1;
} struct1;

typedef struct packed {
struct1 value2;
} struct2;

module mod (
);

struct2 v;
assign v.value2.value1 = 32'h1;
endmodule   // mod

