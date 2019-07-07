# Kratos
[![Build Status](https://travis-ci.com/Kuree/kratos.svg?branch=master)](https://travis-ci.com/Kuree/kratos)
[![PyPI - Format](https://img.shields.io/pypi/format/kratos.svg)](https://pypi.org/project/kratos/)
[![PyPI - Version](https://badge.fury.io/py/kratos.svg)](https://pypi.org/project/kratos/)

Kratos is a hardware design language written in C++/Python. It differentiates itself with the following
design philosophy:
- Fully debuggable: users can see a trace of every passes on every verilog statement.
- Highly efficient: Python frontend powered by Modern C++ binding. Designed with multi-processing in mind.
- Human-readable verilog: we know how difficult it is to read machine generated verilog. We have it covered.
- Generator of generators: Every python object is a generator that can be modified at any time,
  even after instantiation. This allows complex passes on the generators without ripping old structure apart.
- Keep the good parts of verilog: The `always` block in behavioral verilog is close to other programming
  languages. Kratos allows you to write python code similar to behavioral verilog
- Static elaboration: kratos allows user to write parametrized code, even in the `always` block.
- Type checking: kratos check the variable types for each assignment to make sure there is no implicit conversion.

## Install
```
pip install kratos
```

To build it from scratch, you need a `C++17` compatible compiler, such as `g++-8`.

## Examples
Here are some examples to showcase the ability of kratos

### Asnyc Reset Register
Python code that parametrizes based on the `width`. Notice that we specify the
sensitivity of the `always` block when defining `seq_code_block`.
```Python
class AsyncReg(Generator):
    def __init__(self, width):
        super().__init__("register")

        # define inputs and outputs
        self._in = self.port("in", width, PortDirection.In)
        self._out = self.port("out", width, PortDirection.Out)
        self._clk = self.port("clk", 1, PortDirection.In, PortType.Clock)
        self._rst = self.port("rst", 1, PortDirection.In,
                              PortType.AsyncReset)
        self._val = self.var("val", width)

        # add combination and sequential blocks
        self.add_code(self.seq_code_block)

        self.add_code(self.comb_code_block)

    @always([(BlockEdgeType.Posedge, "clk"),
             (BlockEdgeType.Posedge, "rst")])
    def seq_code_block(self):
        if ~self._rst:
            self._val = 0
        else:
            self._val = self._in

    def comb_code_block(self):
        self._out = self._val
```
Here is the generated verilog
```Verilog
module register (
  input  clk,
  input [15:0] in,
  output reg [15:0] out,
  input  rst
);

logic  [15:0] val;

always @(posedge clk, posedge rst) begin
  if (~rst) begin
    val <= 16'h0;
  end
  else begin
    val <= in;
  end
end
always_comb begin
  out = val;
end
endmodule   // register
```

### Fanout module
This is an example to showcase the kratos' static elaboration ability in `always` block.
In practice we would not write it this way.
```Python
class PassThrough(Generator):
    def __init__(self, num_loop):
        super().__init__("PassThrough", True)
        self.in_ = self.port("in", 1, PortDirection.In)
        self.out_ = self.port("out", num_loop, PortDirection.Out)
        self.num_loop = num_loop

        self.add_code(self.code)

    def code(self):
        if self.in_ == self.const(1, 1):
            for i in range(self.num_loop):
                self.out_[i] = 1
        else:
            for i in range(self.num_loop):
                self.out_[i] = 0
```
Here is generated verilog
```Verilog
module PassThrough (
  input  in,
  output reg [3:0] out
);

always_comb begin
  if (in == 1'h1) begin
    out[0:0] = 1'h1;
    out[1:1] = 1'h1;
    out[2:2] = 1'h1;
    out[3:3] = 1'h1;
  end
  else begin
    out[0:0] = 1'h0;
    out[1:1] = 1'h0;
    out[2:2] = 1'h0;
    out[3:3] = 1'h0;
  end
end
endmodule   // PassThrough
```

## Ecosystem
Similar to [Magma](https://github.com/phanrahan/magma), kratos has its own ecosystem to program
behavioral verilog in Python. They are named after sons of Titans in Greek mythology.

[kratos](https://github.com/Kuree/kratos) is a programming model for building hardware. The main
abstraction in kratos in a `Generator`. `Generator` can be modified at any time through passes.

[zelus](https://github.com/Kuree/zelus) is a library of useful generators, such as mux and decoder.
They are designed to be as efficient as possible.