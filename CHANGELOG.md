# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.0.16] - 2019-10-06
### Added
- Add handle name to FSM state
- Add kratos-vscode launch json example
- Add _kratos namespace doc generation
- Add ability to insert debug info at the beginning of the list
- Add breakpoint on clock
- Add support for parameter variable width (#97)
- Add abspath to fs util
- Add C implementation of `get_fn_ln` and expose it to Python (#98)

### Changed
- Split debug table generation to support kratos-runtime
- Refactor table implementation code for kratos-runtime
- Remove the name calculation logic; this will be handled in kratos-runtime
- Automatically infer active low/high and run analysis on it
- Use `signed'` instead of system function `$signed`
- Produce SystemVerilog package when outputting in a directory (#96)

### Fixed
- Fix a bug in sliding through fsm dot graph generation
- Fix a bug in port decouple when the expr is larger than 2
- Fix a bug where two child generators wire to each other may cause an exception about wiring

## [0.0.15] - 2019-09-18
### Added
- Add ability to add function call var to statement block in python
- Add handle name to variables/generators
- Add symbol table extraction
- Add hashing for function call
- Add ability to output files per modules with proper include header (#86)
- Add support for initial block
- Add support for test bench generation; add property assertion
- Add pass to detect non-synthesiszable components (#84)
- Add integration to kratos-runtime
  - SQLite3 integration
  - Breakpoint injection
  - Design database dump
- Add pass to analyze latch in `always_comb` and `always_ff`.

### Changed
- `clang-tidy` will run through `kratos` target
- DPI call by default won't have any type

### Fixed
- Fix a bug where DPI call won't be generated properly when the arg is const
- Fix FSM code gen produces latch.

## [0.0.14] - 2019-08-25
### Added
- Add ability to slice variable with another variable (#73)
- Add ability to sort top level assignments, off by default (#74)
- Add ability to comment on any IR node (#72)
- Add SystemVerilog keyword checker
- Add ability to mark top level always block
- Add support for packed array (#78)
- Add active high/low check
- Add dpi from C/C++ and Python (#83). Python interface is done throug kratos-dpi.
- Add support for nested FSM

### Changed
- Refactor the Python binding code to reduce binary size
- Exceptions are more informative
- Remove redundant replace code in generator.
- Improve the Python binding on generator name/instance_name change
- Empty generator name is handled properly
- FSM now requires a start state

### Fixed
- Fix pass through module with cloned modules (#79)
- Fix move_src/move_sink for sliced variables
- Fix the variable parent calculation (#77)
- Fix enum variable code gen

## [0.0.13] - 2019-08-11
### Fixed
- Fix a bug where sliced ports cannot be connected properly using `self.wire()`

## [0.0.12] - 2019-08-09
### Added
- Automatic Moore -> Mealy FSM conversion (#69)
- Combinational function block from Python. The argument order are the same
  as in Python (#70)
- Function calls as expr or stmt
- A pass to analyze return statements inside function block

### Changed
- Constant creation no longer tied to Generator object itself.
- `const(value, width)` and `Const[width](value)` syntax sugar to create constant in Python (#70).
- `pyast` now evaluates based on the caller's `locals` and `globals`.
- Use `Var` as a base-class to reduce binary size
- helper function such as `signed` is moved to `util` submodule.

## [0.0.11] - 2019-08-03
### Added
- Port bundles and a pass to convert port bundle to packed struct
- Named code blocks
- Add enum.
- Add class-class object FSM and full debugging.

### Changed
- `__eq__` can be used to compare numbers
- All `case` will be `unique case`.
- Most tests will have gold files to compare with.

### Fixed
- Fixed slicing bugs in `move_src_to` and `move_sink_to`.
- Fixed one extra pass in the pass manager.

## [0.0.10] - 2019-07-30
### Added
- Ternary op
- `reg_next` implementation
- Ability to add code block in `__init__` as nexted function
- Expose helper function `move_src_to` and `move_sink_to` to Python.
- Add an efficient replace to generator
- Add zero out input pass

### Changed:
- Simplify how posedge is used in Python.
- Simplify `always` interface

### Fixed:
- verify connectivity pass

## [0.0.9] - 2019-07-27
### Added
- Parallel visit framework for IR (#22)
- Remove unused stmt pass
- API to control how many CPUs to use in compilation
- Insert pipeline registers pass
- Debug info in if statement
- Array interface up to 2D array
- Lots of helper functions in Python front-end, including `zext`, `input` etc.

### Changed:
- Remove `PortArray` since the array interface is unified.
- `PassManager` is refactored. Users now have the complete freedom on what passes
  to run and reuse (#54).
- Unique naming function is changed so that if will attempt to create names without
  `count`.
- All extern modules have been updated to the latest.

### Fixed
- Fix `remove_unused_var` (#55).
- Fix `move_src_to` due to the changes of where to store the statements
- Fix port array code gen
- Fix code gen bug in if statement
- Fix pyast statement generation for nested statements


## [0.0.8] - 2019-07-25
### Added
- Proper source code distribution for compiling form scratch (PyPI)
- Array support variable declaration in generator
- ScopedStatement for better IR and code quality (#52)
- `ctest` to travis CI.
- Add more robust merge wire logic
- Lots of syntax sugar in Python front-end (#53)
- Add `clog2()`

### Changed
- Generator instance has to be unique in C++
- Add statement will return itself in reference
- Remove `assign()` side-effects (#48)
- Split Python bindings into multiple files to speed up the build process.

### Fixed
- Generator name is wrong in Python front-end
- Incorrect cache logic in `combinational()` and `sequential()`
- Fix a bug in source/sink movement due to the change in how connections are stored in slices.

## [0.0.7] - 2019-07-21
### Added
- Port Assignment check in SV codegen.
- Macos build on travis

### Changed
- remove slang dependency (#44).
- Code adjustment to make the code base cross-platform.

### Fixed
- Port const test

## [0.0.6] - 2019-07-20
### Added
- Stmt remove APIs (#41).
- API doc generation.
- `kratos` namespace in C++ source files (#37)

### Changed:
- IR attributes share the memory pointer
- Rename AST to IR.

### Fixed
- `instance_name` in the python `Generator` class
- Parallel hashing needs to use leveled generators.
- Generator unique names logic was wrong.
- Typos in documentation (#40).

## [0.0.5] - 2019-07-19
### Added
- More comprehensive documentation that covers the statements.
- Add visual debugger through `kratos-debug`.
- Add full support for attributes on IR node (#33).
- Parallel hash implementation (#27).
- Merge wire pass (#38).
- More debugging info related to module instantiation.
- Add helper function to create combinational/sequential blocks.

### Changed:
- Adjusted `clone`/`create` interface (#36)

### Fixed:
- Decouple port wires pass naming.

## [0.0.4] - 2019-07-16
### Added
- Documentation for most of the interfaces (#28)
- Support for SystemVerilog Packed Struct in port interface (#20)
- Debug info for fanout pass.
- Add variable and parameter proxy (#30)
- Add type cast interface (#31)
- Helper function to produce the verilog file

### Changed:
- `clone`/`create` interface has been improved (#32). A lot of work still need to be done.
- `signed` is now created using the new casting interface.

### Fixed
- Pass through module removal pass will sometimes remove modules that perform simple arithmetic.
- Fix a bug where module instantiation will cause infinite loop.

## [0.0.3] - 2019-07-07
### Added
- `PortProxy` to mimic gemstone interface
- `create()` helper function to create clones efficiently

### Fixed
- `is_cloned` setting during cloning
- `VarSlice` string during code gen.

## [0.0.2] - 2019-07-06
### Added
- Static evaluation on `if` and `for` statements.
- Hashing to external verilog (#2).
- Skip hashing if the generator is unique (#3).
- Collapse else if into actual else if in verilog (#4).
- Bypass python's lack of switch statement (#5).
- Add a way to specify verilog stubs (#6).
- Add cache to instantiate generators (#11).
- Transform == into eq call (#14).
- Add switch code gen (#15).
- Add pass through module detection and removal pass (#17).
- Add pass to remove chains of fan-out 1 wires (#18).
- Add a way to manage passes (#19).
- Add full trace of statements for debugging (#24).

### Changed
- Verilog code generation is refactored to be more consistent with each other (#1)
- Refactor how instance name is done (#7).
- Unify comb and seq add interface in Python (#16).
- Refactor ast visit (#21).
- Allow arbitrary for loop (#22).
- Refactor how sources and sinks are handled in slices (#25).

### Fixed
- Hashing not picking up the variable width (#8).
- Detect the output being used as a register (#10).
- Extra "end" for else if statement (#12).

## [0.0.1] - 2019-06-27
### Added
- Initial release of kratos.

