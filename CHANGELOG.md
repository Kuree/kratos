# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
## [0.0.31] - 2020-09-14
### Added
- Added packed struct array
- Allow parameters to be "type", advanced use only
- Enhance copy port definition by copying parameter as well
- Add enum, struct, and raw_type to copy port definition
- Allow parameter setting in add_child function
- Add `__len__` to var, which has the same semantics as array size in Python
- Add multi-stage generation support. The context will keep track of already generated instances
- Allow additoinal frames for fn_ln inspection
- Add tests to run on examples
- Add ability to resize parameter at compile time (#159)
- Add support for parameter as variable width
- Add builtin tasks support, e.g., $clog2


### Changed
- Parameter value codegen is adjusted based on initial value
- case statement will have begin-end block if the single statement is not an assignment

### Fixed
- Fix var_width for packed struct (#157)
- Fix typo in ast (#158)
- Fix cerr printout using mutex lock
- Fix parameter propagation when flattening the instances
- Fix slice on parametrization with width
- Fix error message in interface valid varible name

## [0.0.30] - 2020-08-05
### Added
- Add helper functions to get connected ports
- Add async reset cast
- Add ability to specify parameter value when adding child generator
- Add iter support in port/var/param proxy (Python)
- Add parameter initial value
- Allow port types to be change during runtime in Python
- Add port creation with another port's definition in Python
- Add uart examples
- Add support for raw package import and raw parameter type
- Add helper function to tell if the port is connected or not
- Allow variable size to be parametrized by param
- Add pow op

### Changed
- Relax if to case restrictions
- Adjust param codegen
- Sort port by directions as well (grouping inputs and outputs)

### Fixed
- Fix stdfs linking if filesystem not found
- Fix complex expression with const generator
- Fix type in sram generator (#150)
- Fix value update in param chaining

## [0.0.29] - 2020-05-06
### Added
- More SVA actions, such as `cover`
- Add `src` attribute for yosys code generation

### Changed
- Simplified FSM code generation
- Disable parallel module instantiation

### Fixed
- Fix stmt access in passes, which may cause memory access error

## [0.0.28] - 2020-04-14
### Added
- A pass to automatically insert clock gating logic into the design
- A pass to automatically insert synchronous reset based on async reset logic
- Add helper function in Python to construct clock enable ports and type conversion
- Add port and var parametrized by array size as a Verilog Parameter
- Add statement clone logic
- Move scope eval to each ast transformer (#148)
- Add a switch to force loop unroll in python add_always
- Add find_attribute to simplify the attribute search

### Changed
- Refactor clear source and clear sinks so that the statements will be removed from parent

### Fixed
- Fix enum const generator assignment parent generated from FSM
- Fix a bug where the for loop may not be generated correctly

## [0.0.27] - 2020-03-21
### Added
- `always_latch` code generation and Python front-end
- Parametrized always blocks as function arguments (as kwargs)
- Allow slicing being used in the if condition in pyast

### Changed
- Update `to_magma` logic due to upstream changes in magma IO
- Refactor string join namespace

### Fixed
- Keep packed attribute when creating new expressions
- Fix a loop construction bug where a bit signal cannot be sliced
- Fix var casted as ports
- Fix move link with self loop
- Fix error message in add child generator

## [0.0.26] - 2020-02-24
### Added
- Allow top name to be changed when converting generator to magma circuit
- Add ability to output `BTOR2` via `yosys`. Notice that some of the semantics needs sv2v's conversion.
- Add support for `for` loops that can be converted into SystemVerilog `for` loops.
  This is only enabled when the generator is not in debug mode.
- Add `resize` function and resize as a new variable cast
- Add a pass to check top-level `if` statement in `always_comb` to make sure
  variables are inferred as D flip-flops in DC (#145.
- Add struct extract pass for `VarPacked`.

### Changed
- Refactor C++ core interfaces: `generator()` and `const` usage in simulator.
  This should not affect Python front end
- All Travis tests are moved to Github Actions.
- Refactor `debug` to `debug_fn_ln` flag in `verilog` function.
- Speed up CI builds by turning on debug mode (#144).

### Fixed
- Use generated name when storing generator variables
- Fix a bug where the top module is not in debug mode but child is during debug info dump

## [0.0.25] - 2020-02-02
### Added
- add bulking wiring when adding a child instance in python wrapper
- Add sanity check on width 0
- Add dedicated docker image for kratos testing
- Add source-level coverage report in xml cobertura format
  - ncsim
  - verilator
- Add insert verilator info to verilog function
- Add support for block comment in Python, which will turn into a normal comment stmt

### Changed
- Relax output port inline requirements
- Code base refactoring based on clang-tidy-9
- All C++ unit tests tested against valgrind
- Use to_string() instead of name when throwing an exception
- merge_if_block is off by default and need to turn on by an attribute
- Allow sequence-based property to be inserted into normal design
- util.py helper functions now support single arguments

### Fixed
- Fix nested fsm next state inferred as latch (#95)
- Fix a bug where explicit array is not passed down to the wrapper
- Fix bit select on logic
- Fix nested loop in pyast
- Fix line number tracking when merging code in Python side
- Fix a bug in the simulator where default case will hit seg-fault
- Fix array flattening logic when dumping debug database
- Fix [n, 1] slicing where the last dim is 1

## [0.0.24.3] - 2020-01-23
### Fixed
- Fix multi-driver algorithm again

## [0.0.24.2] - 2020-01-23
### Added
- Add logical operator, i.e. && and ||
- Add direct python code transform from short-circuited boolean ops to proper function calls
- Add additional support for passes in Python. Improve Attribute creation

### Fixed
- Fix the bug in nested var slice; the VarSlice class tried to walk the chain back, which is wrong
- Fix a multi-driver bug where you can have priority assignment in an combinational block

### Changed
- Refactor get tokens in C++

## [0.0.24.1] - 2020-01-22
### Added
- Add full docker build image ready for ncsim and verilator
- Add coverage report from both C++ and python code
- Expose more C++ to Python

### Changed
- Refactor get tokens in C++

## [0.0.24] - 2020-01-17
### Added
- Add a pass to extract all variable information
- Add spectrum-based fault analyser
- Add docker release for latest master build

### Changed
- Adjust `pybind11` remote.

### Fixed
- Fix a bug where a sliced vars is added as source instead of
  sink

## [0.0.23.4] - 2020-01-14
### Fixed
- Fix the same bug in mixed assignment check where a slice will trigger false positive result

## [0.0.23.3] - 2020-01-14
### Fixed
- Fix a bug in multi-driver detection where a slice will trigger false positive result

## [0.0.23.2] - 2020-01-13
### Added
- Add ability to generate old-style Verilog based on `sv2v`
- Add SRAM library generation as a native lib
- Add flatten pass to flatten N-D array for tools that don't support it
- Add a pass to extract registers names from the design

### Changed
- Drop Python 3.5 support
- Lower MacOS version requirement, thanks to miniconda
- Improved ternary code generation
- Loose decouple ports requirements (#132)

### Fixed
- Adjusted python pass order to check connectivity first before decouple the wires
- Get def instance if all the instances linked in the graph is cloned (#133)

## [0.0.23.1] - 2020-01-06
### Added
- Allow normal values to be casted to enum;
- Add strict type checking
- Add pass to check combinational loop (#87)
- Add raw string statement
- Add windows build and native wheel (#131)

### Changed
- Remove old verilog generation requirements
- C++ enum is now enum class

### Fixed
- Fix filesystem detection code on gcc-8

## [0.0.23] - 2019-12-20
### Added
- Use BSD-2 license
- Add a pass to detect multiple drivers
- Upload src files to pypi

### Changed
- Use old mac-os image but switch to gcc-8 for consistent result
- Refactor `always` to `always_comb` and `always_ff` for better semantics, and add warnings
  if absent.
- Python based tests are refactored to re-use pytest fixtures 

### Fixed
- Fixed a bug in var high calculation when the parent is a slice
- Various interface bug fixes

## [0.0.22.1] - 2019-12-10
### Added
- Add helper function to expose kratos interface to magma

### Changed
- Change port_type and port_direction to property in Python binding

## [0.0.22] - 2019-12-10
### Added
- Add ability to keep track of which definition has been generated from Python side

### Changed
- Use up to 50% of CPU when compiling Python binding
- Improve parameter list and DPI code gen (removing unnecessary spaces)
- Expose context binding to Python

## [0.0.21] - 2019-12-09
### Added
- SystemVerilog interface support (#123)
- Better integration ability to other Python-based generators
- Allow `enum` on port (public enum definition); #122
- Add context variables to `If` statement

### Changed
- Pause on clock not enabled by default
- Reduce verbosity in enum creation; sort enum by values, not by name
- Automatically detect `<filesystem>` availability
- Merge static elaboration passes with `for` and `if`.

### Fixed
- Numerous simulator issue fixes
- Fixed a known problem with astor-based code gen where long statement causes error (#125)

## [0.0.20] - 2019-11-07
### Added
- Add past transform to change exception into assertion (#116)
- Add a pass to fix the design hierarchy if Kratos is only used partially
- Add instance_id to breakpoint/assertin to support concurrency
- Add support for ndarray in kratos
- Add an event-driven IR-level simulator (#120)

### Changed
- Disable context variable if a particular fn_ln is given
- Gnerator ids are re-used acorss multile runs on dumped debug database
- Remove stmt after port decoupling

### Fixed
- Fix a bug where adding a child to an IR node may affect its visit order

## [0.0.19] - 2019-10-25
### Added
- Add old verilog style module definition code gen (also stub)
- Add comment node
- Add pass to move top level assignemtn to always_comb
- Add check for mixing packed/unpacked array
- Add helper function in port bundle for creating clock and reset (#110)
- Allow variable to be passed in always function
- Allow users realize fsm during design and expose state and enum variable
- Add a pass to find out signal drivers
- Add support not in pyast
- Add proper extension using SV syntax
- Add detection for duplicated enum names (#114)
- Add Python3.8 support
- Add a pass to merge if statement

### Changed
- Change the how comment works in top level blocks
- Change how packed variable works internally
- `get_local()` is now implement in C++
- Rename var/port packed  with packed struct
- Generator names are now checked for keywords
- if to case/switch only happens if it's fully specified or has trailing else (#115)

### Fixed
- Fix bug in port decoupling algorithm where variable meta doesn't get carried over
- Fix linked variable move (#105)
- Fix a bug where if predicate may not return a node in pyast

## [0.0.18.5] - 2019-10-14
### Added
- Add a pass to produce a verilog stub that can be fed into ancient systems
- Add automatic long assignment wrapping
- Add comment statement, which can be used in always block from Python

### Changed
- Syntax for python wrapper for comment has changed to avoid naming conflict

## [0.0.18.4] - 2019-10-14
### Added
- Add assertion for port/var accessing

### Changed
- remove os restriction on exception print ast_node;
- add check for stmt block add_stmt is null
- Put () around ternary

#### Fixed
- Fix wire merge stmt removal and assignment type
- Fix globals (with a hack on locals)
- Fix ne python binding

## [0.0.18.3] - 2019-10-13
### Fixed
- Fix reduction op width calculation

## [0.0.18.2] - 2019-10-13
### Added
- Add ability for wrapper class to accept wrapper class as stmt inputs

### Changed
- Refactor debug database logic to conform with the new spec in kratos-runtime

### Fixed
- fix a bug due to memory re-work in expression (left will be null)

## [0.0.18.1] - 2019-10-12
### Changed
- Refactor database table schema

### Fixed
- Fix complex expr to_string()
- Fix var used in if/switch target not registered as sinks.

## [0.0.18] - 2019-10-12
### Added
- Add variable indexing with explicit array

### Changed
- Fix memory model in the internal system. Should be leak free (#100)
- Change how port bundle is constructed
- Change debug database schema.

### Fixed
- Fix width calculation in a pass that involves with relational op
- Fix ternary construction

## [0.0.17] - 2019-10-10
### Added
- Add a pass to remove assertions
- Add a pass to remove empty code blocks
- Add a pass to inject exceptions on accertions
- Add a special flag in variable creation that create a 2D array when size=1
- Allow assertions to have breakpoint statements

### Changed
- Parameter of parameters has better implementation
- Revert the pass on inserting breakpoints into always_ff block

### Fixed
- Fix a bug in parallel visit in connection debug pass by adding mutex
- Fix port decoupling parameter bug.
- Fix a bug where concat variables won't be renamed in port decoupling

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

