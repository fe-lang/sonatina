# Sonatina

Sonatina is a compiler backend specialized for smart contracts.  

Sonatina is really early stage in development, so do NOT use it for production!


## Project layout
`sonatina` consists of several crates.
* `codegen`: The main crate of `sonatina`, providing builder for IR modules and functions, optimization passes, instruction selection DAG, and binary code emitting.
* `filecheck`: Provides test runner for `filecheck` and test fixtures.
* `interpreter`: Interpreter for `sonatina` IR, this is mainly for testing transformation passes.
* `ir`: `sonatina` intermediate representation.
* `object`: Provides abstract object file format for linker.
* `parser`: Parser for `sonatina` IR, this is mainly for `filecheck` test.
* `triple`: Provides target triple for smart contracts.
* `verifier`: Verifier for `sonatina` IR, this is mainly for testing transformation passes.

## TODO
* [ ] IR verifier
* [ ] ISel DAG
* [ ] [Global Stack allocation](https://www.semanticscholar.org/paper/Global-Stack-Allocation-%E2%80%93-Register-Allocation-for-Shannon/c8efedfa6907e31cb2a30d5494f5353b8689e8b9) for EVM
* [ ] Intrinsics
* [ ] Object
* [ ] Linker

## Test
Run `test_all.sh`.