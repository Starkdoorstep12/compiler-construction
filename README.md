# Compiler Construction

A compiler implemented in Racket that progressively lowers a series of
increasingly feature-rich source languages (integers, variables, conditionals,
loops, vectors, functions, lambdas, and gradual/dynamic typing) down to x86
assembly, through a sequence of well-defined compiler passes.

## Project Structure

- `compiler.rkt` - the main compiler, defining the passes that translate
  each source language down toward x86 assembly.
- `interp-*.rkt` - interpreters for each intermediate language (`L*`) and
  C-like language (`C*`) used to verify passes at each stage.
- `type-check-*.rkt` - type checkers for each language variant.
- `runtime.c` / `runtime.h` - the runtime system linked with compiled
  programs (garbage collection, I/O, etc.).
- `utilities.rkt` - shared utilities, including `interp-tests` and
  `compiler-tests` used for testing passes and generated assembly.
- `run-tests.rkt` - the test runner that exercises the compiler passes
  against the test suite.
- `tests/` - test programs and expected results for each language stage.

## Setup

### 1. Clone the repository

```bash
git clone https://github.com/Starkdoorstep12/compiler-construction.git
cd compiler-construction
```

### 2. Compile the runtime

The `runtime.c` file must be compiled and linked with the assembly code
produced by the compiler:

```bash
gcc -c -g -std=c99 runtime.c
```

This produces `runtime.o`. The `-g` flag includes debug info for use with
`gdb`/`lldb`.

On a Mac with an M1/ARM processor, compile for x86_64 instead:

```bash
gcc -c -g -std=c99 -arch x86_64 runtime.c
```

### 3. Run the compiler tests

```bash
racket run-tests.rkt
```

Alternatively, open and run `run-tests.rkt` in DrRacket.

`interp-tests` (used internally by the test suite) checks the intermediate
representations at each pass, while `compiler-tests` checks the final
generated x86 assembly output.

### 4. Build and run a compiled program

Suppose the compiler translates a Racket program `foo.rkt` into an x86
assembly file `foo.s`. To produce a runnable executable:

```bash
gcc -g runtime.o foo.s -o foo
./foo
```

## License

See [LICENSE](./LICENSE).
