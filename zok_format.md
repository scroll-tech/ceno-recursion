# Custom Zokrates File Format
This file provides an overview of the Zokrates format used by CoBBl

## `.zok` Files
These are the main code used to emit constraints. The syntax largely resembles modern high-level languages. See `zok_tests\benchmarks` for some examples. Below I list a few unique features:

#### Arrays and Pointers
Arrays are treated as pointers and multi-dimensional arrays are accessed through pointer redirection. **Similar to C, array accesses are simply pointer addition, and there are no out-of-bound checks within the constraints.** Arrays can be declared in two ways:
* `array_decl <type>[<arr_size>]` allocates `arr_size * sizeof(type)` entries to the memory without initialization. Arrays of higher-dimensions are equivalent to arrays of pointers: `array_decl <type>[<arr_size0>][<arr_size1>]` allocates `arr_size0 * sizeof(field)` entries. _The verifier only accepts the proof if every allocated memory cell is initialized_, the responsbility of which lands in the hand of the programmer.
* `<type>[<size>] arr = [...]` assigns the array variable `arr` to the right-hand side array, which can be:
  * Inline arrays: `[1, 2, 3, 4, 5]`, etc, or
  * Array initializers: `[1; x]`, etc, where `x` can be a constant or a variable

  `<type>` must match with the entry type in RHS. `<size>` can be a constant, variable, or 0 (indicates unknown) **and ONLY SERVES AS A LABEL for the programmer**. E.g., `field[x] arr = [0; y]` allocates an array of size `y` and ignores `x` completely.

  Nested arrays can be constructed through similar construction, **DO NOT USE ARRAY INITIALIZERS ON NESTED ARRAYS**: `[[0; x]; y]` copies the same pointer `y` times, think of Python.

* **Read-only** arrays are a special type, marked by adding `ro` after `[`: e.g. `field[ro 5] arr = [ro 0, 1, 2, 3, 4]`. Read-only arrays cannot be assigned to regular array variables, or vice-versa. One should always use read-only arrays if possible.

#### Witness Statements
`witness <type> x` reads out the next witness (see `.witness` files) into `x`.

## `.input` Files
Input files list values of all input variables of the main function. All inputs must be listed in the **exact same order** as the main function. Every line is consisted of a variable name and a value, one of the three forms (note the spaces and NO COMMAS):
* `<name> <val>`
* `<name> [ <val> <val> <val> ]`
* `<name> [ro <val> <val> <val> ]`

The file terminates with a single line `END`, without linebreak.

## `.witness` Files
Witness files list witnesses used by the Prover, separated by space or linebreak. Whenever P encounters a `witness` statement (regardless of alive or dead), it reads in the next value in the `.witness` file. This means that to generate the `.witness`, one should know the exact execution path P takes.

The file terminates with a single line `END`, without linebreak.