# CoqLex

These source files contain the implementation, models, and proof of correctness of a formally verified lexers. A verified lexer (or RecLexer) is a lexer that satisfies correctness properties about positions and character consumption. We implemented a constructor for RecLexer from a specification : a list of regular expressions and actions.

The example/ directory contains specifications for [JSON](https://medium.com/@aleksandrasays/tutorial-parsing-json-with-ocaml-579cc054924f), [Mini-ML](https://github.com/rinderknecht/Mini-ML/blob/master/Lang0/Lexer.mll) and an example of a lexer that can loop.

## Building the lexical analyzer
### Prerequisites
Coqlex builds on the following dependencies:

- 4.03 ≤ OCaml ≤ 4.07.1
- Coq = 8.9.0
- Menhir = 20200624
- [Regexp-coq](https://github.com/coq-contribs/regexp)

### Build
To compile, use the makefile and the following command:

`make`

### Usage
To use the lexer-generator run the following command :

`a.out file_dir/vl_filename`

This command generates 3 versions of the specified lexer in `file_dir`. Each version contains 
- A file named `CoqLexer.v` that performs the lexical analysis
- Files named `lexer.ml` and `main.ml` that contain utility functions to call the lexer using lexbufs or strings.
- A script `compile.sh` to extract and compile the lexical analyzer

## Implementation details
- `MachLen.v`, `MachLenSpeedUp.v` (for v0.1) and `MachLenSpeedUp2.v` (for v0.2) contain the implementation and the proofs for score computation
- `SimpleLexerGenerator.v` contains the definitions, the implementations and proofs for election, action, action interpretation.
- `SimpleLexerGeneratorSpeedUp.v` and `SimpleLexerGeneratorSpeedUp2.v`contain the the implementation and the proofs for election optimizations
- `UsefullProfs.v` contains some helper proofs for `SimpleLexerGenerator.v`
- `Lexer.v` is the implementation of the lexer to build the generator
- `Parser.vy` is the parser specification used to build the generator
- `lexerUtils.ml` and `parserUtils.ml` are helper files that help to use to manage lexbufs
- `coqlex.ml` is the entrypoint of our software. It reads the input file and handle generations

