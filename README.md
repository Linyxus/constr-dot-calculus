# DOT Calculus with Constraints
 Soundness proof for DOT calculus enhanced with constraints.
 
 The proof is based on the [DOT soundness
 proof](https://github.com/amaurremi/dot-calculus/tree/master/src/simple-proof).
 
## Extending DOT with Constraint

- [ConstrLang.v](src/constr-dot/ConstrLang.v) contains constraint language
  definition, constraint interpretation, entailment definition and a bunch of
  entailment laws. It implements constraint interpretation in an assignment-free
  manner.
- [ConstrLangAlt.v](src/constr-dot/ConstrLangAlt.v) contains the standard way to
  implement constraint languages. It implement ground assignments with `env` and
  interpret the constraint based on them. It is in progress and only have some
  half-way definitions.
- [ConstrTyping.v](src/constr-dot/ConstrTyping.v) defines the type system
  with constraints. <!-- It currently use the definition in -->
  <!-- [ConstrLang.v](src/constr-dot/ConstrLang.v). -->
- [ConstrSafety.v](src/constr-dot/ConstrSafety.v) states and proves the
  soundness theorems (preservation and progress) for cDOT.

