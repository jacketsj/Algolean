# Algolean

Algolean is a library of algorithms and complexity theory, defined broadly to include much of the Algorithms and Complexity theory literature. It is written in the lightweight free monad version of what I call the "query-combinator" model. It currently consists of code that lies in several CSLib pull requests. The framework can encompass standard and custom models in algorithms theory, ranging from RAM and Turing machines, to circuits, and even niche models like the Robertson-Webb cake cutting model. The intent is to provide an all-encompassing framework of models and reductions between them. Complexity claims are relative to the operations exposed as queries and their declared costs; pure Lean work is uncharged, so the chosen query language is part of the auditable specification.

`Algolean.Models.RAM` is a small uniform machine model shared by integer RAM, word RAM, and real
RAM. Programs are finite instruction lists with jumps, so one fixed program can contain
input-dependent loops. Data and address registers have separate types, avoiding a hidden
real-to-natural conversion in the real RAM. The existing square-root, power, exponential,
logarithmic, trigonometric, root, and floor extensions also have typed program instructions.

For auditable existential algorithm statements, use the APIs added under
`Algolean.Complexity.MachineProblem` and `Algolean.Complexity.RAMProblem`:

- `MachineProblem.HasFixedMachineAlgorithm` uses the sealed two-bank `StructuredRealRAM`, closed
  structural layouts, canonical zero initialization, relational outputs, and one costed halting
  trace for both correctness and resources.
- `IntegerRAM.Problem.HasFixedMachineAlgorithm` and
  `WordRAM.Problem.HasFixedMachineAlgorithm` provide the corresponding fixed-program claims for
  native cell-array inputs. Word width and address-space fit are explicit.
- `HasNonuniformFamily` and `HasUniformlyGeneratedFamily` are separate from fixed-program claims
  and carry code-size (and, for generated families, generation) obligations.
- `HasMonteCarloAlgorithm` and `HasLasVegasStepAlgorithm` fix the program before inputs and random
  tapes; Monte Carlo uses worst-case tape cost, while Las Vegas exposes the scalarized expectation.
- `QueryProblem.HasQueryAlgorithm` is the explicit name for the existing `Prog` claim, where pure
  Lean work between emitted queries is uncharged.

`Algolean.Compiler.CFG` supplies first-order labeled blocks, shared branch joins, backward runtime
loops, typed register handles, numeric-jump assembly, and an exact emitted-code-size theorem.
`Algolean.Audit.Algorithm` provides manifest metadata that records the claim and cost source;
`#algorithm_audit manifestName` prints its compact report.
Typed oracle contracts use canonical query/answer layouts and explicit transfer costs in
`Algolean.Models.StructuredRealRAM.Oracle`; admissible-oracle non-vacuity is a separate proposition.

The checked module [`Algolean.Tutorial`](Algolean/Tutorial.lean) explains how to define a query
language, prove functional correctness and cost, package a problem statement, choose between
`Prog` and a fixed RAM program, and audit the resulting guarantee. Checked acceptance examples for
the new interfaces are in
[`AlgoleanTests.ExistentialAlgorithms`](AlgoleanTests/ExistentialAlgorithms.lean).

## Nomenclature
`Algolean` is a pun. It is intended to be read in two ways.
* "Algo" + "Lean" : A library of algorithms and complexity theory in lean
* "Algol" + "ean" (pronounced like "ene") : To pay homage to Algol which motivates a lot of modern algorithmic pseudocode, and whose simplicity this framework hopes to mimic (hence the "ene").



## Acknowledgements
For timing we build on top of the Writer monad `AddWriter` that was proposed in CSLib as the TimeM model by Sorrachai Yingchareonthawornchai and whose API was perfected by Eric Wieser. 

Further, Eric Wieser substantially assisted with the improvement of the implementation through extensive and detailed PR reviews. 
