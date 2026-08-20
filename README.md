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
  trace for both correctness and resources. Its typed certificate exposes the concrete witness.
- `IntegerRAM.Problem.HasFixedMachineAlgorithm` and
  `WordRAM.Problem.HasFixedMachineAlgorithm` provide the corresponding fixed-program claims for
  native cell-array inputs. Word width and address-space fit are explicit.
- `HasNonuniformFamily` is separate from fixed-program claims and bounds both instruction count and
  full description size, including literals and jump targets. `HasUniformlyGeneratedFamily` uses
  one sealed structured-real-RAM generator and materializes the target's canonical binary
  serialization in charged output memory. The caller-defined alternative is honestly named
  `HasFamilyRelativeToGeneratorSpecification`; it is not an absolute uniform claim.
- `BitRandomizedMachineProblem.HasMonteCarloAlgorithm` uses a library-fixed iid fair-bit tape law
  whose length depends only on represented input size. Arbitrary input-dependent laws survive only
  under `InputDependentTapeProblem` names ending in `RelativeToTapeLaw`.
- `QueryProblem.HasQueryAlgorithm` is the explicit name for the existing `Prog` claim, where pure
  Lean work between emitted queries is uncharged.

`Algolean.Compiler.CFG` supplies first-order labeled blocks, shared branch joins, backward runtime
loops, typed register handles, numeric-jump assembly, and an exact emitted-code-size theorem.
`Algolean.Audit.Algorithm` records and prints every manifest field: layouts, both code-size metrics,
generation, randomness, oracles, extensions, machine conventions, claim kind, and cost source.
`#algorithm_audit publication` consumes a typed structured-, integer-, or word-RAM publication and
computes code sizes from its actual certificate; `#algorithm_manifest metadata` prints legacy
name-only navigation metadata without claiming consistency. Modules executing either command need
a `meta import Algolean.Audit.Algorithm` under Lean's module system.
Typed oracle contracts use canonical query/answer layouts and layout-derived answer-transfer cell
counts in `Algolean.Models.StructuredRealRAM.Oracle`; admissible-oracle non-vacuity is separate. The
oracle module remains a contract scaffold rather than a same-trace oracle-machine claim.

Machine conventions are intentionally distinct. `IntegerRAM` is an ordinary unit-cost RAM with
unbounded signed integer data and natural addresses. `WordRAM` has explicit fixed-width modular
words and addresses. `StructuredRealRAM` has exact reals plus an unbounded unit-cost natural bank,
totalized real division, truncating natural subtraction, rational source literals, and
represented-cell input size. These are different complexity models, not interchangeable labels.

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
