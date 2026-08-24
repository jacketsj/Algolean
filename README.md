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
- `BitRandomizedMachineProblem.HasMonteCarloAlgorithm` uses a hidden, lengthless source with the
  library-fixed iid fair-bit product law. A program can observe it only through a closed, charged
  `randBit` instruction; random draws and output come from the same trace. Arbitrary input-dependent
  laws survive only under `InputDependentTapeProblem` names ending in `RelativeToTapeLaw`, and
  observable finite bit-count schedules only under `ScheduledBitTapeProblem` names ending in
  `RelativeToBitCountSchedule`.
- `UniformRealRandomizedMachineProblem.HasMonteCarloAlgorithm` is a separate stronger profile with
  a hidden lengthless product source of exact uniform `[0,1]` values and one closed, charged
  `sampleUniform` instruction. Other distributions must be implemented from named primitives or
  introduced as separately disclosed machine profiles.
- `QueryProblem.HasQueryAlgorithm` is the explicit name for the existing `Prog` claim, where pure
  Lean work between emitted queries is uncharged.

For structured ordinary Word-RAM claims, `WordRAM.StructuredProblem` stores closed model-specific
`WordLayout` syntax. `WordRAM.CanonicalLayout w α` contains only that syntax: raw `Nat`, `Int`,
`Rat`, and `Real` have no implicit one-word layouts. The library provides explicit bounded words,
multiword integers/rationals, address-fitting arrays, matrices/tensors, sparse tables, bit sets,
permutations, partitions, forests, and named edge-list/dart-list/CSR/adjacency-matrix graph formats.
Conversions between physical formats are charged algorithms. `UniformAlgorithmCertificate` uses
one width-independent finite template rather than an arbitrary `Nat → Program` family.

`ProcedureContract`, `RelativeAlgorithmCertificate`, and the shared-body Word-RAM linker support
separately verified subroutines. Abstract calls are finite typed syntax; linking emits one shared
callee body, executes every callee instruction in the same trace, records structured dynamic calls,
and charges setup, complete callee cost, dispatch, and cleanup. A completed implementation
environment yields a concrete `FixedWidthAlgorithmCertificateBy` without repeating the relative
client correctness proof. Every callable certificate carries an ABI-realizability proof for its
actual input and output values. `ProcedureCertificate` permits declared scratch to remain changed;
the explicitly stronger `RestoringProcedureCertificate` proves that only the canonical output
overwrite remains. In-place and disjoint input/output policies are stated in the calling convention.
Width-uniform dependency linking requires one finite open template and
one finite linked template whose every specialization is the concrete linker output; it cannot
choose code independently by width. `WordRAM.RandomBit` separately supplies a hidden lengthless iid
source for randomized ordinary Word-RAM claims. Randomized relative clients preserve that hidden
source across deterministic calls and can be discharged only to ordinary closed randomized syntax
with a same-source trace-refinement proof.

The Word RAM has a sealed word/address bridge: a word loaded from data memory can become an address
in one charged transition, and word address multiplication is an explicit unit-cost primitive.
Typed fixed-stride accessors therefore compile to multiply-and-add code, carry no-wrap conditions,
and have operational trace, cost, and frame theorems. Variable-footprint `IndexedArray` offsets are
required to equal cumulative canonical element footprints, not merely to be monotone.

Structured exact-real/natural RAM has parallel model-specific infrastructure.
`StructuredRealRAM.CanonicalLayout` selects only closed `Layout` syntax; reusable compact arrays,
matrices, tensors, sparse and indexed tables, combinatorial structures, and named physical graph
formats make storage explicit. Exact input-dependent bounds use `MachineProblem.HasAlgorithmBy`.
Callable contracts distinguish general frame-safe and restoring procedures, relative traces expose
typed calls and exact call costs, and the shared-body linker emits each deterministic dependency
once into one finite core program. External `oracleCall` profiles remain separately named.

`Algolean.Compiler.CFG` supplies first-order labeled blocks, shared branch joins, backward runtime
loops, typed register handles, numeric-jump assembly, and an exact emitted-code-size theorem.
`Algolean.Audit.Algorithm` records and prints every manifest field: layouts, both code-size metrics,
generation, randomness, oracles, extensions, machine conventions, claim kind, and cost source.
`#algorithm_audit publication` consumes typed deterministic, compiled, generated-family,
randomized, oracle, integer-RAM, or word-RAM publications and computes concrete code sizes from
their actual certificates; `#algorithm_manifest metadata` prints legacy name-only navigation
metadata without claiming consistency. Modules executing either command need a
`meta import Algolean.Audit.Algorithm` under Lean's module system.
`OracleMachineProblem.HasOracleAlgorithm` uses a closed `oracleCall` instruction, canonical
query/answer layouts, layout-derived transfer costs, one responder fixed throughout each trace,
and a typed certificate that both proves interface non-vacuity and works for every admissible
responder.

`#layout_audit WordRAM w T` and `#layout_audit StructuredRealRAM T` print resolved closed
representation syntax and access/footprint conventions. `#machine_profile_audit` reports the
StructuredRealRAM core, hidden-bit, or exact-uniform-real profile. Continuous-randomness Monte Carlo
certificates carry an explicit measurable-success-event proof; fair-bit certificates carry the
corresponding product-measure obligation.

Machine conventions are intentionally distinct. `IntegerRAM` is an ordinary unit-cost RAM with
unbounded signed integer data and natural addresses. `WordRAM` has explicit fixed-width modular
words and addresses. `StructuredRealRAM` has exact reals plus an unbounded unit-cost natural bank,
totalized real division, truncating natural subtraction, rational source literals, and
represented-cell input size. These are different complexity models, not interchangeable labels.
The structured-real and ordinary Word-RAM random-bit profiles are separate sealed machines;
neither silently establishes a randomized integer-RAM claim. Exact continuous sampling remains a
separately named exact-real profile rather than an ordinary word operation.

The checked module [`Algolean.Tutorial`](Algolean/Tutorial.lean) explains how to define a query
language, prove functional correctness and cost, package a problem statement, choose between
`Prog` and a fixed RAM program, and audit the resulting guarantee. Checked acceptance examples for
the new interfaces are in
[`AlgoleanTests.ExistentialAlgorithms`](AlgoleanTests/ExistentialAlgorithms.lean),
[`AlgoleanTests.WordRAMInfrastructure`](AlgoleanTests/WordRAMInfrastructure.lean), and
[`AlgoleanTests.StructuredRealRAMProcedureComposition`](AlgoleanTests/StructuredRealRAMProcedureComposition.lean).

## Nomenclature
`Algolean` is a pun. It is intended to be read in two ways.
* "Algo" + "Lean" : A library of algorithms and complexity theory in lean
* "Algol" + "ean" (pronounced like "ene") : To pay homage to Algol which motivates a lot of modern algorithmic pseudocode, and whose simplicity this framework hopes to mimic (hence the "ene").



## Acknowledgements
For timing we build on top of the Writer monad `AddWriter` that was proposed in CSLib as the TimeM model by Sorrachai Yingchareonthawornchai and whose API was perfected by Eric Wieser. 

Further, Eric Wieser substantially assisted with the improvement of the implementation through extensive and detailed PR reviews. 
