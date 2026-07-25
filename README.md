# Algolean

Algolean is a library of algorithms and complexity theory, defined broadly to include much of the Algorithms and Complexity theory literature. It is written in the lightweight free monad version of what I call the "query-combinator" model. It currently consists of code that lies in several CSLib pull requests. The framework can encompass standard and custom models in algorithms theory, ranging from RAM and Turing machines, to circuits, and even niche models like the Robertson-Webb cake cutting model. The intent is to provide an all-encompassing framework of models and reductions between them. Complexity claims are relative to the operations exposed as queries and their declared costs; pure Lean work is uncharged, so the chosen query language is part of the auditable specification.

`Algolean.Machine` provides finite first-order machine code for independent algorithm-existence
statements. Its fixed translations record instructions and finalization as ordinary `Prog`
queries; `Program.compile` records initialization too, while `Program.compileFrom` makes an
existing initial state the caller's explicit responsibility. Runtime values can select only
successors already stored in the source tree. Existing models give those queries semantics and
costs, while a `Reduction` can lower them to another query language, including one extended with
an oracle.

The checked module [`Algolean.Tutorial`](Algolean/Tutorial.lean) explains how to define a query
language, prove functional correctness and cost, package a problem statement, choose between
`Prog` and `Machine.Program`, add an oracle, and audit the resulting guarantee.

## Nomenclature
`Algolean` is a pun. It is intended to be read in two ways.
* "Algo" + "Lean" : A library of algorithms and complexity theory in lean
* "Algol" + "ean" (pronounced like "ene") : To pay homage to Algol which motivates a lot of modern algorithmic pseudocode, and whose simplicity this framework hopes to mimic (hence the "ene").



## Acknowledgements
For timing we build on top of the Writer monad `AddWriter` that was proposed in CSLib as the TimeM model by Sorrachai Yingchareonthawornchai and whose API was perfected by Eric Wieser. 

Further, Eric Wieser substantially assisted with the improvement of the implementation through extensive and detailed PR reviews. 
