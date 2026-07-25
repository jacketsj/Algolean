/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.QueryModel

/-!
# Finite machine programs

`Program` is a small first-order control-flow language for machine code. Every successor is stored
in the syntax, so source-level runtime values can only select an existing branch.

`Query` records initialization, one instruction, or finalization as a single machine operation.
`Program.compile` is the fixed translation to `Prog Query`; algorithms do not supply any Lean
continuations. A `Model Query Cost` gives the machine's semantics and costs. An optional
`Reduction` can implement its operations using a lower-level query language, including one
extended with an oracle.

The restriction is on source programs. Concrete instruction types, models, and reductions remain
the trusted machine specification and should stay small enough to audit directly. In particular,
the guarantee applies to a `Program` translated by `Program.compile` or `Program.compileFrom`, not
to an arbitrary hand-written `Prog Query`. A caller using `compileFrom` owns the encoding,
provenance, and cost contract for the supplied initial state.

Programs are finite execution trees. Algorithms with a public size or fuel parameter can be
families of such trees, as in circuit families. A uniform language with runtime-dependent loops
needs a separate control-flow-graph model.
-/

@[expose] public section

namespace Algolean.Algorithms.Machine

/-- The outcome of an instruction with two successors. -/
inductive Choice2 where
  | first
  | second

/-- The outcome of an instruction with three successors. -/
inductive Choice3 where
  | first
  | second
  | third

/-- Static instruction types, classified by their number of successors. -/
structure Language where
  /-- Instructions with one successor. -/
  Next : Type u
  /-- Instructions with two successors. -/
  Choose2 : Type u
  /-- Instructions with three successors. -/
  Choose3 : Type u

/-- Finite machine code whose complete control-flow tree is explicit data. -/
inductive Program (language : Language.{u}) (Exit : Type u) where
  | halt (exit : Exit)
  | next (instruction : language.Next) (continuation : Program language Exit)
  | choose2 (instruction : language.Choose2)
      (first second : Program language Exit)
  | choose3 (instruction : language.Choose3)
      (first second third : Program language Exit)

/--
The recorded operations of a machine.

`State` is absent from `Program` and is carried only as an operand or result of recorded operations
during compilation; it is never exposed to source code. `Exit` is a static descriptor interpreted
by `finish`, while `Result` is the returned value.
-/
inductive Query (language : Language.{u}) (Input Exit State Result : Type u) : Type u → Type u where
  | init (input : Input) : Query language Input Exit State Result State
  | execute (instruction : language.Next) (state : State) :
      Query language Input Exit State Result State
  | choose2 (instruction : language.Choose2) (state : State) :
      Query language Input Exit State Result (State × Choice2)
  | choose3 (instruction : language.Choose3) (state : State) :
      Query language Input Exit State Result (State × Choice3)
  | finish (exit : Exit) (state : State) :
      Query language Input Exit State Result Result

/--
Run finite source code from an already initialized state, recording every source node as a query.

This definition is public so proofs about machine implementations can use its stable recursive
equations. Most clients should call `Program.compile`, which records initialization as well.
-/
def Program.compileFrom (program : Program language Exit) (state : State) :
    Prog (Query language Input Exit State Result) Result :=
  match program with
  | .halt exit =>
      Cslib.FreeM.lift (.finish exit state)
  | .next instruction continuation => do
      let state ← Cslib.FreeM.lift (.execute instruction state)
      continuation.compileFrom state
  | .choose2 instruction first second => do
      let (state, choice) ← Cslib.FreeM.lift (.choose2 instruction state)
      match choice with
      | .first => first.compileFrom state
      | .second => second.compileFrom state
  | .choose3 instruction first second third => do
      let (state, choice) ← Cslib.FreeM.lift (.choose3 instruction state)
      match choice with
      | .first => first.compileFrom state
      | .second => second.compileFrom state
      | .third => third.compileFrom state

@[simp]
theorem Program.compileFrom_halt (exit : Exit) (state : State) :
    compileFrom (Input := Input) (Result := Result) (.halt exit : Program language Exit) state =
      Cslib.FreeM.lift (.finish exit state) :=
  rfl

@[simp]
theorem Program.compileFrom_next
    (instruction : language.Next) (continuation : Program language Exit) (state : State) :
    compileFrom (Input := Input) (Result := Result) (.next instruction continuation) state =
      (do
        let state ← Cslib.FreeM.lift (.execute instruction state)
        continuation.compileFrom state) :=
  rfl

@[simp]
theorem Program.compileFrom_choose2
    (instruction : language.Choose2) (first second : Program language Exit) (state : State) :
    compileFrom (Input := Input) (Result := Result) (.choose2 instruction first second) state =
      (do
        let (state, choice) ← Cslib.FreeM.lift (.choose2 instruction state)
        match choice with
        | .first => first.compileFrom state
        | .second => second.compileFrom state) :=
  rfl

@[simp]
theorem Program.compileFrom_choose3
    (instruction : language.Choose3) (first second third : Program language Exit) (state : State) :
    compileFrom (Input := Input) (Result := Result)
        (.choose3 instruction first second third) state =
      (do
        let (state, choice) ← Cslib.FreeM.lift (.choose3 instruction state)
        match choice with
        | .first => first.compileFrom state
        | .second => second.compileFrom state
        | .third => third.compileFrom state) :=
  rfl

/--
Translate finite source code to its recorded machine operations.

The translation first records initialization, then calls `Program.compileFrom`. Each source node
emits one query, and a branch result selects only a subtree already stored in `program`.
-/
def Program.compile (program : Program language Exit) (input : Input) :
    Prog (Query language Input Exit State Result) Result := do
  let state ← Cslib.FreeM.lift (.init input)
  program.compileFrom state

@[simp]
theorem Program.compile_eq (program : Program language Exit) (input : Input) :
    compile (State := State) (Result := Result) program input =
      (do
        let state ← Cslib.FreeM.lift (.init input)
        program.compileFrom state) :=
  rfl

end Algolean.Algorithms.Machine
