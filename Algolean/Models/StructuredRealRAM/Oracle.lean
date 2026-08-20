/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.StructuredRealRAM.Layout

/-!
# Auditable oracle contracts

This module defines the typed, layout-aware contract needed before an oracle instruction can be
added to a named machine profile.  It intentionally does not represent an oracle as an arbitrary
memory transformer.  Query and answer transfer costs are explicit, and non-vacuity is a separate
property.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM

/-- A closed typed query/answer interface with canonical memory layouts. -/
@[nolint checkUnivs]
structure OracleInterface (Cost : Type w) where
  /-- Query carrier. -/
  Query : Type u
  /-- Query-dependent answer carrier. -/
  Answer : Query → Type v
  /-- Closed canonical query layout. -/
  queryLayout : Layout Query
  /-- Closed canonical answer layout for each query. -/
  answerLayout : (query : Query) → Layout (Answer query)
  /-- Independent admissibility relation for returned answers. -/
  ValidAnswer : (query : Query) → Answer query → Prop
  /-- Cost of issuing a query. -/
  queryCost : (query : Query) → Cost
  /-- Cost of transferring the canonical answer into memory. -/
  answerWriteCost : (query : Query) → Answer query → Cost

/-- One fixed responder satisfying the interface's advertised answer relation. -/
structure AdmissibleOracle (interface : OracleInterface Cost) where
  /-- Fixed answer selected for every typed query. -/
  answer : (query : interface.Query) → interface.Answer query
  correct : ∀ query, interface.ValidAnswer query (answer query)

namespace OracleInterface

/-- Whether the advertised oracle assumption is non-vacuous. -/
abbrev Nonvacuous (interface : OracleInterface Cost) : Prop :=
  Nonempty (AdmissibleOracle interface)

/-- Canonical query memory; no query encoder is supplied by an algorithm witness. -/
noncomputable def queryMemory (interface : OracleInterface Cost)
    (query : interface.Query) : Memory :=
  interface.queryLayout.init query

/-- Canonical answer representation in a designated result region. -/
noncomputable def AnswerRep (interface : OracleInterface Cost) (query : interface.Query)
    (region : Region) (answer : interface.Answer query) (memory : Memory) : Prop :=
  (interface.answerLayout query).RepAt region answer memory

/-- Canonical oracle answers have a functional memory interpretation. -/
theorem AnswerRep.functional (interface : OracleInterface Cost) (query : interface.Query)
    (region : Region) {left right : interface.Answer query} {memory : Memory}
    (leftRep : interface.AnswerRep query region left memory)
    (rightRep : interface.AnswerRep query region right memory) : left = right :=
  (interface.answerLayout query).rep_functional region leftRep rightRep

end OracleInterface

end Algolean.Algorithms.StructuredRealRAM
