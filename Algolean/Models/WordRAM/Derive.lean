/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.WordRAM.Layout

/-!
# Safe structural payload declarations

These commands give user-defined records a concise machine-facing carrier without generating a
codec or an equivalence.  The carrier must itself be assembled from types with closed
`CanonicalLayout` instances; optional invariants become proof-erased subtypes.  Conversion from an
existing rich structure is deliberately not installed as a free machine operation.
-/

/-- Declare a name for an already structural machine payload. -/
@[nolint topNamespace]
syntax (name := wordRAMPayloadAliasCmd)
  "wordram_payload " ident " := " term : command

/-- Declare a proof-erased refinement of an already structural machine payload. -/
@[nolint topNamespace]
syntax (name := wordRAMPayloadSubtypeCmd)
  "wordram_payload " ident " : " term " where " ident " => " term : command

macro_rules
  | `(wordram_payload $name:ident := $carrier:term) =>
      `(abbrev $name := $carrier)
  | `(wordram_payload $name:ident : $carrier:term where $value:ident => $predicate:term) =>
      `(abbrev $name := { $value : $carrier // $predicate })
