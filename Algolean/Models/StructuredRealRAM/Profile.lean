/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.StructuredRealRAM.UniformReal
public import Algolean.Models.StructuredRealRAM.Oracle

/-!
# Sealed structured exact-real/natural RAM profile hierarchy

This closed index is the machine-readable profile identity used by composition and audits.  It
does not contain evaluator functions.  External-oracle machines remain separately indexed by
their typed `OracleInterface`, because an oracle is an explicit relative assumption rather than
an arithmetic or randomness capability.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM

/-- Closed, library-interpreted profiles available to unconditional machine certificates. -/
inductive SealedProfile where
  | deterministic
  | hiddenFairBits
  | hiddenUniformReal
deriving DecidableEq, Repr

namespace SealedProfile

/-- The concrete finite first-order program syntax selected by a sealed profile. -/
def Program : SealedProfile → Type
  | .deterministic => StructuredRealRAM.Program
  | .hiddenFairBits => RandomBit.Program
  | .hiddenUniformReal => UniformReal.Program

/-- Profile validity always comes from the corresponding closed instruction syntax. -/
def Valid : (profile : SealedProfile) → profile.Program → Prop
  | .deterministic => StructuredRealRAM.Program.Valid
  | .hiddenFairBits => RandomBit.Program.Valid
  | .hiddenUniformReal => UniformReal.Program.Valid

/-- Canonical finite binary description size for the selected syntax. -/
def descriptionSize : (profile : SealedProfile) → profile.Program → Nat
  | .deterministic => StructuredRealRAM.Program.descriptionSize
  | .hiddenFairBits => RandomBit.Program.descriptionSize
  | .hiddenUniformReal => UniformReal.Program.descriptionSize

/-- Stable audit disclosure; the constructors, not caller-provided strings, determine the text. -/
def summary : SealedProfile → String
  | .deterministic => StructuredRealRAM.coreProfile.name
  | .hiddenFairBits => RandomBit.profile.name
  | .hiddenUniformReal => UniformReal.profile.name

/-- Whether the hidden source is discrete, continuous, or absent. -/
def randomness : SealedProfile → String
  | .deterministic => "none"
  | .hiddenFairBits => "hidden lengthless iid fair bits"
  | .hiddenUniformReal => "hidden lengthless exact uniform [0,1] reals"

end SealedProfile

end Algolean.Algorithms.StructuredRealRAM
