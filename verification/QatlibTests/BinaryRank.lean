/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CodeCert.RankCert.Binary
import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

/-! # Consumers of the binary rank certificate -/

namespace QatlibTests.BinaryRank

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodeCert.RankCert

/-- Three binary checks with a nontrivial dependency. -/
def repetitionChecks : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![1, 1, 0; 0, 1, 1; 1, 0, 1]

/-- The dependent check is excluded from the computed rank. -/
theorem repetitionRank : repetitionChecks.rank = 2 :=
  (checkRank_iff (Equiv.refl _) (Equiv.refl _) repetitionChecks 2).mp (by decide +kernel)

/-- A false rank claim is rejected even though the supplied matrix has three rows. -/
theorem rejection : checkRank (Equiv.refl _) (Equiv.refl _) repetitionChecks 3 = false := by
  decide +kernel

/-- The three-bit repetition checks form a CSS code with no X checks. -/
def repetitionCss : CssData (Fin 3) (Fin 0) (Fin 3) where
  hX := 0
  hZ := repetitionChecks
  hcompat := by
    funext i
    exact Fin.elim0 i

/-- Accepted certificates for both check matrices yield one logical qubit. -/
theorem repetitionEncoded : repetitionCss.encodedQubits = 1 :=
  encoded_eq (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) repetitionCss 0 2
    (by decide +kernel) (by decide +kernel)

end QatlibTests.BinaryRank
