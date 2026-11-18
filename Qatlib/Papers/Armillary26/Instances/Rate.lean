/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CodeCert.PermBlocks.Rank
public import Qatlib.Concepts.ErrorCorrection.CssBuild.Constructions
public import Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# A structural rate bound for retained Armillary checks

Three retained permutation-block rows on each side have at least two linear
dependencies each. For twelve data groups, CSS compatibility therefore gives
at least `6 * P + 4` logical qubits. This lower bound does not assert exact rank,
distance, schedule realizability, or existence of suitable routing parameters.
-/

namespace Qatlib.Papers.Armillary26.Instances

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodeCert.PermBlocks
open Qatlib.Concepts.ErrorCorrection.CssBuild
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open scoped Matrix

/-- A compatible pair of three-by-twelve permutation-block arrays defines a CSS code. -/
def retainedCode {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σX σZ : Fin 3 → Fin 12 → Equiv.Perm ι)
    (hcompat : permBlocks (K := ZMod 2) σX * (permBlocks (K := ZMod 2) σZ)ᵀ = 0) :
    CssData (Fin 12 × ι) (Fin 3 × ι) (Fin 3 × ι) :=
  ofComplex (permBlocks σX) (permBlocks σZ)ᵀ hcompat

/-- Equal block sums imply the Armillary structural lower bound on encoded qubits. -/
theorem encoded_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p₀ : ι) (σX σZ : Fin 3 → Fin 12 → Equiv.Perm ι)
    (hcompat : permBlocks (K := ZMod 2) σX * (permBlocks (K := ZMod 2) σZ)ᵀ = 0) :
    6 * Fintype.card ι + 4 ≤ (retainedCode σX σZ hcompat).encodedQubits := by
  have hx := perm_rank_add (K := ZMod 2) 2 p₀ σX
  have hz := perm_rank_add (K := ZMod 2) 2 p₀ σZ
  simp only [CssData.encodedQubits, retainedCode, ofComplex,
    Matrix.transpose_transpose, Fintype.card_prod, Fintype.card_fin] at *
  omega

/-- The logical-to-data-qubit ratio is strictly larger than one half. -/
theorem rate_gt_half {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p₀ : ι) (σX σZ : Fin 3 → Fin 12 → Equiv.Perm ι)
    (hcompat : permBlocks (K := ZMod 2) σX * (permBlocks (K := ZMod 2) σZ)ᵀ = 0) :
    (1 / 2 : ℚ) < ((retainedCode σX σZ hcompat).encodedQubits : ℚ) /
      (12 * Fintype.card ι : ℕ) := by
  have hp : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨p₀⟩
  have hd : (0 : ℚ) < (12 * Fintype.card ι : ℕ) := by positivity
  rw [lt_div_iff₀ hd]
  have hk := encoded_lower p₀ σX σZ hcompat
  have hk' : (6 * Fintype.card ι + 4 : ℚ) ≤
      ((retainedCode σX σZ hcompat).encodedQubits : ℚ) := by exact_mod_cast hk
  push_cast
  linarith

end Qatlib.Papers.Armillary26.Instances
