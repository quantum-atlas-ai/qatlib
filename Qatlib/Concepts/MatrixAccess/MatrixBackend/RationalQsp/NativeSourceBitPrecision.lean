/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-!
# Native Source Bit Precision

The SAME source grid, chosen with the literal controller above.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords

/-- The SAME source grid, chosen with the literal controller above. -/
def sourceGrid (N : ℕ) (u : ℚ) : ℚ :=
  1/(2 : ℚ)^sourceCeilLog2 (64*(N+1 : ℚ)/u)

/-- Construction for source K in the native source bit precision model. -/
def sourceK (N : ℕ) (u : ℚ) : ℚ := 2^20*(N+1 : ℚ)^6/u^2

/-- Construction for source Root Precision in the native source bit precision model. -/
def sourceRootPrecision (N : ℕ) (u : ℚ) : ℕ :=
  let h := sourceGrid N u
  sourceCeilLog2 (sourceK N u)+(N+1)*sourceCeilLog2 (128/h)+
    sourceCeilLog2 (max (16/h) (32*(N+1 : ℚ)/u))

/-- The finite construction in `NativeSourceBitPrecision` satisfies `sourceGrid_pos` under the displayed hypotheses. -/
theorem sourceGrid_pos (N : ℕ) (u : ℚ) : 0<sourceGrid N u := by
  dsimp only [sourceGrid]
  positivity

/-- The finite construction in `NativeSourceBitPrecision` satisfies `sourceGrid_upper` under the displayed hypotheses. -/
theorem sourceGrid_upper (N : ℕ) (u : ℚ) (hu : 0<u) :
    sourceGrid N u ≤ u/(64*(N+1 : ℚ)) := by
  have h := sourceCeilLog2_envelope (64*(N+1 : ℚ)/u) (by positivity)
  have hm := (div_le_iff₀ hu).mp h
  dsimp only [sourceGrid]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

/-- The actual source R pays both displayed prospective envelope budgets.
The remaining original-H/radial bridge must still consume these inequalities. -/
theorem source_generated_budget (N : ℕ) (u : ℚ) (hu : 0<u) :
    let h := sourceGrid N u
    let R := sourceRootPrecision N u
    sourceK N u*(1/(2 : ℚ)^R)*(128/h)^(N+1) ≤ h/16 ∧
    sourceK N u*(1/(2 : ℚ)^R)*(128/h)^(N+1) ≤ u/(32*(N+1 : ℚ)) := by
  let h := sourceGrid N u
  let K := sourceK N u
  let L : ℚ := 128/h
  let T : ℚ := max (16/h) (32*(N+1 : ℚ)/u)
  have hh : 0<h := sourceGrid_pos N u
  have hK : 0<K := by dsimp [K,sourceK]; positivity
  have hL : 0<L := by dsimp [L]; positivity
  have hT : 0<T := lt_of_lt_of_le (by positivity : (0 : ℚ)<16/h)
    (le_max_left _ _)
  have hk := sourceCeilLog2_envelope K hK
  have hl := sourceCeilLog2_envelope L hL
  have ht := sourceCeilLog2_envelope T hT
  have hp : L^(N+1) ≤ ((2 : ℚ)^sourceCeilLog2 L)^(N+1) :=
    pow_le_pow_left₀ hL.le hl _
  have hprod : K*L^(N+1)*T ≤ (2 : ℚ)^sourceRootPrecision N u := by
    calc
      _ ≤ (2 : ℚ)^sourceCeilLog2 K*
          ((2 : ℚ)^sourceCeilLog2 L)^(N+1)*(2 : ℚ)^sourceCeilLog2 T :=
        mul_le_mul (mul_le_mul hk hp (by positivity) (by positivity)) ht hT.le
          (by positivity)
      _ = (2 : ℚ)^sourceRootPrecision N u := by
        symm
        change (2 : ℚ)^(sourceCeilLog2 K+(N+1)*sourceCeilLog2 L+sourceCeilLog2 T)=
          (2 : ℚ)^sourceCeilLog2 K*((2 : ℚ)^sourceCeilLog2 L)^(N+1)*
            (2 : ℚ)^sourceCeilLog2 T
        rw [Nat.mul_comm (N+1) (sourceCeilLog2 L),pow_add,pow_add,pow_mul]
  let env := K*(1/(2 : ℚ)^sourceRootPrecision N u)*L^(N+1)
  have hscaled : env*T ≤ 1 := by
    calc
      _ = (K*L^(N+1)*T)/(2 : ℚ)^sourceRootPrecision N u := by dsimp only [env]; ring
      _ ≤ 1 := (div_le_one (by positivity)).mpr hprod
  have henv : env ≤ 1/T := (le_div_iff₀ hT).mpr hscaled
  have hhbound : 1/T ≤ h/16 := by
    calc
      _ ≤ 1/(16/h) := one_div_le_one_div_of_le (by positivity) (le_max_left _ _)
      _ = h/16 := by field_simp
  have hubound : 1/T ≤ u/(32*(N+1 : ℚ)) := by
    calc
      _ ≤ 1/(32*(N+1 : ℚ)/u) :=
        one_div_le_one_div_of_le (by positivity) (le_max_right _ _)
      _ = u/(32*(N+1 : ℚ)) := by field_simp
  exact ⟨henv.trans hhbound,henv.trans hubound⟩

/-- Full supplied input length remains in the tolerance controller, even
when the discarded tail is exact zero. -/
def sourceInputU (cs : List ℚ) (N : ℕ) (E : ℚ) : ℚ :=
  min (1/2) (E/(2*(max (N+1) cs.length : ℕ)))

/-- Construction for source Input R in the native source bit precision model. -/
def sourceInputR (cs : List ℚ) (N : ℕ) (E : ℚ) : ℕ :=
  sourceRootPrecision N (sourceInputU cs N E)

/-- Construction for source Input Eta in the native source bit precision model. -/
def sourceInputEta (cs : List ℚ) (N : ℕ) (E : ℚ) : ℚ :=
  1/(2 : ℚ)^sourceInputR cs N E

/-- The finite construction in `NativeSourceBitPrecision` satisfies `sourceInputU_pos` under the displayed hypotheses. -/
theorem sourceInputU_pos (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E) :
    0<sourceInputU cs N E := by
  have hm : (0 : ℚ)<(max (N+1) cs.length : ℕ) := by
    exact_mod_cast lt_of_lt_of_le (Nat.succ_pos N) (le_max_left (N+1) cs.length)
  dsimp only [sourceInputU]
  exact lt_min (by norm_num) (by positivity)

/-- The finite construction in `NativeSourceBitPrecision` satisfies `sourceInputU_le_half` under the displayed hypotheses. -/
theorem sourceInputU_le_half (cs : List ℚ) (N : ℕ) (E : ℚ) :
    sourceInputU cs N E ≤ 1/2 := min_le_left _ _

/-- Both actual K/Lambda envelopes from original cs/N/E, without externally
chosen u,h,R. This still does NOT supply the missing original-H radial proof. -/
theorem source_input_budget (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E) :
    let u := sourceInputU cs N E
    let h := sourceGrid N u
    sourceK N u*sourceInputEta cs N E*(128/h)^(N+1) ≤ h/16 ∧
    sourceK N u*sourceInputEta cs N E*(128/h)^(N+1) ≤ u/(32*(N+1 : ℚ)) := by
  exact source_generated_budget N (sourceInputU cs N E) (sourceInputU_pos cs N E hE)

/-- A source-derived eta upper bound needed by the later ORIGINAL-H gap
consumer. It is not itself a proof that any given H has that radial gap. -/
theorem source_input_eta_small (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E) :
    sourceInputEta cs N E ≤
      (sourceInputU cs N E)^3/((2 : ℚ)^30*(N+1 : ℚ)^7) := by
  let u := sourceInputU cs N E
  let h := sourceGrid N u
  let K := sourceK N u
  let eta := sourceInputEta cs N E
  have hu : 0<u := sourceInputU_pos cs N E hE
  have hu1 : u ≤ 1/2 := sourceInputU_le_half cs N E
  have hN : (0 : ℚ)<N+1 := by positivity
  have hh : 0<h := sourceGrid_pos N u
  have hK : 0<K := by dsimp only [K,sourceK]; positivity
  have heta : 0<eta := by dsimp only [eta,sourceInputEta]; positivity
  have hg : h ≤ u/(64*(N+1 : ℚ)) := sourceGrid_upper N u hu
  have hh1 : h ≤ 1 := by
    have hb : u/(64*(N+1 : ℚ)) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      have hn0 : (0 : ℚ) ≤ N := by positivity
      linarith
    exact hg.trans hb
  have hL : (1 : ℚ) ≤ 128/h := (le_div_iff₀ hh).mpr (by linarith)
  have hpow : (1 : ℚ) ≤ (128/h)^(N+1) := one_le_pow₀ hL
  have hb := (source_input_budget cs N E hE).1
  change K*eta*(128/h)^(N+1) ≤ h/16 at hb
  have hk : K*eta ≤ h/16 :=
    (le_mul_of_one_le_right (mul_nonneg hK.le heta.le) hpow).trans hb
  calc
    eta ≤ (h/16)/K := (le_div_iff₀ hK).mpr (by nlinarith [hk])
    _ ≤ (u/(64*(N+1 : ℚ))/16)/K :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hg (by norm_num)) hK.le
    _ = u^3/((2 : ℚ)^30*(N+1 : ℚ)^7) := by
      dsimp only [K,sourceK]
      field_simp [ne_of_gt hu,ne_of_gt hN]
      ring

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
