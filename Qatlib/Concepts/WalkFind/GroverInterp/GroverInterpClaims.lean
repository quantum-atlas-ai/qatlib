/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.GroverInterp.GroverInterpolationQuan
import Qatlib.Concepts.WalkFind.GroverInterp.GroverIncludingMinusOneQuan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.WalkFind.GroverInterp

open Qatlib
open Matrix
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

def Lemma3Statement : Prop :=
  Qatlib.Concepts.WalkFind.GroverInterp.GroverInterpolation ∧
    Qatlib.Concepts.WalkFind.GroverInterp.GroverIncludingMinusOne

theorem lemma3 : Lemma3Statement :=
  ⟨Qatlib.Concepts.WalkFind.GroverInterp.groverInterpolation_answer,
    Qatlib.Concepts.WalkFind.GroverInterp.groverIncludingMinusOne_answer⟩

def Claim2Statement : Prop :=
  (∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 2 →
      2 * x / Real.pi ≤ Real.sin x ∧ Real.sin x ≤ x) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 4 →
      4 * x / Real.pi ≤ Real.cot x ∧ Real.cot x ≤ 1 / x)

theorem claim2 : Claim2Statement := by
  constructor
  · intro x hx0 hx2
    constructor
    · rcases lt_or_eq_of_le hx0 with hx | hx
      · rcases lt_or_eq_of_le hx2 with h2 | h2
        · have h := Real.mul_lt_sin hx h2
          have he : 2 * x / Real.pi = 2 / Real.pi * x := by ring
          rw [he]
          exact le_of_lt h
        · subst h2
          rw [Real.sin_pi_div_two]
          have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
          have he : 2 * (Real.pi / 2) / Real.pi = 1 := by field_simp
          rw [he]
      · subst hx
        simp
    · rcases lt_or_eq_of_le hx0 with hx | hx
      · exact le_of_lt (Real.sin_lt hx)
      · subst hx
        simp
  · intro x hx0 hx4
    constructor
    · rcases lt_or_eq_of_le hx0 with hx | hx
      · have hpi : 0 < Real.pi := Real.pi_pos
        have hsin : 0 < Real.sin x :=
          Real.sin_pos_of_pos_of_lt_pi hx (by nlinarith [Real.pi_pos])
        have hsinle : Real.sin x ≤ Real.cos x := by
          have h1 : Real.sin x ≤ Real.sin (Real.pi / 4) := by
            refine Real.sin_le_sin_of_le_of_le_pi_div_two ?_ ?_ hx4
            · nlinarith [Real.pi_pos]
            · nlinarith [Real.pi_pos]
          have h2 : Real.cos (Real.pi / 4) ≤ Real.cos x := by
            refine Real.cos_le_cos_of_nonneg_of_le_pi ?_ ?_ hx4
            · positivity
            · nlinarith [Real.pi_pos]
          rw [Real.sin_pi_div_four] at h1
          rw [Real.cos_pi_div_four] at h2
          linarith
        have hcot : 1 ≤ Real.cot x := by
          rw [Real.cot_eq_cos_div_sin]
          rw [one_le_div hsin]
          exact hsinle
        have hbound : 4 * x / Real.pi ≤ 1 := by
          rw [div_le_one hpi]
          linarith
        linarith
      · subst hx
        simp [Real.cot_eq_cos_div_sin]
    · rcases lt_or_eq_of_le hx0 with hx | hx
      · have hpi : 0 < Real.pi := Real.pi_pos
        have hsin : 0 < Real.sin x :=
          Real.sin_pos_of_pos_of_lt_pi hx (by nlinarith [Real.pi_pos])
        have hcos : 0 < Real.cos x :=
          Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
        have htan : x < Real.tan x := Real.lt_tan hx (by nlinarith [Real.pi_pos])
        rw [Real.tan_eq_sin_div_cos] at htan
        have hlt : x * Real.cos x < Real.sin x := (lt_div_iff₀ hcos).mp htan
        rw [Real.cot_eq_cos_div_sin]
        rw [div_le_div_iff₀ hsin hx]
        linarith
      · subst hx
        simp [Real.cot_eq_cos_div_sin]

def Claim3Statement : Prop :=
  ∀ (m : ℕ) (Uf U : Matrix (Fin m) (Fin m) ℂ) (good : Fin m → ℂ) (z : ℂ),
    (∑ i, ‖good i‖ ^ 2) = 1 →
    Uf *ᵥ good = -good →
    (∀ v : Fin m → ℂ, (∑ i, star (v i) * good i) = 0 → Uf *ᵥ v = v) →
    IsUnit (U - z • (1 : Matrix (Fin m) (Fin m) ℂ)) →
    (∑ i, star (good i) *
        ((U - z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)) i) = 1 / 2 →
      let y := (U - z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)
      (U * Uf) *ᵥ y = z • y ∧ y ≠ 0

theorem claim3 : Claim3Statement :=
  fun m Uf U good z hn hgood hfix hinv hroot =>
    Qatlib.Concepts.WalkFind.GroverInterp.grover_resolvent_search_eigenvector
      m Uf U good z hn hgood hfix hinv hroot

def Claim4Statement : Prop :=
  ∀ (m : ℕ) (ε α : ℝ), 0 < ε → ε ≤ 1 → 0 < α → α ≤ ε ^ 2 / 200 →
    ∀ (Uf U : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ),
      (star U * U = 1) →
      (∀ i j, (U i j).im = 0) →
      (∀ i, (good i).im = 0) →
      (∑ i, ‖start i‖ ^ 2) = 1 →
      (∑ i, ‖good i‖ ^ 2) = 1 →
      (∑ i, star (good i) * start i) = (α : ℂ) →
      U *ᵥ start = start →
      Uf *ᵥ good = -good →
      (∀ v : Fin m → ℂ, (∑ i, star (v i) * good i) = 0 → Uf *ᵥ v = v) →
      (∀ (ν : ℂ) (v : Fin m → ℂ), U *ᵥ v = ν • v →
        (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
        ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ θ ≠ Real.pi ∧
          ν = Complex.exp (Complex.I * θ)) →
      ∃ β ∈ Set.Icc (Real.sqrt (ε * α / Real.pi)) ((13 / 5 : ℝ) * α),
        let z := Complex.exp (Complex.I * β)
        let y := (U - z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)
        Qatlib.Concepts.WalkFind.GroverInterp.groverSecularScalar m U good β = 0 ∧
          (star good ⬝ᵥ y) = 1 / 2 ∧ (U * Uf) *ᵥ y = z • y ∧ y ≠ 0

def Claim4RestrictedStatement : Prop :=
  ∀ (m : ℕ) (ε α : ℝ), 0 < ε → ε ≤ 1 → 0 < α → α ≤ ε ^ 2 / 200 →
    ∀ (Uf U : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ),
      (star U * U = 1) →
      (∀ i j, (U i j).im = 0) →
      (∀ i, (good i).im = 0) →
      (∑ i, ‖start i‖ ^ 2) = 1 →
      (∑ i, ‖good i‖ ^ 2) = 1 →
      (∑ i, star (good i) * start i) = (α : ℂ) →
      U *ᵥ start = start →
      Uf *ᵥ good = -good →
      (∀ v : Fin m → ℂ, (∑ i, star (v i) * good i) = 0 → Uf *ᵥ v = v) →
      (∀ (ν : ℂ) (v : Fin m → ℂ), U *ᵥ v = ν • v →
        (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
        ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ θ ≠ Real.pi ∧
          ν = Complex.exp (Complex.I * θ)) →
      ∃ β ∈ Set.Icc (ε * α / Real.sqrt (2 * Real.pi)) ((13 / 5 : ℝ) * α),
        let z := Complex.exp (Complex.I * β)
        let y := (U - z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)
        Qatlib.Concepts.WalkFind.GroverInterp.groverSecularScalar m U good β = 0 ∧
          (star good ⬝ᵥ y) = 1 / 2 ∧ (U * Uf) *ᵥ y = z • y ∧ y ≠ 0

theorem claim4_restricted : Claim4RestrictedStatement :=
  fun m ε α hε hε1 hα hsmall Uf U start good hu hU hg hsn hgn hoverlap
    hstart hgood hfix hphase =>
    Qatlib.Concepts.WalkFind.GroverInterp.grover_small_overlap_root
      m ε α hε hε1 hα hsmall Uf U start good hu hU hg hsn hgn hoverlap
      hstart hgood hfix hphase

def Claim5Statement : Prop :=
  ∀ (m : ℕ) (ε α β : ℝ),
    0 < ε → ε ≤ 1 → 0 < α → α ≤ ε ^ 2 / 200 →
    β ∈ Set.Icc (ε * α / Real.sqrt (2 * Real.pi)) ((13 / 5 : ℝ) * α) →
    ∀ (U : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ),
      (star U * U = 1) →
      (∀ i j, (U i j).im = 0) →
      (∀ i, (start i).im = 0) →
      (∀ i, (good i).im = 0) →
      (∑ i, ‖start i‖ ^ 2) = 1 →
      (∑ i, ‖good i‖ ^ 2) = 1 →
      (∑ i, star (good i) * start i) = (α : ℂ) →
      U *ᵥ start = start →
      (∀ (ν : ℂ) (v : Fin m → ℂ), U *ᵥ v = ν • v →
        (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
        ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ θ ≠ Real.pi ∧
          ν = Complex.exp (Complex.I * θ)) →
      Qatlib.Concepts.WalkFind.GroverInterp.groverSecularScalar m U good β = 0 →
        let y := (U - Complex.exp (Complex.I * β) • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ
          (U *ᵥ good)
        let C := α * Real.sin β / (2 * (1 - Real.cos β))
        0 < C ∧ (∑ i, ‖((y i).im : ℂ)‖ ^ 2) ≤ 36 / ε ^ 2 ∧
          (∑ i, ‖((y i).im : ℂ) - (C : ℂ) * start i‖ ^ 2) ≤ (2 * β / ε * C) ^ 2

theorem claim5 : Claim5Statement :=
  fun m ε α β hε hε1 hα hsmall hβbounds U start good hu hU hsr hgr hsn hgn
    hoverlap hstart hphase hroot =>
    Qatlib.Concepts.WalkFind.GroverInterp.grover_small_overlap_normalization_bounds
      m ε α β hε hε1 hα hsmall hβbounds U start good hu hU hsr hgr hsn hgn
      hoverlap hstart hphase hroot

def Claim6Statement : Prop :=
  ∀ (m l : ℕ) (α ε : ℝ) (start good : Fin m → ℂ)
    (a : Fin l → ℂ) (θ : Fin l → ℝ) (w : Fin l → Bool → Fin m → ℂ),
    (∑ i, ‖start i‖ ^ 2) = 1 →
    (∑ i, ‖good i‖ ^ 2) = 1 →
    (∀ j s, (∑ i, ‖w j s i‖ ^ 2) = 1) →
    (∀ (j j' : Fin l) (s s' : Bool), (j, s) ≠ (j', s') →
      (∑ i, star (w j s i) * w j' s' i) = 0) →
    (∀ j s, (∑ i, star (w j s i) * start i) = 0) →
    (∀ i, (start i).im = 0) →
    (∀ j, (a j).im = 0) →
    (∑ i, star (good i) * start i) = (α : ℂ) →
    (∀ i, good i = (α : ℂ) * start i + ∑ j, a j * (w j true i + w j false i)) →
    0 < ε →
    (∀ j, ε ≤ θ j ∧ θ j ≤ 2 * Real.pi - ε) →
      let vend : Fin m → ℂ := fun i => ∑ j, a j *
        ((1 + Complex.I * (Real.cot (θ j / 2) : ℂ)) * w j true i +
          (1 - Complex.I * (Real.cot (θ j / 2) : ℂ)) * w j false i)
      min ((1 - α ^ 2) / 2) ((1 - α ^ 2) / 4 * ε) ≤
        ‖∑ i, star (good i) * vend i‖ / Real.sqrt (∑ i, ‖vend i‖ ^ 2)

end Qatlib.Concepts.WalkFind.GroverInterp
