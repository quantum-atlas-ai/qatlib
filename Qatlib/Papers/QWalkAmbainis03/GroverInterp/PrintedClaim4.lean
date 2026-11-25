/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.WalkFind.GroverInterp.GroverInterpolationQuan

@[expose] public section

/-!
# The printed Claim 4 phase interval

The lower endpoint in the fixed paper is `ε * α / sqrt π`.
At that endpoint the pole in the weighted secular sum is at least
`6 / ε²`, which dominates the sum over the nontrivial eigenphases.
The existing upper-endpoint sign then gives the root and its eigenvector.
-/

set_option autoImplicit false

open Matrix
open scoped Matrix BigOperators
open Qatlib.Concepts.WalkFind.GroverInterp

namespace Qatlib.Papers.QWalkAmbainis03.GroverInterp

/-- At the printed lower endpoint of Claim 4, the weighted secular bracket is nonnegative. -/
private theorem printed_lower_sign {J : Type*} [Fintype J]
    (ε α : ℝ) (hε : 0 < ε) (he1 : ε ≤ 1) (ha : 0 < α) (hl : α ≤ ε ^ 2 / 200)
    (w eig : J → ℝ) (hw : ∀ j, 0 ≤ w j) (hmass : (∑ j, w j) = 1 - α ^ 2)
    (heig : ∀ j, -1 ≤ eig j ∧ eig j ≤ Real.cos ε) :
    let lo := ε * α / Real.sqrt Real.pi
    0 ≤ α ^ 2 / (1 - Real.cos lo) - ∑ j, w j / (Real.cos lo - eig j) := by
  let lo := ε * α / Real.sqrt Real.pi
  have hlp : 0 < lo := by dsimp [lo]; positivity
  have hp : (1 : ℝ) ≤ Real.sqrt Real.pi := by
    rw [Real.le_sqrt (by norm_num) Real.pi_pos.le]
    nlinarith [Real.pi_gt_three]
  have hlo : lo ≤ ε * α := by dsimp [lo]; exact div_le_self (by positivity) hp
  have ha1 : α ≤ 1 / 200 := by nlinarith
  have hle : lo ≤ ε / 2 := by
    have h := mul_le_mul_of_nonneg_left ha1 hε.le
    linarith [hlo]
  have hβ1 : lo ≤ 1 := by linarith
  have hcos := grover_one_sub_cos_bounds lo hlp.le hβ1
  have hden : 0 < 1 - Real.cos lo := by nlinarith [sq_pos_of_pos hlp]
  have hpi : Real.pi * lo ^ 2 = ε ^ 2 * α ^ 2 := by
    dsimp [lo]
    rw [div_pow, Real.sq_sqrt Real.pi_pos.le]
    field_simp
  have hes : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hpole : 6 / ε ^ 2 ≤ α ^ 2 / (1 - Real.cos lo) := by
    apply (div_le_div_iff₀ hes hden).2
    nlinarith [mul_nonneg (sq_nonneg lo) (show 0 ≤ Real.pi - 3 by linarith [Real.pi_gt_three])]
  have hsum := (grover_weighted_inverse_bounds ε lo hε he1 hlp.le hle w eig hw heig).2
  rw [hmass] at hsum
  have hn : (6 * (1 - α ^ 2)) / ε ^ 2 ≤ 6 / ε ^ 2 :=
    div_le_div_of_nonneg_right (by nlinarith [sq_nonneg α]) hes.le
  exact sub_nonneg.mpr (hsum.trans (hn.trans hpole))

/-- Claim 4 with the fixed paper's phase interval, and the corresponding nonzero
resolvent eigenvector. -/
theorem claim4_source_interval (m : ℕ) (ε α : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hα : 0 < α) (hsmall : α ≤ ε ^ 2 / 200)
    (Uf U : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ)
    (hu : star U * U = 1) (hU : ∀ i j, (U i j).im = 0) (hg : ∀ i, (good i).im = 0)
    (hsn : (∑ i, ‖start i‖ ^ 2) = 1) (hgn : (∑ i, ‖good i‖ ^ 2) = 1)
    (hoverlap : (∑ i, star (good i) * start i) = (α : ℂ))
    (hstart : U *ᵥ start = start) (hgood : Uf *ᵥ good = -good)
    (hfix : ∀ v : Fin m → ℂ, (∑ i, star (v i) * good i) = 0 → Uf *ᵥ v = v)
    (hphase : ∀ (ν : ℂ) (v : Fin m → ℂ), U *ᵥ v = ν • v →
      (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
      ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ θ ≠ Real.pi ∧
        ν = Complex.exp (Complex.I * θ)) :
    ∃ β ∈ Set.Icc (ε * α / Real.sqrt Real.pi) ((13 / 5 : ℝ) * α),
      let z := Complex.exp (Complex.I * β)
      let y := (U - z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)
      groverSecularScalar m U good β = 0 ∧
        (star good ⬝ᵥ y) = 1 / 2 ∧ (U * Uf) *ᵥ y = z • y ∧ y ≠ 0 := by
  classical
  let lo := ε * α / Real.sqrt Real.pi
  let hi := (13 / 5 : ℝ) * α
  obtain ⟨B, μ, w, s, hB, hB', hμ, he, hw, _, hmass, hsums, hwfix, hsfix, hweights⟩ :=
    jw_unitary_gap_weights m ε α hε U start good hu hstart hsn hgn hoverlap hphase
  let eig := fun j => if μ j = 1 then (-1 : ℝ) else (μ j).re
  have heig := jw_unitary_basis_real_gap m ε hε U B start μ hu hB hstart he hphase
  have hlow := printed_lower_sign ε α hε hε1 hα hsmall w eig hw hmass heig
  have hhigh := (grover_weighted_endpoint_signs ε α hε hε1 hα hsmall w eig hw hmass heig).1
  have hp : (1 : ℝ) ≤ Real.sqrt Real.pi := by
    rw [Real.le_sqrt (by norm_num) Real.pi_pos.le]
    nlinarith [Real.pi_gt_three]
  have hlop : 0 < lo := by dsimp [lo]; positivity
  have hloa : lo ≤ ε * α := by dsimp [lo]; exact div_le_self (by positivity) hp
  have hhip : 0 < hi := by dsimp [hi]; positivity
  have he2 : ε ^ 2 ≤ ε := by nlinarith
  have hhieps : hi < ε := by dsimp [hi]; nlinarith
  have hab : lo ≤ hi := by dsimp [hi]; nlinarith [mul_nonneg hα.le (sub_nonneg.mpr hε1)]
  have hloeps : lo < ε := hab.trans_lt hhieps
  have hslo := grover_secular_gap_weights m U B μ good α lo w s hu hU hg hB' hμ he
    hwfix hsfix hsums hweights (grover_resolvent_isUnit m ε lo hε hε1 hlop hloeps U start hu hstart hphase)
  have hshi := grover_secular_gap_weights m U B μ good α hi w s hu hU hg hB' hμ he
    hwfix hsfix hsums hweights (grover_resolvent_isUnit m ε hi hε hε1 hhip hhieps U start hu hstart hphase)
  have hpos (x : ℝ) (hx : 0 ≤ x) (hxε : x < ε) : 0 ≤ Real.sin x / 2 :=
    div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx (by linarith [Real.pi_gt_three])) (by norm_num)
  apply grover_secular_root_of_signs m ε lo hi hε hε1 hlop hab hhieps Uf U start good
    hu hstart hgn hgood hfix hphase
  · rw [hslo]
    exact mul_nonneg (hpos lo hlop.le hloeps) hlow
  · rw [hshi]
    exact mul_nonpos_of_nonneg_of_nonpos (hpos hi hhip.le hhieps) hhigh

end Qatlib.Papers.QWalkAmbainis03.GroverInterp
