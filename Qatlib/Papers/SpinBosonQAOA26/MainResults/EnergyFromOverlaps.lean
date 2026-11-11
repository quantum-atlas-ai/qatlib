/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions.SourceStates

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 1 — SK-QAOA energy from spin–boson overlaps

Fixed source: arXiv:2505.07929v2, Corollary 1, PDF p. 13, eq. (43), to be read together
with the definition of the infinite-size energy in eqs. (14)–(15), PDF p. 5.

The SK-QAOA energy `ν_p(γ, β)` is determined by the `(2p+1) × (2p+1)` correlation matrix
`G^{(p)}` via eq. (15):
  `ν_p = (i/2) ∑_{j=-p}^{p} Γ_j (G^{(p)}_{0,j})²`.
Corollary 1 evaluates the same number from the overlaps of the `Z`-inserted spin–boson
states:
  `ν_p(γ, β) = Im[∑_{r=1}^{p} γ_r (⟨Ψ_0|Ψ_r⟩)²]`.

The two inputs identifying the zero row of `G^{(p)}` with the overlaps are exactly the
path-integral representation of Proposition 1 (arXiv:2505.07929v2, eq. (120)): with the
four-block structure the entries `G^{(p)}_{0,-r}` are the overlaps `⟨Ψ_0|Ψ_r⟩` and
`G^{(p)}_{0,r}` their conjugates.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset Matrix

namespace Qatlib.Papers.SpinBosonQAOA26.MainResults.EnergyFromOverlaps

open Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions

variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B]

/-- The infinite-size SK-QAOA energy functional determined by the correlation matrix
`G^{(p)}`, as in eq. (15) (PDF p. 5): `ν_p = (i/2) ∑_j Γ_j (G_{0,j})²`.  It is kept
complex-valued; the energy itself is its real part (`corollary1_energy_from_overlaps`
shows that this real part is the imaginary part of the overlap sum). -/
def energyFromCorrelations {p : ℕ} (Γ : Fin (2 * p + 1) → ℝ)
    (G : Matrix (Fin (2 * p + 1)) (Fin (2 * p + 1)) ℂ) : ℂ :=
  (Complex.I / 2) * ∑ j : Fin (2 * p + 1), (Γ j : ℂ) * (G (zeroIdx p) j) ^ 2

/-- Conjugation symmetry of the spin–boson overlap: `⟨s|t⟩ = conj ⟨t|s⟩` for the
two-component inner product `stateInner`. -/
lemma stateInner_conj_symm {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    (s t : SBState B) :
    stateInner t s = (starRingEnd ℂ) (stateInner s t) := by
  rw [stateInner, stateInner, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (inner_conj_symm (t i) (s i)).symm

/-- Split the sum over the `(2p+1)`-element index set of eq. (121) (PDF p. 25) into
the positive block `posIdx`, the negative block `negIdx` and the zero slot `zeroIdx`. -/
lemma sum_fin_three_blocks {M : Type*} [AddCommMonoid M] {p : ℕ}
    (f : Fin (2 * p + 1) → M) :
    (∑ j : Fin (2 * p + 1), f j)
      = (∑ r : Fin p, f (posIdx p r)) + (∑ r : Fin p, f (negIdx p r))
        + f (zeroIdx p) := by
  set F : ℕ → M := fun k => if hk : k < 2 * p + 1 then f ⟨k, hk⟩ else 0 with hF
  have hFapply : ∀ j : Fin (2 * p + 1), F (j : ℕ) = f j := by
    intro j
    rw [hF]
    simp only [dif_pos j.isLt]
  have hpos : (∑ r : Fin p, f (posIdx p r)) = ∑ k ∈ Finset.range p, F k := by
    have hr : ∀ r : Fin p, f (posIdx p r) = F (r : ℕ) := by
      intro r
      rw [hF]
      simp only [dif_pos (show (r : ℕ) < 2 * p + 1 by omega)]
      congr 1
    have hs : (∑ r : Fin p, f (posIdx p r)) = ∑ r : Fin p, F (r : ℕ) :=
      Finset.sum_congr rfl fun r _ => hr r
    rw [hs]
    exact Fin.sum_univ_eq_sum_range F p
  have hneg : (∑ r : Fin p, f (negIdx p r)) = ∑ k ∈ Finset.range p, F (p + 1 + k) := by
    have hr : ∀ r : Fin p, f (negIdx p r) = F (2 * p - (r : ℕ)) := by
      intro r
      rw [hF]
      simp only [dif_pos (show 2 * p - (r : ℕ) < 2 * p + 1 by omega)]
      congr 1
    have hs : (∑ r : Fin p, f (negIdx p r)) = ∑ r : Fin p, F (2 * p - (r : ℕ)) :=
      Finset.sum_congr rfl fun r _ => hr r
    rw [hs]
    have hs' : (∑ r : Fin p, F (2 * p - (r : ℕ)))
        = ∑ k ∈ Finset.range p, F (2 * p - k) :=
      Fin.sum_univ_eq_sum_range (fun k => F (2 * p - k)) p
    rw [hs']
    have hrefl : (∑ j ∈ Finset.range p, F (2 * p - (p - 1 - j)))
        = ∑ j ∈ Finset.range p, F (2 * p - j) := by
      simpa only using Finset.sum_range_reflect (fun k => F (2 * p - k)) p
    have hcongr : (∑ j ∈ Finset.range p, F (p + 1 + j))
        = ∑ j ∈ Finset.range p, F (2 * p - (p - 1 - j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < p := Finset.mem_range.mp hj
      congr 1
      omega
    rw [hcongr, hrefl]
  have hzero : f (zeroIdx p) = F p := by
    rw [hF]
    simp only [dif_pos (show p < 2 * p + 1 by omega)]
    congr 1
  have hsum_range : (∑ j : Fin (2 * p + 1), f j) = ∑ k ∈ Finset.range (2 * p + 1), F k := by
    have hs : (∑ j : Fin (2 * p + 1), f j)
        = ∑ j : Fin (2 * p + 1), F (j : ℕ) :=
      Finset.sum_congr rfl fun j _ => (hFapply j).symm
    rw [hs]
    exact Fin.sum_univ_eq_sum_range F (2 * p + 1)
  calc (∑ j : Fin (2 * p + 1), f j)
      = ∑ k ∈ Finset.range (2 * p + 1), F k := hsum_range
    _ = (∑ k ∈ Finset.range (p + 1), F k) + ∑ k ∈ Finset.range p, F (p + 1 + k) := by
        have h : 2 * p + 1 = (p + 1) + p := by omega
        rw [h, Finset.sum_range_add]
    _ = ((∑ k ∈ Finset.range p, F k) + F p) + ∑ k ∈ Finset.range p, F (p + 1 + k) := by
        rw [Finset.sum_range_succ]
    _ = (∑ r : Fin p, f (posIdx p r)) + (∑ r : Fin p, f (negIdx p r)) + f (zeroIdx p) := by
        rw [← hpos, ← hneg, ← hzero]
        ac_rfl

/-- The elementary complex identity behind the rearrangement in Corollary 1:
`Re[(i/2)(conj (z²) − z²)] = Im (z²)`. -/
lemma re_I_div_two_mul_conj_sq_sub (z : ℂ) :
    (Complex.I / 2 * (((starRingEnd ℂ) z) ^ 2 - z ^ 2)).re = (z ^ 2).im := by
  have hconj : ((starRingEnd ℂ) z) ^ 2 = (starRingEnd ℂ) (z ^ 2) :=
    (map_pow (starRingEnd ℂ) z 2).symm
  rw [hconj]
  have hmain : Complex.I * ((starRingEnd ℂ) (z ^ 2) - z ^ 2)
      = ((2 * (z ^ 2).im : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [-map_pow, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.conj_re,
        Complex.conj_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]
      ring
    · simp [-map_pow, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
        Complex.conj_im, Complex.I_re, Complex.I_im, Complex.ofReal_im]
  have hdiv : Complex.I / 2 * ((starRingEnd ℂ) (z ^ 2) - z ^ 2) = ((z ^ 2).im : ℂ) := by
    have h2 : (2 : ℂ) * (Complex.I / 2 * ((starRingEnd ℂ) (z ^ 2) - z ^ 2))
        = 2 * ((z ^ 2).im : ℂ) := by
      calc (2 : ℂ) * (Complex.I / 2 * ((starRingEnd ℂ) (z ^ 2) - z ^ 2))
          = Complex.I * ((starRingEnd ℂ) (z ^ 2) - z ^ 2) := by ring
        _ = ((2 * (z ^ 2).im : ℝ) : ℂ) := hmain
        _ = 2 * ((z ^ 2).im : ℂ) := by push_cast; ring
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h2
  rw [hdiv, Complex.ofReal_re]

/-- **Corollary 1** (arXiv:2505.07929v2, PDF p. 13, eq. (43)), together with eq. (15)
(PDF p. 5).  The infinite-size SK-QAOA energy, written through the correlation matrix
`G^{(p)}` as in eq. (15), equals the imaginary part of the weighted sum of squared
overlaps of the `Z`-inserted spin–boson states of eqs. (39), (40).

The hypotheses `hGpos`/`hGneg` record the identification furnished by Proposition 1
(arXiv:2505.07929v2, eq. (120)) and Hermiticity of the correlation matrix:
`G_{0,r} = ⟨Ψ_r|Ψ_0⟩ = conj ⟨Ψ_0|Ψ_r⟩` and `G_{0,-r} = ⟨Ψ_0|Ψ_r⟩`.  The hypotheses
`hΓpos`, `hΓneg`, `hΓzero` are eqs. (19), (133)–(134). -/
theorem corollary1_energy_from_overlaps
    {p' p : ℕ} (W : WeylFock (B := B) p') (L : Matrix (Fin p') (Fin p) ℂ) (γ β : Fin p → ℝ)
    (G : Matrix (Fin (2 * p + 1)) (Fin (2 * p + 1)) ℂ) (Γ : Fin (2 * p + 1) → ℝ)
    (hΓpos : ∀ r, Γ (posIdx p r) = γ r)
    (hΓneg : ∀ r, Γ (negIdx p r) = -γ r)
    (hΓzero : Γ (zeroIdx p) = 0)
    (hGpos : ∀ r, G (zeroIdx p) (posIdx p r) =
      stateInner (psi W.dop W.vacuum L γ β (PsiIndex.pos r)) (psi W.dop W.vacuum L γ β PsiIndex.zero))
    (hGneg : ∀ r, G (zeroIdx p) (negIdx p r) =
      stateInner (psi W.dop W.vacuum L γ β PsiIndex.zero) (psi W.dop W.vacuum L γ β (PsiIndex.pos r))) :
    (energyFromCorrelations Γ G).re =
      (∑ r : Fin p, (γ r : ℂ) *
        (stateInner (psi W.dop W.vacuum L γ β PsiIndex.zero)
          (psi W.dop W.vacuum L γ β (PsiIndex.pos r))) ^ 2).im := by
  let x : Fin p → ℂ := fun r =>
    stateInner (psi W.dop W.vacuum L γ β PsiIndex.zero)
      (psi W.dop W.vacuum L γ β (PsiIndex.pos r))
  change (energyFromCorrelations Γ G).re = (∑ r : Fin p, (γ r : ℂ) * (x r) ^ 2).im
  have hposTerm : ∀ r : Fin p,
      (Γ (posIdx p r) : ℂ) * (G (zeroIdx p) (posIdx p r)) ^ 2
        = (γ r : ℂ) * ((starRingEnd ℂ) (x r)) ^ 2 := by
    intro r
    rw [hΓpos r, hGpos r, stateInner_conj_symm]
  have hnegTerm : ∀ r : Fin p,
      (Γ (negIdx p r) : ℂ) * (G (zeroIdx p) (negIdx p r)) ^ 2
        = (-(γ r) : ℂ) * (x r) ^ 2 := by
    intro r
    rw [hΓneg r, hGneg r]
    push_cast
    rfl
  have hzeroTerm : (Γ (zeroIdx p) : ℂ) * (G (zeroIdx p) (zeroIdx p)) ^ 2 = 0 := by
    rw [hΓzero]
    simp
  have hposSum : (∑ r : Fin p, (Γ (posIdx p r) : ℂ) * (G (zeroIdx p) (posIdx p r)) ^ 2)
      = ∑ r : Fin p, (γ r : ℂ) * ((starRingEnd ℂ) (x r)) ^ 2 :=
    Finset.sum_congr rfl fun r _ => hposTerm r
  have hnegSum : (∑ r : Fin p, (Γ (negIdx p r) : ℂ) * (G (zeroIdx p) (negIdx p r)) ^ 2)
      = ∑ r : Fin p, (-(γ r) : ℂ) * (x r) ^ 2 :=
    Finset.sum_congr rfl fun r _ => hnegTerm r
  rw [energyFromCorrelations, sum_fin_three_blocks, hposSum, hnegSum, hzeroTerm, add_zero]
  have hcombine : (∑ r : Fin p, (γ r : ℂ) * ((starRingEnd ℂ) (x r)) ^ 2)
      + (∑ r : Fin p, (-(γ r) : ℂ) * (x r) ^ 2)
      = ∑ r : Fin p, (γ r : ℂ) * (((starRingEnd ℂ) (x r)) ^ 2 - (x r) ^ 2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hcombine]
  have hterm : ∀ r : Fin p,
      (Complex.I / 2 * ((γ r : ℂ) * (((starRingEnd ℂ) (x r)) ^ 2 - (x r) ^ 2))).re
        = ((γ r : ℂ) * (x r) ^ 2).im := by
    intro r
    have hcomm : Complex.I / 2 * ((γ r : ℂ) * (((starRingEnd ℂ) (x r)) ^ 2 - (x r) ^ 2))
        = (γ r : ℂ) * (Complex.I / 2 * (((starRingEnd ℂ) (x r)) ^ 2 - (x r) ^ 2)) := by
      ring
    rw [hcomm, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [re_I_div_two_mul_conj_sq_sub, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [Finset.mul_sum, Complex.re_sum, Complex.im_sum]
  exact Finset.sum_congr rfl fun r _ => hterm r

end Qatlib.Papers.SpinBosonQAOA26.MainResults.EnergyFromOverlaps
