/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# State Preparation and Decision Lemmas for Quantum Nearest-Neighbor Learning

This module formalizes the state-preparation, swap-test overlap, and likelihood-ratio
decision lemmas from [Wiebe, Kapoor, and Svore, 2015][WiebeKapoorSvore2015]:

* **Lemma 4** (`lemma4_columnMass`, `lemma4_exists_unitary`): unit-norm verification and
  explicit Householder unitary completion for the prescribed first-column magnitudes
  `|V_{00}| = 1/√2` and `|V_{j0}| = 1/√(2M)` (`j ≠ 0`).
* **Lemma 6** (`lemma6_uniformState_unit`, `lemma6_amplitude_value`): unit-norm verification
  for the uniform superposition `(1/√M) ∑_{j=1}^M |j⟩`.
* **Lemma 10** (`lemma10_branchMass`): branch-mass normalization for the `d`-sparse state
  preparation encoder.
* **Lemma 11** (`lemma11_swapIdentity`, `lemma11_stepCount`): swap-test inner-product
  recovery identity and amplitude-estimation step count.
* **Theorem 13** (`theorem13_distanceA_likelihood`, `theorem13_distanceB_likelihood`):
  consistency between normalized-distance classification and the Chebyshev likelihood-ratio
  decision rule.

## Main statements

* `lemma4_exists_unitary`
* `lemma6_uniformState_unit`
* `lemma10_branchMass`
* `lemma11_swapIdentity`
* `theorem13_distanceA_likelihood`
* `theorem13_distanceB_likelihood`

## References

* [Wiebe, Kapoor, and Svore, 2015][WiebeKapoorSvore2015]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NearestLearn14.MainResults.StatePrep

open Complex

/-- Lemma 4 (p. 17): the prescribed first-column magnitudes of `V`, namely
`|V_{00}| = 1/√2` and `|V_{j0}| = 1/√(2M)` for `j ≠ 0`. -/
def lemma4Amplitude (M : ℕ) (j : Fin (M + 1)) : ℝ :=
  if j = 0 then 1 / Real.sqrt 2 else 1 / Real.sqrt (2 * (M : ℝ))

/-- Lemma 4 (p. 17), column-mass identity: the prescribed column is a unit
vector, `(1/√2)² + M·(1/√(2M))² = 1/2 + 1/2 = 1`, as required for the first
column of the unitary `V` used in the nearest-centroid probability (6). -/
theorem lemma4_columnMass (M : ℕ) (hM : 0 < M) :
    ∑ j : Fin (M + 1), (lemma4Amplitude M j) ^ 2 = 1 := by
  rw [Fin.sum_univ_succ]
  have hzero : lemma4Amplitude M 0 = 1 / Real.sqrt 2 := by
    simp [lemma4Amplitude]
  have hsucc : ∀ i : Fin M, lemma4Amplitude M i.succ = 1 / Real.sqrt (2 * (M : ℝ)) := by
    intro i
    simp [lemma4Amplitude, Fin.succ_ne_zero]
  simp only [hzero, hsucc]
  have hM' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have h2 : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hM2 : (1 / Real.sqrt (2 * (M : ℝ))) ^ 2 = 1 / (2 * (M : ℝ)) := by
    rw [div_pow, one_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * (M : ℝ))]
  rw [Finset.sum_const, h2, hM2, Finset.card_univ]
  simp only [Fintype.card_fin, nsmul_eq_mul]
  have hMn : (M : ℝ) ≠ 0 := ne_of_gt hM'
  field_simp
  ring

/-- Nonnegativity of each prescribed first-column amplitude in Lemma 4. -/
private theorem lemma4Amplitude_nonneg (M : ℕ) (j : Fin (M + 1)) :
    0 ≤ lemma4Amplitude M j := by
  unfold lemma4Amplitude
  split_ifs <;> positivity

/-- Lemma 4 (Appendix B.1, p. 17) of [Wiebe, Kapoor, and Svore, 2015][WiebeKapoorSvore2015]:
a unitary `V` with first-column magnitudes `|V_{j0}| = 1/√2` for `j = 0` and
`1/√(2M)` otherwise exists, constructed explicitly as the real symmetric Householder
reflection `(2 / ‖e₀ + v‖²) (e₀ + v)(e₀ + v)ᵀ - I`. -/
theorem lemma4_exists_unitary (M : ℕ) (hM : 0 < M) :
    (∑ j : Fin (M + 1), (lemma4Amplitude M j) ^ 2 = 1) ∧
      ∃ V : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ,
        V ∈ Matrix.unitaryGroup (Fin (M + 1)) ℂ ∧
          ∀ j : Fin (M + 1), ‖V j 0‖ = lemma4Amplitude M j := by
  have hv_sum : ∑ j : Fin (M + 1), (lemma4Amplitude M j) ^ 2 = 1 :=
    lemma4_columnMass M hM
  refine ⟨hv_sum, ?_⟩
  let v : Fin (M + 1) → ℝ := lemma4Amplitude M
  let δ0 : Fin (M + 1) → ℝ := fun j => if j = 0 then 1 else 0
  let w : Fin (M + 1) → ℝ := fun j => δ0 j + v j
  let c : ℝ := 2 * (1 + v 0)
  have hv0_nonneg : 0 ≤ v 0 := lemma4Amplitude_nonneg M 0
  have hc_pos : 0 < c := by dsimp [c]; linarith
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hw_sum : ∑ k : Fin (M + 1), (w k) ^ 2 = c := by
    have hexp : ∀ k : Fin (M + 1), (w k) ^ 2 = (δ0 k) ^ 2 + 2 * (δ0 k * v k) + (v k) ^ 2 := by
      intro k; dsimp [w]; ring
    simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hδ2 : ∑ k : Fin (M + 1), (δ0 k) ^ 2 = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp [δ0]
      · intro k _ hk; simp [δ0, hk]
      · intro h0; exact absurd (Finset.mem_univ 0) h0
    have hδv : ∑ k : Fin (M + 1), δ0 k * v k = v 0 := by
      rw [Finset.sum_eq_single 0]
      · simp [δ0]
      · intro k _ hk; simp [δ0, hk]
      · intro h0; exact absurd (Finset.mem_univ 0) h0
    dsimp [c, v] at hv_sum ⊢
    linarith
  let UR : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ :=
    fun i j => (2 / c) * w i * w j - if i = j then 1 else 0
  let V : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ :=
    fun i j => ((UR i j : ℝ) : ℂ)
  have hV_star : star V = V := by
    ext i j
    change star ((UR j i : ℝ) : ℂ) = ((UR i j : ℝ) : ℂ)
    rw [Complex.star_def, Complex.conj_ofReal]
    congr 1
    dsimp [UR]
    by_cases hij : i = j
    · subst hij; ring
    · have hji : j ≠ i := Ne.symm hij
      simp [hij, hji]
      ring
  have hUR_sq : ∀ i l : Fin (M + 1),
      ∑ k : Fin (M + 1), UR i k * UR k l = if i = l then 1 else 0 := by
    intro i l
    have hexp : ∀ k : Fin (M + 1),
        UR i k * UR k l =
          ((2 / c) ^ 2 * w i * w l) * (w k) ^ 2 -
            (if k = l then (2 / c) * w i * w l else 0) -
            (if i = k then (2 / c) * w i * w l else 0) +
            (if i = k then (if k = l then (1 : ℝ) else 0) else 0) := by
      intro k
      dsimp [UR]
      by_cases hik : i = k <;> by_cases hkl : k = l
      · subst hik; subst hkl; simp; ring
      · subst hik; simp [hkl]; ring
      · subst hkl; simp [hik]; ring
      · simp [hik, hkl]; ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hs1 : (∑ k : Fin (M + 1), if k = l then (2 / c) * w i * w l else 0) =
        (2 / c) * w i * w l := by simp
    have hs2 : (∑ k : Fin (M + 1), if i = k then (2 / c) * w i * w l else 0) =
        (2 / c) * w i * w l := by simp
    have hs3 : (∑ k : Fin (M + 1), if i = k then (if k = l then (1 : ℝ) else 0) else 0) =
        if i = l then 1 else 0 := by simp
    rw [hw_sum, hs1, hs2, hs3]
    have hcancel : ((2 / c) ^ 2 * w i * w l) * c - (2 / c) * w i * w l - (2 / c) * w i * w l = 0 := by
      field_simp
      ring
    linarith
  have hV_sq : V * V = 1 := by
    ext i l
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hcast : (∑ k : Fin (M + 1), V i k * V k l) =
        (((∑ k : Fin (M + 1), UR i k * UR k l) : ℝ) : ℂ) := by
      dsimp [V]
      push_cast
      rfl
    rw [hcast, hUR_sq]
    split_ifs <;> simp
  refine ⟨V, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, hV_star]
    exact hV_sq
  · intro j
    have hUR_col : UR j 0 = v j := by
      dsimp [UR, w, δ0, c]
      have h1 : (1 : ℝ) + v 0 ≠ 0 := by linarith
      by_cases hj : j = 0
      · subst hj; simp; field_simp; ring
      · simp [hj]; field_simp
    dsimp [V]
    rw [hUR_col, Complex.norm_real, Real.norm_of_nonneg (lemma4Amplitude_nonneg M j)]

/-- Lemma 6 (p. 18): the uniform superposition amplitude `1/√M`. -/
def uniformAmplitude (M : ℕ) : Fin M → ℝ := fun _ => 1 / Real.sqrt (M : ℝ)

/-- Lemma 6 (p. 18): the state `(1/√M) Σ_{j=1}^M |j⟩` is a unit vector,
`Σ_j (1/√M)² = M·(1/M) = 1`, prepared in [Wiebe, Kapoor, and Svore, 2015][WiebeKapoorSvore2015]
via `H^{⊗m}`, comparison `CMP`, and exact amplitude amplification. -/
theorem lemma6_uniformState_unit (M : ℕ) (hM : 0 < M) :
    ∑ j : Fin M, (uniformAmplitude M j) ^ 2 = 1 := by
  simp only [uniformAmplitude]
  have hM' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have h2 : (1 / Real.sqrt (M : ℝ)) ^ 2 = 1 / (M : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hM')]
  rw [Finset.sum_const, h2, Finset.card_univ]
  simp only [Fintype.card_fin, nsmul_eq_mul]
  have hMn : (M : ℝ) ≠ 0 := ne_of_gt hM'
  field_simp

/-- Lemma 6 (p. 18): every amplitude of the prepared state equals `1/√M`. -/
theorem lemma6_amplitude_value (M : ℕ) (j : Fin M) :
    uniformAmplitude M j = 1 / Real.sqrt (M : ℝ) := rfl

/-- Lemma 10 (p. 21, (B19)–(B22)): for a `d`-sparse vector the branch masses of
the encoder `1/√d Σ_i |f(j,i)⟩ (√(1−r²/R²)|0⟩ + (r/R)|1⟩)` sum to one on every
branch, `(1−r²/R²) + (r/R)² = 1`, hence the encoded vector has norm one and the
three-oracle-call circuit of (B20)–(B22) is a well-formed state preparation. -/
theorem lemma10_branchMass (d : ℕ) (hd : 0 < d) (r : Fin d → ℝ) (R : ℝ) (_hR : 0 < R) :
    (1 / (d : ℝ)) * ∑ i : Fin d, ((1 - (r i) ^ 2 / R ^ 2) + (r i / R) ^ 2) = 1 := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hterm : ∀ i : Fin d, ((1 - (r i) ^ 2 / R ^ 2) + (r i / R) ^ 2) = 1 := by
    intro i
    rw [div_pow]
    ring
  simp only [hterm]
  rw [Finset.sum_const, Finset.card_univ]
  simp only [Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hdn : (d : ℝ) ≠ 0 := ne_of_gt hd'
  field_simp

/-- Lemma 11 (p. 22, eq. (B26)): the swap-test identity
`(2|A|−1) d² r₀max² r_jmax² = |⟨u|v_j⟩|²`, written for the amplitude relation
`|A| = (1 + x²/(d²r₀²r_j²))/2` where `x = |⟨u|v_j⟩|` and the overlap is
`⟨φ|ψ⟩ = ⟨v₀|v_j⟩/(d r₀max r_jmax)` (B25). -/
theorem lemma11_swapIdentity (x : ℝ) (d : ℕ) (hd : 0 < d) (r0 rj : ℝ)
    (h0 : r0 ≠ 0) (hj : rj ≠ 0) :
    (2 * ((1 + x ^ 2 / ((d : ℝ) ^ 2 * r0 ^ 2 * rj ^ 2)) / 2) - 1) *
        ((d : ℝ) ^ 2 * r0 ^ 2 * rj ^ 2) = x ^ 2 := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hden : ((d : ℝ) ^ 2 * r0 ^ 2 * rj ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hd') (pow_ne_zero 2 h0)) (pow_ne_zero 2 hj)
  field_simp [hden]
  ring

/-- Lemma 11 (p. 22, (B29)–(B31)): the amplitude-estimation step count needed
for relative error `δ` is `R ≥ π(π+1)/δ`, and with `δ = ε/(4d²r₀²r_j²)`
(B30) this is exactly `R ≥ 4π(π+1)d²r₀²r_j²/ε`, whose twelvefold is the
announced `Q` (B32). -/
theorem lemma11_stepCount (d : ℕ) (r0 rj ε : ℝ) (hd : 0 < d) (_h0 : 0 < r0) (_hj : 0 < rj)
    (_hε : 0 < ε) :
    Real.pi * (Real.pi + 1) / (ε / (4 * (d : ℝ) ^ 2 * r0 ^ 2 * rj ^ 2))
      = 4 * Real.pi * (Real.pi + 1) * (d : ℝ) ^ 2 * r0 ^ 2 * rj ^ 2 / ε := by
  have _hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have _hden : (4 * (d : ℝ) ^ 2 * r0 ^ 2 * rj ^ 2) ≠ 0 := by positivity
  field_simp

/-- Theorem 13 (p. 27, (C3)–(C4)), direction `A`: under the Chebyshev
envelopes `aσ_A²/χ² ≤ Pr_A` and `Pr_B ≤ βσ_B²/χ²`, the condition `a ≥ β`
(the paper's first disjunct) and a normalized-distance assignment to `{A}`
(`(σ_B/ξ_B)/(σ_A/ξ_A) ≤ 1`) imply a likelihood ratio at least one,
`1 ≤ Pr_A/Pr_B`, i.e. the likelihood-ratio test also assigns `{A}`. -/
theorem theorem13_distanceA_likelihood (a β σA σB ξA ξB PA PB : ℝ)
    (ha : 0 < a) (_hβ : 0 < β) (hσA : 0 < σA) (hσB : 0 < σB)
    (hξA : 0 < ξA) (hξB : 0 < ξB) (_hPA : 0 < PA) (hPB : 0 < PB)
    (hPA_low : a * σA ^ 2 / ξA ^ 2 ≤ PA)
    (hPB_up : PB ≤ β * σB ^ 2 / ξB ^ 2)
    (hdist : (σB / ξB) / (σA / ξA) ≤ 1)
    (hcond : β ≤ a) :
    1 ≤ PA / PB := by
  have hratio : σB / ξB ≤ σA / ξA :=
    (div_le_one (by positivity : (0 : ℝ) < σA / ξA)).1 hdist
  have hsq : (σB / ξB) ^ 2 ≤ (σA / ξA) ^ 2 := by
    simpa [pow_two] using
      mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ σB / ξB) hratio
  have hmul : β * (σB / ξB) ^ 2 ≤ a * (σA / ξA) ^ 2 :=
    mul_le_mul hcond hsq (sq_nonneg _) (le_of_lt ha)
  have hchain : PB ≤ a * σA ^ 2 / ξA ^ 2 := by
    calc PB ≤ β * σB ^ 2 / ξB ^ 2 := hPB_up
      _ = β * (σB / ξB) ^ 2 := by ring
      _ ≤ a * (σA / ξA) ^ 2 := hmul
      _ = a * σA ^ 2 / ξA ^ 2 := by ring
  rw [le_div_iff₀ hPB]
  linarith

/-- Theorem 13 (p. 27, (C5)), direction `B`: under the Chebyshev envelopes
`Pr_A ≤ ασ_A²/χ²` and `bσ_B²/χ² ≤ Pr_B`, the condition `α ≤ b` and a
normalized-distance assignment to `{B}` (`1 ≤ (σ_B/ξ_B)/(σ_A/ξ_A)`) imply a
likelihood ratio at most one, `Pr_A/Pr_B ≤ 1`, i.e. the likelihood-ratio test
also assigns `{B}`. -/
theorem theorem13_distanceB_likelihood (b α σA σB ξA ξB PA PB : ℝ)
    (hb : 0 < b) (_hα : 0 < α) (hσA : 0 < σA) (_hσB : 0 < σB)
    (hξA : 0 < ξA) (_hξB : 0 < ξB) (_hPA : 0 < PA) (hPB : 0 < PB)
    (hPA_up : PA ≤ α * σA ^ 2 / ξA ^ 2)
    (hPB_low : b * σB ^ 2 / ξB ^ 2 ≤ PB)
    (hdist : 1 ≤ (σB / ξB) / (σA / ξA))
    (hcond : α ≤ b) :
    PA / PB ≤ 1 := by
  have hratio : σA / ξA ≤ σB / ξB :=
    (one_le_div (by positivity : (0 : ℝ) < σA / ξA)).1 hdist
  have hsq : (σA / ξA) ^ 2 ≤ (σB / ξB) ^ 2 := by
    simpa [pow_two] using
      mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ σA / ξA) hratio
  have hmul : α * (σA / ξA) ^ 2 ≤ b * (σB / ξB) ^ 2 :=
    mul_le_mul hcond hsq (sq_nonneg _) (le_of_lt hb)
  have hchain : PA ≤ b * σB ^ 2 / ξB ^ 2 := by
    calc PA ≤ α * σA ^ 2 / ξA ^ 2 := hPA_up
      _ = α * (σA / ξA) ^ 2 := by ring
      _ ≤ b * (σB / ξB) ^ 2 := hmul
      _ = b * σB ^ 2 / ξB ^ 2 := by ring
  rw [div_le_one hPB]
  linarith

end Qatlib.Papers.NearestLearn14.MainResults.StatePrep
