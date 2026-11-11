/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.HermitianFunctionStability

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 6.12: the smoothened principal-component filter on the actual spectrum

Source: arXiv:1910.06151v4 (fixed version), Section 6.4 (principal component analysis).

The classical PCA corollary estimates the top `k` eigenvalues of `X†X` from sketched spectral
data, then applies the smoothened indicator `f_i` of Corollary 6.12's proof to the *actual*
matrix `X†X` so that `f_i(X†X) = v_i v_i†` holds exactly; the sketch error is then paid only
through Theorem 5.1 applied to `f_i`.

The paper defines the five-branch piecewise-linear function

```
f_i(x) = 0                                              x - λ̂_i < -η‖X‖²/4
         2 + 8/(η‖X‖²) (x - λ̂_i)                       -η‖X‖²/4 ≤ x - λ̂_i < -η‖X‖²/8
         1                                              |x - λ̂_i| < η‖X‖²/8
         2 - 8/(η‖X‖²) (x - λ̂_i)                       η‖X‖²/8 ≤ x - λ̂_i < η‖X‖²/4
         0                                              η‖X‖²/4 ≤ x - λ̂_i
```

This file formalizes, with `S := ‖X‖²` and `r := ηS`:

* `principalFilter` — the five branches verbatim;
* `principalFilter_eq_clamp` — the branches are the clamped tent
  `max 0 (min 1 (2 - 8|x - λ̂_i| / r))`, from which boundedness and the Lipschitz constant
  `L = 8/(ηS)` follow (`principalFilter_nonneg`, `principalFilter_le_one`,
  `principalFilter_lipschitz`);
* `principalFilter_eq_one_of_abs_le` / `principalFilter_eq_zero_of_le_abs` — the exact
  one/zero regions, and `principalFilter_exact_of_estimates` — the transfer
  `f_i(λ_i) = 1`, `f_i(λ_j) = 0` for `j ≠ i` from the spectral gap `ηS ≤ |λ_j - λ_i|` and
  the eigenvalue estimate `|λ̂_i - λ_i| ≤ ηS/8`;
* `hermitianFunction_principalFilter_eq_rankOne` — the paper's conclusion
  `f_i(X†X) = v_i v_i†` for a Hermitian matrix with the ordered eigenbasis, i.e. the filter
  reproduces the exact rank-one spectral projector of the `i`-th eigenvector;
* `principalFilter_zero` — `f_i(0) = 0`, the hypothesis Theorem 5.1 needs;
* the eigenvalue-estimate aggregation of the proof (`sum_abs_le_sqrt_card_mul_sqrt_sum_sq`,
  `eigenvalue_l1_le`, `eigenvalue_coord_le`) and the Theorem 5.1 parameter identities
  (`filter_lipschitz_norm_condition`, `filter_row_budget`).

Not covered here: the sketched eigenvalue computation of Lemma 4.9, the Theorem 5.1 output
guarantee for `R† f̄_i(CC†) R`, the extraction of `v̂_i` from that rank-one approximation, the
sampling/query access statement and the Corollary 6.12 runtime `r`, `c`, `sq̃(v̂_i)`. Those
consume the even-SVT sketch contracts of `EvenSVT` and the SQ-closure ledger; this file only
supplies the exact-spectrum filter step they depend on.
-/

set_option autoImplicit false

namespace Qatlib.Papers.LowRankMatrix19.LowRankPCA

open Matrix
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.WalkSearch.Spectral
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## 1. The smoothened spectral filter -/

/-- Corollary 6.12's smoothened indicator of the `i`-th eigenvalue estimate `λ̂_i`.

`S` is `‖X‖²` (the squared spectral norm) and the transition half-width used by the paper is
`η‖X‖²`, so the branches are stated in terms of `η * S`. The estimate `λ̂_i` is `lhat`. -/
noncomputable def principalFilter (S η lhat x : ℝ) : ℝ :=
  if x - lhat < -(1 / 4) * η * S then 0
  else if x - lhat < -(1 / 8) * η * S then 2 + 8 / (η * S) * (x - lhat)
  else if x - lhat < (1 / 8) * η * S then 1
  else if x - lhat < (1 / 4) * η * S then 2 - 8 / (η * S) * (x - lhat)
  else 0

/-- A clamped value that is already nonpositive clamps to zero. -/
private lemma clamp_zero (g : ℝ) (h : g ≤ 0) : max 0 (min 1 g) = 0 := by
  rw [min_eq_right (le_trans h zero_le_one), max_eq_left h]

/-- A clamped value that is already at least one clamps to one. -/
private lemma clamp_one (g : ℝ) (h : 1 ≤ g) : max 0 (min 1 g) = 1 := by
  rw [min_eq_left h, max_eq_right zero_le_one]

/-- A clamped value inside `[0, 1]` is unchanged. -/
private lemma clamp_self (g : ℝ) (h0 : 0 ≤ g) (h1 : g ≤ 1) : max 0 (min 1 g) = g := by
  rw [min_eq_right h1, max_eq_right h0]

/-- The five printed branches are exactly the clamped tent
`max 0 (min 1 (2 - 8|x - λ̂_i|/(ηS)))`. -/
theorem principalFilter_eq_clamp (S η lhat x : ℝ) (hS : 0 < S) (hη : 0 < η) :
    principalFilter S η lhat x
      = max 0 (min 1 (2 - 8 * |x - lhat| / (η * S))) := by
  have hr : 0 < η * S := mul_pos hη hS
  have h8 : 0 < 8 / (η * S) := div_pos (by norm_num) hr
  set t := x - lhat with ht
  -- unfold and rewrite the branch conditions in terms of `t`
  unfold principalFilter
  rw [← ht]
  split_ifs with h1 h2 h3 h4
  · -- far left: the tent is nonpositive
    have hneg : t < 0 := by nlinarith
    rw [abs_of_neg hneg]
    refine (clamp_zero _ ?_).symm
    · have : (1 / 4) * (η * S) < -t := by linarith
      have : 2 ≤ 8 / (η * S) * (-t) := by
        calc 2 = 8 / (η * S) * ((1 / 4) * (η * S)) := by field_simp; norm_num
          _ ≤ 8 / (η * S) * (-t) := by exact mul_le_mul_of_nonneg_left (le_of_lt this) (le_of_lt h8)
      have hle : 2 - 8 * (-t) / (η * S) ≤ 0 := by
        rw [show 8 * (-t) / (η * S) = 8 / (η * S) * (-t) by ring]
        linarith
      exact hle
  · -- left ramp: the tent lies in `[0, 1]` and equals the branch value
    have hneg : t < 0 := by nlinarith
    rw [abs_of_neg hneg]
    have hlow : (1 / 8) * (η * S) < -t := by linarith
    have hhigh : -t ≤ (1 / 4) * (η * S) := by linarith
    have hge1 : 1 ≤ 8 / (η * S) * (-t) := by
      calc 1 = 8 / (η * S) * ((1 / 8) * (η * S)) := by field_simp
        _ ≤ 8 / (η * S) * (-t) := mul_le_mul_of_nonneg_left (le_of_lt hlow) (le_of_lt h8)
    have hle2 : 8 / (η * S) * (-t) ≤ 2 := by
      calc 8 / (η * S) * (-t) ≤ 8 / (η * S) * ((1 / 4) * (η * S)) :=
            mul_le_mul_of_nonneg_left hhigh (le_of_lt h8)
        _ = 2 := by field_simp; norm_num
    have h0 : 0 ≤ 2 - 8 * (-t) / (η * S) := by
      rw [show 8 * (-t) / (η * S) = 8 / (η * S) * (-t) by ring]; linarith
    have h1' : 2 - 8 * (-t) / (η * S) ≤ 1 := by
      rw [show 8 * (-t) / (η * S) = 8 / (η * S) * (-t) by ring]; linarith
    rw [clamp_self _ h0 h1']
    ring
  · -- plateau: the tent is at least one
    have hb : -((1 / 8) * (η * S)) ≤ t := by linarith
    have habs : |t| ≤ (1 / 8) * (η * S) := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    rw [clamp_one _ ?_]
    have : 8 * |t| / (η * S) ≤ 1 := by
      rw [div_le_iff₀ hr]
      calc 8 * |t| ≤ 8 * ((1 / 8) * (η * S)) := by
            exact mul_le_mul_of_nonneg_left habs (by norm_num)
        _ = 1 * (η * S) := by ring
    linarith
  · -- right ramp
    have hpos : 0 ≤ t := by linarith
    rw [abs_of_nonneg hpos]
    have hlow : (1 / 8) * (η * S) ≤ t := by linarith
    have hhigh : t < (1 / 4) * (η * S) := by linarith [h4]
    have hge1 : 1 ≤ 8 / (η * S) * t := by
      calc 1 = 8 / (η * S) * ((1 / 8) * (η * S)) := by field_simp
        _ ≤ 8 / (η * S) * t := mul_le_mul_of_nonneg_left hlow (le_of_lt h8)
    have hle2 : 8 / (η * S) * t < 2 := by
      calc 8 / (η * S) * t < 8 / (η * S) * ((1 / 4) * (η * S)) :=
            mul_lt_mul_of_pos_left hhigh h8
        _ = 2 := by field_simp; norm_num
    have h0 : 0 ≤ 2 - 8 * t / (η * S) := by
      rw [show 8 * t / (η * S) = 8 / (η * S) * t by ring]; linarith
    have h1' : 2 - 8 * t / (η * S) ≤ 1 := by
      rw [show 8 * t / (η * S) = 8 / (η * S) * t by ring]; linarith
    rw [clamp_self _ h0 h1']
    ring
  · -- far right: the tent is nonpositive
    have hpos : 0 < t := by nlinarith
    rw [abs_of_pos hpos]
    rw [clamp_zero _ ?_]
    have : (1 / 4) * (η * S) ≤ t := by linarith
    have : 2 ≤ 8 / (η * S) * t := by
      calc 2 = 8 / (η * S) * ((1 / 4) * (η * S)) := by field_simp; norm_num
        _ ≤ 8 / (η * S) * t := mul_le_mul_of_nonneg_left this (le_of_lt h8)
    rw [show 8 * t / (η * S) = 8 / (η * S) * t by ring]; linarith

/-- The filter takes values in `[0, 1]`. -/
theorem principalFilter_nonneg (S η lhat x : ℝ) (hS : 0 < S) (hη : 0 < η) :
    0 ≤ principalFilter S η lhat x := by
  rw [principalFilter_eq_clamp S η lhat x hS hη]
  exact le_max_left _ _

/-- The filter never exceeds one. -/
theorem principalFilter_le_one (S η lhat x : ℝ) (hS : 0 < S) (hη : 0 < η) :
    principalFilter S η lhat x ≤ 1 := by
  rw [principalFilter_eq_clamp S η lhat x hS hη]
  exact max_le zero_le_one (min_le_left _ _)

/-- `min 1 ·` is nonexpansive. -/
theorem abs_min_one_sub_min_one_le (a b : ℝ) : |min 1 a - min 1 b| ≤ |a - b| := by
  have h := abs_min_sub_min_le_max 1 a 1 b
  simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (a - b))] using h

/-- `max 0 (min 1 ·)` is nonexpansive. -/
theorem abs_clamp_sub_clamp_le (a b : ℝ) :
    |max 0 (min 1 a) - max 0 (min 1 b)| ≤ |a - b| := by
  have h1 : |max 0 (min 1 a) - max 0 (min 1 b)| ≤ |min 1 a - min 1 b| := by
    simpa only [max_comm] using abs_max_sub_max_le_abs (min 1 a) (min 1 b) 0
  exact le_trans h1 (abs_min_one_sub_min_one_le a b)

/-- The filter is `8/(ηS)`-Lipschitz; this is the constant `L` that Corollary 6.12's proof
feeds into Theorem 5.1. -/
theorem principalFilter_lipschitz (S η lhat : ℝ) (hS : 0 < S) (hη : 0 < η) (x y : ℝ) :
    |principalFilter S η lhat x - principalFilter S η lhat y|
      ≤ 8 / (η * S) * |x - y| := by
  have hr : 0 < η * S := mul_pos hη hS
  have hc : 0 ≤ 8 / (η * S) := le_of_lt (div_pos (by norm_num) hr)
  rw [principalFilter_eq_clamp S η lhat x hS hη, principalFilter_eq_clamp S η lhat y hS hη]
  refine le_trans (abs_clamp_sub_clamp_le _ _) ?_
  have hfac : (2 - 8 * |x - lhat| / (η * S)) - (2 - 8 * |y - lhat| / (η * S))
      = 8 / (η * S) * (|y - lhat| - |x - lhat|) := by ring
  rw [hfac, abs_mul, abs_of_nonneg hc, abs_sub_comm]
  refine mul_le_mul_of_nonneg_left ?_ hc
  have htri := abs_abs_sub_abs_le (x - lhat) (y - lhat)
  have he : (x - lhat) - (y - lhat) = x - y := by ring
  rwa [he] at htri

/-- The `1` region: `|x - λ̂_i| ≤ ηS/8` gives `f_i(x) = 1`. -/
theorem principalFilter_eq_one_of_abs_le (S η lhat x : ℝ) (hS : 0 < S) (hη : 0 < η)
    (h : |x - lhat| ≤ η * S / 8) : principalFilter S η lhat x = 1 := by
  have hr : 0 < η * S := mul_pos hη hS
  rw [principalFilter_eq_clamp S η lhat x hS hη]
  refine clamp_one _ ?_
  have h8 : 8 * |x - lhat| / (η * S) ≤ 1 := by
    rw [div_le_iff₀ hr]
    nlinarith
  linarith

/-- The `0` region: `ηS/4 ≤ |x - λ̂_i|` gives `f_i(x) = 0`. -/
theorem principalFilter_eq_zero_of_le_abs (S η lhat x : ℝ) (hS : 0 < S) (hη : 0 < η)
    (h : η * S / 4 ≤ |x - lhat|) : principalFilter S η lhat x = 0 := by
  have hr : 0 < η * S := mul_pos hη hS
  rw [principalFilter_eq_clamp S η lhat x hS hη]
  refine clamp_zero _ ?_
  have h8 : 2 ≤ 8 * |x - lhat| / (η * S) := by
    rw [le_div_iff₀ hr]
    nlinarith
  linarith

/-- The paper's transfer: with the spectral gap `ηS ≤ |λ_j - λ_i|` and the estimate
`|λ̂_i - λ_i| ≤ ηS/8`, the filter is one exactly at `λ_i` and zero at every other `λ_j`. -/
theorem principalFilter_exact_of_estimates {k : ℕ} (lam lamhat : Fin k → ℝ) (i : Fin k)
    (S η : ℝ) (hS : 0 < S) (hη : 0 < η)
    (hgap : ∀ j, j ≠ i → η * S ≤ |lam j - lam i|)
    (hest : |lamhat i - lam i| ≤ η * S / 8) :
    principalFilter S η (lamhat i) (lam i) = 1
      ∧ ∀ j, j ≠ i → principalFilter S η (lamhat i) (lam j) = 0 := by
  have hr : 0 < η * S := mul_pos hη hS
  refine ⟨principalFilter_eq_one_of_abs_le S η (lamhat i) (lam i) hS hη (by
    rw [abs_sub_comm]; exact hest), ?_⟩
  intro j hj
  apply principalFilter_eq_zero_of_le_abs S η (lamhat i) (lam j) hS hη
  have hg := hgap j hj
  have htri : |lam j - lam i| - |lam i - lamhat i| ≤ |lam j - lamhat i| := by
    have h := abs_sub_abs_le_abs_add (lam j - lam i) (lam i - lamhat i)
    have he : (lam j - lam i) + (lam i - lamhat i) = lam j - lamhat i := by ring
    rwa [he] at h
  have he' : |lam i - lamhat i| ≤ η * S / 8 := by rw [abs_sub_comm]; exact hest
  nlinarith

/-! ## 2. The exact rank-one spectral projector

Corollary 6.12's proof uses that `f_i(X†X) = v_i v_i†` holds exactly once the eigenvalues are
separated by the gap. The `i`-th eigenvector `v_i` is the `i`-th column of the ordered
eigenbasis of `X†X`; `f_i(X†X)` is `hermitianFunction` applied to the filter. -/

/-- A single spectral diagonal entry is the rank-one projector of the corresponding basis
vector: `spectralDiagonal b (Pi.single i 1) = v_i v_i†`. -/
theorem spectralDiagonal_piSingle_eq_rankOne {I : Type} [Fintype I] [DecidableEq I]
    (b : OrthonormalBasis (Fin (Fintype.card I)) ℂ (EuclideanSpace ℂ I))
    (i : Fin (Fintype.card I)) :
    spectralDiagonal b (Pi.single i (1 : ℂ))
      = Matrix.of (fun a c => (b i).ofLp a * star ((b i).ofLp c)) := by
  ext a c
  set g : Fin (Fintype.card I) → ℂ := Pi.single i (1 : ℂ) with hg
  rw [spectralDiagonal, Matrix.mul_apply]
  have hmul : ∀ p : Fin (Fintype.card I),
      (basisColumns b * Matrix.diagonal g) a p = basisColumns b a p * g p := by
    intro p
    rw [Matrix.mul_apply, Finset.sum_eq_single p]
    · rw [Matrix.diagonal_apply_eq]
    · intro q _ hqp
      rw [Matrix.diagonal_apply_ne _ hqp, mul_zero]
    · intro hp
      exact absurd (Finset.mem_univ p) hp
  simp only [hmul]
  rw [Finset.sum_eq_single i]
  · rw [show g i = 1 from by simp [hg], mul_one, Matrix.conjTranspose_apply,
      basisColumns_apply, basisColumns_apply]
    rfl
  · intro p _ hp
    rw [show g p = 0 from by simp [hg, hp], mul_zero, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **Corollary 6.12 filter identity.** For a Hermitian matrix with ordered eigenvalues `λ`,
if `|λ_i - λ̂_i| ≤ ηS/8` and every other eigenvalue is at distance at least `ηS` from `λ_i`,
then applying the paper's filter to the matrix-spectral decomposition yields exactly
`v_i v_i†`. -/
theorem hermitianFunction_principalFilter_eq_rankOne {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℂ} (hA : A.IsHermitian) (i : Fin (Fintype.card I))
    (S η lhat : ℝ) (hS : 0 < S) (hη : 0 < η)
    (hown : |orderedHermitianValues hA i - lhat| ≤ η * S / 8)
    (hother : ∀ j : Fin (Fintype.card I), j ≠ i →
      η * S ≤ |orderedHermitianValues hA j - orderedHermitianValues hA i|) :
    hermitianFunction A hA (fun x => (principalFilter S η lhat x : ℂ))
      = Matrix.of (fun a c =>
          (orderedHermitianBasis hA i).ofLp a * star ((orderedHermitianBasis hA i).ofLp c)) := by
  have hfun : (fun j => ((principalFilter S η lhat (orderedHermitianValues hA j) : ℝ) : ℂ))
      = (Pi.single i (1 : ℂ) : Fin (Fintype.card I) → ℂ) := by
    funext j
    by_cases hj : j = i
    · subst hj
      rw [principalFilter_eq_one_of_abs_le S η lhat (orderedHermitianValues hA j) hS hη hown]
      simp
    · rw [(principalFilter_exact_of_estimates (fun j => orderedHermitianValues hA j)
        (fun _ => lhat) i S η hS hη hother (by simpa only [abs_sub_comm] using hown)).2 j hj]
      simp [hj]
  unfold hermitianFunction
  rw [hfun, spectralDiagonal_piSingle_eq_rankOne]

/-! ## 3. The eigenvalue estimates of Corollary 6.12

Corollary 6.12 first turns the sketched spectral estimate of Lemma 4.9 into
`∑ᵢ |λ̂ᵢ - λᵢ| ≤ ε‖X‖²_F` and `|λ̂ᵢ - λᵢ| ≤ η‖X‖²/8`. -/

/-- Cauchy–Schwarz for the `ℓ¹`-`ℓ²` comparison of `k` eigenvalue errors:
`∑ |aᵢ| ≤ √k · √(∑ aᵢ²)`. -/
theorem sum_abs_le_sqrt_card_mul_sqrt_sum_sq {k : ℕ} (a : Fin k → ℝ) :
    (∑ i, |a i|) ≤ Real.sqrt (k : ℝ) * Real.sqrt (∑ i, (a i) ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ) (fun i => |a i|) (fun _ => (1 : ℝ))
  have h1 : (∑ i, |a i| * 1) = ∑ i, |a i| := by simp
  have h2 : (∑ i, |a i| ^ 2) = ∑ i, (a i) ^ 2 := by
    exact Finset.sum_congr rfl (fun i _ => by rw [sq_abs])
  have h3 : (∑ _i : Fin k, (1 : ℝ) ^ 2) = (k : ℝ) := by
    simp
  rw [h1, h2, h3] at h
  calc (∑ i, |a i|) ≤ Real.sqrt (∑ i, (a i) ^ 2) * Real.sqrt (k : ℝ) := h
    _ = Real.sqrt (k : ℝ) * Real.sqrt (∑ i, (a i) ^ 2) := mul_comm _ _

/-- Corollary 6.12's eigenvalue aggregation: from the squared-error estimate
`∑ (λ̂ᵢ - λᵢ)² ≤ (ε√λ_k/8)²` and `k·λ_k ≤ ‖X‖_F²` (`K ≥ k`), the total eigenvalue error is
`∑ |λ̂ᵢ - λᵢ| ≤ ε‖X‖_F/8`; the paper absorbs the constant `8` into `ε` and prints
`ε‖X‖_F²`. -/
theorem eigenvalue_l1_le {k : ℕ} (lam lamhat : Fin k → ℝ) {ε lamk F : ℝ}
    (hε : 0 ≤ ε) (hF : 0 < F)
    (hk : (k : ℝ) * lamk ≤ F ^ 2)
    (hest : ∑ i, (lamhat i - lam i) ^ 2 ≤ (ε * Real.sqrt lamk / 8) ^ 2) :
    (∑ i, |lamhat i - lam i|) ≤ ε * F / 8 := by
  have hsum : 0 ≤ ∑ i, (lamhat i - lam i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hA : 0 ≤ ε * Real.sqrt lamk / 8 := by positivity
  have hsq : Real.sqrt (∑ i, (lamhat i - lam i) ^ 2) ≤ ε * Real.sqrt lamk / 8 := by
    rw [← Real.sqrt_sq hA]
    exact Real.sqrt_le_sqrt hest
  have hcard : Real.sqrt (k : ℝ) * Real.sqrt lamk = Real.sqrt ((k : ℝ) * lamk) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg k)]
  have hFk : Real.sqrt ((k : ℝ) * lamk) ≤ F := by
    rw [← Real.sqrt_sq (le_of_lt hF)]
    exact Real.sqrt_le_sqrt hk
  calc (∑ i, |lamhat i - lam i|)
      ≤ Real.sqrt (k : ℝ) * Real.sqrt (∑ i, (lamhat i - lam i) ^ 2) :=
        sum_abs_le_sqrt_card_mul_sqrt_sum_sq _
    _ ≤ Real.sqrt (k : ℝ) * (ε * Real.sqrt lamk / 8) := by
        exact mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
    _ = ε / 8 * (Real.sqrt (k : ℝ) * Real.sqrt lamk) := by ring
    _ = ε / 8 * Real.sqrt ((k : ℝ) * lamk) := by rw [hcard]
    _ ≤ ε / 8 * F := by exact mul_le_mul_of_nonneg_left hFk (by positivity)
    _ = ε * F / 8 := by ring

/-- A single eigenvalue error is bounded by the square root of the squared-error budget, which
is what the filter's `ηS/8` hypothesis needs. -/
theorem eigenvalue_coord_le {k : ℕ} (lam lamhat : Fin k → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hest : ∑ i, (lamhat i - lam i) ^ 2 ≤ A ^ 2) (i : Fin k) :
    |lamhat i - lam i| ≤ A := by
  have hsingle : (lamhat i - lam i) ^ 2 ≤ ∑ j, (lamhat j - lam j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (lamhat j - lam j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hsq : Real.sqrt ((lamhat i - lam i) ^ 2) ≤ A := by
    rw [← Real.sqrt_sq hA]
    exact Real.sqrt_le_sqrt (le_trans hsingle hest)
  rwa [Real.sqrt_sq_eq_abs] at hsq

/-! ## 4. Theorem 5.1 parameters for the filter

Corollary 6.12 chooses the Theorem 5.1 sample parameters `r`, `c` from the filter's Lipschitz
constant `L = 8/(η‖X‖²)` and checks the smallness condition `ε ≲ 8 ≤ L‖X‖²`. -/

/-- `L‖X‖² = (8/(ηS))·S = 8/η`: the filter's Lipschitz constant times the squared spectral norm
is independent of `‖X‖`. -/
theorem filter_lipschitz_mul_norm (S η : ℝ) (hS : S ≠ 0) (hη : η ≠ 0) :
    8 / (η * S) * S = 8 / η := by
  field_simp

/-- The Theorem 5.1 smallness hypothesis `ε ≤ L‖X‖²` holds as soon as `ε ≤ 8` and `η ≤ 1`,
which is the paper's "the conditions of Theorem 5.1 are satisfied because `ε ≲ 8 ≤ 8/η = L‖X‖²`". -/
theorem filter_lipschitz_norm_condition (S η ε : ℝ) (hS : 0 < S) (hη0 : 0 < η)
    (hη1 : η ≤ 1) (hε : ε ≤ 8) : ε ≤ 8 / (η * S) * S := by
  rw [filter_lipschitz_mul_norm S η (ne_of_gt hS) (ne_of_gt hη0)]
  have : 8 ≤ 8 / η := by
    rw [le_div_iff₀ hη0]; nlinarith
  linarith

/-- The `r`-parameter of Theorem 5.1 for the PCA filter,
`r = L²‖X‖²‖X‖_F² ε⁻² log(1/δ)`, is `64‖X‖_F²/(η²‖X‖²ε²) log(1/δ)`; Corollary 6.12 prints
the same expression with the constant absorbed into `Õ`. -/
theorem filter_row_budget (S F η ε δ : ℝ) (hS : S ≠ 0) (hη : η ≠ 0) (hε : ε ≠ 0) :
    (8 / (η * S)) ^ 2 * S * F ^ 2 / ε ^ 2 * Real.log (1 / δ)
      = 64 * F ^ 2 / (η ^ 2 * S * ε ^ 2) * Real.log (1 / δ) := by
  field_simp
  ring

end

end Qatlib.Papers.LowRankMatrix19.LowRankPCA
