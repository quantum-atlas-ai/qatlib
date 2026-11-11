/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BoolHidShift11.InputModel.BHSPModel.SourceBHSP

set_option backward.isDefEq.respectTransparency false

/-!
# BoolHidShift11.MainResults.InfluenceFourier — Lemma 1 of arXiv:1103.3017v1

Fixed version: arXiv:1103.3017v1 (2011-03-15, Gavinsky–Roetteler–Roland),
Lemma 1 on p.2 (proved in Appendix A, pp.6–7):

`γ_{f,v} = Σ_{u : ⟨v,u⟩ = 1} F̂(u)²`, where `F(x) = (-1)^{f(x)}` (equation (1))
and `F̂(u) = 2^{-n} Σ_x F(x) χ_u(x)`.

The development follows Appendix A exactly:

* `chi_xor`, `sum_chi`, `sum_chi_mul`, `sum_chi_triple`: character algebra and
  orthogonality (`Σ_u χ_u(z) = 2^n [z = 0]`);
* `sum_chi_fourier_mul`: the shifted correlation
  `Σ_u χ_v(u) F̂(u)² = 2^{-n} Σ_x F(x) F(x+v)`;
* `sum_sq_fourier`: Parseval `Σ_u F̂(u)² = 1`;
* `indicator_eq_half`: the paper's indicator `1_{⟨v,u⟩=1} = (1 - χ_v(u))/2`;
* `influence_eq_half`: `γ_{f,v} = (1/2)(1 - 2^{-n} Σ_x F(x)F(x+v))`.

The final linear combination is Lemma 1. No `sorry`, no additional hypotheses
beyond the paper's `±1`-valuedness `F(x)² = 1`.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open scoped BigOperators

namespace Qatlib.Papers.BoolHidShift11.ShiftSample.InfluenceFourier

open Qatlib.Papers.BoolHidShift11.InputModel.BHSPModel

/-! ### Character identities -/

/-- Characters are multiplicative under the group law `regXor`:
`χ_u(x+v) = χ_u(x)·χ_u(v)`. -/
theorem chi_xor {n : ℕ} (u x y : Reg n) :
    chi u (regXor x y) = chi u x * chi u y := by
  unfold chi regXor
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rcases u i <;> rcases x i <;> rcases y i <;> simp

/-- The character is symmetric in its two arguments: `χ_u(v) = χ_v(u)`. -/
theorem chi_comm {n : ℕ} (u v : Reg n) : chi u v = chi v u := by
  unfold chi
  apply Finset.prod_congr rfl
  intro i _
  simp only [Bool.and_comm]

/-- `χ_u(0) = 1`. -/
@[simp] theorem chi_zero_right {n : ℕ} (u : Reg n) : chi u (ZeroStr n) = 1 := by
  unfold chi ZeroStr
  simp

/-- `χ_0(v) = 1`. -/
@[simp] theorem chi_zero_left {n : ℕ} (v : Reg n) : chi (ZeroStr n) v = 1 := by
  unfold chi ZeroStr
  simp

/-- Closed form of the character: `χ_u(x) = -1` when the parity is odd and `1`
otherwise. This is the bridge between the product definition and the paper's
`1_{⟨v,u⟩=1}` indicator. -/
theorem chi_eq_ite {n : ℕ} (u x : Reg n) :
    chi u x = if parityDot u x = true then (-1 : ℝ) else 1 := by
  unfold chi parityDot
  rw [← Finset.prod_filter (s := Finset.univ) (p := fun i => u i && x i)
        (f := fun _ => (-1 : ℝ))]
  rw [Finset.prod_const]
  have hmod : (Finset.univ.filter fun i => u i && x i).card % 2 < 2 :=
    Nat.mod_lt _ (by norm_num)
  rw [neg_one_pow_eq_pow_mod_two]
  interval_cases h : (Finset.univ.filter fun i => u i && x i).card % 2 <;> simp [h]

/-- Every character value is `1` or `-1`. -/
theorem chi_val {n : ℕ} (u x : Reg n) : chi u x = 1 ∨ chi u x = -1 := by
  rw [chi_eq_ite]
  by_cases h : parityDot u x = true <;> simp [h]

/-- The character is `-1` exactly on the hyperplane `⟨u,x⟩ = 1`. -/
theorem chi_eq_neg_iff {n : ℕ} (u x : Reg n) :
    chi u x = -1 ↔ parityDot u x = true := by
  rw [chi_eq_ite]
  constructor
  · intro h
    by_contra hc
    rw [if_neg hc] at h
    norm_num at h
  · intro h
    rw [if_pos h]

/-- The paper's indicator `1_{⟨v,u⟩=1}` written through the character:
`1_{⟨v,u⟩=1} = (1 - χ_v(u))/2`. -/
theorem indicator_eq_half {n : ℕ} (v u : Reg n) :
    (if parityDot v u = true then (1 : ℝ) else 0) = (1 - chi v u) / 2 := by
  rw [chi_eq_ite]
  by_cases h : parityDot v u = true <;> simp [h]

/-! ### Character orthogonality -/

/-- **Orthogonality of characters:** `Σ_x χ_u(x) = 2^n` if `u = 0` and `0`
otherwise (the real form of the standard `Z_2^n` orthogonality relation). -/
theorem sum_chi {n : ℕ} (z : Reg n) :
    (∑ u : Reg n, chi u z) = if z = ZeroStr n then (2 : ℝ) ^ n else 0 := by
  have hprod : (∑ u : Reg n, chi u z)
      = ∏ i : Fin n, ∑ b : Bool, (if b && z i then (-1 : ℝ) else 1) := by
    unfold chi
    rw [← Fintype.prod_sum
      (f := fun (i : Fin n) (b : Bool) => if b && z i then (-1 : ℝ) else 1)]
  rw [hprod]
  have hinner : ∀ i : Fin n,
      (∑ b : Bool, (if b && z i then (-1 : ℝ) else 1)) = if z i then 0 else 2 := by
    intro i
    rcases hzi : z i <;> simp [hzi, Fintype.sum_bool]
  simp_rw [hinner]
  by_cases hz : z = ZeroStr n
  · subst hz
    simp [ZeroStr, Finset.prod_const]
  · rw [if_neg hz]
    have hne : ∃ i, z i = true := by
      by_contra h
      apply hz
      funext j
      have hj : z j ≠ true := fun ht => h ⟨j, ht⟩
      cases hzj : z j
      · rfl
      · exact absurd hzj hj
    obtain ⟨i, hi⟩ := hne
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- **Two-character orthogonality:** `Σ_u χ_u(x) χ_u(y) = 2^n` iff `x = y`. -/
theorem sum_chi_mul {n : ℕ} (x y : Reg n) :
    (∑ u : Reg n, chi u x * chi u y) = if x = y then (2 : ℝ) ^ n else 0 := by
  have h : ∀ u : Reg n, chi u x * chi u y = chi u (regXor x y) :=
    fun u => (chi_xor u x y).symm
  simp_rw [h]
  rw [sum_chi]
  by_cases hxy : x = y
  · subst hxy
    simp
  · rw [if_neg hxy, if_neg (fun h => hxy ((regXor_eq_zero_iff x y).mp h))]

/-- **Three-character orthogonality:** `Σ_u χ_v(u) χ_u(x) χ_u(y) = 2^n` iff
`v = x + y`. -/
theorem sum_chi_triple {n : ℕ} (v x y : Reg n) :
    (∑ u : Reg n, chi v u * (chi u x * chi u y))
      = if v = regXor x y then (2 : ℝ) ^ n else 0 := by
  have h : ∀ u : Reg n, chi v u * (chi u x * chi u y) = chi u v * chi u (regXor x y) := by
    intro u
    rw [chi_comm v u, chi_xor u x y]
  simp_rw [h]
  exact sum_chi_mul v (regXor x y)

/-! ### Auxiliary arithmetic for the uniform weight -/

/-- `(2⁻ⁿ)² · 2ⁿ = 2⁻ⁿ`. -/
theorem uniformWeight_sq_mul {n : ℕ} :
    uniformWeight n ^ 2 * (2 : ℝ) ^ n = uniformWeight n := by
  unfold uniformWeight
  have h2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  field_simp

/-- `2⁻ⁿ · 2ⁿ = 1`. -/
theorem uniformWeight_mul {n : ℕ} : uniformWeight n * (2 : ℝ) ^ n = 1 := by
  unfold uniformWeight
  have h2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  field_simp

/-- `Σ_x 1 = 2ⁿ` over the cube. -/
theorem sum_one {n : ℕ} : (∑ _x : Reg n, (1 : ℝ)) = (2 : ℝ) ^ n := by
  rw [Finset.sum_const, Finset.card_univ]
  have hcard : Fintype.card (Reg n) = 2 ^ n := by
    simp [Reg, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [hcard, nsmul_eq_mul, mul_one, Nat.cast_pow]
  norm_num

/-! ### The shifted correlation (Appendix A) -/

/-- **Shifted correlation.** Expanding both Fourier coefficients and applying
character orthogonality three times gives
`Σ_u χ_v(u) F̂(u)² = 2^{-n} Σ_x F(x) F(x+v)` (the `v`-Fourier coefficient of
the autocorrelation, cf. Appendix A of arXiv:1103.3017v1). -/
theorem sum_chi_fourier_mul {n : ℕ} (F : Reg n → ℝ) (v : Reg n) :
    (∑ u : Reg n, chi v u * (fourierCoef F u) ^ 2)
      = uniformWeight n * ∑ x : Reg n, F x * F (regXor x v) := by
  classical
  -- Step 1: expand `F̂(u)² = w²·(Σ_x F x χ_u x)·(Σ_y F y χ_u y)` and push sums.
  have h1 : (∑ u : Reg n, chi v u * (fourierCoef F u) ^ 2)
      = uniformWeight n ^ 2 * ∑ u : Reg n, ∑ x : Reg n, ∑ y : Reg n,
          chi v u * ((F x * chi u x) * (F y * chi u y)) := by
    have hp : ∀ u : Reg n, chi v u * (fourierCoef F u) ^ 2
        = uniformWeight n ^ 2 *
            (chi v u * ((∑ x : Reg n, F x * chi u x)
              * (∑ y : Reg n, F y * chi u y))) := by
      intro u
      unfold fourierCoef
      ring
    simp_rw [hp]
    rw [← Finset.mul_sum]
    congr 1
    simp_rw [Finset.sum_mul_sum]
    simp_rw [Finset.mul_sum]
  rw [h1]
  -- Step 2: evaluate the inner sums with the orthogonality relations.
  have h2 : (∑ u : Reg n, ∑ x : Reg n, ∑ y : Reg n,
        chi v u * ((F x * chi u x) * (F y * chi u y)))
      = (2 : ℝ) ^ n * ∑ x : Reg n, F x * F (regXor x v) := by
    rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    have hinner : ∀ y : Reg n,
        (∑ u : Reg n, chi v u * ((F x * chi u x) * (F y * chi u y)))
          = (F x * F y) * (if v = regXor x y then (2 : ℝ) ^ n else 0) := by
      intro y
      have hfac : ∀ u : Reg n, chi v u * ((F x * chi u x) * (F y * chi u y))
          = (F x * F y) * (chi v u * (chi u x * chi u y)) := by
        intro u; ring
      simp_rw [hfac]
      rw [← Finset.mul_sum, sum_chi_triple]
    simp_rw [hinner]
    have hv : ∀ y : Reg n, (v = regXor x y) ↔ (y = regXor x v) := by
      intro y
      constructor
      · intro h
        rw [h]
        exact (regXor_left_cancel x y).symm
      · intro h
        rw [h]
        exact (regXor_left_cancel x v).symm
    have hpt : ∀ y : Reg n,
        (F x * F y) * (if v = regXor x y then (2 : ℝ) ^ n else 0)
          = if y = regXor x v then (F x * F y) * (2 : ℝ) ^ n else 0 := by
      intro y
      by_cases h : y = regXor x v
      · have hv' : v = regXor x y := (hv y).mpr h
        rw [if_pos hv', if_pos h]
      · have h' : ¬ (v = regXor x y) := fun hv' => h ((hv y).mp hv')
        rw [if_neg h', if_neg h]
        ring
    simp_rw [hpt]
    rw [Finset.sum_ite_eq']
    simp
    ring
  rw [h2]
  -- Step 3: `w²·2ⁿ = w`.
  rw [← mul_assoc, uniformWeight_sq_mul]

/-! ### Parseval -/

/-- **Parseval.** For a `{+1,-1}`-valued `F`, `Σ_u F̂(u)² = 1`
(Appendix A, applied with the trivial shift; equivalently Parseval plus
`Σ_x F(x)² = 2^n`). -/
theorem sum_sq_fourier {n : ℕ} (F : Reg n → ℝ)
    (hF : ∀ x : Reg n, F x * F x = 1) :
    (∑ u : Reg n, (fourierCoef F u) ^ 2) = 1 := by
  have hzero : (∑ u : Reg n, (fourierCoef F u) ^ 2)
      = ∑ u : Reg n, chi (ZeroStr n) u * (fourierCoef F u) ^ 2 := by
    apply Finset.sum_congr rfl
    intro u _
    simp
  rw [hzero, sum_chi_fourier_mul]
  have hsq : (∑ x : Reg n, F x * F (regXor x (ZeroStr n))) = (2 : ℝ) ^ n := by
    simp only [regXor_zero_right]
    simp_rw [hF]
    exact sum_one
  rw [hsq, uniformWeight_mul]

/-! ### Influence in terms of the autocorrelation -/

/-- Since `F` is `{+1,-1}`-valued, the influence probability is the algebraic
expression `(1 - F(x)F(x+v))/2`; summing gives
`γ_{f,v} = (1/2)(1 - 2^{-n} Σ_x F(x)F(x+v))` (Definition 2). -/
theorem influence_eq_half {n : ℕ} (F : Reg n → ℝ)
    (hF : ∀ x : Reg n, F x * F x = 1) (v : Reg n) :
    influence F v
      = (1 / 2) * (1 - uniformWeight n * ∑ x : Reg n, F x * F (regXor x v)) := by
  have hstep : ∀ x : Reg n,
      (if F x = F (regXor x v) then (0 : ℝ) else 1)
        = (1 - F x * F (regXor x v)) / 2 := by
    intro x
    rcases mul_self_eq_one_iff.mp (hF x) with hx | hx <;>
      rcases mul_self_eq_one_iff.mp (hF (regXor x v)) with hy | hy <;>
      simp [hx, hy] <;> norm_num
  have h1 : influence F v
      = uniformWeight n * ∑ x : Reg n, (1 - F x * F (regXor x v)) / 2 := by
    unfold influence
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    exact hstep x
  have hsplit : (∑ x : Reg n, (1 - F x * F (regXor x v)) / 2)
      = ((2 : ℝ) ^ n - ∑ x : Reg n, F x * F (regXor x v)) / 2 := by
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_sub_distrib, sum_one]
  rw [h1, hsplit]
  unfold uniformWeight
  have h2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  field_simp
  try ring

/-! ### Lemma 1 -/

/-- **Lemma 1 of arXiv:1103.3017v1** (p.2, Appendix A pp.6–7).
For a `{+1,-1}`-valued `F`, the influence of the shift `v` equals the Fourier
mass on the hyperplane `⟨v,u⟩ = 1`:
`γ_{f,v} = Σ_{u : ⟨v,u⟩=1} F̂(u)²`. -/
theorem source_lemma1_influence {n : ℕ} (F : Reg n → ℝ)
    (hF : ∀ x : Reg n, F x * F x = 1) (v : Reg n) :
    influence F v
      = ∑ u ∈ Finset.univ.filter (fun u => parityDot v u = true),
          (fourierCoef F u) ^ 2 := by
  classical
  -- The indicator rewrites the filtered sum as `(1/2)(Σ F̂² - Σ χ_v F̂²)`.
  have hindicator : (∑ u ∈ Finset.univ.filter (fun u => parityDot v u = true),
        (fourierCoef F u) ^ 2)
      = (1 / 2) * ((∑ u : Reg n, (fourierCoef F u) ^ 2)
          - ∑ u : Reg n, chi v u * (fourierCoef F u) ^ 2) := by
    rw [Finset.sum_filter]
    have hpt : ∀ u : Reg n,
        (if parityDot v u = true then (fourierCoef F u) ^ 2 else 0)
          = (1 / 2) * (fourierCoef F u) ^ 2
            - (1 / 2) * (chi v u * (fourierCoef F u) ^ 2) := by
      intro u
      rw [chi_eq_ite]
      by_cases h : parityDot v u = true
      · simp only [if_pos h]
        ring
      · simp only [if_neg h]
        ring
    simp_rw [hpt]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [← mul_sub]
  rw [hindicator, sum_sq_fourier F hF, sum_chi_fourier_mul F v,
    influence_eq_half F hF v]

end Qatlib.Papers.BoolHidShift11.ShiftSample.InfluenceFourier
