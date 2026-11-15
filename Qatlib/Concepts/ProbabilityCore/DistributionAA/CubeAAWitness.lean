/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeDegenerateVariance

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- Shows that the variance-to-degree ratio lies between zero and one under the stated variance
bounds. -/
theorem cube_aa_ratio_range {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1/4) (d : ℕ) :
    v/(d : ℝ) ∈ Set.Icc 0 1 := by
  constructor
  · positivity
  · by_cases hd : d=0
    · simp [hd]
    · have hdr : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_ne_zero hd
      exact (div_le_self hv.le hdr).trans (by linarith only [hv1])

/-- Extracts a positive normalized polynomial witness from `AAHolds`, with values between zero
and one in the prescribed range. -/
theorem cube_aa_normalized_witness {Λ : CubeFamily} (h : AAHolds Λ) :
    ∃ c : ℝ, ∃ C : ℕ, 0 < c ∧ c ≤ 1 ∧ 0 < C ∧
      AAWith Λ (fun v d => c*(v/(d : ℝ))^C) ∧
      ∀ v, 0 < v → v ≤ 1/4 → ∀ d : ℕ, c*(v/(d : ℝ))^C ∈ Set.Icc 0 1 := by
  obtain ⟨c,C,hc,hAA⟩ := h
  let c' := min c 1
  let C' := max C 1
  have hc' : 0 < c' := lt_min hc (by norm_num)
  have hc1 : c' ≤ 1 := min_le_right _ _
  have hr (v) (hv : 0 < v) (hv1 : v ≤ 1/4) (d : ℕ) : c'*(v/(d : ℝ))^C' ≤ c*(v/(d : ℝ))^C := by
    have hx := cube_aa_ratio_range hv hv1 d
    have hp := pow_le_pow_of_le_one hx.1 hx.2 (le_max_left C 1)
    exact (mul_le_mul_of_nonneg_left hp hc'.le).trans
      (mul_le_mul_of_nonneg_right (min_le_left c 1) (pow_nonneg hx.1 C))
  refine ⟨c',C',hc',hc1,by dsimp [C']; omega,?_,?_⟩
  · intro n d v hv hv1 f hb hd hvar
    obtain ⟨i,hi⟩ := hAA n d v hv hv1 f hb hd hvar
    exact ⟨i,(hr v hv hv1 d).trans hi⟩
  · intro v hv hv1 d
    have hx := cube_aa_ratio_range hv hv1 d
    constructor
    · exact mul_nonneg hc'.le (pow_nonneg hx.1 C')
    · exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hx.1 hx.2) hc'.le).trans (by simpa using hc1)

/-- Gives an explicit polynomial lower bound on the slice transfer of a polynomial AA witness. -/
theorem cube_slice_polynomial_witness {c v : ℝ} (hc : 0 < c) (hv : 0 < v) (hv1 : v ≤ 1/4)
    (C d : ℕ) (hd : 0 < d) :
    (min 1 (c^4/(2 : ℝ)^(4*C))/(10 : ℝ)^9)*(v/(d : ℝ))^(4*C+8) ≤
      sliceTransferS (fun v d => c*(v/(d : ℝ))^C) v d := by
  let x := v/(d : ℝ)
  let K := c^4/(2 : ℝ)^(4*C)
  let θ := min 1 K
  have hK : 0 < K := by dsimp [K]; positivity
  have hθ : 0 ≤ θ := le_min (by norm_num) hK.le
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθK : θ ≤ K := min_le_right _ _
  have hx := cube_aa_ratio_range hv hv1 d
  have hxpow : 0 ≤ x^(4*C) := pow_nonneg hx.1 _
  have hxpow1 : x^(4*C) ≤ 1 := pow_le_one₀ hx.1 hx.2
  have hvle1 : v ≤ 1 := by linarith only [hv1]
  have hv8le5 : v^8 ≤ v^5 := pow_le_pow_of_le_one hv.le hvle1 (by decide : 5 ≤ 8)
  have hv8le : v^8 ≤ v := by
    simpa only [pow_one] using pow_le_pow_of_le_one hv.le hvle1 (by decide : 1 ≤ 8)
  have hθx : θ*x^(4*C) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hxpow1 hθ).trans (by simpa using hθ1)
  have h1 : θ*v^8*x^(4*C) ≤ v^5 := by
    have h := mul_le_mul_of_nonneg_left hθx (pow_nonneg hv.le 8)
    nlinarith only [h,hv8le5]
  have h2 : θ*v^8*x^(4*C) ≤ v*K*x^(4*C) := by
    have h := mul_le_mul hθK hv8le (pow_nonneg hv.le 8) hK.le
    simpa only [mul_comm K v] using mul_le_mul_of_nonneg_right h hxpow
  have hs : (c*((v/2)/(d : ℝ))^C)^4=K*x^(4*C) := by
    have he : (v/2)/(d : ℝ)=x/2 := by dsimp [x]; ring
    rw [he,mul_pow,← pow_mul,div_pow]
    dsimp [K]
    rw [Nat.mul_comm C 4]
    ring
  have hdn : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hxd : x*(d : ℝ)=v := by dsimp [x]; exact div_mul_cancel₀ v hdn
  have hleft : (θ/(10 : ℝ)^9)*x^(4*C+8)*((10 : ℝ)^9*(d : ℝ)^8)=θ*v^8*x^(4*C) := by
    rw [pow_add]
    calc
      _ = θ*x^(4*C)*(x*(d : ℝ))^8 := by rw [mul_pow]; ring
      _ = _ := by rw [hxd]; ring
  unfold sliceTransferS
  change (θ/(10 : ℝ)^9)*x^(4*C+8) ≤ min (v^5) (v*(c*((v/2)/(d : ℝ))^C)^4)/((10 : ℝ)^9*(d : ℝ)^8)
  rw [hs]
  apply (le_div_iff₀ (show 0 < (10 : ℝ)^9*(d : ℝ)^8 by positivity)).2
  rw [hleft]
  exact le_min h1 (by simpa only [mul_assoc] using h2)

/-- Transfers `AAHolds` to a weighted cube family using the assumed slice transfer principle. -/
theorem cube_aa_holds_from_slice_transfer (Λ Γ : CubeFamily) (hΓ : ∀ n, CubeWeight n (Γ n))
    (htransfer : ∀ S : ℝ → ℕ → ℝ,
      (∀ v, 0 < v → v ≤ 1/4 → ∀ d, S v d ∈ Set.Icc 0 1) →
      AAWith Λ S → AAWith Γ (sliceTransferS S)) (hAA : AAHolds Λ) : AAHolds Γ := by
  obtain ⟨c,C,hc,_hc1,_hC,hAA,hS⟩ := cube_aa_normalized_witness hAA
  have ht := htransfer (fun v d => c*(v/(d : ℝ))^C) hS hAA
  refine ⟨min 1 (c^4/(2 : ℝ)^(4*C))/(10 : ℝ)^9,4*C+8,by positivity,?_⟩
  intro n d v hv hv1 f hb hd hvar
  have hd0 : 0 < d := by
    by_contra he
    have he0 : d=0 := by omega
    subst d
    rw [cube_degree_zero_variance (hΓ n) hd] at hvar
    linarith only [hv,hvar]
  obtain ⟨i,hi⟩ := ht n d v hv hv1 f hb hd hvar
  exact ⟨i,(cube_slice_polynomial_witness hc hv hv1 C d hd0).trans hi⟩

end Qatlib.Concepts.ProbabilityCore.DistributionAA
