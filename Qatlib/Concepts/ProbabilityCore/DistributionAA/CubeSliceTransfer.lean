/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeDegenerateVariance
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeProductSliceMoments
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeSlicePoincare

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- Bounds the defined slice transfer threshold by half of `s` and, under the stated
small-dimension condition, by `v` divided by twice `N` squared. -/
theorem cube_slice_transfer_numeric {v s t N d : ℝ} (hv : 0 < v) (hv1 : v ≤ 1/4)
    (hs : s ∈ Set.Icc 0 1) (ht : t=min v s) (hN : 1 ≤ N) (hd : 1 ≤ d) :
    let T := min (v^5) (v*s^4)/(10^9*d^8)
    T ≤ s/2 ∧ (t*Real.sqrt N < 96*d^2 → 2*N^2*T ≤ v) := by
  have ht0 : 0 ≤ t := by rw [ht]; exact le_min hv.le hs.1
  have hd0 : 0 < d := by linarith
  have hE0 : 0 < (10 : ℝ)^9*d^8 := by positivity
  have hpow : s^4 ≤ s := by
    have h2 : s^2 ≤ s := by nlinarith [hs.1,hs.2]
    have h4 : (s^2)^2 ≤ s^2 := by nlinarith [sq_nonneg s,show s^2 ≤ 1 by nlinarith [h2,hs.2]]
    nlinarith only [h2,h4]
  have hE1 : (1 : ℝ) ≤ (10 : ℝ)^9*d^8 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hd 8
    norm_num at h ⊢
    linarith only [h]
  have hnum : min (v^5) (v*s^4)=v*t^4 := by
    rw [ht]
    by_cases hvs : v ≤ s
    · rw [min_eq_left hvs,min_eq_left]
      · ring
      · have hh := pow_le_pow_left₀ hv.le hvs 4
        nlinarith only [mul_le_mul_of_nonneg_left hh hv.le]
    · have hsv : s ≤ v := (lt_of_not_ge hvs).le
      rw [min_eq_right hsv,min_eq_right]
      have hh := pow_le_pow_left₀ hs.1 hsv 4
      nlinarith only [mul_le_mul_of_nonneg_left hh hv.le]
  (try dsimp only)
  constructor
  · apply (div_le_iff₀ hE0).2
    have hn := min_le_right (v^5) (v*s^4)
    have hp := mul_le_mul_of_nonneg_left hpow hv.le
    have he := mul_le_mul_of_nonneg_left hE1 (show 0 ≤ s/2 by exact div_nonneg hs.1 (by norm_num))
    nlinarith only [hn,hp,he,hs.1,hv1]
  · intro hsmall
    rw [hnum]
    have hsq : N*t^2 < 96^2*d^4 := by
      have he := Real.sq_sqrt (show 0 ≤ N by linarith)
      have hmul := mul_self_lt_mul_self (show 0 ≤ t*Real.sqrt N by positivity) hsmall
      nlinarith only [hmul,he]
    have hsqsq : N^2*t^4 < (96 : ℝ)^4*d^8 := by
      have hh := mul_self_lt_mul_self (show 0 ≤ N*t^2 by positivity) hsq
      nlinarith only [hh]
    have hd8 := pow_nonneg hd0.le 8
    have hslack : 2*N^2*t^4 ≤ (10 : ℝ)^9*d^8 := by nlinarith only [hsqsq,hd8]
    have he : 2*N^2*(v*t^4/((10 : ℝ)^9*d^8)) = v*(2*N^2*t^4)/((10 : ℝ)^9*d^8) := by ring
    rw [he]
    exact (div_le_iff₀ hE0).2 (by nlinarith only [mul_le_mul_of_nonneg_left hslack hv.le])

/-- Transfers an AA witness between cube families using variance and influence closeness and the
stated variance-influence bound. -/
theorem cube_aa_transfer_from_moments (Λ Γ : CubeFamily)
    (hΓ : ∀ n, CubeWeight n (Γ n))
    (hgap : ∀ n d, ∀ f : (Fin n → Bool) → ℝ,
      (∀ x, f x ∈ Set.Icc 0 1) → CubeDegreeLE d f →
      |cubeVar n (Λ n) f-cubeVar n (Γ n) f| ≤ 48*(d : ℝ)^2/Real.sqrt (n : ℝ) ∧
      ∀ i, |cubeInf n (Λ n) f i-cubeInf n (Γ n) f i| ≤ 48*(d : ℝ)^2/Real.sqrt (n : ℝ))
    (hlarge : ∀ n, 0 < n → ∀ f : (Fin n → Bool) → ℝ,
      ∃ i, cubeVar n (Γ n) f ≤ 2*(n : ℝ)^2*cubeInf n (Γ n) f i)
    (S : ℝ → ℕ → ℝ) (hS : ∀ v, 0 < v → v ≤ 1/4 → ∀ d, S v d ∈ Set.Icc 0 1)
    (hAA : AAWith Λ S) : AAWith Γ (sliceTransferS S) := by
  intro n d v hv hv1 f hb hd hvar
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n=0 := by omega
    subst n
    rw [cube_zero_dimension_variance (hΓ 0) f] at hvar
    linarith only [hv,hvar]
  have hd0 : 0 < d := by
    by_contra hd0
    have he : d=0 := by omega
    subst d
    rw [cube_degree_zero_variance (hΓ n) hd] at hvar
    linarith only [hv,hvar]
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hv2 : 0 < v/2 := by linarith
  have hv21 : v/2 ≤ 1/4 := by linarith
  let s := S (v/2) d
  let t := min v s
  have hs : s ∈ Set.Icc 0 1 := hS (v/2) hv2 hv21 d
  have ht0 : 0 ≤ t := le_min hv.le hs.1
  have htV : t ≤ v := min_le_left _ _
  have htS : t ≤ s := min_le_right _ _
  obtain ⟨hTs,hsmall⟩ := cube_slice_transfer_numeric hv hv1 hs (show t=min v s by rfl) hnr hdr
  change sliceTransferS S v d ≤ s/2 at hTs
  change t*Real.sqrt (n : ℝ) < 96*(d : ℝ)^2 → 2*(n : ℝ)^2*sliceTransferS S v d ≤ v at hsmall
  by_cases hdim : t*Real.sqrt (n : ℝ) < 96*(d : ℝ)^2
  · obtain ⟨i,hi⟩ := hlarge n hn f
    refine ⟨i, ?_⟩
    have hc : 0 < 2*(n : ℝ)^2 := by positivity
    have ht := hsmall hdim
    exact (mul_le_mul_iff_right₀ hc).1 (ht.trans (hvar.trans hi))
  · have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hδ : 48*(d : ℝ)^2/Real.sqrt (n : ℝ) ≤ t/2 := by
      apply (div_le_iff₀ hsqrt).2
      have he : 96*(d : ℝ)^2 ≤ t*Real.sqrt (n : ℝ) := le_of_not_gt hdim
      linarith only [he]
    have hg := hgap n d f hb hd
    have hvΛ : v/2 ≤ cubeVar n (Λ n) f := by
      have he := (abs_le.1 hg.1).1
      linarith only [he,hδ,htV,hvar]
    obtain ⟨i,hi⟩ := hAA n d (v/2) hv2 hv21 f hb hd hvΛ
    have he := (abs_le.1 (hg.2 i)).2
    refine ⟨i,hTs.trans ?_⟩
    change s ≤ cubeInf n (Λ n) f i at hi
    linarith only [he,hi,hδ,htS]

end Qatlib.Concepts.ProbabilityCore.DistributionAA
