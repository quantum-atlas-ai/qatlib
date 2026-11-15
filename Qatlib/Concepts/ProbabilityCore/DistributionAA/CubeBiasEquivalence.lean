/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeDegenerateVariance

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open Filter

def cubeBiasSizeConstant (a : ℝ) : ℝ := 4/(a*Real.log 2)+1

/-- Shows that `cubeBiasSizeConstant` is positive for a positive bias parameter. -/
theorem cube_bias_size_constant_pos {a : ℝ} (ha : 0 < a) : 0 < cubeBiasSizeConstant a := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  dsimp [cubeBiasSizeConstant]
  positivity

/-- Bounds the bias gadget size by the explicit size constant times `D` divided by the
variance-to-degree ratio. -/
theorem cube_bias_gadget_size_upper {a v : ℝ} (ha : 0 < a) (hv : 0 < v) (hv1 : v ≤ 1/4)
    {d D : ℕ} (hd : 0 < d) (hD : 0 < D) :
    (biasGadgetSize a D v d : ℝ) ≤ cubeBiasSizeConstant a*(D : ℝ)/(v/(d : ℝ)) := by
  let z := (d : ℝ)/v
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hz : 1 ≤ z := by
    apply (le_div_iff₀ hv).2
    linarith only [hdr,hv1]
  have hz0 : 0 < z := lt_of_lt_of_le (by norm_num) hz
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogz : 0 ≤ Real.logb 2 z := Real.logb_nonneg (by norm_num) hz
  have hL : Real.logb 2 z ≤ z/Real.log 2 := by
    unfold Real.logb
    apply (div_le_div_iff_of_pos_right hlog).2
    exact (Real.log_le_sub_one_of_pos hz0).trans (by linarith)
  have hb : 0 ≤ (4*(D : ℝ)/a)*Real.logb 2 z := by positivity
  have hceil := (Nat.ceil_lt_add_one hb).le
  have hmul := mul_le_mul_of_nonneg_left hL (show 0 ≤ 4*(D : ℝ)/a by positivity)
  have hDz : 1 ≤ (D : ℝ)*z := by nlinarith only [hDr,hz]
  have he : cubeBiasSizeConstant a*(D : ℝ)/(v/(d : ℝ)) =
      (4*(D : ℝ)/a)*(z/Real.log 2)+(D : ℝ)*z := by
    dsimp [cubeBiasSizeConstant,z]
    field_simp
  rw [he]
  change (Nat.ceil ((4*(D : ℝ)/a)*Real.logb 2 z) : ℝ) ≤ _
  linarith only [hceil,hmul,hDz]

/-- Chooses a sufficiently large exponent so that the geometric error is dominated by the stated
polynomial expression. -/
theorem cube_bias_absorb_error {c K : ℝ} (hc : 0 < c) (hK : 0 < K) (C : ℕ) :
    ∃ D : ℕ, 0 < D ∧ 2*C ≤ D ∧
      (1/4 : ℝ)^(D-2*C) ≤ c/(2*(2*K)^C*(D : ℝ)^C) := by
  let η := c*(1/4 : ℝ)^(2*C)/(2*(2*K)^C)
  have hη : 0 < η := by dsimp [η]; positivity
  have ht := tendsto_pow_const_mul_const_pow_of_lt_one C
    (by norm_num : (0 : ℝ) ≤ 1/4) (by norm_num : (1/4 : ℝ) < 1)
  have hev := ht.eventually_lt_const hη
  obtain ⟨D,hsmall,hD⟩ := (hev.and (eventually_ge_atTop (2*C+1))).exists
  have hD0 : 0 < D := by omega
  have hDC : 2*C ≤ D := by omega
  have hp0 : 0 < (1/4 : ℝ)^(2*C) := by positivity
  have hA0 : 0 < 2*(2*K)^C := by positivity
  have hDp0 : 0 < (D : ℝ)^C := by positivity
  refine ⟨D,hD0,hDC,?_⟩
  apply (le_div_iff₀ (mul_pos hA0 hDp0)).2
  have hp : (1/4 : ℝ)^D=(1/4 : ℝ)^(2*C)*(1/4 : ℝ)^(D-2*C) := by
    rw [← pow_add,Nat.add_sub_of_le hDC]
  rw [hp] at hsmall
  have hs := (mul_lt_mul_of_pos_right hsmall hA0).le
  have hηA : η*(2*(2*K)^C)=c*(1/4 : ℝ)^(2*C) := div_mul_cancel₀ _ hA0.ne'
  rw [hηA] at hs
  apply (mul_le_mul_iff_left₀ hp0).1
  nlinarith only [hs]

/-- Gives an explicit polynomial lower bound on the bias transfer of a polynomial AA witness. -/
theorem cube_bias_polynomial_lower {a c v : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hv : 0 < v) (hv1 : v ≤ 1/4) (C D d : ℕ) (hD : 0 < D) (hd : 0 < d)
    (hDC : 2*C ≤ D)
    (hsmall : (1/4 : ℝ)^(D-2*C) ≤ c/(2*(2*cubeBiasSizeConstant a)^C*(D : ℝ)^C)) :
    (c/(2*(2*cubeBiasSizeConstant a)^C*(D : ℝ)^C))*(v/(d : ℝ))^(2*C) ≤
      biasTransferS (fun v d => c*(v/(d : ℝ))^C) a D v d := by
  let K := cubeBiasSizeConstant a
  let m := biasGadgetSize a D v d
  let x := v/(d : ℝ)
  let A := 2*K*(D : ℝ)
  have hK : 0 < K := cube_bias_size_constant_pos ha
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast hD
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hx4 : x ≤ 1/4 := (div_le_self hv.le (by exact_mod_cast hd)).trans hv1
  have hA : 0 < A := by dsimp [A]; positivity
  have hm0 : 0 < m := by
    have hz : 1 < (d : ℝ)/v := (lt_div_iff₀ hv).2 (by
      have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith only [hv1,hdr])
    apply Nat.ceil_pos.2
    exact mul_pos (by positivity) (Real.logb_pos (by norm_num) hz)
  have hmp : 0 < (m : ℝ) := by exact_mod_cast hm0
  have hmu := cube_bias_gadget_size_upper ha hv hv1 hd hD
  have hmx : (m : ℝ)*x ≤ K*(D : ℝ) := (le_div_iff₀ hx0).1 hmu
  have hratio : x^2/A ≤ (v/2)/((d*m : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    have he : (v/2)/((d : ℝ)*(m : ℝ))=x/(2*(m : ℝ)) := by dsimp [x]; field_simp
    rw [he]
    apply (div_le_div_iff₀ hA (by positivity : 0 < 2*(m : ℝ))).2
    have hh := mul_le_mul_of_nonneg_left hmx hx0.le
    dsimp [A]
    nlinarith only [hh]
  have hterm :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity : 0 ≤ x^2/A) hratio C) hc.le
  have hpow : x^D=x^(2*C)*x^(D-2*C) := by rw [← pow_add,Nat.add_sub_of_le hDC]
  have hxp := pow_le_pow_left₀ hx0.le hx4 (D-2*C)
  have herr : x^D ≤ (c/(2*(2*K)^C*(D : ℝ)^C))*x^(2*C) := by
    rw [hpow]
    have hh := mul_le_mul_of_nonneg_left (hxp.trans hsmall) (pow_nonneg hx0.le (2*C))
    simpa only [mul_comm] using hh
  have hcoef : c*(x^2/A)^C = 2*(c/(2*(2*K)^C*(D : ℝ)^C))*x^(2*C) := by
    rw [div_pow,← pow_mul]
    dsimp [A]
    rw [mul_pow]
    field_simp
  rw [hcoef] at hterm
  change c/(2*(2*K)^C*(D : ℝ)^C)*x^(2*C) ≤ c*((v/2)/((d*m : ℕ) : ℝ))^C-x^D
  linarith only [hterm,herr]

/-- Transfers `AAHolds` to a weighted cube family using the assumed bias transfer principle. -/
theorem cube_aa_holds_from_bias_transfer (Λ Γ : CubeFamily) (hΓ : ∀ n, CubeWeight n (Γ n))
    (a : ℝ) (ha : 0 < a)
    (htransfer : ∀ S : ℝ → ℕ → ℝ, AAWith Λ S → ∀ D, 0 < D → AAWith Γ (biasTransferS S a D))
    (hAA : AAHolds Λ) : AAHolds Γ := by
  obtain ⟨c,C,hc,hAA⟩ := hAA
  have hK := cube_bias_size_constant_pos ha
  obtain ⟨D,hD,hDC,hsmall⟩ := cube_bias_absorb_error hc hK C
  have ht := htransfer (fun v d => c*(v/(d : ℝ))^C) hAA D hD
  refine ⟨c/(2*(2*cubeBiasSizeConstant a)^C*(D : ℝ)^C),2*C,by positivity,?_⟩
  intro n d v hv hv1 f hb hd hvar
  have hd0 : 0 < d := by
    by_contra he
    have he0 : d=0 := by omega
    subst d
    rw [cube_degree_zero_variance (hΓ n) hd] at hvar
    linarith only [hv,hvar]
  obtain ⟨i,hi⟩ := ht n d v hv hv1 f hb hd hvar
  exact ⟨i,(cube_bias_polynomial_lower ha hc hv hv1 C D d hD hd0 hDC hsmall).trans hi⟩

end Qatlib.Concepts.ProbabilityCore.DistributionAA
