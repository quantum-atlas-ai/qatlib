/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellDenseTail
import Qatlib.Concepts.SpinorSampling.Matching.MatchedPlanArithmetic

set_option backward.isDefEq.respectTransparency false

/-!
# Retained Bell Plan Arithmetic

Retained Bell Plan Arithmetic constructions and identities for Spinor Sampling.
-/

open Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open scoped BigOperators
open Matched

/-- Constructors for Bell Mode in the retained bell plan arithmetic model. -/
inductive BellMode where
  | identity | midpoint | sparse | pooled
  deriving DecidableEq, Repr

/-- Data and invariants for Bell Plan Q in the retained bell plan arithmetic model. -/
structure BellPlanQ where
  mode : BellMode
  records : ℕ
  blocks : ℕ
  copies : ℕ
  meanUpper : ℚ
  tolerance : ℚ
  failureProbability : ℚ
  deriving Repr

/-- Construction for bell Strength Q in the retained bell plan arithmetic model. -/
def bellStrengthQ (p ε δ : ℚ) : ℚ :=
  128*(p+ε)*(ceilLog2Q (4/δ) : ℚ)/ε^2

/-- Construction for bell Records Q in the retained bell plan arithmetic model. -/
def bellRecordsQ (M : ℕ) (p ε δ : ℚ) : ℕ :=
  ceilSqrtQ ((M : ℚ)*bellStrengthQ p ε δ)

/-- Construction for bell Blocks Q in the retained bell plan arithmetic model. -/
def bellBlocksQ (M : ℕ) (p ε δ : ℚ) : ℕ :=
  ceilNatQ (bellStrengthQ p ε δ/(M : ℚ))

/-- The branch order, constants and fields are the public Python schedule. -/
def bellPlanQ (side M : ℕ) (p ε δ : ℚ) : BellPlanQ :=
  if side≤2 then ⟨.identity,0,0,0,p,ε,δ⟩ else
    if p≤2*ε then ⟨.midpoint,0,0,0,p,ε,δ⟩ else
      let n := bellRecordsQ M p ε δ
      if n≤M then ⟨.sparse,n,1,2*n,p,ε,δ⟩ else
        let K := bellBlocksQ M p ε δ
        ⟨.pooled,M,K,2*M*K,p,ε,δ⟩

/-- Construction for checked Bell Plan Q in the retained bell plan arithmetic model. -/
def checkedBellPlanQ (side M : ℕ) (p ε δ : ℚ) : Option BellPlanQ :=
  if 0≤p ∧ p≤1/2 ∧ 0<ε ∧ 0<δ ∧ δ<1 then some (bellPlanQ side M p ε δ) else none

/-- Construction for dyadic Bell Plan Q in the retained bell plan arithmetic model. -/
def dyadicBellPlanQ (d r : ℕ) (p ε δ : ℚ) : Option BellPlanQ :=
  checkedBellPlanQ (2^r) ((2^r)^d) p ε δ

/-- Construction for bell Scheduled Copies in the retained bell plan arithmetic model. -/
def bellScheduledCopies (p : BellPlanQ) : ℕ :=
  match p.mode with
  | .identity | .midpoint => 0
  | .sparse | .pooled => 2*p.records*p.blocks

/-- Complete original `bell_plan_copy_account` guarantee for `RetainedBellPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem bell_plan_copy_account (side M : ℕ) (p ε δ : ℚ) :
    (bellPlanQ side M p ε δ).copies=bellScheduledCopies (bellPlanQ side M p ε δ) := by
  by_cases hside : side≤2
  · simp [bellPlanQ,hside,bellScheduledCopies]
  · by_cases hmid : p≤2*ε
    · simp [bellPlanQ,hside,hmid,bellScheduledCopies]
    · by_cases hn : bellRecordsQ M p ε δ≤M <;>
        simp [bellPlanQ,hside,hmid,hn,bellScheduledCopies]

noncomputable section

/-- Complete original `bell_log_pos` guarantee for `RetainedBellPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem bell_log_pos (δ : ℚ) (hδ : 0<δ) (hδ1 : δ<1) : 0<ceilLog2Q (4/δ) := by
  have hq : (1 : ℚ)<4/δ := (lt_div_iff₀ hδ).mpr (by linarith)
  by_contra h
  have hL : ceilLog2Q (4/δ)=0 := by omega
  have hp := ceil_log2_power (4/δ)
  rw [hL,pow_zero] at hp
  linarith

/-- Complete original `bell_exp_log_quarter` guarantee for `RetainedBellPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem bell_exp_log_quarter (δ : ℚ) (hδ : 0<δ) :
    Real.exp (-(ceilLog2Q (4/δ) : ℝ))≤(δ : ℝ)/4 := by
  have hδR : (0 : ℝ)<δ := Rat.cast_pos.mpr hδ
  have hlog : Real.log (4/(δ : ℝ))≤(ceilLog2Q (4/δ) : ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using ceil_log2_log_bound (4/δ) (by positivity)
  calc
    _ ≤ Real.exp (-Real.log (4/(δ : ℝ))) := Real.exp_le_exp.mpr (neg_le_neg hlog)
    _ = _ := by rw [Real.exp_neg,Real.exp_log (by positivity)]; field_simp

/-- Complete original `bell_nonzero_tolerance` guarantee for `RetainedBellPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem bell_nonzero_tolerance (p ε : ℚ) (hp : p≤1/2) (hε : 0<ε) (hmid : ¬p≤2*ε) :
    0<(ε : ℝ) ∧ (ε : ℝ)<1/4 ∧ (ε : ℝ)≤(p : ℝ)+(ε : ℝ) := by
  have hq : 2*ε<p := lt_of_not_ge hmid
  have hr : (2 : ℝ)*(ε : ℝ)<(p : ℝ) := by exact_mod_cast hq
  have hpR : (p : ℝ)≤1/2 := by
    have hcast : (p : ℝ)≤((1/2 : ℚ) : ℝ) := Rat.cast_le.mpr hp
    push_cast at hcast
    exact hcast
  have hεR : (0 : ℝ)<ε := Rat.cast_pos.mpr hε
  constructor
  · exact hεR
  · constructor <;> linarith

/-- Complete original `bell_strength_pos` guarantee for `RetainedBellPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem bell_strength_pos (p ε δ : ℚ) (hp : 0≤p) (hε : 0<ε)
    (hδ : 0<δ) (hδ1 : δ<1) : 0<bellStrengthQ p ε δ := by
  have hL := bell_log_pos δ hδ hδ1
  have hLQ : (0 : ℚ)<ceilLog2Q (4/δ) := by exact_mod_cast hL
  unfold bellStrengthQ
  positivity

/-- Complete original `bell_records_square_budget` guarantee for `RetainedBellPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem bell_records_square_budget (M : ℕ) (p ε δ : ℚ) (hp : 0≤p) (hε : 0<ε) :
    128*(M : ℝ)*((p : ℝ)+(ε : ℝ))*(ceilLog2Q (4/δ) : ℝ)≤
      (bellRecordsQ M p ε δ : ℝ)^2*(ε : ℝ)^2 := by
  have hq : (0 : ℚ)≤(M : ℚ)*bellStrengthQ p ε δ := by unfold bellStrengthQ; positivity
  have hs := ceil_sqrt_q_square _ hq
  have hsR : 128*(M : ℝ)*((p : ℝ)+(ε : ℝ))*(ceilLog2Q (4/δ) : ℝ)/(ε : ℝ)^2≤
      (bellRecordsQ M p ε δ : ℝ)^2 := by
    convert hs using 1 <;> try rfl
    simp only [bellStrengthQ,Rat.cast_mul,Rat.cast_div,Rat.cast_add,
      Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat]
    ring
  have hsq : (0 : ℝ)<(ε : ℝ)^2 := by
    have he : (0 : ℝ)<ε := Rat.cast_pos.mpr hε
    positivity
  exact (div_le_iff₀ hsq).mp hsR

/-- Complete original `bell_records_pos` guarantee for `RetainedBellPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem bell_records_pos (M : ℕ) (hM : 0<M) (p ε δ : ℚ) (hp : 0≤p) (hε : 0<ε)
    (hδ : 0<δ) (hδ1 : δ<1) : 0<bellRecordsQ M p ε δ := by
  have hs := ceil_sqrt_q_square ((M : ℚ)*bellStrengthQ p ε δ)
    (by have hpos := bell_strength_pos p ε δ hp hε hδ hδ1; positivity)
  have hq : (0 : ℝ)<(M : ℝ)*(bellStrengthQ p ε δ : ℝ) := by
    have hMR : (0 : ℝ)<M := by exact_mod_cast hM
    exact mul_pos hMR (Rat.cast_pos.mpr (bell_strength_pos p ε δ hp hε hδ hδ1))
  by_contra h
  have hz : bellRecordsQ M p ε δ=0 := by omega
  change _≤(bellRecordsQ M p ε δ : ℝ)^2 at hs
  rw [hz] at hs
  norm_num at hs
  linarith

/-- Complete original `bell_blocks_budget` guarantee for `RetainedBellPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem bell_blocks_budget (M : ℕ) (hM : 0<M) (p ε δ : ℚ) (hp : 0≤p) (hε : 0<ε) :
    128*((p : ℝ)+(ε : ℝ))*(ceilLog2Q (4/δ) : ℝ)≤
      (bellBlocksQ M p ε δ : ℝ)*(M : ℝ)*(ε : ℝ)^2 := by
  have hq : (0 : ℚ)≤bellStrengthQ p ε δ/(M : ℚ) := by unfold bellStrengthQ; positivity
  have hc := (ceil_nat_bounds _ hq).1
  have hratio : 128*((p : ℝ)+(ε : ℝ))*(ceilLog2Q (4/δ) : ℝ)/
      ((M : ℝ)*(ε : ℝ)^2)≤(bellBlocksQ M p ε δ : ℝ) := by
    convert hc using 1 <;> try rfl
    simp only [bellStrengthQ,Rat.cast_mul,Rat.cast_div,Rat.cast_add,
      Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat]
    field_simp
  have hden : (0 : ℝ)<(M : ℝ)*(ε : ℝ)^2 := by
    have hm : (0 : ℝ)<M := by exact_mod_cast hM
    have he : (0 : ℝ)<ε := Rat.cast_pos.mpr hε
    positivity
  have hh := (div_le_iff₀ hden).mp hratio
  nlinarith

-- The inequalities use the actual rounded budgets, not plan certificates.
/-- Complete original `bell_sparse_rates` guarantee for `RetainedBellPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem bell_sparse_rates (M : ℕ) (hM : 0<M) (p ε δ : ℚ)
    (hp : 0≤p) (hp1 : p≤1/2) (hε : 0<ε) (hmid : ¬p≤2*ε) :
    let r := (bellRecordsQ M p ε δ : ℝ)^2/(32*(M : ℝ))
    (ceilLog2Q (4/δ) : ℝ)≤r ∧
      (ceilLog2Q (4/δ) : ℝ)≤r*(ε : ℝ)^2/(4*((p : ℝ)+(ε : ℝ))) := by
  dsimp only
  have hm : (0 : ℝ)<M := by exact_mod_cast hM
  rcases bell_nonzero_tolerance p ε hp1 hε hmid with ⟨he,he1,hev⟩
  let v : ℝ := (p : ℝ)+(ε : ℝ)
  let L : ℝ := ceilLog2Q (4/δ)
  let r : ℝ := (bellRecordsQ M p ε δ : ℝ)^2/(32*(M : ℝ))
  have hv : 0<v := by dsimp [v]; linarith
  have hL : 0≤L := Nat.cast_nonneg _
  have hb := bell_records_square_budget M p ε δ hp hε
  have hrate : L≤r*(ε : ℝ)^2/(4*v) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<4*v)).mpr
    dsimp only [r]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<32*(M : ℝ))).mpr
    dsimp only [v,L]
    nlinarith [hb]
  have hs : (ε : ℝ)^2≤4*v := by dsimp [v] at *; nlinarith
  have hr0 : 0≤r := by dsimp [r]; positivity
  have hrate1 : r*(ε : ℝ)^2/(4*v)≤r := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<4*v)).mpr
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hs)]
  exact ⟨hrate.trans hrate1,hrate⟩

/-- Complete original `bell_dense_rates` guarantee for `RetainedBellPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem bell_dense_rates (M : ℕ) (hM : 0<M) (p ε δ : ℚ)
    (hp : 0≤p) (hp1 : p≤1/2) (hε : 0<ε) (hmid : ¬p≤2*ε) :
    (ceilLog2Q (4/δ) : ℝ)≤(bellBlocksQ M p ε δ : ℝ)*(M : ℝ)/64 ∧
      (ceilLog2Q (4/δ) : ℝ)≤
        ((bellBlocksQ M p ε δ : ℝ)*(M : ℝ)/8)*(ε : ℝ)^2/
          (4*((p : ℝ)+(ε : ℝ))) := by
  rcases bell_nonzero_tolerance p ε hp1 hε hmid with ⟨he,he1,hev⟩
  let v : ℝ := (p : ℝ)+(ε : ℝ)
  let L : ℝ := ceilLog2Q (4/δ)
  let T : ℝ := (bellBlocksQ M p ε δ : ℝ)*(M : ℝ)
  have hv : 0<v := by dsimp [v]; linarith
  have hL : 0≤L := Nat.cast_nonneg _
  have hT : 0≤T := by dsimp [T]; positivity
  have hb : 128*v*L≤T*(ε : ℝ)^2 := bell_blocks_budget M hM p ε δ hp hε
  have hs : (ε : ℝ)^2≤2*v := by dsimp [v] at *; nlinarith
  have haddr : L≤T/64 := by
    have hcancel : (64*L)*v≤T*v := by
      nlinarith [mul_nonneg hT (sub_nonneg.mpr hs)]
    have h64 : 64*L≤T := le_of_mul_le_mul_right hcancel hv
    apply (le_div_iff₀ (by norm_num : (0 : ℝ)<64)).mpr
    linarith
  have hrate : L≤(T/8)*(ε : ℝ)^2/(4*v) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<4*v)).mpr
    nlinarith
  exact ⟨haddr,hrate⟩

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_plan_copy_account
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_records_square_budget
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_blocks_budget
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_sparse_rates
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_dense_rates
