/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchFees.InterleaveComparison
import Qatlib.Papers.QAOAScaling23.SearchFees.Failure

/-!
# Resource bounds for large marked mass

The sampled search stage has resource increment at most `5 * m`, which controls geometric-window
costs. When marked mass is at least one half and validation is exact, plain trials give
sufficient early termination to bound every interleaved expected ledger by forty.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `slot_cost_bound`: For positive `m`, the expected single-stage charge in any ledger is at most
  `5 * m`.
* `highQ_interleaved_budget`: With exact validation and marked mass at least `1/2`, the expected
  charge in every ledger of interleaved geometric search is at most forty.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess
namespace Qatlib.Papers.QAOAScaling23.SearchFees

/-- The natural ceiling logarithm `Nat.clog 2 m` is at most `m`. -/
theorem clog_le_window (m:ℕ) : Nat.clog 2 m≤m := by
  rcases Nat.lt_or_ge m 2 with hm|hm
  · rcases Nat.eq_zero_or_pos m with h|h
    · simp [h]
    · have he:m=1:=by omega
      simp [he]
  · by_contra hc
    have hlt:m<Nat.clog 2 m:=by omega
    have hp:2^(Nat.clog 2 m-1)<m:=Nat.pow_pred_clog_lt_self (by norm_num : 1<2) (by omega : 1<m)
    have hk:m≤Nat.clog 2 m-1:=by omega
    have hh:m≤2^(Nat.clog 2 m-1):=hk.trans (le_of_lt Nat.lt_two_pow_self)
    omega
variable {I:Type} [Fintype I] [DecidableEq I]

/-- For a positive window `m`, every supported sampled outcome contributes at most `5 * m` to
any resource ledger. -/
theorem slot_increment_bound (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (f:Fee) (m:ℕ) (hm:0<m) (out:Option (I×ℕ)×ℕ×ℕ)
    (hout:out∈(preparedAASampled U hU seed S (Nat.clog 2 m) m 3).support) : increment f out≤5*m := by
  have hs:=sampled_attempt_shape U hU seed S m out hout
  have hc:=clog_le_window m
  rcases out with ⟨a,b,c⟩
  have hq:c≤m:=hs.1
  have hb:b≤3*Nat.clog 2 m:=hs.2.1
  cases a with
  | none=>
    cases f <;>simp only
        [increment,Option.isSome_none,Bool.false_eq_true,if_false,Option.map_none,Option.getD_none] <;>omega
  | some yg=>
    obtain ⟨y,g⟩:=yg
    have hg:g=3*c+1:=hs.2.2.2 y g rfl
    cases f <;>simp only
        [increment,Option.isSome_some,if_true,Option.map_some,Option.getD_some] <;>omega

/-- For positive `m`, the expected single-stage charge in any ledger is at most `5 * m`. -/
theorem slot_cost_bound (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (f:Fee) (m:ℕ) (hm:0<m) : slot U hU seed S f m≤((5*m:ℕ):ℝ≥0∞) := by
  apply expectation_le_of_support
  intro out hout
  exact_mod_cast slot_increment_bound U hU seed S f m hm out hout

/-- The expected resource charge of geometric window `off` is at most `15 * (6/5)^off` in
extended nonnegative reals. -/
theorem geometric_slot_cost (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (f:Fee) (M off:ℕ) : slot U hU seed S f (geometricWindow M off)≤
      ENNReal.ofReal 15*(ENNReal.ofReal (6/5:ℝ))^off := by
  calc
    _ ≤ ((5*geometricWindow M off:ℕ):ℝ≥0∞) := slot_cost_bound U hU seed S f _ (geometric_window_pos M off)
    _ = ENNReal.ofReal (5*(geometricWindow M off:ℝ)) := by norm_num
    _ ≤ ENNReal.ofReal (15*((6/5:ℝ)^off)) := ENNReal.ofReal_le_ofReal (by have h:=geometric_window_le M off;linarith)
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤15),ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤6/5)]

/-- With exact validation and marked mass at least `1/2`, a plain trial fails with probability
at most `1/2`. -/
theorem highQ_plain_fail (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) (hQ:(1/2:ℝ)≤MeasureProb (preparedAAState U seed) S) :
    fail U hU seed S valid 1≤(1/2:ℝ≥0∞) := by
  rw [plain_failure U hU seed S valid hvalid]
  have he:(1/2:ℝ≥0∞)=ENNReal.ofReal (1/2:ℝ) := by norm_num [ENNReal.ofReal_div_of_pos]
  have hh:(1/2:ℝ≥0∞)≤ENNReal.ofReal (MeasureProb (preparedAAState U seed) S) :=
      he.le.trans (ENNReal.ofReal_le_ofReal hQ)
  have hs:=tsub_le_tsub_left hh 1
  have hhalf:(1/2:ℝ≥0∞)+(1/2:ℝ≥0∞)=1 := by
    calc
      _ = 2*(2:ℝ≥0∞)⁻¹ := by simp only [div_eq_mul_inv,one_mul];ring
      _ = _ := ENNReal.mul_inv_cancel (by norm_num) (by finiteness)
  exact hs.trans_eq (ENNReal.eq_sub_of_add_eq (by finiteness) hhalf).symm

/-- With exact validation and marked mass at least `1/2`, the expected charge in every ledger of
interleaved geometric search is at most forty. -/
theorem highQ_interleaved_budget (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) (hQ:(1/2:ℝ)≤MeasureProb (preparedAAState U seed) S)
    (f:Fee) (M T:ℕ) : expected U hU seed S valid f (interleavePlain (geometricSearchSchedule M T))≤ENNReal.ofReal 40 := by
  let g:=ENNReal.ofReal (6/5:ℝ)
  have hg:(1:ℝ≥0∞)≤g := by rw [← ENNReal.ofReal_one];exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hnum:1+(1/2:ℝ≥0∞)*(ENNReal.ofReal 15+ENNReal.ofReal 40*g)≤ENNReal.ofReal 40 := by
    have hhalf:(1/2:ℝ≥0∞)=ENNReal.ofReal (1/2:ℝ) := by norm_num [ENNReal.ofReal_div_of_pos]
    change 1+(1/2:ℝ≥0∞)*(ENNReal.ofReal 15+ENNReal.ofReal 40*ENNReal.ofReal (6/5:ℝ))≤_
    rw [hhalf,← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤40),← ENNReal.ofReal_add (by norm_num : (0:ℝ)≤15) (by positivity),
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤1/2),← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (by norm_num : (0:ℝ)≤1) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hbound:∀t off:ℕ,expected U hU seed S valid f (interleavePlain (schedFrom M off t))≤ENNReal.ofReal 40*g^off := by
    intro t
    induction t with
    | zero=>intro off;simp [schedFrom_nil,interleavePlain,expected_nil]
    | succ t ih=>
      intro off
      rw [schedFrom_succ,interleaved_expected_cons]
      have hp:(1:ℝ≥0∞)≤g^off := one_le_pow₀ hg
      calc
        _ ≤ 1+(1/2:ℝ≥0∞)*(ENNReal.ofReal 15*g^off+1*(ENNReal.ofReal 40*g^(off+1))) :=
          add_le_add (plain_slot_le_one U hU seed S f)
            (mul_le_mul' (highQ_plain_fail U hU seed S valid hvalid hQ)
              (add_le_add (geometric_slot_cost U hU seed S f M off)
                (mul_le_mul' (fail_le_one U hU seed S valid _) (ih (off+1)))))
        _ ≤ g^off+(1/2:ℝ≥0∞)*(ENNReal.ofReal 15*g^off+1*(ENNReal.ofReal 40*g^(off+1))) := add_le_add hp le_rfl
        _ = (1+(1/2:ℝ≥0∞)*(ENNReal.ofReal 15+ENNReal.ofReal 40*g))*g^off := by rw [pow_succ];ring
        _ ≤ _ := mul_le_mul_left hnum _
  have h:=hbound T 0
  simpa only [schedFrom_zero,pow_zero,mul_one] using h
end Qatlib.Papers.QAOAScaling23.SearchFees
