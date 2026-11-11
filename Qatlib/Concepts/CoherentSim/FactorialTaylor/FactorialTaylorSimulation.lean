/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.TaylorEncoding.LogarithmicTaylorSimulation

/-!
# Factorial Taylor cutoff and remainder estimates

`factorialTaylorCutoff` searches for the first factorial exceeding a dyadic threshold, and
`factorialTaylorPrecision` budgets the error of repeated coherent amplification. The cutoff has
an eventual logarithmic rate bound, and factorial tail estimates control scalar and matrix
remainders for truncated Taylor simulation [BerryEtAl2015Taylor].

## Main statements

* `factorial_taylor_native_cutoff_and_rate`: Correctness and eventual growth bound for the
  cutoff search.
* `factorial_taylor_tail_and_coherent_precision`: Factorial tail estimates and the accumulated
  coherent error budget.
* `factorialTaylor_matrix_remainder_of_unitary`: A matrix Taylor remainder bound for unitary
  summands.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

open Qatlib.Concepts.OperatorErrors.Robustness
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.CoherentSim.FactorialTaylor
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-- The first searched index `n` with `2^m ≤ (n + 1)!`, with fallback value `2 * m + 1`. -/
def factorialTaylorCutoff (m : ℕ) : ℕ :=
  ((List.range (2*m+2)).find? (fun n => 2^m ≤ (n+1).factorial)).getD (2*m+1)

/-- The precision parameter `2 * (k + Nat.clog 2 (max 1 s) + 8)` for `s` coherent Taylor
segments. -/
def factorialTaylorPrecision (s k : ℕ) : ℕ := 2*(k + Nat.clog 2 (max 1 s) + 8)

/-- The factorial cutoff reaches its threshold, is minimal, lies below `2 * m + 1`, and is found
by the bounded search. -/
private theorem factorial_search (m : ℕ) :
    2^m ≤ (factorialTaylorCutoff m+1).factorial ∧
    (∀ j < factorialTaylorCutoff m, (j+1).factorial < 2^m) ∧
    factorialTaylorCutoff m ≤ 2*m+1 ∧
    ((List.range (2*m+2)).find? (fun n => 2^m ≤ (n+1).factorial)).isSome := by
  have hb : 2^m ≤ (2*m+2).factorial := by
    have h := Nat.two_pow_mul_factorial_le_factorial_two_mul m
    have hp := Nat.factorial_pos m
    exact (by nlinarith : 2^m ≤ (2*m).factorial).trans
      (Nat.factorial_le (by omega))
  cases he : (List.range (2*m+2)).find? (fun n => decide (2^m ≤ (n+1).factorial)) with
  | none =>
    have hn := List.find?_eq_none.mp he (2*m+1) (by simp)
    simp only [decide_eq_true_eq] at hn
    exact (hn (by simpa [Nat.add_assoc] using! hb)).elim
  | some n =>
    have hn := (List.find?_range'_eq_some.mp (by simpa only [List.range_eq_range'] using! he))
    simp only [decide_eq_true_eq, List.mem_range'_1, Nat.zero_le, Nat.zero_add,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_le, true_and, true_implies] at hn
    simpa [factorialTaylorCutoff, he] using!
      (show 2^m ≤ (n+1).factorial ∧ (∀ j < n, (j+1).factorial < 2^m) ∧
        n ≤ 2*m+1 ∧ True from ⟨hn.1, fun j hj => hn.2.2 j hj,
          by omega, trivial⟩)

/-- Any index whose successor factorial reaches `2^m` bounds `factorialTaylorCutoff m` from
above. -/
private theorem factorial_cutoff_le (m n : ℕ) (hn : 2^m ≤ (n+1).factorial) :
    factorialTaylorCutoff m ≤ n := by
  by_contra h
  exact (not_lt_of_ge hn) ((factorial_search m).2.1 n (by omega))

/-- For a natural number `a`, the power `a^a` is bounded by `(2 * a)!`. -/
private theorem factorial_half_power (a : ℕ) : a^a ≤ (2*a).factorial := by
  have h := Nat.factorial_mul_pow_le_factorial (m := a) (n := a)
  have hp := Nat.factorial_pos a
  have hpow := Nat.pow_le_pow_left (show a ≤ a+1 by omega) a
  have ha : a+a = 2*a := by omega
  rw [ha] at h
  nlinarith

/-- The bounded factorial search succeeds and returns the minimal cutoff. Eventually, the cutoff
times `Nat.log 2 m` is bounded by a fixed positive constant times `m`. See
[BerryEtAl2015Taylor]. -/
theorem factorial_taylor_native_cutoff_and_rate :
  (∀ m : ℕ, 2^m ≤ (factorialTaylorCutoff m+1).factorial ∧
    (∀ j < factorialTaylorCutoff m, (j+1).factorial < 2^m) ∧
    factorialTaylorCutoff m ≤ 2*m+1 ∧
    ((List.range (2*m+2)).find? (fun n => 2^m ≤ (n+1).factorial)).isSome) ∧
  (∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ m ≥ m₀,
    factorialTaylorCutoff m * Nat.log 2 m ≤ C*m) := by
  refine ⟨factorial_search, 12, 4, by omega, by omega, ?_⟩
  intro m hm
  let L := Nat.log 2 m
  let r := L/2
  let a := m/r+1
  have hL : 2 ≤ L := Nat.le_log_of_pow_le (by omega) (by norm_num; omega)
  have hr : 0 < r := by dsimp [r]; omega
  have hLr : L ≤ 3*r := by dsimp [r]; omega
  have h2r : 2*r ≤ L := by dsimp [r]; omega
  have hpow : 2^L ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hrr : r ≤ 2^r := Nat.lt_two_pow_self.le
  have hrpow : r*2^r ≤ m := calc
    r*2^r ≤ 2^r*2^r := Nat.mul_le_mul_right _ hrr
    _ = 2^(2*r) := by rw [← pow_add]; congr 1; omega
    _ ≤ 2^L := Nat.pow_le_pow_right (by omega) h2r
    _ ≤ m := hpow
  have ha : 2^r ≤ a := by
    have hd : 2^r ≤ m/r := (Nat.le_div_iff_mul_le hr).mpr (by simpa [Nat.mul_comm] using! hrpow)
    dsimp [a]
    omega
  have hma : m ≤ r*a := by
    have hh := Nat.mod_lt m hr
    have hd := Nat.mod_add_div m r
    dsimp [a]
    nlinarith
  have hf : 2^m ≤ (2*a).factorial := calc
    2^m ≤ 2^(r*a) := Nat.pow_le_pow_right (by omega) hma
    _ = (2^r)^a := pow_mul _ _ _
    _ ≤ a^a := Nat.pow_le_pow_left ha a
    _ ≤ (2*a).factorial := factorial_half_power a
  have hk : factorialTaylorCutoff m ≤ 2*a :=
    factorial_cutoff_le m (2*a) (hf.trans (Nat.factorial_le (by omega)))
  have har : a*r ≤ m+r := by
    have hd := Nat.div_mul_le_self m r
    dsimp [a]
    nlinarith
  have hrm : r ≤ m := by
    have hh := Nat.log_le_self 2 m
    dsimp [r, L]
    omega
  calc
    factorialTaylorCutoff m * L ≤ (2*a)*L := Nat.mul_le_mul_right _ hk
    _ ≤ (2*a)*(3*r) := Nat.mul_le_mul_left _ hLr
    _ ≤ 12*m := by nlinarith

/-- For `0 ≤ θ ≤ 1`, the factorial tail after order `K` is summable and at most twice its first
term. -/
theorem factorialTaylor_tail (θ : ℝ) (K : ℕ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Summable (fun j : ℕ => θ^(K+1+j)/((K+1+j).factorial : ℝ)) ∧
    (∑' j : ℕ, θ^(K+1+j)/((K+1+j).factorial : ℝ)) ≤
      2*θ^(K+1)/((K+1).factorial : ℝ) := by
  have hf : Summable (fun j : ℕ => θ^(K+1+j)/((K+1+j).factorial : ℝ)) := by
    simpa [Nat.add_comm] using! (summable_nat_add_iff (K+1)).2
      (Real.summable_pow_div_factorial θ)
  have hg := summable_geometric_two.mul_left (θ^(K+1)/((K+1).factorial : ℝ))
  have hb : ∀ j : ℕ, θ^(K+1+j)/((K+1+j).factorial : ℝ) ≤
      (θ^(K+1)/((K+1).factorial : ℝ))*(1/2:ℝ)^j := by
    intro j
    have hn : (K+1).factorial * 2^j ≤ (K+1+j).factorial :=
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : 2 ≤ K+1+1) j)).trans
        Nat.factorial_mul_pow_le_factorial
    have hnR : ((K+1).factorial : ℝ) * (2:ℝ)^j ≤ ((K+1+j).factorial : ℝ) := by
      exact_mod_cast hn
    have hp := pow_le_one₀ hθ hθ1 (n := j)
    rw [pow_add]
    calc
      θ^(K+1)*θ^j/((K+1+j).factorial : ℝ) ≤ θ^(K+1)/((K+1+j).factorial : ℝ) := by
        gcongr
        exact mul_le_of_le_one_right (by positivity) hp
      _ ≤ θ^(K+1)/(((K+1).factorial : ℝ)*(2:ℝ)^j) := by gcongr
      _ = (θ^(K+1)/((K+1).factorial : ℝ))*(1/2:ℝ)^j := by
        rw [div_mul_eq_div_mul_one_div, _root_.one_div_pow]
  refine ⟨hf, (hf.tsum_le_tsum hb hg).trans_eq ?_⟩
  rw [tsum_mul_left, tsum_geometric_two]
  ring

/-- The factorial cutoff and precision choices bound the accumulated coherent amplification
error over `s` segments by `2⁻ᵏ`. -/
theorem factorialTaylor_coherent_precision (s k : ℕ) :
    (s:ℝ)*Real.sqrt (2*coherentOAAError
      (2/((factorialTaylorCutoff (factorialTaylorPrecision s k)+1).factorial : ℝ))) ≤
        (1/2:ℝ)^k := by
  let a : ℝ := (1/2:ℝ)^(k+Nat.clog 2 (max 1 s)+8)
  let ε : ℝ := 2/((factorialTaylorCutoff (factorialTaylorPrecision s k)+1).factorial : ℝ)
  have he : ε ≤ 2*a^2 := by
    have hn := (factorial_taylor_native_cutoff_and_rate.1 (factorialTaylorPrecision s k)).1
    have hnR : (2:ℝ)^factorialTaylorPrecision s k ≤
        ((factorialTaylorCutoff (factorialTaylorPrecision s k)+1).factorial : ℝ) := by
      exact_mod_cast hn
    calc ε ≤ 2/(2:ℝ)^factorialTaylorPrecision s k := by dsimp [ε]; gcongr
         _ = 2*a^2 := by
           dsimp [factorialTaylorPrecision, a]
           rw [Nat.mul_comm 2, pow_mul]
           simp only [div_eq_mul_inv, one_mul, inv_pow]
  have ha : 0 ≤ a := by positivity
  have ha1 : a ≤ (1/2:ℝ)^8 := by
    dsimp [a]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have he0 : 0 ≤ ε := by dsimp [ε]; positivity
  have he1 : ε ≤ 1 := by norm_num at ha1; nlinarith
  have hc : coherentOAAError ε ≤ 5*ε := by
    unfold coherentOAAError
    have hsq := pow_le_one₀ he0 he1 (n := 2)
    nlinarith
  have hsqrt : Real.sqrt (2*coherentOAAError ε) ≤ 8*a := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg a]
  have hs : (s:ℝ) ≤ (2:ℝ)^Nat.clog 2 (max 1 s) := by
    exact_mod_cast (le_max_right 1 s).trans (Nat.le_pow_clog (by omega) (max 1 s))
  have hsp : (s:ℝ)*(1/2:ℝ)^Nat.clog 2 (max 1 s) ≤ 1 := by
    have hp : (2:ℝ)^Nat.clog 2 (max 1 s)*(1/2:ℝ)^Nat.clog 2 (max 1 s) = 1 := by
      rw [← mul_pow]; norm_num
    exact (mul_le_mul_of_nonneg_right hs (by positivity)).trans hp.le
  calc
    _ ≤ (s:ℝ)*(8*a) := mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg _)
    _ = (1/2:ℝ)^k*((s:ℝ)*(1/2:ℝ)^Nat.clog 2 (max 1 s))/32 := by
      dsimp [a]; simp only [pow_add]; norm_num; ring
    _ ≤ (1/2:ℝ)^k := by
      have hp : 0 ≤ (1/2:ℝ)^k := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hsp hp]

/-- The scalar factorial-tail estimate and the dyadic coherent precision budget hold
simultaneously. See [BerryEtAl2015Taylor]. -/
theorem factorial_taylor_tail_and_coherent_precision :
  (∀ (θ : ℝ) (K : ℕ), 0 ≤ θ → θ ≤ 1 →
    Summable (fun j : ℕ => θ^(K+1+j)/((K+1+j).factorial : ℝ)) ∧
    (∑' j : ℕ, θ^(K+1+j)/((K+1+j).factorial : ℝ)) ≤
      2*θ^(K+1)/((K+1).factorial : ℝ)) ∧
  (∀ s k : ℕ,
    (s:ℝ)*Real.sqrt (2*coherentOAAError
      (2/((factorialTaylorCutoff (factorialTaylorPrecision s k)+1).factorial : ℝ))) ≤
        (1/2:ℝ)^k) :=
  ⟨factorialTaylor_tail, factorialTaylor_coherent_precision⟩

variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

omit [DecidableEq J] in
set_option maxHeartbeats 800000 in

/-- For unitary summands and coefficient mass times segment duration at most `1 / 2`, the
order-`K` Taylor approximation has norm error at most `2 / (K + 1)!`. -/
theorem factorialTaylor_matrix_remainder_of_unitary
    (h : J → ℝ) (U : J → Matrix I I ℂ) (τ : ℝ) (K : ℕ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ)
    (hτ : (∑ j, |h j|) * |τ| ≤ 1 / 2) :
    ‖Polynomial.aeval (∑ j, (h j : ℂ) • U j) (exponentialTaylorPolynomial τ (K + 1)) -
      hamiltonianEvolution (∑ j, (h j : ℂ) • U j) τ‖ ≤ 2 / ((K+1).factorial : ℝ) := by
  let H : Matrix I I ℂ := ∑ j, (h j : ℂ) • U j
  let X : Matrix I I ℂ := (-Complex.I * (τ : ℂ)) • H
  have hH : ‖H‖ ≤ ∑ j, |h j| := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (l2_norm_unitary_le_one (hU j))
  have hX : ‖X‖ ≤ 1 / 2 := by
    have hc : ‖-Complex.I * (τ : ℂ)‖ = |τ| := by
      simp [Complex.norm_real, Real.norm_eq_abs]
    calc ‖X‖ = |τ| * ‖H‖ := by rw [norm_smul, hc]
      _ ≤ |τ| * ∑ j, |h j| := mul_le_mul_of_nonneg_left hH (abs_nonneg _)
      _ ≤ 1 / 2 := by simpa [mul_comm] using! hτ
  let f : ℕ → Matrix I I ℂ := fun n => (n.factorial : ℂ)⁻¹ • X ^ n
  have hf : Summable f := NormedSpace.expSeries_summable' X
  have hfn : Summable fun n => ‖f n‖ := NormedSpace.norm_expSeries_summable' X
  have ht : ∑' n, f n = NormedSpace.exp X := (NormedSpace.exp_series_hasSum_exp' X).tsum_eq
  have htail : NormedSpace.exp X - ∑ n ∈ Finset.range (K + 1), f n =
      ∑' n, f (n + (K + 1)) := by
    have hs := hf.sum_add_tsum_nat_add (K + 1)
    rw [ht] at hs
    exact eq_sub_of_add_eq' hs |>.symm
  have hterm : ∀ n, 0 < n → ‖f n‖ ≤ (1 : ℝ)^n/(n.factorial : ℝ) := by
    intro n hnpos
    calc ‖f n‖ = (n.factorial : ℝ)⁻¹ * ‖X ^ n‖ := by
          simp [f, norm_smul, norm_inv]
      _ ≤ (n.factorial : ℝ)⁻¹ * ‖X‖ ^ n :=
          mul_le_mul_of_nonneg_left (norm_pow_le' X hnpos) (by positivity)
      _ ≤ (n.factorial : ℝ)⁻¹ * 1^n := by
          gcongr
          linarith
      _ = (1:ℝ)^n/(n.factorial : ℝ) := by simp
  have hn : Summable fun n => ‖f (n + (K + 1))‖ := (summable_nat_add_iff _).2 hfn
  have htailScalar := factorial_taylor_tail_and_coherent_precision.1 1 K (by norm_num) (by norm_num)
  have hg : Summable fun n => (1 : ℝ)^(n+(K+1))/((n+(K+1)).factorial : ℝ) := by
    simpa [Nat.add_comm] using! htailScalar.1
  rw [aeval_exponentialTaylorPolynomial, norm_sub_rev]
  change ‖NormedSpace.exp X - ∑ n ∈ Finset.range (K + 1), f n‖ ≤ _
  rw [htail]
  calc ‖∑' n, f (n + (K + 1))‖ ≤ ∑' n, ‖f (n + (K + 1))‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n, (1 : ℝ)^(n+(K+1))/((n+(K+1)).factorial : ℝ) :=
      hn.tsum_le_tsum (fun n => hterm _ (by omega)) hg
    _ ≤ 2/((K+1).factorial : ℝ) := by
      simpa [Nat.add_comm] using! htailScalar.2

set_option maxHeartbeats 800000 in

/-- For Hermitian unitary summands with the stated small-segment bound, the Taylor approximation
has norm error at most `2 / (K + 1)!`. -/
theorem factorialTaylor_matrix_remainder
    (h : J → ℝ) (U : J → Matrix I I ℂ) (τ : ℝ) (K : ℕ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ ∧ (U j).IsHermitian)
    (hτ : (∑ j, |h j|) * |τ| ≤ 1 / 2) :
    ‖Polynomial.aeval (∑ j, (h j : ℂ) • U j) (exponentialTaylorPolynomial τ (K + 1)) -
      hamiltonianEvolution (∑ j, (h j : ℂ) • U j) τ‖ ≤ 2 / ((K+1).factorial : ℝ) := by
  exact factorialTaylor_matrix_remainder_of_unitary h U τ K (fun j => (hU j).1) hτ

end Qatlib.Concepts.CoherentSim.FactorialTaylor
