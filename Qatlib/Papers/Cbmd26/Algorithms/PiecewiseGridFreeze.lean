/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.InputBridge
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Freezing Supplied Piecewise Hamiltonians

This module represents piecewise constant Hamiltonian evolution using `suppliedGridEvolution`, a
chronological product over supplied breakpoints. `suppliedGridTick` rounds breakpoints upward to
a uniform time grid, and `suppliedFrozenTable` repeats each interval's Hamiltonian according to
its rounded duration.

The product perturbation and Hamiltonian time-Lipschitz estimates yield
`suppliedGridEvolution_freezing_error`, whose error is at most `2 * Λ * N * h` for Hermitian
interval matrices bounded by `Λ`. The piecewise field `suppliedGridField` is also related
exactly to frozen-table entries and to its full uniform sample list. See [WangEtAl2026].

## Main statements

* `piecewiseLeftProduct_error` bounds product error by the sum of factor errors for
  contractions.
* `suppliedFrozenTable_evolution` identifies the frozen-table evolution with evolution over
  rounded breakpoints.
* `suppliedGridEvolution_freezing_error` bounds the effect of rounding the supplied grid.
* `suppliedGridField_sample_list` identifies all uniform samples with the frozen table.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace CBMD
open Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

section Matrices
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The chronological matrix product that starts with the identity and multiplies each
successive factor on the left. -/
def piecewiseLeftProduct (f : ℕ → Matrix I I ℂ) : ℕ → Matrix I I ℂ
  | 0 => 1
  | n + 1 => f n * piecewiseLeftProduct f n

/-- Expresses the chronological product of the first `n` factors as the product of the reversed
list obtained from `List.range n`. -/
theorem piecewiseLeftProduct_eq_reverse_prod (f : ℕ → Matrix I I ℂ) (n : ℕ) :
    piecewiseLeftProduct f n = (((List.range n).map f).reverse).prod := by
  induction n with
  | zero => simp [piecewiseLeftProduct]
  | succ n ih => simp [List.range_succ, piecewiseLeftProduct, ih]

/-- A chronological product of factors with norm at most one also has norm at most one. -/
theorem piecewiseLeftProduct_norm_le_one (f : ℕ → Matrix I I ℂ) (n : ℕ)
    (hf : ∀ j < n, ‖f j‖ ≤ 1) : ‖piecewiseLeftProduct f n‖ ≤ 1 := by
  induction n with
  | zero => exact l2_norm_one_le
  | succ n ih =>
    exact (norm_mul_le _ _).trans ((mul_le_mul (hf n (by omega))
      (ih (fun j hj => hf j (by omega))) (norm_nonneg _) (by norm_num)).trans_eq (by ring))

/-- For two families of contraction factors, bounds the difference of their chronological
products by the sum of the corresponding factor errors. -/
theorem piecewiseLeftProduct_error (f g : ℕ → Matrix I I ℂ) (n : ℕ)
    (hf : ∀ j < n, ‖f j‖ ≤ 1) (hg : ∀ j < n, ‖g j‖ ≤ 1) :
    ‖piecewiseLeftProduct f n - piecewiseLeftProduct g n‖ ≤
      ∑ j ∈ Finset.range n, ‖f j - g j‖ := by
  induction n with
  | zero => simp [piecewiseLeftProduct]
  | succ n ih =>
    have hp := ih (fun j hj => hf j (by omega)) (fun j hj => hg j (by omega))
    have hn := piecewiseLeftProduct_norm_le_one g n (fun j hj => hg j (by omega))
    have he : piecewiseLeftProduct f (n+1) - piecewiseLeftProduct g (n+1) =
        f n * (piecewiseLeftProduct f n - piecewiseLeftProduct g n) +
          (f n - g n) * piecewiseLeftProduct g n := by
      simp only [piecewiseLeftProduct]
      noncomm_ring
    rw [he, Finset.sum_range_succ]
    calc
      _ ≤ ‖f n‖ * ‖piecewiseLeftProduct f n - piecewiseLeftProduct g n‖ +
          ‖f n-g n‖ * ‖piecewiseLeftProduct g n‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ 1 * (∑ j ∈ Finset.range n, ‖f j-g j‖) + ‖f n-g n‖ * 1 := by
        exact add_le_add (mul_le_mul (hf n (by omega)) hp (norm_nonneg _) (by norm_num))
          (mul_le_mul_of_nonneg_left hn (norm_nonneg _))
      _ = _ := by ring

/-- The derivative of `HamiltonianEvolution B` at time `t` is `-(Complex.I • B *
HamiltonianEvolution B t)`. -/
private theorem piecewise_hamiltonian_deriv (B : Matrix I I ℂ) (t : ℝ) :
    HasDerivAt (HamiltonianEvolution B) (-(Complex.I • B * HamiltonianEvolution B t)) t := by
  have he : (fun u : ℝ => NormedSpace.exp (u • (-Complex.I • B))) = HamiltonianEvolution B := by
    funext u
    unfold HamiltonianEvolution
    congr 1
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
    ring
  have hd := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-Complex.I • B) t
  rw [congrFun he t, he] at hd
  simpa only [neg_smul, neg_mul] using hd

/-- For Hermitian `B`, its Hamiltonian evolution is Lipschitz in time with constant `‖B‖` in
operator norm. -/
theorem piecewise_hamiltonian_time_lipschitz (B : Matrix I I ℂ) (hB : B.IsHermitian)
    (s t : ℝ) : ‖HamiltonianEvolution B t - HamiltonianEvolution B s‖ ≤ ‖B‖ * |t-s| := by
  have hb (u : ℝ) : ‖-(Complex.I • B * HamiltonianEvolution B u)‖ ≤ ‖B‖ := by
    rw [norm_neg]
    have hn := l2_norm_unitary_le_one (hamiltonianEvolution_unitary hB u)
    have h := (norm_mul_le (Complex.I • B) (HamiltonianEvolution B u)).trans
      (mul_le_mul_of_nonneg_left hn (norm_nonneg _))
    simpa only [mul_one, norm_smul, Complex.norm_I, one_mul] using h
  have hst (a b : ℝ) (hab : a ≤ b) :
      ‖HamiltonianEvolution B b-HamiltonianEvolution B a‖ ≤ ‖B‖*(b-a) :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      (fun u _ => (piecewise_hamiltonian_deriv B u).hasDerivWithinAt)
      (fun u _ => hb u) b ⟨hab,le_rfl⟩
  rcases le_total s t with h | h
  · simpa only [abs_of_nonneg (sub_nonneg.mpr h)] using hst s t h
  · rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr h)]
    simpa only [neg_sub] using hst t s h

/-- The chronological product of exact Hamiltonian evolutions for the first `N` supplied
intervals, using matrix `B j` for duration `τ (j+1) - τ j`. -/
def suppliedGridEvolution (τ : ℕ → ℝ) (B : ℕ → Matrix I I ℂ) (N : ℕ) : Matrix I I ℂ :=
  piecewiseLeftProduct (fun j => HamiltonianEvolution (B j) (τ (j+1)-τ j)) N

/-- The natural-number ceiling of the supplied breakpoint `τ j` divided by the uniform grid step
`h`. -/
def suppliedGridTick (τ : ℕ → ℝ) (h : ℝ) (j : ℕ) : ℕ := ⌈τ j / h⌉₊

/-- The list that repeats each interval matrix `B j` according to the difference between its
consecutive rounded grid ticks. -/
def suppliedFrozenTable (τ : ℕ → ℝ) (B : ℕ → Matrix I I ℂ) (h : ℝ) (N : ℕ) :
    List (Matrix I I ℂ) :=
  (List.range N).flatMap (fun j => List.replicate
    (suppliedGridTick τ h (j+1)-suppliedGridTick τ h j) (B j))

/-- Rounding supplied breakpoints to grid ticks preserves monotonicity when the grid step is
positive. -/
private theorem suppliedGridTick_mono {τ : ℕ → ℝ} (hτ : Monotone τ) {h : ℝ} (hh : 0 < h) :
    Monotone (suppliedGridTick τ h) := by
  intro i j hij
  exact Nat.ceil_mono (div_le_div_of_nonneg_right (hτ hij) hh.le)

omit [Fintype I] [DecidableEq I] in

/-- Extending the frozen table by one supplied interval appends the corresponding number of
copies of its matrix `B N`. -/
private theorem suppliedFrozenTable_succ (τ : ℕ → ℝ) (B : ℕ → Matrix I I ℂ) (h : ℝ) (N : ℕ) :
    suppliedFrozenTable τ B h (N+1) = suppliedFrozenTable τ B h N ++
      List.replicate (suppliedGridTick τ h (N+1)-suppliedGridTick τ h N) (B N) := by
  simp [suppliedFrozenTable, List.range_succ]

/-- For a monotone breakpoint grid starting at zero and a positive step, the frozen table length
is the final rounded grid tick. -/
theorem suppliedFrozenTable_length {τ : ℕ → ℝ} (hτ : Monotone τ) (hτ0 : τ 0 = 0)
    (B : ℕ → Matrix I I ℂ) {h : ℝ} (hh : 0 < h) (N : ℕ) :
    (suppliedFrozenTable τ B h N).length = suppliedGridTick τ h N := by
  induction N with
  | zero => simp [suppliedFrozenTable, suppliedGridTick, hτ0]
  | succ N ih =>
    rw [suppliedFrozenTable_succ, List.length_append, List.length_replicate, ih]
    exact Nat.add_sub_of_le (suppliedGridTick_mono hτ hh (Nat.le_succ N))

/-- Repeating the same Hamiltonian evolution `n` times equals evolution for the total time `n *
h`. -/
private theorem piecewise_evolution_pow (B : Matrix I I ℂ) (h : ℝ) (n : ℕ) :
    HamiltonianEvolution B h ^ n = HamiltonianEvolution B ((n : ℝ)*h) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← hamiltonianEvolution_add]
    congr 1
    push_cast
    ring

/-- The reversed product of step-`h` evolutions of the frozen table equals supplied-grid
evolution with every breakpoint rounded up to its grid tick. -/
theorem suppliedFrozenTable_evolution {τ : ℕ → ℝ} (hτ : Monotone τ)
    (B : ℕ → Matrix I I ℂ) {h : ℝ} (hh : 0 < h) (N : ℕ) :
    (((suppliedFrozenTable τ B h N).map (fun X => HamiltonianEvolution X h)).reverse).prod =
      suppliedGridEvolution (fun j => (suppliedGridTick τ h j : ℝ)*h) B N := by
  induction N with
  | zero => simp [suppliedFrozenTable, suppliedGridEvolution, piecewiseLeftProduct]
  | succ N ih =>
    rw [suppliedFrozenTable_succ, List.map_append, List.reverse_append, List.prod_append,
      List.map_replicate, List.reverse_replicate, List.prod_replicate, piecewise_evolution_pow, ih]
    unfold suppliedGridEvolution
    rw [piecewiseLeftProduct]
    congr 2
    rw [Nat.cast_sub (suppliedGridTick_mono hτ hh (Nat.le_succ N))]
    ring

/-- For a monotone grid starting at zero and Hermitian interval matrices bounded by `Λ`,
rounding to a positive uniform step `h` changes the evolution by at most `2 * Λ * N * h`. -/
theorem suppliedGridEvolution_freezing_error {τ : ℕ → ℝ} (hτ : Monotone τ) (hτ0 : τ 0 = 0)
    (B : ℕ → Matrix I I ℂ) (N : ℕ) {h Λ : ℝ} (hh : 0 < h) (hΛ : 0 ≤ Λ)
    (hB : ∀ j < N, (B j).IsHermitian ∧ ‖B j‖ ≤ Λ) :
    ‖suppliedGridEvolution τ B N -
      (((suppliedFrozenTable τ B h N).map (fun X => HamiltonianEvolution X h)).reverse).prod‖ ≤
        2 * Λ * N * h := by
  have he (j : ℕ) : |(suppliedGridTick τ h j : ℝ)*h-τ j| ≤ h := by
    have hj : 0 ≤ τ j := by simpa only [hτ0] using hτ (Nat.zero_le j)
    have hl := Nat.le_ceil (τ j / h)
    have hu := Nat.ceil_lt_add_one (div_nonneg hj hh.le)
    have hl' := (div_le_iff₀ hh).mp hl
    have hu' := mul_lt_mul_of_pos_right hu hh
    rw [add_mul, div_mul_cancel₀ _ hh.ne', one_mul] at hu'
    apply abs_le.mpr
    dsimp [suppliedGridTick] at *
    constructor <;> linarith
  rw [suppliedFrozenTable_evolution hτ B hh N]
  have hp := piecewiseLeftProduct_error
    (fun j => HamiltonianEvolution (B j) (τ (j+1)-τ j))
    (fun j => HamiltonianEvolution (B j)
      ((suppliedGridTick τ h (j+1):ℝ)*h-(suppliedGridTick τ h j:ℝ)*h)) N
    (fun j hj => l2_norm_unitary_le_one (hamiltonianEvolution_unitary (hB j hj).1 _))
    (fun j hj => l2_norm_unitary_le_one (hamiltonianEvolution_unitary (hB j hj).1 _))
  apply hp.trans
  calc
    _ ≤ ∑ j ∈ Finset.range N, Λ*(2*h) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjN := Finset.mem_range.mp hj
      have ht := piecewise_hamiltonian_time_lipschitz (B j) (hB j hjN).1
        ((suppliedGridTick τ h (j+1):ℝ)*h-(suppliedGridTick τ h j:ℝ)*h) (τ (j+1)-τ j)
      have hd : |(τ (j+1)-τ j)-
          ((suppliedGridTick τ h (j+1):ℝ)*h-(suppliedGridTick τ h j:ℝ)*h)| ≤ 2*h := by
        have h1 := abs_le.mp (he (j+1))
        have h0 := abs_le.mp (he j)
        exact abs_le.mpr ⟨by linarith,by linarith⟩
      exact ht.trans (mul_le_mul (hB j hjN).2 hd (abs_nonneg _) hΛ)
    _ = _ := by simp; ring

/-- The piecewise constant matrix field equal to the first `B j` whose supplied half-open
interval contains the time, and zero if no interval contains it. -/
def suppliedGridField (τ : ℕ → ℝ) (B : ℕ → Matrix I I ℂ) (N : ℕ) (u : ℝ) :
    Matrix I I ℂ := by
  classical
  exact if h : ∃ j : ℕ, j < N ∧ τ j ≤ u ∧ u < τ (j+1)
    then B (Nat.find h) else 0

/-- A time belongs to at most one half-open interval of a monotone supplied breakpoint sequence. -/
private theorem suppliedGrid_interval_unique {τ : ℕ → ℝ} (hτ : Monotone τ)
    {u : ℝ} {i j : ℕ} (hi : τ i ≤ u ∧ u < τ (i+1))
    (hj : τ j ≤ u ∧ u < τ (j+1)) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := hτ (show i+1 ≤ j by omega)
    linarith [hi.2, hj.1]
  · exact h
  · have := hτ (show j+1 ≤ i by omega)
    linarith [hj.2, hi.1]

omit [Fintype I] [DecidableEq I] in

/-- On the half-open interval from `τ j` to `τ (j+1)`, the supplied field equals `B j` when `j <
N` and the breakpoints are monotone. -/
theorem suppliedGridField_on_interval {τ : ℕ → ℝ} (hτ : Monotone τ)
    (B : ℕ → Matrix I I ℂ) {N j : ℕ} {u : ℝ}
    (hj : j < N) (hu : τ j ≤ u ∧ u < τ (j+1)) :
    suppliedGridField τ B N u = B j := by
  classical
  have hex : ∃ i : ℕ, i < N ∧ τ i ≤ u ∧ u < τ (i+1) := ⟨j,hj,hu⟩
  have hi := Nat.find_spec hex
  have he := suppliedGrid_interval_unique hτ hi.2 hu
  simp only [suppliedGridField, dite_eq_left hex, he]

/-- If the first `N` interval matrices are Hermitian with norm at most a nonnegative `Λ`, then
the supplied field has these properties at every time. -/
theorem suppliedGridField_bound (τ : ℕ → ℝ) (B : ℕ → Matrix I I ℂ)
    (N : ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hB : ∀ j < N, (B j).IsHermitian ∧ ‖B j‖ ≤ Λ) (u : ℝ) :
    (suppliedGridField τ B N u).IsHermitian ∧ ‖suppliedGridField τ B N u‖ ≤ Λ := by
  classical
  unfold suppliedGridField
  split_ifs with h
  · exact hB (Nat.find h) (Nat.find_spec h).1
  · simpa using And.intro (Matrix.isHermitian_zero : (0 : Matrix I I ℂ).IsHermitian) hΛ

/-- Every natural tick before the final supplied tick lies between two consecutive supplied
ticks, provided the breakpoint sequence starts at zero. -/
private theorem suppliedGridTick_block {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    (h : ℝ) (N j : ℕ) (hj : j < suppliedGridTick τ h N) :
    ∃ i < N, suppliedGridTick τ h i ≤ j ∧ j < suppliedGridTick τ h (i+1) := by
  induction N with
  | zero => simp [suppliedGridTick, hτ0] at hj
  | succ N ih =>
    by_cases hn : j < suppliedGridTick τ h N
    · obtain ⟨i,hi,hil,hir⟩ := ih hn
      exact ⟨i,by omega,hil,hir⟩
    · exact ⟨N,by omega,by omega,hj⟩

/-- A frozen-table entry whose index lies between the rounded endpoints of interval `i` is
exactly `B i`, under the monotone-grid and positive-step assumptions. -/
private theorem suppliedFrozenTable_lookup {τ : ℕ → ℝ} (hτ : Monotone τ) (hτ0 : τ 0 = 0)
    (B : ℕ → Matrix I I ℂ) {h : ℝ} (hh : 0 < h) (N i j : ℕ)
    (hi : i < N) (hjl : suppliedGridTick τ h i ≤ j)
    (hjr : j < suppliedGridTick τ h (i+1)) :
    (suppliedFrozenTable τ B h N)[j]? = some (B i) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [suppliedFrozenTable_succ]
    by_cases hin : i < N
    · have hjN : j < (suppliedFrozenTable τ B h N).length := by
        rw [suppliedFrozenTable_length hτ hτ0 B hh]
        exact hjr.trans_le (suppliedGridTick_mono hτ hh (by omega))
      rw [List.getElem?_append_left hjN]
      exact ih hin
    · have hiN : i = N := by omega
      subst i
      have hl := suppliedFrozenTable_length hτ hτ0 B hh N
      rw [List.getElem?_append_right (by omega), hl]
      apply List.getElem?_replicate_of_lt
      omega

/-- At a uniform-grid time before the final rounded tick, the supplied field equals the
corresponding entry of the frozen table. -/
theorem suppliedGridField_sample {τ : ℕ → ℝ} (hτ : Monotone τ) (hτ0 : τ 0 = 0)
    (B : ℕ → Matrix I I ℂ) {h : ℝ} (hh : 0 < h) (N j : ℕ)
    (hj : j < suppliedGridTick τ h N) :
    suppliedGridField τ B N ((j:ℝ)*h) = (suppliedFrozenTable τ B h N).getD j 0 := by
  obtain ⟨i,hi,hil,hir⟩ := suppliedGridTick_block hτ0 h N j hj
  have hul : τ i ≤ (j:ℝ)*h := (div_le_iff₀ hh).mp (Nat.ceil_le.mp hil)
  have hur : (j:ℝ)*h < τ (i+1) := (lt_div_iff₀ hh).mp (Nat.lt_ceil.mp hir)
  rw [suppliedGridField_on_interval hτ B hi ⟨hul,hur⟩,
    List.getD_eq_getElem?_getD, suppliedFrozenTable_lookup hτ hτ0 B hh N i j hi hil hir]
  rfl

/-- If `τ N = T > 0`, a uniform step `T/M` with positive `M` places the final supplied
breakpoint at exactly tick `M`. -/
theorem suppliedGridTick_horizon {τ : ℕ → ℝ} {N M : ℕ} {T : ℝ}
    (hτN : τ N = T) (hT : 0 < T) (hM : 0 < M) :
    suppliedGridTick τ (T/M) N = M := by
  have hM0 : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have he : τ N / (T/M) = (M:ℝ) := by rw [hτN]; field_simp
  simp [suppliedGridTick, he]

/-- For a monotone supplied grid starting at zero and ending at `T > 0`, the list of its `M`
uniform left-endpoint samples is exactly the frozen table for step `T/M`. -/
theorem suppliedGridField_sample_list {τ : ℕ → ℝ} (hτ : Monotone τ) (hτ0 : τ 0 = 0)
    (B : ℕ → Matrix I I ℂ) (N M : ℕ) {T : ℝ}
    (hτN : τ N = T) (hT : 0 < T) (hM : 0 < M) :
    List.ofFn (fun j : Fin M => suppliedGridField τ B N (T*j.val/M)) =
      suppliedFrozenTable τ B (T/M) N := by
  have hh : 0 < T/(M:ℝ) := div_pos hT (by exact_mod_cast hM)
  have hq := suppliedGridTick_horizon hτN hT hM
  have hl : (suppliedFrozenTable τ B (T/M) N).length = M :=
    (suppliedFrozenTable_length hτ hτ0 B hh N).trans hq
  apply List.ext_getElem?
  intro j
  by_cases hj : j < M
  · obtain ⟨i,hi,hil,hir⟩ := suppliedGridTick_block hτ0 (T/M) N j (by rwa [hq])
    have hs := suppliedGridField_sample hτ hτ0 B hh N j (by rwa [hq])
    have hlook := suppliedFrozenTable_lookup hτ hτ0 B hh N i j hi hil hir
    rw [List.getD_eq_getElem?_getD, hlook] at hs
    simp only [Option.getD_some] at hs
    have ht : T*(j:ℝ)/M = (j:ℝ)*(T/M) := by ring
    simpa only [List.getElem?_ofFn, dite_eq_left hj, ht, hs] using hlook.symm
  · simp only [List.getElem?_ofFn, dite_eq_right hj]
    exact (List.getElem?_eq_none (by omega)).symm

end Matrices
end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
