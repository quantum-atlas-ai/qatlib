/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.EffectiveMeanDerivativeGridErrorStat
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-!
# Dyson error with an integrable derivative

This module proves the three-term truncated Dyson grid error estimate assuming integrability of
the derivative norm. It controls sampled evolution through an interval-integrable derivative and
then combines sampling, Euler, and truncation errors. `effectiveMeanDerivativeGridError`
establishes the resulting contract in the setting of [LowWiebe2018].

## Main statements

* `effectiveMeanDerivativeGridError`: the joint error bound under an integrable derivative-norm
  hypothesis.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.InteractionEvo.DysonGrid
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid.EffectiveMeanDerivativeGridErrorHami
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- For a nonnegative step `h` and norm bound `Λ`, the Euler factor differs from constant
Hamiltonian evolution by at most `exp(Λ h) (Λ h)² / 2`. -/
private theorem dyson_euler_factor_error {I : Type} [Fintype I] [DecidableEq I]
    (B : Matrix I I ℂ) (h Λ : ℝ) (hh : 0 ≤ h) (hΛ : 0 ≤ Λ) (hB : ‖B‖ ≤ Λ) :
    ‖(1 - (h : ℂ) • (Complex.I • B)) - HamiltonianEvolution B h‖ ≤
      Real.exp (Λ * h) * (Λ * h) ^ 2 / 2 := by
  have hb : ∀ u ∈ Set.uIcc (0 : ℝ) h, ‖(fun _ => Complex.I • B) u‖ ≤ Λ := by
    intro u _
    simpa [norm_smul] using! hB
  have ht := dyson_finite_prefix_explicit_factorial_tail I (fun _ => Complex.I • B)
    0 h Λ 1 continuous_const hΛ hb
  have hp : dysonPrefix (fun _ => Complex.I • B) 0 h 1 =
      1 - (h : ℂ) • (Complex.I • B) := by
    simp [dysonPrefix, Finset.sum_range_succ, orderedDysonTerm,
      intervalIntegral.integral_const, sub_eq_add_neg]
    rw [smul_comm]
  rw [hp, orderedEvolution_constant_hamiltonian, sub_zero, norm_sub_rev] at ht
  simpa [abs_of_nonneg hh, Nat.factorial] using! ht

/-- The Euler factor at a nonnegative step `h` has norm at most `exp(Λ h)` when `‖B‖ ≤ Λ`. -/
private theorem dyson_euler_factor_norm {I : Type} [Fintype I] [DecidableEq I]
    (B : Matrix I I ℂ) (h Λ : ℝ) (hh : 0 ≤ h) (hB : ‖B‖ ≤ Λ) :
    ‖1 - (h : ℂ) • (Complex.I • B)‖ ≤ Real.exp (Λ * h) := by
  calc
    _ ≤ ‖(1 : Matrix I I ℂ)‖ + ‖(h : ℂ) • (Complex.I • B)‖ := norm_sub_le _ _
    _ ≤ 1 + h * Λ := by
      rw [norm_smul, norm_smul]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh, Complex.norm_I,
        one_mul]
      exact add_le_add l2_norm_one_le (mul_le_mul_of_nonneg_left hB hh)
    _ ≤ _ := by simpa [add_comm, mul_comm] using! Real.add_one_le_exp (Λ * h)

/-- The ordered product of the first `n` factors, with each new factor multiplied on the left. -/
private noncomputable def dysonLeftProduct {I : Type} [Fintype I] [DecidableEq I]
    (f : ℕ → Matrix I I ℂ) : ℕ → Matrix I I ℂ
  | 0 => 1
  | n + 1 => f n * dysonLeftProduct f n

/-- The recursively defined left product equals the product of the reversed list of its first
`n` factors. -/
private theorem dysonLeftProduct_eq_reverse_prod {I : Type} [Fintype I] [DecidableEq I]
    (f : ℕ → Matrix I I ℂ) (n : ℕ) :
    dysonLeftProduct f n = ((List.ofFn (fun j : Fin n => f j.val)).reverse).prod := by
  induction n with
  | zero => simp [dysonLeftProduct]
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.prod_cons]
    simp only [Fin.val_last, Fin.val_castSucc]
    rw [dysonLeftProduct, ih]

/-- The recursively defined left product equals the reverse product of `f` mapped over
`List.range n`. -/
private theorem dysonLeftProduct_eq_range_prod {I : Type} [Fintype I] [DecidableEq I]
    (f : ℕ → Matrix I I ℂ) (n : ℕ) :
    dysonLeftProduct f n = (((List.range n).map f).reverse).prod := by
  induction n with
  | zero => simp [dysonLeftProduct]
  | succ n ih => simp [List.range_succ, dysonLeftProduct, ih]

/-- Clamp a real number to the interval with endpoints zero and `t` by taking `max 0 (min t u)`. -/
private def dysonClip (t u : ℝ) : ℝ := max 0 (min t u)

/-- For nonnegative `t`, clamping any real number produces a point of `[0, t]`. -/
private theorem dysonClip_mem (t : ℝ) (ht : 0 ≤ t) (u : ℝ) :
    dysonClip t u ∈ Set.Icc 0 t :=
  ⟨le_max_left _ _, max_le ht (min_le_left _ _)⟩

/-- Clamping fixes every point already in `[0, t]`. -/
private theorem dysonClip_eq {t u : ℝ} (hu : u ∈ Set.Icc 0 t) : dysonClip t u = u := by
  simp [dysonClip, min_eq_right hu.2, max_eq_right hu.1]

/-- Matrix fields agreeing on `[0, t]` have equal ordered evolutions from zero to nonnegative
time `t`. -/
private theorem dyson_interval_evolution_congr {I : Type} [Fintype I] [DecidableEq I]
    (A B : ℝ → Matrix I I ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hAB : ∀ u ∈ Set.Icc 0 t, A u = B u) :
    orderedEvolution A 0 t = orderedEvolution B 0 t := by
  have hterm (n : ℕ) : ∀ u ∈ Set.Icc 0 t,
      orderedDysonTerm A 0 n u = orderedDysonTerm B 0 n u := by
    induction n with
    | zero => intro u _; rfl
    | succ n ih =>
      intro u hu
      simp only [orderedDysonTerm]
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le hu.1] at hv
      have hvT : v ∈ Set.Icc 0 t := ⟨hv.1, hv.2.trans hu.2⟩
      (try dsimp only)
      rw [hAB v hvT, ih v hvT]
  unfold orderedEvolution
  exact tsum_congr (fun n => hterm n t ⟨ht, le_rfl⟩)

/-- If one factor family is bounded by `B ≥ 1`, the other by one, and their differences by `B
d`, their length-`M` left products differ by at most `M B^M d`. -/
private theorem dysonLeftProduct_perturbation {I : Type} [Fintype I] [DecidableEq I]
    (f g : ℕ → Matrix I I ℂ) (B d : ℝ) (M : ℕ) (hB : 1 ≤ B) (hd : 0 ≤ d)
    (hf : ∀ j < M, ‖f j‖ ≤ B) (hg : ∀ j < M, ‖g j‖ ≤ 1)
    (hfg : ∀ j < M, ‖f j - g j‖ ≤ B * d) :
    ‖dysonLeftProduct f M - dysonLeftProduct g M‖ ≤ (M : ℝ) * B ^ M * d := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hgn (n : ℕ) (hn : n ≤ M) : ‖dysonLeftProduct g n‖ ≤ 1 := by
    induction n with
    | zero => exact l2_norm_one_le
    | succ n ih =>
      have hnM : n < M := by omega
      calc
        _ ≤ ‖g n‖ * ‖dysonLeftProduct g n‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul (hg n hnM) (ih (by omega)) (norm_nonneg _)
          (by norm_num)
        _ = 1 := one_mul _
  have herr (n : ℕ) (hn : n ≤ M) :
      ‖dysonLeftProduct f n - dysonLeftProduct g n‖ ≤ (n : ℝ) * B ^ n * d := by
    induction n with
    | zero => simp [dysonLeftProduct]
    | succ n ih =>
      have hnM : n < M := by omega
      have he : dysonLeftProduct f (n + 1) - dysonLeftProduct g (n + 1) =
          f n * (dysonLeftProduct f n - dysonLeftProduct g n) +
            (f n - g n) * dysonLeftProduct g n := by
        simp only [dysonLeftProduct]
        noncomm_ring
      have hpow : B ≤ B ^ (n + 1) := by
        rw [pow_succ]
        have hpn : 1 ≤ B ^ n := one_le_pow₀ hB
        nlinarith
      rw [he]
      calc
        _ ≤ ‖f n * (dysonLeftProduct f n - dysonLeftProduct g n)‖ +
            ‖(f n - g n) * dysonLeftProduct g n‖ := norm_add_le _ _
        _ ≤ B * ((n : ℝ) * B ^ n * d) + B * d := by
          apply add_le_add
          · exact (norm_mul_le _ _).trans
              (mul_le_mul (hf n hnM) (ih (by omega)) (norm_nonneg _) hB0)
          · exact (norm_mul_le _ _).trans
              ((mul_le_mul (hfg n hnM) (hgn n (by omega)) (norm_nonneg _)
                (by positivity)).trans_eq (mul_one _))
        _ = (n : ℝ) * B ^ (n + 1) * d + B * d := by rw [pow_succ]; ring
        _ ≤ (n : ℝ) * B ^ (n + 1) * d + B ^ (n + 1) * d := by
          gcongr
        _ = ((n + 1 : ℕ) : ℝ) * B ^ (n + 1) * d := by push_cast; ring
  exact herr M le_rfl

/-- The time derivative of constant Hamiltonian evolution is left multiplication by `-i H`. -/
private theorem ordered_hamiltonian_deriv {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (t : ℝ) :
    HasDerivAt (HamiltonianEvolution H) (-(Complex.I • H * HamiltonianEvolution H t)) t := by
  have he : (fun u : ℝ => NormedSpace.exp (u • (-Complex.I • H))) = HamiltonianEvolution H := by
    funext u
    unfold HamiltonianEvolution
    congr 1
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
    ring
  have hd := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-Complex.I • H) t
  rw [congrFun he t] at hd
  rw [he] at hd
  simpa [neg_smul, neg_mul] using! hd

/-- A continuous Hermitian field varying by at most `D` from its left-endpoint value on `[a, b]`
has frozen-evolution error at most `(b - a) D`. -/
private theorem dyson_mean_local_error {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (hH : Continuous H) (hHerm : ∀ u, (H u).IsHermitian)
    (a b D : ℝ) (hab : a ≤ b)
    (hvar : ∀ u ∈ Set.Icc a b, ‖H u-H a‖ ≤ D) :
    ‖HamiltonianEvolution (H a) (b-a)-orderedEvolution (fun u => Complex.I • H u) a b‖ ≤
      (b-a)*D := by
  let A := fun u => Complex.I • H u
  let U := fun u => HamiltonianEvolution (H a) (u-a)
  let F := fun u => orderedEvolution A u b * U u - orderedEvolution A a b
  let d := fun u => orderedEvolution A u b * (Complex.I • (H u-H a)) * U u
  have hA : Continuous A := by dsimp [A]; fun_prop
  have hU (u : ℝ) : HasDerivAt U (-(Complex.I • H a * U u)) u := by
    simpa [U] using! (ordered_hamiltonian_deriv (H a) (u-a)).scomp u ((hasDerivAt_id u).sub_const a)
  have hd (u : ℝ) : HasDerivAt F (d u) u := by
    convert! ((orderedEvolution_hasDerivAt_start A hA b u).mul (hU u)).sub_const
      (orderedEvolution A a b) using 1
    dsimp [F, d, A]
    simp only [smul_sub, Matrix.mul_sub, Matrix.sub_mul, mul_neg]
    noncomm_ring
  have hn (u : ℝ) (hu : u ∈ Set.Ico a b) : ‖d u‖ ≤ D := by
    have hE := l2_norm_unitary_le_one (ordered_evolution_hermitian_unitary I H hH hHerm u b)
    have hU' := l2_norm_unitary_le_one (hamiltonianEvolution_unitary (hHerm a) (u-a))
    calc
      _ ≤ ‖orderedEvolution A u b‖ * ‖Complex.I • (H u-H a)‖ * ‖U u‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1*‖Complex.I • (H u-H a)‖*1 := by gcongr
      _ = ‖H u-H a‖ := by simp [norm_smul]
      _ ≤ D := hvar u ⟨hu.1, hu.2.le⟩
  have hbnd := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := F) (f' := d) (B := fun u => D*(u-a)) (B' := fun _ => D)
    (fun u _ => (hd u).continuousAt.continuousWithinAt)
    (fun u _ => (hd u).hasDerivWithinAt) (by simp [F, U])
    (fun u => (by simpa using! ((hasDerivAt_id u).sub_const a).const_mul D)) hn
  simpa [F, U, mul_comm] using! hbnd (Set.right_mem_Icc.mpr hab)

/-- With an interval-integrable derivative and the stated Hermitian and continuity hypotheses,
the sampled evolution product has error at most `(T / M) ∫₀ᵀ ‖Hd u‖`. -/
private theorem sampled_grid_integrable_derivative_error :
∀ (I : Type) [Fintype I] [DecidableEq I] (H Hd : ℝ → Matrix I I ℂ) (T : ℝ) (M : ℕ),
    Continuous H → 0 ≤ T → 0 < M →
    (∀ u ∈ Set.Icc 0 T, (H u).IsHermitian) →
    IntervalIntegrable Hd MeasureTheory.volume 0 T → (∀ u ∈ Set.Icc 0 T, HasDerivAt H (Hd u) u) →
    ‖sampledEvolutionProduct H T M -
        orderedEvolution (fun u => Complex.I • H u) 0 T‖ ≤
      (T / M) * ∫ u in (0 : ℝ)..T, ‖Hd u‖ := by
  intro I _ _ H Hd T M hH hT hM hHerm hHd hderiv
  let G : ℝ → Matrix I I ℂ := fun u => H (dysonClip T u)
  have hG : Continuous G := by dsimp [G, dysonClip]; fun_prop
  have hGe (u : ℝ) (hu : u ∈ Set.Icc 0 T) : G u = H u := by
    dsimp only [G]
    rw [dysonClip_eq hu]
  have hGHerm (u : ℝ) : (G u).IsHermitian := hHerm _ (dysonClip_mem T hT u)
  let h : ℝ := T/M
  let A : ℝ → Matrix I I ℂ := fun u => Complex.I • G u
  let f : ℕ → Matrix I I ℂ := fun n => HamiltonianEvolution (G ((n : ℝ)*h)) h
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hh : 0 ≤ h := div_nonneg hT hMr.le
  have hMh : (M : ℝ)*h = T := by dsimp [h]; field_simp
  have hmem (n : ℕ) (hn : n ≤ M) : (n : ℝ)*h ∈ Set.Icc 0 T := by
    refine ⟨mul_nonneg (Nat.cast_nonneg n) hh, ?_⟩
    have hn' : (n : ℝ) ≤ M := by exact_mod_cast hn
    exact (mul_le_mul_of_nonneg_right hn' hh).trans_eq hMh
  have herr (n : ℕ) (hn : n ≤ M) :
      ‖dysonLeftProduct f n-orderedEvolution A 0 ((n : ℝ)*h)‖ ≤
        h * ∫ u in (0 : ℝ)..((n : ℝ)*h), ‖Hd u‖ := by
    induction n with
    | zero => simp [dysonLeftProduct]
    | succ n ih =>
      have hn0 : n ≤ M := by omega
      have hi := ih hn0
      let a := (n : ℝ)*h
      let b := ((n+1 : ℕ) : ℝ)*h
      have ha := hmem n hn0
      have hb := hmem (n+1) hn
      have heh : b-a = h := by dsimp [a, b]; push_cast; ring
      have hab : a ≤ b := by linarith
      have hvar (u : ℝ) (hu : u ∈ Set.Icc a b) :
          ‖G u-G a‖ ≤ ∫ v in a..b, ‖Hd v‖ := by
        have huT : u ∈ Set.Icc 0 T := ⟨ha.1.trans hu.1, hu.2.trans hb.2⟩
        rw [hGe u huT, hGe a ha]
        have hFTC : (∫ v in a..u, Hd v) = H u-H a := by
          apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          · intro v hv
            rw [Set.uIcc_of_le hu.1] at hv
            exact hderiv v ⟨ha.1.trans hv.1, hv.2.trans huT.2⟩
          · exact hHd.mono_set
              (by rw [Set.uIcc_of_le hu.1, Set.uIcc_of_le hT]; exact Set.Icc_subset_Icc ha.1 huT.2)
        rw [← hFTC]
        exact (intervalIntegral.norm_integral_le_integral_norm hu.1).trans
          (intervalIntegral.integral_mono_interval le_rfl hu.1 hu.2
            (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) ((hHd.mono_set (by rw [Set.uIcc_of_le hab, Set.uIcc_of_le hT]; exact Set.Icc_subset_Icc ha.1 hb.2)).norm))
      have hloc := dyson_mean_local_error G hG hGHerm a b
        (∫ u in a..b, ‖Hd u‖) hab hvar
      rw [heh] at hloc
      let U := HamiltonianEvolution (G a) h
      let E := orderedEvolution A a b
      let P := dysonLeftProduct f n
      let Q := orderedEvolution A 0 a
      have hU : ‖U‖ ≤ 1 := l2_norm_unitary_le_one (hamiltonianEvolution_unitary (hGHerm a) h)
      have hQ : ‖Q‖ ≤ 1 :=
          l2_norm_unitary_le_one (ordered_evolution_hermitian_unitary I G hG hGHerm 0 a)
      have hA : Continuous A := by dsimp [A]; fun_prop
      have he : dysonLeftProduct f (n+1)-orderedEvolution A 0 b = U*(P-Q)+(U-E)*Q := by
        rw [dysonLeftProduct, ← orderedEvolution_cocycle A hA 0 a b]
        dsimp [U, P, Q, E, f, a]
        noncomm_ring
      rw [he]
      calc
        _ ≤ ‖U*(P-Q)‖+‖(U-E)*Q‖ := norm_add_le _ _
        _ ≤ ‖P-Q‖+‖U-E‖ := by
          apply add_le_add
          · exact (norm_mul_le _ _).trans
              ((mul_le_mul_of_nonneg_right hU (norm_nonneg _)).trans_eq (one_mul _))
          · exact (norm_mul_le _ _).trans
              ((mul_le_mul_of_nonneg_left hQ (norm_nonneg _)).trans_eq (mul_one _))
        _ ≤ h*(∫ u in (0 : ℝ)..a, ‖Hd u‖)+h*(∫ u in a..b, ‖Hd u‖) := add_le_add hi hloc
        _ = _ := by
          rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals
            ((hHd.mono_set (by rw [Set.uIcc_of_le ha.1, Set.uIcc_of_le hT]; exact Set.Icc_subset_Icc le_rfl ha.2)).norm) ((hHd.mono_set (by rw [Set.uIcc_of_le hab, Set.uIcc_of_le hT]; exact Set.Icc_subset_Icc ha.1 hb.2)).norm)]
  have hn := herr M le_rfl
  rw [hMh] at hn
  have hprod : dysonLeftProduct f M = sampledEvolutionProduct H T M := by
    rw [dysonLeftProduct_eq_reverse_prod]
    unfold sampledEvolutionProduct
    congr 2
    apply congrArg List.ofFn
    funext j
    have hj : (j.val : ℝ)*h ∈ Set.Icc 0 T := hmem j.val j.isLt.le
    have htime : T*j.val/M = (j.val : ℝ)*h := by dsimp [h]; ring
    dsimp only [f]
    rw [htime, hGe _ hj]
  have hsame : orderedEvolution A 0 T = orderedEvolution (fun u => Complex.I • H u) 0 T := by
    apply dyson_interval_evolution_congr A (fun u => Complex.I • H u) T hT
    intro u hu
    dsimp only [A]
    rw [hGe u hu]
  rwa [hprod, hsame] at hn

/-- A bounded continuous Hermitian field with an interval-integrable derivative has Euler grid
error at most `exp(Λ t) Λ² t² / (2 M) + (t / M) ∫₀ᵗ ‖Hd u‖` under the stated time and grid
hypotheses. -/
private theorem dyson_grid_integrable_derivative_error :
∀ (I : Type) [Fintype I] [DecidableEq I] (H Hd : ℝ → Matrix I I ℂ) (t Λ : ℝ) (M : ℕ),
    Continuous H → 0 ≤ t → 0 ≤ Λ → 0 < M →
    (∀ u ∈ Set.Icc 0 t, (H u).IsHermitian ∧ ‖H u‖ ≤ Λ) →
    IntervalIntegrable Hd MeasureTheory.volume 0 t → (∀ u ∈ Set.Icc 0 t, HasDerivAt H (Hd u) u) →
    ‖dysonGridRun H t M - orderedEvolution (fun u => Complex.I • H u) 0 t‖ ≤
      Real.exp (Λ * t) * Λ ^ 2 * t ^ 2 / (2 * M)
        + (t / M) * ∫ u in (0 : ℝ)..t, ‖Hd u‖ := by
  intro I _ _ H Hd t Λ M hH ht hΛ hM hbound hHd hderiv
  let h : ℝ := t/M
  let c := Λ*h
  let d := c^2/2
  let B := Real.exp c
  let f := fun j : ℕ => 1-(h : ℂ) • (Complex.I • H ((j : ℝ)*h))
  let g := fun j : ℕ => HamiltonianEvolution (H ((j : ℝ)*h)) h
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hh : 0 ≤ h := div_nonneg ht (Nat.cast_nonneg M)
  have hc : 0 ≤ c := mul_nonneg hΛ hh
  have hmem (j : ℕ) (hj : j < M) : (j : ℝ)*h ∈ Set.Icc 0 t := by
    refine ⟨mul_nonneg (Nat.cast_nonneg j) hh, ?_⟩
    have hj' : (j : ℝ) ≤ M := by exact_mod_cast hj.le
    calc
      (j : ℝ)*h ≤ (M : ℝ)*h := mul_le_mul_of_nonneg_right hj' hh
      _ = t := by dsimp [h]; field_simp
  have hrun : dysonGridRun H t M = dysonLeftProduct f M := by
    rw [dysonLeftProduct_eq_reverse_prod]
    unfold dysonGridRun
    congr 3
    funext j
    simp only [dysonGridStep, f, h]
    rw [mul_comm t (j.val : ℝ), mul_div_assoc]
  have hp := dysonLeftProduct_perturbation f g B d M (Real.one_le_exp hc)
    (by positivity) (fun j hj => dyson_euler_factor_norm _ h Λ hh (hbound _ (hmem j hj)).2)
    (fun j hj => l2_norm_unitary_le_one (hamiltonianEvolution_unitary
      (hbound _ (hmem j hj)).1 h))
    (fun j hj => by simpa [B, d, c, mul_div_assoc] using!
      dyson_euler_factor_error (H ((j : ℝ)*h)) h Λ hh hΛ (hbound _ (hmem j hj)).2)
  have hs := sampled_grid_integrable_derivative_error I H Hd t M hH ht hM
    (fun u hu => (hbound u hu).1) hHd hderiv
  have hsample : sampledEvolutionProduct H t M = dysonLeftProduct g M := by
    rw [dysonLeftProduct_eq_reverse_prod]
    unfold sampledEvolutionProduct
    congr 3
    funext j
    dsimp only [g, h]
    rw [mul_comm t (j.val : ℝ), mul_div_assoc]
  rw [hsample] at hs
  have hBpow : B^M = Real.exp (Λ*t) := by
    dsimp [B]
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [c, h]
    field_simp
  have hpoly : (M : ℝ)*B^M*d = Real.exp (Λ*t)*Λ^2*t^2/(2*M) := by
    rw [hBpow]
    dsimp [d, c, h]
    field_simp
  rw [hrun]
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (by simpa only [hpoly] using! add_le_add hp hs)

/-- The truncated strict Dyson grid satisfies the three-term operator error contract when the
derivative norm is interval integrable. This gives an integrable-derivative version of the
estimate in [Low and Wiebe, Lemma 5][LowWiebe2018]. -/
theorem effectiveMeanDerivativeGridError : EffectiveMeanDerivativeGridError := by
  intro I _ _ H Hd t alpha M K hH hint hderiv ht ha hM hbound hlog
  have hm : MeasureTheory.AEStronglyMeasurable Hd
      (MeasureTheory.volume.restrict (Set.uIoc 0 t)) := by
    apply (aestronglyMeasurable_deriv H _).congr
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with u hu
    rw [Set.uIoc_of_le ht] at hu
    exact (hderiv u ⟨hu.1.le,hu.2⟩).deriv
  have hdi := (IntervalIntegrable.intervalIntegrable_norm_iff hm).mp hint
  have he := dyson_grid_integrable_derivative_error I H Hd t alpha M
    hH ht ha hM hbound hdi hderiv
  have htail := dyson_grid_truncation_factorial_tail I H t alpha M K ht ha hM
    (fun u hu => (hbound u hu).2) hlog
  exact (norm_sub_le_norm_sub_add_norm_sub _ (dysonGridRun H t M) _).trans
    ((add_le_add htail he).trans_eq (by ring))

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid.EffectiveMeanDerivativeGridErrorHami
