/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.DysonGrid.DysonTruncationGridConsumers
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.InteractionEvo.DysonGrid
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

noncomputable def sampledEvolutionProduct {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (T : ℝ) (M : ℕ) : Matrix I I ℂ :=
  ((List.ofFn (fun j : Fin M => HamiltonianEvolution (H (T * j.val / M)) (T / M))).reverse).prod

noncomputable def dysonGridDegreeSum {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) : Matrix I I ℂ :=
  ((((List.ofFn (fun j : Fin M =>
    -((t / (M : ℝ) : ℝ) : ℂ) • (Complex.I • H (t * j.val / M))))).reverse.sublistsLen k).map
      List.prod).sum

noncomputable def dysonGridTruncatedSum {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M K : ℕ) : Matrix I I ℂ :=
  ∑ k ∈ Finset.range (K + 1), dysonGridDegreeSum H t M k

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

private noncomputable def dysonLeftProduct {I : Type} [Fintype I] [DecidableEq I]
    (f : ℕ → Matrix I I ℂ) : ℕ → Matrix I I ℂ
  | 0 => 1
  | n + 1 => f n * dysonLeftProduct f n

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

private theorem dysonLeftProduct_eq_range_prod {I : Type} [Fintype I] [DecidableEq I]
    (f : ℕ → Matrix I I ℂ) (n : ℕ) :
    dysonLeftProduct f n = (((List.range n).map f).reverse).prod := by
  induction n with
  | zero => simp [dysonLeftProduct]
  | succ n ih => simp [List.range_succ, dysonLeftProduct, ih]

private def dysonClip (t u : ℝ) : ℝ := max 0 (min t u)

private theorem dysonClip_mem (t : ℝ) (ht : 0 ≤ t) (u : ℝ) :
    dysonClip t u ∈ Set.Icc 0 t :=
  ⟨le_max_left _ _, max_le ht (min_le_left _ _)⟩

private theorem dysonClip_eq {t u : ℝ} (hu : u ∈ Set.Icc 0 t) : dysonClip t u = u := by
  simp [dysonClip, min_eq_right hu.2, max_eq_right hu.1]

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

theorem sampled_grid_mean_derivative_error :
∀ (I : Type) [Fintype I] [DecidableEq I] (H Hd : ℝ → Matrix I I ℂ) (T : ℝ) (M : ℕ),
    Continuous H → 0 ≤ T → 0 < M →
    (∀ u ∈ Set.Icc 0 T, (H u).IsHermitian) →
    Continuous Hd → (∀ u ∈ Set.Icc 0 T, HasDerivAt H (Hd u) u) →
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
          · exact hHd.intervalIntegrable a u
        rw [← hFTC]
        exact (intervalIntegral.norm_integral_le_integral_norm hu.1).trans
          (intervalIntegral.integral_mono_interval le_rfl hu.1 hu.2
            (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) (hHd.norm.intervalIntegrable a b))
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
      have he : dysonLeftProduct f (n+1)-orderedEvolution A 0 b = U*(P-Q)+(U-E)*Q := by
        rw [dysonLeftProduct, ← orderedEvolution_cocycle A (by dsimp [A]; fun_prop) 0 a b]
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
            (hHd.norm.intervalIntegrable 0 a) (hHd.norm.intervalIntegrable a b)]
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

theorem dyson_grid_mean_derivative_error :
∀ (I : Type) [Fintype I] [DecidableEq I] (H Hd : ℝ → Matrix I I ℂ) (t Λ : ℝ) (M : ℕ),
    Continuous H → 0 ≤ t → 0 ≤ Λ → 0 < M →
    (∀ u ∈ Set.Icc 0 t, (H u).IsHermitian ∧ ‖H u‖ ≤ Λ) →
    Continuous Hd → (∀ u ∈ Set.Icc 0 t, HasDerivAt H (Hd u) u) →
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
  have hs := sampled_grid_mean_derivative_error I H Hd t M hH ht hM
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

private theorem dyson_mean_list_product_bound {I : Type} [Fintype I] [DecidableEq I]
    (l : List (Matrix I I ℂ)) (B : ℝ) (hB : 0 ≤ B) (hl : ∀ a ∈ l, ‖a‖ ≤ B) :
    ‖l.prod‖ ≤ B^l.length := by
  induction l with
  | nil => simpa using! (l2_norm_one_le (I := I))
  | cons a l ih =>
    simp only [List.prod_cons, List.length_cons, pow_succ]
    refine (norm_mul_le _ _).trans ?_
    have ht := ih (fun x hx => hl x (List.mem_cons_of_mem a hx))
    simpa only [mul_comm] using! mul_le_mul (hl a List.mem_cons_self) ht (norm_nonneg _) hB

private theorem dyson_mean_list_sum_bound {I : Type} [Fintype I] [DecidableEq I]
    (l : List (Matrix I I ℂ)) (D : ℝ) (hl : ∀ a ∈ l, ‖a‖ ≤ D) :
    ‖l.sum‖ ≤ (l.length : ℝ)*D := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    exact (norm_add_le _ _).trans (by
      have ht := ih (fun x hx => hl x (List.mem_cons_of_mem a hx))
      have hh := hl a List.mem_cons_self
      nlinarith)

private theorem dyson_mean_range_sum {I : Type} [Fintype I] [DecidableEq I]
    (f : ℕ → Matrix I I ℂ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

private theorem dyson_mean_flatmap_sum {I : Type} [Fintype I] [DecidableEq I]
    {α : Type*} (l : List α) (f : α → List (Matrix I I ℂ)) :
    (l.flatMap f).sum = (l.map (fun a => (f a).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private theorem dyson_mean_sum_by_degree {I : Type} [Fintype I] [DecidableEq I]
    (l : List (Matrix I I ℂ)) :
    ((l.sublists).map List.prod).sum =
      ∑ k ∈ Finset.range (l.length+1), ((l.sublistsLen k).map List.prod).sum := by
  have hp := (List.range_bind_sublistsLen_perm l).trans (List.sublists_perm_sublists' l).symm
  rw [← (hp.map List.prod).sum_eq]
  rw [List.map_flatMap, dyson_mean_flatmap_sum, dyson_mean_range_sum]

private theorem dyson_mean_degree_bound {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t Λ : ℝ) (M k : ℕ)
    (ht : 0 ≤ t) (hΛ : 0 ≤ Λ) (hM : 0 < M)
    (hbound : ∀ u ∈ Set.Icc 0 t, ‖H u‖ ≤ Λ) :
    ‖dysonGridDegreeSum H t M k‖ ≤ (Λ*t)^k/(k.factorial : ℝ) := by
  let h : ℝ := t/M
  let l := (List.ofFn (fun j : Fin M =>
    -(h : ℂ) • (Complex.I • H (t*j.val/M)))).reverse
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hh : 0 ≤ h := div_nonneg ht hMr.le
  have hinc : ∀ a ∈ l, ‖a‖ ≤ Λ*h := by
    intro a ha
    dsimp only [l] at ha
    rw [List.mem_reverse] at ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    have hj : t*j.val/M ∈ Set.Icc (0 : ℝ) t := by
      refine ⟨by positivity, ?_⟩
      rw [div_le_iff₀ hMr]
      have hj' : (j.val : ℝ) ≤ M := by exact_mod_cast j.isLt.le
      nlinarith
    simp only [norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh,
      Complex.norm_I, one_mul]
    simpa only [mul_comm] using! mul_le_mul_of_nonneg_left (hbound _ hj) hh
  have hw (w : List (Matrix I I ℂ)) (hw : w ∈ l.sublistsLen k) : ‖w.prod‖ ≤ (Λ*h)^k := by
    have hs := (List.mem_sublistsLen.mp hw).1
    have hn := (List.mem_sublistsLen.mp hw).2
    simpa only [hn] using! dyson_mean_list_product_bound w (Λ*h) (mul_nonneg hΛ hh)
      (fun a ha => hinc a (hs.subset ha))
  have hsum : ‖((l.sublistsLen k).map List.prod).sum‖ ≤
      (M.choose k : ℝ)*(Λ*h)^k := by
    have hs := dyson_mean_list_sum_bound ((l.sublistsLen k).map List.prod) ((Λ*h)^k) (by
      intro a ha
      obtain ⟨w, hw', rfl⟩ := List.mem_map.mp ha
      exact hw w hw')
    simpa only [List.length_map, List.length_sublistsLen, l, List.length_reverse,
      List.length_ofFn] using! hs
  have hchoose : (M.choose k : ℝ)*(k.factorial : ℝ) ≤ (M : ℝ)^k := by
    have hc := Nat.descFactorial_le_pow M k
    rw [Nat.descFactorial_eq_factorial_mul_choose] at hc
    exact_mod_cast (by simpa only [Nat.mul_comm] using! hc)
  change ‖((l.sublistsLen k).map List.prod).sum‖ ≤ _
  refine hsum.trans ?_
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < k.factorial)).mpr
  calc
    (M.choose k : ℝ)*(Λ*h)^k*(k.factorial : ℝ) =
        ((M.choose k : ℝ)*(k.factorial : ℝ))*(Λ*h)^k := by ring
    _ ≤ (M : ℝ)^k*(Λ*h)^k := mul_le_mul_of_nonneg_right hchoose (pow_nonneg (mul_nonneg hΛ hh) k)
    _ = (Λ*t)^k := by
      rw [← mul_pow]
      congr 1
      dsimp [h]
      field_simp

private theorem dyson_mean_factorial_tail (a : ℝ) (ha : 0 ≤ a) (hlog : a ≤ Real.log 2)
    (K L : ℕ) :
    (∑ n ∈ Finset.range L, a^(K+1+n)/((K+1+n).factorial : ℝ)) ≤
      2*a^(K+1)/((K+1).factorial : ℝ) := by
  let k := K+1
  have hmajorant (n : ℕ) : a^(k+n)/((k+n).factorial : ℝ) ≤
      (a^k/(k.factorial : ℝ)) * (a^n/(n.factorial : ℝ)) := by
    have hd : (n.factorial : ℝ)*(k.factorial : ℝ) ≤ ((k+n).factorial : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (k+n))
        (by simpa only [Nat.add_comm] using! Nat.factorial_mul_factorial_dvd_factorial_add n k)
    calc
      _ ≤ a^(k+n)/((n.factorial : ℝ)*(k.factorial : ℝ)) :=
        div_le_div_of_nonneg_left (pow_nonneg ha _) (by positivity) hd
      _ = _ := by rw [pow_add]; ring
  have hs : Summable (fun n : ℕ =>
      (a^k/(k.factorial : ℝ)) * (a^n/(n.factorial : ℝ))) :=
    (Real.summable_pow_div_factorial a).mul_left _
  calc
    _ ≤ ∑ n ∈ Finset.range L, (a^k/(k.factorial : ℝ)) * (a^n/(n.factorial : ℝ)) :=
      Finset.sum_le_sum (fun n _ => hmajorant n)
    _ ≤ ∑' n : ℕ, (a^k/(k.factorial : ℝ)) * (a^n/(n.factorial : ℝ)) :=
      hs.sum_le_tsum _ (fun _ _ => by positivity)
    _ = (a^k/(k.factorial : ℝ))*Real.exp a := by
      rw [tsum_mul_left, ← congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)) a,
        ← Real.exp_eq_exp_ℝ]
    _ ≤ (a^k/(k.factorial : ℝ))*2 := by
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      have he := Real.exp_le_exp.mpr hlog
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
      exact he
    _ = _ := by dsimp [k]; ring

theorem dyson_grid_truncation_factorial_tail :
∀ (I : Type) [Fintype I] [DecidableEq I] (H : ℝ → Matrix I I ℂ) (t Λ : ℝ) (M K : ℕ),
    0 ≤ t → 0 ≤ Λ → 0 < M →
    (∀ u ∈ Set.Icc 0 t, ‖H u‖ ≤ Λ) → Λ * t ≤ Real.log 2 →
    ‖dysonGridTruncatedSum H t M K - dysonGridRun H t M‖ ≤
      (2 : ℝ) * (Λ * t) ^ (K + 1) / (Nat.factorial (K + 1) : ℝ) := by
  intro I _ _ H t Λ M K ht hΛ hM hbound hlog
  have hfull : dysonGridRun H t M =
      ∑ k ∈ Finset.range (M+1), dysonGridDegreeSum H t M k := by
    rw [dyson_grid_strict_subset_expansion, dyson_mean_sum_by_degree]
    simp only [List.length_reverse, List.length_ofFn, dysonGridDegreeSum]
  have hzero (k : ℕ) (hk : M < k) : dysonGridDegreeSum H t M k = 0 := by
    unfold dysonGridDegreeSum
    rw [List.sublistsLen_of_length_lt (by simpa only [List.length_reverse, List.length_ofFn] using! hk)]
    simp
  by_cases hKM : M ≤ K
  · have he : dysonGridTruncatedSum H t M K = dysonGridRun H t M := by
      rw [hfull, dysonGridTruncatedSum]
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k _ hk
      exact hzero k (by simp only [Finset.mem_range] at hk; omega)
    rw [he, sub_self, norm_zero]
    positivity
  · have hle : K+1 ≤ M+1 := by omega
    calc
      _ = ‖∑ k ∈ Finset.Ico (K+1) (M+1), dysonGridDegreeSum H t M k‖ := by
        rw [norm_sub_rev, hfull, dysonGridTruncatedSum, Finset.sum_Ico_eq_sub _ hle]
      _ ≤ ∑ k ∈ Finset.Ico (K+1) (M+1), ‖dysonGridDegreeSum H t M k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.Ico (K+1) (M+1), (Λ*t)^k/(k.factorial : ℝ) :=
        Finset.sum_le_sum (fun k _ => dyson_mean_degree_bound H t Λ M k ht hΛ hM hbound)
      _ = ∑ n ∈ Finset.range (M-K), (Λ*t)^(K+1+n)/((K+1+n).factorial : ℝ) := by
        rw [Finset.sum_Ico_eq_sum_range, show M+1-(K+1) = M-K by omega]
      _ ≤ _ := dyson_mean_factorial_tail (Λ*t) (mul_nonneg hΛ ht) hlog K (M-K)

theorem dyson_truncated_grid_three_term_error :
∀ (I : Type) [Fintype I] [DecidableEq I] (H Hd : ℝ → Matrix I I ℂ) (t Λ : ℝ) (M K : ℕ),
    Continuous H → 0 ≤ t → 0 ≤ Λ → 0 < M →
    (∀ u ∈ Set.Icc 0 t, (H u).IsHermitian ∧ ‖H u‖ ≤ Λ) →
    Continuous Hd → (∀ u ∈ Set.Icc 0 t, HasDerivAt H (Hd u) u) →
    Λ * t ≤ Real.log 2 →
    ‖dysonGridTruncatedSum H t M K -
        orderedEvolution (fun u => Complex.I • H u) 0 t‖ ≤
      Real.exp (Λ * t) * Λ ^ 2 * t ^ 2 / (2 * M)
        + (t / M) * (∫ u in (0 : ℝ)..t, ‖Hd u‖)
        + (2 : ℝ) * (Λ * t) ^ (K + 1) / (Nat.factorial (K + 1) : ℝ) := by
  intro I _ _ H Hd t Λ M K hH ht hΛ hM hbound hHd hderiv hlog
  have he := dyson_grid_mean_derivative_error I H Hd t Λ M hH ht hΛ hM hbound hHd hderiv
  have ht' := dyson_grid_truncation_factorial_tail I H t Λ M K ht hΛ hM
    (fun u hu => (hbound u hu).2) hlog
  exact (norm_sub_le_norm_sub_add_norm_sub (dysonGridTruncatedSum H t M K)
    (dysonGridRun H t M) (orderedEvolution (fun u => Complex.I • H u) 0 t)).trans
    ((add_le_add ht' he).trans_eq (by ring))

theorem dyson_truncated_grid_joint_error :
∀ (I : Type) [Fintype I] [DecidableEq I] (H Hd : ℝ → Matrix I I ℂ) (t Λ : ℝ) (M K : ℕ),
    Continuous H → 0 ≤ t → 0 ≤ Λ → 0 < M →
    (∀ u ∈ Set.Icc 0 t, (H u).IsHermitian ∧ ‖H u‖ ≤ Λ) →
    Continuous Hd → (∀ u ∈ Set.Icc 0 t, HasDerivAt H (Hd u) u) →
    Λ * t ≤ Real.log 2 →
    ‖dysonGridTruncatedSum H t M K -
        orderedEvolution (fun u => Complex.I • H u) 0 t‖ ≤
      Real.exp (Λ * t) * Λ ^ 2 * t ^ 2 / (2 * M)
        + (t / M) * (∫ u in (0 : ℝ)..t, ‖Hd u‖)
        + (2 : ℝ) * (Λ * t) ^ (K + 1) / (Nat.factorial (K + 1) : ℝ) := dyson_truncated_grid_three_term_error

private theorem dyson_mean_scalar_exp (z : ℂ) :
    NormedSpace.exp (z • (1 : Matrix (Fin 1) (Fin 1) ℂ)) = Complex.exp z • 1 := by
  have he := NormedSpace.map_exp (algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ))
    (continuous_algebraMap _ _) z
  simpa only [Algebra.algebraMap_eq_smul_one, Complex.exp_eq_exp_ℂ] using! he.symm
set_option maxHeartbeats 1200000 in

theorem dyson_unparenthesized_tail_counterexample :
    ‖dysonGridTruncatedSum (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) (1/2) 16 0 -
      orderedEvolution (fun _ => Complex.I • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 (1/2)‖ >
    Real.exp (1/2)*(1/2)^2/(2*16) + ((1/2)/16)*(∫ _u in (0 : ℝ)..(1/2),
      ‖(0 : Matrix (Fin 1) (Fin 1) ℂ)‖ + 2*(1/2)^1/(Nat.factorial 1 : ℝ)) := by
  have hlog : (1/2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hexp : Real.exp (1/2) ≤ 2 := by
    have hh := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh
  have hsin : (1/4 : ℝ) ≤ Real.sin (1/2) := by
    have hh := Real.mul_le_sin (by norm_num : (0 : ℝ) ≤ 1/2)
      (by linarith [Real.pi_gt_three] : (1/2 : ℝ) ≤ Real.pi/2)
    have hp := one_div_le_one_div_of_le Real.pi_pos Real.pi_lt_four.le
    norm_num at hp
    calc
      (1/4 : ℝ) ≤ Real.pi⁻¹ := hp
      _ ≤ Real.sin (1/2) := by convert! hh using 1; ring
  have hnorm : (1/4 : ℝ) ≤
      ‖(1 : Matrix (Fin 1) (Fin 1) ℂ)-HamiltonianEvolution 1 (1/2)‖ := by
    unfold HamiltonianEvolution
    rw [dyson_mean_scalar_exp]
    have heq : (1 : Matrix (Fin 1) (Fin 1) ℂ) - Complex.exp (-Complex.I*((1/2 : ℝ) : ℂ)) • 1 =
        (1-Complex.exp (-Complex.I*((1/2 : ℝ) : ℂ))) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
      rw [sub_smul, one_smul]
    rw [heq, norm_smul, CStarRing.norm_one, mul_one]
    have hi : (1-Complex.exp (-Complex.I*((1/2 : ℝ) : ℂ))).im = Real.sin (1/2) := by
      simp [Complex.exp_im]
    have hh := Complex.abs_im_le_norm (1-Complex.exp (-Complex.I*((1/2 : ℝ) : ℂ)))
    rw [hi] at hh
    exact hsin.trans ((le_abs_self _).trans hh)
  have htrunc : dysonGridTruncatedSum (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) (1/2) 16 0 = 1 := by
    simp [dysonGridTruncatedSum, dysonGridDegreeSum]
  rw [htrunc, orderedEvolution_constant_hamiltonian, sub_zero]
  norm_num [intervalIntegral.integral_const, smul_eq_mul, Nat.factorial]
  nlinarith

theorem dyson_joint_unparenthesized_contract_false : ¬ (
∀ (I : Type) [Fintype I] [DecidableEq I] (H Hd : ℝ → Matrix I I ℂ) (t Λ : ℝ) (M K : ℕ),
    Continuous H → 0 ≤ t → 0 ≤ Λ → 0 < M →
    (∀ u ∈ Set.Icc 0 t, (H u).IsHermitian ∧ ‖H u‖ ≤ Λ) →
    Continuous Hd → (∀ u ∈ Set.Icc 0 t, HasDerivAt H (Hd u) u) →
    Λ * t ≤ Real.log 2 →
    ‖dysonGridTruncatedSum H t M K -
        orderedEvolution (fun u => Complex.I • H u) 0 t‖ ≤
      Real.exp (Λ * t) * Λ ^ 2 * t ^ 2 / (2 * M)
        + (t / M) * ∫ u in (0 : ℝ)..t, ‖Hd u‖
        + (2 : ℝ) * (Λ * t) ^ (K + 1) / (Nat.factorial (K + 1) : ℝ)) := by
  intro h
  have hlog : (1/2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hbound : ∀ u ∈ Set.Icc (0 : ℝ) (1/2),
      (1 : Matrix (Fin 1) (Fin 1) ℂ).IsHermitian ∧
        ‖(1 : Matrix (Fin 1) (Fin 1) ℂ)‖ ≤ 1 := by
    intro u _
    exact ⟨by simp, CStarRing.norm_one.le⟩
  have hb := h (Fin 1) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ))
    (fun _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) (1/2) 1 16 0 continuous_const
    (by norm_num) (by norm_num) (by norm_num) hbound continuous_const
    (fun u _ => by simpa using! hasDerivAt_const u (1 : Matrix (Fin 1) (Fin 1) ℂ))
    (by simpa only [one_mul] using! hlog)
  have hc := dyson_unparenthesized_tail_counterexample
  norm_num [intervalIntegral.integral_const, smul_eq_mul, Nat.factorial] at hb hc
  exact (not_le_of_gt hc) hb

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
