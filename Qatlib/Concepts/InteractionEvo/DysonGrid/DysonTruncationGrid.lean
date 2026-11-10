/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.TimeOrdered.TimeOrderedConsumers
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.List.Sublists
import Mathlib.Algebra.BigOperators.Ring.List

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.DysonGrid
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

noncomputable def dysonPrefix {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (s t : ℝ) (K : ℕ) : Matrix I I ℂ :=
  ∑ j ∈ Finset.range (K + 1), orderedDysonTerm A s j t

noncomputable def dysonGridStep {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M : ℕ) (j : Fin M) : Matrix I I ℂ :=
  1 - ((t / (M : ℝ) : ℝ) : ℂ) • (Complex.I • H (t * j.val / M))

noncomputable def dysonGridRun {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M : ℕ) : Matrix I I ℂ :=
  ((List.ofFn (dysonGridStep H t M)).reverse).prod

theorem dyson_finite_prefix_explicit_factorial_tail :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A : ℝ → Matrix I I ℂ)
      (s t Λ : ℝ) (K : ℕ), Continuous A → 0 ≤ Λ →
      (∀ u ∈ Set.uIcc s t, ‖A u‖ ≤ Λ) →
      ‖orderedEvolution A s t - dysonPrefix A s t K‖ ≤
        Real.exp (Λ * |t - s|) * (Λ * |t - s|) ^ (K + 1) /
          (Nat.factorial (K + 1) : ℝ) := by
  intro I _ _ A s t Λ K hA hΛ hbound
  let a := Λ * |t - s|
  let k := K + 1
  have ha : 0 ≤ a := mul_nonneg hΛ (abs_nonneg _)
  have hmajorant : ∀ n : ℕ, ‖orderedDysonTerm A s (n + k) t‖ ≤
      (a ^ k / (k.factorial : ℝ)) * (a ^ n / (n.factorial : ℝ)) := by
    intro n
    have hd : (n.factorial : ℝ) * (k.factorial : ℝ) ≤ ((n + k).factorial : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (n + k))
        (Nat.factorial_mul_factorial_dvd_factorial_add n k)
    calc
      _ ≤ a ^ (n + k) / ((n + k).factorial : ℝ) :=
        orderedDysonTerm_norm_le A hA s t Λ hΛ hbound (n + k)
      _ ≤ a ^ (n + k) / ((n.factorial : ℝ) * (k.factorial : ℝ)) :=
        div_le_div_of_nonneg_left (pow_nonneg ha _) (by positivity) hd
      _ = _ := by rw [pow_add]; ring
  have hm : Summable (fun n : ℕ =>
      (a ^ k / (k.factorial : ℝ)) * (a ^ n / (n.factorial : ℝ))) :=
    (Real.summable_pow_div_factorial a).mul_left _
  have hn : Summable (fun n : ℕ => ‖orderedDysonTerm A s (n + k) t‖) :=
    hm.of_nonneg_of_le (fun _ => norm_nonneg _) hmajorant
  have htail : orderedEvolution A s t - dysonPrefix A s t K =
      ∑' n : ℕ, orderedDysonTerm A s (n + k) t := by
    have h := (orderedDysonTerm_summable A hA s t).sum_add_tsum_nat_add k
    change dysonPrefix A s t K + (∑' n : ℕ, orderedDysonTerm A s (n + k) t) =
      orderedEvolution A s t at h
    exact sub_eq_iff_eq_add.mpr (by rw [← h]; abel)
  rw [htail]
  calc
    _ ≤ ∑' n : ℕ, ‖orderedDysonTerm A s (n + k) t‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, (a ^ k / (k.factorial : ℝ)) *
        (a ^ n / (n.factorial : ℝ)) := hn.tsum_le_tsum hmajorant hm
    _ = _ := by
      rw [tsum_mul_left, ← congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)) a,
        ← Real.exp_eq_exp_ℝ]
      dsimp [a, k]
      ring

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

private theorem dysonLeftProduct_run {I : Type} [Fintype I] [DecidableEq I]
    (f : ℕ → Matrix I I ℂ) (n : ℕ) (ψ : QState I) :
    Run 1 ((List.range n).map (fun j => Step.gate (f j))) ψ =
      (dysonLeftProduct f n).mulVec ψ := by
  induction n with
  | zero => simp [dysonLeftProduct]
  | succ n ih =>
    rw [List.range_succ, List.map_append, run_append, ih]
    simp [Run, ApplyGate, dysonLeftProduct, Matrix.mulVec_mulVec]

private theorem dyson_sampled_product_error {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t L : ℝ) (M : ℕ) (hH : Continuous H)
    (ht : 0 ≤ t) (hL : 0 ≤ L) (hM : 0 < M)
    (hHerm : ∀ u ∈ Set.Icc 0 t, (H u).IsHermitian)
    (hLip : ∀ u ∈ Set.Icc 0 t, ∀ v ∈ Set.Icc 0 t, ‖H u - H v‖ ≤ L * |u - v|) :
    ‖dysonLeftProduct (fun j => HamiltonianEvolution (H ((j : ℝ) * (t / M))) (t / M)) M -
      orderedEvolution (fun u => Complex.I • H u) 0 t‖ ≤ L * t ^ 2 / (2 * M) := by
  let F := fun u => H (dysonClip t u)
  have hF : Continuous F := hH.comp (continuous_const.max (continuous_const.min continuous_id))
  have hFherm : ∀ u, (F u).IsHermitian := fun u => hHerm _ (dysonClip_mem t ht u)
  have hFeq : ∀ u ∈ Set.Icc 0 t, F u = H u := by
    intro u hu
    dsimp [F]
    rw [dysonClip_eq hu]
  have hFlip : ∀ u ∈ Set.Icc 0 t, ∀ v ∈ Set.Icc 0 t, ‖F u - F v‖ ≤ L * |u - v| := by
    intro u hu v hv
    rw [hFeq u hu, hFeq v hv]
    exact hLip u hu v hv
  have hN : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hmem (j : ℕ) (hj : j < M) : (j : ℝ) * (t / M) ∈ Set.Icc 0 t := by
    refine ⟨mul_nonneg (Nat.cast_nonneg j) (div_nonneg ht (Nat.cast_nonneg M)), ?_⟩
    have hj' : (j : ℝ) ≤ M := by exact_mod_cast hj.le
    calc
      (j : ℝ) * (t / M) ≤ (M : ℝ) * (t / M) :=
        mul_le_mul_of_nonneg_right hj' (div_nonneg ht (Nat.cast_nonneg M))
      _ = t := by field_simp
  have hproduct : dysonLeftProduct
      (fun j => HamiltonianEvolution (F ((j : ℝ) * (t / M))) (t / M)) M =
      dysonLeftProduct (fun j => HamiltonianEvolution (H ((j : ℝ) * (t / M))) (t / M)) M := by
    rw [dysonLeftProduct_eq_range_prod, dysonLeftProduct_eq_range_prod]
    congr 2
    apply List.map_congr_left
    intro j hj
    rw [hFeq _ (hmem j (List.mem_range.mp hj))]
  have hevolution : orderedEvolution (fun u => Complex.I • F u) 0 t =
      orderedEvolution (fun u => Complex.I • H u) 0 t :=
    dyson_interval_evolution_congr _ _ t ht (fun u hu => by rw [hFeq u hu])
  have hrun (ψ : QState I) : Run 1 (sampledEvolutionWord F t M) ψ =
      (dysonLeftProduct (fun j => HamiltonianEvolution (F ((j : ℝ) * (t / M)))
        (t / M)) M).mulVec ψ := by
    have hword : sampledEvolutionWord F t M =
        (List.range M).map (fun j : ℕ => Step.gate
          (HamiltonianEvolution (F ((j : ℝ) * t / M)) (t / M))) := by
      change ((List.range M).flatMap (fun j : ℕ => [(j : ℝ)])).map _ = _
      rw [← List.map_eq_flatMap, List.map_map]
      rfl
    rw [hword]
    simpa only [mul_div_assoc] using!
      dysonLeftProduct_run (fun j => HamiltonianEvolution (F ((j : ℝ) * (t / M)))
        (t / M)) M ψ
  have hstate := (ordered_sampled_program_error_and_cost I F t L M hF hFherm
    ht hL hM hFlip).2.2.2
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I) _‖ ≤ _
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have h := hstate (toVec_fromEuclidean x)
  rw [hrun, hproduct, hevolution, ← Matrix.sub_mulVec] at h
  change ‖toEuclidean_fromVec (ApplyGate _ (toVec_fromEuclidean x))‖ ≤
    L * t ^ 2 / (2 * M) * ‖toEuclidean_fromVec (toVec_fromEuclidean x)‖ at h
  rw [← toEuclideanCLM_applyGate, toEuclidean_fromVec_toVec_fromEuclidean] at h
  exact h

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

theorem dyson_sorted_grid_actual_error_and_cost :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (H : ℝ → Matrix I I ℂ)
      (t Λ L : ℝ) (M : ℕ), Continuous H → 0 ≤ t → 0 ≤ Λ → 0 ≤ L → 0 < M →
      (∀ u ∈ Set.Icc 0 t, (H u).IsHermitian ∧ ‖H u‖ ≤ Λ) →
      (∀ u ∈ Set.Icc 0 t, ∀ v ∈ Set.Icc 0 t, ‖H u - H v‖ ≤ L * |u - v|) →
      ‖dysonGridRun H t M - orderedEvolution (fun u => Complex.I • H u) 0 t‖ ≤
        Real.exp (Λ * t) * (Λ ^ 2 + L) * t ^ 2 / (2 * M) ∧
      ((List.ofFn (dysonGridStep H t M)).reverse).length = M := by
  intro I _ _ H t Λ L M hH ht hΛ hL hM hbound hLip
  refine ⟨?_, by simp⟩
  let h : ℝ := t / M
  let c := Λ * h
  let d := c ^ 2 / 2
  let B := Real.exp c
  let f := fun j : ℕ => 1 - (h : ℂ) • (Complex.I • H ((j : ℝ) * h))
  let g := fun j : ℕ => HamiltonianEvolution (H ((j : ℝ) * h)) h
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hh : 0 ≤ h := div_nonneg ht (Nat.cast_nonneg M)
  have hc : 0 ≤ c := mul_nonneg hΛ hh
  have hmem (j : ℕ) (hj : j < M) : (j : ℝ) * h ∈ Set.Icc 0 t := by
    refine ⟨mul_nonneg (Nat.cast_nonneg j) hh, ?_⟩
    have hj' : (j : ℝ) ≤ M := by exact_mod_cast hj.le
    calc
      (j : ℝ) * h ≤ (M : ℝ) * h := mul_le_mul_of_nonneg_right hj' hh
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
    (fun j hj => by
      simpa [B, d, c, mul_div_assoc] using!
        dyson_euler_factor_error (H ((j : ℝ) * h)) h Λ hh hΛ (hbound _ (hmem j hj)).2)
  have hs := dyson_sampled_product_error H t L M hH ht hL hM
    (fun u hu => (hbound u hu).1) hLip
  change ‖dysonLeftProduct g M - orderedEvolution (fun u => Complex.I • H u) 0 t‖ ≤
    L * t ^ 2 / (2 * M) at hs
  have hBpow : B ^ M = Real.exp (Λ * t) := by
    dsimp [B]
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [c, h]
    field_simp
  have hpoly : (M : ℝ) * B ^ M * d =
      Real.exp (Λ * t) * Λ ^ 2 * t ^ 2 / (2 * M) := by
    rw [hBpow]
    dsimp [d, c, h]
    field_simp
  rw [hrun]
  calc
    _ ≤ ‖dysonLeftProduct f M - dysonLeftProduct g M‖ +
        ‖dysonLeftProduct g M - orderedEvolution (fun u => Complex.I • H u) 0 t‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (M : ℝ) * B ^ M * d + L * t ^ 2 / (2 * M) := add_le_add hp hs
    _ ≤ _ := by
      rw [hpoly, ← add_div, mul_add]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have he : 1 ≤ Real.exp (Λ * t) := Real.one_le_exp (mul_nonneg hΛ ht)
      nlinarith [mul_nonneg hL (sq_nonneg t)]

private theorem dyson_list_product_one_add {I : Type} [Fintype I] [DecidableEq I]
    (l : List (Matrix I I ℂ)) :
    (l.map (fun A => 1 + A)).prod = (l.sublists.map List.prod).sum := by
  induction l with
  | nil => simp
  | cons A l ih =>
    rw [List.map_cons, List.prod_cons, ih,
      ((List.sublists_cons_perm_append A l).map List.prod).sum_eq]
    simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def,
      List.prod_cons]
    rw [List.sum_map_mul_left]
    simp [add_mul]

theorem dyson_grid_strict_subset_expansion {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M : ℕ) :
    dysonGridRun H t M =
      ((((List.ofFn (fun j : Fin M =>
        -((t / (M : ℝ) : ℝ) : ℂ) • (Complex.I • H (t * j.val / M)))).reverse).sublists
          ).map List.prod).sum := by
  let l := (List.ofFn (fun j : Fin M =>
    -((t / (M : ℝ) : ℝ) : ℂ) • (Complex.I • H (t * j.val / M)))).reverse
  have hword : l.map (fun A => 1 + A) = (List.ofFn (dysonGridStep H t M)).reverse := by
    dsimp [l]
    rw [List.map_reverse, List.map_ofFn]
    congr 2
    funext j
    simp [dysonGridStep, sub_eq_add_neg]
  rw [dysonGridRun, ← hword]
  exact dyson_list_product_one_add l

theorem dyson_grid_strict_degree_count {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) :
    let l := (List.ofFn (fun j : Fin M =>
      -((t / (M : ℝ) : ℝ) : ℂ) • (Complex.I • H (t * j.val / M)))).reverse
    (l.sublistsLen k).length = M.choose k ∧
      ∀ w ∈ l.sublistsLen k, w.length = k := by
  (try dsimp only)
  refine ⟨?_, fun w hw => List.length_of_sublistsLen hw⟩
  rw [List.length_sublistsLen, List.length_reverse, List.length_ofFn]

end Qatlib.Concepts.InteractionEvo.DysonGrid
