/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClassShadows20.HigherMoments.CubicPauliShadows
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.ClassShadows20.HigherMoments
open Matrix
open scoped Classical BigOperators ComplexOrder
set_option autoImplicit false

def cubicKernelRat {n : ℕ} (a b c : Fin n → Fin 3 × Bool) : ℚ :=
  ((List.ofFn (fun i => cubicLocalRat (a i) (b i) (c i))).foldl gaussianRatMul (1,0)).1

def cubicKernelRatCounted {n : ℕ} (a b c : Fin n → Fin 3 × Bool) : ℚ × ℕ :=
  let z := (List.ofFn (fun i => cubicLocalRat (a i) (b i) (c i))).foldl
    (fun z v => (gaussianRatMul z.1 v,z.2+1)) ((1,0),0)
  (z.1.1,z.2)

def cubicURatCounted {n m : ℕ} (ω : Fin m → Fin n → Fin 3 × Bool) : ℚ × ℕ × ℕ :=
  let a := (tripleIndexList m).foldl (fun a t =>
    let v := cubicKernelRatCounted (ω t.1) (ω t.2.1) (ω t.2.2)
    (a.1+v.1,a.2.1+1,a.2.2+v.2)) (0,0,0)
  (a.1/(m.choose 3:ℚ),a.2.1,a.2.2)

noncomputable def cubicMixedTwo : Operator 4 :=
  Matrix.diagonal ![(1/2:ℂ),1/4,1/4,0]

private theorem cubic_gaussian_fold (vs : List (ℚ × ℚ)) (a : ℚ × ℚ) :
    cubicGaussianComplex (vs.foldl gaussianRatMul a) =
      cubicGaussianComplex a*(vs.map cubicGaussianComplex).prod := by
  induction vs generalizing a with
  | nil => simp
  | cons v vs ih => simp only [List.foldl_cons,ih,gaussianRatMul_complex,List.map_cons,List.prod_cons]; ring

private theorem cubic_local_count_fold (vs : List (ℚ × ℚ)) (a : (ℚ × ℚ) × ℕ) :
    vs.foldl (fun z v => (gaussianRatMul z.1 v,z.2+1)) a =
      (vs.foldl gaussianRatMul a.1,a.2+vs.length) := by
  induction vs generalizing a with
  | nil => rfl
  | cons v vs ih => simp [ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem cubicKernelRatCounted_spec {n : ℕ} (a b c : Fin n → Fin 3 × Bool) :
    cubicKernelRatCounted a b c = (cubicKernelRat a b c,n) := by
  simp [cubicKernelRatCounted,cubic_local_count_fold,cubicKernelRat]

theorem cubicKernelRat_real {n : ℕ} (a b c : Fin n → Fin 3 × Bool) :
    (cubicKernelRat a b c : ℝ) = cubicShadowKernel n a b c := by
  have he := cubic_gaussian_fold (List.ofFn (fun i => cubicLocalRat (a i) (b i) (c i))) (1,0)
  simp only [List.map_ofFn,List.prod_ofFn] at he
  have ht : Matrix.trace (tensorPauliSnapshot n a*tensorPauliSnapshot n b*tensorPauliSnapshot n c) =
      cubicGaussianComplex
        ((List.ofFn (fun i => cubicLocalRat (a i) (b i) (c i))).foldl gaussianRatMul (1,0)) := by
    rw [tensorPauliSnapshot,tensorPauliSnapshot,tensorPauliSnapshot,
      tensorPauliProduct_mul,tensorPauliProduct_mul,tensorPauliProduct_trace]
    simp_rw [cubicLocalRat_trace]
    simpa [cubicGaussianComplex] using he.symm
  have hr := congrArg Complex.re ht
  simpa [cubicShadowKernel,cubicKernelRat,cubicGaussianComplex] using hr.symm

private theorem cubic_triple_count_fold {T : Type} (f : T → ℚ × ℕ)
    (ts : List T) (a : ℚ × ℕ × ℕ) :
    ts.foldl (fun a t => let v := f t; (a.1+v.1,a.2.1+1,a.2.2+v.2)) a =
      (a.1+(ts.map (fun t => (f t).1)).sum,
       a.2.1+ts.length,a.2.2+(ts.map (fun t => (f t).2)).sum) := by
  induction ts generalizing a with
  | nil => simp
  | cons t ts ih => simp [ih,add_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem cubic_shadow_rational_fold_and_actual_resources (n m r : ℕ)
    (ω : Fin m → Fin n → Fin 3 × Bool)
    (W : Fin (2*r+1) → Fin m → Fin n → Fin 3 × Bool) :
    ((cubicURatCounted ω).1:ℝ)=cubicShadowU n m ω ∧
    (cubicURatCounted ω).2.1=m.choose 3 ∧
    (cubicURatCounted ω).2.2=n*(m.choose 3) ∧
    tensorPauliFreshResourceCounts n m (2*r+1) W=
      ((2*r+1)*m,2*n*((2*r+1)*m),n*((2*r+1)*m),0) := by
  have hf := cubic_triple_count_fold
    (fun t : TripleIndex m => cubicKernelRatCounted (ω t.1) (ω t.2.1) (ω t.2.2))
    (tripleIndexList m) (0,0,0)
  simp only [cubicURatCounted,hf]
  simp only [cubicKernelRatCounted_spec,zero_add,List.map_const',
    List.sum_replicate,nsmul_eq_mul,tripleIndexList_length]
  refine ⟨?_,trivial,Nat.mul_comm _ _,tensorPauliFreshResourceCounts_spec n m (2*r+1) W⟩
  unfold cubicShadowU tripleUStatistic
  simp only [Rat.cast_div,Rat.cast_natCast]
  congr 1
  induction tripleIndexList m with
  | nil => simp
  | cons t ts ih => simp only [List.map_cons,List.sum_cons,Rat.cast_add,cubicKernelRat_real,ih]

theorem cubicMixedTwo_density : IsDensityOperator cubicMixedTwo := by
  constructor
  · rw [cubicMixedTwo,Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> norm_num [Complex.nonneg_iff]
  · norm_num [cubicMixedTwo,Matrix.trace_diagonal,Fin.sum_univ_succ]

theorem cubicMixedTwo_trace_cube : (Matrix.trace (cubicMixedTwo^3)).re = 5/32 := by
  norm_num [cubicMixedTwo,pow_succ,Matrix.diagonal_mul_diagonal,Matrix.trace_diagonal,
    Fin.sum_univ_succ]

theorem cubic_shadow_genuine_four_dimensional_mixed_consumer :
    IsDensityOperator cubicMixedTwo ∧
    (Matrix.trace (cubicMixedTwo^3)).re=5/32 ∧
    ∀ (m : ℕ), 3 ≤ m →
    ∀ hρ : IsDensityOperator cubicMixedTwo,
      (∑ ω : Fin m → Fin 2 → Fin 3 × Bool,
        (tensorPauliLaw 2 cubicMixedTwo hρ).probOf ω*cubicShadowU 2 m ω)=5/32 := by
  refine ⟨cubicMixedTwo_density,cubicMixedTwo_trace_cube,?_⟩
  intro m hm hρ
  have he := (cubic_shadow_same_record_mean_and_variance 2 m cubicMixedTwo hρ hm).1
  rw [cubicMixedTwo_trace_cube] at he
  exact he

end Qatlib.Papers.ClassShadows20.HigherMoments
