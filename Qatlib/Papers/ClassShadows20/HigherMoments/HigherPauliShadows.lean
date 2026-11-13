/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClassShadows20.HigherMoments.CubicPauliShadows
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Mathlib.Data.List.FinRange

/-!
# Exact higher Pauli shadow kernels

`higherQPauliEntry`, `higherQMatMul`, and `higherQLocalTrace` implement single-qubit snapshot
products with Gaussian rational arithmetic. Tensor factorization identifies
`higherShadowKernelQ` with the real trace kernel `higherShadowKernel`. Norm bounds give an
explicit estimate depending on the qubit count and number of snapshots.

These constructions support the treatment in [HuangKuengPreskill2020].

## Main statements

* `higherShadowKernelQ_cast`: identifies the rational and real kernels.
* `higher_pauli_actual_gaussian_rational_trace`: combines exact evaluation with a uniform kernel
  bound.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
namespace Qatlib.Papers.ClassShadows20.HigherMoments
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Componentwise addition of Gaussian rationals represented as rational pairs. -/
def higherGAdd (x y : ℚ×ℚ) : ℚ×ℚ := (x.1+y.1,x.2+y.2)

/-- The Gaussian rational matrix entry of the single-qubit snapshot specified by a Pauli label
and outcome. -/
def higherQPauliEntry (a : Fin 3×Bool) (i j : Fin 2) : ℚ×ℚ :=
  let s := (3/2:ℚ)*cubicSign a.2
  let z : ℚ×ℚ := if a.1=0 then (if i≠j then 1 else 0,0)
    else if a.1=1 then (0,if i=j then 0 else if i=0 then -1 else 1)
    else (if i=j then if i=0 then 1 else -1 else 0,0)
  ((if i=j then 1/2 else 0)+s*z.1,s*z.2)

/-- Multiplication of two-by-two matrices of Gaussian rationals using pair addition and
multiplication. -/
def higherQMatMul (A B : Matrix (Fin 2) (Fin 2) (ℚ×ℚ)) : Matrix (Fin 2) (Fin 2) (ℚ×ℚ) :=
  fun i j=>higherGAdd (gaussianRatMul (A i 0) (B 0 j)) (gaussianRatMul (A i 1) (B 1 j))

/-- The Gaussian rational trace of the ordered product of single-qubit snapshots, with the
identity as the initial product. -/
def higherQLocalTrace (xs : List (Fin 3×Bool)) : ℚ×ℚ :=
  let U := xs.foldl (fun U a=>higherQMatMul U (higherQPauliEntry a))
    (fun i j=>(if i=j then 1 else 0,0))
  higherGAdd (U 0 0) (U 1 1)

/-- The rational real part of the product of the local snapshot-product traces over all `n`
qubits. -/
def higherShadowKernelQ (n : ℕ) (xs : List (Fin n→Fin 3×Bool)) : ℚ :=
  ((List.finRange n).foldl (fun z i=>gaussianRatMul z (higherQLocalTrace (xs.map (fun x=>x i)))) (1,0)).1

/-- The real trace of the ordered product of tensor Pauli snapshots, starting from the identity. -/
noncomputable def higherShadowKernel (n : ℕ) (xs : List (Fin n→Fin 3×Bool)) : ℝ :=
  (Matrix.trace (xs.foldl (fun U x=>U*tensorPauliSnapshot n x) 1)).re

/-- Conversion of Gaussian rational pairs to complex numbers preserves addition. -/
private theorem higherGAdd_complex (x y : ℚ×ℚ) :
    cubicGaussianComplex (higherGAdd x y)=cubicGaussianComplex x+cubicGaussianComplex y := by
  simp only [higherGAdd,cubicGaussianComplex,Rat.cast_add]
  ring

/-- A Pauli snapshot equals one half of the identity plus three halves of its signed Pauli
matrix. -/
private theorem higher_snapshot_form (a : Fin 3×Bool) :
    PauliShadow a.2 a.1=(1/2:ℂ) • (1:Operator 2)+
      ((3/2:ℂ)*(cubicSign a.2:ℂ)) • pauliMatrix a.1 := by
  cases a.2 <;> simp only
      [PauliShadow,PauliProjector,cubicSign,Bool.false_eq_true,if_false,if_true] <;> module

/-- Converting a Gaussian rational snapshot entry to a complex number gives the corresponding
`PauliShadow` entry. -/
theorem higherQPauliEntry_complex (a : Fin 3×Bool) (i j : Fin 2) :
    cubicGaussianComplex (higherQPauliEntry a i j)=PauliShadow a.2 a.1 i j := by
  rw [higher_snapshot_form]
  have h20 : (2:Fin 3)≠0 := by decide
  have h21 : (2:Fin 3)≠1 := by decide
  rcases a with ⟨a,b⟩
  fin_cases a <;> cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [higherQPauliEntry,cubicGaussianComplex,cubicSign,PauliShadow,PauliProjector,
      pauliMatrix,pauliX,pauliY,pauliZ,h20,h21,Matrix.one_apply,Matrix.add_apply,Matrix.smul_apply,
      smul_eq_mul,Complex.ext_iff,
      Complex.mul_re,Complex.mul_im]

/-- Converting Gaussian rational matrix multiplication entrywise to complex numbers gives
ordinary matrix multiplication. -/
private theorem higherQMatMul_complex (A B : Matrix (Fin 2) (Fin 2) (ℚ×ℚ)) :
    (higherQMatMul A B).map cubicGaussianComplex=A.map cubicGaussianComplex*B.map cubicGaussianComplex := by
  ext i j
  simp only [Matrix.map_apply,higherQMatMul,higherGAdd_complex,gaussianRatMul_complex,
    Matrix.mul_apply,Fin.sum_univ_two]

/-- Entrywise complex conversion commutes with a fold multiplying single-qubit snapshot
matrices. -/
private theorem higher_local_fold_complex (xs : List (Fin 3×Bool))
    (A : Matrix (Fin 2) (Fin 2) (ℚ×ℚ)) :
    (xs.foldl (fun U a=>higherQMatMul U (higherQPauliEntry a)) A).map cubicGaussianComplex=
      xs.foldl (fun U a=>U*PauliShadow a.2 a.1) (A.map cubicGaussianComplex) := by
  induction xs generalizing A with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.foldl_cons,ih,higherQMatMul_complex]
    have he : Matrix.map (higherQPauliEntry a) cubicGaussianComplex=PauliShadow a.2 a.1 := by
      ext i j
      exact higherQPauliEntry_complex a i j
    rw [he]

/-- The Gaussian rational local trace converts to the trace of the corresponding complex
snapshot product. -/
theorem higherQLocalTrace_complex (xs : List (Fin 3×Bool)) :
    cubicGaussianComplex (higherQLocalTrace xs)=
      Matrix.trace (xs.foldl (fun U a=>U*PauliShadow a.2 a.1) 1) := by
  let A : Matrix (Fin 2) (Fin 2) (ℚ×ℚ) := fun i j=>(if i=j then 1 else 0,0)
  have hA : A.map cubicGaussianComplex=1 := by
    ext i j
    by_cases hij : i=j <;> simp [A,cubicGaussianComplex,Matrix.one_apply,hij]
  have he := higher_local_fold_complex xs A
  rw [hA] at he
  unfold higherQLocalTrace
  rw [higherGAdd_complex]
  change (xs.foldl (fun U a=>higherQMatMul U (higherQPauliEntry a)) A).map cubicGaussianComplex 0 0+
    (xs.foldl (fun U a=>higherQMatMul U (higherQPauliEntry a)) A).map cubicGaussianComplex 1 1 = _
  rw [he]
  simp [Matrix.trace,Fin.sum_univ_two]

/-- A fold of tensor snapshot products factors into the tensor product of the local snapshot
folds. -/
private theorem higher_tensor_fold (n : ℕ) (xs : List (Fin n→Fin 3×Bool))
    (A : Fin n→Operator 2) :
    xs.foldl (fun U x=>U*tensorPauliSnapshot n x) (tensorPauliProduct n A)=
      tensorPauliProduct n (fun i=>(xs.map (fun x=>x i)).foldl (fun U a=>U*PauliShadow a.2 a.1) (A i)) := by
  induction xs generalizing A with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons]
    change xs.foldl (fun U x=>U*tensorPauliSnapshot n x)
      (tensorPauliProduct n A*tensorPauliProduct n (fun i=>PauliShadow (x i).2 (x i).1)) = _
    rw [tensorPauliProduct_mul,ih]
    rfl

/-- Converting a Gaussian rational product fold gives the initial complex value times the
product of the converted factors. -/
private theorem higher_gaussian_fold {α : Type} (xs : List α) (f : α→ℚ×ℚ) (z : ℚ×ℚ) :
    cubicGaussianComplex (xs.foldl (fun z a=>gaussianRatMul z (f a)) z)=
      cubicGaussianComplex z*(xs.map (fun a=>cubicGaussianComplex (f a))).prod := by
  induction xs generalizing z with
  | nil => simp
  | cons a xs ih => simp only [List.foldl_cons,ih,gaussianRatMul_complex,List.map_cons,List.prod_cons,mul_assoc]

/-- Casting the rational higher shadow kernel to the reals gives the real trace kernel. -/
theorem higherShadowKernelQ_cast (n : ℕ) (xs : List (Fin n→Fin 3×Bool)) :
    (higherShadowKernelQ n xs:ℝ)=higherShadowKernel n xs := by
  have he :=
      higher_gaussian_fold (List.finRange n) (fun i=>higherQLocalTrace (xs.map (fun x=>x i))) (1,0)
  have hunit : cubicGaussianComplex ((1,0):ℚ×ℚ)=1 := by simp [cubicGaussianComplex]
  rw [hunit,one_mul] at he
  simp_rw [higherQLocalTrace_complex] at he
  rw [← List.ofFn_eq_map,List.prod_ofFn] at he
  have ht := higher_tensor_fold n xs (fun _=>1)
  rw [tensorPauliProduct_one] at ht
  unfold higherShadowKernel
  rw [ht,tensorPauliProduct_trace]
  have hr := congrArg Complex.re he
  simpa [higherShadowKernelQ,cubicGaussianComplex] using hr

/-- The norm of a single-qubit Pauli snapshot is at most two. -/
private theorem higher_snapshot_norm (a : Fin 3×Bool) : ‖PauliShadow a.2 a.1‖≤(2:ℝ) := by
  have hu : pauliMatrix a.1∈unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,pauliMatrix_conjTranspose,pauliMatrix_mul_self]
  have hs := l2_norm_unitary_le_one hu
  rw [higher_snapshot_form]
  have hh := norm_add_le ((1/2:ℂ) • (1:Operator 2))
    (((3/2:ℂ)*(cubicSign a.2:ℂ)) • pauliMatrix a.1)
  rcases a with ⟨a,b⟩
  cases b <;> norm_num [norm_smul,cubicSign] at hh ⊢ <;>
    nlinarith [l2_norm_one_le (I:=Fin 2)]

/-- A product fold of single-qubit snapshots has norm at most the initial operator norm times
`2^xs.length`. -/
private theorem higher_local_fold_norm (xs : List (Fin 3×Bool)) (A : Operator 2) :
    ‖xs.foldl (fun U a=>U*PauliShadow a.2 a.1) A‖≤‖A‖*(2:ℝ)^xs.length := by
  induction xs generalizing A with
  | nil => simp
  | cons a xs ih =>
    have hh := (ih (A*PauliShadow a.2 a.1)).trans
      (mul_le_mul_of_nonneg_right ((Matrix.l2_opNorm_mul A _).trans
        (mul_le_mul_of_nonneg_left (higher_snapshot_norm a) (norm_nonneg A))) (by positivity))
    simpa only [List.foldl_cons,List.length_cons,pow_succ,mul_assoc,mul_comm,mul_left_comm] using hh

/-- The norm of any entry of a two-by-two operator is at most its matrix norm. -/
private theorem higher_entry_norm_le (A : Operator 2) (i j : Fin 2) : ‖A i j‖≤‖A‖ := by
  have hk : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j)‖=1 := by
    have hs : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j)‖^2=1 := by
      rw [norm_toEuclidean_sq_eq_re_inner,(normalized_iff_inner_self _).mp (normalized_ket j)]
      rfl
    nlinarith [norm_nonneg (toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j))]
  have hn := l2_norm_mulVec_fromVec_le A (Qatlib.Foundations.PureStateMath.Ket j)
  rw [hk,mul_one] at hn
  have hi := PiLp.norm_apply_le (toEuclidean_fromVec (A*ᵥKet j)) i
  have he : (A*ᵥKet j) i=A i j := by
    simp [Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket,mul_ite]
  change ‖(A*ᵥKet j) i‖≤‖toEuclidean_fromVec (A*ᵥKet j)‖ at hi
  rw [he] at hi
  exact hi.trans hn

/-- The norm of the trace of a local snapshot product is at most `2 * 2^xs.length`. -/
private theorem higher_local_trace_bound (xs : List (Fin 3×Bool)) :
    ‖Matrix.trace (xs.foldl (fun U a=>U*PauliShadow a.2 a.1) 1)‖≤2*(2:ℝ)^xs.length := by
  let A := xs.foldl (fun U a=>U*PauliShadow a.2 a.1) (1:Operator 2)
  have ht : ‖Matrix.trace A‖≤2*‖A‖ := by
    rw [Matrix.trace_fin_two]
    exact (norm_add_le (A 0 0) (A 1 1)).trans
        (by linarith [higher_entry_norm_le A 0 0,higher_entry_norm_le A 1 1])
  have hn := (higher_local_fold_norm xs (1:Operator 2)).trans
    (mul_le_mul_of_nonneg_right (l2_norm_one_le (I:=Fin 2)) (by positivity))
  change ‖Matrix.trace A‖≤_
  nlinarith

/-- The rational kernel equals the real trace kernel after casting, and its absolute value is at
most `2^n * 2^(n * xs.length)`. -/
theorem higher_pauli_actual_gaussian_rational_trace :
    ∀ (n : ℕ) (xs : List (Fin n→Fin 3×Bool)),
    (higherShadowKernelQ n xs:ℝ)=higherShadowKernel n xs ∧
    |higherShadowKernel n xs|≤(2:ℝ)^n*(2:ℝ)^(n*xs.length) := by
  intro n xs
  refine ⟨higherShadowKernelQ_cast n xs,?_⟩
  have ht := higher_tensor_fold n xs (fun _=>1)
  rw [tensorPauliProduct_one] at ht
  unfold higherShadowKernel
  rw [ht,tensorPauliProduct_trace]
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_prod]
  calc
    _ ≤ ∏ i : Fin n,2*(2:ℝ)^xs.length := by
      apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
      intro i _
      simpa only [List.length_map] using higher_local_trace_bound (xs.map (fun x=>x i))
    _ = _ := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow,← pow_mul]
      rw [Nat.mul_comm xs.length n]

end Qatlib.Papers.ClassShadows20.HigherMoments
