/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Qatlib.Concepts.QueryWordCore.QueryMachinery.NegativeAdversary
import Mathlib.Analysis.Matrix.Order
import Qatlib.Foundations.OperatorErrors.OperatorError

/-!
# Weighted adversary matrix composition

`weightedAdvGamma` composes an outer Boolean adversary matrix with inner matrices through
shifted factors `‖Gg i‖ • 1 + Gg i`. Lifting, compression, and positive semidefinite
Hadamard-product estimates establish exact formulas for the composed matrix norm and its
coordinate-filter norms, following the negative-weight composition framework of
[HoyerLeeSpalek2007].

The module derives weighted witness inequalities and a bounded-error query-circuit lower bound.
It also constructs extreme eigenvectors under sufficient nonemptiness hypotheses and exhibits an
empty-block counterexample to the unrestricted extreme-eigenvector contract.

## Main statements

* `weightedAdvGamma_norm_eq`: factor the composed norm into the outer and inner norms.
* `weightedAdvGamma_filter_norm_eq`: factor each composed coordinate-filter norm.
* `weightedAdvGamma_actual_lower_bound`: apply the composed witness to a query circuit.
* `weightedAdvGamma_original_extreme_contract_false`: refute the contract that lacks a
  nonempty-domain condition.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.AdversaryBounds.WeightedAdvComp
open Matrix BigOperators
open scoped Classical Matrix.Norms.L2Operator ComplexOrder ENNReal MatrixOrder

/-- Lift each column of `S` into the block indexed by its label under `e`, filling the other
label blocks with zero. -/
noncomputable def weightedAdvLift {Y F T : Type} [DecidableEq F]
    (e : Y → F) (S : Matrix T Y ℂ) : Matrix (F×T) Y ℂ :=
  fun z x => if z.1=e x then S z.2 x else 0

/-- The Gram matrix of `weightedAdvLift e S` equals `Sᴴ * S` within equal-label blocks and is
zero between different-label blocks. -/
theorem weightedAdvLift_gram {Y F T : Type} [Fintype F] [Fintype T]
    [DecidableEq F] (e : Y → F) (S : Matrix T Y ℂ) (x y : Y) :
    ((weightedAdvLift e S)ᴴ*weightedAdvLift e S) x y =
      if e x=e y then (Sᴴ*S) x y else 0 := by
  classical
  by_cases h : e x=e y
  · simp [weightedAdvLift,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,h]
  · simp [weightedAdvLift,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,h,Ne.symm h]

/-- Compressing `A` tensored with the identity by `weightedAdvLift e S` gives entry `A (e x) (e
y) * (Sᴴ * S) x y`. -/
theorem weightedAdvLift_compression {Y F T : Type} [Fintype F] [Fintype T]
    [DecidableEq F] [DecidableEq T] (e : Y → F) (S : Matrix T Y ℂ)
    (A : Matrix F F ℂ) (x y : Y) :
    ((weightedAdvLift e S)ᴴ*TensorGate A (1 : Matrix T T ℂ)*weightedAdvLift e S) x y =
      A (e x) (e y)*(Sᴴ*S) x y := by
  classical
  simp [weightedAdvLift,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
    TensorGate,Matrix.one_apply,Finset.mul_sum,apply_ite,mul_left_comm,mul_comm]

/-- If `‖V‖ * ‖V‖ ≤ r`, the norm of `Vᴴ * (A ⊗ 1) * V` is at most `r * ‖A‖`. -/
theorem weightedAdv_compression_norm_le {Y F T : Type} [Fintype Y] [Fintype F] [Fintype T]
    [DecidableEq Y] [DecidableEq F] [DecidableEq T]
    (V : Matrix (F×T) Y ℂ) (A : Matrix F F ℂ) (r : ℝ)
    (hV : ‖V‖*‖V‖≤r) :
    ‖Vᴴ*TensorGate A (1 : Matrix T T ℂ)*V‖≤r*‖A‖ := by
  calc
    _ ≤ (‖Vᴴ‖*‖TensorGate A (1 : Matrix T T ℂ)‖)*‖V‖ :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ = (‖V‖*(‖A‖*‖(1 : Matrix T T ℂ)‖))*‖V‖ := by rw [Matrix.l2_opNorm_conjTranspose,l2_norm_tensorGate]
    _ ≤ (‖V‖*(‖A‖*1))*‖V‖ := by gcongr; exact l2_norm_one_le
    _ = (‖V‖*‖V‖)*‖A‖ := by ring
    _ ≤ r*‖A‖ := mul_le_mul_of_nonneg_right hV (norm_nonneg _)

/-- For Hermitian `A` and positive semidefinite `B`, the operator norm of their Hadamard product
is at most `‖A‖` times the supremum of the real diagonal entries of `B`. -/
theorem weightedAdv_hadamard_norm_le {Y : Type} [Fintype Y] [DecidableEq Y]
    (A : Matrix Y Y ℂ) (_hA : A.IsHermitian) (B : Matrix Y Y ℂ) (hB : B.PosSemidef) :
    ‖Matrix.hadamard A B‖≤(⨆ y,(B y y).re)*‖A‖ := by
  classical
  rcases isEmpty_or_nonempty Y with hY|hY
  · let := hY
    have hA0 : A=0 := by ext x; exact isEmptyElim x
    rw [hA0]
    have hh : Matrix.hadamard (0 : Matrix Y Y ℂ) B=0 := by ext x y; simp [Matrix.hadamard]
    rw [hh,norm_zero,mul_zero]
  · let := hY
    obtain ⟨S,hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
    have hgram : B=Sᴴ*S := by simpa only [Matrix.star_eq_conjTranspose] using hS
    let V := weightedAdvLift (id : Y → Y) S
    have hVG : Vᴴ*V=diagonal (fun y => B y y) := by
      ext x y
      rw [weightedAdvLift_gram,← hgram]
      by_cases h : x=y
      · subst y; simp
      · simp [h]
    let d := ⨆ y,(B y y).re
    have hbdd : BddAbove (Set.range fun y => (B y y).re) := Finite.bddAbove_range _
    have hb0 (y : Y) : 0≤(B y y).re := (Complex.nonneg_iff.mp hB.diag_nonneg).1
    have hd0 : 0≤d := (hb0 (Classical.arbitrary Y)).trans (le_ciSup hbdd (Classical.arbitrary Y))
    have hreal (y : Y) : ((B y y).re : ℂ)=B y y := by
      have him : (B y y).im=0 := (Complex.nonneg_iff.mp (hB.diag_nonneg (i := y))).2.symm
      exact Complex.ext rfl (by simpa using him.symm)
    have hvn : ‖V‖*‖V‖≤d := by
      rw [← Matrix.l2_opNorm_conjTranspose_mul_self,hVG,Matrix.l2_opNorm_diagonal,
        pi_norm_le_iff_of_nonneg hd0]
      intro y
      rw [← hreal y,Complex.norm_of_nonneg (hb0 y)]
      exact le_ciSup hbdd y
    have he : Vᴴ*TensorGate A (1 : Matrix Y Y ℂ)*V=Matrix.hadamard A B := by
      ext x y
      rw [weightedAdvLift_compression,← hgram]
      rfl
    rw [← he]
    exact weightedAdv_compression_norm_le V A d hvn

/-- For a matrix vanishing on equal-output pairs, multiplying an eigenvector by the Boolean
output sign negates its eigenvalue. -/
theorem weightedAdv_bipartite_flip {Y : Type} [Fintype Y] (g : Y → Bool)
    (G : Matrix Y Y ℂ) (hz : ∀ x y,g x=g y → G x y=0)
    (u : QState Y) (lam : ℂ) (he : G*ᵥu=lam • u) :
    G*ᵥ(fun y => (if g y then (-1 : ℂ) else 1)*u y)=
      (-lam) • (fun y => (if g y then (-1 : ℂ) else 1)*u y) := by
  have hp (x y : Y) : G x y*((if g y then (-1 : ℂ) else 1)*u y)=
      (-(if g x then (-1 : ℂ) else 1))*(G x y*u y) := by
    cases hx : g x <;> cases hy : g y
    · rw [hz x y (by rw [hx,hy])]; simp
    · simp
    · simp
    · rw [hz x y (by rw [hx,hy])]; simp
  funext x
  change (∑ y,G x y*((if g y then (-1 : ℂ) else 1)*u y))=
    (-lam)*((if g x then (-1 : ℂ) else 1)*u x)
  simp_rw [hp]
  rw [← Finset.mul_sum]
  have hx := congrFun he x
  change (∑ y,G x y*u y)=lam*u x at hx
  rw [hx]
  ring

/-- A nonzero eigenvector with nonzero eigenvalue for an output-bipartite matrix has a nonzero
coordinate in each Boolean output fiber. -/
theorem weightedAdv_bipartite_fiber_nonzero {Y : Type} [Fintype Y] (g : Y → Bool)
    (G : Matrix Y Y ℂ) (hz : ∀ x y,g x=g y → G x y=0)
    (u : QState Y) (hu : u≠0) (lam : ℂ) (hlam : lam≠0) (he : G*ᵥu=lam • u) (b : Bool) :
    ∃ y,g y=b ∧ u y≠0 := by
  classical
  by_contra hb
  push Not at hb
  apply hu
  funext x
  by_cases hxb : g x=b
  · exact hb x hxb
  · have hr : (G*ᵥu) x=0 := by
      simp only [Matrix.mulVec,dotProduct]
      apply Finset.sum_eq_zero
      intro y _
      by_cases hyb : g y=b
      · rw [hb y hyb,mul_zero]
      · have hxy : g x=g y := by
          cases b <;> cases hx : g x <;> cases hy : g y <;> simp_all
        rw [hz x y hxy,zero_mul]
    have hx := congrFun he x
    change (G*ᵥu) x=lam*u x at hx
    rw [hr] at hx
    exact (mul_eq_zero.mp hx.symm).resolve_left hlam

/-- A Hermitian output-bipartite matrix on a nonempty finite domain possesses a nonzero
eigenvector with eigenvalue equal to its operator norm. -/
theorem weightedAdv_positive_eigenvector {Y : Type} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (g : Y → Bool) (G : Matrix Y Y ℂ) (hG : G.IsHermitian)
    (hz : ∀ x y,g x=g y → G x y=0) :
    ∃ u : QState Y,u≠0 ∧ G*ᵥu=(‖G‖ : ℂ) • u := by
  classical
  obtain ⟨u,lam,hn,habs,he,_⟩ :=
      negative_adversary_extreme_eigenvector_and_start Y Unit G (Ket ()) hG
      (by simp [Normalized,Ket])
  have hu : u≠0 := by
    intro h0
    rw [h0] at hn
    simp [Normalized] at hn
  by_cases hlam : 0≤lam
  · have hnorm : lam=‖G‖ := by simpa only [abs_of_nonneg hlam] using habs
    exact ⟨u,hu,by simpa only [hnorm] using he⟩
  · let w : QState Y := fun y => (if g y then (-1 : ℂ) else 1)*u y
    have hw : w≠0 := by
      intro hw0
      apply hu
      funext y
      have hy := congrFun hw0 y
      change (if g y then (-1 : ℂ) else 1)*u y=0 at hy
      cases hgy : g y <;> simpa [hgy] using hy
    have hneg : -lam=‖G‖ := by simpa only [abs_of_neg (lt_of_not_ge hlam)] using habs
    have hc : -(lam : ℂ)=(‖G‖ : ℂ) := by exact_mod_cast hneg
    have he' := weightedAdv_bipartite_flip g G hz u (lam : ℂ) he
    change G*ᵥw=(-(lam : ℂ)) • w at he'
    rw [hc] at he'
    exact ⟨w,hw,he'⟩

/-- A finite square matrix with strictly positive operator norm has a nonempty index type. -/
theorem weightedAdv_nonempty_of_norm_pos {Y : Type} [Fintype Y] [DecidableEq Y]
    (G : Matrix Y Y ℂ) (hG : 0<‖G‖) : Nonempty Y := by
  by_contra hy
  let : IsEmpty Y := not_nonempty_iff.mp hy
  have hg : G=0 := by ext x; exact isEmptyElim x
  rw [hg,norm_zero] at hG
  exact lt_irrefl 0 hG

/-- The absolute value of a real eigenvalue associated with a nonzero vector is at most the
matrix operator norm. -/
theorem weightedAdv_eigenvalue_norm_le {Y : Type} [Fintype Y] [DecidableEq Y]
    (G : Matrix Y Y ℂ) (w : QState Y) (hw : w≠0) (lam : ℝ)
    (he : G*ᵥw=(lam : ℂ) • w) : |lam|≤‖G‖ := by
  have hwn : toEuclidean_fromVec w≠0 := by
    intro hz
    apply hw
    funext y
    exact congrArg (fun u : EuclideanSpace ℂ Y => u y) hz
  have hp : 0<‖toEuclidean_fromVec w‖ := norm_pos_iff.mpr hwn
  have h := ((Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix Y Y ℂ ≃⋆ₐ[ℂ]
    (EuclideanSpace ℂ Y →L[ℂ] EuclideanSpace ℂ Y)) G).le_opNorm (toEuclidean_fromVec w)
  rw [← Matrix.cstar_norm_def,toEuclideanCLM_applyGate] at h
  change ‖toEuclidean_fromVec (G*ᵥw)‖≤‖G‖*‖toEuclidean_fromVec w‖ at h
  rw [he] at h
  change ‖(lam : ℂ) • toEuclidean_fromVec w‖≤‖G‖*‖toEuclidean_fromVec w‖ at h
  rw [norm_smul,Complex.norm_real] at h
  have h' : |lam| *‖toEuclidean_fromVec w‖≤‖G‖*‖toEuclidean_fromVec w‖ := by
    simpa only [Real.norm_eq_abs] using h
  nlinarith

variable {k : ℕ} {X : Fin k → Type} {n : Fin k → ℕ}
variable [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

/-- Retain the entries of `Gamma` whose inputs differ at coordinate `c`, replacing all other
entries by zero. -/
noncomputable def weightedAdvFilter {X : Type} {κ : Type} [DecidableEq κ]
    (input : X → κ → Bool) (Gamma : Matrix X X ℂ) (c : κ) : Matrix X X ℂ :=
  fun x y => if input x c ≠ input y c then Gamma x y else 0

/-- Read the inner input bit indexed by the block-coordinate pair `c` from the block tuple `x`. -/
def weightedAdvInput {X : Fin k → Type} {n : Fin k → ℕ}
    (gin : ∀ i, X i → Fin (n i) → Bool) (x : (i : Fin k) → X i)
    (c : (i : Fin k) × Fin (n i)) : Bool :=
  gin c.1 (x c.1) c.2


/-- The composed matrix whose entry is the outer matrix evaluated at inner output strings times
the product of the shifted inner-matrix entries. -/
noncomputable def weightedAdvGamma
    (g : ∀ i, X i → Bool) (_f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : ∀ i, Matrix (X i) (X i) ℂ) :
    Matrix ((i : Fin k) → X i) ((i : Fin k) → X i) ℂ :=
  fun x y => Gf (fun i => g i (x i)) (fun i => g i (y i)) *
    ∏ i, (Matrix.diagonal (fun _ : X i => (‖Gg i‖ : ℂ)) + Gg i) (x i) (y i)

/-- The composed adversary matrix is Hermitian when the outer and all inner matrices are
Hermitian. -/
theorem weightedAdvGamma_isHermitian
    (g : ∀ i, X i → Bool) (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : ∀ i, Matrix (X i) (X i) ℂ)
    (hGf : Gf.IsHermitian) (hGg : ∀ i, (Gg i).IsHermitian) :
    (weightedAdvGamma g f Gf Gg).IsHermitian := by
  have hK : ∀ i, (Matrix.diagonal (fun _ : X i => (‖Gg i‖ : ℂ)) + Gg i).IsHermitian := by
    intro i
    apply Matrix.IsHermitian.add _ (hGg i)
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro x
    simp [IsSelfAdjoint]
  apply Matrix.IsHermitian.ext
  intro x y
  simp only [weightedAdvGamma, star_mul, star_prod]
  rw [mul_comm, hGf.apply]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact (hK i).apply (x i) (y i)

/-- If the outer matrix vanishes on equal outer outputs, the composed matrix vanishes on equal
composed outputs. -/
theorem weightedAdvGamma_same_output_zero
    (g : ∀ i, X i → Bool) (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : ∀ i, Matrix (X i) (X i) ℂ)
    (hzf : ∀ u v, f u = f v → Gf u v = 0)
    (x y : (i : Fin k) → X i)
    (hxy : f (fun i => g i (x i)) = f (fun i => g i (y i))) :
    weightedAdvGamma g f Gf Gg x y = 0 := by
  simp [weightedAdvGamma, hzf _ _ hxy]

/-- Hadamard multiplication by a fixed positive semidefinite matrix is monotone in the positive
semidefinite matrix order. -/
theorem weightedAdv_hadamard_mono {Y : Type} [Fintype Y]
    (B : Matrix Y Y ℂ) (hB : B.PosSemidef) : Monotone (fun A => Matrix.hadamard A B) := by
  intro A C hAC
  rw [Matrix.le_iff] at hAC ⊢
  have hPSD := hAC.hadamard hB
  have he : Matrix.hadamard (C - A) B = Matrix.hadamard C B - Matrix.hadamard A B := by
    ext i j
    simp [Matrix.hadamard, sub_mul]
  rw [he] at hPSD
  exact hPSD

/-- For Hermitian `G`, the shifted matrix `‖G‖ • 1 + G` is positive semidefinite. -/
theorem weightedAdv_factor_posSemidef {Y : Type} [Fintype Y] [DecidableEq Y]
    (G : Matrix Y Y ℂ) (hG : G.IsHermitian) :
    (diagonal (fun _ : Y => (‖G‖ : ℂ))+G).PosSemidef := by
  classical
  rcases isEmpty_or_nonempty Y with hY|hY
  · let := hY
    have he : diagonal (fun _ : Y => (‖G‖ : ℂ))+G=0 := by ext x; exact isEmptyElim x
    rw [he]
    exact Matrix.PosSemidef.zero
  · let := hY
    let : CStarAlgebra (Matrix Y Y ℂ) := {}
    have hself : IsSelfAdjoint G := Matrix.isHermitian_iff_isSelfAdjoint.mp hG
    have hb := IsSelfAdjoint.neg_algebraMap_norm_le_self (a := G) (ha := by exact hself)
    rw [Matrix.le_iff] at hb
    have hm : algebraMap ℝ (Matrix Y Y ℂ) ‖G‖=diagonal (fun _ : Y => (‖G‖ : ℂ)) := by
      ext x y
      simp [Algebra.algebraMap_eq_smul_one,Matrix.diagonal_apply,Matrix.one_apply,
        Matrix.smul_apply,Complex.real_smul]
    rw [hm] at hb
    simpa only [sub_neg_eq_add,add_comm] using hb

/-- The matrix formed by the product of the shifted inner-matrix entries is positive
semidefinite when every inner matrix is Hermitian. -/
theorem weightedAdv_product_posSemidef
    (Gg : ∀ i, Matrix (X i) (X i) ℂ) (hGg : ∀ i,(Gg i).IsHermitian) :
    Matrix.PosSemidef (fun x y : (i : Fin k) → X i =>
      ∏ i,(diagonal (fun _ : X i => (‖Gg i‖ : ℂ))+Gg i) (x i) (y i)) := by
  classical
  let K := fun i : Fin k =>
    (diagonal (fun _ : X i => (‖Gg i‖ : ℂ))+Gg i).submatrix (fun x : (j : Fin k) → X j => x i) (fun x : (j : Fin k) → X j => x i)
  have hk (i : Fin k) : (K i).PosSemidef :=
      (weightedAdv_factor_posSemidef (Gg i) (hGg i)).submatrix _
  have hp (s : Finset (Fin k)) : Matrix.PosSemidef (fun x y : (i : Fin k) → X i => ∏ i ∈ s,K i x y) := by
    induction s using Finset.induction_on with
    | empty =>
      simpa [Matrix.vecMulVec] using!
          Matrix.posSemidef_vecMulVec_self_star (fun _ : (i : Fin k) → X i => (1 : ℂ))
    | @insert i s hi ih =>
      have he : (fun x y : (i : Fin k) → X i => ∏ j ∈ insert i s,K j x y)=Matrix.hadamard (K i) (fun x y => ∏ j ∈ s,K j x y) := by
        ext x y
        simp [Finset.prod_insert hi,Matrix.hadamard]
      rw [he]
      exact (hk i).hadamard ih
  exact hp Finset.univ

/-- For Hermitian inner matrices vanishing on equal inner outputs, the composed matrix norm is
at most the outer norm times the product of inner norms. -/
theorem weightedAdvGamma_norm_le
    (g : ∀ i, X i → Bool) (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : ∀ i, Matrix (X i) (X i) ℂ)
    (hGg : ∀ i,(Gg i).IsHermitian)
    (hzg : ∀ (i : Fin k) (u v : X i),g i u=g i v → Gg i u v=0) :
    ‖weightedAdvGamma g f Gf Gg‖≤‖Gf‖*∏ i,‖Gg i‖ := by
  classical
  let B : Matrix ((i : Fin k) → X i) ((i : Fin k) → X i) ℂ := fun x y =>
    ∏ i,(diagonal (fun _ : X i => (‖Gg i‖ : ℂ))+Gg i) (x i) (y i)
  have hB : B.PosSemidef := weightedAdv_product_posSemidef Gg hGg
  obtain ⟨S,hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  have hgram : Sᴴ*S=B := by simpa only [Matrix.star_eq_conjTranspose] using hS.symm
  let e := fun x : (i : Fin k) → X i => fun i => g i (x i)
  let V := weightedAdvLift e S
  let r : ℝ := ∏ i,‖Gg i‖
  have hr : 0≤r := Finset.prod_nonneg (fun i _ => norm_nonneg (Gg i))
  have hVG : Vᴴ*V=diagonal (fun _ : (i : Fin k) → X i => (r : ℂ)) := by
    ext x y
    rw [weightedAdvLift_gram,hgram]
    by_cases hxy : x=y
    · subst y
      simp only [ite_true,Matrix.diagonal_apply_eq]
      change (∏ i,(diagonal (fun _ : X i => (‖Gg i‖ : ℂ))+Gg i) (x i) (x i))=(r : ℂ)
      simp only [Matrix.add_apply,Matrix.diagonal_apply_eq,hzg _ _ _ rfl,add_zero]
      simp only [r,Complex.ofReal_prod]
    · have hdiag : diagonal (fun _ : (i : Fin k) → X i => (r : ℂ)) x y=0 := by simp [hxy]
      rw [hdiag]
      split_ifs with he
      · obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
        have hg : g i (x i)=g i (y i) := congrArg (fun a => a i) he
        have hki : (diagonal (fun _ : X i => (‖Gg i‖ : ℂ))+Gg i) (x i) (y i)=0 := by
          simp [Matrix.add_apply,hi,hzg i _ _ hg]
        exact Finset.prod_eq_zero (Finset.mem_univ i) hki
      · rfl
  have hvn : ‖V‖*‖V‖≤r := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self,hVG,Matrix.l2_opNorm_diagonal,
      pi_norm_le_iff_of_nonneg hr]
    intro x
    exact (Complex.norm_of_nonneg hr).le
  have he : Vᴴ*TensorGate Gf (1 : Matrix ((i : Fin k) → X i) ((i : Fin k) → X i) ℂ)*V=
      weightedAdvGamma g f Gf Gg := by
    ext x y
    rw [weightedAdvLift_compression,hgram]
    rfl
  rw [← he]
  simpa only [r,mul_comm] using weightedAdv_compression_norm_le V Gf r hvn

omit [∀ i, DecidableEq (X i)] in

/-- Regroup a sum over block tuples by their Boolean output strings, factoring each output fiber
into a product of coordinate-fiber sums. -/
theorem weightedAdv_sum_by_outputs (g : ∀ i,X i → Bool)
    (a : (Fin k → Bool) → ℂ) (p : ∀ i,X i → ℂ) :
    (∑ y : (i : Fin k) → X i,a (fun i => g i (y i))*∏ i,p i (y i))=
      ∑ s : Fin k → Bool,a s*∏ i,∑ y : X i,if g i y=s i then p i y else 0 := by
  classical
  have hp (s : Fin k → Bool) (y : (i : Fin k) → X i) :
      (∏ i,if g i (y i)=s i then p i (y i) else 0)=
        (if (fun i => g i (y i))=s then (1 : ℂ) else 0)*(∏ i,p i (y i)) := by
    by_cases he : (fun i => g i (y i))=s
    · have hc (i : Fin k) : g i (y i)=s i := congrFun he i
      simp only [ite_eq_left he,ite_eq_left (hc _),one_mul]
    · have hz : (∏ i,if g i (y i)=s i then p i (y i) else 0)=0 := by
        obtain ⟨i,hi⟩ := Function.ne_iff.mp he
        exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
      rw [hz,ite_eq_right he,zero_mul]
  symm
  calc
    _ = ∑ s : Fin k → Bool,∑ y : (i : Fin k) → X i,
        a s*(∏ i,if g i (y i)=s i then p i (y i) else 0) := by
      simp_rw [Fintype.prod_sum,Finset.mul_sum]
    _ = ∑ y : (i : Fin k) → X i,∑ s : Fin k → Bool,
        a s*((if (fun i => g i (y i))=s then (1 : ℂ) else 0)*(∏ i,p i (y i))) := by
      rw [Finset.sum_comm]
      simp_rw [hp]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      simp [mul_ite]

/-- If `u` is a norm-eigenvalue eigenvector of an output-bipartite matrix `G`, summing the
action of `‖G‖ • 1 + G` over either output fiber gives `‖G‖ * u x` at every coordinate. -/
theorem weightedAdv_factor_fiber_action {Y : Type} [Fintype Y] [DecidableEq Y]
    (g : Y → Bool) (G : Matrix Y Y ℂ) (hz : ∀ x y,g x=g y → G x y=0)
    (u : QState Y) (he : G*ᵥu=(‖G‖ : ℂ) • u) (x : Y) (b : Bool) :
    (∑ y : Y,if g y=b then (diagonal (fun _ : Y => (‖G‖ : ℂ))+G) x y*u y else 0)=
      (‖G‖ : ℂ)*u x := by
  classical
  by_cases hxb : g x=b
  · have hp (y : Y) : (if g y=b then (diagonal (fun _ : Y => (‖G‖ : ℂ))+G) x y*u y else 0)=
        if y=x then (‖G‖ : ℂ)*u x else 0 := by
      by_cases hyb : g y=b
      · rw [ite_eq_left hyb,Matrix.add_apply,hz x y (hxb.trans hyb.symm),add_zero]
        by_cases hxy : x=y
        · subst y; simp
        · simp [hxy,Ne.symm hxy]
      · have hyx : y≠x := fun h => hyb (h ▸ hxb)
        simp [hyb,hyx]
    simp_rw [hp]
    simp
  · have hp (y : Y) : (if g y=b then (diagonal (fun _ : Y => (‖G‖ : ℂ))+G) x y*u y else 0)=G x y*u y := by
      by_cases hyb : g y=b
      · have hxy : x≠y := fun h => hxb (h ▸ hyb)
        simp [hyb,Matrix.add_apply,hxy]
      · have hxy : g x=g y := by
          cases b <;> cases hx : g x <;> cases hy : g y <;> simp_all
        rw [hz x y hxy]
        simp [hyb]
    simp_rw [hp]
    exact congrFun he x

/-- For Hermitian outer and inner matrices, output-bipartite inner matrices with positive norms
yield a nonzero composed eigenvector whose real eigenvalue has magnitude `‖Gf‖ * ∏ i, ‖Gg
i‖`. This is the product-eigenvector construction associated with [Hoyer, Lee, and Spalek,
Lemma 16][HoyerLeeSpalek2007]. -/
theorem weightedAdvGamma_product_eigenvector
    (g : ∀ i,X i → Bool) (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : ∀ i,Matrix (X i) (X i) ℂ) (hGf : Gf.IsHermitian)
    (hGg : ∀ i,(Gg i).IsHermitian)
    (hzg : ∀ (i : Fin k) (u v : X i),g i u=g i v → Gg i u v=0)
    (hpos : ∀ i,0<‖Gg i‖) :
    ∃ (w : QState ((i : Fin k) → X i)) (lam : ℝ),w≠0 ∧
      weightedAdvGamma g f Gf Gg*ᵥw=(lam : ℂ) • w ∧
      |lam|=‖Gf‖*∏ i,‖Gg i‖ := by
  classical
  let : ∀ i,Nonempty (X i) := fun i => weightedAdv_nonempty_of_norm_pos (Gg i) (hpos i)
  have hui (i : Fin k) : ∃ u : QState (X i),u≠0 ∧ Gg i*ᵥu=(‖Gg i‖ : ℂ) • u :=
    weightedAdv_positive_eigenvector (g i) (Gg i) (hGg i) (hzg i)
  choose ui hune hue using hui
  obtain ⟨uf,lamf,hnf,habsf,hef,_⟩ :=
      negative_adversary_extreme_eigenvector_and_start (Fin k → Bool) Unit Gf (Ket ()) hGf
      (by simp [Normalized,Ket])
  have huf : uf≠0 := by
    intro h0
    rw [h0] at hnf
    simp [Normalized] at hnf
  let e := fun x : (i : Fin k) → X i => fun i => g i (x i)
  let w : QState ((i : Fin k) → X i) := fun x => uf (e x)*∏ i,ui i (x i)
  let r : ℝ := ∏ i,‖Gg i‖
  have hw : w≠0 := by
    obtain ⟨s,hs⟩ := Function.ne_iff.mp huf
    have hx (i : Fin k) : ∃ y,g i y=s i ∧ ui i y≠0 :=
      weightedAdv_bipartite_fiber_nonzero (g i) (Gg i) (hzg i) (ui i) (hune i) (‖Gg i‖ : ℂ)
        (Complex.ofReal_ne_zero.mpr (hpos i).ne') (hue i) (s i)
    choose x hxg hxn using hx
    have hex : e x=s := funext hxg
    intro hw0
    have hz := congrFun hw0 x
    change uf (e x)*(∏ i,ui i (x i))=0 at hz
    rw [hex] at hz
    exact (mul_ne_zero hs (Finset.prod_ne_zero_iff.mpr (fun i _ => hxn i))) hz
  refine ⟨w,lamf*r,hw,?_,?_⟩
  · funext x
    change (∑ y : (i : Fin k) → X i,
      Gf (e x) (e y)*(∏ i,(diagonal (fun _ : X i => (‖Gg i‖ : ℂ))+Gg i) (x i) (y i))*(uf (e y)*∏ i,ui i (y i)))=
        ((lamf*r : ℝ) : ℂ)*(uf (e x)*∏ i,ui i (x i))
    calc
      _ = ∑ y : (i : Fin k) → X i,(Gf (e x) (e y)*uf (e y))*
          ∏ i,((diagonal (fun _ : X i => (‖Gg i‖ : ℂ))+Gg i) (x i) (y i)*ui i (y i)) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.prod_mul_distrib]
        ring
      _ = ∑ s : Fin k → Bool,(Gf (e x) s*uf s)*∏ i,(‖Gg i‖ : ℂ)*ui i (x i) := by
        have hsum := weightedAdv_sum_by_outputs g (fun s => Gf (e x) s*uf s)
          (fun i y => (diagonal (fun _ : X i => (‖Gg i‖ : ℂ))+Gg i) (x i) y*ui i y)
        change (∑ y : (i : Fin k) → X i,(Gf (e x) (fun i => g i (y i))*uf (fun i => g i (y i)))*
          ∏ i,((diagonal (fun _ : X i => (‖Gg i‖ : ℂ))+Gg i) (x i) (y i)*ui i (y i)))=_
        rw [hsum]
        simp_rw [weightedAdv_factor_fiber_action (g _) (Gg _) (hzg _) (ui _) (hue _)]
      _ = (∑ s : Fin k → Bool,Gf (e x) s*uf s)*∏ i,(‖Gg i‖ : ℂ)*ui i (x i) := by rw [Finset.sum_mul]
      _ = (lamf : ℂ)*uf (e x)*∏ i,(‖Gg i‖ : ℂ)*ui i (x i) := by
        have he := congrFun hef (e x)
        change (∑ s : Fin k → Bool,Gf (e x) s*uf s)=(lamf : ℂ)*uf (e x) at he
        rw [he]
      _ = _ := by
        simp only [Finset.prod_mul_distrib,r,Complex.ofReal_mul,Complex.ofReal_prod]
        ring
  · rw [abs_mul,abs_of_nonneg (Finset.prod_nonneg (fun i _ => norm_nonneg (Gg i))),habsf]

/-- For Hermitian outer and inner matrices with the inner same-output zero condition, the
composed matrix norm equals `‖Gf‖ * ∏ i, ‖Gg i‖`, as in [Hoyer, Lee, and Spalek, Lemma
16][HoyerLeeSpalek2007]. -/
theorem weightedAdvGamma_norm_eq
    (g : ∀ i,X i → Bool) (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : ∀ i,Matrix (X i) (X i) ℂ) (hGf : Gf.IsHermitian)
    (hGg : ∀ i,(Gg i).IsHermitian)
    (hzg : ∀ (i : Fin k) (u v : X i),g i u=g i v → Gg i u v=0) :
    ‖weightedAdvGamma g f Gf Gg‖=‖Gf‖*∏ i,‖Gg i‖ := by
  classical
  apply le_antisymm (weightedAdvGamma_norm_le g f Gf Gg hGg hzg)
  by_cases hpos : ∀ i,0<‖Gg i‖
  · obtain ⟨w,lam,hw,he,hn⟩ := weightedAdvGamma_product_eigenvector g f Gf Gg hGf hGg hzg hpos
    rw [← hn]
    exact weightedAdv_eigenvalue_norm_le _ w hw lam he
  · push Not at hpos
    obtain ⟨i,hi⟩ := hpos
    have hz : ‖Gg i‖=0 := le_antisymm hi (norm_nonneg _)
    have hp : (∏ j,‖Gg j‖)=0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
    rw [hp,mul_zero]
    exact norm_nonneg _

/-- On a nonempty product input domain, Hermitian outer and output-bipartite inner matrices
yield a nonzero composed eigenvector whose real eigenvalue has magnitude equal to the
product of the outer and inner norms. -/
theorem weightedAdvGamma_extreme_eigenvector
    (g : ∀ i,X i → Bool) (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : ∀ i,Matrix (X i) (X i) ℂ) [Nonempty ((i : Fin k) → X i)]
    (hGf : Gf.IsHermitian) (hGg : ∀ i,(Gg i).IsHermitian)
    (hzg : ∀ (i : Fin k) (u v : X i),g i u=g i v → Gg i u v=0) :
    ∃ (weight : QState ((i : Fin k) → X i)) (lam : ℝ),weight≠0 ∧
      weightedAdvGamma g f Gf Gg*ᵥweight=(lam : ℂ) • weight ∧
      |lam|=‖Gf‖*∏ i,‖Gg i‖ := by
  obtain ⟨w,lam,hw,hn,he,_⟩ := negative_adversary_extreme_eigenvector_and_start
    ((i : Fin k) → X i) Unit (weightedAdvGamma g f Gf Gg) (Ket ())
    (weightedAdvGamma_isHermitian g f Gf Gg hGf hGg) (by simp [Normalized,Ket])
  have hne : w≠0 := by
    intro h0
    rw [h0] at hw
    simp [Normalized] at hw
  exact ⟨w,lam,hne,he,hn.trans (weightedAdvGamma_norm_eq g f Gf Gg hGf hGg hzg)⟩

/-- Coordinate filtering preserves the Hermitian property of an adversary matrix. -/
theorem weightedAdvFilter_isHermitian {Y κ : Type} [DecidableEq κ]
    (input : Y → κ → Bool) (G : Matrix Y Y ℂ) (hG : G.IsHermitian) (c : κ) :
    (weightedAdvFilter input G c).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro x y
  by_cases h : input x c≠input y c
  · simp only [weightedAdvFilter,ite_eq_left h,ite_eq_left (Ne.symm h),hG.apply]
  · have he : input x c=input y c := not_ne_iff.mp h
    simp [weightedAdvFilter,he]

/-- Coordinate filtering preserves the condition that entries vanish on equal-output pairs. -/
theorem weightedAdvFilter_same_output_zero {Y κ : Type} [DecidableEq κ]
    (input : Y → κ → Bool) (g : Y → Bool) (G : Matrix Y Y ℂ)
    (hz : ∀ x y,g x=g y → G x y=0) (c : κ) (x y : Y) (he : g x=g y) :
    weightedAdvFilter input G c x y=0 := by
  simp [weightedAdvFilter,hz x y he]

/-- Filtering the composition at block `p`, coordinate `q`, equals composing the outer matrix
filtered at `p` with the inner family updated by filtering its `p`th matrix at `q`. -/
theorem weightedAdvGamma_filter_identity
    (g : ∀ i,X i → Bool) (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : ∀ i,Matrix (X i) (X i) ℂ)
    (gin : ∀ i,X i → Fin (n i) → Bool)
    (hzg : ∀ (i : Fin k) (u v : X i),g i u=g i v → Gg i u v=0)
    (p : Fin k) (q : Fin (n p)) :
    weightedAdvFilter (weightedAdvInput gin) (weightedAdvGamma g f Gf Gg) ⟨p,q⟩=
      weightedAdvGamma g f (advFilter id Gf p) (Function.update Gg p (advFilter (gin p) (Gg p) q)) := by
  classical
  let Gg' := Function.update Gg p (advFilter (gin p) (Gg p) q)
  let K := fun i => diagonal (fun _ : X i => (‖Gg i‖ : ℂ))+Gg i
  let K' := fun i => diagonal (fun _ : X i => (‖Gg' i‖ : ℂ))+Gg' i
  ext x y
  have hrest : (∏ i ∈ Finset.univ.erase p,K' i (x i) (y i))=
      ∏ i ∈ Finset.univ.erase p,K i (x i) (y i) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hip : i≠p := (Finset.mem_erase.mp hi).1
    simp only [K',K,Gg',Function.update_of_ne hip]
  have hprod : (∏ i,K i (x i) (y i))=K p (x p) (y p)*(∏ i ∈ Finset.univ.erase p,K i (x i) (y i)) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ p)).symm
  have hprod' : (∏ i,K' i (x i) (y i))=K' p (x p) (y p)*(∏ i ∈ Finset.univ.erase p,K i (x i) (y i)) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p),hrest]
  change (if gin p (x p) q≠gin p (y p) q then
      Gf (fun i => g i (x i)) (fun i => g i (y i))*(∏ i,K i (x i) (y i)) else 0)=
    (if g p (x p)≠g p (y p) then Gf (fun i => g i (x i)) (fun i => g i (y i)) else 0)*(∏ i,K' i (x i) (y i))
  rw [hprod,hprod']
  have hp' : K' p=diagonal (fun _ : X p => (‖advFilter (gin p) (Gg p) q‖ : ℂ))+advFilter (gin p) (Gg p) q := by
    simp only [K',Gg',Function.update_self]
  rw [hp']
  by_cases hb : gin p (x p) q=gin p (y p) q
  · have hfilter : advFilter (gin p) (Gg p) q (x p) (y p)=0 := by simp [advFilter,hb]
    by_cases hg : g p (x p)=g p (y p)
    · simp [hb,hg]
    · have hxy : x p≠y p := fun h => hg (h ▸ rfl)
      simp [hb,hg,Matrix.add_apply,hxy,hfilter]
  · have hxy : x p≠y p := fun h => hb (h ▸ rfl)
    have hK : K p (x p) (y p)=Gg p (x p) (y p) := by simp [K,Matrix.add_apply,hxy]
    rw [hK]
    by_cases hg : g p (x p)=g p (y p)
    · simp [hb,hg,hzg p _ _ hg]
    · simp [hb,hg,Matrix.add_apply,hxy,advFilter]

/-- Under the Hermitian and output-zero hypotheses, the composed filter norm at `(p, q)` equals
the outer filter norm at `p` times the inner filter norm at `q` times all other inner norms.
This supplies a norm identity for the composition argument of [HoyerLeeSpalek2007]. -/
theorem weightedAdvGamma_filter_norm_eq
    (g : ∀ i,X i → Bool) (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : ∀ i,Matrix (X i) (X i) ℂ) (gin : ∀ i,X i → Fin (n i) → Bool)
    (hGf : Gf.IsHermitian) (hGg : ∀ i,(Gg i).IsHermitian)
    (_hzf : ∀ u v,f u=f v → Gf u v=0)
    (hzg : ∀ (i : Fin k) (u v : X i),g i u=g i v → Gg i u v=0)
    (p : Fin k) (q : Fin (n p)) :
    ‖weightedAdvFilter (weightedAdvInput gin) (weightedAdvGamma g f Gf Gg) ⟨p,q⟩‖=
      ‖advFilter id Gf p‖*‖advFilter (gin p) (Gg p) q‖*∏ i ∈ Finset.univ.erase p,‖Gg i‖ := by
  classical
  let Gg' := Function.update Gg p (advFilter (gin p) (Gg p) q)
  have houter : (advFilter id Gf p).IsHermitian := weightedAdvFilter_isHermitian id Gf hGf p
  have hinner (i : Fin k) : (Gg' i).IsHermitian := by
    by_cases hip : i=p
    · subst i
      simpa only [Gg',Function.update_self] using!
          weightedAdvFilter_isHermitian (gin p) (Gg p) (hGg p) q
    · simpa only [Gg',Function.update_of_ne hip] using hGg i
  have hzero (i : Fin k) (x y : X i) (hg : g i x=g i y) : Gg' i x y=0 := by
    by_cases hip : i=p
    · subst i
      simpa only [Gg',Function.update_self] using!
          weightedAdvFilter_same_output_zero (gin p) (g p) (Gg p) (hzg p) q x y hg
    · simpa only [Gg',Function.update_of_ne hip] using hzg i x y hg
  rw [weightedAdvGamma_filter_identity g f Gf Gg gin hzg p q,
    weightedAdvGamma_norm_eq g f (advFilter id Gf p) Gg' houter hinner hzero]
  have hprod : (∏ i,‖Gg' i‖)=‖advFilter (gin p) (Gg p) q‖*(∏ i ∈ Finset.univ.erase p,‖Gg i‖) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
    simp only [Gg',Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [hprod]
  ring

/-- If every inner weighted norm ratio in block `p` is at least `β p` and all inner norms are
positive, each composed coordinate ratio is at least `β p` times the outer norm-to-filter
ratio. This is the witness inequality used in the composition framework of
[HoyerLeeSpalek2007]. -/
theorem weightedAdvGamma_composition_value
    (g : ∀ i,X i → Bool) (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : ∀ i,Matrix (X i) (X i) ℂ) (gin : ∀ i,X i → Fin (n i) → Bool)
    (hGf : Gf.IsHermitian) (hGg : ∀ i,(Gg i).IsHermitian)
    (hzf : ∀ u v,f u=f v → Gf u v=0)
    (hzg : ∀ (i : Fin k) (u v : X i),g i u=g i v → Gg i u v=0)
    (α : ∀ i,Fin (n i) → ℝ) (_hα : ∀ (i : Fin k) (q : Fin (n i)),0≤α i q)
    (hpos : ∀ i,0<‖Gg i‖) (β : Fin k → ℝ)
    (hβ : ∀ (p : Fin k) (q : Fin (n p)),β p≤α p q*‖Gg p‖/‖advFilter (gin p) (Gg p) q‖)
    (p : Fin k) (q : Fin (n p)) :
    α p q*‖weightedAdvGamma g f Gf Gg‖/
      ‖weightedAdvFilter (weightedAdvInput gin) (weightedAdvGamma g f Gf Gg) ⟨p,q⟩‖≥
        (‖Gf‖/‖advFilter id Gf p‖)*β p := by
  rw [weightedAdvGamma_norm_eq g f Gf Gg hGf hGg hzg,
    weightedAdvGamma_filter_norm_eq g f Gf Gg gin hGf hGg hzf hzg p q]
  have hp : (∏ i,‖Gg i‖)=‖Gg p‖*(∏ i ∈ Finset.univ.erase p,‖Gg i‖) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ p)).symm
  rw [hp]
  have hb := hβ p q
  by_cases hB : ‖advFilter id Gf p‖=0
  · simp [hB]
  · by_cases hbq : ‖advFilter (gin p) (Gg p) q‖=0
    · rw [hbq,div_zero] at hb
      have hr :=
          mul_nonpos_of_nonneg_of_nonpos
          (div_nonneg (norm_nonneg Gf) (norm_nonneg (advFilter id Gf p))) hb
      simpa only [hbq,mul_zero,zero_mul,div_zero] using hr
    · have hR : (∏ i ∈ Finset.univ.erase p,‖Gg i‖)≠0 :=
        ne_of_gt (Finset.prod_pos (fun i _ => hpos i))
      have he : α p q*(‖Gf‖*(‖Gg p‖*(∏ i ∈ Finset.univ.erase p,‖Gg i‖)))/
          (‖advFilter id Gf p‖*‖advFilter (gin p) (Gg p) q‖*(∏ i ∈ Finset.univ.erase p,‖Gg i‖))=
            (‖Gf‖/‖advFilter id Gf p‖)*(α p q*‖Gg p‖/‖advFilter (gin p) (Gg p) q‖) := by
        field_simp
      rw [he]
      exact mul_le_mul_of_nonneg_left hb
          (div_nonneg (norm_nonneg Gf) (norm_nonneg (advFilter id Gf p)))

/-- A normalized unitary circuit computing the composed Boolean function with error `eps` in
`[0, 1/2]` satisfies the adversary inequality with numerator `(1 - 2 * sqrt(eps * (1 -
eps))) * ‖Gf‖ * ∏ i, ‖Gg i‖` and the stated supremum of factored filter norms. This applies
the composition framework of [HoyerLeeSpalek2007] to the circuit's query count. -/
theorem weightedAdvGamma_actual_lower_bound
    (g : ∀ i,X i → Bool) (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : ∀ i,Matrix (X i) (X i) ℂ) (gin : ∀ i,X i → Fin (n i) → Bool)
    (hGf : Gf.IsHermitian) (hGg : ∀ i,(Gg i).IsHermitian)
    (hzf : ∀ u v,f u=f v → Gf u v=0)
    (hzg : ∀ (i : Fin k) (u v : X i),g i u=g i v → Gg i u v=0)
    (e : ((i : Fin k)×Fin (n i))≃Fin (∑ i,n i))
    (W : Type) [Fintype W] [DecidableEq W] [Nonempty ((i : Fin k) → X i)]
    (C : Circuit ((Fin (∑ i,n i)×Bool)×W))
    (psi : QState ((Fin (∑ i,n i)×Bool)×W))
    (E : Finset ((Fin (∑ i,n i)×Bool)×W))
    (eps : ℝ) (he0 : 0≤eps) (he1 : eps≤1/2)
    (hC : IsUnitaryCircuit C) (hpsi : Normalized psi)
    (hsuccess : ∀ x : (i : Fin k) → X i,1-eps≤MeasureProb
      (Run (workspaceBitOracle (W := W)
        (fun j => gin (e.symm j).1 (x (e.symm j).1) (e.symm j).2)) C psi)
      (if f (fun i => g i (x i)) then E else Eᶜ)) :
    (1-2*Real.sqrt (eps*(1-eps)))*(‖Gf‖*∏ i,‖Gg i‖)≤
      2*QueryCount C*(⨆ c : (i : Fin k)×Fin (n i),
        ‖advFilter id Gf c.1‖*‖advFilter (gin c.1) (Gg c.1) c.2‖*
          ∏ i ∈ Finset.univ.erase c.1,‖Gg i‖) := by
  classical
  let input := fun (x : (i : Fin k) → X i) (j : Fin (∑ i,n i)) =>
    gin (e.symm j).1 (x (e.symm j).1) (e.symm j).2
  let Gamma := weightedAdvGamma g f Gf Gg
  let h := fun x : (i : Fin k) → X i => f (fun i => g i (x i))
  have hg := weightedAdvGamma_isHermitian g f Gf Gg hGf hGg
  have hz : ∀ x y,h x=h y → Gamma x y=0 :=
      fun x y he => weightedAdvGamma_same_output_zero g f Gf Gg hzf x y he
  have hc := negative_adversary_actual_bounded_error_circuit_lower_bound
    ((i : Fin k) → X i) W (∑ i,n i) input Gamma h C psi E eps hg hz hC hpsi he0 he1 hsuccess
  let V := fun c : (i : Fin k)×Fin (n i) =>
    ‖advFilter id Gf c.1‖*‖advFilter (gin c.1) (Gg c.1) c.2‖*(∏ i ∈ Finset.univ.erase c.1,‖Gg i‖)
  let d : ℝ := ⨆ c,V c
  have hnepsi : psi≠0 := by
    intro h0
    rw [h0] at hpsi
    simp [Normalized] at hpsi
  obtain ⟨z,_hz⟩ := Function.ne_iff.mp hnepsi
  let : Nonempty ((i : Fin k)×Fin (n i)) := ⟨e.symm z.1.1⟩
  have hbdd : BddAbove (Set.range V) := Finite.bddAbove_range V
  have hv0 (c : (i : Fin k)×Fin (n i)) : 0≤V c := by
    apply mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    exact Finset.prod_nonneg (fun i _ => norm_nonneg _)
  have hd0 : 0≤d := (hv0 (Classical.arbitrary _)).trans (le_ciSup hbdd (Classical.arbitrary _))
  have hfilter (j : Fin (∑ i,n i)) : ‖advFilter input Gamma j‖≤d := by
    have hid : advFilter input Gamma j=weightedAdvFilter (weightedAdvInput gin) Gamma (e.symm j) :=
        rfl
    rw [hid]
    have heq :=
        weightedAdvGamma_filter_norm_eq g f Gf Gg gin hGf hGg hzf hzg (e.symm j).1 (e.symm j).2
    exact heq.trans_le (le_ciSup hbdd (e.symm j))
  have hfmax : advFilterBound input Gamma≤d := by
    have helper (l : List ℝ) (a : ℝ) (ha : a≤d) (hl : ∀ x∈l,x≤d) : l.foldl max a≤d := by
      induction l generalizing a with
      | nil => exact ha
      | cons b l ih =>
        apply ih (max a b) (max_le ha (hl b List.mem_cons_self))
        intro x hx
        exact hl x (List.mem_cons_of_mem _ hx)
    apply helper _ 0 hd0
    intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    exact hfilter j
  have hb := mul_le_mul_of_nonneg_left hfmax (by positivity : (0 : ℝ)≤2*QueryCount C)
  rw [weightedAdvGamma_norm_eq g f Gf Gg hGf hGg hzg] at hc
  exact hc.trans hb

omit [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)] in

/-- If any input block is empty, there is no nonzero state vector on the product input domain. -/
theorem weightedAdvGamma_no_nonzero_vector_of_empty_block
    (p : Fin k) [IsEmpty (X p)] :
    ¬ ∃ weight : QState ((i : Fin k) → X i), weight ≠ 0 := by
  rintro ⟨weight, hweight⟩
  apply hweight
  funext x
  exact isEmptyElim (x p)

/-- A one-block construction over `Empty` satisfies the Hermitian and inner output-zero
conditions but has no nonzero composed extreme eigenvector. -/
theorem weightedAdvGamma_empty_block_obstruction :
    let g : ∀ _i : Fin 1, Empty → Bool := fun _ _ => false
    let f : (Fin 1 → Bool) → Bool := fun _ => false
    let Gf : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ := 0
    let Gg : ∀ _i : Fin 1, Matrix Empty Empty ℂ := fun _ => 0
    Gf.IsHermitian ∧ (∀ i, (Gg i).IsHermitian) ∧
      (∀ (i : Fin 1) (u v : Empty), g i u = g i v → Gg i u v = 0) ∧
      ¬ ∃ (weight : QState ((i : Fin 1) → Empty)) (lam : ℝ), weight ≠ 0 ∧
        weightedAdvGamma g f Gf Gg *ᵥ weight = (lam : ℂ) • weight ∧
        |lam| = ‖Gf‖ * ∏ i, ‖Gg i‖ := by
  dsimp
  refine ⟨Matrix.isHermitian_zero, fun _ => Matrix.isHermitian_zero, ?_, ?_⟩
  · intro i u
    exact isEmptyElim u
  · rintro ⟨weight, lam, hweight, _⟩
    exact weightedAdvGamma_no_nonzero_vector_of_empty_block (X := fun _ : Fin 1 => Empty)
      0 ⟨weight, hweight⟩

/-- The unrestricted proposition that every Hermitian composition with output-bipartite inner
matrices possesses a nonzero eigenvector attaining the product of norms, without a
nonempty-domain hypothesis. -/
def WeightedAdvExtremeOriginalContract : Prop :=
  ∀ (k : ℕ) (X : Fin k → Type) [∀ i,Fintype (X i)] [∀ i,DecidableEq (X i)]
    (g : ∀ i,X i → Bool) (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : ∀ i,Matrix (X i) (X i) ℂ),Gf.IsHermitian → (∀ i,(Gg i).IsHermitian) →
    (∀ (i : Fin k) (u v : X i),g i u=g i v → Gg i u v=0) →
      ∃ (weight : QState ((i : Fin k) → X i)) (lam : ℝ),weight≠0 ∧
        weightedAdvGamma g f Gf Gg*ᵥweight=(lam : ℂ) • weight ∧
        |lam|=‖Gf‖*∏ i,‖Gg i‖

/-- The unrestricted extreme-eigenvector contract is false, as witnessed by the empty-block
construction. -/
theorem weightedAdvGamma_original_extreme_contract_false : ¬WeightedAdvExtremeOriginalContract := by
  intro h
  have hc := weightedAdvGamma_empty_block_obstruction
  dsimp only at hc
  have he := h 1 (fun _ : Fin 1 => Empty) (fun _ _ => false) (fun _ => false) 0 (fun _ => 0)
    hc.1 hc.2.1 hc.2.2.1
  exact hc.2.2.2 he

end Qatlib.Concepts.AdversaryBounds.WeightedAdvComp
