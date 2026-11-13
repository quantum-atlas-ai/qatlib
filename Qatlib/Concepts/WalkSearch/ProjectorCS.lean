/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Qatlib.Concepts.WalkSearch.CountedWalk.CountedSzegedyAccess
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

/-!
# Unmarked principal matrices and walk gaps

`SymmetricChainGap` expresses a quadratic-form spectral gap for a symmetric transition matrix.
The module restricts the Szegedy row frame to unmarked states, identifies its swap Gram matrix
with the unmarked principal matrix, and bounds that matrix's norm by `1 - δ * markedFraction S`.

These constructions connect a classical chain gap and marked fraction to the walk geometry of
[Szegedy2004].

## Main statements

* `unmarkedRowFrame_swap_gram`: the restricted swap Gram identity.
* `symmetric_chain_unmarked_real_quadratic_upper`: the unmarked quadratic-form bound.
* `unmarked_principal_gram_and_gap`: combine isometry, Gram identity, and norm bound.

## References

* [Szegedy, 2004][Szegedy2004]
-/

open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Concepts.WalkSearch.ProjectorCS
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Kronecker Matrix.Norms.L2Operator

/-- The condition that `P` is a symmetric transition matrix and its quadratic form on zero-sum
real vectors is bounded by `1 - δ` times squared norm. -/
def SymmetricChainGap {I : Type} [Fintype I] (P : I→I→ℝ) (δ : ℝ) : Prop :=
  IsTransitionMatrix P ∧ (∀ i j,P i j= P j i) ∧
  ∀ v : I→ℝ,(∑ i,v i)=0 →
    (∑ i,∑ j,v i*P i j*v j)   ≤   (1-δ)*∑ i,(v i)^2
/-- The subtype of indices outside the marked finite set `S`. -/
abbrev Unmarked (I : Type) [DecidableEq I] (S : Finset I) := {i : I // i∉S}
/-- The Szegedy isometry matrix restricted to columns indexed by unmarked states. -/
noncomputable def unmarkedRowFrame {I : Type} [DecidableEq I] (P : I→I→ℝ) (S : Finset I) :
    Matrix (I×I) (Unmarked I S) ℂ := fun xy i=> SzegedyIsometry P xy i.1
/-- The complex-valued principal matrix obtained by restricting `P` to unmarked rows and
columns. -/
noncomputable def unmarkedPrincipal {I : Type} [DecidableEq I] (P : I→I→ℝ) (S : Finset I) :
    Matrix (Unmarked I S) (Unmarked I S) ℂ := fun i j=>(P i.1 j.1:ℂ)
/-- The real ratio of the marked-set cardinality to the total index cardinality. -/
noncomputable def markedFraction {I : Type} [Fintype I] (S : Finset I) : ℝ :=
  (S.card:ℝ)/(Fintype.card I:ℝ)

/-- Matrix multiplication with its finite-index multiplication instance supplied explicitly. -/
private noncomputable abbrev principalMul {M N K : Type} [Fintype N]
    (A : Matrix M N ℂ) (B : Matrix N K ℂ) : Matrix M K ℂ :=
  @HMul.hMul (Matrix M N ℂ) (Matrix N K ℂ) (Matrix M K ℂ)
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

/-- The explicitly instantiated matrix multiplication `principalMul` is associative. -/
private theorem principalMul_assoc {M N K L : Type} [Fintype N] [Fintype K]
    (A : Matrix M N ℂ) (B : Matrix N K ℂ) (C : Matrix K L ℂ) :
    principalMul (principalMul A B) C=principalMul A (principalMul B C) := Matrix.mul_assoc A B C

/-- Restricting the Szegedy row frame to unmarked columns preserves the isometry property for a
transition matrix. -/
theorem unmarkedRowFrame_isIsometry {I : Type} [Fintype I] [DecidableEq I]
    (P : I→I→ℝ) (S : Finset I) (hP : IsTransitionMatrix P) :
    IsIsometry (unmarkedRowFrame P S) := by
  unfold IsIsometry
  ext i j
  have he := congrFun (congrFun (szegedyIsometry_conjTranspose_mul P hP) i.1) j.1
  simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,unmarkedRowFrame,Matrix.one_apply,
    Subtype.val_inj] using! he

/-- For a symmetric transition matrix, the swap Gram matrix of the unmarked row frame equals the
unmarked principal matrix. -/
theorem unmarkedRowFrame_swap_gram {I : Type} [Fintype I] [DecidableEq I]
    (P : I→I→ℝ) (S : Finset I) (hP : IsTransitionMatrix P) (hs : ∀ i j,P i j=P j i) :
    (unmarkedRowFrame P S)ᴴ*(SwapGate : Matrix (I×I) (I×I) ℂ)*(unmarkedRowFrame P S)=unmarkedPrincipal P S := by
  change principalMul (principalMul (unmarkedRowFrame P S)ᴴ (SwapGate : Matrix (I×I) (I×I) ℂ))
      (unmarkedRowFrame P S)=unmarkedPrincipal P S
  ext i j
  have he := congrFun (congrFun (szegedy_gram_eq_discriminant P hP) i.1) j.1
  have hc : principalMul (principalMul (unmarkedRowFrame P S)ᴴ (SwapGate : Matrix (I×I) (I×I) ℂ)) (unmarkedRowFrame P S) i j =
      ((SzegedyIsometry P)ᴴ*SzegedyIsometryB P) i.1 j.1 := by
    rw [principalMul_assoc]
    simp only [principalMul,SzegedyIsometryB,Matrix.mul_apply,CStarMatrix.mul_apply,Matrix.conjTranspose_apply,unmarkedRowFrame]
  rw [hc,he]
  simp only [unmarkedPrincipal,SzegedyDiscriminant,Matrix.map_apply,Matrix.of_apply]
  rw [← hs i.1 j.1,← pow_two,Real.sqrt_sq (hP.1 i.1 j.1)]

/-- The unmarked principal matrix of a real symmetric matrix is Hermitian. -/
theorem unmarkedPrincipal_isHermitian {I : Type} [Fintype I] [DecidableEq I]
    (P : I→I→ℝ) (S : Finset I) (hs : ∀ i j,P i j=P j i) :
    (unmarkedPrincipal P S).IsHermitian := by
  change (unmarkedPrincipal P S)ᴴ=unmarkedPrincipal P S
  ext i j
  simp [unmarkedPrincipal,Matrix.conjTranspose_apply,hs]

/-- On a nonempty finite index type, the marked fraction lies between zero and one. -/
theorem markedFraction_mem_Icc {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Finset I) : markedFraction S∈Set.Icc 0 1 := by
  have hn : 0<(Fintype.card I : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨div_nonneg (Nat.cast_nonneg _) hn.le,?_⟩
  apply (div_le_iff₀ hn).mpr
  simpa only [one_mul] using!
      (show (S.card : ℝ)   ≤   (Fintype.card I : ℝ) by exact_mod_cast S.card_le_univ)

/-- The chain-gap condition bounds an arbitrary real quadratic form by `(1 - δ)` times squared
norm plus the stated squared-sum correction. -/
theorem symmetric_chain_real_quadratic_upper {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I→I→ℝ) (δ : ℝ) (h : SymmetricChainGap P δ) (v : I→ℝ) :
    (∑ i,∑ j,v i*P i j*v j)   ≤   (1-δ)*(∑ i,(v i)^2)+δ*(∑ i,v i)^2/(Fintype.card I : ℝ) := by
  let n : ℝ := Fintype.card I
  let m := (∑ i,v i)/n
  let z := fun i=>v i-m
  have hn : 0<n := Nat.cast_pos.mpr Fintype.card_pos
  have hrow (i : I) : (∑ j,P i j)=1 := h.1.2 i
  have hcol (j : I) : (∑ i,P i j)=1 := by simp only [h.2.1]; exact hrow j
  have hz : (∑ i,z i)=0 := by
    simp only [z,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
    change (∑ i,v i)-n*((∑ i,v i)/n)=0
    field_simp
    ring
  have hv (i : I) : v i=z i+m := by dsimp [z]; ring
  have hcross1 : (∑ i,∑ j,m*z i*P i j)=0 := by
    simp only [← Finset.mul_sum,hrow,mul_one,← Finset.mul_sum,hz,mul_zero]
  have hcross2 : (∑ i,∑ j,m*P i j*z j)=0 := by
    rw [Finset.sum_comm]
    have he (j : I) : (∑ i,m*P i j*z j)=m*z j*(∑ i,P i j) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    simp only [he,hcol,mul_one,← Finset.mul_sum,hz,mul_zero]
  have hconst : (∑ i,∑ j,m^2*P i j)=n*m^2 := by
    simp only [← Finset.mul_sum,hrow,mul_one,Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
    rfl
  have hquad : (∑ i,∑ j,v i*P i j*v j)=(∑ i,∑ j,z i*P i j*z j)+n*m^2 := by
    have he (i j : I) : v i*P i j*v j=
        z i*P i j*z j+m*z i*P i j+m*P i j*z j+m^2*P i j := by rw [hv i,hv j]; ring
    simp_rw [he]
    simp only [Finset.sum_add_distrib,hcross1,hcross2,hconst,add_zero]
  have hsquares : (∑ i,(v i)^2)=(∑ i,(z i)^2)+n*m^2 := by
    have he (i : I) : (v i)^2=(z i)^2+2*m*z i+m^2 := by rw [hv]; ring
    simp_rw [he]
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,hz,mul_zero,add_zero,Finset.sum_const,
      nsmul_eq_mul,Finset.card_univ]
    rfl
  have hmean : n*m^2=(∑ i,v i)^2/n := by dsimp [m]; field_simp
  have hgap := h.2.2 z hz
  rw [hquad,hsquares]
  change (∑ i,∑ j,z i*P i j*z j)+n*m^2   ≤   (1-δ)*((∑ i,(z i)^2)+n*m^2)+δ*(∑ i,v i)^2/n
  calc
    _   ≤   (1-δ)*(∑ i,(z i)^2)+n*m^2 := add_le_add hgap le_rfl
    _ = _ := by rw [mul_div_assoc,← hmean]; ring

/-- Extends a real function on unmarked indices by zero on the marked set. -/
private noncomputable def principalZeroExtend {I : Type} [DecidableEq I] (S : Finset I)
    (f : Unmarked I S→ℝ) : I→ℝ := fun i=>if h : i∉S then f ⟨i,h⟩ else 0

/-- Summing the zero extension over all indices equals summing the original function over
unmarked indices. -/
private theorem principalZeroExtend_sum {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (f : Unmarked I S→ℝ) :
    (∑ i,principalZeroExtend S f i)=∑ i : Unmarked I S,f i := by
  have hs := Finset.sum_subtype (F:=inferInstance) (p:=fun i : I=>i∉S)
    (Finset.univ.filter (fun i=>i∉S)) (by intro i; simp) (principalZeroExtend S f)
  have ht : (∑ i : Unmarked I S,principalZeroExtend S f i.1)=∑ i : Unmarked I S,f i := by
    apply Finset.sum_congr rfl; intro i _; simp only [principalZeroExtend,dif_pos i.2]
  rw [← ht,← hs]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi
  have hm : i∈S := by simpa using! hi
  simp [principalZeroExtend,hm]

/-- A weighted sum of the zero extension equals the corresponding weighted sum over unmarked
indices. -/
private theorem principalZeroExtend_weighted {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (f : Unmarked I S→ℝ) (c : I→ℝ) :
    (∑ i,c i*principalZeroExtend S f i)=∑ i : Unmarked I S,c i.1*f i := by
  have he (i : I) : c i*principalZeroExtend S f i=principalZeroExtend S (fun i=>c i.1*f i) i := by
    unfold principalZeroExtend; split_ifs <;> simp
  simp only [he,principalZeroExtend_sum]

/-- For a nonnegative gap parameter, the unmarked real quadratic form is at most `(1 - δ *
markedFraction S)` times squared norm. -/
theorem symmetric_chain_unmarked_real_quadratic_upper {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I→I→ℝ) (S : Finset I) (δ : ℝ) (hδ : 0  ≤  δ) (h : SymmetricChainGap P δ)
    (f : Unmarked I S→ℝ) :
    (∑ i : Unmarked I S,∑ j : Unmarked I S,f i*P i.1 j.1*f j)  ≤
      (1-δ*markedFraction S)*(∑ i : Unmarked I S,(f i)^2) := by
  let v := principalZeroExtend S f
  have hs := principalZeroExtend_sum S f
  have hv2 : (∑ i,(v i)^2)=∑ i : Unmarked I S,(f i)^2 := by
    have he (i : I) : (v i)^2=principalZeroExtend S (fun i=>(f i)^2) i := by
      unfold v principalZeroExtend; split_ifs <;> simp
    simp only [he,principalZeroExtend_sum]
  have hq : (∑ i,∑ j,v i*P i j*v j)=∑ i : Unmarked I S,∑ j : Unmarked I S,f i*P i.1 j.1*f j := by
    calc
      _ = ∑ i,v i*(∑ j,P i j*v j) := by simp only [Finset.mul_sum]; congr 1; funext i; apply Finset.sum_congr rfl; intro j _; ring
      _ = ∑ i,v i*(∑ j : Unmarked I S,P i j.1*f j) := by simp only [v,principalZeroExtend_weighted]
      _ = ∑ i : Unmarked I S,(∑ j : Unmarked I S,P i.1 j.1*f j)*f i := by
        simp only [mul_comm (v _)]; exact principalZeroExtend_weighted S f _
      _ = _ := by simp only [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  have hh := symmetric_chain_real_quadratic_upper P δ h v
  rw [hq,hv2] at hh
  change _  ≤
      (1-δ)*(∑ i : Unmarked I S,(f i)^2)+δ*(∑ i,principalZeroExtend S f i)^2/(Fintype.card I : ℝ) at hh
  rw [principalZeroExtend_sum] at hh
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Unmarked I S)) (fun _=>(1 : ℝ)) f
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,mul_one] at hc
  have hn : 0<(Fintype.card I : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hcard : Fintype.card (Unmarked I S)+S.card=Fintype.card I := by
    have he := Fintype.card_subtype_compl (fun i : I=>i∈S)
    simpa only [Unmarked,Fintype.card_coe,Nat.sub_add_cancel S.card_le_univ] using!
        congrArg (fun n=>n+S.card) he
  have hcardR : (Fintype.card (Unmarked I S) : ℝ)+(S.card : ℝ)=(Fintype.card I : ℝ) := by
    exact_mod_cast hcard
  have hscaled := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc hδ) hn.le
  have hbase := add_le_add (le_refl ((1-δ)*(∑ i : Unmarked I S,(f i)^2))) hscaled
  refine hh.trans (hbase.trans_eq ?_)
  unfold markedFraction
  field_simp
  rw [← hcardR]
  ring

/-- For entrywise nonnegative `P`, the norm of the unmarked complex quadratic form is bounded by
the quadratic sum of coordinate norms. -/
private theorem principal_complex_quadratic_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (P : I→I→ℝ) (S : Finset I) (hp : ∀ i j,0 ≤ P i j) (u : QState (Unmarked I S)) :
    ‖Qatlib.Foundations.PureStateMath.Inner u ((unmarkedPrincipal P S)*ᵥu)‖ ≤
      ∑ i : Unmarked I S,∑ j : Unmarked I S,‖u i‖*P i.1 j.1*‖u j‖ := by
  have he : Qatlib.Foundations.PureStateMath.Inner u ((unmarkedPrincipal P S)*ᵥu)=
      ∑ i : Unmarked I S,∑ j : Unmarked I S,star (u i)*(P i.1 j.1 : ℂ)*u j := by
    simp only [Qatlib.Foundations.PureStateMath.Inner,dotProduct,Pi.star_apply,Matrix.mulVec,unmarkedPrincipal,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  rw [he]
  calc
    _  ≤  ∑ i : Unmarked I S,‖∑ j : Unmarked I S,star (u i)*(P i.1 j.1 : ℂ)*u j‖ := norm_sum_le _ _
    _  ≤  ∑ i : Unmarked I S,∑ j : Unmarked I S,‖star (u i)*(P i.1 j.1 : ℂ)*u j‖ := by
      apply Finset.sum_le_sum; intro i _; exact norm_sum_le _ _
    _ = _ := by simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp _ _)]

/-- For `0 < δ ≤ 1` and `SymmetricChainGap P δ`, establishes the restricted-frame isometry, swap
Gram identity, and norm bound `1 - δ * markedFraction S`. -/
theorem unmarked_principal_gram_and_gap : ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I→I→ℝ) (S : Finset I) (δ : ℝ),0<δ → δ ≤ 1 → SymmetricChainGap P δ →
  IsIsometry (unmarkedRowFrame P S) ∧
  (unmarkedRowFrame P S)ᴴ*(SwapGate:Matrix (I×I) (I×I) ℂ)*(unmarkedRowFrame P S)= unmarkedPrincipal P S ∧
  ‖unmarkedPrincipal P S‖ ≤ 1-δ*markedFraction S := by
  intro I _ _ _ P S δ hδ hδ1 h
  refine ⟨unmarkedRowFrame_isIsometry P S h.1,unmarkedRowFrame_swap_gram P S h.1 h.2.1,?_⟩
  let M := unmarkedPrincipal P S
  let k := 1-δ*markedFraction S
  have hp := markedFraction_mem_Icc S
  have hk : 0 ≤ k := by
    have hh := mul_le_mul_of_nonneg_left hp.2 hδ.le
    dsimp [k]
    nlinarith only [hh,hδ1]
  have hM : M.IsHermitian := unmarkedPrincipal_isHermitian P S h.2.1
  have heig (i : Unmarked I S) : |hM.eigenvalues i| ≤ k := by
    let u : QState (Unmarked I S) := fun j=>hM.eigenvectorBasis i j
    have hun : ‖toEuclidean_fromVec u‖=1 := hM.eigenvectorBasis.norm_eq_one i
    have hnorm : Normalized u := (normalized_iff_norm_toEuclidean_fromVec _).mpr hun
    have hui : Qatlib.Foundations.PureStateMath.Inner u u=1 :=
        (normalized_iff_inner_self _).mp hnorm
    have hui' : star u ⬝ᵥ u=1 := hui
    have hact : M*ᵥu=(hM.eigenvalues i : ℂ) • u := hM.mulVec_eigenvectorBasis i
    have hquad : Qatlib.Foundations.PureStateMath.Inner u (M*ᵥu)=(hM.eigenvalues i : ℂ) := by
      rw [hact]
      simp only [Qatlib.Foundations.PureStateMath.Inner,dotProduct_smul,smul_eq_mul,hui',mul_one]
    have hh := (principal_complex_quadratic_norm_le P S h.1.1 u).trans
      (symmetric_chain_unmarked_real_quadratic_upper P S δ hδ.le h (fun i=>‖u i‖))
    rw [hquad,Complex.norm_real,Real.norm_eq_abs] at hh
    have hsum : (∑ i : Unmarked I S,‖u i‖^2)=1 := hnorm
    simpa only [hsum,mul_one] using! hh
  let U : Matrix (Unmarked I S) (Unmarked I S) ℂ := hM.eigenvectorUnitary
  let D := diagonal (fun i=>(hM.eigenvalues i : ℂ))
  have hU : U∈unitaryGroup (Unmarked I S) ℂ := hM.eigenvectorUnitary.property
  have hu : ‖U‖ ≤ 1 := l2_norm_unitary_le_one hU
  have hus : ‖Uᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hu
  have hd : ‖D‖ ≤ k := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg hk).mpr
    intro i
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact heig i
  have hs : M=U*D*Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,Function.comp_def] using!
        hM.spectral_theorem
  change ‖M‖ ≤ k
  rw [hs]
  have hb := (Matrix.l2_opNorm_mul (U*D) Uᴴ).trans
    (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul U D) (norm_nonneg Uᴴ))
  have hprod :=
      mul_le_mul (mul_le_mul hu hd (norm_nonneg D) (by norm_num)) hus (norm_nonneg Uᴴ)
      (by simpa only [one_mul] using! hk)
  exact hb.trans (by simpa only [one_mul,mul_one] using! hprod)

end Qatlib.Concepts.WalkSearch.ProjectorCS
