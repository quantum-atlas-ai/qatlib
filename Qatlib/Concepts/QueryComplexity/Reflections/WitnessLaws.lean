/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.SpanProgram
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.Reflections
open Matrix
open scoped Classical BigOperators

theorem source_fiber_norm (n m : ℕ) (b : Fin n → Bool) (u : Fin n → Fin m → ℂ) :
    (∑ p : IVert n m,‖if p.2.1=b p.1 then u p.1 p.2.2 else 0‖^2)=∑ j,∑ k,‖u j k‖^2 := by
  simp only [Fintype.sum_prod_type,Fintype.sum_bool]
  apply Finset.sum_congr rfl
  intro j _
  cases b j <;> simp

variable {X : Type} [Fintype X] [DecidableEq X] {n m : ℕ}

omit [Fintype X] [DecidableEq X] in

theorem source_available_overlap (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (x : X) (y : Fin0 X f) :
    (∑ p : IVert n m,bigA input f v y p*(if p.2.1=input x p.1 then v x p.1 p.2.2 else 0))=
      ∑ j : Fin n,if input y.val j≠input x j then Qatlib.Foundations.PureStateMath.Inner (v y.val j) (v x j) else 0 := by
  simp only [Fintype.sum_prod_type,Fintype.sum_bool]
  apply Finset.sum_congr rfl
  intro j _
  cases hy : input y.val j <;> cases hx :
      input x j <;> simp [bigA,hy,Qatlib.Foundations.PureStateMath.Inner,dotProduct]

omit [DecidableEq X] in

theorem source_positive_kernel (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (hd : SourceDualFeasible input f v W)
    (hW : 1 ≤ W) (x : X) (hx : f x=true) :
    sourceMarkedBiadj input f v W x*ᵥsourcePositiveWitness input f v W x=0 := by
  have hw : 0 < W := by linarith
  have hs : Real.sqrt W≠0 := ne_of_gt (Real.sqrt_pos.mpr hw)
  have ht (y : Fin0 X f) : tvec W y*((-3*Real.sqrt W : ℝ) : ℂ)=(-1 : ℂ) := by
    unfold tvec
    rw [← Complex.ofReal_mul]
    norm_cast
    field_simp [hs]
    norm_num
  unfold sourceMarkedBiadj
  rw [Matrix.fromCols_mulVec,Matrix.fromRows_mulVec,Matrix.fromRows_mulVec]
  ext p
  cases p with
  | inl y=>
    have ho:=source_available_overlap input f v x y
    have hc:=hd.2 y.val x y.property hx
    simp only [Pi.add_apply,Sum.elim_inl,Matrix.mulVec,dotProduct,Fintype.sum_unique]
    change tvec W y*((-3*Real.sqrt W : ℝ) : ℂ)+
      (∑ p : IVert n m,bigA input f v y p*(if p.2.1=input x p.1 then v x p.1 p.2.2 else 0))=0
    rw [ht,ho,hc]
    ring
  | inr p=>
    simp only [Pi.add_apply,Sum.elim_inr,Matrix.zero_mulVec,Pi.zero_apply,zero_add,
      sourcePixBar,Matrix.mulVec_diagonal]
    rcases p with ⟨j,b,k⟩
    cases hb : input x j <;> cases b <;> simp [sourcePositiveWitness,hb]

omit [Fintype X] [DecidableEq X] in

theorem source_positive_norm (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (hW : 0 ≤ W) (x : X) :
    (∑ c : ColLab X f n m,‖sourcePositiveWitness input f v W x c‖^2)=9*W+∑ j,∑ k,‖v x j k‖^2 := by
  simp only [Fintype.sum_sum_type,sourcePositiveWitness,Fintype.sum_unique]
  rw [source_fiber_norm,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,Real.sq_sqrt hW]
  norm_num

omit [Fintype X] [DecidableEq X] in

theorem source_positive_nonzero (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (hW : 1 ≤ W) (x : X) :
    sourcePositiveWitness input f v W x≠0 := by
  intro he
  have h:=congrFun he (Sum.inl ())
  have hs : 0 < Real.sqrt W := Real.sqrt_pos.mpr (by linarith)
  change ((-3*Real.sqrt W : ℝ) : ℂ)=0 at h
  have hr := Complex.ofReal_eq_zero.mp h
  nlinarith

theorem source_negative_kernel (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (x : X) (hx : f x=false) :
    (sourceRestrictedBiadj input f v x)ᴴ*ᵥsourceNegativeWitness input f v x=0 := by
  have hrow (p : IVert n m) :
      (∑ y : Fin0 X f,star (bigA input f v y p)*(if y.val=x then (-1 : ℂ) else 0))=
        -star (bigA input f v ⟨x,hx⟩ p) := by
    rw [Finset.sum_eq_single ⟨x,hx⟩]
    · simp
    · intro y _ hy
      have hv : y.val≠x := fun h=>hy (Subtype.ext h)
      simp [hv]
    · simp
  rw [sourceRestrictedBiadj,Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,Matrix.fromCols_mulVec]
  ext p
  change (∑ y : Fin0 X f,star (bigA input f v y p)*(if y.val=x then (-1 : ℂ) else 0))+
    ((sourcePixBar input x)ᴴ*ᵥ(fun q : IVert n m=>if q.2.1= !(input x q.1) then v x q.1 q.2.2 else 0)) p=0
  rw [hrow,sourcePixBar,Matrix.diagonal_conjTranspose,Matrix.mulVec_diagonal]
  by_cases hp : p.2.1= !(input x p.1) <;> simp [bigA,hp]

theorem source_negative_norm (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (x : X) (hx : f x=false) :
    (∑ r : RowLab X f n m,‖sourceNegativeWitness input f v x r‖^2)=1+∑ j,∑ k,‖v x j k‖^2 := by
  simp only [Fintype.sum_sum_type,sourceNegativeWitness]
  have hr : (∑ y : Fin0 X f,‖if y.val=x then (-1 : ℂ) else 0‖^2)=1 := by
    rw [Finset.sum_eq_single ⟨x,hx⟩]
    · simp
    · intro y _ hy
      have hv : y.val≠x := fun h=>hy (Subtype.ext h)
      simp [hv]
    · simp
  rw [hr]
  exact congrArg (fun z : ℝ=>1+z) (source_fiber_norm n m (fun j=>!(input x j)) (v x))

theorem source_negative_overlap (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (x : X) (hx : f x=false) :
    Qatlib.Foundations.PureStateMath.Inner (tvec W) (fun y=>sourceNegativeWitness input f v x (Sum.inl y))=
      -((1/(3*Real.sqrt W) : ℝ) : ℂ) := by
  unfold Qatlib.Foundations.PureStateMath.Inner dotProduct
  change (∑ y : Fin0 X f,star (tvec W y)*(if y.val=x then (-1 : ℂ) else 0))=_
  rw [Finset.sum_eq_single ⟨x,hx⟩]
  · simp [tvec]
  · intro y _ hy
    have hv : y.val≠x := fun h=>hy (Subtype.ext h)
    simp [hv]
  · simp

omit [Fintype X] in

theorem source_negative_nonzero (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (x : X) (hx : f x=false) :
    sourceNegativeWitness input f v x≠0 := by
  intro he
  have h:=congrFun he (Sum.inl ⟨x,hx⟩)
  norm_num [sourceNegativeWitness] at h
end Qatlib.Concepts.QueryComplexity.Reflections
