/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace
namespace Qatlib.Foundations.MatrixGeometry.TupleDeletion
variable {L : Type*} [Fintype L] [DecidableEq L]

abbrev Pair (L : Type*) := {xy : L×L // xy.1≠xy.2}

def entry (v : EuclideanSpace ℂ (Pair L)) (x y : L) : ℂ :=
  if h : x≠y then v ⟨(x,y),h⟩ else 0

def column (v : EuclideanSpace ℂ (Pair L)) (y : L) : ℂ := ∑ x,entry v x y

def row (v : EuclideanSpace ℂ (Pair L)) (x : L) : ℂ := ∑ y,entry v x y

def R (v : EuclideanSpace ℂ (Pair L)) : EuclideanSpace ℂ (Pair L) :=
  WithLp.toLp 2 (fun p => column v p.val.2)

def S (v : EuclideanSpace ℂ (Pair L)) : EuclideanSpace ℂ (Pair L) :=
  WithLp.toLp 2 (fun p => row v p.val.1)

def fibreSize (L : Type*) [Fintype L] : ℝ := (Fintype.card L : ℝ)-1

def P (v : EuclideanSpace ℂ (Pair L)) : EuclideanSpace ℂ (Pair L) :=
  (((fibreSize L)⁻¹ : ℝ) : ℂ) • R v

def Q (v : EuclideanSpace ℂ (Pair L)) : EuclideanSpace ℂ (Pair L) :=
  (((fibreSize L)⁻¹ : ℝ) : ℂ) • S v

theorem totals_eq (v : EuclideanSpace ℂ (Pair L)) : (∑ y,column v y) = ∑ x,row v x := by
  unfold column row
  exact Finset.sum_comm

theorem sum_pair {A : Type*} [AddCommMonoid A] (f : L→L→A) :
    (∑ p : Pair L,f p.val.1 p.val.2) = ∑ x,∑ y,if x≠y then f x y else 0 := by
  calc
    _ = ∑ xy ∈ Finset.univ.filter (fun xy : L×L => xy.1≠xy.2), f xy.1 xy.2 :=
      (Finset.sum_subtype (p := fun xy : L×L => xy.1≠xy.2)
        (Finset.univ.filter (fun xy : L×L => xy.1≠xy.2)) (by simp) (fun xy => f xy.1 xy.2)).symm
    _ = _ := by rw [Finset.sum_filter,Fintype.sum_prod_type]

theorem sum_pair_sub {A : Type*} [AddCommGroup A] (f : L→L→A) :
    (∑ p : Pair L,f p.val.1 p.val.2) = (∑ x,∑ y,f x y)-(∑ x,f x x) := by
  rw [sum_pair]
  apply (eq_sub_iff_add_eq).mpr
  have h (x : L) : (∑ y,if x≠y then f x y else 0)+f x x=∑ y,f x y := by
    calc
      _ = (∑ y,if x≠y then f x y else 0)+(∑ y,if x=y then f x y else 0) := by simp
      _ = ∑ y,((if x≠y then f x y else 0)+(if x=y then f x y else 0)) := Finset.sum_add_distrib.symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases he : x=y <;> simp [he]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => h x)

theorem cross_re_le (z w : ℂ) : 2*(star z*w).re ≤ Complex.normSq z+Complex.normSq w := by
  simp only [Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
  nlinarith [sq_nonneg (z.re-w.re),sq_nonneg (z.im-w.im)]

theorem balanced_cross (u w : L→ℂ) (hs : (∑ y,u y)=∑ x,w x) :
    -(∑ y,Complex.normSq (u y))-(∑ x,Complex.normSq (w x)) ≤
      2*(∑ p : Pair L,star (u p.val.2)*w p.val.1).re := by
  have he : (∑ p : Pair L,star (u p.val.2)*w p.val.1) =
      star (∑ y,u y)*(∑ x,w x)-(∑ x,star (u x)*w x) := by
    rw [sum_pair_sub (fun x y => star (u y)*w x)]
    congr 1
    rw [star_sum,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  have hpos : 0≤(star (∑ x,w x)*(∑ x,w x)).re := by
    simp only [Complex.star_def]
    rw [← Complex.normSq_eq_conj_mul_self]
    exact Complex.normSq_nonneg _
  have hdiag : 2*(∑ x,star (u x)*w x).re ≤
      (∑ x,Complex.normSq (u x))+(∑ x,Complex.normSq (w x)) := by
    change 2*Complex.reAddGroupHom (∑ x,star (u x)*w x) ≤ _
    rw [map_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun x _ => cross_re_le (u x) (w x))
  rw [he,hs,Complex.sub_re]
  linarith

theorem sum_pair_second (f : L→ℝ) : (∑ p : Pair L,f p.val.2)=fibreSize L*(∑ y,f y) := by
  rw [sum_pair_sub (fun _ y => f y)]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  unfold fibreSize
  ring

theorem sum_pair_first (f : L→ℝ) : (∑ p : Pair L,f p.val.1)=fibreSize L*(∑ x,f x) := by
  rw [sum_pair_sub (fun x _ => f x)]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [← Finset.mul_sum]
  unfold fibreSize
  ring

theorem norm_R_sq (v : EuclideanSpace ℂ (Pair L)) :
    ‖R v‖^2=fibreSize L*(∑ y,Complex.normSq (column v y)) := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ p : Pair L,‖column v p.val.2‖^2)=_
  simp_rw [← Complex.normSq_eq_norm_sq]
  exact sum_pair_second (fun y : L => Complex.normSq (column v y))

theorem norm_S_sq (v : EuclideanSpace ℂ (Pair L)) :
    ‖S v‖^2=fibreSize L*(∑ x,Complex.normSq (row v x)) := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ p : Pair L,‖row v p.val.1‖^2)=_
  simp_rw [← Complex.normSq_eq_norm_sq]
  exact sum_pair_first (fun x : L => Complex.normSq (row v x))

theorem inner_RS (v : EuclideanSpace ℂ (Pair L)) :
    inner ℂ (R v) (S v)=∑ p : Pair L,star (column v p.val.2)*row v p.val.1 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [RCLike.inner_apply']
  rfl

theorem unscaled_cross (v : EuclideanSpace ℂ (Pair L)) :
    -(∑ y,Complex.normSq (column v y))-(∑ x,Complex.normSq (row v x)) ≤
      2*(inner ℂ (R v) (S v)).re := by
  rw [inner_RS]
  exact balanced_cross _ _ (totals_eq v)
omit [DecidableEq L] in

theorem fibreSize_pos (hc : 2≤Fintype.card L) : 0<fibreSize L := by
  have h : (2:ℝ)≤Fintype.card L := by exact_mod_cast hc
  unfold fibreSize
  linarith

theorem norm_P_sq (v : EuclideanSpace ℂ (Pair L)) (hc : 2≤Fintype.card L) :
    ‖P v‖^2=(fibreSize L)⁻¹*(∑ y,Complex.normSq (column v y)) := by
  have ha := fibreSize_pos hc
  rw [P,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha),mul_pow,norm_R_sq]
  field_simp [ha.ne']

theorem norm_Q_sq (v : EuclideanSpace ℂ (Pair L)) (hc : 2≤Fintype.card L) :
    ‖Q v‖^2=(fibreSize L)⁻¹*(∑ x,Complex.normSq (row v x)) := by
  have ha := fibreSize_pos hc
  rw [Q,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha),mul_pow,norm_S_sq]
  field_simp [ha.ne']

theorem inner_PQ_re (v : EuclideanSpace ℂ (Pair L)) :
    (inner ℂ (P v) (Q v)).re=(fibreSize L)⁻¹^2*(inner ℂ (R v) (S v)).re := by
  rw [P,Q,inner_smul_left,inner_smul_right]
  simp only [Complex.conj_ofReal,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  ring

theorem pair_resampling_bound (v : EuclideanSpace ℂ (Pair L)) (hc : 2≤Fintype.card L) :
    -(1/fibreSize L)*(‖P v‖^2+‖Q v‖^2) ≤ 2*(inner ℂ (P v) (Q v)).re := by
  rw [norm_P_sq v hc,norm_Q_sq v hc,inner_PQ_re]
  have h := mul_le_mul_of_nonneg_left (unscaled_cross v) (sq_nonneg (fibreSize L)⁻¹)
  convert! h using 1 <;> ring

theorem sum_entry_second (v : EuclideanSpace ℂ (Pair L)) (f : L→ℂ) :
    (∑ p : Pair L,star (v p)*f p.val.2)=∑ y,star (column v y)*f y := by
  calc
    _ = ∑ p : Pair L,star (entry v p.val.1 p.val.2)*f p.val.2 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [entry,dif_pos p.property]
    _ = ∑ x,∑ y,if x≠y then star (entry v x y)*f y else 0 := sum_pair (fun x y : L => star (entry v x y)*f y)
    _ = ∑ x,∑ y,star (entry v x y)*f y := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : x≠y <;> simp [h,entry]
    _ = ∑ y,∑ x,star (entry v x y)*f y := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.sum_mul,← star_sum]
      rfl

theorem sum_entry_first (v : EuclideanSpace ℂ (Pair L)) (f : L→ℂ) :
    (∑ p : Pair L,star (v p)*f p.val.1)=∑ x,star (row v x)*f x := by
  calc
    _ = ∑ p : Pair L,star (entry v p.val.1 p.val.2)*f p.val.1 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [entry,dif_pos p.property]
    _ = ∑ x,∑ y,if x≠y then star (entry v x y)*f x else 0 := sum_pair (fun x y : L => star (entry v x y)*f x)
    _ = ∑ x,∑ y,star (entry v x y)*f x := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : x≠y <;> simp [h,entry]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_mul,← star_sum]
      rfl

theorem inner_R_re (v : EuclideanSpace ℂ (Pair L)) :
    (inner ℂ v (R v)).re=∑ y,Complex.normSq (column v y) := by
  have he : inner ℂ v (R v)=∑ p : Pair L,star (v p)*column v p.val.2 := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro p _
    rw [RCLike.inner_apply']
    rfl
  rw [he,sum_entry_second]
  change Complex.reAddGroupHom (∑ y,star (column v y)*column v y)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Complex.star_def]
  rw [← Complex.normSq_eq_conj_mul_self]
  rfl

theorem inner_S_re (v : EuclideanSpace ℂ (Pair L)) :
    (inner ℂ v (S v)).re=∑ x,Complex.normSq (row v x) := by
  have he : inner ℂ v (S v)=∑ p : Pair L,star (v p)*row v p.val.1 := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro p _
    rw [RCLike.inner_apply']
    rfl
  rw [he,sum_entry_first]
  change Complex.reAddGroupHom (∑ x,star (row v x)*row v x)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Complex.star_def]
  rw [← Complex.normSq_eq_conj_mul_self]
  rfl

theorem pair_resampling_unscaled (v : EuclideanSpace ℂ (Pair L)) :
    -(inner ℂ v (R v)).re-(inner ℂ v (S v)).re ≤ 2*(inner ℂ (R v) (S v)).re := by
  rw [inner_R_re,inner_S_re]
  exact unscaled_cross v

def RMatrix : Matrix (Pair L) (Pair L) ℂ := fun u v => if u.val.2=v.val.2 then 1 else 0

def SMatrix : Matrix (Pair L) (Pair L) ℂ := fun u v => if u.val.1=v.val.1 then 1 else 0

theorem R_matrix_apply (v : EuclideanSpace ℂ (Pair L)) (u : Pair L) :
    R v u=∑ q : Pair L,RMatrix u q*v q := by
  have h := sum_entry_second v (fun y => if u.val.2=y then 1 else 0)
  have he : (∑ q : Pair L,if u.val.2=q.val.2 then star (v q) else 0)=star (column v u.val.2) := by
    simpa [mul_ite] using h
  have hs := congrArg star he
  simpa only [R,RMatrix,star_sum,apply_ite,star_star,star_zero,ite_mul,one_mul,zero_mul] using
      hs.symm

theorem S_matrix_apply (v : EuclideanSpace ℂ (Pair L)) (u : Pair L) :
    S v u=∑ q : Pair L,SMatrix u q*v q := by
  have h := sum_entry_first v (fun x => if u.val.1=x then 1 else 0)
  have he : (∑ q : Pair L,if u.val.1=q.val.1 then star (v q) else 0)=star (row v u.val.1) := by
    simpa [mul_ite] using h
  have hs := congrArg star he
  simpa only [S,SMatrix,star_sum,apply_ite,star_star,star_zero,ite_mul,one_mul,zero_mul] using
      hs.symm

def PMatrix : Matrix (Pair L) (Pair L) ℂ :=
  fun u v => if u.val.2=v.val.2 then (((fibreSize L)⁻¹ : ℝ) : ℂ) else 0

def QMatrix : Matrix (Pair L) (Pair L) ℂ :=
  fun u v => if u.val.1=v.val.1 then (((fibreSize L)⁻¹ : ℝ) : ℂ) else 0

theorem PMatrix_entry (u v : Pair L) :
    PMatrix u v=if u.val.2=v.val.2 then (fibreSize L : ℂ)⁻¹ else 0 := by
  simp only [PMatrix,Complex.ofReal_inv]

theorem QMatrix_entry (u v : Pair L) :
    QMatrix u v=if u.val.1=v.val.1 then (fibreSize L : ℂ)⁻¹ else 0 := by
  simp only [QMatrix,Complex.ofReal_inv]

theorem P_matrix_apply (v : EuclideanSpace ℂ (Pair L)) (u : Pair L) :
    P v u=∑ q : Pair L,PMatrix u q*v q := by
  change (((fibreSize L)⁻¹ : ℝ) : ℂ)*R v u=_
  rw [R_matrix_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : u.val.2=q.val.2 <;> simp [PMatrix,RMatrix,h]

theorem Q_matrix_apply (v : EuclideanSpace ℂ (Pair L)) (u : Pair L) :
    Q v u=∑ q : Pair L,QMatrix u q*v q := by
  change (((fibreSize L)⁻¹ : ℝ) : ℂ)*S v u=_
  rw [S_matrix_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : u.val.1=q.val.1 <;> simp [QMatrix,SMatrix,h]

theorem R_eq_matrix (v : EuclideanSpace ℂ (Pair L)) : R v=Matrix.toEuclideanLin (RMatrix (L:=L)) v := by
  ext u
  exact R_matrix_apply v u

theorem S_eq_matrix (v : EuclideanSpace ℂ (Pair L)) : S v=Matrix.toEuclideanLin (SMatrix (L:=L)) v := by
  ext u
  exact S_matrix_apply v u

theorem P_eq_matrix (v : EuclideanSpace ℂ (Pair L)) : P v=Matrix.toEuclideanLin (PMatrix (L:=L)) v := by
  ext u
  exact P_matrix_apply v u

theorem Q_eq_matrix (v : EuclideanSpace ℂ (Pair L)) : Q v=Matrix.toEuclideanLin (QMatrix (L:=L)) v := by
  ext u
  exact Q_matrix_apply v u

theorem pair_resampling_matrix (v : EuclideanSpace ℂ (Pair L)) (hc : 2≤Fintype.card L) :
    -(1/fibreSize L)*(‖Matrix.toEuclideanLin (PMatrix (L:=L)) v‖^2+
      ‖Matrix.toEuclideanLin (QMatrix (L:=L)) v‖^2) ≤
        2*(inner ℂ (Matrix.toEuclideanLin (PMatrix (L:=L)) v) (Matrix.toEuclideanLin (QMatrix (L:=L)) v)).re := by
  rw [← P_eq_matrix v,← Q_eq_matrix v]
  exact pair_resampling_bound v hc

theorem pair_resampling_unscaled_matrix (v : EuclideanSpace ℂ (Pair L)) :
    -(inner ℂ v (Matrix.toEuclideanLin (RMatrix (L:=L)) v)).re-
      (inner ℂ v (Matrix.toEuclideanLin (SMatrix (L:=L)) v)).re ≤
        2*(inner ℂ (Matrix.toEuclideanLin (RMatrix (L:=L)) v) (Matrix.toEuclideanLin (SMatrix (L:=L)) v)).re := by
  rw [← R_eq_matrix v,← S_eq_matrix v]
  exact pair_resampling_unscaled v
end Qatlib.Foundations.MatrixGeometry.TupleDeletion
