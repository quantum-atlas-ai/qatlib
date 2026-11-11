/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Find
import Mathlib.Data.Option.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.List.Nodup
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.List.FinRange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.List.Sort
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Data.List.Induction
import Mathlib.Data.List.ToFinsupp
import Mathlib.RingTheory.Polynomial.GaussLemma
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Sturm

set_option backward.isDefEq.respectTransparency false

/-! Exact polynomial-array algorithms: Projection.
Ported from OQ #132 at c0d79a391c008771dd64bd305ec2133c1b32c2d6,
retaining program bodies, guards, hypotheses and finite-fuel semantics. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
namespace RootYunInternal

namespace ActualProjectionSylvester
open Polynomial Matrix

/-- Construction for source Matrix in the projection model. -/
def sourceMatrix {R : Type} [CommRing R] (f g : R[X]) (m n : ℕ) :
    Matrix (Fin (m+n)) (Fin (m+n)) R :=
  fun i j => if i.val < n then
    if i.val ≤ j.val ∧ j.val ≤ i.val+m then f.coeff (m+i.val-j.val) else 0
  else
    if i.val-n ≤ j.val ∧ j.val ≤ i.val then g.coeff (i.val-j.val) else 0

/-- The finite construction in `Projection` satisfies `source_matrix_eq` under the displayed hypotheses. -/
theorem source_matrix_eq {R : Type} [CommRing R] (f g : R[X]) (m n : ℕ) :
    sourceMatrix f g m n=(f.sylvester g m n).transpose.submatrix Fin.rev Fin.rev := by
  ext i j
  by_cases hi : i.val < n
  · let u : Fin n := ⟨n-(i.val+1),by omega⟩
    have hie : Fin.rev i=Fin.natAdd m u := by apply Fin.ext; dsimp [u]; omega
    simp only [sourceMatrix,ite_eq_left hi,Matrix.submatrix_apply,Matrix.transpose_apply,
      Polynomial.sylvester,Matrix.of_apply,hie,Fin.addCases_right]
    dsimp only [u]
    simp only [Set.mem_Icc,Fin.val_rev]
    by_cases hj : i.val ≤ j.val ∧ j.val ≤ i.val+m
    · have hcond : n-(i.val+1) ≤ m+n-(j.val+1) ∧ m+n-(j.val+1) ≤ n-(i.val+1)+m := by omega
      rw [ite_eq_left hj,ite_eq_left hcond]
      congr 1
      omega
    · have hcond : ¬(n-(i.val+1) ≤ m+n-(j.val+1) ∧ m+n-(j.val+1) ≤ n-(i.val+1)+m) := by omega
      rw [ite_eq_right hj,ite_eq_right hcond]
  · let u : Fin m := ⟨m+n-(i.val+1),by omega⟩
    have hie : Fin.rev i=Fin.castAdd n u := by apply Fin.ext; rfl
    simp only [sourceMatrix,ite_eq_right hi,Matrix.submatrix_apply,Matrix.transpose_apply,
      Polynomial.sylvester,Matrix.of_apply,hie,Fin.addCases_left]
    dsimp only [u]
    simp only [Set.mem_Icc,Fin.val_rev]
    by_cases hj : i.val-n ≤ j.val ∧ j.val ≤ i.val
    · have hcond : m+n-(i.val+1) ≤ m+n-(j.val+1) ∧ m+n-(j.val+1) ≤ m+n-(i.val+1)+n := by omega
      rw [ite_eq_left hj,ite_eq_left hcond]
      congr 1
      omega
    · have hcond : ¬(m+n-(i.val+1) ≤ m+n-(j.val+1) ∧ m+n-(j.val+1) ≤ m+n-(i.val+1)+n) := by omega
      rw [ite_eq_right hj,ite_eq_right hcond]

/-- The finite construction in `Projection` satisfies `source_det_eq_resultant` under the displayed hypotheses. -/
theorem source_det_eq_resultant {R : Type} [CommRing R] (f g : R[X]) (m n : ℕ) :
    (sourceMatrix f g m n).det=f.resultant g m n := by
  rw [source_matrix_eq]
  change ((f.sylvester g m n).transpose.submatrix Fin.revPerm Fin.revPerm).det=_
  rw [Matrix.det_submatrix_equiv_self,Matrix.det_transpose]
  rfl

end ActualProjectionSylvester


namespace ActualProjectionRows
open ActualProjectionSylvester ActualYunRationalArray

/-- The finite construction in `Projection` satisfies `zero_getD` under the displayed hypotheses. -/
theorem zero_getD (n j : ℕ) : (List.replicate n (0 : ℚ)).getD j 0=0 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_replicate]
  split_ifs <;> rfl

/-- The finite construction in `Projection` satisfies `append_zeros_getD` under the displayed hypotheses. -/
theorem append_zeros_getD (a : List ℚ) (n j : ℕ) :
    (a++List.replicate n 0).getD j 0=a.getD j 0 := by
  by_cases hj : j<a.length
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hj]
  · have hh : a.length ≤ j := by omega
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right hh,
      List.getElem?_eq_none hh,Option.getD_none]
    exact zero_getD n (j-a.length)

/-- Construction for row in the projection model. -/
def row (a : List ℚ) (shift trailing : ℕ) : List ℚ :=
  List.replicate shift 0++a.reverse++List.replicate trailing 0

/-- The finite construction in `Projection` satisfies `row_getD` under the displayed hypotheses. -/
theorem row_getD (a : List ℚ) (m shift trailing j : ℕ) (hlen : a.length=m+1) :
    (row a shift trailing).getD j 0=
      if shift ≤ j ∧ j ≤ shift+m then a.getD (m+shift-j) 0 else 0 := by
  rw [row,append_zeros_getD]
  by_cases hj : j<shift
  · have he : j<(List.replicate shift (0 : ℚ)).length := by simpa only [List.length_replicate] using hj
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left he]
    have hcond : ¬(shift ≤ j ∧ j ≤ shift+m) := by omega
    rw [ite_eq_right hcond]
    exact zero_getD shift j
  · have he : (List.replicate shift (0 : ℚ)).length ≤ j := by simp only [List.length_replicate]; omega
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right he,List.length_replicate]
    by_cases hk : j-shift<a.length
    · have hcond : shift ≤ j ∧ j ≤ shift+m := by omega
      rw [ite_eq_left hcond,List.getElem?_reverse hk]
      have hi : a.length-1-(j-shift)=m+shift-j := by omega
      rw [hi]
    · have hcond : ¬(shift ≤ j ∧ j ≤ shift+m) := by omega
      rw [ite_eq_right hcond,List.getElem?_eq_none (by simp only [List.length_reverse]; omega)]
      rfl

/-- Construction for rows in the projection model. -/
def rows (a b : List ℚ) (m n : ℕ) : List (List ℚ) :=
  ((List.range n).map (fun j => row a j (n-1-j)))++
    ((List.range m).map (fun j => row b j (m-1-j)))

/-- The same emitted instruction list satisfies `rows_length` with the displayed gate and query accounting. -/
theorem rows_length (a b : List ℚ) (m n : ℕ) : (rows a b m n).length=m+n := by
  simp only [rows,List.length_append,List.length_map,List.length_range]
  omega


/-- Construction for list Matrix in the projection model. -/
def listMatrix (a b : List ℚ) (m n : ℕ) : Matrix (Fin (m+n)) (Fin (m+n)) ℚ :=
  fun i j => ((rows a b m n).getD i.val []).getD j.val 0

/-- The finite construction in `Projection` satisfies `rows_matrix_eq` under the displayed hypotheses. -/
theorem rows_matrix_eq (a b : List ℚ) (m n : ℕ) (ha : a.length=m+1) (hb : b.length=n+1) :
    listMatrix a b m n=sourceMatrix (poly a) (poly b) m n := by
  ext i j
  change ((rows a b m n).getD i.val []).getD j.val 0=_
  by_cases hi : i.val < n
  · have hil : i.val < ((List.range n).map (fun k => row a k (n-1-k))).length := by
      simpa only [List.length_map,List.length_range] using hi
    simp only [rows,List.getD_eq_getElem?_getD,List.getElem?_append_left hil,
      List.getElem?_map,List.getElem?_range hi,Option.map_some,Option.getD_some]
    change (row a i.val (n-1-i.val)).getD j.val 0=_
    rw [row_getD a m i.val (n-1-i.val) j.val ha]
    simp only [sourceMatrix,ite_eq_left hi,coeff]
  · have hin : n ≤ i.val := by omega
    have hil : ((List.range n).map (fun k => row a k (n-1-k))).length ≤ i.val := by
      simpa only [List.length_map,List.length_range] using hin
    have hik : i.val-n < m := by omega
    simp only [rows,List.getD_eq_getElem?_getD,List.getElem?_append_right hil,
      List.length_map,List.length_range,List.getElem?_map,List.getElem?_range hik,
      Option.map_some,Option.getD_some]
    change (row b (i.val-n) (m-1-(i.val-n))).getD j.val 0=_
    rw [row_getD b n (i.val-n) (m-1-(i.val-n)) j.val hb]
    simp only [sourceMatrix,ite_eq_right hi,coeff]
    have he1 : i.val-n+n=i.val := by omega
    have he2 : n+(i.val-n)=i.val := by omega
    rw [he1,he2]

/-- The finite construction in `Projection` satisfies `rows_det_eq_resultant` under the displayed hypotheses. -/
theorem rows_det_eq_resultant (a b : List ℚ) (m n : ℕ)
    (ha : a.length=m+1) (hb : b.length=n+1) :
    (listMatrix a b m n).det=(poly a).resultant (poly b) m n := by
  rw [rows_matrix_eq a b m n ha hb,source_det_eq_resultant]


-- Degree-dropping specialization must retain the symbolic m/n. For
-- evaluated constant 1 and X, padding with m=1 changes the determinant.


end ActualProjectionRows


namespace ActualProjectionSpecialization
open Polynomial ActualYunRationalArray ActualProjectionRows

/-- Construction for specialize Array in the projection model. -/
def specializeArray (F : Polynomial (Polynomial ℚ)) (m : ℕ) (t : ℚ) : List ℚ :=
  List.ofFn (fun i : Fin (m+1) => (F.coeff i.val).eval t)

/-- The finite construction in `Projection` satisfies `specialize_poly` under the displayed hypotheses. -/
theorem specialize_poly (F : Polynomial (Polynomial ℚ)) (m : ℕ) (t : ℚ)
    (hF : F.natDegree ≤ m) :
    poly (specializeArray F m t)=F.map (Polynomial.evalRingHom t) := by
  ext k
  by_cases hk : k < m+1
  · rw [ActualYunRationalArray.coeff,Polynomial.coeff_map]
    dsimp only [specializeArray]
    rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left hk]
    rfl
  · have hzero : F.coeff k=0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [ActualYunRationalArray.coeff,Polynomial.coeff_map,hzero]
    dsimp only [specializeArray]
    rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_right hk]
    simp only [map_zero,Option.getD_none]

/-- The finite construction in `Projection` satisfies `specialized_rows_det` under the displayed hypotheses. -/
theorem specialized_rows_det (F G : Polynomial (Polynomial ℚ)) (m n : ℕ) (t : ℚ)
    (hF : F.natDegree ≤ m) (hG : G.natDegree ≤ n) :
    (listMatrix (specializeArray F m t) (specializeArray G n t) m n).det=
      (F.resultant G m n).eval t := by
  rw [rows_det_eq_resultant _ _ m n (by simp only [specializeArray,List.length_ofFn]) (by simp only [specializeArray,List.length_ofFn]),
    specialize_poly F m t hF,specialize_poly G n t hG,Polynomial.resultant_map_map]
  rfl

end ActualProjectionSpecialization


namespace ActualProjectionGaussianHead
open Matrix

/-- Construction for sweep in the projection model. -/
def sweep {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  fun i j => if i=0 then A i j else if j=0 then 0 else A i j-(A i 0/A 0 0)*A 0 j

/-- Construction for trailing in the projection model. -/
def trailing {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => A i.succ j.succ-(A i.succ 0/A 0 0)*A 0 j.succ

/-- The finite construction in `Projection` satisfies `sweep_det` under the displayed hypotheses. -/
theorem sweep_det {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (hp : A 0 0≠0) :
    (sweep A).det=A.det := by
  apply Matrix.det_eq_of_forall_row_eq_smul_add_const (fun i => if i=0 then 0 else -(A i 0/A 0 0)) 0
  · simp
  · intro i j
    by_cases hi : i=0
    · simp only [sweep,ite_eq_left hi,zero_mul,add_zero]
    · by_cases hj : j=0
      · subst j
        simp only [sweep,ite_eq_right hi,ite_true]
        field_simp
        ring
      · simp only [sweep,ite_eq_right hi,ite_eq_right hj]
        ring

/-- The finite construction in `Projection` satisfies `first_column_det` under the displayed hypotheses. -/
theorem first_column_det {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (hz : ∀ i : Fin n,A i.succ 0=0) :
    A.det=A 0 0*(A.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero,Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,one_mul,Fin.succAbove_zero,hz,mul_zero,zero_mul,
    Finset.sum_const_zero,add_zero]

/-- The finite construction in `Projection` satisfies `schur_det` under the displayed hypotheses. -/
theorem schur_det {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (hp : A 0 0≠0) :
    A.det=A 0 0*(trailing A).det := by
  rw [← sweep_det A hp,first_column_det (sweep A) (by intro i; simp [sweep])]
  rfl

/-- Construction for swap Rows in the projection model. -/
def swapRows {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (p : Fin (n+1)) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℚ := A.submatrix (Equiv.swap 0 p) id

/-- Construction for swap Sign in the projection model. -/
def swapSign {n : ℕ} (p : Fin (n+1)) : ℚ := if p=0 then 1 else -1

/-- The finite construction in `Projection` satisfies `swap_pivot` under the displayed hypotheses. -/
theorem swap_pivot {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (p : Fin (n+1)) :
    swapRows A p 0 0=A p 0 := by simp [swapRows]

/-- The finite construction in `Projection` satisfies `swap_det` under the displayed hypotheses. -/
theorem swap_det {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (p : Fin (n+1)) :
    (swapRows A p).det=swapSign p*A.det := by
  rw [swapRows,Matrix.det_permute]
  by_cases hp : p=0
  · subst p
    simp [swapSign]
  · simp [swapSign,hp,Equiv.Perm.sign_swap (Ne.symm hp)]

/-- The finite construction in `Projection` satisfies `pivot_schur_det` under the displayed hypotheses. -/
theorem pivot_schur_det {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (p : Fin (n+1)) (hp : A p 0≠0) :
    A.det=swapSign p*(swapRows A p 0 0)*(trailing (swapRows A p)).det := by
  have hpn : swapRows A p 0 0≠0 := by rw [swap_pivot]; exact hp
  have hh := schur_det (swapRows A p) hpn
  rw [swap_det] at hh
  by_cases hp0 : p=0
  · simp only [swapSign,ite_eq_left hp0,one_mul] at hh ⊢
    exact hh
  · simp only [swapSign,ite_eq_right hp0,neg_one_mul] at hh ⊢
    linarith

end ActualProjectionGaussianHead


namespace ActualProjectionGaussianCore
open Matrix ActualProjectionGaussianHead

/-- Construction for pivot in the projection model. -/
def pivot {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) : Option (Fin (n+1)) :=
  (List.finRange (n+1)).find? (fun i => decide (A i 0≠0))

/-- The finite construction in `Projection` satisfies `pivot_some` under the displayed hypotheses. -/
theorem pivot_some {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (p : Fin (n+1))
    (hp : pivot A=some p) : A p 0≠0 := by
  have hh : decide (A p 0≠0)=true := List.find?_some (p:=fun i => decide (A i 0≠0)) hp
  exact of_decide_eq_true hh

/-- The finite construction in `Projection` satisfies `pivot_none` under the displayed hypotheses. -/
theorem pivot_none {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (hp : pivot A=none) : ∀ i,A i 0=0 := by
  have hh := List.find?_eq_none.mp hp
  intro i
  have hi := hh i (by simp)
  simpa only [decide_eq_true_eq,not_not] using hi

/-- Construction for gauss in the projection model. -/
def gauss : (n : ℕ) → Matrix (Fin n) (Fin n) ℚ → ℚ
  | 0,_ => 1
  | n+1,A => match pivot A with
    | none => 0
    | some p => swapSign p*(swapRows A p 0 0)*gauss n (trailing (swapRows A p))

/-- The finite construction in `Projection` satisfies `gauss_eq_det` under the displayed hypotheses. -/
theorem gauss_eq_det (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) : gauss n A=A.det := by
  induction n with
  | zero => simp only [gauss,Matrix.det_isEmpty]
  | succ n ih =>
    cases hp : pivot A with
    | none =>
      rw [gauss,hp]
      exact (Matrix.det_eq_zero_of_column_eq_zero 0 (pivot_none A hp)).symm
    | some p =>
      simp only [gauss,hp]
      rw [ih]
      exact (pivot_schur_det A p (pivot_some A p hp)).symm

/-- Construction for gauss Acc in the projection model. -/
def gaussAcc : (n : ℕ) → Matrix (Fin n) (Fin n) ℚ → ℚ → ℚ
  | 0,_,value => value
  | n+1,A,value => match pivot A with
    | none => 0
    | some p =>
      let B := swapRows A p
      gaussAcc n (trailing B) ((if p=0 then value else -value)*B 0 0)

/-- The finite construction in `Projection` satisfies `gaussAcc_eq` under the displayed hypotheses. -/
theorem gaussAcc_eq (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (value : ℚ) :
    gaussAcc n A value=value*A.det := by
  induction n generalizing value with
  | zero => simp only [gaussAcc,Matrix.det_isEmpty,mul_one]
  | succ n ih =>
    cases hp : pivot A with
    | none =>
      rw [gaussAcc,hp,Matrix.det_eq_zero_of_column_eq_zero 0 (pivot_none A hp),mul_zero]
    | some p =>
      simp only [gaussAcc,hp]
      rw [ih,pivot_schur_det A p (pivot_some A p hp)]
      by_cases hz : p=0
      · simp only [swapSign,ite_eq_left hz,one_mul]
        ring
      · simp only [swapSign,ite_eq_right hz,neg_one_mul]
        ring



end ActualProjectionGaussianCore


namespace ActualProjectionGaussianCells
open Matrix

/-- Construction for write Cell in the projection model. -/
def writeCell {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (k t : Fin N) (v : ℚ) :
    Matrix (Fin N) (Fin N) ℚ := A.updateRow k (Function.update (A k) t v)

/-- The finite construction in `Projection` satisfies `writeCell_apply` under the displayed hypotheses. -/
theorem writeCell_apply {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (k t i j : Fin N) (v : ℚ) :
    writeCell A k t v i j=if i=k ∧ j=t then v else A i j := by
  by_cases hi : i=k <;> by_cases hj : j=t <;> simp [writeCell,Matrix.updateRow_apply,hi,hj]

/-- Construction for columns in the projection model. -/
def columns {N : ℕ} (p k : Fin N) (ratio : ℚ) : List (Fin N) →
    Matrix (Fin N) (Fin N) ℚ → Matrix (Fin N) (Fin N) ℚ
  | [],A => A
  | t::ts,A => columns p k ratio ts (writeCell A k t (A k t-ratio*A p t))

/-- The finite construction in `Projection` satisfies `columns_apply` under the displayed hypotheses. -/
theorem columns_apply {N : ℕ} (p k : Fin N) (ratio : ℚ)
    (ts : List (Fin N)) (hts : ts.Nodup) (A : Matrix (Fin N) (Fin N) ℚ) (i j : Fin N) :
    columns p k ratio ts A i j=
      if i=k ∧ j∈ts then A i j-ratio*A p j else A i j := by
  induction ts generalizing A with
  | nil => simp [columns]
  | cons t ts ih =>
    have hnot : t∉ts := (List.nodup_cons.mp hts).1
    have htail : ts.Nodup := (List.nodup_cons.mp hts).2
    rw [columns,ih htail]
    by_cases hi : i=k
    · subst i
      by_cases hjt : j=t
      · subst j
        simp only [writeCell_apply,and_true]
        simp [hnot]
      · by_cases hj : j∈ts
        · simp [writeCell_apply,hjt,hj]
        · simp [writeCell_apply,hjt,hj]
    · simp [writeCell_apply,hi]

/-- Construction for eliminate Row in the projection model. -/
def eliminateRow {N : ℕ} (p k : Fin N) (ts : List (Fin N))
    (A : Matrix (Fin N) (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ :=
  if A k p=0 then A else
    let ratio := A k p/A p p
    let B := columns p k ratio ts A
    writeCell B k p 0

/-- The finite construction in `Projection` satisfies `eliminateRow_apply` under the displayed hypotheses. -/
theorem eliminateRow_apply {N : ℕ} (p k : Fin N)
    (ts : List (Fin N)) (hts : ts.Nodup) (hp : p∉ts)
    (A : Matrix (Fin N) (Fin N) ℚ) (i j : Fin N) :
    eliminateRow p k ts A i j=
      if i=k then
        if j=p then 0 else if j∈ts then A i j-(A k p/A p p)*A p j else A i j
      else A i j := by
  by_cases hz : A k p=0
  · rw [eliminateRow,ite_eq_left hz]
    by_cases hi : i=k
    · subst i
      by_cases hj : j=p
      · subst j; simp [hz]
      · simp [hj,hz]
    · simp [hi]
  · rw [eliminateRow,ite_eq_right hz,writeCell_apply,columns_apply p k _ ts hts]
    by_cases hi : i=k <;> by_cases hj : j=p <;> simp [hi,hj,hp]

end ActualProjectionGaussianCells


namespace ActualProjectionGaussianRows
open Matrix ActualProjectionGaussianCells

/-- Construction for eliminate Rows in the projection model. -/
def eliminateRows {N : ℕ} (p : Fin N) (ts : List (Fin N)) : List (Fin N) →
    Matrix (Fin N) (Fin N) ℚ → Matrix (Fin N) (Fin N) ℚ
  | [],A => A
  | k::ks,A => eliminateRows p ts ks (eliminateRow p k ts A)

/-- The finite construction in `Projection` satisfies `eliminateRows_apply` under the displayed hypotheses. -/
theorem eliminateRows_apply {N : ℕ} (p : Fin N) (ts ks : List (Fin N))
    (hts : ts.Nodup) (hpt : p∉ts) (hks : ks.Nodup) (hpk : p∉ks)
    (A : Matrix (Fin N) (Fin N) ℚ) (i j : Fin N) :
    eliminateRows p ts ks A i j=
      if i∈ks then
        if j=p then 0 else if j∈ts then A i j-(A i p/A p p)*A p j else A i j
      else A i j := by
  induction ks generalizing A with
  | nil => simp only [eliminateRows,List.not_mem_nil,ite_false]
  | cons k ks ih =>
    have hnot : k∉ks := (List.nodup_cons.mp hks).1
    have htail : ks.Nodup := (List.nodup_cons.mp hks).2
    have hpk' : p≠k := by intro he; subst k; exact hpk (by simp)
    have hptail : p∉ks := by intro hp; exact hpk (by simp only [List.mem_cons]; exact Or.inr hp)
    rw [eliminateRows,ih htail hptail]
    by_cases hi : i=k
    · subst i
      simp only [ite_eq_right hnot]
      rw [eliminateRow_apply p k ts hts hpt]
      simp
    · by_cases him : i∈ks
      · simp [eliminateRow_apply p k ts hts hpt,hi,hpk',him]
      · simp [eliminateRow_apply p k ts hts hpt,hi,him]

end ActualProjectionGaussianRows


namespace ActualProjectionGaussianEmbedding
open Matrix ActualProjectionGaussianHead ActualProjectionGaussianRows ActualProjectionGaussianCore

/-- Construction for remaining in the projection model. -/
def remaining {N n : ℕ} (e : Fin (n+1) → Fin N) : List (Fin N) :=
  List.ofFn (fun i : Fin n => e i.succ)

/-- Construction for swap Full in the projection model. -/
def swapFull {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (p q : Fin N) :
    Matrix (Fin N) (Fin N) ℚ := A.submatrix (Equiv.swap p q) id

/-- The finite construction in `Projection` satisfies `swap_project` under the displayed hypotheses. -/
theorem swap_project {N n : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (e : Fin (n+1) → Fin N) (he : Function.Injective e) (p : Fin (n+1)) :
    (swapFull A (e 0) (e p)).submatrix e e=swapRows (A.submatrix e e) p := by
  ext i j
  change A (Equiv.swap (e 0) (e p) (e i)) (e j)=A (e (Equiv.swap 0 p i)) (e j)
  rw [he.swap_apply]

/-- The finite construction in `Projection` satisfies `remaining_nodup` under the displayed hypotheses. -/
theorem remaining_nodup {N n : ℕ} (e : Fin (n+1) → Fin N) (he : Function.Injective e) :
    (remaining e).Nodup := List.nodup_ofFn.mpr (he.comp (Fin.succ_injective n))

/-- The finite construction in `Projection` satisfies `head_not_remaining` under the displayed hypotheses. -/
theorem head_not_remaining {N n : ℕ} (e : Fin (n+1) → Fin N) (he : Function.Injective e) :
    e 0∉remaining e := by
  simp only [remaining,List.mem_ofFn]
  rintro ⟨i,hi⟩
  exact Fin.succ_ne_zero i (he hi)

/-- The finite construction in `Projection` satisfies `remaining_mem` under the displayed hypotheses. -/
theorem remaining_mem {N n : ℕ} (e : Fin (n+1) → Fin N) (i : Fin n) :
    e i.succ∈remaining e := List.mem_ofFn.mpr ⟨i,rfl⟩

/-- The finite construction in `Projection` satisfies `eliminate_project` under the displayed hypotheses. -/
theorem eliminate_project {N n : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (e : Fin (n+1) → Fin N) (he : Function.Injective e) :
    (eliminateRows (e 0) (remaining e) (remaining e) A).submatrix
      (fun i : Fin n => e i.succ) (fun j : Fin n => e j.succ)=trailing (A.submatrix e e) := by
  ext i j
  change eliminateRows (e 0) (remaining e) (remaining e) A (e i.succ) (e j.succ)=_
  rw [eliminateRows_apply (e 0) (remaining e) (remaining e) (remaining_nodup e he)
    (head_not_remaining e he) (remaining_nodup e he) (head_not_remaining e he),ite_eq_left (remaining_mem e i)]
  have hj : e j.succ≠e 0 := fun h => Fin.succ_ne_zero j (he h)
  rw [ite_eq_right hj,ite_eq_left (remaining_mem e j)]
  rfl

/-- Construction for first Pivot in the projection model. -/
def firstPivot {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (p : Fin N)
    (ids : List (Fin N)) : Option (Fin N) := ids.find? (fun i => decide (A i p≠0))

/-- The finite construction in `Projection` satisfies `pivot_project` under the displayed hypotheses. -/
theorem pivot_project {N n : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (e : Fin (n+1) → Fin N) :
    firstPivot A (e 0) (List.ofFn e)=(pivot (A.submatrix e e)).map e := by
  have hmap : List.ofFn e=(List.finRange (n+1)).map e := by simp only [List.finRange,List.map_ofFn]; rfl
  rw [firstPivot,hmap,List.find?_map]
  rfl

end ActualProjectionGaussianEmbedding


namespace ActualProjectionGaussianLoop
open Matrix ActualProjectionGaussianHead ActualProjectionGaussianCells
open ActualProjectionGaussianRows ActualProjectionGaussianCore ActualProjectionGaussianEmbedding

/-- Construction for source Loop in the projection model. -/
def sourceLoop {N : ℕ} : List (Fin N) → Matrix (Fin N) (Fin N) ℚ → ℚ → ℚ
  | [],_,value => value
  | p::ps,A,value => match firstPivot A p (p::ps) with
    | none => 0
    | some q =>
      let B := swapFull A p q
      let value' := (if q=p then value else -value)*B p p
      let C := eliminateRows p ps ps B
      sourceLoop ps C value'

/-- The finite construction in `Projection` satisfies `loop_project` under the displayed hypotheses. -/
theorem loop_project {N : ℕ} (n : ℕ) (e : Fin n → Fin N) (he : Function.Injective e)
    (A : Matrix (Fin N) (Fin N) ℚ) (value : ℚ) :
    sourceLoop (List.ofFn e) A value=gaussAcc n (A.submatrix e e) value := by
  induction n generalizing A value with
  | zero => simp only [List.ofFn_zero,sourceLoop,gaussAcc]
  | succ n ih =>
    have hp : firstPivot A (e 0) (e 0::remaining e)=(pivot (A.submatrix e e)).map e := by
      have hh := pivot_project A e
      simpa only [List.ofFn_succ,remaining] using hh
    rw [List.ofFn_succ]
    change (match firstPivot A (e 0) (e 0::remaining e) with
      | none => 0
      | some q => sourceLoop (remaining e)
        (eliminateRows (e 0) (remaining e) (remaining e) (swapFull A (e 0) q))
        ((if q=e 0 then value else -value)*swapFull A (e 0) q (e 0) (e 0)))=_
    rw [hp]
    cases hlocal : pivot (A.submatrix e e) with
    | none => simp only [hlocal,Option.map_none,gaussAcc]
    | some q =>
      simp only [hlocal,Option.map_some,gaussAcc]
      change sourceLoop (List.ofFn (fun i : Fin n => e i.succ)) _ _=_
      rw [ih (fun i : Fin n => e i.succ) (he.comp (Fin.succ_injective n))]
      rw [eliminate_project _ e he,swap_project A e he q]
      have hsame : e q=e 0 ↔ q=0 := he.eq_iff
      simp only [hsame]
      have hval : swapFull A (e 0) (e q) (e 0) (e 0)=swapRows (A.submatrix e e) q 0 0 := by
        exact congrArg (fun B : Matrix (Fin (n+1)) (Fin (n+1)) ℚ => B 0 0) (swap_project A e he q)
      rw [hval]

/-- Construction for determinant in the projection model. -/
def determinant (N : ℕ) (A : Matrix (Fin N) (Fin N) ℚ) : ℚ :=
  sourceLoop (List.finRange N) A 1

/-- The finite construction in `Projection` satisfies `source_determinant_eq` under the displayed hypotheses. -/
theorem source_determinant_eq (N : ℕ) (A : Matrix (Fin N) (Fin N) ℚ) :
    determinant N A=A.det := by
  have hh := loop_project N (fun i : Fin N => i) Function.injective_id A 1
  have hA : A.submatrix (fun i : Fin N => i) (fun i : Fin N => i) = A := by
    ext i j
    rfl
  simpa only [determinant,List.finRange,gaussAcc_eq,hA,one_mul] using hh



end ActualProjectionGaussianLoop


namespace ActualProjectionResultantSamples
open Polynomial ActualYunRationalArray ActualProjectionRows ActualProjectionGaussianLoop
open ActualProjectionSpecialization

/-- Construction for pad in the projection model. -/
def pad (a : List ℚ) (m : ℕ) : List ℚ := a++List.replicate (m+1-a.length) 0

/-- The finite construction in `Projection` satisfies `poly_append_zeros` under the displayed hypotheses. -/
theorem poly_append_zeros (a : List ℚ) (r : ℕ) : poly (a++List.replicate r 0)=poly a := by
  induction r generalizing a with
  | zero => simp only [List.replicate_zero,List.append_nil]
  | succ r ih =>
    have he : a++List.replicate (r+1) 0=(a++[0])++List.replicate r 0 := by
      rw [List.replicate_succ,List.append_assoc]
      rfl
    rw [he,ih,poly_append_zero]

/-- The finite construction in `Projection` satisfies `pad_poly` under the displayed hypotheses. -/
theorem pad_poly (a : List ℚ) (m : ℕ) : poly (pad a m)=poly a := poly_append_zeros _ _

/-- The same emitted instruction list satisfies `pad_length` with the displayed gate and query accounting. -/
theorem pad_length (a : List ℚ) (m : ℕ) (ha : a.length ≤ m+1) : (pad a m).length=m+1 := by
  simp only [pad,List.length_append,List.length_replicate]
  omega

/-- The finite construction in `Projection` satisfies `square_rows` under the displayed hypotheses. -/
theorem square_rows (a b : List ℚ) (m n : ℕ) (ha : a.length=m+1) (hb : b.length=n+1) :
    (rows a b m n).length=m+n ∧ ∀ r∈rows a b m n,r.length=m+n := by
  refine ⟨rows_length a b m n,?_⟩
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hr
    have hj' := List.mem_range.mp hj
    simp only [row,List.length_append,List.length_replicate,List.length_reverse,ha]
    omega
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hr
    have hj' := List.mem_range.mp hj
    simp only [row,List.length_append,List.length_replicate,List.length_reverse,hb]
    omega

/-- Construction for list Determinant in the projection model. -/
def listDeterminant (rs : List (List ℚ)) : ℚ :=
  determinant rs.length (fun i j => (rs.getD i.val []).getD j.val 0)

/-- Construction for fixed Resultant in the projection model. -/
def fixedResultant (a b : List ℚ) (m n : ℕ) : ℚ :=
  listDeterminant (rows (pad a m) (pad b n) m n)

/-- The finite construction in `Projection` satisfies `fixedResultant_eq` under the displayed hypotheses. -/
theorem fixedResultant_eq (a b : List ℚ) (m n : ℕ)
    (ha : a.length ≤ m+1) (hb : b.length ≤ n+1) :
    fixedResultant a b m n=(poly a).resultant (poly b) m n := by
  rw [fixedResultant,listDeterminant,rows_length]
  change determinant (m+n) (listMatrix (pad a m) (pad b n) m n)=_
  rw [source_determinant_eq,rows_det_eq_resultant _ _ m n (pad_length a m ha)
    (pad_length b n hb),pad_poly,pad_poly]

/-- Construction for samples in the projection model. -/
def samples (F G : Polynomial (Polynomial ℚ)) (m n D : ℕ) : List ℚ :=
  List.ofFn (fun i : Fin (2*D*D+1) => fixedResultant
    (specializeArray F m (i.val : ℚ)) (specializeArray G n (i.val : ℚ)) m n)

/-- The finite construction in `Projection` satisfies `actual_samples` under the displayed hypotheses. -/
theorem actual_samples (F G : Polynomial (Polynomial ℚ)) (m n D : ℕ)
    (hF : F.natDegree ≤ m) (hG : G.natDegree ≤ n) :
    samples F G m n D=List.ofFn (fun i : Fin (2*D*D+1) => (F.resultant G m n).eval (i.val : ℚ)) := by
  apply congrArg List.ofFn
  funext i
  rw [fixedResultant_eq _ _ m n (le_of_eq (by simp only [specializeArray,List.length_ofFn]))
    (le_of_eq (by simp only [specializeArray,List.length_ofFn])),specialize_poly F m _ hF,
    specialize_poly G n _ hG,Polynomial.resultant_map_map]
  rfl



end ActualProjectionResultantSamples


namespace ActualProjectionDegree
open Matrix Polynomial

/-- The finite construction in `Projection` satisfies `determinant_degree` under the displayed hypotheses. -/
theorem determinant_degree {N D : ℕ} (A : Matrix (Fin N) (Fin N) (Polynomial ℚ))
    (hA : ∀ i j,(A i j).natDegree ≤ D) : A.det.natDegree ≤ N*D := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro p hp
  calc
    (Equiv.Perm.sign p • ∏ i : Fin N,A (p i) i).natDegree ≤
        (∏ i : Fin N,A (p i) i).natDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign p) with he|he
      · rw [he,one_smul]
      · rw [he,Units.neg_smul,one_smul,Polynomial.natDegree_neg]
    _ ≤ ∑ i : Fin N,(A (p i) i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ N*D := by
      calc
        _ ≤ ∑ _i : Fin N,D := Finset.sum_le_sum (fun i _ => hA (p i) i)
        _ = N*D := by simp

/-- The finite construction in `Projection` satisfies `resultant_degree` under the displayed hypotheses. -/
theorem resultant_degree (F G : Polynomial (Polynomial ℚ)) (m n D : ℕ)
    (hF : ∀ k,(F.coeff k).natDegree ≤ D) (hG : ∀ k,(G.coeff k).natDegree ≤ D) :
    (F.resultant G m n).natDegree ≤ (m+n)*D := by
  apply determinant_degree
  intro i j
  induction j using Fin.addCases <;>
    simp only [Polynomial.sylvester,Matrix.of_apply,Fin.addCases_left,Fin.addCases_right] <;>
    split_ifs
  · exact hG _
  · simp only [Polynomial.natDegree_zero]; omega
  · exact hF _
  · simp only [Polynomial.natDegree_zero]; omega

/-- The finite construction in `Projection` satisfies `source_sample_degree` under the displayed hypotheses. -/
theorem source_sample_degree (F G : Polynomial (Polynomial ℚ)) (m n D : ℕ)
    (hm : m ≤ D) (hn : n ≤ D)
    (hF : ∀ k,(F.coeff k).natDegree ≤ D) (hG : ∀ k,(G.coeff k).natDegree ≤ D) :
    (F.resultant G m n).natDegree < 2*D*D+1 := by
  have hh := resultant_degree F G m n D hF hG
  have hmul : (m+n)*D ≤ (D+D)*D := Nat.mul_le_mul_right D (by omega)
  nlinarith

end ActualProjectionDegree


namespace ActualProjectionForwardDifferences
open Finset

/-- Construction for diffs in the projection model. -/
def diffs (vs : List ℚ) : List ℚ := (vs.zip vs.tail).map (fun p => p.2-p.1)

/-- The same emitted instruction list satisfies `diffs_length` with the displayed gate and query accounting. -/
theorem diffs_length (vs : List ℚ) : (diffs vs).length=vs.length-1 := by
  simp only [diffs,List.length_map,List.length_zip,List.length_tail]
  omega

/-- The finite construction in `Projection` satisfies `diffs_cons` under the displayed hypotheses. -/
theorem diffs_cons (a b : ℚ) (vs : List ℚ) : diffs (a::b::vs)=(b-a)::diffs (b::vs) := rfl

/-- The finite construction in `Projection` satisfies `diffs_getD` under the displayed hypotheses. -/
theorem diffs_getD (vs : List ℚ) (n : ℕ) (hn : n+1 < vs.length) :
    (diffs vs).getD n 0=vs.getD (n+1) 0-vs.getD n 0 := by
  induction n generalizing vs with
  | zero =>
    cases vs with
    | nil => simp at hn
    | cons a vs =>
      cases vs with
      | nil => simp at hn
      | cons b vs => rfl
  | succ n ih =>
    cases vs with
    | nil => simp at hn
    | cons a vs =>
      cases vs with
      | nil => simp at hn
      | cons b vs =>
        rw [diffs_cons]
        change (diffs (b::vs)).getD n 0=(b::vs).getD (n+1) 0-(b::vs).getD n 0
        exact ih (b::vs) (by simp only [List.length_cons] at hn ⊢; omega)

/-- Construction for coefficient in the projection model. -/
def coefficient : ℕ → List ℚ → ℚ
  | 0,vs => vs.getD 0 0
  | k+1,vs => coefficient k (diffs vs)

/-- Construction for binomial Sum in the projection model. -/
def binomialSum (f : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ k∈Finset.range (n+1),(n.choose k : ℚ)*f k

/-- The finite construction in `Projection` satisfies `binomial_succ` under the displayed hypotheses. -/
theorem binomial_succ (f : ℕ → ℚ) (n : ℕ) :
    binomialSum f (n+1)=binomialSum f n+binomialSum (fun k => f (k+1)) n := by
  have hzero : n.choose (n+1)=0 := Nat.choose_eq_zero_of_lt (by omega)
  have hrest : (∑ k∈Finset.range (n+1),(n.choose (k+1) : ℚ)*f (k+1))=
      binomialSum f n-f 0 := by
    rw [Finset.sum_range_succ]
    simp only [hzero,Nat.cast_zero,zero_mul,add_zero]
    have hh : binomialSum f n=(∑ k∈Finset.range n,(n.choose (k+1) : ℚ)*f (k+1))+f 0 := by
      rw [binomialSum,Finset.sum_range_succ']
      simp only [Nat.choose_zero_right,Nat.cast_one,one_mul]
    linarith
  rw [binomialSum,Finset.sum_range_succ']
  simp only [Nat.choose_succ_succ',Nat.cast_add,add_mul,Finset.sum_add_distrib,
    Nat.choose_zero_right,Nat.cast_one,one_mul]
  rw [hrest]
  change binomialSum (fun k => f (k+1)) n+(binomialSum f n-f 0)+f 0=_
  ring

/-- The finite construction in `Projection` satisfies `reconstruct` under the displayed hypotheses. -/
theorem reconstruct (vs : List ℚ) (n : ℕ) (hn : n < vs.length) :
    binomialSum (fun k => coefficient k vs) n=vs.getD n 0 := by
  induction n generalizing vs with
  | zero => simp [binomialSum,coefficient]
  | succ n ih =>
    rw [binomial_succ,ih vs (by omega)]
    have hh : binomialSum (fun k => coefficient (k+1) vs) n=(diffs vs).getD n 0 :=
      ih (diffs vs) (by rw [diffs_length]; omega)
    rw [hh,diffs_getD vs n hn]
    ring

end ActualProjectionForwardDifferences


namespace ActualProjectionNewtonBasis
open Polynomial Finset ActualProjectionForwardDifferences

/-- Construction for basis in the projection model. -/
def basis : ℕ → Polynomial ℚ
  | 0 => 1
  | k+1 => C (1/((k+1 : ℕ) : ℚ))*(basis k*(X-C (k : ℚ)))

/-- The finite construction in `Projection` satisfies `basis_eq` under the displayed hypotheses. -/
theorem basis_eq (k : ℕ) : basis k=C (1/(k.factorial : ℚ))*descPochhammer ℚ k := by
  induction k with
  | zero => simp [basis]
  | succ k ih =>
    rw [basis,ih,descPochhammer_succ_right,Nat.factorial_succ,Nat.cast_mul]
    have hc : (1/((k+1 : ℕ) : ℚ))*(1/(k.factorial : ℚ))=
        1/(((k+1 : ℕ) : ℚ)*(k.factorial : ℚ)) := by ring
    rw [← hc,Polynomial.C_mul]
    simp only [C_eq_natCast]
    ring

/-- The finite construction in `Projection` satisfies `basis_eval` under the displayed hypotheses. -/
theorem basis_eval (k n : ℕ) : (basis k).eval (n : ℚ)=(n.choose k : ℚ) := by
  rw [basis_eq,Polynomial.eval_mul,Polynomial.eval_C,Nat.cast_choose_eq_descPochhammer_div]
  ring

/-- The finite construction in `Projection` satisfies `basis_degree` under the displayed hypotheses. -/
theorem basis_degree (k : ℕ) : (basis k).natDegree=k := by
  rw [basis_eq,Polynomial.natDegree_C_mul (by
    exact div_ne_zero (by norm_num) (by exact_mod_cast k.factorial_ne_zero)),descPochhammer_natDegree]

/-- Construction for newton in the projection model. -/
def newton (vs : List ℚ) : Polynomial ℚ :=
  ∑ k∈Finset.range vs.length,C (coefficient k vs)*basis k

/-- The finite construction in `Projection` satisfies `newton_eval` under the displayed hypotheses. -/
theorem newton_eval (vs : List ℚ) (n : ℕ) (hn : n < vs.length) :
    (newton vs).eval (n : ℚ)=vs.getD n 0 := by
  rw [newton,Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul,Polynomial.eval_C,basis_eval]
  have hsub : Finset.range (n+1)⊆Finset.range vs.length := by
    intro k hk
    have hh := Finset.mem_range.mp hk
    exact Finset.mem_range.mpr (by omega)
  have htrunc : (∑ k∈Finset.range vs.length,coefficient k vs*(n.choose k : ℚ))=
      ∑ k∈Finset.range (n+1),coefficient k vs*(n.choose k : ℚ) := by
    symm
    apply Finset.sum_subset hsub
    intro k hk hnot
    have hkn : n < k := by
      have hh : ¬k < n+1 := fun hh => hnot (Finset.mem_range.mpr hh)
      omega
    rw [Nat.choose_eq_zero_of_lt hkn,Nat.cast_zero,mul_zero]
  rw [htrunc]
  have hh := reconstruct vs n hn
  simpa only [binomialSum,mul_comm] using hh

/-- The finite construction in `Projection` satisfies `newton_degree` under the displayed hypotheses. -/
theorem newton_degree (vs : List ℚ) : (newton vs).natDegree ≤ vs.length-1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hkm := Finset.mem_range.mp hk
  calc
    (C (coefficient k vs)*basis k).natDegree ≤
        (C (coefficient k vs)).natDegree+(basis k).natDegree := Polynomial.natDegree_mul_le
    _ = k := by simp only [Polynomial.natDegree_C,basis_degree,zero_add]
    _ ≤ vs.length-1 := by omega

/-- The finite construction in `Projection` satisfies `recover_polynomial` under the displayed hypotheses. -/
theorem recover_polynomial (P : Polynomial ℚ) (vs : List ℚ)
    (hd : P.natDegree < vs.length)
    (hv : ∀ i : Fin vs.length,vs.getD i.val 0=P.eval (i.val : ℚ)) : newton vs=P := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (newton vs) P
    (f:=fun i : Fin vs.length => (i.val : ℚ))
  · intro i j hij
    apply Fin.ext
    change (i.val : ℚ)=(j.val : ℚ) at hij
    exact_mod_cast hij
  · intro i
    rw [newton_eval vs i.val i.isLt]
    exact hv i
  · have hh := newton_degree vs
    simp only [Fintype.card_fin]
    omega

end ActualProjectionNewtonBasis


namespace ActualProjectionInterpolationArrays
open Polynomial ActualYunRationalArray ActualYunProductArrays
open ActualProjectionNewtonBasis

/-- Construction for q Scale in the projection model. -/
def qScale (v : ℚ) (a : List ℚ) : List ℚ := a.map (fun c => v*c)
/-- Construction for q Divide in the projection model. -/
def qDivide (a : List ℚ) (d : ℚ) : List ℚ := a.map (fun c => c/d)

/-- The finite construction in `Projection` satisfies `qScale_poly` under the displayed hypotheses. -/
theorem qScale_poly (v : ℚ) (a : List ℚ) : poly (qScale v a)=C v*poly a := by
  ext k
  rw [ActualYunRationalArray.coeff,Polynomial.coeff_C_mul,ActualYunRationalArray.coeff]
  simp only [qScale,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : a[k]? <;> simp

/-- The finite construction in `Projection` satisfies `qDivide_poly` under the displayed hypotheses. -/
theorem qDivide_poly (a : List ℚ) (d : ℚ) : poly (qDivide a d)=C (1/d)*poly a := by
  have he : qDivide a d=qScale (1/d) a := by
    apply List.map_congr_left
    intro c hc
    ring
  rw [he,qScale_poly]

/-- The finite construction in `Projection` satisfies `zeros_poly` under the displayed hypotheses. -/
theorem zeros_poly (n : ℕ) : poly (List.replicate n (0 : ℚ))=0 := by
  ext k
  rw [ActualYunRationalArray.coeff]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_replicate,Polynomial.coeff_zero]
  split_ifs <;> rfl

/-- Construction for q Add in the projection model. -/
def qAdd (a b : List ℚ) : List ℚ :=
  trim (subtractShift (subtractShift (List.replicate (max a.length b.length) 0) a 0 (-1)) b 0 (-1))

/-- The finite construction in `Projection` satisfies `qAdd_poly` under the displayed hypotheses. -/
theorem qAdd_poly (a b : List ℚ) : poly (qAdd a b)=poly a+poly b := by
  rw [qAdd,trim_poly,subtractShift_poly _ _ _ _ (by rw [subtractShift_length,List.length_replicate]; omega),
    subtractShift_poly _ _ _ _ (by rw [List.length_replicate]; omega),zeros_poly]
  simp only [pow_zero,one_mul,Polynomial.C_neg,map_one,neg_mul,sub_neg_eq_add,zero_add]

/-- Construction for next Basis in the projection model. -/
def nextBasis (a : List ℚ) (k : ℕ) : List ℚ :=
  qDivide (qMul a [-(k : ℚ),1]) ((k+1 : ℕ) : ℚ)

/-- The finite construction in `Projection` satisfies `nextBasis_poly` under the displayed hypotheses. -/
theorem nextBasis_poly (a : List ℚ) (k : ℕ) (ha : poly a=basis k) :
    poly (nextBasis a k)=basis (k+1) := by
  rw [nextBasis,qDivide_poly,qMul_poly,ha]
  have hx : poly [-(k : ℚ),1]=X-C (k : ℚ) := by
    rw [poly_cons,poly_cons,poly_nil]
    simp only [Polynomial.C_neg,map_one,mul_zero,add_zero,mul_one]
    ring
  rw [hx]
  rfl

end ActualProjectionInterpolationArrays


namespace ActualProjectionInterpolationLoop
open Polynomial Finset ActualYunRationalArray ActualYunProductArrays
open ActualProjectionForwardDifferences ActualProjectionNewtonBasis ActualProjectionInterpolationArrays

/-- Construction for run in the projection model. -/
def run : ℕ → List ℚ → List ℚ → List ℚ → ℕ → Option (List ℚ)
  | _,[],_,out,_ => some (trim out)
  | 0,_::_,_,_,_ => none
  | fuel+1,v::vs,b,out,k => run fuel (diffs (v::vs)) (nextBasis b k)
      (qAdd out (qScale v b)) (k+1)

/-- The finite construction in `Projection` satisfies `tail_sum` under the displayed hypotheses. -/
theorem tail_sum (v : ℚ) (vs : List ℚ) (k : ℕ) :
    (∑ j∈Finset.range (v::vs).length,C (coefficient j (v::vs))*basis (k+j))=
      C v*basis k+(∑ j∈Finset.range (diffs (v::vs)).length,
        C (coefficient j (diffs (v::vs)))*basis ((k+1)+j)) := by
  have hlen : (diffs (v::vs)).length=vs.length := by rw [diffs_length]; simp only [List.length_cons,Nat.add_sub_cancel]
  rw [hlen,List.length_cons,Finset.sum_range_succ']
  change (∑ j∈Finset.range vs.length,C (coefficient j (diffs (v::vs)))*basis (k+(j+1)))+
    C v*basis k=_
  have he : (∑ j∈Finset.range vs.length,C (coefficient j (diffs (v::vs)))*basis (k+(j+1)))=
      ∑ j∈Finset.range vs.length,C (coefficient j (diffs (v::vs)))*basis ((k+1)+j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [show k+(j+1)=(k+1)+j by omega]
  rw [he,add_comm]

/-- The finite construction in `Projection` satisfies `run_success` under the displayed hypotheses. -/
theorem run_success (fuel : ℕ) (values b out : List ℚ) (k : ℕ)
    (hfuel : values.length ≤ fuel) (hb : poly b=basis k) :
    ∃ result,run fuel values b out k=some result ∧
      poly result=poly out+∑ j∈Finset.range values.length,C (coefficient j values)*basis (k+j) := by
  induction fuel generalizing values b out k with
  | zero =>
    have hv : values=[] := List.length_eq_zero_iff.mp (by omega)
    subst values
    exact ⟨trim out,rfl,by simp only [trim_poly,List.length_nil,Finset.sum_range_zero,add_zero]⟩
  | succ fuel ih =>
    cases values with
    | nil => exact ⟨trim out,rfl,by simp only [trim_poly,List.length_nil,Finset.sum_range_zero,add_zero]⟩
    | cons v vs =>
      have hnext : (diffs (v::vs)).length ≤ fuel := by
        rw [diffs_length]
        simp only [List.length_cons] at hfuel ⊢
        omega
      obtain ⟨result,hrun,hpoly⟩ := ih (diffs (v::vs)) (nextBasis b k)
        (qAdd out (qScale v b)) (k+1) hnext (nextBasis_poly b k hb)
      refine ⟨result,hrun,?_⟩
      rw [tail_sum v vs k,hpoly,qAdd_poly,qScale_poly,hb]
      ring

/-- Construction for interpolate in the projection model. -/
def interpolate (values : List ℚ) : Option (List ℚ) := run values.length values [1] [] 0

/-- The finite construction in `Projection` satisfies `interpolate_poly` under the displayed hypotheses. -/
theorem interpolate_poly (values : List ℚ) :
    ∃ result,interpolate values=some result ∧ poly result=newton values := by
  obtain ⟨result,hrun,hpoly⟩ := run_success values.length values [1] [] 0 (le_refl _) (by
    rw [poly_cons,poly_nil]
    simp only [basis,mul_zero,add_zero,map_one])
  refine ⟨result,hrun,?_⟩
  simpa only [newton,poly_nil,zero_add,Nat.zero_add] using hpoly

/-- The finite construction in `Projection` satisfies `interpolate_recovers` under the displayed hypotheses. -/
theorem interpolate_recovers (P : Polynomial ℚ) (values : List ℚ)
    (hd : P.natDegree < values.length)
    (hv : ∀ i : Fin values.length,values.getD i.val 0=P.eval (i.val : ℚ)) :
    ∃ result,interpolate values=some result ∧ poly result=P := by
  obtain ⟨result,hr,hp⟩ := interpolate_poly values
  exact ⟨result,hr,hp.trans (recover_polynomial P values hd hv)⟩



end ActualProjectionInterpolationLoop


namespace ActualProjectionComputedResultant
open Polynomial ActualYunRationalArray ActualProjectionResultantSamples
open ActualProjectionSpecialization ActualProjectionDegree ActualProjectionInterpolationLoop

/-- Construction for compute in the projection model. -/
def compute (F G : Polynomial (Polynomial ℚ)) (m n D : ℕ) : Option (List ℚ) :=
  interpolate (samples F G m n D)

/-- The finite construction in `Projection` satisfies `computed_resultant` under the displayed hypotheses. -/
theorem computed_resultant (F G : Polynomial (Polynomial ℚ)) (m n D : ℕ)
    (hFm : F.natDegree ≤ m) (hGn : G.natDegree ≤ n) (hm : m ≤ D) (hn : n ≤ D)
    (hF : ∀ k,(F.coeff k).natDegree ≤ D) (hG : ∀ k,(G.coeff k).natDegree ≤ D) :
    ∃ result,compute F G m n D=some result ∧ poly result=F.resultant G m n := by
  rw [compute,actual_samples F G m n D hFm hGn]
  apply interpolate_recovers
  · simp only [List.length_ofFn]
    exact source_sample_degree F G m n D hm hn hF hG
  · intro i
    have hi : i.val < 2*D*D+1 := by simpa only [List.length_ofFn] using i.isLt
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left hi,Option.getD_some]

/-- Construction for cast Bivariate in the projection model. -/
def castBivariate (F : Polynomial (Polynomial ℤ)) : Polynomial (Polynomial ℚ) :=
  F.map (Polynomial.mapRingHom (Int.castRingHom ℚ))

/-- The finite construction in `Projection` satisfies `cast_resultant` under the displayed hypotheses. -/
theorem cast_resultant (F G : Polynomial (Polynomial ℤ)) (m n : ℕ) :
    (castBivariate F).resultant (castBivariate G) m n=(F.resultant G m n).map (Int.castRingHom ℚ) :=
  Polynomial.resultant_map_map F G m n (Polynomial.mapRingHom (Int.castRingHom ℚ))

/-- The finite construction in `Projection` satisfies `integral_computed_resultant` under the displayed hypotheses. -/
theorem integral_computed_resultant (F G : Polynomial (Polynomial ℤ)) (m n D : ℕ)
    (hFm : F.natDegree ≤ m) (hGn : G.natDegree ≤ n) (hm : m ≤ D) (hn : n ≤ D)
    (hF : ∀ k,(F.coeff k).natDegree ≤ D) (hG : ∀ k,(G.coeff k).natDegree ≤ D) :
    ∃ result,compute (castBivariate F) (castBivariate G) m n D=some result ∧
      poly result=(F.resultant G m n).map (Int.castRingHom ℚ) ∧
      ∀ j : ℕ,(result.getD j 0).den=1 := by
  have hFm' : (castBivariate F).natDegree ≤ m := Polynomial.natDegree_map_le.trans hFm
  have hGn' : (castBivariate G).natDegree ≤ n := Polynomial.natDegree_map_le.trans hGn
  have hF' : ∀ k,((castBivariate F).coeff k).natDegree ≤ D := by
    intro k
    rw [castBivariate,Polynomial.coeff_map]
    exact Polynomial.natDegree_map_le.trans (hF k)
  have hG' : ∀ k,((castBivariate G).coeff k).natDegree ≤ D := by
    intro k
    rw [castBivariate,Polynomial.coeff_map]
    exact Polynomial.natDegree_map_le.trans (hG k)
  obtain ⟨result,hrun,hp⟩ := computed_resultant (castBivariate F) (castBivariate G) m n D
    hFm' hGn' hm hn hF' hG'
  have he : poly result=(F.resultant G m n).map (Int.castRingHom ℚ) := hp.trans (cast_resultant F G m n)
  refine ⟨result,hrun,he,?_⟩
  intro j
  have hc := congrArg (fun P : Polynomial ℚ => P.coeff j) he
  rw [ActualYunRationalArray.coeff,Polynomial.coeff_map] at hc
  rw [hc]
  simp

/-- The finite construction in `Projection` satisfies `nonzero_guard_of_symbolic` under the displayed hypotheses. -/
theorem nonzero_guard_of_symbolic (F G : Polynomial (Polynomial ℤ)) (m n D : ℕ)
    (hFm : F.natDegree ≤ m) (hGn : G.natDegree ≤ n) (hm : m ≤ D) (hn : n ≤ D)
    (hF : ∀ k,(F.coeff k).natDegree ≤ D) (hG : ∀ k,(G.coeff k).natDegree ≤ D)
    (hres : F.resultant G m n≠0) :
    ∃ result,compute (castBivariate F) (castBivariate G) m n D=some result ∧
      result≠[] ∧ (∀ j : ℕ,(result.getD j 0).den=1) ∧
      poly result=(F.resultant G m n).map (Int.castRingHom ℚ) := by
  obtain ⟨result,hrun,hpoly,hden⟩ := integral_computed_resultant F G m n D hFm hGn hm hn hF hG
  have hnz : result≠[] := by
    intro hz
    rw [hz,poly_nil] at hpoly
    apply hres
    apply Polynomial.map_injective (Int.castRingHom ℚ) Rat.intCast_injective
    simpa only [Polynomial.map_zero] using hpoly.symm
  exact ⟨result,hrun,hnz,hden,hpoly⟩

end ActualProjectionComputedResultant


namespace ActualProjectionIntegerGuard
open Polynomial ActualYunRationalArray ActualYunPrimitiveContent ActualYunContentSupply
open ActualProjectionComputedResultant

/-- Construction for finish in the projection model. -/
def finish (result : List ℚ) : Option (List ℤ) :=
  if result=[] ∨ result.any (fun c => decide (c.den≠1))=true then none else some (result.map Rat.num)

/-- The finite construction in `Projection` satisfies `den_one_mem` under the displayed hypotheses. -/
theorem den_one_mem (result : List ℚ) (hd : ∀ j : ℕ,(result.getD j 0).den=1)
    (c : ℚ) (hc : c∈result) : c.den=1 := by
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hc
  have hh := hd i
  simpa only [List.getD_eq_getElem?_getD,hi,Option.getD_some] using hh

/-- The finite construction in `Projection` satisfies `finish_success` under the displayed hypotheses. -/
theorem finish_success (result : List ℚ) (hn : result≠[]) (hd : ∀ j : ℕ,(result.getD j 0).den=1) :
    finish result=some (result.map Rat.num) ∧
      (result.map Rat.num).map (fun z : ℤ => (z : ℚ))=result := by
  have ha : result.any (fun c => decide (c.den≠1))=false := by
    apply List.any_eq_false.mpr
    intro c hc
    simp only [decide_eq_true_eq,not_ne_iff]
    exact den_one_mem result hd c hc
  have hg : ¬(result=[] ∨ result.any (fun c => decide (c.den≠1))=true) := by rw [ha]; simpa only [Bool.false_eq_true,or_false] using hn
  refine ⟨by rw [finish,ite_eq_right hg],?_⟩
  calc
    _ = result.map (fun c : ℚ => c) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro c hc
      exact Rat.coe_int_num_of_den_eq_one (den_one_mem result hd c hc)
    _ = result := List.map_id result

/-- Construction for project in the projection model. -/
def project (F G : Polynomial (Polynomial ℤ)) (m n D : ℕ) : Option (List ℤ) :=
  (compute (castBivariate F) (castBivariate G) m n D).bind finish

/-- The finite construction in `Projection` satisfies `source_integer_guard` under the displayed hypotheses. -/
theorem source_integer_guard (F G : Polynomial (Polynomial ℤ)) (m n D : ℕ)
    (hFm : F.natDegree ≤ m) (hGn : G.natDegree ≤ n) (hm : m ≤ D) (hn : n ≤ D)
    (hF : ∀ k,(F.coeff k).natDegree ≤ D) (hG : ∀ k,(G.coeff k).natDegree ≤ D)
    (hres : F.resultant G m n≠0) :
    ∃ result,project F G m n D=some result ∧ integerPoly result=F.resultant G m n := by
  obtain ⟨out,hrun,hnz,hden,hpoly⟩ := nonzero_guard_of_symbolic F G m n D hFm hGn hm hn hF hG hres
  obtain ⟨hfinish,harray⟩ := finish_success out hnz hden
  refine ⟨out.map Rat.num,?_,?_⟩
  · simp only [project,hrun,Option.bind_some,hfinish]
  · apply Polynomial.map_injective (Int.castRingHom ℚ) Rat.intCast_injective
    rw [← castArray_poly,harray]
    exact hpoly



end ActualProjectionIntegerGuard



namespace ActualProjectionResultantCriteria
open Polynomial

/-- The finite construction in `Projection` satisfies `fixed_common_root_zero` under the displayed hypotheses. -/
theorem fixed_common_root_zero (f g : Polynomial ℂ) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (hsize : m≠0 ∨ n≠0)
    (z : ℂ) (hfr : f.eval z=0) (hgr : g.eval z=0) : f.resultant g m n=0 := by
  obtain ⟨p,q,hp,hq,he⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant (m:=m) (n:=n) f g hf hg hsize
  have hh := congrArg (fun P : Polynomial ℂ => P.eval z) he
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,hfr,hgr,
    zero_mul,zero_add] using hh.symm

/-- The finite construction in `Projection` satisfies `fixed_nonzero_of_saturated` under the displayed hypotheses. -/
theorem fixed_nonzero_of_saturated (f g : Polynomial ℂ) (m n : ℕ)
    (hfn : f≠0) (hfm : f.natDegree=m) (hgn : g.natDegree ≤ n) (hc : IsCoprime f g) :
    f.resultant g m n≠0 := by
  have hn : n=g.natDegree+(n-g.natDegree) := by omega
  rw [hn,Polynomial.resultant_add_right_deg f g m g.natDegree (n-g.natDegree) (le_refl _)]
  have hl : f.coeff m≠0 := by rw [← hfm,Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hfn
  have hr : f.resultant g m g.natDegree≠0 := by rw [← hfm]; exact Polynomial.resultant_ne_zero f g hc
  exact mul_ne_zero (pow_ne_zero _ hl) hr

/-- The finite construction in `Projection` satisfies `coordinate_vanishing` under the displayed hypotheses. -/
theorem coordinate_vanishing (F G : Polynomial (Polynomial ℂ)) (m n : ℕ)
    (hF : F.natDegree ≤ m) (hG : G.natDegree ≤ n) (hsize : m≠0 ∨ n≠0)
    (x y : ℂ) (hFx : (F.map (Polynomial.evalRingHom x)).eval y=0)
    (hGx : (G.map (Polynomial.evalRingHom x)).eval y=0) :
    (F.resultant G m n).eval x=0 := by
  have hh := fixed_common_root_zero (F.map (Polynomial.evalRingHom x))
    (G.map (Polynomial.evalRingHom x)) m n
    (Polynomial.natDegree_map_le.trans hF) (Polynomial.natDegree_map_le.trans hG) hsize y hFx hGx
  rw [Polynomial.resultant_map_map] at hh
  exact hh

end ActualProjectionResultantCriteria


namespace ActualProjectionRootSeparation
open Polynomial

/-- The finite construction in `Projection` satisfies `coprime_of_no_common_root` under the displayed hypotheses. -/
theorem coprime_of_no_common_root (f g : Polynomial ℂ)
    (hno : ∀ z : ℂ,f.eval z=0 → g.eval z≠0) : IsCoprime f g := by
  classical
  apply (_root_.gcd_isUnit_iff f g).mp
  apply Polynomial.isUnit_iff_degree_eq_zero.mpr
  by_contra hd
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_root (gcd f g) hd
  change (gcd f g).eval z=0 at hz
  have hfz : f.eval z=0 := by
    obtain ⟨a,ha⟩ := gcd_dvd_left f g
    rw [ha,Polynomial.eval_mul,hz,zero_mul]
  have hgz : g.eval z=0 := by
    obtain ⟨a,ha⟩ := gcd_dvd_right f g
    rw [ha,Polynomial.eval_mul,hz,zero_mul]
  exact hno z hfz hgz

/-- The finite construction in `Projection` satisfies `coprime_real_outside` under the displayed hypotheses. -/
theorem coprime_real_outside (p f g : Polynomial ℂ) (B : ℝ) (hB : 0 < B)
    (hroots : ∀ z : ℂ,p.eval z=0 → ‖z‖ < B)
    (hplus : ∀ y : ℂ,p.eval ((B : ℂ)+Complex.I*y)=f.eval y+Complex.I*g.eval y)
    (hminus : ∀ y : ℂ,p.eval ((B : ℂ)-Complex.I*y)=f.eval y-Complex.I*g.eval y) :
    IsCoprime f g := by
  apply coprime_of_no_common_root
  intro y hf hg
  have ha : p.eval ((B : ℂ)+Complex.I*y)=0 := by rw [hplus,hf,hg]; ring
  have hb : p.eval ((B : ℂ)-Complex.I*y)=0 := by rw [hminus,hf,hg]; ring
  have hα := hroots _ ha
  have hβ := hroots _ hb
  have ht := norm_add_le ((B : ℂ)+Complex.I*y) ((B : ℂ)-Complex.I*y)
  have he : ((B : ℂ)+Complex.I*y)+((B : ℂ)-Complex.I*y)=2*(B : ℂ) := by ring
  have hn : ‖(2 : ℂ)*(B : ℂ)‖=2*B := by rw [norm_mul]; simp [Complex.norm_real,abs_of_pos hB]
  rw [he,hn] at ht
  linarith

/-- The finite construction in `Projection` satisfies `coprime_imag_outside` under the displayed hypotheses. -/
theorem coprime_imag_outside (p f g : Polynomial ℂ) (B : ℝ) (hB : 0 < B)
    (hroots : ∀ z : ℂ,p.eval z=0 → ‖z‖ < B)
    (hplus : ∀ x : ℂ,p.eval (x+Complex.I*(B : ℂ))=f.eval x+Complex.I*g.eval x)
    (hminus : ∀ x : ℂ,p.eval (x-Complex.I*(B : ℂ))=f.eval x-Complex.I*g.eval x) :
    IsCoprime f g := by
  apply coprime_of_no_common_root
  intro x hf hg
  have ha : p.eval (x+Complex.I*(B : ℂ))=0 := by rw [hplus,hf,hg]; ring
  have hb : p.eval (x-Complex.I*(B : ℂ))=0 := by rw [hminus,hf,hg]; ring
  have hα := hroots _ ha
  have hβ := hroots _ hb
  have ht := norm_sub_le (x+Complex.I*(B : ℂ)) (x-Complex.I*(B : ℂ))
  have he : (x+Complex.I*(B : ℂ))-(x-Complex.I*(B : ℂ))=2*Complex.I*(B : ℂ) := by ring
  have hn : ‖(2 : ℂ)*Complex.I*(B : ℂ)‖=2*B := by
    rw [norm_mul,norm_mul]
    simp [Complex.norm_real,abs_of_pos hB]
  rw [he,hn] at ht
  linarith

end ActualProjectionRootSeparation


namespace ActualProjectionEntries

/-- Data and invariants for Term in the projection model. -/
structure Term where
  x : ℕ
  y : ℕ
  c : ℤ
  deriving DecidableEq

/-- Construction for pairs in the projection model. -/
def pairs (cs : List ℤ) : List (ℕ×ℕ) :=
  (List.range cs.length).flatMap (fun k => (List.range (k+1)).map (fun j => (k,j)))

/-- Construction for value in the projection model. -/
def value (cs : List ℤ) (k j : ℕ) : ℤ :=
  cs.getD k 0*(k.choose j : ℤ)*(-1 : ℤ)^(j/2)

/-- Construction for raw Term in the projection model. -/
def rawTerm (cs : List ℤ) (p : ℕ×ℕ) : Term := ⟨p.1-p.2,p.2,value cs p.1 p.2⟩

/-- Construction for keep in the projection model. -/
def keep (cs : List ℤ) (parity : ℕ) (p : ℕ×ℕ) : Bool :=
  decide (p.2%2=parity ∧ value cs p.1 p.2≠0)

/-- Construction for entries in the projection model. -/
def entries (cs : List ℤ) (parity : ℕ) : List Term :=
  ((pairs cs).filter (keep cs parity)).map (rawTerm cs)

/-- Construction for key in the projection model. -/
def key (t : Term) : ℕ×ℕ := (t.x,t.y)

/-- The finite construction in `Projection` satisfies `pairs_mem` under the displayed hypotheses. -/
theorem pairs_mem (cs : List ℤ) (p : ℕ×ℕ) : p∈pairs cs ↔ p.1 < cs.length ∧ p.2 ≤ p.1 := by
  simp only [pairs,List.mem_flatMap,List.mem_range,List.mem_map]
  constructor
  · rintro ⟨k,hk,j,hj,he⟩
    cases he
    exact ⟨hk,by omega⟩
  · rintro ⟨hk,hj⟩
    exact ⟨p.1,hk,p.2,by omega,Prod.eta p⟩

/-- The finite construction in `Projection` satisfies `pairs_nodup` under the displayed hypotheses. -/
theorem pairs_nodup (cs : List ℤ) : (pairs cs).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro k hk
    apply List.Nodup.map (fun a b h => (Prod.mk.inj h).2)
    exact List.nodup_range
  · apply (List.nodup_range (n:=cs.length)).imp
    intro k l hkl
    apply List.disjoint_left.mpr
    intro p hpk hpl
    obtain ⟨j,hj,he⟩ := List.mem_map.mp hpk
    obtain ⟨j',hj',he'⟩ := List.mem_map.mp hpl
    have h1 : k=p.1 := congrArg Prod.fst he
    have h2 : l=p.1 := congrArg Prod.fst he'
    exact hkl (h1.trans h2.symm)

/-- The finite construction in `Projection` satisfies `entry_mem` under the displayed hypotheses. -/
theorem entry_mem (cs : List ℤ) (parity : ℕ) (t : Term) :
    t∈entries cs parity ↔ ∃ p : ℕ×ℕ,p.1 < cs.length ∧ p.2 ≤ p.1 ∧
      p.2%2=parity ∧ value cs p.1 p.2≠0 ∧ rawTerm cs p=t := by
  simp only [entries,List.mem_map,List.mem_filter,keep,decide_eq_true_eq,pairs_mem]
  constructor
  · rintro ⟨p,⟨⟨hk,hj⟩,hpar,hv⟩,he⟩
    exact ⟨p,hk,hj,hpar,hv,he⟩
  · rintro ⟨p,hk,hj,hpar,hv,he⟩
    exact ⟨p,⟨⟨hk,hj⟩,hpar,hv⟩,he⟩

/-- The estimate `entry_bounds` retains the actual parameter, input-error and normalization budgets. -/
theorem entry_bounds (cs : List ℤ) (parity : ℕ) (t : Term) (ht : t∈entries cs parity) :
    t.x+t.y < cs.length ∧ t.y%2=parity ∧ t.c≠0 := by
  obtain ⟨p,hk,hj,hpar,hv,rfl⟩ := (entry_mem cs parity t).mp ht
  exact ⟨by dsimp only [rawTerm]; omega,hpar,hv⟩

/-- The finite construction in `Projection` satisfies `keys_nodup` under the displayed hypotheses. -/
theorem keys_nodup (cs : List ℤ) (parity : ℕ) : ((entries cs parity).map key).Nodup := by
  rw [entries,List.map_map]
  apply List.Nodup.map_on ?_ ((pairs_nodup cs).filter (keep cs parity))
  intro p hp q hq he
  have hp' := (pairs_mem cs p).mp (List.mem_filter.mp hp).1
  have hq' := (pairs_mem cs q).mp (List.mem_filter.mp hq).1
  change (p.1-p.2,p.2)=(q.1-q.2,q.2) at he
  have hy := (Prod.mk.inj he).2
  have hx := (Prod.mk.inj he).1
  apply Prod.ext <;> omega



end ActualProjectionEntries


namespace ActualProjectionEntryDegrees
open ActualProjectionEntries

/-- Constructors for Axis in the projection model. -/
inductive Axis where
  | real
  | imag
  deriving DecidableEq

/-- Construction for kept in the projection model. -/
def kept : Axis → Term → ℕ
  | .real,t => t.x
  | .imag,t => t.y

/-- Construction for eliminated in the projection model. -/
def eliminated : Axis → Term → ℕ
  | .real,t => t.y
  | .imag,t => t.x

/-- Construction for source Degree in the projection model. -/
def sourceDegree (axis : Axis) (es : List Term) : Option ℕ := (es.map (eliminated axis)).max?

/-- The finite construction in `Projection` satisfies `generated_nonempty` under the displayed hypotheses. -/
theorem generated_nonempty (cs : List ℤ) (D : ℕ) (hlen : cs.length=D+1)
    (hD : 0 < D) (hlead : cs.getD D 0≠0) : entries cs 0≠[] ∧ entries cs 1≠[] := by
  have he : rawTerm cs (D,0)∈entries cs 0 := by
    apply (entry_mem cs 0 _).mpr
    refine ⟨(D,0),by dsimp; omega,by simp,by simp,?_,rfl⟩
    simpa only [value,Nat.choose_zero_right,Nat.cast_one,mul_one,Nat.zero_div,pow_zero] using hlead
  have ho : rawTerm cs (D,1)∈entries cs 1 := by
    apply (entry_mem cs 1 _).mpr
    refine ⟨(D,1),by dsimp; omega,by dsimp; omega,by norm_num,?_,rfl⟩
    have hDn : (D : ℤ)≠0 := by exact_mod_cast (ne_of_gt hD)
    simpa only [value,Nat.choose_one_right,show 1/2=0 from rfl,pow_zero,mul_one] using mul_ne_zero hlead hDn
  exact ⟨List.ne_nil_of_mem he,List.ne_nil_of_mem ho⟩

/-- The estimate `dimension_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem dimension_bound (cs : List ℤ) (parity : ℕ) (axis : Axis) (t : Term)
    (ht : t∈entries cs parity) :
    eliminated axis t ≤ cs.length-1 ∧ kept axis t ≤ cs.length-1 := by
  have hh := (entry_bounds cs parity t ht).1
  cases axis <;> dsimp only [eliminated,kept] <;> omega

/-- The finite construction in `Projection` satisfies `max_success` under the displayed hypotheses. -/
theorem max_success (axis : Axis) (es : List Term) (hes : es≠[]) :
    ∃ d,sourceDegree axis es=some d ∧
      (∃ t∈es,eliminated axis t=d) ∧ ∀ t∈es,eliminated axis t ≤ d := by
  have hmap : es.map (eliminated axis)≠[] := fun h => hes (List.map_eq_nil_iff.mp h)
  let d := (es.map (eliminated axis)).max hmap
  have hd : sourceDegree axis es=some d := List.max?_eq_some_max hmap
  have info := List.max?_eq_some_iff.mp hd
  obtain ⟨t,ht,he⟩ := List.mem_map.mp info.1
  exact ⟨d,hd,⟨t,ht,he⟩,fun u hu => info.2 _ (List.mem_map.mpr ⟨u,hu,rfl⟩)⟩

/-- The finite construction in `Projection` satisfies `generated_sizes` under the displayed hypotheses. -/
theorem generated_sizes (cs : List ℤ) (D : ℕ) (hlen : cs.length=D+1)
    (hD : 0 < D) (hlead : cs.getD D 0≠0) (axis : Axis) :
    ∃ m n,sourceDegree axis (entries cs 0)=some m ∧ sourceDegree axis (entries cs 1)=some n ∧
      m ≤ D ∧ n ≤ D ∧ (∀ t∈entries cs 0,eliminated axis t ≤ m) ∧
      (∀ t∈entries cs 1,eliminated axis t ≤ n) := by
  obtain ⟨hu,hv⟩ := generated_nonempty cs D hlen hD hlead
  obtain ⟨m,hm,⟨tu,htu,heu⟩,hmu⟩ := max_success axis (entries cs 0) hu
  obtain ⟨n,hn,⟨tv,htv,hev⟩,hnv⟩ := max_success axis (entries cs 1) hv
  have hmb := (dimension_bound cs 0 axis tu htu).1
  have hnb := (dimension_bound cs 1 axis tv htv).1
  rw [hlen] at hmb hnb
  exact ⟨m,n,hm,hn,by omega,by omega,hmu,hnv⟩



end ActualProjectionEntryDegrees


namespace ActualProjectionEntrySpecialization
open Polynomial ActualProjectionEntries ActualProjectionEntryDegrees
open ActualYunRationalArray ActualProjectionComputedResultant

/-- Construction for term Poly in the projection model. -/
def termPoly (axis : Axis) (t : Term) : Polynomial (Polynomial ℤ) :=
  C (Polynomial.monomial (kept axis t) t.c)*X^(eliminated axis t)

/-- Construction for symbolic in the projection model. -/
def symbolic (axis : Axis) : List Term → Polynomial (Polynomial ℤ)
  | [] => 0
  | t::ts => termPoly axis t+symbolic axis ts

/-- Construction for eval Symbolic in the projection model. -/
def evalSymbolic (F : Polynomial (Polynomial ℤ)) (v : ℚ) : Polynomial ℚ :=
  (castBivariate F).map (Polynomial.evalRingHom v)

/-- The finite construction in `Projection` satisfies `evalSymbolic_add` under the displayed hypotheses. -/
theorem evalSymbolic_add (F G : Polynomial (Polynomial ℤ)) (v : ℚ) :
    evalSymbolic (F+G) v=evalSymbolic F v+evalSymbolic G v := by
  simp only [evalSymbolic,castBivariate,Polynomial.map_add]

/-- The finite construction in `Projection` satisfies `evalSymbolic_zero` under the displayed hypotheses. -/
theorem evalSymbolic_zero (v : ℚ) : evalSymbolic 0 v=0 := by
  simp only [evalSymbolic,castBivariate,Polynomial.map_zero]

/-- The finite construction in `Projection` satisfies `term_specialization` under the displayed hypotheses. -/
theorem term_specialization (axis : Axis) (t : Term) (v : ℚ) :
    evalSymbolic (termPoly axis t) v=C ((t.c : ℚ)*v^(kept axis t))*X^(eliminated axis t) := by
  simp [evalSymbolic,castBivariate,termPoly,Polynomial.map_monomial]

/-- Construction for loop in the projection model. -/
def loop (axis : Axis) (v : ℚ) : List Term → List ℚ → List ℚ
  | [],out => out
  | t::ts,out => loop axis v ts (out.set (eliminated axis t)
      (out.getD (eliminated axis t) 0+(t.c : ℚ)*v^(kept axis t)))

/-- The same emitted instruction list satisfies `loop_length` with the displayed gate and query accounting. -/
theorem loop_length (axis : Axis) (v : ℚ) (es : List Term) (out : List ℚ) :
    (loop axis v es out).length=out.length := by
  induction es generalizing out with
  | nil => rfl
  | cons t ts ih => rw [loop,ih,List.length_set]

/-- The finite construction in `Projection` satisfies `loop_poly` under the displayed hypotheses. -/
theorem loop_poly (axis : Axis) (v : ℚ) (es : List Term) (out : List ℚ)
    (hbound : ∀ t∈es,eliminated axis t < out.length) :
    poly (loop axis v es out)=poly out+evalSymbolic (symbolic axis es) v := by
  induction es generalizing out with
  | nil => simp only [loop,symbolic,evalSymbolic_zero,add_zero]
  | cons t ts ih =>
    have ht := hbound t (by simp)
    have hrest : ∀ u∈ts,eliminated axis u <
        (out.set (eliminated axis t) (out.getD (eliminated axis t) 0+(t.c : ℚ)*v^(kept axis t))).length := by
      intro u hu
      rw [List.length_set]
      exact hbound u (by simp only [List.mem_cons]; exact Or.inr hu)
    rw [loop,ih _ hrest,poly_set _ _ _ ht,symbolic,evalSymbolic_add,term_specialization]
    have he : out.getD (eliminated axis t) 0+(t.c : ℚ)*v^(kept axis t)-
        out.getD (eliminated axis t) 0=(t.c : ℚ)*v^(kept axis t) := by ring
    rw [he,← Polynomial.C_mul_X_pow_eq_monomial]
    ring

/-- The finite construction in `Projection` satisfies `zeros_poly` under the displayed hypotheses. -/
theorem zeros_poly (d : ℕ) : poly (List.replicate d (0 : ℚ))=0 := by
  ext k
  rw [ActualYunRationalArray.coeff]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_replicate,Polynomial.coeff_zero]
  split_ifs <;> rfl

/-- Construction for specialize in the projection model. -/
def specialize (axis : Axis) (es : List Term) (v : ℚ) (d : ℕ) : List ℚ :=
  loop axis v es (List.replicate (d+1) 0)

/-- The same emitted instruction list satisfies `specialize_length` with the displayed gate and query accounting. -/
theorem specialize_length (axis : Axis) (es : List Term) (v : ℚ) (d : ℕ) :
    (specialize axis es v d).length=d+1 := by rw [specialize,loop_length,List.length_replicate]

/-- The finite construction in `Projection` satisfies `specialize_poly` under the displayed hypotheses. -/
theorem specialize_poly (axis : Axis) (es : List Term) (v : ℚ) (d : ℕ)
    (hd : sourceDegree axis es=some d) :
    poly (specialize axis es v d)=evalSymbolic (symbolic axis es) v := by
  have hmax := (List.max?_eq_some_iff.mp hd).2
  rw [specialize,loop_poly]
  · rw [zeros_poly,zero_add]
  · intro t ht
    have hh := hmax _ (List.mem_map.mpr ⟨t,ht,rfl⟩)
    rw [List.length_replicate]
    omega

/-- The finite construction in `Projection` satisfies `symbolic_degree` under the displayed hypotheses. -/
theorem symbolic_degree (axis : Axis) (es : List Term) (d : ℕ)
    (hb : ∀ t∈es,eliminated axis t ≤ d) : (symbolic axis es).natDegree ≤ d := by
  induction es with
  | nil => simp only [symbolic,Polynomial.natDegree_zero]; omega
  | cons t ts ih =>
    apply Polynomial.natDegree_add_le_of_degree_le
    · calc
        (termPoly axis t).natDegree ≤ (eliminated axis t) := by
          exact (Polynomial.natDegree_C_mul_le _ _).trans_eq (Polynomial.natDegree_X_pow _)
        _ ≤ d := hb t (by simp)
    · exact ih (fun u hu => hb u (by simp only [List.mem_cons]; exact Or.inr hu))



end ActualProjectionEntrySpecialization


namespace ActualProjectionEntryArrays
open Polynomial ActualProjectionEntries ActualProjectionEntryDegrees
open ActualProjectionEntrySpecialization ActualYunRationalArray ActualProjectionComputedResultant

/-- The finite construction in `Projection` satisfies `arrays_eq` under the displayed hypotheses. -/
theorem arrays_eq (a b : List ℚ) (hlen : a.length=b.length) (he : poly a=poly b) : a=b := by
  apply List.ext_getElem hlen
  intro k hka hkb
  have hh : a.getD k 0=b.getD k 0 := by rw [← ActualYunRationalArray.coeff,he,ActualYunRationalArray.coeff]
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hka,
    List.getElem?_eq_getElem hkb,Option.getD_some] using hh

/-- The finite construction in `Projection` satisfies `specialize_array` under the displayed hypotheses. -/
theorem specialize_array (axis : Axis) (es : List Term) (v : ℚ) (d : ℕ)
    (hd : sourceDegree axis es=some d) : specialize axis es v d=
      ActualProjectionSpecialization.specializeArray (castBivariate (symbolic axis es)) d v := by
  have hbound : ∀ t∈es,eliminated axis t ≤ d := by
    intro t ht
    exact (List.max?_eq_some_iff.mp hd).2 _ (List.mem_map.mpr ⟨t,ht,rfl⟩)
  have hdeg := symbolic_degree axis es d hbound
  have hcast : (castBivariate (symbolic axis es)).natDegree ≤ d := Polynomial.natDegree_map_le.trans hdeg
  apply arrays_eq
  · rw [specialize_length]
    simp only [ActualProjectionSpecialization.specializeArray,List.length_ofFn]
  · exact (specialize_poly axis es v d hd).trans
      (ActualProjectionSpecialization.specialize_poly _ d v hcast).symm

/-- The finite construction in `Projection` satisfies `term_coeff` under the displayed hypotheses. -/
theorem term_coeff (axis : Axis) (t : Term) (j : ℕ) :
    (termPoly axis t).coeff j=if eliminated axis t=j then Polynomial.monomial (kept axis t) t.c else 0 := by
  rw [termPoly,Polynomial.C_mul_X_pow_eq_monomial,Polynomial.coeff_monomial]

/-- The finite construction in `Projection` satisfies `symbolic_coeff_degree` under the displayed hypotheses. -/
theorem symbolic_coeff_degree (axis : Axis) (es : List Term) (D : ℕ)
    (hbound : ∀ t∈es,kept axis t ≤ D) (j : ℕ) : ((symbolic axis es).coeff j).natDegree ≤ D := by
  induction es with
  | nil => simp only [symbolic,Polynomial.coeff_zero,Polynomial.natDegree_zero]; omega
  | cons t ts ih =>
    rw [symbolic,Polynomial.coeff_add]
    apply Polynomial.natDegree_add_le_of_degree_le
    · rw [term_coeff]
      split_ifs
      · exact (Polynomial.natDegree_monomial_le _).trans (hbound t (by simp))
      · simp only [Polynomial.natDegree_zero]; omega
    · exact ih (fun u hu => hbound u (by simp only [List.mem_cons]; exact Or.inr hu))

/-- The estimate `generated_symbolic_bounds` retains the actual parameter, input-error and normalization budgets. -/
theorem generated_symbolic_bounds (cs : List ℤ) (D : ℕ) (hlen : cs.length=D+1)
    (hD : 0 < D) (hlead : cs.getD D 0≠0) (axis : Axis) :
    ∃ m n,sourceDegree axis (entries cs 0)=some m ∧ sourceDegree axis (entries cs 1)=some n ∧
      (symbolic axis (entries cs 0)).natDegree ≤ m ∧ (symbolic axis (entries cs 1)).natDegree ≤ n ∧
      m ≤ D ∧ n ≤ D ∧
      (∀ j,((symbolic axis (entries cs 0)).coeff j).natDegree ≤ D) ∧
      (∀ j,((symbolic axis (entries cs 1)).coeff j).natDegree ≤ D) := by
  obtain ⟨m,n,hm,hn,hmD,hnD,hmu,hnv⟩ := generated_sizes cs D hlen hD hlead axis
  refine ⟨m,n,hm,hn,symbolic_degree axis _ m hmu,symbolic_degree axis _ n hnv,hmD,hnD,?_,?_⟩
  · apply symbolic_coeff_degree
    intro t ht
    have hh := (dimension_bound cs 0 axis t ht).2
    rw [hlen] at hh
    omega
  · apply symbolic_coeff_degree
    intro t ht
    have hh := (dimension_bound cs 1 axis t ht).2
    rw [hlen] at hh
    omega

end ActualProjectionEntryArrays


namespace ActualProjectionDictionary
open ActualProjectionEntries

/-- Construction for assign in the projection model. -/
def assign (state : List Term) (t : Term) : List Term :=
  if key t∈state.map key then state.map (fun old => if key old=key t then t else old)
  else state++[t]

/-- Construction for write All in the projection model. -/
def writeAll : List Term → List Term → List Term
  | [],state => state
  | t::ts,state => writeAll ts (assign state t)

/-- The finite construction in `Projection` satisfies `writeAll_fresh` under the displayed hypotheses. -/
theorem writeAll_fresh (ts state : List Term) (hn : ((state++ts).map key).Nodup) :
    writeAll ts state=state++ts := by
  induction ts generalizing state with
  | nil => simp only [writeAll,List.append_nil]
  | cons t ts ih =>
    have hdis : List.Disjoint (state.map key) ((t::ts).map key) := by
      apply List.disjoint_of_nodup_append
      simpa only [List.map_append] using hn
    have ht : key t∉state.map key := fun hh => List.disjoint_left.mp hdis hh (by simp)
    have hnext : (((state++[t])++ts).map key).Nodup := by
      simpa only [List.append_assoc,List.singleton_append] using hn
    rw [writeAll,assign,ite_eq_right ht,ih _ hnext,List.append_assoc,List.singleton_append]

/-- Construction for build Part in the projection model. -/
def buildPart (cs : List ℤ) (parity : ℕ) : List (ℕ×ℕ) → List Term → List Term
  | [],state => state
  | p::ps,state => if keep cs parity p then buildPart cs parity ps (assign state (rawTerm cs p))
      else buildPart cs parity ps state

/-- The finite construction in `Projection` satisfies `buildPart_filter` under the displayed hypotheses. -/
theorem buildPart_filter (cs : List ℤ) (parity : ℕ) (ps : List (ℕ×ℕ)) (state : List Term) :
    buildPart cs parity ps state=writeAll ((ps.filter (keep cs parity)).map (rawTerm cs)) state := by
  induction ps generalizing state with
  | nil => rfl
  | cons p ps ih =>
    by_cases hp : keep cs parity p=true
    · simp only [buildPart,ite_eq_left hp,List.filter_cons_of_pos hp,List.map_cons,writeAll,ih]
    · have hf : keep cs parity p=false := Bool.eq_false_of_not_eq_true hp
      simp only [buildPart,hf,Bool.false_eq_true,ite_false,List.filter_cons_of_neg hp,ih]

/-- Construction for build Both in the projection model. -/
def buildBoth (cs : List ℤ) : List (ℕ×ℕ) → List Term×List Term → List Term×List Term
  | [],state => state
  | p::ps,(u,v) =>
    if value cs p.1 p.2=0 then buildBoth cs ps (u,v) else
    if p.2%2=0 then buildBoth cs ps (assign u (rawTerm cs p),v)
    else buildBoth cs ps (u,assign v (rawTerm cs p))

/-- The finite construction in `Projection` satisfies `buildBoth_parts` under the displayed hypotheses. -/
theorem buildBoth_parts (cs : List ℤ) (ps : List (ℕ×ℕ)) (u v : List Term) :
    buildBoth cs ps (u,v)=(buildPart cs 0 ps u,buildPart cs 1 ps v) := by
  induction ps generalizing u v with
  | nil => rfl
  | cons p ps ih =>
    by_cases hz : value cs p.1 p.2=0
    · simp [buildBoth,buildPart,keep,hz,ih]
    · by_cases hp : p.2%2=0
      · simp [buildBoth,buildPart,keep,hz,hp,ih]
      · have h1 : p.2%2=1 := by have hh := Nat.mod_lt p.2 (by decide : 0 < 2); omega
        simp [buildBoth,buildPart,keep,hz,h1,ih]

/-- Construction for dictionaries in the projection model. -/
def dictionaries (cs : List ℤ) : List Term×List Term := buildBoth cs (pairs cs) ([],[])

/-- The finite construction in `Projection` satisfies `dictionaries_eq` under the displayed hypotheses. -/
theorem dictionaries_eq (cs : List ℤ) : dictionaries cs=(entries cs 0,entries cs 1) := by
  rw [dictionaries,buildBoth_parts,buildPart_filter,buildPart_filter]
  change (writeAll (entries cs 0) [],writeAll (entries cs 1) [])=_
  rw [writeAll_fresh _ [] (by simpa only [List.nil_append] using keys_nodup cs 0),
    writeAll_fresh _ [] (by simpa only [List.nil_append] using keys_nodup cs 1)]
  rfl



end ActualProjectionDictionary


namespace ActualProjectionGeneratedAxes
open Polynomial ActualProjectionEntries ActualProjectionEntryDegrees
open ActualProjectionEntrySpecialization ActualProjectionEntryArrays
open ActualProjectionComputedResultant ActualYunPrimitiveContent

/-- Construction for axis Samples in the projection model. -/
def axisSamples (axis : Axis) (u v : List Term) (m n D : ℕ) : List ℚ :=
  List.ofFn (fun i : Fin (2*D*D+1) => ActualProjectionResultantSamples.fixedResultant
    (specialize axis u (i.val : ℚ) m) (specialize axis v (i.val : ℚ) n) m n)

/-- Construction for axis Project in the projection model. -/
def axisProject (axis : Axis) (u v : List Term) (D : ℕ) : Option (List ℤ) :=
  (sourceDegree axis u).bind (fun m => (sourceDegree axis v).bind (fun n =>
    (ActualProjectionInterpolationLoop.interpolate (axisSamples axis u v m n D)).bind
      ActualProjectionIntegerGuard.finish))

/-- Construction for projections in the projection model. -/
def projections (cs : List ℤ) : Option (List ℤ) × Option (List ℤ) :=
  let uv := ActualProjectionDictionary.dictionaries cs
  let D := cs.length-1
  (axisProject Axis.real uv.1 uv.2 D,axisProject Axis.imag uv.1 uv.2 D)

/-- The finite construction in `Projection` satisfies `axis_samples_eq` under the displayed hypotheses. -/
theorem axis_samples_eq (axis : Axis) (u v : List Term) (m n D : ℕ)
    (hm : sourceDegree axis u=some m) (hn : sourceDegree axis v=some n) :
    axisSamples axis u v m n D=ActualProjectionResultantSamples.samples
      (castBivariate (symbolic axis u)) (castBivariate (symbolic axis v)) m n D := by
  apply congrArg List.ofFn
  funext i
  rw [specialize_array axis u _ m hm,specialize_array axis v _ n hn]

/-- The finite construction in `Projection` satisfies `axis_project_eq` under the displayed hypotheses. -/
theorem axis_project_eq (axis : Axis) (u v : List Term) (m n D : ℕ)
    (hm : sourceDegree axis u=some m) (hn : sourceDegree axis v=some n) :
    axisProject axis u v D=ActualProjectionIntegerGuard.project
      (symbolic axis u) (symbolic axis v) m n D := by
  simp only [axisProject,hm,hn,Option.bind_some,axis_samples_eq axis u v m n D hm hn,
    ActualProjectionIntegerGuard.project,compute]

/-- The finite construction in `Projection` satisfies `generated_axis` under the displayed hypotheses. -/
theorem generated_axis (cs : List ℤ) (D : ℕ) (hlen : cs.length=D+1)
    (hD : 0 < D) (hlead : cs.getD D 0≠0) (axis : Axis)
    (hres : ∀ m n,sourceDegree axis (entries cs 0)=some m →
      sourceDegree axis (entries cs 1)=some n →
      (symbolic axis (entries cs 0)).resultant (symbolic axis (entries cs 1)) m n≠0) :
    ∃ result m n,axisProject axis (entries cs 0) (entries cs 1) D=some result ∧
      sourceDegree axis (entries cs 0)=some m ∧ sourceDegree axis (entries cs 1)=some n ∧
      integerPoly result=(symbolic axis (entries cs 0)).resultant (symbolic axis (entries cs 1)) m n := by
  obtain ⟨m,n,hm,hn,hFm,hGn,hmD,hnD,hF,hG⟩ := generated_symbolic_bounds cs D hlen hD hlead axis
  obtain ⟨result,hr,hp⟩ := ActualProjectionIntegerGuard.source_integer_guard _ _ m n D
    hFm hGn hmD hnD hF hG (hres m n hm hn)
  exact ⟨result,m,n,(axis_project_eq axis _ _ m n D hm hn).trans hr,hm,hn,hp⟩

/-- The finite construction in `Projection` satisfies `actual_dictionaries_axis` under the displayed hypotheses. -/
theorem actual_dictionaries_axis (cs : List ℤ) (D : ℕ) (hlen : cs.length=D+1)
    (hD : 0 < D) (hlead : cs.getD D 0≠0) (axis : Axis)
    (hres : ∀ m n,sourceDegree axis (entries cs 0)=some m →
      sourceDegree axis (entries cs 1)=some n →
      (symbolic axis (entries cs 0)).resultant (symbolic axis (entries cs 1)) m n≠0) :
    ∃ result m n,axisProject axis (ActualProjectionDictionary.dictionaries cs).1
      (ActualProjectionDictionary.dictionaries cs).2 (cs.length-1)=some result ∧
      integerPoly result=(symbolic axis (entries cs 0)).resultant (symbolic axis (entries cs 1)) m n := by
  obtain ⟨result,m,n,hr,_,_,hp⟩ := generated_axis cs D hlen hD hlead axis hres
  refine ⟨result,m,n,?_,hp⟩
  simpa only [ActualProjectionDictionary.dictionaries_eq,hlen,Nat.add_sub_cancel,
    Prod.fst,Prod.snd] using hr

end ActualProjectionGeneratedAxes


namespace ActualProjectionBinomial
open Polynomial ActualProjectionEntries ActualProjectionEntryDegrees
open ActualProjectionEntrySpecialization

/-- The finite construction in `Projection` satisfies `square_minus_one_power` under the displayed hypotheses. -/
theorem square_minus_one_power (u : ℂ) (hu : u^2=-1) (j : ℕ) :
    u^j=if j%2=0 then (-1 : ℂ)^(j/2) else u*(-1 : ℂ)^(j/2) := by
  have hj : j=2*(j/2)+j%2 := by omega
  conv_lhs => rw [hj,pow_add,pow_mul,hu]
  by_cases he : j%2=0
  · simp only [he,pow_zero,mul_one,ite_true]
  · have ho : j%2=1 := by have hh := Nat.mod_lt j (by decide : 0 < 2); omega
    simp only [ho,pow_one,Nat.one_ne_zero,ite_false]
    ring

/-- Construction for entry Value in the projection model. -/
def entryValue (t : Term) (x y : ℂ) : ℂ := (t.c : ℂ)*x^t.x*y^t.y

/-- Construction for mixed Value in the projection model. -/
def mixedValue (cs : List ℤ) (p : ℕ×ℕ) (x y u : ℂ) : ℂ :=
  (cs.getD p.1 0 : ℂ)*(p.1.choose p.2 : ℂ)*x^(p.1-p.2)*(u*y)^p.2

/-- The finite construction in `Projection` satisfies `mixed_value` under the displayed hypotheses. -/
theorem mixed_value (cs : List ℤ) (p : ℕ×ℕ) (x y u : ℂ) (hu : u^2=-1) :
    mixedValue cs p x y u=if p.2%2=0 then entryValue (rawTerm cs p) x y
      else u*entryValue (rawTerm cs p) x y := by
  simp only [mixedValue,entryValue,rawTerm,value,Int.cast_mul,Int.cast_pow,
    Int.cast_natCast,Int.cast_neg,Int.cast_one,mul_pow,square_minus_one_power u hu]
  split_ifs <;> ring

/-- Construction for part Sum in the projection model. -/
def partSum (cs : List ℤ) (parity : ℕ) (ps : List (ℕ×ℕ)) (x y : ℂ) : ℂ :=
  (((ps.filter (keep cs parity)).map (rawTerm cs)).map (fun t => entryValue t x y)).sum

/-- The finite construction in `Projection` satisfies `part_sum_cons` under the displayed hypotheses. -/
theorem part_sum_cons (cs : List ℤ) (parity : ℕ) (p : ℕ×ℕ) (ps : List (ℕ×ℕ)) (x y : ℂ) :
    partSum cs parity (p::ps) x y=(if p.2%2=parity then entryValue (rawTerm cs p) x y else 0)+
      partSum cs parity ps x y := by
  by_cases hz : value cs p.1 p.2=0
  · have he : entryValue (rawTerm cs p) x y=0 := by
      simp only [entryValue,rawTerm,hz,Int.cast_zero,zero_mul]
    simp [partSum,keep,hz,he]
  · by_cases hp : p.2%2=parity
    · simp [partSum,keep,hz,hp]
    · simp [partSum,keep,hz,hp]

/-- The finite construction in `Projection` satisfies `split_sum` under the displayed hypotheses. -/
theorem split_sum (cs : List ℤ) (ps : List (ℕ×ℕ)) (x y u : ℂ) (hu : u^2=-1) :
    partSum cs 0 ps x y+u*partSum cs 1 ps x y=(ps.map (fun p => mixedValue cs p x y u)).sum := by
  induction ps with
  | nil => simp [partSum]
  | cons p ps ih =>
    rw [part_sum_cons,part_sum_cons,List.map_cons,List.sum_cons,mixed_value cs p x y u hu]
    by_cases hp : p.2%2=0
    · have h1 : p.2%2≠1 := by omega
      simp only [ite_eq_left hp,ite_eq_right h1,zero_add]
      linear_combination ih
    · have h1 : p.2%2=1 := by have hh := Nat.mod_lt p.2 (by decide : 0 < 2); omega
      simp only [ite_eq_right hp,ite_eq_left h1,zero_add]
      linear_combination ih

end ActualProjectionBinomial


namespace ActualProjectionBinomialEval
open Polynomial ActualProjectionEntries ActualProjectionEntryDegrees
open ActualProjectionEntrySpecialization ActualProjectionBinomial
open scoped BigOperators

/-- Construction for bivariate Value in the projection model. -/
def bivariateValue (axis : Axis) (F : Polynomial (Polynomial ℤ)) (x y : ℂ) : ℂ :=
  match axis with
  | .real => F.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) x) y
  | .imag => F.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) y) x

/-- The finite construction in `Projection` satisfies `bivariate_add` under the displayed hypotheses. -/
theorem bivariate_add (axis : Axis) (F G : Polynomial (Polynomial ℤ)) (x y : ℂ) :
    bivariateValue axis (F+G) x y=bivariateValue axis F x y+bivariateValue axis G x y := by
  cases axis <;> exact Polynomial.eval₂_add _ _

/-- The finite construction in `Projection` satisfies `bivariate_term` under the displayed hypotheses. -/
theorem bivariate_term (axis : Axis) (t : Term) (x y : ℂ) :
    bivariateValue axis (termPoly axis t) x y=entryValue t x y := by
  cases axis with
  | real => simp [bivariateValue,termPoly,kept,eliminated,entryValue,
      Polynomial.eval₂_monomial,Polynomial.eval₂_mul]
  | imag =>
    simp [bivariateValue,termPoly,kept,eliminated,entryValue,
      Polynomial.eval₂_monomial,Polynomial.eval₂_mul]
    ring

/-- The finite construction in `Projection` satisfies `bivariate_symbolic` under the displayed hypotheses. -/
theorem bivariate_symbolic (axis : Axis) (es : List Term) (x y : ℂ) :
    bivariateValue axis (symbolic axis es) x y=(es.map (fun t => entryValue t x y)).sum := by
  induction es with
  | nil => cases axis <;> simp [symbolic,bivariateValue]
  | cons t ts ih => rw [symbolic,bivariate_add,bivariate_term,ih,List.map_cons,List.sum_cons]

/-- The finite construction in `Projection` satisfies `bivariate_entries` under the displayed hypotheses. -/
theorem bivariate_entries (axis : Axis) (cs : List ℤ) (parity : ℕ) (x y : ℂ) :
    bivariateValue axis (symbolic axis (entries cs parity)) x y=partSum cs parity (pairs cs) x y :=
  bivariate_symbolic axis (entries cs parity) x y

/-- The finite construction in `Projection` satisfies `list_range_sum` under the displayed hypotheses. -/
theorem list_range_sum (f : ℕ → ℂ) (n : ℕ) :
    ((List.range n).map f).sum=∑ k∈Finset.range n,f k := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.range_succ,List.map_append,List.sum_append,
      List.map_singleton,List.sum_singleton,Finset.sum_range_succ,ih]

/-- The finite construction in `Projection` satisfies `flat_sum` under the displayed hypotheses. -/
theorem flat_sum (ks : List ℕ) (g : ℕ → List (ℕ×ℕ)) (f : ℕ×ℕ → ℂ) :
    ((ks.flatMap g).map f).sum=(ks.map (fun k => ((g k).map f).sum)).sum := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,
      List.map_cons,List.sum_cons,ih]

/-- Construction for input Poly in the projection model. -/
def inputPoly (cs : List ℤ) : Polynomial ℂ :=
  (ActualYunPrimitiveContent.integerPoly cs).map (Int.castRingHom ℂ)

/-- The finite construction in `Projection` satisfies `input_coeff` under the displayed hypotheses. -/
theorem input_coeff (cs : List ℤ) (k : ℕ) : (inputPoly cs).coeff k=(cs.getD k 0 : ℂ) := by
  rw [inputPoly,Polynomial.coeff_map]
  change (Int.castRingHom ℂ) (cs.toFinsupp k)=_
  rw [List.toFinsupp_apply]
  rfl

/-- The finite construction in `Projection` satisfies `input_eval` under the displayed hypotheses. -/
theorem input_eval (cs : List ℤ) (z : ℂ) :
    (inputPoly cs).eval z=∑ k∈Finset.range cs.length,(cs.getD k 0 : ℂ)*z^k := by
  by_cases he : cs=[]
  · subst cs
    have hz : inputPoly []=0 := by
      ext k
      rw [input_coeff]
      simp
    simp [hz]
  · have hlen : 0 < cs.length := List.length_pos_iff.mpr he
    have hdeg : (inputPoly cs).natDegree < cs.length := by
      by_cases hz : inputPoly cs=0
      · simpa only [hz,Polynomial.natDegree_zero] using hlen
      · apply (Polynomial.natDegree_lt_iff_degree_lt hz).mpr
        apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
        intro k hk
        rw [input_coeff,List.getD_eq_default _ _ (by omega),Int.cast_zero]
    rw [Polynomial.eval_eq_sum_range' hdeg]
    simp only [input_coeff]

/-- The finite construction in `Projection` satisfies `pair_sum` under the displayed hypotheses. -/
theorem pair_sum (cs : List ℤ) (x y u : ℂ) :
    ((pairs cs).map (fun p => mixedValue cs p x y u)).sum=(inputPoly cs).eval (x+u*y) := by
  rw [pairs,flat_sum,list_range_sum,input_eval]
  apply Finset.sum_congr rfl
  intro k hk
  rw [List.map_map,list_range_sum,add_comm x (u*y),add_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Function.comp_apply,mixedValue]
  ring

/-- The finite construction in `Projection` satisfies `paired_identity` under the displayed hypotheses. -/
theorem paired_identity (axis : Axis) (cs : List ℤ) (x y u : ℂ) (hu : u^2=-1) :
    (inputPoly cs).eval (x+u*y)=bivariateValue axis (symbolic axis (entries cs 0)) x y+
      u*bivariateValue axis (symbolic axis (entries cs 1)) x y := by
  rw [bivariate_entries,bivariate_entries,split_sum cs (pairs cs) x y u hu,pair_sum]

/-- The finite construction in `Projection` satisfies `plus_identity` under the displayed hypotheses. -/
theorem plus_identity (axis : Axis) (cs : List ℤ) (x y : ℂ) :
    (inputPoly cs).eval (x+Complex.I*y)=bivariateValue axis (symbolic axis (entries cs 0)) x y+
      Complex.I*bivariateValue axis (symbolic axis (entries cs 1)) x y :=
  paired_identity axis cs x y Complex.I Complex.I_sq

/-- The finite construction in `Projection` satisfies `minus_identity` under the displayed hypotheses. -/
theorem minus_identity (axis : Axis) (cs : List ℤ) (x y : ℂ) :
    (inputPoly cs).eval (x-Complex.I*y)=bivariateValue axis (symbolic axis (entries cs 0)) x y-
      Complex.I*bivariateValue axis (symbolic axis (entries cs 1)) x y := by
  have hh := paired_identity axis cs x y (-Complex.I) (by simpa only [neg_sq] using Complex.I_sq)
  simpa only [neg_mul,sub_eq_add_neg] using hh

end ActualProjectionBinomialEval


namespace ActualProjectionLeading
open Polynomial ActualProjectionEntries ActualProjectionEntryDegrees
open ActualProjectionEntrySpecialization ActualProjectionEntryArrays

/-- The finite construction in `Projection` satisfies `coeff_zero_of_absent` under the displayed hypotheses. -/
theorem coeff_zero_of_absent (axis : Axis) (es : List Term) (d : ℕ)
    (habs : ∀ t∈es,eliminated axis t≠d) : (symbolic axis es).coeff d=0 := by
  induction es with
  | nil => simp only [symbolic,Polynomial.coeff_zero]
  | cons t ts ih =>
    rw [symbolic,Polynomial.coeff_add,term_coeff,ite_eq_right (habs t (by simp)),zero_add]
    exact ih (fun u hu => habs u (by simp only [List.mem_cons]; exact Or.inr hu))

/-- The finite construction in `Projection` satisfies `coeff_isolated` under the displayed hypotheses. -/
theorem coeff_isolated (axis : Axis) (es : List Term) (d : ℕ) (t : Term)
    (hnd : es.Nodup) (ht : t∈es) (he : eliminated axis t=d)
    (honly : ∀ u∈es,eliminated axis u=d → u=t) :
    (symbolic axis es).coeff d=Polynomial.monomial (kept axis t) t.c := by
  induction es with
  | nil => simp only [List.not_mem_nil] at ht
  | cons a as ih =>
    obtain ⟨hna,hns⟩ := List.nodup_cons.mp hnd
    by_cases hat : a=t
    · subst a
      rw [symbolic,Polynomial.coeff_add,term_coeff,ite_eq_left he,
        coeff_zero_of_absent axis as d,add_zero]
      intro u hu hue
      have hut := honly u (by simp only [List.mem_cons]; exact Or.inr hu) hue
      subst u
      exact hna hu
    · have hae : eliminated axis a≠d := fun hh => hat (honly a (by simp) hh)
      have htail : t∈as := (List.mem_cons.mp ht).resolve_left (Ne.symm hat)
      rw [symbolic,Polynomial.coeff_add,term_coeff,ite_eq_right hae,zero_add]
      exact ih hns htail (fun u hu => honly u (by simp only [List.mem_cons]; exact Or.inr hu))

/-- Construction for top Pair in the projection model. -/
def topPair : Axis → ℕ → ℕ×ℕ
  | .real,D => (D,D)
  | .imag,D => (D,0)

/-- Construction for top Parity in the projection model. -/
def topParity : Axis → ℕ → ℕ
  | .real,D => D%2
  | .imag,_ => 0

/-- The finite construction in `Projection` satisfies `top_entry` under the displayed hypotheses. -/
theorem top_entry (axis : Axis) (cs : List ℤ) (D : ℕ) (hlen : cs.length=D+1)
    (hlead : cs.getD D 0≠0) : rawTerm cs (topPair axis D)∈entries cs (topParity axis D) := by
  apply (entry_mem cs _ _).mpr
  refine ⟨topPair axis D,?_,?_,?_,?_,rfl⟩
  · cases axis <;> dsimp only [topPair] <;> omega
  · cases axis <;> dsimp only [topPair] <;> omega
  · cases axis <;> rfl
  · cases axis with
    | real =>
      simpa only [topPair,value,Nat.choose_self,Nat.cast_one,mul_one] using
        mul_ne_zero hlead (pow_ne_zero (D/2) (by decide : (-1 : ℤ)≠0))
    | imag =>
      simpa only [topPair,value,Nat.choose_zero_right,Nat.cast_one,mul_one,Nat.zero_div,pow_zero] using hlead

/-- The finite construction in `Projection` satisfies `top_unique` under the displayed hypotheses. -/
theorem top_unique (axis : Axis) (cs : List ℤ) (D : ℕ) (hlen : cs.length=D+1)
    (t : Term) (ht : t∈entries cs (topParity axis D)) (he : eliminated axis t=D) :
    t=rawTerm cs (topPair axis D) := by
  obtain ⟨p,hk,hj,_,_,rfl⟩ := (entry_mem cs _ _).mp ht
  have hp : p=topPair axis D := by
    cases axis <;> dsimp only [eliminated,rawTerm,topPair] at he ⊢ <;> apply Prod.ext <;> dsimp <;> omega
  rw [hp]

/-- The finite construction in `Projection` satisfies `top_coefficient` under the displayed hypotheses. -/
theorem top_coefficient (axis : Axis) (cs : List ℤ) (D : ℕ) (hlen : cs.length=D+1)
    (hlead : cs.getD D 0≠0) :
    (symbolic axis (entries cs (topParity axis D))).coeff D=C (value cs
      (topPair axis D).1 (topPair axis D).2) := by
  have hh := coeff_isolated axis (entries cs (topParity axis D)) D (rawTerm cs (topPair axis D))
    (List.Nodup.of_map key (keys_nodup cs _)) (top_entry axis cs D hlen hlead)
    (by cases axis <;> simp [topPair,eliminated,rawTerm])
    (top_unique axis cs D hlen)
  have hk : kept axis (rawTerm cs (topPair axis D))=0 := by
    cases axis <;> simp [kept,rawTerm,topPair]
  rw [hk,Polynomial.monomial_zero_left] at hh
  exact hh

/-- The finite construction in `Projection` satisfies `top_max` under the displayed hypotheses. -/
theorem top_max (axis : Axis) (cs : List ℤ) (D : ℕ) (hlen : cs.length=D+1)
    (hlead : cs.getD D 0≠0) : sourceDegree axis (entries cs (topParity axis D))=some D := by
  apply List.max?_eq_some_iff.mpr
  constructor
  · refine List.mem_map.mpr ⟨rawTerm cs (topPair axis D),top_entry axis cs D hlen hlead,?_⟩
    cases axis <;> simp [eliminated,rawTerm,topPair]
  · intro d hd
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hd
    have hh := (dimension_bound cs (topParity axis D) axis t ht).1
    rw [hlen] at hh
    omega

/-- The finite construction in `Projection` satisfies `top_value_ne_zero` under the displayed hypotheses. -/
theorem top_value_ne_zero (axis : Axis) (cs : List ℤ) (D : ℕ) (hlen : cs.length=D+1)
    (hlead : cs.getD D 0≠0) : value cs (topPair axis D).1 (topPair axis D).2≠0 :=
  (entry_bounds cs _ _ (top_entry axis cs D hlen hlead)).2.2

end ActualProjectionLeading


namespace ActualProjectionComplexSpecialization
open Polynomial ActualProjectionEntries ActualProjectionEntryDegrees
open ActualProjectionEntrySpecialization ActualProjectionEntryArrays
open ActualProjectionBinomialEval ActualProjectionLeading

/-- Construction for complex Specialize in the projection model. -/
def complexSpecialize (F : Polynomial (Polynomial ℤ)) (z : ℂ) : Polynomial ℂ :=
  F.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ) z)

/-- The finite construction in `Projection` satisfies `eval_real` under the displayed hypotheses. -/
theorem eval_real (F : Polynomial (Polynomial ℤ)) (x y : ℂ) :
    (complexSpecialize F x).eval y=bivariateValue Axis.real F x y :=
  Polynomial.eval_map _ y

/-- The finite construction in `Projection` satisfies `eval_imag` under the displayed hypotheses. -/
theorem eval_imag (F : Polynomial (Polynomial ℤ)) (x y : ℂ) :
    (complexSpecialize F y).eval x=bivariateValue Axis.imag F x y :=
  Polynomial.eval_map _ x

/-- The finite construction in `Projection` satisfies `top_specialized_coeff` under the displayed hypotheses. -/
theorem top_specialized_coeff (axis : Axis) (cs : List ℤ) (D : ℕ) (hlen : cs.length=D+1)
    (hlead : cs.getD D 0≠0) (z : ℂ) :
    (complexSpecialize (symbolic axis (entries cs (topParity axis D))) z).coeff D=
      (value cs (topPair axis D).1 (topPair axis D).2 : ℂ) := by
  rw [complexSpecialize,Polynomial.coeff_map,top_coefficient axis cs D hlen hlead]
  exact Polynomial.eval₂_C _ _

/-- The finite construction in `Projection` satisfies `top_specialized_degree` under the displayed hypotheses. -/
theorem top_specialized_degree (axis : Axis) (cs : List ℤ) (D : ℕ) (hlen : cs.length=D+1)
    (hlead : cs.getD D 0≠0) (z : ℂ) :
    complexSpecialize (symbolic axis (entries cs (topParity axis D))) z≠0 ∧
      (complexSpecialize (symbolic axis (entries cs (topParity axis D))) z).natDegree=D := by
  have hc : (complexSpecialize (symbolic axis (entries cs (topParity axis D))) z).coeff D≠0 := by
    rw [top_specialized_coeff axis cs D hlen hlead z]
    exact_mod_cast top_value_ne_zero axis cs D hlen hlead
  have hd : (symbolic axis (entries cs (topParity axis D))).natDegree ≤ D := by
    apply symbolic_degree
    intro t ht
    have hh := (dimension_bound cs _ axis t ht).1
    rw [hlen] at hh
    omega
  exact ⟨fun hz => hc (by rw [hz,Polynomial.coeff_zero]),
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (Polynomial.natDegree_map_le.trans hd) hc⟩

/-- The finite construction in `Projection` satisfies `generated_coprime` under the displayed hypotheses. -/
theorem generated_coprime (axis : Axis) (cs : List ℤ) (D : ℕ) (hlen : cs.length=D+1)
    (hlead : cs.getD D 0≠0) :
    IsCoprime (complexSpecialize (symbolic axis (entries cs 0)) (ActualSturmCauchyInput.listBound cs : ℂ))
      (complexSpecialize (symbolic axis (entries cs 1)) (ActualSturmCauchyInput.listBound cs : ℂ)) := by
  have htop : cs.getD (cs.length-1) 0≠0 := by simpa only [hlen,Nat.add_sub_cancel] using hlead
  have hpos : (0 : ℝ) < ActualSturmCauchyInput.listBound cs := by
    exact_mod_cast (ActualSturmCauchyInput.list_endpoints cs htop).1
  have hroots : ∀ z : ℂ,(inputPoly cs).eval z=0 → ‖z‖<(ActualSturmCauchyInput.listBound cs : ℝ) :=
    fun z hz => ActualSturmCauchyInput.list_bound_roots cs htop z hz
  cases axis with
  | real =>
    apply ActualProjectionRootSeparation.coprime_real_outside (inputPoly cs) _ _ _ hpos hroots
    · intro y
      rw [eval_real,eval_real]
      exact plus_identity Axis.real cs _ y
    · intro y
      rw [eval_real,eval_real]
      exact minus_identity Axis.real cs _ y
  | imag =>
    apply ActualProjectionRootSeparation.coprime_imag_outside (inputPoly cs) _ _ _ hpos hroots
    · intro x
      rw [eval_imag,eval_imag]
      exact plus_identity Axis.imag cs x _
    · intro x
      rw [eval_imag,eval_imag]
      exact minus_identity Axis.imag cs x _

end ActualProjectionComplexSpecialization


namespace ActualProjectionGeneratedNonzero
open Polynomial ActualProjectionEntries ActualProjectionEntryDegrees
open ActualProjectionEntrySpecialization ActualProjectionEntryArrays
open ActualProjectionLeading ActualProjectionComplexSpecialization
open ActualProjectionGeneratedAxes ActualYunPrimitiveContent

/-- The finite construction in `Projection` satisfies `top_parity_cases` under the displayed hypotheses. -/
theorem top_parity_cases (axis : Axis) (D : ℕ) : topParity axis D=0 ∨ topParity axis D=1 := by
  cases axis with
  | real => dsimp only [topParity]; have hh := Nat.mod_lt D (by decide : 0 < 2); omega
  | imag => exact Or.inl rfl

/-- The finite construction in `Projection` satisfies `actual_sizes_positive` under the displayed hypotheses. -/
theorem actual_sizes_positive (axis : Axis) (cs : List ℤ) (D m n : ℕ) (hlen : cs.length=D+1)
    (hD : 0 < D) (hlead : cs.getD D 0≠0)
    (hm : sourceDegree axis (entries cs 0)=some m) (hn : sourceDegree axis (entries cs 1)=some n) :
    m≠0 ∨ n≠0 := by
  have ht := top_max axis cs D hlen hlead
  rcases top_parity_cases axis D with hp|hp
  · rw [hp,hm] at ht
    exact Or.inl (by have hh := Option.some.inj ht; omega)
  · rw [hp,hn] at ht
    exact Or.inr (by have hh := Option.some.inj ht; omega)

/-- The finite construction in `Projection` satisfies `actual_symbolic_nonzero` under the displayed hypotheses. -/
theorem actual_symbolic_nonzero (axis : Axis) (cs : List ℤ) (D m n : ℕ) (hlen : cs.length=D+1)
    (hlead : cs.getD D 0≠0)
    (hm : sourceDegree axis (entries cs 0)=some m) (hn : sourceDegree axis (entries cs 1)=some n) :
    (symbolic axis (entries cs 0)).resultant (symbolic axis (entries cs 1)) m n≠0 := by
  let B : ℂ := (ActualSturmCauchyInput.listBound cs : ℂ)
  let f := complexSpecialize (symbolic axis (entries cs 0)) B
  let g := complexSpecialize (symbolic axis (entries cs 1)) B
  have hFm : (symbolic axis (entries cs 0)).natDegree ≤ m := by
    apply symbolic_degree
    intro t ht
    exact (List.max?_eq_some_iff.mp hm).2 _ (List.mem_map.mpr ⟨t,ht,rfl⟩)
  have hGn : (symbolic axis (entries cs 1)).natDegree ≤ n := by
    apply symbolic_degree
    intro t ht
    exact (List.max?_eq_some_iff.mp hn).2 _ (List.mem_map.mpr ⟨t,ht,rfl⟩)
  have hc : IsCoprime f g := generated_coprime axis cs D hlen hlead
  have hs := top_specialized_degree axis cs D hlen hlead B
  have hmax := top_max axis cs D hlen hlead
  have hr : f.resultant g m n≠0 := by
    rcases top_parity_cases axis D with hp|hp
    · rw [hp,hm] at hmax
      rw [hp] at hs
      have hmD : m=D := Option.some.inj hmax
      exact ActualProjectionResultantCriteria.fixed_nonzero_of_saturated f g m n hs.1
        (hs.2.trans hmD.symm) (Polynomial.natDegree_map_le.trans hGn) hc
    · rw [hp,hn] at hmax
      rw [hp] at hs
      have hnD : n=D := Option.some.inj hmax
      rw [Polynomial.resultant_comm]
      apply mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : ℂ)≠0))
      exact ActualProjectionResultantCriteria.fixed_nonzero_of_saturated g f n m hs.1
        (hs.2.trans hnD.symm) (Polynomial.natDegree_map_le.trans hFm) hc.symm
  intro hz
  apply hr
  change (complexSpecialize _ B).resultant (complexSpecialize _ B) m n=0
  rw [complexSpecialize,complexSpecialize,Polynomial.resultant_map_map,hz]
  exact map_zero _

/-- The finite construction in `Projection` satisfies `actual_axis_success` under the displayed hypotheses. -/
theorem actual_axis_success (axis : Axis) (cs : List ℤ) (D : ℕ) (hlen : cs.length=D+1)
    (hD : 0 < D) (hlead : cs.getD D 0≠0) :
    ∃ result m n,axisProject axis (ActualProjectionDictionary.dictionaries cs).1
      (ActualProjectionDictionary.dictionaries cs).2 (cs.length-1)=some result ∧
      sourceDegree axis (entries cs 0)=some m ∧ sourceDegree axis (entries cs 1)=some n ∧
      integerPoly result=(symbolic axis (entries cs 0)).resultant (symbolic axis (entries cs 1)) m n ∧
      integerPoly result≠0 := by
  obtain ⟨result,m,n,hr,hm,hn,hp⟩ := generated_axis cs D hlen hD hlead axis
    (fun m n hm hn => actual_symbolic_nonzero axis cs D m n hlen hlead hm hn)
  refine ⟨result,m,n,?_,hm,hn,hp,?_⟩
  · simpa only [ActualProjectionDictionary.dictionaries_eq,hlen,Nat.add_sub_cancel,Prod.fst,Prod.snd] using hr
  · rw [hp]
    exact actual_symbolic_nonzero axis cs D m n hlen hlead hm hn

end ActualProjectionGeneratedNonzero


namespace ActualProjectionGeneratedCoordinates
open Polynomial ActualProjectionEntries ActualProjectionEntryDegrees
open ActualProjectionEntrySpecialization ActualProjectionEntryArrays
open ActualProjectionBinomial ActualProjectionBinomialEval
open ActualProjectionComplexSpecialization ActualProjectionGeneratedNonzero

/-- The finite construction in `Projection` satisfies `entry_real` under the displayed hypotheses. -/
theorem entry_real (t : Term) (x y : ℝ) : (entryValue t (x : ℂ) (y : ℂ)).im=0 := by
  simp [entryValue,← Complex.ofReal_pow]

/-- The finite construction in `Projection` satisfies `symbolic_real` under the displayed hypotheses. -/
theorem symbolic_real (axis : Axis) (es : List Term) (x y : ℝ) :
    (bivariateValue axis (symbolic axis es) (x : ℂ) (y : ℂ)).im=0 := by
  rw [bivariate_symbolic]
  induction es with
  | nil => rfl
  | cons t ts ih => rw [List.map_cons,List.sum_cons,Complex.add_im,entry_real,ih,zero_add]

/-- The finite construction in `Projection` satisfies `original_root_pair` under the displayed hypotheses. -/
theorem original_root_pair (axis : Axis) (cs : List ℤ) (z : ℂ) (hz : (inputPoly cs).eval z=0) :
    bivariateValue axis (symbolic axis (entries cs 0)) (z.re : ℂ) (z.im : ℂ)=0 ∧
      bivariateValue axis (symbolic axis (entries cs 1)) (z.re : ℂ) (z.im : ℂ)=0 := by
  have he : (z.re : ℂ)+Complex.I*(z.im : ℂ)=z := by simpa only [mul_comm] using Complex.re_add_im z
  have hh := plus_identity axis cs (z.re : ℂ) (z.im : ℂ)
  rw [he,hz] at hh
  have hu := symbolic_real axis (entries cs 0) z.re z.im
  have hv := symbolic_real axis (entries cs 1) z.re z.im
  have hr := congrArg Complex.re hh
  have hi := congrArg Complex.im hh
  simp only [Complex.zero_re,Complex.add_re,Complex.I_mul_re,hv,neg_zero,add_zero] at hr
  simp only [Complex.zero_im,Complex.add_im,Complex.I_mul_im,hu,zero_add] at hi
  constructor
  · exact Complex.ext hr.symm hu
  · exact Complex.ext hi.symm hv

/-- The finite construction in `Projection` satisfies `generated_coordinate_zero` under the displayed hypotheses. -/
theorem generated_coordinate_zero (axis : Axis) (cs : List ℤ) (D m n : ℕ)
    (hlen : cs.length=D+1) (hD : 0 < D) (hlead : cs.getD D 0≠0)
    (hm : sourceDegree axis (entries cs 0)=some m) (hn : sourceDegree axis (entries cs 1)=some n)
    (z : ℂ) (hz : (inputPoly cs).eval z=0) :
    ((symbolic axis (entries cs 0)).resultant (symbolic axis (entries cs 1)) m n).eval₂
      (Int.castRingHom ℂ) (match axis with | .real => (z.re : ℂ) | .imag => (z.im : ℂ))=0 := by
  have hFm : (symbolic axis (entries cs 0)).natDegree ≤ m := by
    apply symbolic_degree
    intro t ht
    exact (List.max?_eq_some_iff.mp hm).2 _ (List.mem_map.mpr ⟨t,ht,rfl⟩)
  have hGn : (symbolic axis (entries cs 1)).natDegree ≤ n := by
    apply symbolic_degree
    intro t ht
    exact (List.max?_eq_some_iff.mp hn).2 _ (List.mem_map.mpr ⟨t,ht,rfl⟩)
  have hs := actual_sizes_positive axis cs D m n hlen hD hlead hm hn
  obtain ⟨hU,hV⟩ := original_root_pair axis cs z hz
  cases axis with
  | real =>
    have hh := ActualProjectionResultantCriteria.fixed_common_root_zero
      (complexSpecialize (symbolic Axis.real (entries cs 0)) (z.re : ℂ))
      (complexSpecialize (symbolic Axis.real (entries cs 1)) (z.re : ℂ)) m n
      (Polynomial.natDegree_map_le.trans hFm) (Polynomial.natDegree_map_le.trans hGn) hs
      (z.im : ℂ) ((eval_real _ _ _).trans hU) ((eval_real _ _ _).trans hV)
    exact (Polynomial.resultant_map_map _ _ m n (Polynomial.eval₂RingHom (Int.castRingHom ℂ) (z.re : ℂ))).symm.trans hh
  | imag =>
    have hh := ActualProjectionResultantCriteria.fixed_common_root_zero
      (complexSpecialize (symbolic Axis.imag (entries cs 0)) (z.im : ℂ))
      (complexSpecialize (symbolic Axis.imag (entries cs 1)) (z.im : ℂ)) m n
      (Polynomial.natDegree_map_le.trans hFm) (Polynomial.natDegree_map_le.trans hGn) hs
      (z.re : ℂ) ((eval_imag _ _ _).trans hU) ((eval_imag _ _ _).trans hV)
    exact (Polynomial.resultant_map_map _ _ m n (Polynomial.eval₂RingHom (Int.castRingHom ℂ) (z.im : ℂ))).symm.trans hh

end ActualProjectionGeneratedCoordinates


namespace ActualProjectionOutputCanonical
open ActualYunRationalArray ActualYunRationalCanonical ActualYunPrimitive ActualSturmArrayTools
open ActualProjectionEntries ActualProjectionEntryDegrees ActualProjectionGeneratedAxes

/-- The finite construction in `Projection` satisfies `run_canonical` under the displayed hypotheses. -/
theorem run_canonical (fuel : ℕ) (values b out : List ℚ) (k : ℕ) (result : List ℚ)
    (hr : ActualProjectionInterpolationLoop.run fuel values b out k=some result) : Canonical result := by
  induction fuel generalizing values b out k with
  | zero =>
    cases values with
    | nil => have he := Option.some.inj hr; subst result; exact trim_canonical out
    | cons v vs => simp [ActualProjectionInterpolationLoop.run] at hr
  | succ fuel ih =>
    cases values with
    | nil => have he := Option.some.inj hr; subst result; exact trim_canonical out
    | cons v vs => exact ih _ _ _ _ hr

/-- The finite construction in `Projection` satisfies `interpolate_canonical` under the displayed hypotheses. -/
theorem interpolate_canonical (values result : List ℚ)
    (hr : ActualProjectionInterpolationLoop.interpolate values=some result) : Canonical result :=
  run_canonical values.length values [1] [] 0 result hr

/-- The finite construction in `Projection` satisfies `finish_lift` under the displayed hypotheses. -/
theorem finish_lift (out : List ℚ) (result : List ℤ)
    (hr : ActualProjectionIntegerGuard.finish out=some result) : lift result=out := by
  unfold ActualProjectionIntegerGuard.finish at hr
  split_ifs at hr with hbad
  have he := Option.some.inj hr
  subst result
  have ha : out.any (fun c => decide (c.den≠1))=false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hbad (Or.inr h)
  have hd : ∀ c∈out,c.den=1 := by
    intro c hc
    have hh := List.any_eq_false.mp ha c hc
    simpa only [decide_eq_true_eq,not_ne_iff] using hh
  simp only [lift,List.map_map]
  calc
    _ = out.map (fun c : ℚ => c) := by
      apply List.map_congr_left
      intro c hc
      exact Rat.coe_int_num_of_den_eq_one (hd c hc)
    _ = out := List.map_id out

/-- The finite construction in `Projection` satisfies `axis_output_canonical` under the displayed hypotheses. -/
theorem axis_output_canonical (axis : Axis) (u v : List Term) (D : ℕ) (result : List ℤ)
    (hr : axisProject axis u v D=some result) : Canonical (lift result) := by
  unfold axisProject at hr
  obtain ⟨m,_,hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨n,_,hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨out,hout,hfinish⟩ := Option.bind_eq_some_iff.mp hr
  rw [finish_lift out result hfinish]
  exact interpolate_canonical _ _ hout

end ActualProjectionOutputCanonical


namespace ActualProjectionProducedArrays
open Polynomial ActualProjectionEntries ActualProjectionEntryDegrees
open ActualProjectionEntrySpecialization ActualProjectionGeneratedAxes
open ActualProjectionGeneratedNonzero ActualProjectionGeneratedCoordinates
open ActualProjectionBinomialEval ActualProjectionOutputCanonical
open ActualYunRationalArray ActualYunRationalCanonical ActualYunPrimitive ActualYunPrimitiveContent
open ActualSturmArrayTools

/-- Construction for coordinate in the projection model. -/
def coordinate (axis : Axis) (z : ℂ) : ℝ := match axis with | .real => z.re | .imag => z.im

/-- Construction for Output Properties in the projection model. -/
def OutputProperties (cs : List ℤ) (axis : Axis) (out : List ℤ) : Prop :=
  Canonical (lift out) ∧ poly (lift out)≠0 ∧ 0 < (poly (lift out)).natDegree ∧
    ∀ z : ℂ,(inputPoly cs).eval z=0 → (inputPoly out).eval (coordinate axis z : ℂ)=0

/-- The finite construction in `Projection` satisfies `original_degree` under the displayed hypotheses. -/
theorem original_degree (cs : List ℤ) (D : ℕ) (hlen : cs.length=D+1) (hlead : cs.getD D 0≠0) :
    (inputPoly cs).natDegree=D := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [input_coeff,List.getD_eq_default _ _ (by omega),Int.cast_zero]
  · rw [input_coeff]
    exact_mod_cast hlead

/-- The finite construction in `Projection` satisfies `original_exists_root` under the displayed hypotheses. -/
theorem original_exists_root (cs : List ℤ) (D : ℕ) (hlen : cs.length=D+1)
    (hD : 0 < D) (hlead : cs.getD D 0≠0) : ∃ z : ℂ,(inputPoly cs).eval z=0 := by
  have hd : 0 < (inputPoly cs).degree := Polynomial.natDegree_pos_iff_degree_pos.mp
    (by rw [original_degree cs D hlen hlead]; exact hD)
  exact IsAlgClosed.exists_root _ (ne_of_gt hd)

/-- The finite construction in `Projection` satisfies `actual_axis_output` under the displayed hypotheses. -/
theorem actual_axis_output (axis : Axis) (cs : List ℤ) (D : ℕ) (hlen : cs.length=D+1)
    (hD : 0 < D) (hlead : cs.getD D 0≠0) :
    ∃ out,axisProject axis (ActualProjectionDictionary.dictionaries cs).1
      (ActualProjectionDictionary.dictionaries cs).2 (cs.length-1)=some out ∧ OutputProperties cs axis out := by
  obtain ⟨out,m,n,hr,hm,hn,hp,hpn⟩ := actual_axis_success axis cs D hlen hD hlead
  have hcoord : ∀ z : ℂ,(inputPoly cs).eval z=0 → (inputPoly out).eval (coordinate axis z : ℂ)=0 := by
    intro z hz
    rw [inputPoly,Polynomial.eval_map,hp]
    cases axis <;> exact generated_coordinate_zero _ cs D m n hlen hD hlead hm hn z hz
  have houtn : inputPoly out≠0 := by
    intro hzero
    apply hpn
    apply Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
    simpa only [inputPoly,Polynomial.map_zero] using hzero
  have hmap : (poly (lift out)).map (Rat.castHom ℂ)=inputPoly out := by
    rw [lift_poly,integerPolyQ_map]
    rfl
  have hqn : poly (lift out)≠0 := by
    intro hz
    apply houtn
    rw [← hmap,hz,Polynomial.map_zero]
  obtain ⟨z,hz⟩ := original_exists_root cs D hlen hD hlead
  have hpos : 0 < (inputPoly out).natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr
    (Polynomial.degree_pos_of_root houtn (hcoord z hz))
  have hqpos : 0 < (poly (lift out)).natDegree := by
    have hle := Polynomial.natDegree_map_le (f := Rat.castHom ℂ) (p := poly (lift out))
    rw [hmap] at hle
    omega
  exact ⟨out,hr,axis_output_canonical axis _ _ _ out hr,hqn,hqpos,hcoord⟩

/-- The finite construction in `Projection` satisfies `actual_projection_pair` under the displayed hypotheses. -/
theorem actual_projection_pair (cs : List ℤ) (D : ℕ) (hlen : cs.length=D+1)
    (hD : 0 < D) (hlead : cs.getD D 0≠0) :
    ∃ rx ry,projections cs=(some rx,some ry) ∧ OutputProperties cs Axis.real rx ∧ OutputProperties cs Axis.imag ry := by
  obtain ⟨rx,hrx,hx⟩ := actual_axis_output Axis.real cs D hlen hD hlead
  obtain ⟨ry,hry,hy⟩ := actual_axis_output Axis.imag cs D hlen hD hlead
  exact ⟨rx,ry,by simp only [projections,hrx,hry],hx,hy⟩

end ActualProjectionProducedArrays


namespace ActualProjectionSturmAxes
open Polynomial ActualProjectionProducedArrays ActualProjectionGeneratedAxes
open ActualProjectionBinomialEval ActualProjectionEntryDegrees
open ActualYunRationalArray ActualYunRationalCanonical ActualSturmArrayTools
open ActualSturmSourceCount ActualSturmQueueCoverage ActualSturmQueueGeometry
open ActualSturmIntervalSort ActualSturmComputedIsolation

/-- Construction for isolate Axes in the projection model. -/
def isolateAxes (cs : List ℤ) (bits fuelX fuelY : ℕ) : Option (List (ℚ×ℚ) × List (ℚ×ℚ)) :=
  match projections cs with
  | (some rx,some ry) => (intervals (lift rx) bits fuelX).bind (fun ix =>
      (intervals (lift ry) bits fuelY).map (fun iy => (ix,iy)))
  | _ => none

/-- The finite construction in `Projection` satisfies `real_root_member` under the displayed hypotheses. -/
theorem real_root_member (out : List ℤ) (hn : poly (lift out)≠0) (x : ℝ)
    (hx : (inputPoly out).eval (x : ℂ)=0) : x∈inputRoots (lift out) := by
  let P := (poly (lift out)).map (Rat.castHom ℝ)
  have hhom : Complex.ofRealHom.comp (Rat.castHom ℝ)=Rat.castHom ℂ := Subsingleton.elim _ _
  have hm : P.map Complex.ofRealHom=inputPoly out := by
    dsimp only [P]
    rw [Polynomial.map_map,hhom,lift_poly,ActualYunPrimitive.integerPolyQ_map]
    rfl
  have hh := Polynomial.eval_map_apply (f := Complex.ofRealHom) (p := P) x
  rw [hm] at hh
  change (inputPoly out).eval (x : ℂ)=((P.eval x : ℝ) : ℂ) at hh
  rw [hx] at hh
  have hp : P.eval x=0 := by exact_mod_cast hh.symm
  rw [inputRoots,Multiset.mem_toFinset,Polynomial.mem_roots (Polynomial.map_ne_zero hn)]
  exact hp

/-- Construction for Isolation Properties in the projection model. -/
def IsolationProperties (cs : List ℤ) (axis : Axis) (out : List ℤ) (bits : ℕ) (ps : List (ℚ×ℚ)) : Prop :=
  (∀ p∈ps,GoodInterval (inputRoots (lift out)) (sourceWidth bits) p) ∧
    (∀ x∈inputRoots (lift out),hits ps x=1) ∧ ps.Pairwise Apart ∧ ps.Pairwise LexLE ∧
    ∀ z : ℂ,(inputPoly cs).eval z=0 → hits ps (coordinate axis z)=1

/-- The finite construction in `Projection` satisfies `actual_axis_isolation` under the displayed hypotheses. -/
theorem actual_axis_isolation (cs : List ℤ) (axis : Axis) (out : List ℤ)
    (houtput : OutputProperties cs axis out) (bits : ℕ) :
    ∃ fuel ps,intervals (lift out) bits fuel=some ps ∧ IsolationProperties cs axis out bits ps := by
  obtain ⟨hcan,hn,hd,hcoord⟩ := houtput
  obtain ⟨fuel,ps,hrun,hgood,hcover,hapart,hsort⟩ := computed_isolation (lift out) hcan hn hd bits
  exact ⟨fuel,ps,hrun,hgood,hcover,hapart,hsort,fun z hz =>
    hcover _ (real_root_member out hn (coordinate axis z) (hcoord z hz))⟩

/-- The finite construction in `Projection` satisfies `computed_axes` under the displayed hypotheses. -/
theorem computed_axes (cs : List ℤ) (D bits : ℕ) (hlen : cs.length=D+1)
    (hD : 0 < D) (hlead : cs.getD D 0≠0) :
    ∃ fuelX fuelY rx ry ix iy,projections cs=(some rx,some ry) ∧
      isolateAxes cs bits fuelX fuelY=some (ix,iy) ∧
      OutputProperties cs Axis.real rx ∧ OutputProperties cs Axis.imag ry ∧
      IsolationProperties cs Axis.real rx bits ix ∧ IsolationProperties cs Axis.imag ry bits iy := by
  obtain ⟨rx,ry,hpr,hx,hy⟩ := actual_projection_pair cs D hlen hD hlead
  obtain ⟨fuelX,ix,hrx,hix⟩ := actual_axis_isolation cs Axis.real rx hx bits
  obtain ⟨fuelY,iy,hry,hiy⟩ := actual_axis_isolation cs Axis.imag ry hy bits
  exact ⟨fuelX,fuelY,rx,ry,ix,iy,hpr,by simp only [isolateAxes,hpr,hrx,hry,Option.bind_some,Option.map_some],hx,hy,hix,hiy⟩

end ActualProjectionSturmAxes


namespace ActualProjectionCartesian
open ActualProjectionSturmAxes ActualProjectionProducedArrays ActualProjectionGeneratedAxes
open ActualProjectionBinomialEval ActualProjectionEntryDegrees
open ActualSturmQueueCoverage ActualSturmComputedIsolation
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- Abbreviation for Interval in the projection model. -/
abbrev Interval := ℚ×ℚ
/-- Abbreviation for Rectangle in the projection model. -/
abbrev Rectangle := Interval×Interval

/-- Construction for rectangles in the projection model. -/
def rectangles (ix iy : List Interval) : List Rectangle :=
  ix.flatMap (fun px => iy.map (fun py => (px,py)))

/-- Construction for rectangle Hit in the projection model. -/
def rectangleHit (r : Rectangle) (z : ℂ) : ℕ := hit r.1 z.re*hit r.2 z.im

/-- Construction for rectangle Hits in the projection model. -/
def rectangleHits (rs : List Rectangle) (z : ℂ) : ℕ := (rs.map (fun r => rectangleHit r z)).sum

/-- Construction for midpoint in the projection model. -/
def midpoint (p : Interval) : ℚ := (p.1+p.2)/2

/-- Construction for centers in the projection model. -/
def centers (ix iy : List Interval) : List (ℚ×ℚ) :=
  (ix.map midpoint).flatMap (fun x => (iy.map midpoint).map (fun y => (x,y)))

/-- The finite construction in `Projection` satisfies `centers_rectangles` under the displayed hypotheses. -/
theorem centers_rectangles (ix iy : List Interval) :
    centers ix iy=(rectangles ix iy).map (fun r => (midpoint r.1,midpoint r.2)) := by
  induction ix with
  | nil => rfl
  | cons px ps ih =>
    change ((iy.map midpoint).map (fun y => (midpoint px,y))++centers ps iy)=
      ((iy.map (fun py => (px,py))++rectangles ps iy).map (fun r => (midpoint r.1,midpoint r.2)))
    rw [List.map_append,ih,List.map_map,List.map_map]
    rfl

/-- The finite construction in `Projection` satisfies `rectangle_hits_product` under the displayed hypotheses. -/
theorem rectangle_hits_product (ix iy : List Interval) (z : ℂ) :
    rectangleHits (rectangles ix iy) z=hits ix z.re*hits iy z.im := by
  induction ix with
  | nil => simp [rectangles,rectangleHits,hits]
  | cons px ps ih =>
    have hrow : ((iy.map (fun py => (px,py))).map (fun r => rectangleHit r z)).sum=
        hit px z.re*hits iy z.im := by
      clear ih
      induction iy with
      | nil => simp [hits]
      | cons py ys ihy =>
        simp only [List.map_cons,List.sum_cons,hits_cons]
        rw [ihy]
        dsimp only [rectangleHit]
        ring
    change ((iy.map (fun py => (px,py))++rectangles ps iy).map (fun r => rectangleHit r z)).sum=_
    rw [List.map_append,List.sum_append,hrow]
    change hit px z.re*hits iy z.im+rectangleHits (rectangles ps iy) z=_
    rw [ih,hits_cons]
    ring

/-- The finite construction in `Projection` satisfies `containing_interval` under the displayed hypotheses. -/
theorem containing_interval (ps : List Interval) (x : ℝ) (hh : hits ps x=1) :
    ∃ p∈ps,(p.1 : ℝ)<x ∧ x<(p.2 : ℝ) := by
  classical
  induction ps with
  | nil => simp [hits] at hh
  | cons p ps ih =>
    by_cases hp : (p.1 : ℝ)<x ∧ x<(p.2 : ℝ)
    · exact ⟨p,by simp,hp⟩
    · have hz : hit p x=0 := ite_eq_right hp
      rw [hits_cons,hz,zero_add] at hh
      obtain ⟨q,hq,hqx⟩ := ih hh
      exact ⟨q,by simp only [List.mem_cons]; exact Or.inr hq,hqx⟩

/-- The estimate `midpoint_error` retains the actual parameter, input-error and normalization budgets. -/
theorem midpoint_error (ax bx ay byy e : ℚ) (z : ℂ)
    (hax : (ax : ℝ) ≤ z.re) (hbx : z.re ≤ (bx : ℝ))
    (hay : (ay : ℝ) ≤ z.im) (hby : z.im ≤ (byy : ℝ))
    (hx : bx-ax ≤ e) (hy : byy-ay ≤ e) :
    ‖rootRationalCoordinate (midpoint (ax,bx),midpoint (ay,byy))-z‖ ≤ (e : ℝ) := by
  have hxR : (bx : ℝ)-(ax : ℝ) ≤ (e : ℝ) := by exact_mod_cast hx
  have hyR : (byy : ℝ)-(ay : ℝ) ≤ (e : ℝ) := by exact_mod_cast hy
  have hr : |((ax : ℝ)+bx)/2-z.re| ≤ (e : ℝ)/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hi : |((ay : ℝ)+byy)/2-z.im| ≤ (e : ℝ)/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  change |(((ax+bx)/2 : ℚ) : ℝ)-z.re|+|(((ay+byy)/2 : ℚ) : ℝ)-z.im| ≤ (e : ℝ)
  push_cast
  linarith

/-- The finite construction in `Projection` satisfies `source_midpoint_near` under the displayed hypotheses. -/
theorem source_midpoint_near (cs : List ℤ) (rx ry : List ℤ) (bits : ℕ) (ix iy : List Interval)
    (hx : IsolationProperties cs Axis.real rx bits ix) (hy : IsolationProperties cs Axis.imag ry bits iy)
    (z : ℂ) (hz : (inputPoly cs).eval z=0) :
    rectangleHits (rectangles ix iy) z=1 ∧
      ∃ c∈centers ix iy,‖rootRationalCoordinate c-z‖ ≤ (sourceWidth bits : ℝ) := by
  have hxr : hits ix z.re=1 := hx.2.2.2.2 z hz
  have hyr : hits iy z.im=1 := hy.2.2.2.2 z hz
  refine ⟨by rw [rectangle_hits_product,hxr,hyr,mul_one],?_⟩
  obtain ⟨px,hpx,hxp⟩ := containing_interval ix z.re hxr
  obtain ⟨py,hpy,hyp⟩ := containing_interval iy z.im hyr
  have hwx := (hx.1 px hpx).2.2.2.2
  have hwy := (hy.1 py hpy).2.2.2.2
  refine ⟨(midpoint px,midpoint py),?_,?_⟩
  · apply List.mem_flatMap.mpr
    refine ⟨midpoint px,List.mem_map.mpr ⟨px,hpx,rfl⟩,?_⟩
    exact List.mem_map.mpr ⟨midpoint py,List.mem_map.mpr ⟨py,hpy,rfl⟩,rfl⟩
  · exact midpoint_error px.1 px.2 py.1 py.2 (sourceWidth bits)
      z hxp.1.le hxp.2.le hyp.1.le hyp.2.le hwx hwy

/-- The finite construction in `Projection` satisfies `computed_cartesian` under the displayed hypotheses. -/
theorem computed_cartesian (cs : List ℤ) (D bits : ℕ) (hlen : cs.length=D+1)
    (hD : 0 < D) (hlead : cs.getD D 0≠0) :
    ∃ fuelX fuelY ix iy,isolateAxes cs bits fuelX fuelY=some (ix,iy) ∧
      ∀ z : ℂ,(inputPoly cs).eval z=0 → rectangleHits (rectangles ix iy) z=1 ∧
        ∃ c∈centers ix iy,‖rootRationalCoordinate c-z‖ ≤ (sourceWidth bits : ℝ) := by
  obtain ⟨fuelX,fuelY,rx,ry,ix,iy,_,hr,_,_,hx,hy⟩ := computed_axes cs D bits hlen hD hlead
  exact ⟨fuelX,fuelY,ix,iy,hr,fun z hz => source_midpoint_near cs rx ry bits ix iy hx hy z hz⟩

end ActualProjectionCartesian



end RootYunInternal
end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
