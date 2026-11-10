/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentGramCompact
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open scoped Classical BigOperators ComplexOrder
variable {n : ℕ} [NeZero n]

omit [NeZero n] in

theorem gramShift_active_value (r i : Fin n) (h : r.val≤(i+r).val) :
    (i+r).val=i.val+r.val := by
  rw [Fin.val_add] at h ⊢
  by_cases hn : i.val+r.val<n
  · exact Nat.mod_eq_of_lt hn
  · have hh : i.val+r.val-n<n := by omega
    rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt hh] at h
    omega

theorem genTrace_zero_prefix_shift (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (r : Fin n)
    (hzero : ∀ i : Fin n,i.val<r.val → ∀ j : Fin n,A i j=0) (k : ℤ) :
    genTrace (A.submatrix (Equiv.addRight r) (Equiv.addRight r)) k=genTrace A k := by
  let E := Equiv.addRight r
  have hcol (i j : Fin n) (hj : j.val<r.val) : A i j=0 := by
    have h : star (A j i)=A i j := by
      simpa only [Matrix.conjTranspose_apply] using congrFun (congrFun hA i) j
    rw [← h,hzero j hj i,star_zero]
  have hpoint (i j : Fin n) :
      (if (j.val : ℤ)-(i.val : ℤ)=k then A (E i) (E j) else 0)=
        (if ((E j).val : ℤ)-((E i).val : ℤ)=k then A (E i) (E j) else 0) := by
    by_cases hi : (E i).val<r.val
    · simp only [hzero (E i) hi (E j),ite_self]
    · by_cases hj : (E j).val<r.val
      · simp only [hcol (E i) (E j) hj,ite_self]
      · have hvi := gramShift_active_value r i (show r.val≤(E i).val from Nat.le_of_not_gt hi)
        have hvj := gramShift_active_value r j (show r.val≤(E j).val from Nat.le_of_not_gt hj)
        have hd : ((E j).val : ℤ)-((E i).val : ℤ)=(j.val : ℤ)-(i.val : ℤ) := by
          change (((j+r).val : ℕ) : ℤ)-(((i+r).val : ℕ) : ℤ)=_
          rw [hvi,hvj,Nat.cast_add,Nat.cast_add]
          ring
        rw [hd]
  unfold genTrace
  simp only [Matrix.submatrix_apply]
  calc
    _ = ∑ i : Fin n,∑ j : Fin n,
        if ((E j).val : ℤ)-((E i).val : ℤ)=k then A (E i) (E j) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun j _ => hpoint i j)
    _ = ∑ i : Fin n,∑ j : Fin n,if (j.val : ℤ)-(i.val : ℤ)=k then A i j else 0 := by
      have hinner (p : Fin n) : (∑ j : Fin n,if ((E j).val : ℤ)-(p.val : ℤ)=k then A p (E j) else 0)=
          ∑ j : Fin n,if (j.val : ℤ)-(p.val : ℤ)=k then A p j else 0 :=
        Equiv.sum_comp E (fun j => if (j.val : ℤ)-(p.val : ℤ)=k then A p j else 0)
      simp_rw [hinner]
      exact Equiv.sum_comp E (fun i => ∑ j : Fin n,if (j.val : ℤ)-(i.val : ℤ)=k then A i j else 0)

omit [NeZero n] in

theorem exists_first_positive_gram_diagonal (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (hA0 : A≠0) :
    ∃ r : Fin n,0<(A r r).re ∧ ∀ i : Fin n,i.val<r.val → ∀ j : Fin n,A i j=0 := by
  have hexdiag : ∃ i : Fin n,0<(A i i).re := by
    by_contra h
    push Not at h
    have hz (i : Fin n) : A i i=0 := by
      have hp := Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))
      apply Complex.ext
      · change (A i i).re=0
        linarith [h i]
      · exact hp.2.symm
    apply hA0
    apply hA.trace_eq_zero_iff.mp
    simp [Matrix.trace,hz]
  have hex : ∃ k : ℕ,∃ hk : k<n,0<(A ⟨k,hk⟩ ⟨k,hk⟩).re := by
    obtain ⟨i,hi⟩ := hexdiag
    exact ⟨i.val,i.isLt,hi⟩
  obtain ⟨hr,hpos⟩ := Nat.find_spec hex
  let r : Fin n := ⟨Nat.find hex,hr⟩
  refine ⟨r,hpos,?_⟩
  intro i hi j
  have hnonpos : (A i i).re≤0 := by
    by_contra hp
    have hpositive : 0<(A i i).re := by linarith
    exact Nat.find_min hex hi ⟨i.isLt,hpositive⟩
  have hp := Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))
  have hdiag : A i i=0 := Complex.ext (by change (A i i).re=0; linarith) hp.2.symm
  have hcol := posSemidef_column_zero_of_diag_zero A hA i hdiag j
  have hherm : star (A j i)=A i j := by
    simpa only [Matrix.conjTranspose_apply] using congrFun (congrFun hA.isHermitian i) j
  rw [← hherm,hcol,star_zero]

theorem maximal_gram_first_pos (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosSemidef) (hB0 : B≠0)
    (hmax : ∀ C : Matrix (Fin n) (Fin n) ℂ,C.PosSemidef →
      (∀ k : ℤ,genTrace C k=genTrace B k) → C 0 0≤B 0 0) : 0<(B 0 0).re := by
  obtain ⟨r,hr,hzero⟩ := exists_first_positive_gram_diagonal B hB hB0
  let E := Equiv.addRight r
  have hp := hmax (B.submatrix E E) (hB.submatrix E)
    (genTrace_zero_prefix_shift B hB.isHermitian r hzero)
  have he : E (0 : Fin n)=r := by simp [E]
  change B (E 0) (E 0)≤B 0 0 at hp
  rw [he] at hp
  exact hr.trans_le (Complex.le_def.mp hp).1
end Qatlib.Concepts.OrderedOracle.TiSdpBridge
