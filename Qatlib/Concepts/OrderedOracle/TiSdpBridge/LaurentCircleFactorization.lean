/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentGram
import Qatlib.Concepts.LaurentPolys.CircleComplement
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Polynomial Matrix
open scoped BigOperators Classical ComplexOrder

def complexLaurentCoefficient {n : ℕ} (a : Fin n → ℂ) (j : ℤ) : ℂ :=
  if h : j.natAbs < n then
    if j < 0 then star (a ⟨j.natAbs,h⟩) else a ⟨j.natAbs,h⟩
  else 0

def complexLaurentEval {n : ℕ} (a : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(n : ℤ)+1) ((n : ℤ)-1), complexLaurentCoefficient a j * z^j

def complexLaurentNonnegative {n : ℕ} (a : Fin n → ℂ) : Prop :=
  (complexLaurentCoefficient a 0).im = 0 ∧
  ∀ z : ℂ, ‖z‖=1 → 0 ≤ (complexLaurentEval a z).re

def laurentCoefficientPolynomial {n : ℕ} (p : Fin n → ℂ) : Polynomial ℂ :=
  ∑ i : Fin n, Polynomial.monomial i.val (p i)

theorem complexLaurentEval_genTrace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (z : ℂ) :
    complexLaurentEval (n := n) (fun k : Fin n => genTrace A (k : ℤ)) z = matrixLaurent A z := by
  unfold complexLaurentEval matrixLaurent
  refine Finset.sum_congr rfl fun j hj => ?_
  have hlt : j.natAbs < n := by
    simp only [Finset.mem_Icc] at hj
    omega
  unfold complexLaurentCoefficient
  rw [dif_pos hlt]
  by_cases hjz : j < 0
  · have he : star (genTrace A (j.natAbs : ℤ)) = genTrace A j := by
      have hg := genTrace_neg_of_isHermitian A hA (j.natAbs : ℤ)
      rw [show -((j.natAbs : ℤ)) = j from by omega] at hg
      exact hg.symm
    rw [he]
    simp only [if_pos hjz]
  · have hnabs : (⟨j.natAbs, hlt⟩ : Fin n).val = j := Int.natAbs_of_nonneg (by omega)
    simp only [hnabs, if_neg hjz]

theorem complexLaurent_coeff_eq_of_eval_eq {n : ℕ} (a b : Fin n → ℂ)
    (h : ∀ z : ℂ, ‖z‖ = 1 → complexLaurentEval a z = complexLaurentEval b z)
    (i : Fin n) : a i = b i := by
  by_cases hn : 0 < n
  swap
  · exact absurd i.2 (by omega)
  classical
  have hcoef (f : Fin n → ℂ) (j : Fin n) : complexLaurentCoefficient f (j : ℤ) = f j := by
    have hnabs : ((j : ℤ)).natAbs = (j : ℕ) := by
      have h1 : ((j : ℤ)).natAbs = ((j : ℕ) : ℤ) := Int.natAbs_of_nonneg (by omega)
      exact_mod_cast h1
    unfold complexLaurentCoefficient
    rw [hnabs, dif_pos j.isLt, if_neg (by omega)]
  have hwin : ∀ z : ℂ, ‖z‖ = 1 →
      ∑ j ∈ Finset.Icc (-(n : ℤ)+1) ((n : ℤ)-1),
        (complexLaurentCoefficient a j - complexLaurentCoefficient b j) * z ^ j = 0 := by
    intro z hz
    have hd := h z hz
    unfold complexLaurentEval at hd
    simp only [sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hd
  have htw (t : ℕ) : ∀ z : ℂ, z ^ n = (-1 : ℂ) ^ t →
      ∑ j : Fin n, (if (j : ℕ) = 0 then
            complexLaurentCoefficient a 0 - complexLaurentCoefficient b 0
          else (complexLaurentCoefficient a (j : ℤ) - complexLaurentCoefficient b (j : ℤ)) +
            (-1 : ℂ) ^ t * (complexLaurentCoefficient a ((j : ℤ) - n) -
              complexLaurentCoefficient b ((j : ℤ) - n))) * z ^ (j : ℕ) = 0 := by
    intro z hz
    rw [← sum_laurent_window_at_root hn t
      (fun j => complexLaurentCoefficient a j - complexLaurentCoefficient b j) z hz]
    exact hwin z (norm_eq_one_of_twisted_root hn t hz)
  have heven := coeff_zero_of_twisted_root_evaluations hn 0
    (fun j => if (j : ℕ) = 0 then
        complexLaurentCoefficient a 0 - complexLaurentCoefficient b 0
      else (complexLaurentCoefficient a (j : ℤ) - complexLaurentCoefficient b (j : ℤ)) +
        (-1 : ℂ) ^ 0 * (complexLaurentCoefficient a ((j : ℤ) - n) -
          complexLaurentCoefficient b ((j : ℤ) - n))) (htw 0)
  have hodd := coeff_zero_of_twisted_root_evaluations hn 1
    (fun j => if (j : ℕ) = 0 then
        complexLaurentCoefficient a 0 - complexLaurentCoefficient b 0
      else (complexLaurentCoefficient a (j : ℤ) - complexLaurentCoefficient b (j : ℤ)) +
        (-1 : ℂ) ^ 1 * (complexLaurentCoefficient a ((j : ℤ) - n) -
          complexLaurentCoefficient b ((j : ℤ) - n))) (htw 1)
  have hzero : complexLaurentCoefficient a 0 = complexLaurentCoefficient b 0 :=
    sub_eq_zero.mp (show complexLaurentCoefficient a 0 - complexLaurentCoefficient b 0 = 0 by
      simpa using heven ⟨0, hn⟩)
  have hd (j : Fin n) (hj : (j : ℕ) ≠ 0) :
      complexLaurentCoefficient a (j : ℤ) = complexLaurentCoefficient b (j : ℤ) := by
    have he := heven j
    have ho := hodd j
    simp only [hj, if_false, pow_zero, one_mul, pow_one, neg_one_mul] at he ho
    have h2 : (complexLaurentCoefficient a (j : ℤ) - complexLaurentCoefficient b (j : ℤ)) * 2
        = 0 := by linear_combination he + ho
    rcases mul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (by norm_num)
  by_cases hi0 : (i : ℕ) = 0
  · have hiz : (i : ℤ) = 0 := by exact_mod_cast hi0
    rw [← hcoef a i, ← hcoef b i, hiz]
    exact hzero
  · rw [← hcoef a i, ← hcoef b i]
    exact hd i hi0

theorem complexLaurentEval_eq_matrixLaurent_of_genTrace {n : ℕ} (a : Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hcoeff : ∀ j : ℤ, genTrace A j = complexLaurentCoefficient a j) (z : ℂ) :
    complexLaurentEval a z = matrixLaurent A z := by
  unfold complexLaurentEval matrixLaurent
  exact Finset.sum_congr rfl fun j _ => by rw [hcoeff j]

theorem complexLaurentNonnegative_of_gram_posSemidef {n : ℕ} (a : Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    (hcoeff : ∀ j : ℤ, genTrace A j = complexLaurentCoefficient a j) :
    complexLaurentNonnegative a := by
  unfold complexLaurentNonnegative
  refine ⟨?_, fun z hz => ?_⟩
  · rw [← hcoeff 0, genTrace_zero]
    have htr : star A.trace = A.trace := by
      rw [← Matrix.trace_conjTranspose, hA.isHermitian]
    have h1 := congrArg Complex.im htr
    rw [Complex.star_def, Complex.conj_im] at h1
    linarith
  · rw [complexLaurentEval_eq_matrixLaurent_of_genTrace a A hcoeff z]
    exact (matrixLaurent_real_nonneg_of_posSemidef A hA hz).2

theorem genTrace_eq_zero_of_natAbs_ge {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (j : ℤ) (hj : n ≤ j.natAbs) : genTrace A j = 0 := by
  unfold genTrace
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro k _
  have hne : (k.val : ℤ)-(i.val : ℤ) ≠ j := by
    have hi := i.isLt
    have hk := k.isLt
    omega
  simp [hne]

theorem complexLaurentCoefficient_nat {n : ℕ} (a : Fin n → ℂ) (i : Fin n) :
    complexLaurentCoefficient a (i.val : ℤ) = a i := by
  simp only [complexLaurentCoefficient, Int.natAbs_natCast, dif_pos i.isLt]
  simp

theorem laurentCoefficientPolynomial_eval {n : ℕ} (p : Fin n → ℂ) (z : ℂ) :
    (laurentCoefficientPolynomial p).eval z = ∑ i : Fin n, p i*z^i.val := by
  simp [laurentCoefficientPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem laurentCoefficientPolynomial_coeff {n : ℕ} (p : Fin n → ℂ) (k : ℕ) :
    (laurentCoefficientPolynomial p).coeff k = if h : k<n then p ⟨k,h⟩ else 0 := by
  unfold laurentCoefficientPolynomial
  rw [Polynomial.finsetSum_coeff]
  by_cases hk : k<n
  · rw [dif_pos hk]
    rw [Finset.sum_eq_single (⟨k,hk⟩ : Fin n)]
    · simp
    · intro i _ hi
      have hv : i.val≠k := by intro h; apply hi; exact Fin.ext h
      simp [Polynomial.coeff_monomial,hv]
    · simp
  · rw [dif_neg hk]
    apply Finset.sum_eq_zero
    intro i _
    have hv : i.val≠k := by have := i.isLt; omega
    simp [Polynomial.coeff_monomial,hv]

theorem laurentCoefficientPolynomial_degree {n : ℕ} (p : Fin n → ℂ) :
    (laurentCoefficientPolynomial p).natDegree ≤ n-1 := by
  apply natDegree_le_of_degree_le
  unfold laurentCoefficientPolynomial
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro i _
  exact (degree_monomial_le i.val (p i)).trans
    (by exact_mod_cast (show i.val ≤ n-1 by omega))

theorem gramOuter_positive_coeff_of_circle_factor {n : ℕ} (a p : Fin n → ℂ)
    (h : ∀ z : ℂ, ‖z‖=1 → complexLaurentEval a z =
      ((‖(laurentCoefficientPolynomial p).eval z‖^2 : ℝ) : ℂ)) (i : Fin n) :
    genTrace (gramOuter p) (i.val : ℤ) = a i := by
  let b : Fin n → ℂ := fun k => genTrace (gramOuter p) (k.val : ℤ)
  apply (complexLaurent_coeff_eq_of_eval_eq a b ?_ i).symm
  intro z hz
  rw [complexLaurentEval_genTrace _ (gramOuter_posSemidef p).isHermitian,
    matrixLaurent_outer_eq_abs_sq p hz, ← laurentCoefficientPolynomial_eval]
  exact h z hz

theorem genTrace_eq_complexLaurentCoefficient_of_positive {n : ℕ} (a : Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (h : ∀ i : Fin n, genTrace A (i.val : ℤ) = a i) (j : ℤ) :
    genTrace A j = complexLaurentCoefficient a j := by
  by_cases hj : j.natAbs < n
  · unfold complexLaurentCoefficient
    rw [dif_pos hj]
    by_cases hneg : j < 0
    · rw [if_pos hneg]
      have he : j = -(j.natAbs : ℤ) := by omega
      conv_lhs => rw [he]
      rw [genTrace_neg_of_isHermitian A hA, h ⟨j.natAbs,hj⟩]
    · rw [if_neg hneg]
      have he : j = (j.natAbs : ℤ) := by omega
      conv_lhs => rw [he]
      exact h ⟨j.natAbs,hj⟩
  · rw [genTrace_eq_zero_of_natAbs_ge A j (by omega)]
    simp [complexLaurentCoefficient, hj]

theorem gramOuter_coeff_of_circle_factor {n : ℕ} (a p : Fin n → ℂ)
    (h : ∀ z : ℂ, ‖z‖=1 → complexLaurentEval a z =
      ((‖(laurentCoefficientPolynomial p).eval z‖^2 : ℝ) : ℂ)) (j : ℤ) :
    genTrace (gramOuter p) j = complexLaurentCoefficient a j :=
  genTrace_eq_complexLaurentCoefficient_of_positive a (gramOuter p)
    (gramOuter_posSemidef p).isHermitian (gramOuter_positive_coeff_of_circle_factor a p h) j

private theorem laurent_reflected_factor_circle_norm (r z : ℂ) (hz : ‖z‖=1) :
    ‖1-star r*z‖ = ‖z-r‖ := by
  have hzz : z*star z=1 := by simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  calc
    _ = ‖z*star (z-r)‖ := by congr 1; rw [star_sub, mul_sub, hzz]; ring
    _ = _ := by rw [norm_mul, hz, norm_star, one_mul]

theorem polynomial_closed_disk_circle_factor (A : Polynomial ℂ) :
    ∃ B : Polynomial ℂ, B.natDegree ≤ A.natDegree ∧ (B=0 ↔ A=0) ∧
      (∀ z : ℂ, ‖z‖=1 → ‖B.eval z‖=‖A.eval z‖) ∧
      (B≠0 → ∀ z : ℂ, B.eval z=0 → ‖z‖≤1) := by
  generalize hd : A.natDegree=n
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
    by_cases ha0 : A=0
    · subst A
      exact ⟨0,by simp,Iff.rfl,fun _ _ => rfl,fun h => (h rfl).elim⟩
    by_cases hdeg : A.natDegree=0
    · obtain ⟨a,rfl⟩ := Polynomial.natDegree_eq_zero.mp hdeg
      have ha : a≠0 := by simpa using ha0
      exact ⟨C a,by simp,Iff.rfl,fun _ _ => rfl,
        fun _ z hz => (ha (by simpa using hz)).elim⟩
    obtain ⟨r,hr⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ A
      (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)))
    have hr' : A.IsRoot r := by simpa [Polynomial.IsRoot, Polynomial.aeval_def] using hr
    obtain ⟨g,hAg⟩ := Polynomial.dvd_iff_isRoot.mpr hr'
    have hg0 : g≠0 := by intro h; simp [h] at hAg; exact ha0 hAg
    have hdegree : A.natDegree=1+g.natDegree := by
      rw [hAg,natDegree_mul (X_sub_C_ne_zero r) hg0,natDegree_X_sub_C]
    obtain ⟨B,hBd,hB0,hBc,hBr⟩ := ih g.natDegree (by omega) g rfl
    have hBn : B≠0 := fun h => hg0 (hB0.mp h)
    by_cases hrin : ‖r‖≤1
    · have hprod : (X-C r)*B≠0 := mul_ne_zero (X_sub_C_ne_zero r) hBn
      refine ⟨(X-C r)*B,?_,iff_of_false hprod ha0,?_,?_⟩
      · have hh := natDegree_mul_le (p := X-C r) (q := B)
        rw [natDegree_X_sub_C] at hh
        omega
      · intro z hz
        simp only [eval_mul,norm_mul]
        rw [hBc z hz,hAg,eval_mul,norm_mul]
      · intro _ z hz
        simp only [eval_mul,eval_sub,eval_X,eval_C] at hz
        rcases mul_eq_zero.mp hz with hz | hz
        · simpa [sub_eq_zero.mp hz] using hrin
        · exact hBr hBn z hz
    · let b : Polynomial ℂ := C 1-C (star r)*X
      have hb0 : b≠0 := by
        intro h
        have he := congrArg (fun P : Polynomial ℂ => P.eval 0) h
        simp [b] at he
      have hbd : b.natDegree≤1 := by
        apply le_trans (natDegree_sub_le _ _)
        simp only [natDegree_C,max_le_iff,zero_le,true_and]
        exact (natDegree_mul_le).trans (by simp)
      have hprod : b*B≠0 := mul_ne_zero hb0 hBn
      refine ⟨b*B,(natDegree_mul_le).trans (by omega),iff_of_false hprod ha0,?_,?_⟩
      · intro z hz
        simp only [eval_mul,norm_mul]
        rw [hBc z hz,hAg,eval_mul,norm_mul]
        congr 1
        simpa [b] using laurent_reflected_factor_circle_norm r z hz
      · intro _ z hz
        rw [eval_mul] at hz
        rcases mul_eq_zero.mp hz with hz | hz
        · have he : star r*z=1 := by
            have hh : 1-star r*z=0 := by simpa [b] using hz
            linear_combination -hh
          have hn : ‖r‖*‖z‖=1 := by simpa [norm_mul] using congrArg norm he
          have hrout : 1<‖r‖ := lt_of_not_ge hrin
          nlinarith [norm_nonneg z]
        · exact hBr hBn z hz

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
