/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCayleyTransport
import Mathlib.Algebra.Polynomial.Reverse
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Polynomial Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open scoped Classical BigOperators ComplexOrder

private def circleStarReverse (P : Polynomial ℂ) (d : ℕ) : Polynomial ℂ :=
  (conjugatePolynomial P).reflect d

private theorem conjugatePolynomial_eval_complex (P : Polynomial ℂ) (z : ℂ) :
    (conjugatePolynomial P).eval z=star (P.eval (star z)) := by
  simpa [conjugatePolynomial] using! Polynomial.eval_map_apply (p := P) (starRingEnd ℂ) (star z)

private theorem circleStarReverse_ne_zero (P : Polynomial ℂ) (d : ℕ) (hP : P≠0) :
    circleStarReverse P d≠0 := by
  intro h
  have hc := Polynomial.reflect_eq_zero_iff.mp h
  have he := congrArg conjugatePolynomial hc
  apply hP
  simpa only [conjugatePolynomial_conjugate,conjugatePolynomial_zero] using! he

private theorem circleStarReverse_mul (P Q : Polynomial ℂ) (d e : ℕ)
    (hP : P.natDegree≤d) (hQ : Q.natDegree≤e) :
    circleStarReverse (P*Q) (d+e)=circleStarReverse P d*circleStarReverse Q e := by
  unfold circleStarReverse
  rw [conjugatePolynomial_mul]
  exact Polynomial.reflect_mul _ _ (Polynomial.natDegree_map_le.trans hP)
    (Polynomial.natDegree_map_le.trans hQ)

private theorem circleStarReverse_eval (P : Polynomial ℂ) (d : ℕ) (hP : P.natDegree≤d)
    (z : ℂ) (hz : z≠0) :
    (circleStarReverse P d).eval z=z^d*star (P.eval (star (z⁻¹))) := by
  letI : Invertible (z⁻¹) := invertibleOfNonzero (inv_ne_zero hz)
  have he := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) (z⁻¹) d
    (conjugatePolynomial P) (Polynomial.natDegree_map_le.trans hP)
  simp only [invOf_eq_inv,inv_inv,Polynomial.eval₂_id] at he
  rw [conjugatePolynomial_eval_complex] at he
  have hp : z^d≠0 := pow_ne_zero _ hz
  have hh := congrArg (fun w : ℂ => w*z^d) he
  simp only [inv_pow,mul_assoc,inv_mul_cancel₀ hp,mul_one] at hh
  exact hh.trans (mul_comm _ _)

private theorem circleStarReverse_eval_zero_iff (P : Polynomial ℂ) (d : ℕ)
    (hP : P.natDegree≤d) (z : ℂ) (hz : z≠0) :
    (circleStarReverse P d).eval z=0 ↔ P.eval (star (z⁻¹))=0 := by
  rw [circleStarReverse_eval P d hP z hz]
  simp only [mul_eq_zero,pow_ne_zero _ hz,false_or,star_eq_zero]

private theorem circleStarReverse_circle_eval (P : Polynomial ℂ) (d : ℕ)
    (hP : P.natDegree≤d) (z : ℂ) (hz : ‖z‖=1) :
    (circleStarReverse P d).eval z=z^d*star (P.eval z) := by
  have hn : z≠0 := by intro h; simp [h] at hz
  rw [circleStarReverse_eval P d hP z hn,Complex.inv_eq_conj hz]
  change z^d*star (P.eval (star (star z)))=z^d*star (P.eval z)
  rw [star_star]

private theorem circleProduct_eval (P : Polynomial ℂ) (d : ℕ)
    (hP : P.natDegree≤d) (z : ℂ) (hz : ‖z‖=1) :
    (P*circleStarReverse P d).eval z=z^d*((‖P.eval z‖^2 : ℝ) : ℂ) := by
  rw [eval_mul,circleStarReverse_circle_eval P d hP z hz]
  calc
    _ = z^d*(P.eval z*star (P.eval z)) := by ring
    _ = _ := by rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]

private theorem circleProducts_eq (P Q : Polynomial ℂ) (d : ℕ)
    (hP : P.natDegree≤d) (hQ : Q.natDegree≤d)
    (h : ∀ z : ℂ, ‖z‖=1 → ‖P.eval z‖=‖Q.eval z‖) :
    P*circleStarReverse P d=Q*circleStarReverse Q d := by
  apply polynomial_eq_of_unit_circle_eval_eq
  intro z hz
  rw [circleProduct_eval P d hP z hz,circleProduct_eval Q d hQ z hz,h z hz]

private theorem closed_disk_associated : ∀ n : ℕ, ∀ P Q : Polynomial ℂ,
    P.natDegree=n → Q.natDegree=n → P.eval 0≠0 → Q.eval 0≠0 →
    P*circleStarReverse P n=Q*circleStarReverse Q n →
    (∀ z : ℂ, P.eval z=0 → ‖z‖≤1) →
    (∀ z : ℂ, Q.eval z=0 → ‖z‖≤1) →
    ∃ u : ℂ, u≠0 ∧ Q=C u*P := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P Q hPd hQd hPc hQc he hPr hQr
    have hP0 : P≠0 := by intro h; apply hPc; simp [h]
    have hQ0 : Q≠0 := by intro h; apply hQc; simp [h]
    by_cases hn : n=0
    · rw [hn] at hPd hQd
      obtain ⟨a,rfl⟩ := Polynomial.natDegree_eq_zero.mp hPd
      obtain ⟨b,rfl⟩ := Polynomial.natDegree_eq_zero.mp hQd
      have ha : a≠0 := by simpa using! hPc
      have hb : b≠0 := by simpa using! hQc
      refine ⟨b/a,div_ne_zero hb ha,?_⟩
      rw [← C_mul,div_mul_cancel₀ b ha]
    obtain ⟨r,hr⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ P
      (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp (by omega)))
    have hrP : P.IsRoot r := by simpa [Polynomial.IsRoot,Polynomial.aeval_def] using! hr
    have hr0 : r≠0 := by
      intro h
      subst r
      exact hPc hrP
    have hrQ : Q.IsRoot r := by
      have hc := congrArg (fun A : Polynomial ℂ => A.eval r) he
      (try dsimp only at hc)
      rw [eval_mul,eval_mul,hrP,zero_mul] at hc
      rcases mul_eq_zero.mp hc.symm with h | h
      · exact h
      · have hroot := (circleStarReverse_eval_zero_iff Q n hQd.le r hr0).mp h
        have hnorm := hQr _ hroot
        rw [norm_star,norm_inv] at hnorm
        have hp : 0<‖r‖ := norm_pos_iff.mpr hr0
        have hge : 1≤‖r‖ := by
          calc
            1 = ‖r‖⁻¹*‖r‖ := (inv_mul_cancel₀ (ne_of_gt hp)).symm
            _ ≤ 1*‖r‖ := mul_le_mul_of_nonneg_right hnorm hp.le
            _ = _ := one_mul _
        have hunit : ‖r‖=1 := le_antisymm (hPr r hrP) hge
        have hinv : star (r⁻¹)=r := by
          rw [Complex.inv_eq_conj hunit]
          change star (star r)=r
          exact star_star r
        simpa only [hinv] using! hroot
    obtain ⟨P₁,hP⟩ := Polynomial.dvd_iff_isRoot.mpr hrP
    obtain ⟨Q₁,hQ⟩ := Polynomial.dvd_iff_isRoot.mpr hrQ
    have hP₁0 : P₁≠0 := by intro h; simp [h] at hP; exact hP0 hP
    have hQ₁0 : Q₁≠0 := by intro h; simp [h] at hQ; exact hQ0 hQ
    have hP₁c : P₁.eval 0≠0 := by
      intro h
      have hc := congrArg (fun A : Polynomial ℂ => A.eval 0) hP
      (try dsimp only at hc)
      rw [eval_mul,h,mul_zero] at hc
      exact hPc hc
    have hQ₁c : Q₁.eval 0≠0 := by
      intro h
      have hc := congrArg (fun A : Polynomial ℂ => A.eval 0) hQ
      (try dsimp only at hc)
      rw [eval_mul,h,mul_zero] at hc
      exact hQc hc
    have hdegP : P.natDegree=1+P₁.natDegree := by
      rw [hP,natDegree_mul (X_sub_C_ne_zero r) hP₁0,natDegree_X_sub_C]
    have hdegQ : Q.natDegree=1+Q₁.natDegree := by
      rw [hQ,natDegree_mul (X_sub_C_ne_zero r) hQ₁0,natDegree_X_sub_C]
    have hm : n=1+P₁.natDegree := by omega
    have hsmall : P₁*circleStarReverse P₁ P₁.natDegree=Q₁*circleStarReverse Q₁ P₁.natDegree := by
      rw [hP,hQ,hm,circleStarReverse_mul (X-C r) P₁ 1 P₁.natDegree (by simp) (le_refl _),
        circleStarReverse_mul (X-C r) Q₁ 1 P₁.natDegree (by simp) (by omega)] at he
      apply mul_left_cancel₀ (mul_ne_zero (X_sub_C_ne_zero r)
        (circleStarReverse_ne_zero (X-C r) 1 (X_sub_C_ne_zero r)))
      calc
        _ = ((X-C r)*P₁)*(circleStarReverse (X-C r) 1*circleStarReverse P₁ P₁.natDegree) := by ring
        _ = _ := he
        _ = _ := by ring
    have hP₁r (z : ℂ) (hz : P₁.eval z=0) : ‖z‖≤1 := hPr z (by simp [hP,hz])
    have hQ₁r (z : ℂ) (hz : Q₁.eval z=0) : ‖z‖≤1 := hQr z (by simp [hQ,hz])
    obtain ⟨u,hu,hrel⟩ := ih P₁.natDegree (by omega) P₁ Q₁ rfl (by omega)
      hP₁c hQ₁c hsmall hP₁r hQ₁r
    refine ⟨u,hu,?_⟩
    rw [hP,hQ,hrel]
    ring

theorem closed_disk_polynomial_phase_unique (P Q : Polynomial ℂ)
    (hD : Q.natDegree=P.natDegree) (hPc : P.eval 0≠0) (hQc : Q.eval 0≠0)
    (hPr : ∀ z : ℂ, P.eval z=0 → ‖z‖≤1) (hQr : ∀ z : ℂ, Q.eval z=0 → ‖z‖≤1)
    (hcircle : ∀ z : ℂ, ‖z‖=1 → ‖P.eval z‖=‖Q.eval z‖) :
    ∃ u : ℂ, ‖u‖=1 ∧ Q=C u*P := by
  have hprod := circleProducts_eq P Q P.natDegree (le_refl _) hD.le hcircle
  obtain ⟨u,_,hu⟩ := closed_disk_associated P.natDegree P Q rfl hD hPc hQc hprod hPr hQr
  have hP0 : P≠0 := by intro h; apply hPc; simp [h]
  obtain ⟨z,hz,hzn⟩ := exists_unit_circle_eval_ne_zero P hP0
  have he := hcircle z hz
  rw [hu,eval_mul,eval_C,norm_mul] at he
  refine ⟨u,?_,hu⟩
  apply mul_right_cancel₀ (norm_ne_zero_iff.mpr hzn)
  simpa only [one_mul] using! he.symm

theorem gramOuter_highest_trace (n : ℕ) [NeZero n] (p : Fin n → ℂ) :
    genTrace (gramOuter p) ((n-1 : ℕ) : ℤ)=
      star (p 0)*p ⟨n-1,by have := NeZero.pos n; omega⟩ := by
  let top : Fin n := ⟨n-1,by have := NeZero.pos n; omega⟩
  unfold genTrace
  rw [Finset.sum_eq_single (0 : Fin n)]
  · rw [Finset.sum_eq_single top]
    · simp [top,gramOuter]
    · intro j _ hj
      have hv : j.val≠n-1 := by intro h; apply hj; exact Fin.ext h
      simp [hv]
    · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    have hiv : i.val≠0 := by intro h; apply hi; exact Fin.ext (by simpa using! h)
    have he : (j.val : ℤ)-(i.val : ℤ)≠((n-1 : ℕ) : ℤ) := by
      have := i.isLt
      have := j.isLt
      omega
    simp [he]
  · simp

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
