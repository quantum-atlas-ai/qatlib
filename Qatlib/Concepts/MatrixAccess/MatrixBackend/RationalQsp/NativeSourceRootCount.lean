/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceCompletionAccuracy
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceReciprocal
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Actual original-input H: reciprocal roots, multiplicity and source guards.
This does not certify the full proposer, interpreter, spectral deflation or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


open Polynomial

/-- The finite construction in `NativeSourceRootCount` satisfies `reverse_linear` under the displayed hypotheses. -/
private theorem reverse_linear (a : ℂ) (ha : a≠0) :
    (X-C a : ℂ[X]).reverse=C (-a)*(X-C (a⁻¹)) := by
  have he : (X-C a : ℂ[X]).reverse=1-C a*X := by
    rw [Polynomial.reverse,Polynomial.natDegree_X_sub_C,
      Polynomial.reflect_sub,← pow_one (X : ℂ[X]),Polynomial.reflect_monomial,Polynomial.reflect_C]
    simp [Polynomial.revAt]
  rw [he,mul_sub,← Polynomial.C_mul]
  simp only [neg_mul,mul_inv_cancel₀ ha,Polynomial.C_neg,Polynomial.C_1]
  ring

/-- The finite construction in `NativeSourceRootCount` satisfies `reverse_root_product` under the displayed hypotheses. -/
private theorem reverse_root_product (l : Multiset ℂ) :
    (∀ a∈l,a≠0) →
      ((l.map (fun a => (X-C a : ℂ[X]))).prod.reverse).roots=l.map (fun a => a⁻¹) := by
  induction l using Multiset.induction_on with
  | empty =>
    intro _
    simp [Polynomial.reverse]
  | @cons a l ih =>
    intro h
    have ha := h a (by simp)
    have hl : ∀ x∈l,x≠0 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have hleft : (X-C a : ℂ[X]).reverse≠0 := by
      simpa only [ne_eq,Polynomial.reverse_eq_zero] using (Polynomial.X_sub_C_ne_zero a)
    have hright : ((l.map (fun x => (X-C x : ℂ[X]))).prod.reverse)≠0 := by
      simpa only [ne_eq,Polynomial.reverse_eq_zero] using
        (Polynomial.monic_multisetProd_X_sub_C l).ne_zero
    rw [Multiset.map_cons,Multiset.prod_cons,Polynomial.reverse_mul_of_domain,
      Polynomial.roots_mul (mul_ne_zero hleft hright),reverse_linear a ha,
      Polynomial.roots_C_mul _ (neg_ne_zero.mpr ha),Polynomial.roots_X_sub_C,ih hl,
      Multiset.map_cons]
    rfl

/-- The finite construction in `NativeSourceRootCount` satisfies `roots_reverse` under the displayed hypotheses. -/
private theorem roots_reverse (p : ℂ[X]) (hp : p≠0) (h0 : p.eval 0≠0) :
    p.reverse.roots=p.roots.map (fun a => a⁻¹) := by
  have hn : ∀ a∈p.roots,a≠0 := by
    intro a ha hzero
    subst a
    exact h0 (Polynomial.isRoot_of_mem_roots ha)
  have he := congrArg Polynomial.reverse
    (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
      (IsAlgClosed.card_roots_eq_natDegree (p := p)))
  rw [Polynomial.reverse_mul_of_domain,Polynomial.reverse_C] at he
  calc
    _ = (C p.leadingCoeff*(p.roots.map (fun a => (X-C a : ℂ[X]))).prod.reverse).roots :=
      congrArg Polynomial.roots he.symm
    _ = _ := by
      rw [Polynomial.roots_C_mul _ (Polynomial.leadingCoeff_ne_zero.mpr hp)]
      exact reverse_root_product p.roots hn

/-- The same emitted instruction list satisfies `inverse_pair_inside_count` with the displayed gate and query accounting. -/
private theorem inverse_pair_inside_count (l : Multiset ℂ)
    (hinverse : l.map (fun z => z⁻¹)=l)
    (hnonzero : ∀ z∈l,z≠0) (hnounit : ∀ z∈l,‖z‖≠1) :
    2*(l.filter (fun z => ‖z‖<1)).card=l.card := by
  classical
  have hswap : (l.filter (fun z => ‖z‖<1)).card=
      (l.filter (fun z => 1<‖z‖)).card := by
    calc
      _ = ((l.map (fun z => z⁻¹)).filter (fun z => ‖z‖<1)).card := by rw [hinverse]
      _ = (l.filter (fun z => ‖z⁻¹‖<1)).card := by
        rw [Multiset.filter_map,Multiset.card_map]
        rfl
      _ = _ := by
        congr 1
        apply Multiset.filter_congr
        intro z hz
        rw [norm_inv]
        exact inv_lt_one₀ (norm_pos_iff.mpr (hnonzero z hz))
  have houtside : l.filter (fun z => ¬‖z‖<1)=l.filter (fun z => 1<‖z‖) := by
    apply Multiset.filter_congr
    intro z hz
    have hne := hnounit z hz
    exact not_lt.trans (le_iff_lt_or_eq.trans (or_iff_left (Ne.symm hne)))
  have he := congrArg Multiset.card (Multiset.filter_add_not (fun z : ℂ => ‖z‖<1) l)
  rw [Multiset.card_add,houtside,← hswap] at he
  omega

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Polynomial

/-- The finite construction in `NativeSourceRootCount` satisfies `sourceLeading_ne_zero` under the displayed hypotheses. -/
private theorem sourceLeading_ne_zero (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hd : 0<sourceDegree cs N E) :
    sourceCoefficient cs N E ⟨sourceDegree cs N E,by have h := sourceDegree_le cs N E; omega⟩≠0 := by
  obtain ⟨i,hi,hv⟩ := sourceArrayDegree_leading (sourceCoefficient cs N E) hd
  have he : i=⟨sourceDegree cs N E,by have h := sourceDegree_le cs N E; omega⟩ := by
    apply Fin.ext
    exact hv.symm
  rw [he] at hi
  exact hi

/-- The finite construction in `NativeSourceRootCount` satisfies `sourceInputP_coeff_zero` under the displayed hypotheses. -/
private theorem sourceInputP_coeff_zero (cs : List ℚ) (N : ℕ) (E : ℚ) :
    (sourceInputP cs N E).coeff 0=
      sourceCoefficient cs N E ⟨sourceDegree cs N E,by have h := sourceDegree_le cs N E; omega⟩ := by
  unfold sourceInputP
  rw [Polynomial.ofFn_coeff_eq_val_of_lt _ (Nat.succ_pos _)]
  unfold sourceP sourceLiftedArray
  congr 1
  apply Fin.ext
  change Nat.dist 0 (sourceDegree cs N E)=sourceDegree cs N E
  simp [Nat.dist]

/-- The finite construction in `NativeSourceRootCount` satisfies `sourceF_eval_zero_ne` under the displayed hypotheses. -/
theorem sourceF_eval_zero_ne (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hd : 0<sourceDegree cs N E) : (sourceF cs N E).eval 0≠0 := by
  have hlead : (sourceCoefficient cs N E
      ⟨sourceDegree cs N E,by have h := sourceDegree_le cs N E; omega⟩ : ℂ)≠0 := by
    exact_mod_cast sourceLeading_ne_zero cs N E hd
  simp only [sourceF,Polynomial.eval_map,Polynomial.eval₂_sub,Polynomial.eval₂_pow,
    Polynomial.eval₂_X,zero_pow (Nat.ne_of_gt hd),zero_sub,Polynomial.eval₂_at_zero,
    sourceInputP_coeff_zero]
  exact neg_ne_zero.mpr (pow_ne_zero 2 hlead)

/-- The finite construction in `NativeSourceRootCount` satisfies `sourceF_natDegree_eq` under the displayed hypotheses. -/
theorem sourceF_natDegree_eq (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hd : 0<sourceDegree cs N E) :
    (sourceF cs N E).natDegree=2*sourceDegree cs N E := by
  have h0 : (sourceF cs N E).coeff 0≠0 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using sourceF_eval_zero_ne cs N E hd
  have hc := congrArg (fun p : ℂ[X] => p.coeff 0) (sourceF_reflect cs N E)
  rw [Polynomial.coeff_reflect,Polynomial.revAt_zero] at hc
  have htop : (sourceF cs N E).coeff (2*sourceDegree cs N E)≠0 := by rw [hc]; exact h0
  exact le_antisymm (sourceF_natDegree_le cs N E) (Polynomial.le_natDegree_of_ne_zero htop)

/-- The finite construction in `NativeSourceRootCount` satisfies `sourceF_reverse` under the displayed hypotheses. -/
theorem sourceF_reverse (cs : List ℚ) (N : ℕ) (E : ℚ) (hd : 0<sourceDegree cs N E) :
    (sourceF cs N E).reverse=sourceF cs N E := by
  unfold Polynomial.reverse
  rw [sourceF_natDegree_eq cs N E hd,sourceF_reflect]

/-- The finite construction in `NativeSourceRootCount` satisfies `sourceF_inverse_roots` under the displayed hypotheses. -/
theorem sourceF_inverse_roots (cs : List ℚ) (N : ℕ) (E : ℚ) (hd : 0<sourceDegree cs N E) :
    (sourceF cs N E).roots.map (fun z => z⁻¹)=(sourceF cs N E).roots := by
  have hp : sourceF cs N E≠0 := by
    intro he
    have hz := sourceF_eval_zero_ne cs N E hd
    rw [he,Polynomial.eval_zero] at hz
    exact hz rfl
  have h := roots_reverse (sourceF cs N E) hp (sourceF_eval_zero_ne cs N E hd)
  rw [sourceF_reverse cs N E hd] at h
  exact h.symm

/-- The finite construction in `NativeSourceRootCount` satisfies `sourceF_no_unit_zero` under the displayed hypotheses. -/
theorem sourceF_no_unit_zero (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (z : ℂ) (hz : (sourceF cs N E).eval z=0) : ‖z‖≠1 := by
  intro hunit
  have hb := (sourceF_circle_bounds cs N E hE htail hparity hd hnorm z hunit).1
  rw [hz,norm_zero] at hb
  have hm := sourceMu_pos cs N E hE
  linarith

/-- The finite construction in `NativeSourceRootCount` satisfies `sourceIntegerComplement_roots` under the displayed hypotheses. -/
theorem sourceIntegerComplement_roots (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) :
    (rootIntegerListPolynomial (sourceIntegerComplement cs N E)).roots=(sourceF cs N E).roots := by
  rw [sourceIntegerComplement_polynomial cs N E hparity hd,
    Polynomial.roots_C_mul _ (sourceIntegerComplement_scalar_ne_zero cs N E hparity hd)]
  rfl

/-- The same emitted instruction list satisfies `sourceIntegerComplement_inside_count` with the displayed gate and query accounting. -/
theorem sourceIntegerComplement_inside_count (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1) :
    ((rootIntegerListPolynomial (sourceIntegerComplement cs N E)).roots.filter
      (fun z => ‖z‖<1)).card=sourceDegree cs N E := by
  rw [sourceIntegerComplement_roots cs N E hparity hd]
  have hn : ∀ z∈(sourceF cs N E).roots,z≠0 := by
    intro z hz hzero
    subst z
    exact sourceF_eval_zero_ne cs N E hd (Polynomial.isRoot_of_mem_roots hz)
  have hunit : ∀ z∈(sourceF cs N E).roots,‖z‖≠1 := by
    intro z hz
    exact sourceF_no_unit_zero cs N E hE htail hparity hd hnorm z
      (Polynomial.isRoot_of_mem_roots hz)
  have h := inverse_pair_inside_count (sourceF cs N E).roots
    (sourceF_inverse_roots cs N E hd) hn hunit
  rw [IsAlgClosed.card_roots_eq_natDegree,sourceF_natDegree_eq cs N E hd] at h
  omega

/-- The finite construction in `NativeSourceRootCount` satisfies `sourceIntegerComplement_all_roots_gap` under the displayed hypotheses. -/
theorem sourceIntegerComplement_all_roots_gap (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (rho : ℂ) (hroot : (rootIntegerListPolynomial (sourceIntegerComplement cs N E)).eval rho=0) :
    (sourceGamma0 cs N E : ℝ) ≤ |‖rho‖-1| := by
  have hF := (sourceIntegerComplement_eval_zero_iff cs N E hparity hd rho).mp hroot
  have hne := sourceF_no_unit_zero cs N E hE htail hparity hd hnorm rho hF
  rcases lt_or_gt_of_ne hne with hi|ho
  · have hg := sourceIntegerComplement_inside_gap cs N E hE htail hparity hd hnorm rho hi hroot
    rw [abs_of_neg (sub_neg.mpr hi)]
    linarith
  · have hg := sourceIntegerComplement_outside_gap cs N E hE htail hparity hd hnorm rho ho hroot
    rw [abs_of_pos (sub_pos.mpr ho)]
    linarith

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
