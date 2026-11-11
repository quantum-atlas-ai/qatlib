/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootCommonDenominator
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootIntegerList

set_option backward.isDefEq.respectTransparency false

/-! Exact denominator clearing and primitive integer content of arbitrary rational arrays. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput

open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Polynomial

/-- Construction for source Denominator in the native source integerization model. -/
def sourceDenominator (a : List ℚ) : ℕ := a.foldl (fun D q => Nat.lcm D q.den) 1

/-- Construction for source Raw Integers in the native source integerization model. -/
def sourceRawIntegers (a : List ℚ) : List ℤ :=
  a.map (fun q => rootScaledNumerator q (sourceDenominator a))

/-- Construction for source Content in the native source integerization model. -/
def sourceContent (a : List ℚ) : ℕ :=
  (sourceRawIntegers a).foldl (fun g x => Nat.gcd g x.natAbs) 0

/-- Construction for source Integer Target in the native source integerization model. -/
def sourceIntegerTarget (a : List ℚ) : List ℤ :=
  (sourceRawIntegers a).map (fun x => x/(sourceContent a : ℤ))

/-- Construction for source Rational Polynomial in the native source integerization model. -/
def sourceRationalPolynomial (a : List ℚ) : ℂ[X] :=
  (⟨⟨a.toFinsupp⟩⟩ : ℚ[X]).map (Rat.castHom ℂ)

/-- The finite construction in `rational array integerization` satisfies `lcmFold_dvd_seed` under the displayed hypotheses. -/
private theorem lcmFold_dvd_seed (a : List ℚ) (s : ℕ) :
    s ∣ a.foldl (fun D q => Nat.lcm D q.den) s := by
  induction a generalizing s with
  | nil => exact dvd_rfl
  | cons q a ih =>
    rw [List.foldl_cons]
    exact (Nat.dvd_lcm_left s q.den).trans (ih (Nat.lcm s q.den))

/-- The finite construction in `rational array integerization` satisfies `lcmFold_dvd_mem` under the displayed hypotheses. -/
private theorem lcmFold_dvd_mem (a : List ℚ) (s : ℕ) (q : ℚ) (hq : q∈a) :
    q.den ∣ a.foldl (fun D q => Nat.lcm D q.den) s := by
  induction a generalizing s with
  | nil => cases hq
  | cons b a ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hq with he|he
    · subst q
      exact (Nat.dvd_lcm_right s b.den).trans (lcmFold_dvd_seed a (Nat.lcm s b.den))
    · exact ih (Nat.lcm s b.den) he

/-- The finite construction in `rational array integerization` satisfies `lcmFold_pos` under the displayed hypotheses. -/
private theorem lcmFold_pos (a : List ℚ) (s : ℕ) (hs : 0<s) :
    0<a.foldl (fun D q => Nat.lcm D q.den) s := by
  induction a generalizing s with
  | nil => exact hs
  | cons q a ih =>
    rw [List.foldl_cons]
    apply ih
    apply Nat.pos_of_ne_zero
    simp [ne_of_gt hs]

/-- The finite construction in `rational array integerization` satisfies `gcdFold_dvd_seed` under the displayed hypotheses. -/
private theorem gcdFold_dvd_seed (a : List ℤ) (s : ℕ) :
    a.foldl (fun g x => Nat.gcd g x.natAbs) s ∣ s := by
  induction a generalizing s with
  | nil => exact dvd_rfl
  | cons q a ih =>
    rw [List.foldl_cons]
    exact (ih (Nat.gcd s q.natAbs)).trans (Nat.gcd_dvd_left s q.natAbs)

/-- The finite construction in `rational array integerization` satisfies `gcdFold_dvd_mem` under the displayed hypotheses. -/
private theorem gcdFold_dvd_mem (a : List ℤ) (s : ℕ) (x : ℤ) (hx : x∈a) :
    a.foldl (fun g x => Nat.gcd g x.natAbs) s ∣ x.natAbs := by
  induction a generalizing s with
  | nil => cases hx
  | cons b a ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with he|he
    · subst x
      exact (gcdFold_dvd_seed a (Nat.gcd s b.natAbs)).trans (Nat.gcd_dvd_right s b.natAbs)
    · exact ih (Nat.gcd s b.natAbs) he

/-- The finite construction in `rational array integerization` satisfies `sourceDenominator_pos` under the displayed hypotheses. -/
theorem sourceDenominator_pos (a : List ℚ) : 0<sourceDenominator a :=
  lcmFold_pos a 1 (by decide)

/-- The finite construction in `rational array integerization` satisfies `sourceDenominator_dvd` under the displayed hypotheses. -/
theorem sourceDenominator_dvd (a : List ℚ) (q : ℚ) (hq : q∈a) :
    q.den ∣ sourceDenominator a := lcmFold_dvd_mem a 1 q hq

/-- The finite construction in `rational array integerization` satisfies `sourceRawIntegers_exact` under the displayed hypotheses. -/
theorem sourceRawIntegers_exact (a : List ℚ) (q : ℚ) (hq : q∈a) :
    (rootScaledNumerator q (sourceDenominator a) : ℚ)=q*(sourceDenominator a : ℚ) :=
  rootScaledNumerator_exact q _ (sourceDenominator_dvd a q hq)

/-- The finite construction in `rational array integerization` satisfies `sourceContent_dvd` under the displayed hypotheses. -/
theorem sourceContent_dvd (a : List ℚ) (x : ℤ) (hx : x∈sourceRawIntegers a) :
    (sourceContent a : ℤ) ∣ x :=
  Int.natCast_dvd.mpr (gcdFold_dvd_mem (sourceRawIntegers a) 0 x hx)

/-- The finite construction in `rational array integerization` satisfies `sourceContent_pos` under the displayed hypotheses. -/
theorem sourceContent_pos (a : List ℚ) (h : ∃ q∈a,q≠0) : 0<sourceContent a := by
  obtain ⟨q,hq,hnq⟩ := h
  have hD : (sourceDenominator a : ℚ)≠0 := by
    exact_mod_cast (sourceDenominator_pos a).ne'
  have hx : rootScaledNumerator q (sourceDenominator a)≠0 := by
    intro hz
    have he := sourceRawIntegers_exact a q hq
    rw [hz,Int.cast_zero] at he
    exact (mul_ne_zero hnq hD) he.symm
  have hm : rootScaledNumerator q (sourceDenominator a)∈sourceRawIntegers a :=
    List.mem_map.mpr ⟨q,hq,rfl⟩
  have hd := sourceContent_dvd a _ hm
  apply Nat.pos_of_ne_zero
  intro he
  rw [he,Nat.cast_zero] at hd
  exact hx (zero_dvd_iff.mp hd)

/-- The finite construction in `rational array integerization` satisfies `sourceIntegerEntry_exact` under the displayed hypotheses. -/
theorem sourceIntegerEntry_exact (a : List ℚ) (h : ∃ q∈a,q≠0)
    (q : ℚ) (hq : q∈a) :
    ((rootScaledNumerator q (sourceDenominator a)/(sourceContent a : ℤ) : ℤ) : ℚ)=
      q*(sourceDenominator a : ℚ)/(sourceContent a : ℚ) := by
  have hm : rootScaledNumerator q (sourceDenominator a)∈sourceRawIntegers a :=
    List.mem_map.mpr ⟨q,hq,rfl⟩
  have hd := sourceContent_dvd a _ hm
  have hg : (sourceContent a : ℚ)≠0 := by
    exact_mod_cast (sourceContent_pos a h).ne'
  apply (eq_div_iff hg).mpr
  have he := Int.ediv_mul_cancel hd
  have hc : ((rootScaledNumerator q (sourceDenominator a)/(sourceContent a : ℤ) : ℤ) : ℚ)*
      (sourceContent a : ℚ)=(rootScaledNumerator q (sourceDenominator a) : ℚ) := by
    exact_mod_cast he
  exact hc.trans (sourceRawIntegers_exact a q hq)

/-- The finite construction in `rational array integerization` satisfies `sourceRationalPolynomial_coeff` under the displayed hypotheses. -/
theorem sourceRationalPolynomial_coeff (a : List ℚ) (k : ℕ) :
    (sourceRationalPolynomial a).coeff k=(a.getD k 0 : ℂ) := by
  rw [sourceRationalPolynomial,Polynomial.coeff_map]
  change (a.toFinsupp k : ℂ)=(a.getD k 0 : ℂ)
  rw [List.toFinsupp_apply]

/-- Actual nonzero denominator/content scalar; no target identity is supplied. -/
theorem sourceIntegerTarget_polynomial (a : List ℚ) (h : ∃ q∈a,q≠0) :
    rootIntegerListPolynomial (sourceIntegerTarget a)=
      C ((sourceDenominator a : ℂ)/(sourceContent a : ℂ))*sourceRationalPolynomial a := by
  apply Polynomial.ext
  intro k
  rw [rootIntegerListPolynomial_coeff,Polynomial.coeff_C_mul,sourceRationalPolynomial_coeff]
  by_cases hk : k<a.length
  · let q := a.get ⟨k,hk⟩
    have hq : q∈a := List.get_mem _ _
    have he := sourceIntegerEntry_exact a h q hq
    have hc := congrArg (fun t : ℚ => (t : ℂ)) he
    have hi : ((sourceIntegerTarget a).getD k 0 : ℂ)=
        ((rootScaledNumerator q (sourceDenominator a)/(sourceContent a : ℤ) : ℤ) : ℂ) := by
      simp only [sourceIntegerTarget,sourceRawIntegers,List.map_map]
      simp [List.getD_eq_getElem?_getD,hk,q]
    rw [hi]
    have hget : a.getD k 0=q := by simp [List.getD_eq_getElem?_getD,hk,q]
    rw [hget]
    simp only [Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_intCast] at hc
    calc
      _=(q : ℂ)*(sourceDenominator a : ℂ)/(sourceContent a : ℂ) := hc
      _=_ := by ring
  · have hlen : (sourceIntegerTarget a).length=a.length := by
      simp [sourceIntegerTarget,sourceRawIntegers]
    have hk' : (sourceIntegerTarget a).length≤k := by omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none hk',
      List.getElem?_eq_none (Nat.le_of_not_gt hk)]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput
