/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.BosonFock.BosonOperators.BosonPermanent
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section


/-! # The actual fixed-particle coefficient polynomial

Demand: LinearOptics10 Theorem 19. Distinct finite occupations have distinct
exponents, so the actual monomial sum preserves every coefficient. This is
a mathematical polynomial map, independent of complexity-class predicates.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open MvPolynomial

namespace Qatlib.Concepts.BosonFock.BosonOperators.CoeffPoly
open Qatlib.Concepts.BosonFock.BosonOperators

/-- The finitely supported monomial exponent of an actual occupation. -/
def exponent {m n : ℕ} (S : FockOccupation m n) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (S.1 i : ℕ))

/-- Every monomial exponent is exactly its corresponding occupation count. -/
@[simp] theorem exponentApply {m n : ℕ} (S : FockOccupation m n) (i : Fin m) :
    exponent S i = (S.1 i : ℕ) := rfl

/-- Different occupations cannot give the same monomial exponent. -/
theorem exponentInj {m n : ℕ} : Function.Injective (exponent (m := m) (n := n)) := by
  intro S T h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrArg (fun d : Fin m →₀ ℕ => d i) h

/-- The actual degree-n polynomial with the specified occupation coefficients. -/
def poly {m n : ℕ} (a : FockOccupation m n → ℂ) : MvPolynomial (Fin m) ℂ :=
  ∑ S, monomial (exponent S) (a S)

/-- Reading a coefficient of the actual polynomial returns the original amplitude. -/
@[simp] theorem coeffRead {m n : ℕ} (a : FockOccupation m n → ℂ)
    (S : FockOccupation m n) : (poly a).coeff (exponent S) = a S := by
  simp [poly, coeff_monomial, exponentInj.eq_iff]

/-- The coefficient-to-polynomial map is injective in every finite particle sector. -/
theorem polyInjective {m n : ℕ} : Function.Injective (poly (m := m) (n := n)) := by
  intro a b h
  funext S
  simpa using congrArg (fun p : MvPolynomial (Fin m) ℂ => p.coeff (exponent S)) h

/-- A finite exponent degree is the sum of all its mode entries. -/
theorem degreeSum {m : ℕ} (d : Fin m →₀ ℕ) : d.degree = ∑ i, d i := by
  rw [Finsupp.degree_apply]
  exact Finset.sum_subset (Finset.subset_univ _) (by
    intro i _ hi
    simpa only [Finsupp.mem_support_iff, not_not] using hi)

/-- An occupation monomial has exactly its fixed total particle degree. -/
theorem exponentDegree {m n : ℕ} (S : FockOccupation m n) : (exponent S).degree = n := by
  rw [degreeSum]
  exact S.property

/-- The actual coefficient polynomial is homogeneous of the sector's degree. -/
theorem homogeneous {m n : ℕ} (a : FockOccupation m n → ℂ) :
    (poly a).IsHomogeneous n := by
  exact IsHomogeneous.sum Finset.univ _ n (fun S _ => isHomogeneous_monomial _ (exponentDegree S))

/-- Every nonnegative exponent of the fixed total degree is a valid finite occupation. -/
def ofExponent {m n : ℕ} (d : Fin m →₀ ℕ) (hd : d.degree = n) : FockOccupation m n :=
  ⟨fun i => ⟨d i, Nat.lt_succ_of_le (by
    rw [← hd, degreeSum]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i))⟩,
    by simpa only using (degreeSum d).symm.trans hd⟩

/-- Reconstructing an occupation keeps its entire actual exponent. -/
theorem exponentOf {m n : ℕ} (d : Fin m →₀ ℕ) (hd : d.degree = n) :
    exponent (ofExponent d hd) = d := by ext i; rfl

/-- Reading all occupation coefficients reconstructs every actual homogeneous polynomial. -/
theorem reconstruct {m n : ℕ} (p : MvPolynomial (Fin m) ℂ) (hp : p.IsHomogeneous n) :
    poly (fun S : FockOccupation m n => p.coeff (exponent S)) = p := by
  ext d
  by_cases hd : d.degree = n
  · have hs := exponentOf d hd
    rw [← hs]
    exact coeffRead _ _
  · have hne : ∀ S : FockOccupation m n, exponent S ≠ d := by
      intro S heq
      exact hd (heq ▸ exponentDegree S)
    have hz : (poly (fun S : FockOccupation m n => p.coeff (exponent S))).coeff d = 0 := by
      simp [poly, coeff_monomial, hne]
    exact hz.trans (hp.coeff_eq_zero hd).symm

/-- Actual linear mode substitution preserves the polynomial's fixed particle degree. -/
theorem substDegree {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (a : FockOccupation m n → ℂ) :
    (aeval (fun i => ∑ j, C (U i j) * X j) (poly a)).IsHomogeneous n := by
  have hlin (i : Fin m) : (∑ j, C (U i j) * X j).IsHomogeneous 1 :=
    IsHomogeneous.sum Finset.univ _ 1 (fun j _ => isHomogeneous_C_mul_X _ _)
  simpa only [one_mul] using (homogeneous a).aeval _ hlin

end Qatlib.Concepts.BosonFock.BosonOperators.CoeffPoly
