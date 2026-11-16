/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.BosonFock.BosonOperators.RowFibers
public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockNormalize

@[expose] public section


/-! # General actual occupation coefficients and normalized Fock amplitudes

The repeated-mode list has its genuine occupation multiplicities. Expanding
the actual product of substituted linear forms then reads precisely the
historical finite assignment sum, with every repeated photon retained.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockExpansion
open Qatlib.Papers.LinearOptics10.StockmeyerSrc
open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib.Concepts.BosonFock.BosonOperators.RowFibers
open FockModel

/-- Actual photon positions realize each prescribed mode multiplicity exactly. -/
theorem pickCount {m n : ℕ} (T : FockOccupation m n) (i : Fin m) :
    (Finset.univ.filter (fun k : Fin n => occPick T k = i)).card = (T.val i).val := by
  calc
    _ = ∑ k : Fin n, if occPick T k = i then (1 : ℕ) else 0 := by
      simp only [Finset.sum_boole, Nat.cast_id]
    _ = ∑ k : Fin (occRows T).length, if (occRows T).get k = i then (1 : ℕ) else 0 :=
      Fintype.sum_equiv (finCongr (occRows_length T).symm) _ _ (fun _ => rfl)
    _ = (occRows T).count i := sumGetCount _ i
    _ = _ := rowCount _ i

/-- The sum of the actual photon-position exponents is the entire occupation exponent. -/
theorem exponentRows {m n : ℕ} (T : FockOccupation m n) :
    (∑ k : Fin n, Finsupp.single (occPick T k) 1) = occFinsupp T := by
  ext i
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, occApply]
  simpa only [Finset.sum_boole, Nat.cast_id] using pickCount T i

/-- The actual coefficient polynomial of a monomial basis vector is its specified monomial. -/
theorem polyBasis {m n : ℕ} (T : FockOccupation m n) :
    polyOfCoeff (basisCoeff T) = monomial (occFinsupp T) (1 : ℂ) := by
  simp [polyOfCoeff, basisCoeff, apply_ite]

/-- Splitting the occupation monomial into its actual repeated photon positions is exact. -/
theorem monomialRows {m n : ℕ} (T : FockOccupation m n) :
    monomial (occFinsupp T) (1 : ℂ) = ∏ k : Fin n, X (occPick T k) := by
  rw [← exponentRows T, monomial_sum_one]
  rfl

/-- Substitution of the actual occupation monomial is the genuine product of row linear forms. -/
theorem substituted {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ) (T : FockOccupation m n) :
    substPoly U (polyOfCoeff (basisCoeff T)) =
      ∏ k : Fin n, ∑ j : Fin m, C (U (occPick T k) j) * X j := by
  rw [polyBasis, monomialRows]
  simp only [substPoly, map_prod, aeval_X]

/-- Equality with an occupation exponent is exactly equality of every assignment fiber count. -/
theorem exponentEq {m n : ℕ} (f : Fin n → Fin m) (S : FockOccupation m n) :
    (∑ k : Fin n, Finsupp.single (f k) 1) = occFinsupp S ↔
      ∀ i : Fin m, (Finset.univ.filter (fun k : Fin n => f k = i)).card = (S.val i).val := by
  rw [Finsupp.ext_iff]
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, occApply, Finset.sum_boole, Nat.cast_id]

/-- Coefficients of the genuine row-linear-form product are the entire actual assignment sum. -/
theorem productCoeff {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (T S : FockOccupation m n) :
    (∏ k : Fin n, ∑ j : Fin m, C (U (occPick T k) j) * X j).coeff (occFinsupp S) =
      polyActGenCoeff U T S := by
  have hx (k : Fin n) (j : Fin m) : C (U (occPick T k) j) * X j =
      monomial (Finsupp.single j 1) (U (occPick T k) j) := by
    rw [X, C_mul_monomial]
    simp
  simp_rw [hx]
  rw [Fintype.prod_sum]
  simp_rw [← monomial_sum_prod]
  rw [coeff_sum]
  unfold polyActGenCoeff
  apply Finset.sum_congr rfl
  intro f _
  simp only [coeff_monomial, exponentEq]

/-- The complete actual assignment vector is the true polynomial coefficient action. -/
theorem assignmentPhi {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (T S : FockOccupation m n) :
    polyActGenCoeff U T S = phi U (basisCoeff T) S := by
  change _ = (substPoly U (polyOfCoeff (basisCoeff T))).coeff (occFinsupp S)
  rw [substituted]
  exact (productCoeff U T S).symm

/-- The entire original amplitude-normalization target follows from the actual coefficient bridge. -/
theorem innerAmplitude {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (S T : FockOccupation m n) :
    fockInner (basisCoeff S) (polyActGenCoeff U T) =
      ((Real.sqrt (occFactorial S : ℝ) * Real.sqrt (occFactorial T : ℝ) : ℝ) : ℂ) *
        fockAmplitude U S T := by
  have hv : polyActGenCoeff U T = phi U (basisCoeff T) := funext (assignmentPhi U T)
  rw [hv]
  exact FockNormalize.amplitudeNorm U S T

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockExpansion
