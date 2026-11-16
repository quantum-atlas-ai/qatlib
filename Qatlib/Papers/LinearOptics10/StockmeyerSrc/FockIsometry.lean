/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockGamma
public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockAction
public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockPermanent

@[expose] public section


/-! # Genuine unitary invariance of the actual coefficient action

The positive factorial-root coefficient change identifies the real
polynomial substitution with the proved gamma(U transpose) sector matrix.
The source unitary matrix predicate supplies gamma's actual isometry;
neither an invariant pairing nor a Gaussian source bridge is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Matrix ComplexConjugate
open ComplexConjugate MvPolynomial
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockIsometry
open Qatlib.Papers.LinearOptics10.StockmeyerSrc
open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib.Concepts.BosonFock.BosonOperators
open FockModel

/-- Actual coefficient polynomials preserve addition in every finite particle sector. -/
theorem polyAdd {m n : ℕ} (a b : FockCoeff m n) :
    polyOfCoeff (a+b) = polyOfCoeff a + polyOfCoeff b := by
  simp only [polyOfCoeff, Pi.add_apply, map_add, Finset.sum_add_distrib]

/-- The actual polynomial coefficient action preserves addition. -/
theorem phiAdd {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ) (a b : FockCoeff m n) :
    phi U (a+b) = phi U a + phi U b := by
  ext S
  simp only [phi, coeffVec, substPoly, polyAdd, map_add, Pi.add_apply]
  exact (coeffAddMonoidHom _).map_add _ _

/-- The genuine coefficient substitution is an actual complex-linear map. -/
def phiLinear {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ) : FockCoeff m n →ₗ[ℂ] FockCoeff m n where
  toFun := phi U
  map_add' := phiAdd U
  map_smul' := FockNormalize.phiScale U

/-- Every coefficient action is the finite sum of its actual monomial basis actions. -/
theorem phiExpand {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ) (a : FockCoeff m n)
    (S : FockOccupation m n) : phi U a S = ∑ T, a T * phi U (basisCoeff T) S := by
  have hb (T : FockOccupation m n) : (Pi.single T (1 : ℂ) : FockCoeff m n) = basisCoeff T := by
    funext R
    by_cases h : R = T
    · subst R
      simp [basisCoeff]
    · simp [basisCoeff, h]
  have he := WeightedPair.expand (phiLinear (n := n) U) a S
  change phi U a S = ∑ T, a T * phi U (Pi.single T 1) S at he
  simpa only [hb] using he

/-- Positive factorial-root scaling gives the actual normalized coefficient coordinates. -/
def normalCoeff {m n : ℕ} (a : FockCoeff m n) : FockCoeff m n :=
  fun S => (Real.sqrt (occFactorial S : ℝ) : ℂ) * a S

/-- The genuine weighted Fock pairing is the ordinary pairing of normalized coordinates. -/
theorem normalPair {m n : ℕ} (a b : FockCoeff m n) :
    fockInner a b = dotProduct (star (normalCoeff a)) (normalCoeff b) := by
  change (∑ S, conj (a S)*b S*(occFactorial S : ℂ)) =
    ∑ S, conj ((Real.sqrt (occFactorial S : ℝ) : ℂ)*a S) *
      ((Real.sqrt (occFactorial S : ℝ) : ℂ)*b S)
  apply Finset.sum_congr rfl
  intro S _
  have hs2 : (Real.sqrt (occFactorial S : ℝ) : ℂ)^2 = (occFactorial S : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (occFactorial S) : (0 : ℝ) ≤ occFactorial S)
  simp only [map_mul, Complex.conj_ofReal]
  rw [← hs2]
  ring

/-- Each actual monomial coefficient has the proved gamma entry with its exact factorial factors. -/
theorem coeffGamma {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (S T : FockOccupation m n) :
    (Real.sqrt (occFactorial S : ℝ) : ℂ) * phi U (basisCoeff T) S =
      gamma m n Uᵀ S T * (Real.sqrt (occFactorial T : ℝ) : ℂ) := by
  have hs : (Real.sqrt (occFactorial S : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast FockNormalize.rootNonzero S
  have hs2 : (Real.sqrt (occFactorial S : ℝ) : ℂ)^2 = (occFactorial S : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (occFactorial S) : (0 : ℝ) ≤ occFactorial S)
  have he := FockNormalize.amplitudeNorm U S T
  rw [FockGamma.basisRead, FockGamma.amplitudeGamma, Complex.ofReal_mul] at he
  apply mul_right_cancel₀ hs
  calc
    _ = phi U (basisCoeff T) S * (occFactorial S : ℂ) := by rw [← hs2]; ring
    _ = _ := he
    _ = _ := by ring

/-- The full actual polynomial action transports to the transposed-mode gamma matrix. -/
theorem normalAction {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ) (a : FockCoeff m n) :
    normalCoeff (phi U a) = (gamma m n Uᵀ) *ᵥ normalCoeff a := by
  funext S
  change (Real.sqrt (occFactorial S : ℝ) : ℂ) * phi U a S =
    ∑ T, gamma m n Uᵀ S T * ((Real.sqrt (occFactorial T : ℝ) : ℂ)*a T)
  rw [phiExpand, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  calc
    _ = a T * ((Real.sqrt (occFactorial S : ℝ) : ℂ)*phi U (basisCoeff T) S) := by ring
    _ = a T * (gamma m n Uᵀ S T * (Real.sqrt (occFactorial T : ℝ) : ℂ)) := by
      rw [coeffGamma]
    _ = _ := by ring

/-- A genuine finite matrix left-isometry preserves the ordinary complex vector pairing. -/
theorem matrixPair {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (hA : Aᴴ*A = 1) (c d : I → ℂ) :
    dotProduct (star (A *ᵥ c)) (A *ᵥ d) = dotProduct (star c) d := by
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    hA, Matrix.vecMul_one]

/-- The entire original unitary pairing-invariance goal holds for the actual phi(U). -/
theorem unitaryPair {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) (a b : FockCoeff m n) :
    fockInner (phi U a) (phi U b) = fockInner a b := by
  have hUT : Uᵀ ∈ Matrix.unitaryGroup (Fin m) ℂ := Matrix.transpose_mem_unitaryGroup_iff.mpr hU
  have hg : (gamma m n Uᵀ)ᴴ * gamma m n Uᵀ = 1 :=
    (second_quantization_permanent_bridge.1 m n ⟨Uᵀ,hUT⟩ ⟨Uᵀ,hUT⟩).1
  simp only [normalPair, normalAction]
  exact matrixPair (gamma m n Uᵀ) hg _ _

/-- Both original Corollary20 conjuncts hold, with no isometry conclusion supplied as a premise. -/
theorem unitaryAction {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    (∀ a b : FockCoeff m n, fockInner (phi U a) (phi U b) = fockInner a b) ∧
      Function.Bijective (phi (m := m) (n := n) U) :=
  ⟨unitaryPair U hU, FockAction.phiBijective U hU⟩

/-- Actual unitary substitution preserves the exact unit norm of the initial photon occupation. -/
theorem initialNorm {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) (h : n ≤ m) :
    fockNormSq (phi U (oneMonomialCoeff h)) = 1 := by
  rw [normEqReInner, unitaryPair U hU]
  change (fockInner (basisCoeff (oneOccupation m n h)) (basisCoeff (oneOccupation m n h))).re = 1
  rw [FockNormalize.basisNorm, FockPermanent.oneFactorial]
  simp

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockIsometry
