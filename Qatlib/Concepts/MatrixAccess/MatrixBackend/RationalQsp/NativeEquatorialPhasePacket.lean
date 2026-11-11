/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeEquatorialHalfPhase
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeStandardPhaseStability
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! Equatorial factors at the SAME signal variable -> a finite standard packet.
No conversion from a half-angle signal oracle is asserted. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords

open Matrix Polynomial
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Matrix.Norms.L2Operator

/-- Construction for equatorial Rotor in the native equatorial phase packet model. -/
def equatorialRotor (q : ℂ) (x s : ℝ) : Matrix Bool Bool ℂ
  | false,false => x
  | true,true => x
  | false,true => Complex.I*(s : ℂ)*q
  | true,false => Complex.I*(s : ℂ)*star q

/-- Construction for equatorial Rotor Product in the native equatorial phase packet model. -/
def equatorialRotorProduct (qs : List ℂ) (x s : ℝ) : Matrix Bool Bool ℂ :=
  (qs.map (fun q => equatorialRotor q x s)).prod

/-- The finite construction in `NativeEquatorialPhasePacket` satisfies `standardPhaseMatrix_mul` under the displayed hypotheses. -/
theorem standardPhaseMatrix_mul (z w : ℂ) :
    standardPhaseMatrix z*standardPhaseMatrix w=standardPhaseMatrix (z*w) := by
  ext i j
  cases i <;> cases j <;> simp [standardPhaseMatrix,Matrix.mul_apply]

/-- Conjugation by a diagonal unit phase squares its off-diagonal coordinate. -/
theorem equatorialRotor_of_phase (u : ℂ) (x s : ℝ) (hu : ‖u‖=1) :
    equatorialRotor (u^2) x s=
      standardPhaseMatrix u*standardSignalMatrix x s*standardPhaseMatrix (star u) := by
  have hunit : u*star u=1 := by
    rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,hu]
    norm_num
  ext i j
  cases i <;> cases j <;>
    simp [equatorialRotor,standardPhaseMatrix,standardSignalMatrix,
      Matrix.mul_apply,pow_two]
  all_goals simp only [Complex.star_def] at hunit ⊢
  all_goals ring_nf at hunit ⊢ <;> linear_combination -(x : ℂ)*hunit

/-- Complex packet boundaries are built from adjacent half phases, preserving
the order E0 E(q1)...E(qn), not reversing the factor list. -/
def nativeEquatorialBoundaryPacket (base : GaussianRat) : List GaussianRat → PhaseData
  | [] => ⟨base,[]⟩
  | u::us =>
    let tail := nativeEquatorialBoundaryPacket (gconj u) us
    ⟨tail.base,gmul base u::tail.phases⟩

/-- The estimate `nativeEquatorialBoundaryPacket_spec` retains the actual parameter, input-error and normalization budgets. -/
theorem nativeEquatorialBoundaryPacket_spec (base : GaussianRat) (us : List GaussianRat)
    (hb : ‖gaussianRatComplex base‖=1) (hu : ∀ u∈us,‖gaussianRatComplex u‖=1) :
    (nativeEquatorialBoundaryPacket base us).phases.length=us.length ∧
    ‖gaussianRatComplex (nativeEquatorialBoundaryPacket base us).base‖=1 ∧
    ∀ z∈(nativeEquatorialBoundaryPacket base us).phases,‖gaussianRatComplex z‖=1 := by
  induction us generalizing base with
  | nil => simp [nativeEquatorialBoundaryPacket,hb]
  | cons u us ih =>
    have hhead := hu u (by simp)
    have ht := ih (gconj u) (by simpa [complex_gconj] using hhead)
      (fun v hv => hu v (by simp [hv]))
    refine ⟨by simpa [nativeEquatorialBoundaryPacket] using congrArg Nat.succ ht.1,
      ht.2.1,?_⟩
    intro z hz
    change z∈gmul base u::(nativeEquatorialBoundaryPacket (gconj u) us).phases at hz
    rcases List.mem_cons.mp hz with h | h
    · subst z
      rw [complex_gmul,norm_mul,hb,hhead,mul_one]
    · exact ht.2.2 z h

/-- The estimate `nativeEquatorialBoundaryPacket_matrix` retains the actual parameter, input-error and normalization budgets. -/
theorem nativeEquatorialBoundaryPacket_matrix (base : GaussianRat) (us : List GaussianRat)
    (x s : ℝ) (hu : ∀ u∈us,‖gaussianRatComplex u‖=1) :
    standardMatrixWord
      (gaussianRatComplex (nativeEquatorialBoundaryPacket base us).base) x s
      ((nativeEquatorialBoundaryPacket base us).phases.map gaussianRatComplex)=
    standardPhaseMatrix (gaussianRatComplex base)*
      equatorialRotorProduct (us.map (fun u => (gaussianRatComplex u)^2)) x s := by
  induction us generalizing base with
  | nil => simp [nativeEquatorialBoundaryPacket,standardMatrixWord,equatorialRotorProduct]
  | cons u us ih =>
    simp only [nativeEquatorialBoundaryPacket,List.map_cons,standardMatrixWord,complex_gmul]
    rw [ih (gconj u) (fun v hv => hu v (by simp [hv]))]
    simp only [equatorialRotorProduct,List.map_cons,List.prod_cons,complex_gconj]
    rw [equatorialRotor_of_phase _ _ _ (hu u (by simp)),←standardPhaseMatrix_mul]
    noncomm_ring

/-- Actual finite construction from unit equatorial coordinates. -/
def nativeEquatorialPacket (base : GaussianRat) (qs : List GaussianRat) (p : ℕ) : PhaseData :=
  nativeEquatorialBoundaryPacket base (qs.map (fun q => nativeEquatorialHalfPhase q p))

/-- The finite construction in `NativeEquatorialPhasePacket` satisfies `nativeEquatorialPacket_spec` under the displayed hypotheses. -/
theorem nativeEquatorialPacket_spec (base : GaussianRat) (qs : List GaussianRat) (p : ℕ)
    (hb : ‖gaussianRatComplex base‖=1) :
    (nativeEquatorialPacket base qs p).phases.length=qs.length ∧
    ‖gaussianRatComplex (nativeEquatorialPacket base qs p).base‖=1 ∧
    ∀ z∈(nativeEquatorialPacket base qs p).phases,‖gaussianRatComplex z‖=1 := by
  have h := nativeEquatorialBoundaryPacket_spec base
    (qs.map (fun q => nativeEquatorialHalfPhase q p)) hb (by
      intro u hu
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hu
      exact nativeEquatorialHalfPhase_norm q p)
  simpa only [nativeEquatorialPacket,List.length_map] using h

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
