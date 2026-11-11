/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeStandardPhaseWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! Exact-unit Gaussian output from approximate rational phase coordinates.
Only output rounding is certified here, not a numerical phase algorithm or its
bit-time. The computed nativePhasePair uses integer square roots and Cayley data. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords

open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QspSimulation.Achievability

/-- Normalizing an approximate nonzero phase pays at most twice its original
error. The rho<1 hypothesis rules out the arbitrary zero-pair fallback. -/
theorem nativePhaseTarget_error_of_unit (x y : ℚ) (z : ℂ) (ρ : ℝ)
    (hz : ‖z‖=1) (hρ : ρ<1)
    (he : ‖gaussianRatComplex (x,y)-z‖≤ρ) :
    ‖nativePhaseTarget x y-z‖≤2*ρ := by
  have hnz : ¬(x=0 ∧ y=0) := by
    intro h
    rcases h with ⟨rfl,rfl⟩
    simp only [gaussianRatComplex,Rat.cast_zero,zero_mul,zero_add,zero_sub,norm_neg,hz] at he
    linarith
  let v := gaussianRatComplex (x,y)
  have hv : v≠0 := by
    intro h
    have h1 : ‖v-z‖=1 := by rw [h,zero_sub,norm_neg,hz]
    change ‖v-z‖≤ρ at he
    rw [h1] at he
    linarith
  have hv0 : 0<‖v‖ := norm_pos_iff.mpr hv
  have hn : |1-‖v‖|≤ρ := by
    have h := abs_norm_sub_norm_le v z
    rw [hz,abs_sub_comm] at h
    exact h.trans he
  have hd : v/(‖v‖ : ℂ)-v=((1-‖v‖ : ℝ) : ℂ)*v/(‖v‖ : ℂ) := by
    have hn0 : (‖v‖ : ℂ)≠0 := by exact_mod_cast ne_of_gt hv0
    push_cast
    field_simp
  have hnorm : ‖v/(‖v‖ : ℂ)-v‖=|1-‖v‖| := by
    rw [hd,norm_div,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hv0]
    exact mul_div_cancel_right₀ _ (ne_of_gt hv0)
  rw [nativePhaseTarget,ite_eq_right hnz]
  change ‖v/(‖v‖ : ℂ)-z‖≤2*ρ
  calc
    _≤‖v/(‖v‖ : ℂ)-v‖+‖v-z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤ρ+ρ := add_le_add (hnorm.le.trans hn) he
    _=2*ρ := by ring

/-- The actual finite rational rounding output is unit modulus with an explicit
distance to the external ideal unit phase; no free normalization error field. -/
theorem nativePhasePair_error_of_unit (x y : ℚ) (p : ℕ) (z : ℂ) (ρ : ℝ)
    (hz : ‖z‖=1) (hρ : ρ<1)
    (he : ‖gaussianRatComplex (x,y)-z‖≤ρ) :
    ‖gaussianRatComplex (nativePhasePair x y p)‖=1 ∧
    ‖gaussianRatComplex (nativePhasePair x y p)-z‖≤2*ρ+1/(16*(2 : ℝ)^p) := by
  refine ⟨nativePhasePair_norm x y p,?_⟩
  calc
    _≤‖gaussianRatComplex (nativePhasePair x y p)-nativePhaseTarget x y‖+
        ‖nativePhaseTarget x y-z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤1/(16*(2 : ℝ)^p)+2*ρ := add_le_add (nativePhasePair_error x y p)
      (nativePhaseTarget_error_of_unit x y z ρ hz hρ he)
    _=2*ρ+1/(16*(2 : ℝ)^p) := by ring

/-- The final output error is total even for coarse approximations: rho>=1 is
paid by the distance<=2 between unit phases. Only the normalization argument
above needs rho<1, not the actual rounding error conclusion. -/
theorem nativePhasePair_error_of_unit_total (x y : ℚ) (p : ℕ) (z : ℂ) (ρ : ℝ)
    (hz : ‖z‖=1) (he : ‖gaussianRatComplex (x,y)-z‖≤ρ) :
    ‖gaussianRatComplex (nativePhasePair x y p)‖=1 ∧
    ‖gaussianRatComplex (nativePhasePair x y p)-z‖≤2*ρ+1/(16*(2 : ℝ)^p) := by
  by_cases hρ : ρ<1
  · exact nativePhasePair_error_of_unit x y p z ρ hz hρ he
  · refine ⟨nativePhasePair_norm x y p,?_⟩
    have hn := norm_sub_le (gaussianRatComplex (nativePhasePair x y p)) z
    rw [nativePhasePair_norm,hz] at hn
    have hd : 0≤1/(16*(2 : ℝ)^p) := by positivity
    linarith [le_of_not_gt hρ]

/-- Both the base and every phase are actually rounded; length is unchanged. -/
def nativeRoundStandardPacket (data : PhaseData) (p : ℕ) : PhaseData where
  base := nativePhasePair data.base.1 data.base.2 p
  phases := data.phases.map (fun z => nativePhasePair z.1 z.2 p)

/-- The finite construction in `NativePhaseOutputRounding` satisfies `nativeRoundStandardPacket_spec` under the displayed hypotheses. -/
theorem nativeRoundStandardPacket_spec (data : PhaseData) (p : ℕ) :
    (nativeRoundStandardPacket data p).phases.length=data.phases.length ∧
    ‖gaussianRatComplex (nativeRoundStandardPacket data p).base‖=1 ∧
    ∀ z∈(nativeRoundStandardPacket data p).phases,‖gaussianRatComplex z‖=1 := by
  refine ⟨by simp [nativeRoundStandardPacket],nativePhasePair_norm _ _ _,?_⟩
  intro z hz
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
  exact nativePhasePair_norm _ _ _

/-- Actual rounded/converted word: units and legality are generated rather
than assumed. This is not its uniform approximation guarantee. -/
theorem native_rounded_standard_word_legal {H : Type} [Fintype H] [DecidableEq H]
    (P Q : Matrix H H ℂ) (data : PhaseData) (p : ℕ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q) :
    WellFormedAdjointCircuit (nativeStandardPhaseWord P Q (nativeRoundStandardPacket data p)) ∧
    adjointQueryCount (nativeStandardPhaseWord P Q (nativeRoundStandardPacket data p))=
      data.phases.length ∧
    adjointGateCount (nativeStandardPhaseWord P Q (nativeRoundStandardPacket data p))=
      data.phases.length+1 := by
  have hs := nativeRoundStandardPacket_spec data p
  refine ⟨native_standard_phase_word_wellFormed P Q _ hP hQ hs.2.1 hs.2.2,?_⟩
  simpa only [hs.1] using native_standard_phase_word_counts P Q (nativeRoundStandardPacket data p)

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
