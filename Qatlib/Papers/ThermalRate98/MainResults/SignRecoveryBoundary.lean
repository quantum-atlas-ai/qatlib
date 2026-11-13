/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.BellReferenceProtocol
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Limits of three-setting sign recovery

This module constructs two real normalized Bell states differing in their relative sign and
prepares each by an explicit unitary circuit. Their Born distributions agree for the three
settings `sourceSignWord`: no gate, a Hadamard on the first qubit, or a Hadamard on the second
qubit, exposing a limitation of these settings for the sign reconstruction discussion in
[LidarWang1999].

The circuit `diagnosticWord`, which applies a Hadamard to both qubits, distinguishes the two
states by the equal-bit event. `source_sign_recovery_not_universal` formalizes the impossibility
of recovering their sign from the three specified distributions alone.

## Main statements

* `sourceSign_outcomes_equal`: proves equality of all outcome probabilities for the three
  settings.
* `diagnostic_distinguishes`: gives equal-bit probabilities one and zero after the diagnostic
  circuit.
* `source_sign_recovery_not_universal`: rules out a Boolean decoder distinguishing the two
  identical data sets.

## References

* [Lidar and Wang, 1999][LidarWang1999]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ThermalRate98.MainResults.SourceSigns
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators

/-- The two-qubit gate applying Hadamard to the first qubit and identity to the second. -/
def firstH : Matrix (Bool×Bool) (Bool×Bool) ℂ := TensorGate Hadamard 1

/-- The two-qubit gate applying identity to the first qubit and Hadamard to the second. -/
def secondH : Matrix (Bool×Bool) (Bool×Bool) ℂ := TensorGate 1 Hadamard

/-- The two-qubit gate applying Pauli Z to the first qubit and identity to the second. -/
def firstZ : Matrix (Bool×Bool) (Bool×Bool) ℂ := TensorGate PauliZ 1

/-- The positive Bell resource state when `negative` is false, and its image under `firstZ` when
`negative` is true. -/
def signBell (negative : Bool) : QState (Bool×Bool) :=
  if negative then ApplyGate firstZ teleportBellResource else teleportBellResource

/-- The circuit applying a first-qubit Hadamard and CNOT, followed by a first-qubit Pauli Z
exactly when `negative` is true. -/
def signPreparation (negative : Bool) : Circuit (Bool×Bool) :=
  [Step.gate firstH,Step.gate CNOT] ++ if negative then [Step.gate firstZ] else []

/-- Applying `firstZ` multiplies each amplitude by minus one exactly when its first bit is true. -/
theorem firstZ_amplitude (psi : QState (Bool×Bool)) (b c : Bool) :
    ApplyGate firstZ psi (b,c) = (if b then (-1 : ℂ) else 1)*psi (b,c) := by
  cases b <;> cases c <;>
    simp [firstZ,ApplyGate,Matrix.mulVec,dotProduct,TensorGate,Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type,PauliZ,Matrix.diagonal_apply,Matrix.one_apply]

/-- Applying `firstH` combines the two amplitudes sharing the second bit using the appropriate
row of the Hadamard matrix. -/
theorem firstH_amplitude (psi : QState (Bool×Bool)) (b c : Bool) :
    ApplyGate firstH psi (b,c) = Hadamard b false*psi (false,c)+Hadamard b true*psi (true,c) := by
  cases c <;>
    simp [firstH,ApplyGate,Matrix.mulVec,dotProduct,TensorGate,Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type,Matrix.one_apply] <;> ring

/-- Applying `secondH` combines the two amplitudes sharing the first bit using the appropriate
row of the Hadamard matrix. -/
theorem secondH_amplitude (psi : QState (Bool×Bool)) (b c : Bool) :
    ApplyGate secondH psi (b,c) = Hadamard c false*psi (b,false)+Hadamard c true*psi (b,true) := by
  cases b <;>
    simp [secondH,ApplyGate,Matrix.mulVec,dotProduct,TensorGate,Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type,Matrix.one_apply] <;> ring

/-- The signed Bell state has equal-bit amplitudes of magnitude `1 / √2`, with the true-true
amplitude negated exactly when `negative` is true. -/
theorem signBell_amplitude (negative b c : Bool) :
    signBell negative (b,c) =
      if b = c then (if negative && b then -((Real.sqrt 2 : ℂ)⁻¹) else (Real.sqrt 2 : ℂ)⁻¹) else 0 := by
  cases negative with
  | false => simp [signBell,teleportBellResource_apply']
  | true =>
    rw [signBell,if_pos rfl,firstZ_amplitude,teleportBellResource_apply']
    cases b <;> cases c <;> simp

/-- Both choices of relative sign give normalized Bell states. -/
theorem signBell_normalized (negative : Bool) : Normalized (signBell negative) := by
  cases negative with
  | false => exact teleportBellResource_normalized
  | true =>
    exact normalized_applyGate
      (tensorGate_unitary pauliZ_unitary (Matrix.unitaryGroup Bool ℂ).one_mem)
      teleportBellResource_normalized

/-- Every amplitude of either signed Bell state has zero imaginary part. -/
theorem signBell_real (negative : Bool) (p : Bool×Bool) : (signBell negative p).im = 0 := by
  rcases p with ⟨b,c⟩
  rw [signBell_amplitude]
  cases negative <;> cases b <;> cases c <;> simp

/-- Running the sign preparation circuit on the false-false basis ket produces the selected
signed Bell state. See [LidarWang1999]. -/
theorem signPreparation_run (negative : Bool) :
    Run 1 (signPreparation negative) (Ket (false,false)) = signBell negative := by
  have hp : ApplyGate firstH (Ket (false,false)) = TensorState Plus (Ket false) := by
    rw [← tensorState_ket_ket false false,firstH,applyGate_tensorGate,
      applyGate_hadamard_ket_false]
    simp only [ApplyGate,Matrix.one_mulVec]
  cases negative <;> simp [signPreparation,Run,hp,signBell,teleportBellResource]

/-- The two signed Bell states have the same Born probability at every computational basis
outcome. -/
theorem signBell_born_equal (p : Bool×Bool) :
    BornProb (signBell false) p = BornProb (signBell true) p := by
  rcases p with ⟨b,c⟩
  simp only [BornProb,signBell_amplitude]
  cases b <;> cases c <;> simp

/-- After a Hadamard on the first qubit, either signed Bell state assigns probability `1 / 4` to
every outcome. -/
theorem firstH_born (negative : Bool) (p : Bool×Bool) :
    BornProb (ApplyGate firstH (signBell negative)) p = (1 : ℝ)/4 := by
  rcases p with ⟨b,c⟩
  rw [BornProb,firstH_amplitude]
  cases negative <;> cases b <;> cases c <;>
    norm_num [signBell_amplitude,Hadamard,sqrt2_inv_sq]

/-- After a Hadamard on the second qubit, either signed Bell state assigns probability `1 / 4`
to every outcome. -/
theorem secondH_born (negative : Bool) (p : Bool×Bool) :
    BornProb (ApplyGate secondH (signBell negative)) p = (1 : ℝ)/4 := by
  rcases p with ⟨b,c⟩
  rw [BornProb,secondH_amplitude]
  cases negative <;> cases b <;> cases c <;>
    norm_num [signBell_amplitude,Hadamard,sqrt2_inv_sq]

/-- The three measurement preprocessing circuits: identity, first-qubit Hadamard, and
second-qubit Hadamard, indexed by `Fin 3`. -/
def sourceSignWord (s : Fin 3) : Circuit (Bool×Bool) :=
  if s.val = 0 then [] else if s.val = 1 then [Step.gate firstH] else [Step.gate secondH]

/-- Each of the three specified preprocessing settings gives identical Born probabilities for
the two signed Bell states. -/
theorem sourceSign_outcomes_equal (s : Fin 3) (p : Bool×Bool) :
    BornProb (Run 1 (sourceSignWord s) (signBell false)) p =
      BornProb (Run 1 (sourceSignWord s) (signBell true)) p := by
  fin_cases s
  · exact signBell_born_equal p
  · exact (firstH_born false p).trans (firstH_born true p).symm
  · exact (secondH_born false p).trans (secondH_born true p).symm

/-- Each of the three specified preprocessing settings gives equal probabilities for every
finite event on the two signed Bell states. -/
theorem sourceSign_events_equal (s : Fin 3) (S : Finset (Bool×Bool)) :
    MeasureProb (Run 1 (sourceSignWord s) (signBell false)) S =
      MeasureProb (Run 1 (sourceSignWord s) (signBell true)) S := by
  unfold MeasureProb
  exact Finset.sum_congr rfl (fun p _ => sourceSign_outcomes_equal s p)

/-- The diagnostic circuit applying a Hadamard to the first qubit and then to the second. -/
def diagnosticWord : Circuit (Bool×Bool) := [Step.gate firstH,Step.gate secondH]

/-- The diagnostic circuit gives amplitude `1 / √2` exactly when the first bit equals the second
bit XOR the sign flag, and zero otherwise. -/
theorem diagnostic_amplitude (negative b c : Bool) :
    Run 1 diagnosticWord (signBell negative) (b,c) =
      if b = (c ^^ negative) then (Real.sqrt 2 : ℂ)⁻¹ else 0 := by
  change ApplyGate secondH (ApplyGate firstH (signBell negative)) (b,c) = _
  rw [secondH_amplitude,firstH_amplitude,firstH_amplitude]
  cases negative <;> cases b <;> cases c <;>
    norm_num [signBell_amplitude,Hadamard,sqrt2_inv_sq] <;> ring

/-- The diagnostic circuit fixes the positive Bell state. -/
theorem diagnostic_plus : Run 1 diagnosticWord (signBell false) = signBell false := by
  ext ⟨b,c⟩
  rw [diagnostic_amplitude,signBell_amplitude]
  cases b <;> cases c <;> simp

/-- The positive Bell state assigns probability one to the event that the two bits are equal. -/
theorem signBell_plus_diagonal :
    MeasureProb (signBell false) (Finset.univ.filter (fun p : Bool×Bool => p.1 = p.2)) = 1 := by
  calc
    _ = MeasureProb (signBell false) Finset.univ := by
      unfold MeasureProb
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro p _ hp
      have hne : p.1 ≠ p.2 := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hp
      rcases p with ⟨b,c⟩
      simp only [BornProb,signBell_amplitude,hne,if_false,norm_zero,zero_pow (by decide : 2 ≠ 0)]
    _ = 1 := signBell_normalized false

/-- After the diagnostic circuit, the equal-bit event has probability one for the positive Bell
state and zero for the negative Bell state. See [LidarWang1999]. -/
theorem diagnostic_distinguishes :
    MeasureProb (Run 1 diagnosticWord (signBell false))
      (Finset.univ.filter (fun p : Bool×Bool => p.1 = p.2)) = 1 ∧
    MeasureProb (Run 1 diagnosticWord (signBell true))
      (Finset.univ.filter (fun p : Bool×Bool => p.1 = p.2)) = 0 := by
  constructor
  · rw [diagnostic_plus]
    exact signBell_plus_diagonal
  · unfold MeasureProb
    apply Finset.sum_eq_zero
    intro p hp
    have he : p.1 = p.2 := (Finset.mem_filter.mp hp).2
    rcases p with ⟨b,c⟩
    unfold BornProb
    rw [diagnostic_amplitude]
    cases b <;> cases c <;> simp_all

/-- The sign preparation circuit is unitary for either sign flag. -/
theorem signPreparation_unitary (negative : Bool) : IsUnitaryCircuit (signPreparation negative) := by
  have hH : firstH ∈ Matrix.unitaryGroup (Bool×Bool) ℂ :=
    tensorGate_unitary hadamard_unitary (Matrix.unitaryGroup Bool ℂ).one_mem
  have hZ : firstZ ∈ Matrix.unitaryGroup (Bool×Bool) ℂ :=
    tensorGate_unitary pauliZ_unitary (Matrix.unitaryGroup Bool ℂ).one_mem
  cases negative <;> simp [signPreparation,hH,hZ,cnot_unitary]

/-- The sign preparation circuit has zero oracle queries and two gates, plus one additional gate
when `negative` is true. -/
theorem signPreparation_resources (negative : Bool) :
    QueryCount (signPreparation negative) = 0 ∧
      GateCount (signPreparation negative) = 2+(if negative then 1 else 0) := by
  cases negative <;> constructor <;> rfl

/-- Each specified sign measurement circuit and the diagnostic circuit are unitary. -/
theorem signMeasurements_unitary (s : Fin 3) :
    IsUnitaryCircuit (sourceSignWord s) ∧ IsUnitaryCircuit diagnosticWord := by
  have hH : firstH ∈ Matrix.unitaryGroup (Bool×Bool) ℂ :=
    tensorGate_unitary hadamard_unitary (Matrix.unitaryGroup Bool ℂ).one_mem
  have hH' : secondH ∈ Matrix.unitaryGroup (Bool×Bool) ℂ :=
    tensorGate_unitary (Matrix.unitaryGroup Bool ℂ).one_mem hadamard_unitary
  constructor
  · fin_cases s <;> simp [sourceSignWord,hH,hH']
  · simp [diagnosticWord,hH,hH']

/-- The outcome probability data from the three specified preprocessing settings after preparing
the Bell state selected by the sign flag. -/
def sourceSignData (negative : Bool) : Fin 3 → Bool×Bool → ℝ :=
  fun s p => BornProb (Run 1 (sourceSignWord s) (Run 1 (signPreparation negative) (Ket (false,false)))) p

/-- The complete three-setting probability data are identical for the two sign flags. -/
theorem sourceSignData_equal : sourceSignData false = sourceSignData true := by
  funext s p
  unfold sourceSignData
  rw [signPreparation_run,signPreparation_run]
  exact sourceSign_outcomes_equal s p

/-- No Boolean-valued function of the specified three-setting probability data can return the
correct sign flag for both of these Bell states. See [LidarWang1999]. -/
theorem source_sign_recovery_not_universal :
    ¬ ∃ recover : (Fin 3 → Bool×Bool → ℝ) → Bool,
      recover (sourceSignData false) = false ∧ recover (sourceSignData true) = true := by
  rintro ⟨recover,hplus,hminus⟩
  rw [sourceSignData_equal] at hplus
  exact Bool.false_ne_true (hplus.symm.trans hminus)

end Qatlib.Papers.ThermalRate98.MainResults.SourceSigns
