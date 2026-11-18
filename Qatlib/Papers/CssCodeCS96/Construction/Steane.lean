/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ErrorCorrection.CssBuild.Constructions
public import Qatlib.Concepts.ErrorCorrection.Recovery.Certified
public import Qatlib.Concepts.ErrorCorrection.ErrorClasses.Quotient
public import Qatlib.Concepts.CodingDecoding.CssRecovery.CodingDecoding
import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# A seven-qubit consumer of the common CSS interfaces

The canonical Steane matrix is the fixed public provider's column convention.
The exact-distance argument feeds finite certificates into the generic logical
distance API. The existing concrete decoder feeds the shared recovery contract.
The finite checks do not assume a precomputed value of code distance or rank.
-/

namespace Qatlib.Papers.CssCodeCS96.Construction

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssRecovery
open Qatlib.Concepts.ErrorCorrection.CssBuild
open Qatlib.Concepts.ErrorCorrection.LogicalOps
open Qatlib.Concepts.ErrorCorrection.Recovery
open Qatlib.Concepts.ErrorCorrection.ErrorClasses
open scoped Matrix

/-- The public Steane instance is a consumer of the chain-compatible CSS constructor. -/
theorem steane_chain : ofComplex steaneH steaneHᵀ steaneH_mul_transpose = steaneData := rfl

set_option maxRecDepth 4096 in
/-- The seven distinct nonzero syndrome columns exclude nonzero kernel vectors below weight three. -/
theorem small_kernel : ∀ v : Fin 7 → ZMod 2,
    bitWeight v < 3 → steaneH *ᵥ v = 0 → v = 0 := by decide

/-- A weight-three undetectable binary label in the provider's coordinate convention. -/
def logicalWord : Fin 7 → ZMod 2 := ![1, 1, 0, 1, 0, 0, 0]

/-- The upper witness is undetectable by the Steane parity-check matrix. -/
theorem word_syndrome : steaneH *ᵥ logicalWord = 0 := by decide

/-- The upper witness has exactly three nonzero coordinates. -/
theorem word_weight : bitWeight logicalWord = 3 := by decide

/-- None of the eight stabilizer row combinations is the logical upper witness. -/
theorem rows_exclude : ∀ u : Fin 3 → ZMod 2, steaneHᵀ *ᵥ u ≠ logicalWord := by decide

/-- The witness is a nontrivial logical Pauli label, not merely a nonzero kernel vector. -/
theorem word_nontrivial : ¬ IsStabilizerLabel steaneData (logicalWord, 0) := by
  intro h
  obtain ⟨u, hu⟩ := h.1
  exact rows_exclude u hu

/-- Every undetectable Pauli label below weight three is a stabilizer. -/
theorem steane_lower (e : PauliLabel (Fin 7))
    (hs : pauliSyndrome steaneData e = (0, 0))
    (hw : (pauliWeight e.1 e.2 : ℕ∞) < 3) : IsStabilizerLabel steaneData e := by
  have hnat : pauliWeight e.1 e.2 < 3 := by exact_mod_cast hw
  have hx : e.1 = 0 := small_kernel e.1
    (lt_of_le_of_lt (bitWeight_le_pauliWeight_left _ _) hnat) (congrArg Prod.snd hs)
  have hz : e.2 = 0 := small_kernel e.2
    (lt_of_le_of_lt (bitWeight_le_pauliWeight_right _ _) hnat) (congrArg Prod.fst hs)
  change e.1 ∈ LinearMap.range (Matrix.mulVecLin steaneHᵀ) ∧
    e.2 ∈ LinearMap.range (Matrix.mulVecLin steaneHᵀ)
  rw [hx, hz]
  exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩

/-- The canonical seven-qubit CSS code has exact logical distance three. -/
theorem steane_distance : cssDistance steaneData = 3 := by
  apply distance_eq steaneData 3 (logicalWord, 0) steane_lower
  · exact Prod.ext (by simp [pauliSyndrome, steaneData]) word_syndrome
  · exact word_nontrivial
  · simpa only [pauliWeight_zero_right] using word_weight

/-- The shared construction has the exact seven-qubit parameters, including logical distance. -/
theorem steane_params : steaneData.numQubits = 7 ∧
    steaneData.encodedQubits = 1 ∧ cssDistance steaneData = 3 := by
  exact ⟨by simp [CssData.numQubits], steaneData_encodedQubits, steane_distance⟩

/-- The public single-error decoder satisfies the shared bounded-output contract. -/
theorem steane_cert : DecoderCert steaneDecoder 1 := by
  constructor
  · intro e he
    change pauliSyndrome steaneData (steaneCorr (pauliSyndrome steaneData e)) = _
    rw [steaneDecoder_corrects_weight_one e he]
  · intro e he
    change pauliWeight (steaneCorr (pauliSyndrome steaneData e)).1
      (steaneCorr (pauliSyndrome steaneData e)).2 ≤ _
    rw [steaneDecoder_corrects_weight_one e he]

/-- The common recovery theorem restores every Steane code-state density after any single-qubit Pauli error. -/
theorem steane_recovers (e : PauliLabel (Fin 7)) (he : pauliWeight e.1 e.2 ≤ 1)
    (ψ : (Fin 7 → ZMod 2) → ℂ) (hψ : ψ ∈ cssCodespace steaneData) :
    recoveryChannel steaneData steaneDecoder
      (densityOf ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ ψ)) = densityOf ψ := by
  apply cert_density steaneData steaneDecoder 1 steane_cert _ e he ψ hψ
  rw [steane_distance]
  norm_num

/-- The same exact-distance result transports through the shared X/Z duality constructor. -/
theorem steane_dual : cssDistance (dual steaneData) = 3 := by
  rw [dual_distance, steane_distance]

/-- Zero syndrome alone does not put the logical witness in the zero error class. -/
theorem word_diff_class : ¬ ErrorEquiv steaneData (logicalWord, 0) (0, 0) := by
  intro h
  change (logicalWord - 0, (0 : Fin 7 → ZMod 2) - 0) ∈ stabilizerSpace steaneData at h
  apply word_nontrivial
  apply (mem_space steaneData (logicalWord, 0)).mp
  simpa only [sub_zero] using h

/-- A nonzero stabilizer example obtained from an actual parity-check row combination. -/
def stabilizerWord : Fin 7 → ZMod 2 :=
  steaneHᵀ *ᵥ (Pi.single (0 : Fin 3) (1 : ZMod 2))

/-- The stabilizer example is nonzero and has weight four. -/
theorem stab_weight : bitWeight stabilizerWord = 4 := by decide

/-- The nonzero stabilizer example belongs to the zero error class. -/
theorem stab_same_class : ErrorEquiv steaneData (stabilizerWord, 0) (0, 0) := by
  change (stabilizerWord - 0, (0 : Fin 7 → ZMod 2) - 0) ∈ stabilizerSpace steaneData
  simp only [sub_zero]
  constructor
  · exact ⟨Pi.single (0 : Fin 3) (1 : ZMod 2), rfl⟩
  · exact Submodule.zero_mem _

/-- Two Steane blocks use the common direct-sum syndrome decomposition. -/
theorem two_syndromes (e f : PauliLabel (Fin 7)) :
    pauliSyndrome (directSum steaneData steaneData)
      (Sum.elim e.1 f.1, Sum.elim e.2 f.2) =
      (Sum.elim (pauliSyndrome steaneData e).1 (pauliSyndrome steaneData f).1,
       Sum.elim (pauliSyndrome steaneData e).2 (pauliSyndrome steaneData f).2) :=
  sum_syndrome steaneData steaneData e f

end Qatlib.Papers.CssCodeCS96.Construction
