/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LocalHam06.MainResults.QmaCompletenessOutput
import Qatlib.Papers.LocalHam06.MainResults.QmaCompletenessEncoding
import Qatlib.Papers.LocalHam06.MainResults.QmaCompletenessScaledSize
import Qatlib.Papers.LocalHam06.MainResults.QmaCompletenessHermitian
import Qatlib.Papers.LocalHam06.MainResults.QmaCompletenessFullSpace
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessNativeNorm
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Papers.LocalHam06.MainResults.NativeOutput

namespace Qatlib.Papers.LocalHam06.MainResults
open Qatlib  Qatlib.Concepts.QmaCompleteness.HistoryHam Matrix
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Papers.LocalHam06.MainResults
open Qatlib.Papers.LocalHam06.MainResults
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Papers.LocalHam06.MainResults
open Qatlib.Papers.LocalHam06.MainResults
open scoped Classical BigOperators
set_option autoImplicit false
noncomputable section

def baseTerms (C : QmaHistoryCircuit) : List (IntegerLocalTerm (C.gates.length+C.qubits)) :=
  outputTerms C.qubits (qmaClause2Bits C) C.gates C.initZeroWires C.outputWire

def extraBits (C : QmaHistoryCircuit) : ℕ := scaleBits (nativeJ C)
def denominator (C : QmaHistoryCircuit) : ℕ := scaleDen (nativeJ C)

abbrev normalizedEncoding (C : QmaHistoryCircuit) : LhEncoding :=
  scaledEncoding C.qubits (qmaClause2Bits C) C.gates C.initZeroWires C.outputWire

theorem normalizedEncoding_def (C : QmaHistoryCircuit) :
    normalizedEncoding C = toLhEncoding (qmaClause2Bits C+1+extraBits C) (baseTerms C) := rfl

def scale (C : QmaHistoryCircuit) : ℝ := 1/(denominator C : ℝ)
def yesThreshold (C : QmaHistoryCircuit) : ℝ := yesCut C/(denominator C : ℝ)
def noThreshold (C : QmaHistoryCircuit) : ℝ := noCut C/(denominator C : ℝ)

theorem denominator_pos (C : QmaHistoryCircuit) : 0 < denominator C := by
  have h := (scaleDen_bounds (nativeJ C)).1
  change 32 ≤ denominator C at h
  omega

theorem scale_pos (C : QmaHistoryCircuit) : 0 < scale C := by
  unfold scale
  exact one_div_pos.mpr (by exact_mod_cast denominator_pos C)

theorem scale_eq_inv_power (C : QmaHistoryCircuit) :
    scale C = ((2:ℝ)^extraBits C)⁻¹ := by
  simp [scale, denominator, scaleDen, extraBits, one_div, Nat.cast_pow]

theorem matrixSum_smul {I : Type} [Fintype I] [DecidableEq I]
    (c : ℂ) (xs : List (Matrix I I ℂ)) :
    matrixSum (xs.map (fun M => c • M)) = c • matrixSum xs := by
  induction xs with
  | nil => simp [matrixSum]
  | cons M xs ih =>
      change c • M + matrixSum (xs.map (fun M => c • M)) = c • (M+matrixSum xs)
      rw [ih, smul_add]

theorem normalizedEncoding_semantics (C : QmaHistoryCircuit) :
    lhHamiltonian (normalizedEncoding C) =
      (scale C:ℂ) • Matrix.reindex (flattenEquiv C.gates.length C.qubits).symm
        (flattenEquiv C.gates.length C.qubits).symm (fullHamiltonian C) := by
  change lhHamiltonian (toLhEncoding (qmaClause2Bits C+1+extraBits C) (baseTerms C))=_
  rw [toLhEncoding_semantics (qmaClause2Bits C+1+extraBits C) (baseTerms C)]
  change matrixSum ((baseTerms C).map (value (qmaClause2Bits C+1+extraBits C))) = _
  have hm : (baseTerms C).map (value (qmaClause2Bits C+1+extraBits C)) =
      (baseTerms C).map (fun t => (scale C:ℂ) • value (qmaClause2Bits C+1) t) := by
    apply List.map_congr_left
    intro t _
    rw [scale_eq_inv_power]
    have hv := value_width_shift (qmaClause2Bits C+1) (extraBits C) t
    push_cast at hv ⊢
    exact hv
  rw [hm]
  have hs := matrixSum_smul (scale C:ℂ)
    ((baseTerms C).map (value (qmaClause2Bits C+1)))
  simp only [List.map_map, Function.comp_def] at hs
  rw [hs]
  have he := outputTerms_value_sum C
  change matrixSum ((baseTerms C).map (value (qmaClause2Bits C+1))) = _ at he
  rw [he]

theorem reindex_quadratic {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I≃J) (H : Matrix I I ℂ) (B : ℝ)
    (hQ : ∀ψ : QState I, |energy H ψ| ≤ B*mass ψ) :
    ∀ψ : QState J, |energy (Matrix.reindex e e H) ψ| ≤ B*mass ψ := by
  intro ψ
  let φ : QState I := fun i => ψ (e i)
  have he := energy_reindex e H φ
  have hm := mass_reindex e φ
  have he' : energy (Matrix.reindex e e H) ψ=energy H φ := by
    simpa only [φ, Equiv.apply_symm_apply] using! he
  have hm' : mass φ=mass ψ := by
    simpa only [φ, Equiv.apply_symm_apply] using! hm.symm
  rw [he', ← hm']
  exact hQ φ

theorem real_smul_hermitian {I : Type} [DecidableEq I]
    (r : ℝ) (H : Matrix I I ℂ) (hH : Matrix.IsHermitian H) :
    Matrix.IsHermitian ((r:ℂ) • H) := by
  change (((r:ℂ) • H)ᴴ) = _
  simp only [Matrix.conjTranspose_smul, hH.eq]
  simp

theorem shifted_value_good {m n : ℕ} (w q : ℕ) (t : IntegerLocalTerm (m+n))
    (H : Matrix (Clock m×Reg n) (Clock m×Reg n) ℂ) (B : ℝ)
    (hv : value w t=Matrix.reindex (flattenEquiv m n).symm (flattenEquiv m n).symm H)
    (hh : Matrix.IsHermitian H) (hB : B ≤ (2:ℝ)^q)
    (hQ : ∀ψ : QState (Clock m×Reg n), |energy H ψ| ≤ B*mass ψ) :
    Matrix.IsHermitian (value (w+q) t) ∧
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (value (w+q) t)‖ ≤ 1 := by
  have h0 : Matrix.IsHermitian (value w t) := by rw [hv]; exact hh.reindex _
  have hq0 : ∀ψ : QState (Reg (m+n)), |energy (value w t) ψ| ≤ B*mass ψ := by
    rw [hv]
    exact reindex_quadratic (flattenEquiv m n).symm H B hQ
  rw [value_width_shift]
  have hs := real_smul_hermitian (((2:ℝ)^q)⁻¹) (value w t) h0
  push_cast at hs
  refine ⟨hs,?_⟩
  apply l2norm_le_of_quadratic _ hs 1 (by norm_num)
  intro ψ
  simpa only [one_mul] using! scaled_quadratic_bound (value w t) q B hB hq0 ψ

theorem extraBits_bounds (C : QmaHistoryCircuit) :
    (32:ℝ) ≤ (2:ℝ)^extraBits C ∧ (nativeJ C:ℝ) ≤ (2:ℝ)^extraBits C := by
  have h0 : (32:ℝ) ≤ (scaleDen (nativeJ C):ℝ) := by
    exact_mod_cast (scaleDen_bounds (nativeJ C)).1
  have h1 : (nativeJ C:ℝ) ≤ (scaleDen (nativeJ C):ℝ) := by
    exact_mod_cast (scaleDen_bounds (nativeJ C)).2.1
  simpa only [scaleDen, extraBits, Nat.cast_pow, Nat.cast_ofNat] using! And.intro h0 h1

theorem normalized_terms_good (C : QmaHistoryCircuit) :
    ∀t∈baseTerms C,
      Matrix.IsHermitian (value (qmaClause2Bits C+1+extraBits C) t) ∧
      ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (value (qmaClause2Bits C+1+extraBits C) t)‖ ≤ 1 := by
  intro t ht
  have h32 := (extraBits_bounds C).1
  have hJ := (extraBits_bounds C).2
  have hb : 1 ≤ qmaClause2Bits C := by unfold qmaClause2Bits; omega
  change t∈outputTerms C.qubits (qmaClause2Bits C) C.gates C.initZeroWires C.outputWire at ht
  simp only [outputTerms, List.mem_append, List.mem_map, List.mem_singleton,
    List.mem_flatMap] at ht
  rcases ht with ((⟨i,_,rfl⟩ | ⟨j,_,rfl⟩) | rfl) | ⟨i,_,j,_,rfl⟩
  · let H := physicalPropagation i (qmaRoundedGate C.qubits (qmaClause2Bits C) (C.gates.get i))
    have hv := propagationTerm_value C.qubits (qmaClause2Bits C) i (C.gates.get i)
    have hE : ∀p q, ‖H p q‖ ≤ 1 := by
      apply physicalPropagation_entry_norm
      intro x y
      exact qmaRoundedGate_entry_norm_le_two (C.gates.get i) (qmaClause2Bits C) hb x y
    exact shifted_value_good (qmaClause2Bits C+1) (extraBits C) _ H 32 hv
      (physicalPropagation_hermitian i _) h32
      (fun ψ => local_table_abs (qmaClause2Bits C+1) _ H
        (propagationTerm_local _ _ _ _) hv hE ψ)
  · have hv := boundaryTerm_value C.gates.length C.qubits (qmaClause2Bits C) false j
    simp only [boundaryTarget] at hv
    exact shifted_value_good (qmaClause2Bits C+1) (extraBits C) _ (physicalInput j) 32 hv
      (physicalInput_hermitian j) h32
      (fun ψ => local_table_abs (qmaClause2Bits C+1) _ (physicalInput j)
        ((boundaryTerm_local _ _ _ _ _).trans (by omega)) hv (physicalInput_entry_norm j) ψ)
  · have hv := boundaryTerm_value C.gates.length C.qubits (qmaClause2Bits C) true C.outputWire
    simp only [boundaryTarget, if_true] at hv
    exact shifted_value_good (qmaClause2Bits C+1) (extraBits C) _ (physicalOutput C.outputWire) 32 hv
      (physicalOutput_hermitian C.outputWire) h32
      (fun ψ => local_table_abs (qmaClause2Bits C+1) _ (physicalOutput C.outputWire)
        ((boundaryTerm_local _ _ _ _ _).trans (by omega)) hv
        (physicalOutput_entry_norm C.outputWire) ψ)
  · exact shifted_value_good (qmaClause2Bits C+1) (extraBits C) _
      ((nativeJ C:ℂ) • TensorGate (pairPenalty i j)
        (1:Matrix (Reg C.qubits) (Reg C.qubits) ℂ)) (nativeJ C:ℝ)
      (clockPairTerm_value C.qubits (qmaClause2Bits C) (nativeJ C) i j)
      (clockPair_hermitian (nativeJ C) i j) hJ (clockPair_energy_abs (nativeJ C) i j)

theorem normalizedEncoding_term_norm (C : QmaHistoryCircuit) :
    ∀t∈(normalizedEncoding C).terms,
      ‖Matrix.toEuclideanCLM (𝕜:=ℂ)
        (lhEmbedTerm (normalizedEncoding C).width t)‖ ≤ 1 := by
  intro s hs
  change s∈(baseTerms C).map toLhTerm at hs
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hs
  change ‖Matrix.toEuclideanCLM (𝕜:=ℂ)
    (lhEmbedTerm (qmaClause2Bits C+1+extraBits C) (toLhTerm t))‖ ≤ 1
  rw [lhEmbedTerm_toLhTerm (qmaClause2Bits C+1+extraBits C) t]
  exact (normalized_terms_good C t ht).2

theorem normalizedEncoding_term_hermitian (C : QmaHistoryCircuit) :
    ∀t∈(normalizedEncoding C).terms,
      Matrix.IsHermitian (lhEmbedTerm (normalizedEncoding C).width t) := by
  intro s hs
  change s∈(baseTerms C).map toLhTerm at hs
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hs
  change Matrix.IsHermitian (lhEmbedTerm (qmaClause2Bits C+1+extraBits C) (toLhTerm t))
  rw [lhEmbedTerm_toLhTerm (qmaClause2Bits C+1+extraBits C) t]
  exact (normalized_terms_good C t ht).1

theorem normalizedEncoding_local (C : QmaHistoryCircuit) :
    lhLocal 5 (normalizedEncoding C) :=
  toLhEncoding_local _ 5 _ (outputTerms_local _ _ _ _ _)

theorem normalizedEncoding_lhHermitian (C : QmaHistoryCircuit) :
    lhHermitian (normalizedEncoding C) := by
  rw [normalizedEncoding_def]
  exact outputEncoding_anyWidth_hermitian C.qubits (qmaClause2Bits C)
    (qmaClause2Bits C+1+extraBits C) C.gates C.initZeroWires C.outputWire

theorem normalizedEncoding_schema (C : QmaHistoryCircuit) :
    lhLocal 5 (normalizedEncoding C) ∧ lhHermitian (normalizedEncoding C) ∧
    (∀t∈(normalizedEncoding C).terms,
      ‖Matrix.toEuclideanCLM (𝕜:=ℂ)
        (lhEmbedTerm (normalizedEncoding C).width t)‖ ≤ 1) :=
  ⟨normalizedEncoding_local C, normalizedEncoding_lhHermitian C,
    normalizedEncoding_term_norm C⟩

theorem normalized_energy_transport (C : QmaHistoryCircuit) (ψ : QState (Phys C)) :
    energy (lhHamiltonian (normalizedEncoding C))
      (fun x => ψ (flattenEquiv C.gates.length C.qubits x)) =
      scale C * energy (fullHamiltonian C) ψ := by
  rw [normalizedEncoding_semantics]
  have hscale := energy_matrix_real_smul (scale C)
    (Matrix.reindex (flattenEquiv C.gates.length C.qubits).symm
      (flattenEquiv C.gates.length C.qubits).symm (fullHamiltonian C))
    (fun x => ψ (flattenEquiv C.gates.length C.qubits x))
  push_cast at hscale
  have he := energy_reindex (flattenEquiv C.gates.length C.qubits).symm (fullHamiltonian C) ψ
  apply hscale.trans
  simpa only [Equiv.symm_symm] using! congrArg (fun r : ℝ => scale C*r) he

theorem flattened_normalized (C : QmaHistoryCircuit) (ψ : QState (Phys C))
    (hψ : Normalized ψ) :
    Normalized (fun x => ψ (flattenEquiv C.gates.length C.qubits x)) := by
  change mass (fun x => ψ (flattenEquiv C.gates.length C.qubits x))=1
  have hm := mass_reindex (flattenEquiv C.gates.length C.qubits).symm ψ
  simpa only [Equiv.symm_symm] using! hm.trans hψ

theorem denominator_le_poly (C : QmaHistoryCircuit) :
    denominator C ≤ 130*restLength C := by
  have h := (scaleDen_bounds (nativeJ C)).2.2.1
  have hL : 1 ≤ restLength C := by unfold restLength; omega
  change denominator C ≤ 2*(32+nativeJ C) at h
  dsimp only [nativeJ, restLength] at hL h ⊢
  omega

theorem gap_positive (C : QmaHistoryCircuit) :
    0 < yesThreshold C ∧ noThreshold C-yesThreshold C=yesThreshold C := by
  constructor
  · unfold yesThreshold
    exact div_pos (cut_gap C).1 (by exact_mod_cast denominator_pos C)
  · unfold noThreshold yesThreshold
    rw [← sub_div, (cut_gap C).2]

theorem gap_inverse_poly (C : QmaHistoryCircuit) :
    1 / ((2:ℝ)^13*130*(restLength C:ℝ)*((C.gates.length:ℝ)+1)^3)  ≤  yesThreshold C := by
  have hS : 0 < (denominator C:ℝ) := by exact_mod_cast denominator_pos C
  have hL : 0 < (restLength C:ℝ) := by unfold restLength; positivity
  have hSP : (denominator C:ℝ) ≤ 130*(restLength C:ℝ) := by
    exact_mod_cast denominator_le_poly C
  have he : yesThreshold C =
      1 / ((2:ℝ)^13*((C.gates.length:ℝ)+1)^3*(denominator C:ℝ)) := by
    unfold yesThreshold yesCut
    field_simp [hS.ne']
  rw [he]
  apply one_div_le_one_div_of_le (by positivity)
  have hm := mul_le_mul_of_nonneg_left hSP
    (by positivity : (0:ℝ) ≤ (2:ℝ)^13*((C.gates.length:ℝ)+1)^3)
  nlinarith

theorem padded_normalized_contract (C : QmaHistoryCircuit) (a ε : ℝ)
    (hε : ε ≤ 1/4)
    (ha : 1-a ≤ 1/((2:ℝ)^14*(((paid64 C).gates.length:ℝ)+1)^2)) :
    ((∃φ : QState (Reg C.qubits), QmaInitLegal C φ ∧ Normalized φ ∧
        a ≤ qmaHistoryAcceptProb C φ) →
      ∃η : QState (Reg ((paid64 C).gates.length+C.qubits)), Normalized η ∧
        energy (lhHamiltonian (normalizedEncoding (paid64 C))) η  ≤  yesThreshold (paid64 C)) ∧
    ((∀φ : QState (Reg C.qubits), QmaInitLegal C φ → Normalized φ →
        qmaHistoryAcceptProb C φ ≤ ε) →
      ∀η : QState (Reg ((paid64 C).gates.length+C.qubits)), Normalized η →
        noThreshold (paid64 C) ≤ energy (lhHamiltonian (normalizedEncoding (paid64 C))) η) ∧
    0 < yesThreshold (paid64 C) ∧
    noThreshold (paid64 C)-yesThreshold (paid64 C)=yesThreshold (paid64 C) := by
  have hc := padded_full_contract C a ε hε ha
  refine ⟨?_,?_,(gap_positive (paid64 C)).1,(gap_positive (paid64 C)).2⟩
  · intro hyes
    obtain ⟨ψ,hψ,hE⟩ := hc.1 hyes
    refine ⟨fun x => ψ (flattenEquiv (paid64 C).gates.length (paid64 C).qubits x),
      flattened_normalized (paid64 C) ψ hψ,?_⟩
    apply (normalized_energy_transport (paid64 C) ψ).trans_le
    have h := mul_le_mul_of_nonneg_left hE (scale_pos (paid64 C)).le
    simpa only [yesThreshold, scale, div_eq_mul_inv, mul_comm,one_mul] using! h
  · intro hsound η hη
    let ψ : QState (Phys (paid64 C)) := fun p =>
      η ((flattenEquiv (paid64 C).gates.length (paid64 C).qubits).symm p)
    have hψ : Normalized ψ := by
      change mass ψ=1
      exact (mass_reindex (flattenEquiv (paid64 C).gates.length (paid64 C).qubits) η).trans hη
    have hE := hc.2.1 hsound ψ hψ
    have ht := normalized_energy_transport (paid64 C) ψ
    have ht' : energy (lhHamiltonian (normalizedEncoding (paid64 C))) η =
        scale (paid64 C)*energy (fullHamiltonian (paid64 C)) ψ := by
      simpa only [ψ, Equiv.symm_apply_apply] using! ht
    rw [ht']
    have h := mul_le_mul_of_nonneg_left hE (scale_pos (paid64 C)).le
    simpa only [noThreshold, scale, div_eq_mul_inv, mul_comm,one_mul] using! h

end
end Qatlib.Papers.LocalHam06.MainResults
