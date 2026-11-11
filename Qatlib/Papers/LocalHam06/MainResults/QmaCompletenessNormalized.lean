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

/-!
# Normalization of history Hamiltonian encodings

The encoding `normalizedEncoding` rescales the generated history Hamiltonian by a dyadic
denominator. Its embedded terms are Hermitian, have operator norm at most one, and act on at
most five wires. The theorem `padded_normalized_contract` transports completeness and soundness
bounds to the normalized encoding with an explicit positive threshold gap. See
[KempeKitaevRegev2006].

## Main statements

* `normalizedEncoding_schema`: The normalized encoding is five-local and Hermitian, and all its
  embedded terms have operator norm at most one.
* `normalizedEncoding_semantics`: The Hamiltonian of the normalized encoding is `scale C` times
  the flattened full physical Hamiltonian.
* `padded_normalized_contract`: Under the stated parameter bounds, acceptance of a legal
  normalized witness with probability at least `a` yields a normalized padded encoding state
  with energy at most `yesThreshold`, while acceptance at most `ε` for every legal normalized
  witness gives energy at least `noThreshold` for every normalized encoding state. The
  thresholds have a positive gap equal to the completeness threshold; this supports the
  reduction in [KempeKitaevRegev2006].

## References

* [Kempe et al., 2006][KempeKitaevRegev2006]
-/

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

/-- The integer local terms generated from the circuit using the precision `qmaClause2Bits C`. -/
def baseTerms (C : QmaHistoryCircuit) : List (IntegerLocalTerm (C.gates.length+C.qubits)) :=
  outputTerms C.qubits (qmaClause2Bits C) C.gates C.initZeroWires C.outputWire

/-- The additional dyadic precision `scaleBits (nativeJ C)` used to normalize the local terms. -/
def extraBits (C : QmaHistoryCircuit) : ℕ := scaleBits (nativeJ C)
/-- The dyadic normalization denominator `scaleDen (nativeJ C)`. -/
def denominator (C : QmaHistoryCircuit) : ℕ := scaleDen (nativeJ C)

/-- The scaled local Hamiltonian encoding of the circuit at precision `qmaClause2Bits C`. -/
abbrev normalizedEncoding (C : QmaHistoryCircuit) : LhEncoding :=
  scaledEncoding C.qubits (qmaClause2Bits C) C.gates C.initZeroWires C.outputWire

/-- The normalized encoding consists of `baseTerms C` encoded at width `qmaClause2Bits C + 1 +
extraBits C`. -/
theorem normalizedEncoding_def (C : QmaHistoryCircuit) :
    normalizedEncoding C = toLhEncoding (qmaClause2Bits C+1+extraBits C) (baseTerms C) := rfl

/-- The reciprocal of the normalization denominator, viewed as a real scaling factor. -/
def scale (C : QmaHistoryCircuit) : ℝ := 1/(denominator C : ℝ)
/-- The completeness cutoff `yesCut C` divided by the normalization denominator. -/
def yesThreshold (C : QmaHistoryCircuit) : ℝ := yesCut C/(denominator C : ℝ)
/-- The soundness cutoff `noCut C` divided by the normalization denominator. -/
def noThreshold (C : QmaHistoryCircuit) : ℝ := noCut C/(denominator C : ℝ)

/-- The normalization denominator is strictly positive. -/
theorem denominator_pos (C : QmaHistoryCircuit) : 0 < denominator C := by
  have h := (scaleDen_bounds (nativeJ C)).1
  change 32 ≤ denominator C at h
  omega

/-- The real normalization factor is strictly positive. -/
theorem scale_pos (C : QmaHistoryCircuit) : 0 < scale C := by
  unfold scale
  exact one_div_pos.mpr (by exact_mod_cast denominator_pos C)

/-- The normalization factor equals the reciprocal of `2^(extraBits C)`. -/
theorem scale_eq_inv_power (C : QmaHistoryCircuit) :
    scale C = ((2:ℝ)^extraBits C)⁻¹ := by
  simp [scale, denominator, scaleDen, extraBits, one_div, Nat.cast_pow]

/-- Summing a list after multiplying each matrix by a complex scalar equals scaling its matrix
sum. -/
theorem matrixSum_smul {I : Type} [Fintype I] [DecidableEq I]
    (c : ℂ) (xs : List (Matrix I I ℂ)) :
    matrixSum (xs.map (fun M => c • M)) = c • matrixSum xs := by
  induction xs with
  | nil => simp [matrixSum]
  | cons M xs ih =>
      change c • M + matrixSum (xs.map (fun M => c • M)) = c • (M+matrixSum xs)
      rw [ih, smul_add]

/-- The Hamiltonian of the normalized encoding is `scale C` times the flattened full physical
Hamiltonian. -/
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

/-- Reindexing a matrix along an equivalence preserves an absolute energy bound by `B` times the
state mass. -/
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

/-- Multiplying a Hermitian complex matrix by a real scalar preserves Hermiticity. -/
theorem real_smul_hermitian {I : Type} [DecidableEq I]
    (r : ℝ) (H : Matrix I I ℂ) (hH : Matrix.IsHermitian H) :
    Matrix.IsHermitian ((r:ℂ) • H) := by
  change (((r:ℂ) • H)ᴴ) = _
  simp only [Matrix.conjTranspose_smul, hH.eq]
  simp

/-- If a term represents a Hermitian matrix with absolute energy bounded by `B` times mass and
`B ≤ 2^q`, increasing its width by `q` gives a Hermitian value of operator norm at most one. -/
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

/-- The power `2^(extraBits C)` bounds both `32` and the natural clock penalty `nativeJ C`. -/
theorem extraBits_bounds (C : QmaHistoryCircuit) :
    (32:ℝ) ≤ (2:ℝ)^extraBits C ∧ (nativeJ C:ℝ) ≤ (2:ℝ)^extraBits C := by
  have h0 : (32:ℝ) ≤ (scaleDen (nativeJ C):ℝ) := by
    exact_mod_cast (scaleDen_bounds (nativeJ C)).1
  have h1 : (nativeJ C:ℝ) ≤ (scaleDen (nativeJ C):ℝ) := by
    exact_mod_cast (scaleDen_bounds (nativeJ C)).2.1
  simpa only [scaleDen, extraBits, Nat.cast_pow, Nat.cast_ofNat] using! And.intro h0 h1

/-- Each base term, interpreted at the normalized width, is Hermitian and has operator norm at
most one. -/
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

/-- Every embedded term of the normalized encoding has operator norm at most one. -/
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

/-- Every embedded term of the normalized encoding is Hermitian. -/
theorem normalizedEncoding_term_hermitian (C : QmaHistoryCircuit) :
    ∀t∈(normalizedEncoding C).terms,
      Matrix.IsHermitian (lhEmbedTerm (normalizedEncoding C).width t) := by
  intro s hs
  change s∈(baseTerms C).map toLhTerm at hs
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hs
  change Matrix.IsHermitian (lhEmbedTerm (qmaClause2Bits C+1+extraBits C) (toLhTerm t))
  rw [lhEmbedTerm_toLhTerm (qmaClause2Bits C+1+extraBits C) t]
  exact (normalized_terms_good C t ht).1

/-- The normalized encoding is five-local. -/
theorem normalizedEncoding_local (C : QmaHistoryCircuit) :
    lhLocal 5 (normalizedEncoding C) :=
  toLhEncoding_local _ 5 _ (outputTerms_local _ _ _ _ _)

/-- The normalized encoding satisfies the integer-field Hermiticity predicate `lhHermitian`. -/
theorem normalizedEncoding_lhHermitian (C : QmaHistoryCircuit) :
    lhHermitian (normalizedEncoding C) := by
  rw [normalizedEncoding_def]
  exact outputEncoding_anyWidth_hermitian C.qubits (qmaClause2Bits C)
    (qmaClause2Bits C+1+extraBits C) C.gates C.initZeroWires C.outputWire

/-- The normalized encoding is five-local and Hermitian, and all its embedded terms have
operator norm at most one. -/
theorem normalizedEncoding_schema (C : QmaHistoryCircuit) :
    lhLocal 5 (normalizedEncoding C) ∧ lhHermitian (normalizedEncoding C) ∧
    (∀t∈(normalizedEncoding C).terms,
      ‖Matrix.toEuclideanCLM (𝕜:=ℂ)
        (lhEmbedTerm (normalizedEncoding C).width t)‖ ≤ 1) :=
  ⟨normalizedEncoding_local C, normalizedEncoding_lhHermitian C,
    normalizedEncoding_term_norm C⟩

/-- The normalized encoding energy of the flattened state is `scale C` times its full physical
Hamiltonian energy. -/
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

/-- Flattening a normalized physical state preserves normalization. -/
theorem flattened_normalized (C : QmaHistoryCircuit) (ψ : QState (Phys C))
    (hψ : Normalized ψ) :
    Normalized (fun x => ψ (flattenEquiv C.gates.length C.qubits x)) := by
  change mass (fun x => ψ (flattenEquiv C.gates.length C.qubits x))=1
  have hm := mass_reindex (flattenEquiv C.gates.length C.qubits).symm ψ
  simpa only [Equiv.symm_symm] using! hm.trans hψ

/-- The normalization denominator is at most `130 * restLength C`. -/
theorem denominator_le_poly (C : QmaHistoryCircuit) :
    denominator C ≤ 130*restLength C := by
  have h := (scaleDen_bounds (nativeJ C)).2.2.1
  have hL : 1 ≤ restLength C := by unfold restLength; omega
  change denominator C ≤ 2*(32+nativeJ C) at h
  dsimp only [nativeJ, restLength] at hL h ⊢
  omega

/-- The normalized completeness threshold is positive, and the difference between the soundness
and completeness thresholds equals the completeness threshold. -/
theorem gap_positive (C : QmaHistoryCircuit) :
    0 < yesThreshold C ∧ noThreshold C-yesThreshold C=yesThreshold C := by
  constructor
  · unfold yesThreshold
    exact div_pos (cut_gap C).1 (by exact_mod_cast denominator_pos C)
  · unfold noThreshold yesThreshold
    rw [← sub_div, (cut_gap C).2]

/-- The normalized completeness threshold is bounded below by the reciprocal of `2^13 * 130 *
restLength C * (C.gates.length + 1)^3`. -/
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

/-- Under the stated parameter bounds, acceptance of a legal normalized witness with probability
at least `a` yields a normalized padded encoding state with energy at most `yesThreshold`,
while acceptance at most `ε` for every legal normalized witness gives energy at least
`noThreshold` for every normalized encoding state. The thresholds have a positive gap equal
to the completeness threshold; this supports the reduction in [KempeKitaevRegev2006]. -/
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
