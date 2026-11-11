/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LocalHam06.MainResults.QmaCompletenessEncoding
import Qatlib.Papers.LocalHam06.MainResults.QmaCompletenessNative
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessNativeBoundary
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessNativeEnergy
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessEntryBounds

/-!
# Hermiticity of encoded history terms

This module transfers Hermiticity of dyadic matrix values to the integer fields of local
Hamiltonian encodings. It proves that every term in `outputTerms` is Hermitian and establishes
`actualEncoding_hermitian`, including preservation under changes of encoding width. See
[KempeKitaevRegev2006].

## Main statements

* `integer_fields_of_value_hermitian`: Hermiticity of the dyadic value of an integer local term
  forces its real numerator matrix to be symmetric and its imaginary numerator matrix to be
  skew-symmetric.
* `actualEncoding_hermitian`: The generated encoding `actualEncoding n b gs aux out` satisfies
  `lhHermitian`.
* `outputEncoding_anyWidth_hermitian`: Encoding the generated output terms at any dyadic width
  satisfies `lhHermitian`.

## References

* [Kempe et al., 2006][KempeKitaevRegev2006]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Papers.LocalHam06.MainResults.NativeOutput

namespace Qatlib.Papers.LocalHam06.MainResults
open Qatlib  Matrix
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Papers.LocalHam06.MainResults
open scoped Classical
set_option autoImplicit false
noncomputable section

/-- The real part of `dyadicValue b r i` is the real integer numerator `r` divided by `2^b`. -/
theorem dyadic_re (b : ℕ) (r i : ℤ) :
    (dyadicValue b r i).re = (r:ℝ)/(2:ℝ)^b := by
  have hd : (2:ℂ)^b = (((2:ℝ)^b:ℝ):ℂ) := (Complex.ofReal_pow (2:ℝ) b).symm
  unfold dyadicValue
  rw [hd, Complex.div_ofReal_re]
  simp

/-- The imaginary part of `dyadicValue b r i` is the real integer numerator `i` divided by
`2^b`. -/
theorem dyadic_im (b : ℕ) (r i : ℤ) :
    (dyadicValue b r i).im = (i:ℝ)/(2:ℝ)^b := by
  have hd : (2:ℂ)^b = (((2:ℝ)^b:ℝ):ℂ) := (Complex.ofReal_pow (2:ℝ) b).symm
  unfold dyadicValue
  rw [hd, Complex.div_ofReal_im]
  simp

/-- Hermiticity of the dyadic value of an integer local term forces its real numerator matrix to
be symmetric and its imaginary numerator matrix to be skew-symmetric. -/
theorem integer_fields_of_value_hermitian {N : ℕ} (b : ℕ) (t : IntegerLocalTerm N)
    (hH : Matrix.IsHermitian (value b t)) (u v : Reg t.support.card) :
    t.re u v = t.re v u ∧ t.im u v = -t.im v u := by
  have he := congrArg (fun M : Matrix (Reg N) (Reg N) ℂ =>
    M (fill t.support u) (fill t.support v)) hH.eq
  change star (value b t (fill t.support v) (fill t.support u)) =
    value b t (fill t.support u) (fill t.support v) at he
  rw [value_fill, value_fill] at he
  have hd : (2:ℝ)^b ≠ 0 := by positivity
  constructor
  · have hr := congrArg Complex.re he
    have hr' : (t.re u v:ℝ)/(2:ℝ)^b = (t.re v u:ℝ)/(2:ℝ)^b := by
      simpa only [Complex.star_def, Complex.conj_re, dyadic_re] using hr.symm
    have hreal : (t.re u v:ℝ) = (t.re v u:ℝ) := (div_left_inj' hd).mp hr'
    exact_mod_cast hreal
  · have hi := congrArg Complex.im he
    have hi' : (t.im u v:ℝ)/(2:ℝ)^b = (-(t.im v u:ℝ))/(2:ℝ)^b := by
      simpa only [Complex.star_def, Complex.conj_im, dyadic_im, neg_div] using hi.symm
    have hreal : (t.im u v:ℝ) = -(t.im v u:ℝ) := (div_left_inj' hd).mp hi'
    exact_mod_cast hreal

/-- Converting a term with Hermitian dyadic value to `LhTerm` preserves symmetry of the real
fields and skew-symmetry of the imaginary fields. -/
theorem toLhTerm_fields {N : ℕ} (b : ℕ) (t : IntegerLocalTerm N)
    (hH : Matrix.IsHermitian (value b t))
    (p q : Fin (2^(toLhTerm t).wires.length)) :
    (toLhTerm t).re p q = (toLhTerm t).re q p ∧
    (toLhTerm t).im p q = -(toLhTerm t).im q p := by
  exact integer_fields_of_value_hermitian b t hH
    (nativeIndexDecode t.support p) (nativeIndexDecode t.support q)

/-- A list of integer local terms with symmetric real fields and skew-symmetric imaginary fields
yields a Hermitian encoding at any width. -/
theorem toLhEncoding_hermitian_of_fields {N : ℕ} (width : ℕ)
    (ts : List (IntegerLocalTerm N))
    (h : ∀t∈ts,∀u v : Reg t.support.card,
      t.re u v=t.re v u ∧ t.im u v= -t.im v u) :
    lhHermitian (toLhEncoding width ts) := by
  intro s hs p q
  change s∈ts.map toLhTerm at hs
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hs
  exact h t ht (nativeIndexDecode t.support p) (nativeIndexDecode t.support q)

/-- A list whose dyadic values at width `b` are Hermitian yields a Hermitian local Hamiltonian
encoding at that width. -/
theorem toLhEncoding_hermitian {N : ℕ} (b : ℕ) (ts : List (IntegerLocalTerm N))
    (h : ∀t∈ts,Matrix.IsHermitian (value b t)) :
    lhHermitian (toLhEncoding b ts) := by
  apply toLhEncoding_hermitian_of_fields
  intro t ht u v
  exact integer_fields_of_value_hermitian b t (h t ht) u v

/-- A clock pair penalty tensored with the data identity and scaled by a natural weight is
Hermitian. -/
theorem weighted_clockPair_hermitian {m n : ℕ} (J : ℕ) (i j : Fin m) :
    Matrix.IsHermitian ((J:ℂ) • TensorGate (pairPenalty i j)
      (1:Matrix (Reg n) (Reg n) ℂ)) := by
  change (((J:ℂ) • TensorGate (pairPenalty i j)
    (1:Matrix (Reg n) (Reg n) ℂ))ᴴ) = _
  simp only [Matrix.conjTranspose_smul, tensorGate_conjTranspose,
    (pairPenalty_hermitian i j).eq, Matrix.conjTranspose_one]
  simp

/-- Every term generated by `outputTerms n b gs aux out` has a Hermitian value at width `b + 1`. -/
theorem outputTerms_each_hermitian (n b : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    ∀t∈outputTerms n b gs aux out, Matrix.IsHermitian (value (b+1) t) := by
  intro t ht
  simp only [outputTerms, List.mem_append, List.mem_map, List.mem_singleton,
    List.mem_flatMap] at ht
  rcases ht with ((⟨i,_,rfl⟩ | ⟨j,_,rfl⟩) | rfl) | ⟨i,_,j,_,rfl⟩
  · rw [propagationTerm_value]
    exact (physicalPropagation_hermitian i (qmaRoundedGate n b (gs.get i))).reindex
      (flattenEquiv gs.length n).symm
  · rw [boundaryTerm_value]
    simpa only [boundaryTarget, Bool.false_eq_true, if_false] using
      (physicalInput_hermitian (m:=gs.length) j).reindex (flattenEquiv gs.length n).symm
  · rw [boundaryTerm_value]
    simpa only [boundaryTarget, if_true] using
      (physicalOutput_hermitian (m:=gs.length) out).reindex (flattenEquiv gs.length n).symm
  · rw [clockPairTerm_value]
    exact (weighted_clockPair_hermitian (n:=n)
      (32*(gs.length+aux.card+1)+1) i j).reindex (flattenEquiv gs.length n).symm

/-- The generated encoding `actualEncoding n b gs aux out` satisfies `lhHermitian`. -/
theorem actualEncoding_hermitian (n b : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    lhHermitian (actualEncoding n b gs aux out) := by
  exact toLhEncoding_hermitian (b+1) _ (outputTerms_each_hermitian n b gs aux out)

/-- Encoding the generated output terms at any dyadic width satisfies `lhHermitian`. -/
theorem outputEncoding_anyWidth_hermitian (n b width : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    lhHermitian (toLhEncoding width (outputTerms n b gs aux out)) := by
  apply toLhEncoding_hermitian_of_fields
  intro t ht u v
  exact integer_fields_of_value_hermitian (b+1) t
    (outputTerms_each_hermitian n b gs aux out t ht) u v

end
end Qatlib.Papers.LocalHam06.MainResults
