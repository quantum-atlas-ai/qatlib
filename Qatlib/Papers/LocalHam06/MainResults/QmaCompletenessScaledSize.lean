/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LocalHam06.MainResults.QmaCompletenessSize
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessNativeNorm
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Papers.LocalHam06.MainResults

open Qatlib Matrix
open  Qatlib.Concepts.QmaCompleteness.HistoryHam
open scoped Classical BigOperators
set_option autoImplicit false

theorem fixedOutput_num_cap (n baseb width : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    ∀t∈(toLhEncoding width (outputTerms n baseb gs aux out)).terms,∀p q,
      (t.re p q).natAbs ≤ 2^(baseb+outputPenalty gs.length aux.card+3) ∧
      (t.im p q).natAbs ≤ 2^(baseb+outputPenalty gs.length aux.card+3) := by
  intro t ht
  change t∈(outputTerms n baseb gs aux out).map toLhTerm at ht
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
  intro p q
  exact outputTerms_natAbsCap n baseb gs aux out u hu
    (nativeIndexDecode u.support p) (nativeIndexDecode u.support q)

theorem fixedOutput_bitlength_general (n baseb width : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    (qmaClause3ToBits (toLhEncoding width (outputTerms n baseb gs aux out))).length ≤
      2*(gs.length+n)+2*width+7+
      (gs.length+aux.card+1+gs.length^2)*
        (10*(gs.length+n)+4096*(baseb+outputPenalty gs.length aux.card+3)+10276) := by
  have h := encoding_length_le (toLhEncoding width (outputTerms n baseb gs aux out))
    (baseb+outputPenalty gs.length aux.card+3)
    (toLhEncoding_local width 5 _ (outputTerms_local n baseb gs aux out))
    (fixedOutput_num_cap n baseb width gs aux out)
  simpa only [toLhEncoding,List.length_map,outputTerms_length] using h

def scaledEncoding (n baseb : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) : LhEncoding :=
  toLhEncoding (baseb+1+Qatlib.Concepts.QueryComplexity.DegreeMethod.scaleBits (outputPenalty gs.length aux.card))
    (outputTerms n baseb gs aux out)

theorem scaledEncoding_terms_eq (n baseb : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    (scaledEncoding n baseb gs aux out).terms=(actualEncoding n baseb gs aux out).terms := rfl

theorem scaledEncoding_local (n baseb : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    lhLocal 5 (scaledEncoding n baseb gs aux out) :=
  toLhEncoding_local _ 5 _ (outputTerms_local n baseb gs aux out)

theorem scaleBits_outputPenalty_le (m a : ℕ) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.scaleBits (outputPenalty m a) ≤ 130*(m+a+1) := by
  have h := (Qatlib.Concepts.QueryComplexity.DegreeMethod.scaleDen_bounds (outputPenalty m a)).2.2.2
  dsimp [outputPenalty] at h ⊢
  omega

theorem scaledEncoding_bitlength_general (n baseb : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    (qmaClause3ToBits (scaledEncoding n baseb gs aux out)).length ≤
      2*(gs.length+n)+
        2*(baseb+1+Qatlib.Concepts.QueryComplexity.DegreeMethod.scaleBits (outputPenalty gs.length aux.card))+7+
      (gs.length+aux.card+1+gs.length^2)*
        (10*(gs.length+n)+4096*(baseb+outputPenalty gs.length aux.card+3)+10276) :=
  fixedOutput_bitlength_general n baseb _ gs aux out

theorem scaledEncoding_width_polynomial (n : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    (scaledEncoding n (3*(gs.length+n)+64) gs aux out).width ≤
      133*(gs.length+n)+195 := by
  have ha : aux.card ≤ n := by
    simpa only [Fintype.card_fin] using (Finset.card_le_univ aux)
  have hq := scaleBits_outputPenalty_le gs.length aux.card
  change 3*(gs.length+n)+64+1+
    Qatlib.Concepts.QueryComplexity.DegreeMethod.scaleBits (outputPenalty gs.length aux.card) ≤ 133*(gs.length+n)+195
  omega

theorem scaledEncoding_bitlength_polynomial (n : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    (qmaClause3ToBits (scaledEncoding n (3*(gs.length+n)+64) gs aux out)).length ≤
      2000000*(gs.length+n+1)^3 := by
  let N := gs.length+n
  let b := 3*N+64
  let J := outputPenalty gs.length aux.card
  let q := Qatlib.Concepts.QueryComplexity.DegreeMethod.scaleBits J
  let T := gs.length+aux.card+1+gs.length^2
  let D := 10*N+4096*(b+J+3)+10276
  have ha : aux.card ≤ n := by
    simpa only [Fintype.card_fin] using (Finset.card_le_univ aux)
  have hm : gs.length ≤ N := by dsimp [N]; omega
  have hJ : J ≤ 32*N+33 := by dsimp [J,outputPenalty,N]; omega
  have hq : q ≤ 130*(N+1) := by
    have h := scaleBits_outputPenalty_le gs.length aux.card
    change q ≤ 130*(N+1)
    dsimp [q,J] at *
    dsimp [N] at *
    omega
  have hD : D ≤ 600000*(N+1) := by dsimp [D,b]; omega
  have hT : T ≤ (N+1)^2 := by
    have hsq := Nat.mul_le_mul hm hm
    dsimp [T,N] at *
    nlinarith
  have hprefix : 2*N+2*(b+1+q)+7 ≤ 600000*(N+1) := by dsimp [b]; omega
  have hprod : T*D ≤ (N+1)^2*(600000*(N+1)) := Nat.mul_le_mul hT hD
  have hcube : N+1 ≤ (N+1)^3 := by
    have h₁ := Nat.le_mul_self (N+1)
    have h₂ := Nat.mul_le_mul_left (N+1) h₁
    nlinarith
  have hbase := scaledEncoding_bitlength_general n b gs aux out
  change (qmaClause3ToBits (scaledEncoding n b gs aux out)).length ≤ 2000000*(N+1)^3
  have hbase' : (qmaClause3ToBits (scaledEncoding n b gs aux out)).length ≤
      2*N+2*(b+1+q)+7+T*D := hbase
  nlinarith

end Qatlib.Papers.LocalHam06.MainResults
