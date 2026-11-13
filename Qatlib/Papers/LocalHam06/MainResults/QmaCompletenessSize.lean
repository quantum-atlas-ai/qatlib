/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LocalHam06.MainResults.QmaCompletenessEncoding

/-!
# Bit length bounds for history Hamiltonian encodings

This module bounds integer coefficient sizes and serialized lengths for the generated local
Hamiltonian encoding. The predicates `SignedCap` and the bounds on `outputTerms` feed into
`actualEncoding_bitlength_polynomial`, an explicit cubic bound at the chosen precision. See
[KempeKitaevRegev2006].

## Main statements

* `encoding_length_le`: A five-local encoding whose integer entries have natural absolute value
  at most `2^E` satisfies the displayed total bit length bound.
* `outputTerms_natAbsCap`: All real and imaginary integer entries of generated output terms have
  natural absolute value at most `2^(b + outputPenalty gs.length aux.card + 3)`.
* `actualEncoding_bitlength_polynomial`: At precision `3 * (gs.length + n) + 64`, the generated
  encoding has bit length at most `1200000 * (gs.length + n + 1)^3`.

## References

* [Kempe et al., 2006][KempeKitaevRegev2006]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Papers.LocalHam06.MainResults

open Qatlib Matrix
open  Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.TensorRegisters.RegisterModel
open scoped Classical BigOperators
set_option autoImplicit false

/-- If every element has encoding length at most `B`, the sum of the encoding lengths is at most
`xs.length * B`. -/
theorem sum_encoded_lengths_le {A : Type} (f : A→List Bool) (xs : List A) (B : ℕ)
    (h : ∀x∈xs,(f x).length ≤ B) :
    ((xs.map f).map List.length).sum ≤ xs.length*B := by
  simp only [List.map_map,Function.comp_def]
  revert h
  induction xs with
  | nil => intro h; simp
  | cons a xs ih =>
    intro h
    have ha := h a (by simp)
    have hs := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- Encoding a list of elements of encoding length at most `B` uses at most `xs.length + 1 +
xs.length * B` bits. -/
theorem encList_length_le {A : Type} (f : A→List Bool) (xs : List A) (B : ℕ)
    (h : ∀x∈xs,(f x).length ≤ B) :
    (qmaClause3EncList f xs).length ≤ xs.length+1+xs.length*B := by
  rw [encList_length]
  have hh := sum_encoded_lengths_le f xs B h
  omega

/-- The list of ordered matrix index pairs for dimension `d` has length `d * d`. -/
theorem lhIndexPairs_length (d : ℕ) : (lhIndexPairs d).length=d*d := by
  simp [lhIndexPairs,List.length_flatMap,List.sum_replicate]

/-- The real and imaginary entry list of a local term has length `2 * (2^t.wires.length)^2`. -/
theorem termEntries_length {N : ℕ} (t : LhTerm N) :
    (qmaClause3TermEntries t).length=2*(2^t.wires.length)^2 := by
  simp only [qmaClause3TermEntries,List.length_append,List.length_map,lhIndexPairs_length,pow_two]
  omega

/-- A natural absolute value bound of `2^E` on both integer entry matrices also bounds every
entry in their serialized list. -/
theorem termEntries_cap {N E : ℕ} (t : LhTerm N)
    (h : ∀p q,(t.re p q).natAbs ≤ 2^E ∧ (t.im p q).natAbs ≤ 2^E) :
    ∀z∈qmaClause3TermEntries t,z.natAbs ≤ 2^E := by
  intro z hz
  simp only [qmaClause3TermEntries,List.mem_append,List.mem_map] at hz
  rcases hz with ⟨p,_,rfl⟩|⟨p,_,rfl⟩
  · exact (h p.1 p.2).1
  · exact (h p.1 p.2).2

/-- The natural number encoding of `v` has length at most `2 * v + 3`. -/
theorem encNat_length_le_self (v : ℕ) : (qmaClause3EncNat v).length ≤ 2*v+3 := by
  rw [encNat_length]
  have h := Nat.log2_le_self v
  omega

/-- A term on at most five wires with integer entries bounded in natural absolute value by `2^E`
has encoding length at most `10 * N + 4096 * E + 10275`. -/
theorem encTerm_length_le {N : ℕ} (t : LhTerm N) (E : ℕ)
    (hk : t.wires.length ≤ 5)
    (hnum : ∀p q,(t.re p q).natAbs ≤ 2^E ∧ (t.im p q).natAbs ≤ 2^E) :
    (qmaClause3EncTerm t).length ≤ 10*N+4096*E+10275 := by
  have hhead : (qmaClause3EncNat t.wires.length).length ≤ 13 := by
    have h := encNat_length_le_self t.wires.length
    omega
  have hwire : ∀j∈t.wires,(qmaClause3EncNat j.val).length ≤ 2*N+3 := by
    intro j _
    have h := encNat_length_le_self j.val
    have hj := j.isLt
    omega
  have hw := encList_length_le (fun j : Fin N => qmaClause3EncNat j.val)
    t.wires (2*N+3) hwire
  have hwm := Nat.mul_le_mul_right (2*N+3) hk
  have hw' : (qmaClause3EncList (fun j : Fin N => qmaClause3EncNat j.val) t.wires).length ≤
      6+5*(2*N+3) := by omega
  have hd : 2^t.wires.length ≤ 32 := by
    exact le_trans (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk) (by norm_num)
  have hlen : (qmaClause3TermEntries t).length ≤ 2048 := by
    rw [termEntries_length,pow_two]
    have hmul := Nat.mul_le_mul hd hd
    nlinarith
  have helem : ∀z∈qmaClause3TermEntries t,(qmaClause3EncInt z).length ≤ 2*E+4 := by
    intro z hz
    exact encInt_length_le_of_natAbs_le_pow z E (termEntries_cap t hnum z hz)
  have he := encList_length_le qmaClause3EncInt (qmaClause3TermEntries t) (2*E+4) helem
  have hem := Nat.mul_le_mul_right (2*E+4) hlen
  have he' : (qmaClause3EncList qmaClause3EncInt (qmaClause3TermEntries t)).length ≤
      2049+2048*(2*E+4) := by omega
  simp only [qmaClause3EncTerm,List.length_append]
  omega

/-- A five-local encoding whose integer entries have natural absolute value at most `2^E`
satisfies the displayed total bit length bound. -/
theorem encoding_length_le (F : LhEncoding) (E : ℕ)
    (hloc : lhLocal 5 F)
    (hnum : ∀t∈F.terms,∀p q,(t.re p q).natAbs ≤ 2^E ∧ (t.im p q).natAbs ≤ 2^E) :
    (qmaClause3ToBits F).length ≤ 2*F.qubitCount+2*F.width+7+
      F.terms.length*(10*F.qubitCount+4096*E+10276) := by
  have hn := encNat_length_le_self F.qubitCount
  have hb := encNat_length_le_self F.width
  have ht : ∀t∈F.terms,(qmaClause3EncTerm t).length ≤ 10*F.qubitCount+4096*E+10275 := by
    intro t h
    exact encTerm_length_le t E (hloc t h) (hnum t h)
  have hs := encList_length_le qmaClause3EncTerm F.terms
    (10*F.qubitCount+4096*E+10275) ht
  simp only [qmaClause3ToBits,List.length_append]
  nlinarith

/-- The coefficient bound `(J + 2) * 2^(b + 1)` for penalty weight `J` and precision `b`. -/
def integerCap (J b : ℕ) : ℕ := (J+2)*2^(b+1)
/-- The natural output penalty weight `32 * (m + a + 1) + 1`. -/
def outputPenalty (m a : ℕ) : ℕ := 32*(m+a+1)+1

/-- The predicate that every real and imaginary integer entry lies between `-K` and `K`. -/
def SignedCap {N : ℕ} (K : ℕ) (t : IntegerLocalTerm N) : Prop :=
  ∀u v,-(K:ℤ) ≤ t.re u v ∧ t.re u v ≤ (K:ℤ) ∧
    -(K:ℤ) ≤ t.im u v ∧ t.im u v ≤ (K:ℤ)

/-- An integer between `-K` and `K` has natural absolute value at most `K`. -/
theorem natAbs_le_of_signed (z : ℤ) (K : ℕ) (hlo : -(K:ℤ) ≤ z) (hhi : z ≤ (K:ℤ)) :
    z.natAbs ≤ K := by
  rw [← Nat.cast_le (α:=ℤ),Int.natCast_natAbs]
  exact abs_le.mpr ⟨hlo,hhi⟩

/-- The coefficient cap `integerCap J b` is at most `2^(b + J + 3)`. -/
theorem integerCap_le_pow (J b : ℕ) : integerCap J b ≤ 2^(b+J+3) := by
  have hj : J+2 ≤ 2^(J+2) := (Nat.lt_two_pow_self).le
  calc
    integerCap J b=(J+2)*2^(b+1) := rfl
    _  ≤ 2^(J+2)*2^(b+1) := Nat.mul_le_mul_right _ hj
    _ =2^((J+2)+(b+1)) := (Nat.pow_add 2 (J+2) (b+1)).symm
    _ =2^(b+J+3) := by congr 1; omega

/-- Every propagation term satisfies the signed coefficient bound `integerCap J b`. -/
theorem propagationTerm_signedCap {m : ℕ} (n b J : ℕ) (i : Fin m) (g : FiniteGateCode) :
    SignedCap (integerCap J b) (propagationTerm n b i g) := by
  intro u v
  let p := flattenEquiv m n (fill (propSites n i g) u)
  let q := flattenEquiv m n (fill (propSites n i g) v)
  have h := propagationCoeff_bounds n b i g p q
  have hp : 0 ≤ (2:ℤ)^(b+1) := by positivity
  have hj : 0 ≤ (J:ℤ) := by positivity
  have hc : 2*(2:ℤ)^(b+1) ≤ (integerCap J b:ℤ) := by
    dsimp [integerCap]
    nlinarith
  change -(integerCap J b:ℤ) ≤ (propagationCoeff n b i g p q).1 ∧
    (propagationCoeff n b i g p q).1 ≤ (integerCap J b:ℤ) ∧
    -(integerCap J b:ℤ) ≤ (propagationCoeff n b i g p q).2 ∧
    (propagationCoeff n b i g p q).2 ≤ (integerCap J b:ℤ)
  rcases h with ⟨h₁,h₂,h₃,h₄⟩
  omega

/-- Every input or output boundary term satisfies the signed coefficient bound `integerCap J b`. -/
theorem boundaryTerm_signedCap (m n b J : ℕ) (last : Bool) (j : Fin n) :
    SignedCap (integerCap J b) (boundaryTerm m n b last j) := by
  intro u v
  have hp : 0 ≤ (2:ℤ)^(b+1) := by positivity
  have hj : 0 ≤ (J:ℤ) := by positivity
  have hc : (2:ℤ)^(b+1) ≤ (integerCap J b:ℤ) := by
    dsimp [integerCap]
    nlinarith
  dsimp only [boundaryTerm]
  unfold boundaryCoeff
  split_ifs <;> (try dsimp only) <;> omega

/-- A clock pair term of weight `J` satisfies the signed coefficient bound `integerCap J b`. -/
theorem clockPairTerm_signedCap (m n b J : ℕ) (i j : Fin m) :
    SignedCap (integerCap J b) (clockPairTerm m n b J i j) := by
  intro u v
  have hp : 0 ≤ (2:ℤ)^(b+1) := by positivity
  have hj : 0 ≤ (J:ℤ) := by positivity
  have hc : (J:ℤ)*(2:ℤ)^(b+1) ≤ (integerCap J b:ℤ) := by
    dsimp [integerCap]
    nlinarith
  have hpj : 0 ≤ (J:ℤ)*(2:ℤ)^(b+1) := mul_nonneg hj hp
  dsimp only [clockPairTerm]
  split_ifs <;> omega

/-- Every generated output term satisfies the signed coefficient bound with weight
`outputPenalty gs.length aux.card`. -/
theorem outputTerms_signedCap (n b : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    ∀t∈outputTerms n b gs aux out,
      SignedCap (integerCap (outputPenalty gs.length aux.card) b) t := by
  intro t ht
  simp only [outputTerms,List.mem_append,List.mem_map,List.mem_singleton,List.mem_flatMap] at ht
  rcases ht with ((⟨i,_,rfl⟩|⟨j,_,rfl⟩)|rfl)|⟨i,_,j,_,rfl⟩
  · exact propagationTerm_signedCap n b _ i (gs.get i)
  · exact boundaryTerm_signedCap gs.length n b _ false j
  · exact boundaryTerm_signedCap gs.length n b _ true out
  · exact clockPairTerm_signedCap gs.length n b _ i j

/-- All real and imaginary integer entries of generated output terms have natural absolute value
at most `2^(b + outputPenalty gs.length aux.card + 3)`. -/
theorem outputTerms_natAbsCap (n b : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    ∀t∈outputTerms n b gs aux out,∀u v,
      (t.re u v).natAbs ≤ 2^(b+outputPenalty gs.length aux.card+3) ∧
      (t.im u v).natAbs ≤ 2^(b+outputPenalty gs.length aux.card+3) := by
  intro t ht u v
  have h := outputTerms_signedCap n b gs aux out t ht u v
  have hc := integerCap_le_pow (outputPenalty gs.length aux.card) b
  exact ⟨(natAbs_le_of_signed _ _ h.1 h.2.1).trans hc,
    (natAbs_le_of_signed _ _ h.2.2.1 h.2.2.2).trans hc⟩

/-- All real and imaginary entries in the generated encoding have natural absolute value at most
`2^(b + outputPenalty gs.length aux.card + 3)`. -/
theorem actualEncoding_num_cap (n b : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    ∀t∈(actualEncoding n b gs aux out).terms,∀p q,
      (t.re p q).natAbs ≤ 2^(b+outputPenalty gs.length aux.card+3) ∧
      (t.im p q).natAbs ≤ 2^(b+outputPenalty gs.length aux.card+3) := by
  intro t ht
  change t∈(outputTerms n b gs aux out).map toLhTerm at ht
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
  intro p q
  exact outputTerms_natAbsCap n b gs aux out u hu
    (nativeIndexDecode u.support p) (nativeIndexDecode u.support q)

/-- The generated encoding satisfies the displayed bit length bound in the gate count, register
size, precision, and output penalty. -/
theorem actualEncoding_bitlength_general (n b : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    (qmaClause3ToBits (actualEncoding n b gs aux out)).length ≤
      2*(gs.length+n)+2*(b+1)+7+
      (gs.length+aux.card+1+gs.length^2)*
        (10*(gs.length+n)+4096*(b+outputPenalty gs.length aux.card+3)+10276) := by
  have h := encoding_length_le (actualEncoding n b gs aux out)
    (b+outputPenalty gs.length aux.card+3)
    (actualEncoding_local n b gs aux out) (actualEncoding_num_cap n b gs aux out)
  simpa only [actualEncoding,toLhEncoding,List.length_map,outputTerms_length] using h

/-- At precision `3 * (gs.length + n) + 64`, the generated encoding has bit length at most
`1200000 * (gs.length + n + 1)^3`. -/
theorem actualEncoding_bitlength_polynomial (n : ℕ) (gs : List FiniteGateCode)
    (aux : Finset (Fin n)) (out : Fin n) :
    (qmaClause3ToBits (actualEncoding n (3*(gs.length+n)+64) gs aux out)).length ≤
      1200000*(gs.length+n+1)^3 := by
  let N := gs.length+n
  let b := 3*N+64
  let J := outputPenalty gs.length aux.card
  let T := gs.length+aux.card+1+gs.length^2
  let D := 10*N+4096*(b+J+3)+10276
  have ha : aux.card ≤ n := by
    simpa only [Fintype.card_fin] using (Finset.card_le_univ aux)
  have hm : gs.length ≤ N := by dsimp [N]; omega
  have hJ : J ≤ 32*N+33 := by dsimp [J,outputPenalty,N]; omega
  have hD : D ≤ 600000*(N+1) := by dsimp [D,b]; omega
  have hT : T ≤ (N+1)^2 := by
    have hsq := Nat.mul_le_mul hm hm
    dsimp [T,N] at *
    nlinarith
  have hprefix : 2*N+2*(b+1)+7 ≤ 600000*(N+1) := by dsimp [b]; omega
  have hprod : T*D ≤ (N+1)^2*(600000*(N+1)) := Nat.mul_le_mul hT hD
  have hq : N+1 ≤ (N+1)^3 := by
    have h₁ := Nat.le_mul_self (N+1)
    have h₂ := Nat.mul_le_mul_left (N+1) h₁
    nlinarith
  have hbase := actualEncoding_bitlength_general n b gs aux out
  change (qmaClause3ToBits (actualEncoding n b gs aux out)).length ≤ 1200000*(N+1)^3
  have hbase' : (qmaClause3ToBits (actualEncoding n b gs aux out)).length ≤
      2*N+2*(b+1)+7+T*D := hbase
  nlinarith

end Qatlib.Papers.LocalHam06.MainResults
