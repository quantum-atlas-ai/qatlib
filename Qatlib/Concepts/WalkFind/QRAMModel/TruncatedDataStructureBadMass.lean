/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs
import Mathlib.Data.Finset.Sort

/-!
# Runtime and bad-mass estimates for collision data structures

This module proves runtime monotonicity, output-size bounds, and explicit bit-RAM reader and
writer specifications. It also bounds hash overflow events and trie sizes, tracks value
multiplicities, and expresses the norm of a slow-operation component through Johnson-walk type
masses.

The mathematical background is developed in [Ambainis2007ElementDistinctness].

## Main statements

* `dataHash_bucketOverflow_tail`: bounds the probability that a hash bucket contains at least
  `d` elements.
* `dataAddressValueTrie_node_count`: bounds the combined address and value trie size.
* `dataBad_bound_of_type_masses`: transfers uniform type-mass bounds to normalized
  superpositions.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.WalkFind.WalkSpectrum

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkFind.QRAMModel
open Qatlib.Concepts.WalkFind.UniqueCollision
open scoped Classical BigOperators

/-- Every bit-RAM step has bit cost at least one. -/
theorem ramStepBits_positive (A : BitRAMMachine) (q : RAMConfiguration) :
    1 ≤ ramStepBits A q := by
  unfold ramStepBits
  split <;> omega

/-- The accumulated bit cost of `n` RAM steps is at least `n`. -/
theorem ramRun_clock_ge_steps (A : BitRAMMachine) (q : RAMConfiguration) (n : ℕ) :
    n ≤ (ramRun A q n).2 := by
  induction n generalizing q with
  | zero => simp [ramRun]
  | succ n ih =>
    simpa only [ramRun, Nat.add_comm] using!
        Nat.add_le_add (ramStepBits_positive A q) (ih (ramStep A q))

/-- A RAM production specification remains valid when its clock bound is increased. -/
theorem ramProduces_mono (A : BitRAMMachine) (record input expected output : List Bool)
    {clock clock' : ℕ} (h : ramProduces A record input expected output clock)
    (hle : clock ≤ clock') : ramProduces A record input expected output clock' := by
  obtain ⟨steps, hh, hc, hm, ho⟩ := h
  exact ⟨steps, hh, hc.trans hle, hm, ho⟩

/-- The fast-operation predicate is preserved when its clock bound is increased. -/
theorem dataOperationsFast_mono {N M r : ℕ} (D : CollisionDataStructure N M r)
    (x : Fin N → ZMod M) (S : Finset (Fin N)) (h : Fin (2^D.seedBits))
    {clock clock' : ℕ} (hfast : dataOperationsFast D x S h clock)
    (hle : clock ≤ clock') : dataOperationsFast D x S h clock' := by
  intro i
  obtain ⟨hi, he, hl⟩ := hfast i
  exact ⟨fun hp => ramProduces_mono _ _ _ _ _ (hi hp) hle,
    fun hp => ramProduces_mono _ _ _ _ _ (he hp) hle,
    fun hp => ramProduces_mono _ _ _ _ _ (hl hp) hle⟩

/-- One RAM step increases the output length by at most one. -/
theorem ramStep_output_length (A : BitRAMMachine) (q : RAMConfiguration) :
    (ramStep A q).output.length ≤ q.output.length+1 := by
  unfold ramStep
  split
  all_goals try simp only [List.length_append, List.length_cons, List.length_nil]
  all_goals try omega
  all_goals split <;> simp only <;> omega

/-- After `n` RAM steps, the output length is at most its initial length plus `n`. -/
theorem ramRun_output_length (A : BitRAMMachine) (q : RAMConfiguration) (n : ℕ) :
    (ramRun A q n).1.output.length ≤ q.output.length+n := by
  induction n generalizing q with
  | zero => simp [ramRun]
  | succ n ih =>
    have hs := ramStep_output_length A q
    have hr := ih (ramStep A q)
    simpa only [ramRun] using! (show (ramRun A (ramStep A q) n).1.output.length ≤
      q.output.length+(n+1) by omega)

/-- A RAM production specification bounds the output length by the available clock. -/
theorem ramProduces_output_length_le_clock (A : BitRAMMachine)
    (record input expected output : List Bool) {clock : ℕ}
    (h : ramProduces A record input expected output clock) : output.length ≤ clock := by
  obtain ⟨steps, _, hc, _, ho⟩ := h
  have hs := ramRun_output_length A (ramInitial A record input) steps
  rw [ho] at hs
  simp only [ramInitial, List.length_nil, zero_add] at hs
  exact hs.trans ((ramRun_clock_ge_steps A _ steps).trans hc)

/-- The increase of output length times its successor is at most twice the bit cost of one RAM
step. -/
theorem ramStep_output_potential (A : BitRAMMachine) (q : RAMConfiguration) :
    (ramStep A q).output.length*((ramStep A q).output.length+1) ≤
      q.output.length*(q.output.length+1)+2*ramStepBits A q := by
  cases he : A.table[q.state]?.getD .halt
  all_goals simp only [ramStep, ramStepBits, he, List.length_append, List.length_cons, List.length_nil]
  all_goals try nlinarith
  all_goals split <;> nlinarith

/-- The output-length potential after a run is at most its initial value plus twice the
accumulated bit cost. -/
theorem ramRun_output_potential (A : BitRAMMachine) (q : RAMConfiguration) (n : ℕ) :
    (ramRun A q n).1.output.length*((ramRun A q n).1.output.length+1) ≤
      q.output.length*(q.output.length+1)+2*(ramRun A q n).2 := by
  induction n generalizing q with
  | zero => simp [ramRun]
  | succ n ih =>
    have hs := ramStep_output_potential A q
    have hr := ih (ramStep A q)
    simp only [ramRun]
    nlinarith

/-- Producing an output of length `L` requires a clock bound satisfying `L * (L + 1) ≤ 2 *
clock`. -/
theorem ramProduces_serialization_cost (A : BitRAMMachine)
    (record input expected output : List Bool) {clock : ℕ}
    (h : ramProduces A record input expected output clock) :
    output.length*(output.length+1) ≤ 2*clock := by
  obtain ⟨steps, _, hc, _, ho⟩ := h
  have hs := ramRun_output_potential A (ramInitial A record input) steps
  rw [ho] at hs
  simp only [ramInitial, List.length_nil, zero_mul, zero_add] at hs
  exact hs.trans (Nat.mul_le_mul_left 2 hc)

/-- The RAM machine with an empty program and initial program counter zero. -/
def haltedRAM : BitRAMMachine := ⟨[],0⟩

/-- Running `haltedRAM` preserves the configuration for every number of steps. -/
theorem haltedRAM_run (q : RAMConfiguration) (n : ℕ) :
    (ramRun haltedRAM q n).1 = q := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [ramRun, ramStep, haltedRAM] using! ih

/-- Every output produced by `haltedRAM` is empty. -/
theorem haltedRAM_output {record input expected output : List Bool} {clock : ℕ}
    (h : ramProduces haltedRAM record input expected output clock) : output = [] := by
  obtain ⟨steps, _, _, _, ho⟩ := h
  rw [haltedRAM_run] at ho
  exact ho.symm

/-- The RAM program that consumes address bits and writes the given Boolean value to the
selected memory cell. -/
def dataAddressWriter (value : Bool) : BitRAMMachine :=
  ⟨[.readInput 3 1 2, .pushAddress false 0, .pushAddress true 0,
    .writeMemory value 4, .halt], 0⟩

/-- The address writer appends the input bits to the address prefix and updates that memory
cell, with the stated step count and bit-cost bound. -/
theorem dataAddressWriter_run (value : Bool) (bits addrPrefix : List Bool)
    (memory : ℕ → Bool) (output : List Bool) :
    let q : RAMConfiguration := ⟨0,addrPrefix,memory,bits,output⟩
    let result := ramRun (dataAddressWriter value) q (2*bits.length+2)
    result.1 = ⟨4,addrPrefix++bits,Function.update memory (binaryAddress (addrPrefix++bits)) value,[],output⟩ ∧
      result.2 ≤ (bits.length+1)*(8+addrPrefix.length+bits.length) := by
  have hlog : Nat.clog 2 6 = 3 := by decide
  induction bits generalizing addrPrefix with
  | nil =>
    simp [ramRun, ramStep, ramStepBits, dataAddressWriter, hlog]
    omega
  | cons b bits ih =>
    (try dsimp only)
    have hn : 2*(b::bits).length+2 = (2*bits.length+2)+1+1 := by simp only [List.length_cons]; omega
    rw [hn, ramRun, ramRun]
    have h := ih (addrPrefix++[b])
    (try dsimp only at h)
    cases b <;> simp [ramStep, ramStepBits, dataAddressWriter, hlog]
    all_goals constructor
    all_goals first
      | simpa only [List.append_assoc, List.singleton_append] using! h.1
      | (have hc := h.2; simp only [List.length_append, List.length_cons, List.length_nil, dataAddressWriter] at hc; nlinarith)

/-- The RAM program that consumes address bits and appends the selected memory bit to the
output. -/
def dataAddressReader : BitRAMMachine :=
  ⟨[.readInput 3 1 2, .pushAddress false 0, .pushAddress true 0,
    .readMemory 4 5, .writeOutput false 6, .writeOutput true 6, .halt], 0⟩

/-- The address reader appends the addressed memory bit to the output, with the stated step
count and bit-cost bound. -/
theorem dataAddressReader_run (bits addrPrefix : List Bool)
    (memory : ℕ → Bool) (output : List Bool) :
    let q : RAMConfiguration := ⟨0,addrPrefix,memory,bits,output⟩
    let result := ramRun dataAddressReader q (2*bits.length+3)
    result.1 = ⟨6,addrPrefix++bits,memory,[],output++[memory (binaryAddress (addrPrefix++bits))]⟩ ∧
      result.2 ≤ (bits.length+1)*(8+addrPrefix.length+bits.length)+4+output.length := by
  have hlog : Nat.clog 2 8 = 3 := by decide
  induction bits generalizing addrPrefix with
  | nil =>
    (try dsimp only)
    cases hb : memory (binaryAddress addrPrefix) <;>
      simp [ramRun, ramStep, ramStepBits, dataAddressReader, hlog, hb] <;> omega
  | cons b bits ih =>
    (try dsimp only)
    have hn : 2*(b::bits).length+3 = (2*bits.length+3)+1+1 := by simp only [List.length_cons]; omega
    rw [hn, ramRun, ramRun]
    have h := ih (addrPrefix++[b])
    (try dsimp only at h)
    cases b <;> simp [ramStep, ramStepBits, dataAddressReader, hlog]
    all_goals constructor
    all_goals first
      | simpa only [List.append_assoc, List.singleton_append] using! h.1
      | (have hc := h.2; simp only [List.length_append, List.length_cons, List.length_nil, dataAddressReader] at hc; nlinarith)

/-- The address reader produces the record bit at the binary input address, defaulting to false,
within the specified clock bound. -/
theorem dataAddressReader_produces (record bits : List Bool) :
    ramProduces dataAddressReader record bits record
      [record[binaryAddress bits]?.getD false] ((bits.length+1)*(8+bits.length)+4) := by
  obtain ⟨hq,hclock⟩ := dataAddressReader_run bits [] (fun i => record[i]?.getD false) []
  simp only [List.nil_append, List.length_nil, Nat.add_zero] at hq hclock
  refine ⟨2*bits.length+3, ?_, hclock, ?_, ?_⟩
  · change (dataAddressReader.table[(ramRun dataAddressReader
      ⟨0,[],(fun i => record[i]?.getD false),bits,[]⟩ (2*bits.length+3)).1.state]?.getD .halt) = .halt
    rw [hq]
    rfl
  · intro i
    change (ramRun dataAddressReader ⟨0,[],(fun i => record[i]?.getD false),bits,[]⟩
      (2*bits.length+3)).1.memory i = record[i]?.getD false
    rw [hq]
  · change (ramRun dataAddressReader ⟨0,[],(fun i => record[i]?.getD false),bits,[]⟩
      (2*bits.length+3)).1.output = _
    rw [hq]

/-- For an address within the record, the address writer updates that record position and
produces empty output within the specified clock bound. -/
theorem dataAddressWriter_produces (value : Bool) (record bits : List Bool)
    (haddress : binaryAddress bits < record.length) :
    ramProduces (dataAddressWriter value) record bits (record.set (binaryAddress bits) value)
      [] ((bits.length+1)*(8+bits.length)) := by
  obtain ⟨hq,hclock⟩ := dataAddressWriter_run value bits [] (fun i => record[i]?.getD false) []
  simp only [List.nil_append, List.length_nil, Nat.add_zero] at hq hclock
  refine ⟨2*bits.length+2, ?_, hclock, ?_, ?_⟩
  · change ((dataAddressWriter value).table[(ramRun (dataAddressWriter value)
      ⟨0,[],(fun i => record[i]?.getD false),bits,[]⟩ (2*bits.length+2)).1.state]?.getD .halt) = .halt
    rw [hq]
    rfl
  · intro i
    change (ramRun (dataAddressWriter value) ⟨0,[],(fun i => record[i]?.getD false),bits,[]⟩
      (2*bits.length+2)).1.memory i = (record.set (binaryAddress bits) value)[i]?.getD false
    rw [hq]
    by_cases hi : i = binaryAddress bits
    · subst i
      simp [List.getElem?_set_self haddress]
    · simp [Function.update_of_ne hi, List.getElem?_set_ne (Ne.symm hi)]
  · change (ramRun (dataAddressWriter value) ⟨0,[],(fun i => record[i]?.getD false),bits,[]⟩
      (2*bits.length+2)).1.output = _
    rw [hq]

/-- A data structure with `haltedRAM` as its lookup machine cannot satisfy the fast-operation
predicate on a nonempty set. -/
theorem dataOperationsFast_not_halted_lookup {N M r : ℕ}
    (D : CollisionDataStructure N M r) (he : D.lookup = haltedRAM)
    (x : Fin N → ZMod M) (S : Finset (Fin N)) (h : Fin (2^D.seedBits)) (clock : ℕ)
    (hS : S.Nonempty) : ¬dataOperationsFast D x S h clock := by
  intro hf
  obtain ⟨i, hi⟩ := hS
  have hl := ((hf i).2.2) hi
  rw [he] at hl
  have ho := haltedRAM_output hl
  have hlen := congrArg List.length ho
  simp [natDescription] at hlen

/-- The probability of a finite union of seed events is at most the sum of their probabilities. -/
theorem dataEventProbability_union_bound {R : ℕ} {J : Type*} [Fintype J]
    (P : J → Fin R → Prop) :
    eventProbability (fun s => ∃ j, P j s) ≤ ∑ j, eventProbability (P j) := by
  classical
  have heq : (Finset.univ.filter (fun s : Fin R => ∃ j, P j s)) =
      Finset.univ.biUnion (fun j : J => Finset.univ.filter (P j)) := by
    ext s
    simp
  have hcNat : (Finset.univ.filter (fun s : Fin R => ∃ j, P j s)).card ≤
      ∑ j : J, (Finset.univ.filter (P j)).card := by
    rw [heq]
    exact Finset.card_biUnion_le
  have hc : ((Finset.univ.filter (fun s : Fin R => ∃ j, P j s)).card : ℝ) ≤
      ∑ j : J, ((Finset.univ.filter (P j)).card : ℝ) := by
    exact_mod_cast hcNat
  unfold eventProbability
  have hd := div_le_div_of_nonneg_right hc (Nat.cast_nonneg R)
  rw [Finset.sum_div] at hd
  convert! hd using 1
  congr 2
  congr 1
  ext s
  simp

/-- For a `d`-wise uniform binary hash, the probability that any of `L` injectively indexed
windows is entirely false is at most `L / 2^d`. -/
theorem dataHash_zero_windows_bound {N R d L : ℕ}
    (hash : Fin R → Fin N → Bool)
    (hind : ∀ i : Fin d → Fin N, Function.Injective i → ∀ values : Fin d → Bool,
      eventProbability (fun s => ∀ j, hash s (i j) = values j) = 1/(2^d : ℝ))
    (windows : Fin L → Fin d → Fin N) (hinj : ∀ a, Function.Injective (windows a)) :
    eventProbability (fun s => ∃ a, ∀ j, hash s (windows a j) = false) ≤
      (L : ℝ)/(2^d : ℝ) := by
  calc
    _ ≤ ∑ a : Fin L, eventProbability (fun s => ∀ j, hash s (windows a j) = false) :=
      dataEventProbability_union_bound _
    _ = _ := by
      simp_rw [hind _ (hinj _) (fun _ => false)]
      simp [div_eq_mul_inv]

/-- For a `d`-wise uniform hash into `Fin U`, the probability of an injective `d`-tuple with a
common hash value is at most `U * A^d / U^d`. -/
theorem dataHash_collisionWitness_tail {A U R d : ℕ} (hU : 0 < U)
    (hash : Fin R → Fin A → Fin U)
    (hind : ∀ i : Fin d → Fin A, Function.Injective i → ∀ values : Fin d → Fin U,
      eventProbability (fun s => ∀ j, hash s (i j) = values j) = 1/((U : ℝ)^d)) :
    eventProbability (fun s => ∃ (v : Fin U) (i : Fin d → Fin A),
      Function.Injective i ∧ ∀ j, hash s (i j) = v) ≤
        (U : ℝ)*(A : ℝ)^d/(U : ℝ)^d := by
  classical
  let P := fun p : Fin U × (Fin d → Fin A) => fun s : Fin R =>
    Function.Injective p.2 ∧ ∀ j, hash s (p.2 j) = p.1
  have heq : eventProbability (fun s => ∃ (v : Fin U) (i : Fin d → Fin A),
      Function.Injective i ∧ ∀ j, hash s (i j) = v) =
      eventProbability (fun s => ∃ p, P p s) := by
    unfold eventProbability
    congr 2
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, P]
    constructor
    · rintro ⟨v, i, hi, hh⟩
      exact ⟨(v,i),hi,hh⟩
    · rintro ⟨⟨v,i⟩,hi,hh⟩
      exact ⟨v,i,hi,hh⟩
  have hb : ∀ p : Fin U × (Fin d → Fin A), eventProbability (P p) ≤ 1/(U : ℝ)^d := by
    intro p
    by_cases hi : Function.Injective p.2
    · simpa only [P, hi, true_and] using! (hind p.2 hi (fun _ => p.1)).le
    · have hn : eventProbability (P p) = 0 := by simp [eventProbability, P, hi]
      rw [hn]
      positivity
  rw [heq]
  calc
    _ ≤ ∑ p : Fin U × (Fin d → Fin A), eventProbability (P p) := dataEventProbability_union_bound P
    _ ≤ ∑ _p : Fin U × (Fin d → Fin A), 1/(U : ℝ)^d := Finset.sum_le_sum (fun p _ => hb p)
    _ = _ := by simp [Fintype.card_prod, div_eq_mul_inv, mul_assoc]

/-- A hash bucket has at least `d` elements exactly when it contains an injectively indexed
`d`-tuple. -/
theorem dataHash_bucketOverflow_witness {A U R d : ℕ}
    (hash : Fin R → Fin A → Fin U) (s : Fin R) (v : Fin U) :
    d ≤ (Finset.univ.filter (fun a => hash s a = v)).card ↔
      ∃ i : Fin d → Fin A, Function.Injective i ∧ ∀ j, hash s (i j) = v := by
  classical
  let B := Finset.univ.filter (fun a : Fin A => hash s a = v)
  constructor
  · intro hc
    let i : Fin d → Fin A := fun j => B.orderEmbOfFin rfl (Fin.castLE hc j)
    refine ⟨i, ?_, ?_⟩
    · have hcast : Function.Injective (fun j : Fin d => Fin.castLE hc j) := by
        intro j j' hh
        apply Fin.ext
        exact congrArg (fun z : Fin B.card => z.val) hh
      exact (B.orderEmbOfFin rfl).injective.comp hcast
    · intro j
      have hm : i j ∈ B := Finset.orderEmbOfFin_mem B rfl _
      exact (Finset.mem_filter.mp hm).2
  · rintro ⟨i, hi, hv⟩
    have hsub : Finset.univ.image i ⊆ B := by
      intro a ha
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hv j
    have hc := Finset.card_le_card hsub
    simpa only [Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin, B] using!
        hc

/-- For a `d`-wise uniform hash, the probability that some bucket has at least `d` elements is
at most `U * A^d / U^d`. -/
theorem dataHash_bucketOverflow_tail {A U R d : ℕ} (hU : 0 < U)
    (hash : Fin R → Fin A → Fin U)
    (hind : ∀ i : Fin d → Fin A, Function.Injective i → ∀ values : Fin d → Fin U,
      eventProbability (fun s => ∀ j, hash s (i j) = values j) = 1/((U : ℝ)^d)) :
    eventProbability (fun s => ∃ v : Fin U,
      d ≤ (Finset.univ.filter (fun a => hash s a = v)).card) ≤
        (U : ℝ)*(A : ℝ)^d/(U : ℝ)^d := by
  have heq : eventProbability (fun s => ∃ v : Fin U,
      d ≤ (Finset.univ.filter (fun a => hash s a = v)).card) =
      eventProbability (fun s => ∃ (v : Fin U) (i : Fin d → Fin A),
        Function.Injective i ∧ ∀ j, hash s (i j) = v) := by
    unfold eventProbability
    congr 2
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, dataHash_bucketOverflow_witness]
  rw [heq]
  exact dataHash_collisionWitness_tail hU hash hind

/-- When `2 * A ≤ U`, the probability that some bucket has at least `d` elements is at most `U /
2^d` for a `d`-wise uniform hash. -/
theorem dataHash_bucketOverflow_doubled_tail {A U R d : ℕ} (hU : 0 < U)
    (hAU : 2*A ≤ U) (hash : Fin R → Fin A → Fin U)
    (hind : ∀ i : Fin d → Fin A, Function.Injective i → ∀ values : Fin d → Fin U,
      eventProbability (fun s => ∀ j, hash s (i j) = values j) = 1/((U : ℝ)^d)) :
    eventProbability (fun s => ∃ v : Fin U,
      d ≤ (Finset.univ.filter (fun a => hash s a = v)).card) ≤ (U : ℝ)/(2^d : ℝ) := by
  have hUR : 0 < (U : ℝ) := by exact_mod_cast hU
  have hratio : (A : ℝ)/(U : ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hUR).mpr
    have hAR : 2*(A : ℝ) ≤ U := by exact_mod_cast hAU
    linarith
  calc
    _ ≤ (U : ℝ)*(A : ℝ)^d/(U : ℝ)^d := dataHash_bucketOverflow_tail hU hash hind
    _ = (U : ℝ)*((A : ℝ)/(U : ℝ))^d := by rw [div_pow]; ring
    _ ≤ (U : ℝ)*(1/2 : ℝ)^d := by gcongr
    _ = _ := by rw [div_pow]; simp [div_eq_mul_inv]

/-- The natural-number key `2^(width - level) + n / 2^level` encoding a binary prefix at the
given level. -/
def dataPrefixKey (width level n : ℕ) : ℕ := 2^(width-level)+n/2^level

/-- For an in-range value and level, the prefix key lies in `[2^(width - level), 2^(width -
level + 1))`. -/
theorem dataPrefixKey_bounds (width level n : ℕ) (hl : level ≤ width) (hn : n < 2^width) :
    2^(width-level) ≤ dataPrefixKey width level n ∧
      dataPrefixKey width level n < 2^(width-level+1) := by
  have hp : 2^level * 2^(width-level) = 2^width := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hl]
  have hdiv : n/2^level < 2^(width-level) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    rw [Nat.mul_comm, hp]
    exact hn
  unfold dataPrefixKey
  constructor
  · exact Nat.le_add_right _ _
  · rw [Nat.pow_succ]
    omega

/-- Every prefix key for an in-range value and level is less than `2^(width + 1)`. -/
theorem dataPrefixKey_lt_keyspace (width level n : ℕ) (hl : level ≤ width) (hn : n < 2^width) :
    dataPrefixKey width level n < 2^(width+1) := by
  exact (dataPrefixKey_bounds width level n hl hn).2.trans_le
    (Nat.pow_le_pow_right (by omega) (by omega))

/-- The finite set of prefix keys obtained from all values and all levels from zero through
`width`. -/
def dataPrefixKeys (width : ℕ) (values : Finset ℕ) : Finset ℕ :=
  values.biUnion (fun n => (Finset.range (width+1)).image (fun level => dataPrefixKey width level n))

/-- The number of prefix keys is at most the number of values times `width + 1`. -/
theorem dataPrefixKeys_card (width : ℕ) (values : Finset ℕ) :
    (dataPrefixKeys width values).card ≤ values.card*(width+1) := by
  unfold dataPrefixKeys
  calc
    _ ≤ ∑ n ∈ values, ((Finset.range (width+1)).image (fun level => dataPrefixKey width level n)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _n ∈ values, (width+1) := Finset.sum_le_sum (fun n _ => by
      simpa only [Finset.card_range] using!
        (Finset.card_image_le (s:=Finset.range (width+1)) (f:=fun level => dataPrefixKey width level n)))
    _ = _ := by simp

/-- Inserting one value adds exactly the union with that value's prefix-key set. -/
theorem dataPrefixKeys_insert (width n : ℕ) (values : Finset ℕ) :
    dataPrefixKeys width (insert n values) = dataPrefixKeys width values ∪
      (Finset.range (width+1)).image (fun level => dataPrefixKey width level n) := by
  ext key
  simp [dataPrefixKeys, or_comm]

/-- The combined address and value prefix-key counts are at most `S.card * (dataBits N M + 1)`. -/
theorem dataAddressValueTrie_node_count {N M : ℕ} (S : Finset (Fin N)) (x : Fin N → ZMod M) :
    (dataPrefixKeys (Nat.clog 2 (N+1)) (S.image Fin.val)).card +
      (dataPrefixKeys (Nat.clog 2 (M+1)) (S.image (fun i => (x i).val))).card ≤
        S.card*(dataBits N M+1) := by
  have haddr := dataPrefixKeys_card (Nat.clog 2 (N+1)) (S.image Fin.val)
  have hvalue := dataPrefixKeys_card (Nat.clog 2 (M+1)) (S.image (fun i => (x i).val))
  have hca : (S.image Fin.val).card ≤ S.card := Finset.card_image_le
  have hcv : (S.image (fun i => (x i).val)).card ≤ S.card := Finset.card_image_le
  unfold dataBits
  nlinarith

/-- The number of indices in `S` whose input value equals `v`. -/
def dataValueMultiplicity {N M : ℕ} (x : Fin N → ZMod M) (S : Finset (Fin N))
    (v : ZMod M) : ℕ := (S.filter (fun i => x i = v)).card

/-- Inserting a new index increases the multiplicity of its value by one and preserves every
other multiplicity. -/
theorem dataValueMultiplicity_insert {N M : ℕ} (x : Fin N → ZMod M)
    (S : Finset (Fin N)) (i : Fin N) (hi : i ∉ S) (v : ZMod M) :
    dataValueMultiplicity x (insert i S) v = dataValueMultiplicity x S v +
      (if x i = v then 1 else 0) := by
  by_cases hv : x i = v
  · have hn : i ∉ S.filter (fun j => x j = v) := by simp [hi]
    simp [dataValueMultiplicity, Finset.filter_insert, hv, hn]
  · simp [dataValueMultiplicity, Finset.filter_insert, hv]

/-- Erasing a present index decreases the multiplicity of its value by one and preserves every
other multiplicity. -/
theorem dataValueMultiplicity_erase {N M : ℕ} (x : Fin N → ZMod M)
    (S : Finset (Fin N)) (i : Fin N) (hi : i ∈ S) (v : ZMod M) :
    dataValueMultiplicity x (S.erase i) v = dataValueMultiplicity x S v -
      (if x i = v then 1 else 0) := by
  by_cases hv : x i = v
  · have hm : i ∈ S.filter (fun j => x j = v) := by simp [hi, hv]
    simp [dataValueMultiplicity, Finset.filter_erase, hv, hm]
  · have hn : i ∉ S.filter (fun j => x j = v) := by simp [hv]
    simp [dataValueMultiplicity, Finset.filter_erase, hv, hn]

/-- A set contains a `k`-collision exactly when some value has multiplicity at least `k` in that
set. -/
theorem dataValueMultiplicity_collision_iff {N M : ℕ} (k : ℕ)
    (x : Fin N → ZMod M) (S : Finset (Fin N)) :
    (∃ J ⊆ S, IsCollision k x J) ↔ ∃ v : ZMod M, k ≤ dataValueMultiplicity x S v := by
  constructor
  · rintro ⟨J, hJS, hk, v, hv⟩
    refine ⟨v, ?_⟩
    rw [← hk]
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨hJS hi, hv i hi⟩
  · rintro ⟨v, hv⟩
    obtain ⟨J, hJS, hk⟩ := Finset.exists_subset_card_eq hv
    refine ⟨J, fun i hi => (Finset.mem_filter.mp (hJS hi)).1, hk, v, ?_⟩
    intro i hi
    exact (Finset.mem_filter.mp (hJS hi)).2

/-- For a single Johnson-walk type with a uniform seed, the slow-operation squared mass equals
the bad-state count divided by the type count and seed count. -/
theorem dataBad_type_count_identity {N M r : ℕ} (D : CollisionDataStructure N M r)
    (k : ℕ) (hkr : k ≤ r) (hkNr : k < N-r) (x : Fin N → ZMod M)
    (I : Finset (Fin N)) (i : Fin (2*k+1)) (clock : ℕ) :
    (∑ z : JRState N r × Fin (2^D.seedBits),
      ‖if dataOperationsFast D x z.1.val.1 z.2 clock then 0
        else jwPsiBigAt k N r I i z.1 *
          ((1/Real.sqrt (2^D.seedBits : ℝ) : ℝ) : ℂ)‖^2) =
      ((Finset.univ.filter (fun z : JRState N r × Fin (2^D.seedBits) =>
        jwTypeOf I z.1 = jwPsiCoord k i ∧
          ¬dataOperationsFast D x z.1.val.1 z.2 clock)).card : ℝ) /
        ((jwCnt k N r (jwPsiCoord k i).1 (jwPsiCoord k i).2 : ℝ) * (2^D.seedBits : ℝ)) := by
  have hc : 0 < (jwCnt k N r (jwPsiCoord k i).1 (jwPsiCoord k i).2 : ℝ) := by
    exact_mod_cast jwCnt_coord_pos k N r hkr hkNr i
  have hR : 0 < (2^D.seedBits : ℝ) := by positivity
  have he : ∀ z : JRState N r × Fin (2^D.seedBits),
      ‖if dataOperationsFast D x z.1.val.1 z.2 clock then 0
        else jwPsiBigAt k N r I i z.1 *
          ((1/Real.sqrt (2^D.seedBits : ℝ) : ℝ) : ℂ)‖^2 =
      if jwTypeOf I z.1 = jwPsiCoord k i ∧
        ¬dataOperationsFast D x z.1.val.1 z.2 clock then
        1/((jwCnt k N r (jwPsiCoord k i).1 (jwPsiCoord k i).2 : ℝ) * (2^D.seedBits : ℝ))
      else 0 := by
    intro z
    by_cases hf : dataOperationsFast D x z.1.val.1 z.2 clock
    · simp [hf]
    · by_cases ht : jwTypeOf I z.1 = jwPsiCoord k i
      · simp [hf, ht, jwPsiBigAt, jwPsiBig, Complex.norm_real, mul_pow,
          Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hc.le,
          Real.sq_sqrt hR.le]
        ring
      · simp [hf, ht, jwPsiBigAt, jwPsiBig]
  simp_rw [he]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  ring

/-- At each walk state, the squared norm of a type expansion is the sum of the squared
coefficient norms times the squared type amplitudes. -/
theorem typeExpansion_normSq_pointwise (k N r : ℕ) (I : Finset (Fin N))
    (a : Fin (2*k+1) → ℂ) (p : JRState N r) :
    ‖∑ i, a i * jwPsiBigAt k N r I i p‖^2 =
      ∑ i, ‖a i‖^2 * ‖jwPsiBigAt k N r I i p‖^2 := by
  by_cases hp : ∃ i : Fin (2*k+1), jwTypeOf I p = jwPsiCoord k i
  · obtain ⟨i, hi⟩ := hp
    have hzero : ∀ j : Fin (2*k+1), j ≠ i → jwPsiBigAt k N r I j p = 0 := by
      intro j hji
      have hj : jwTypeOf I p ≠ jwPsiCoord k j := by
        intro hj
        exact hji (jwPsiCoord_injective k (hj.symm.trans hi))
      simp [jwPsiBigAt, jwPsiBig, hj]
    rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
    · rw [norm_mul, mul_pow]
    · intro j _ hji
      simp [hzero j hji]
    · simp
    · intro j _ hji
      simp [hzero j hji]
    · simp
  · have hz : ∀ i : Fin (2*k+1), jwPsiBigAt k N r I i p = 0 := by
      intro i
      have hi : jwTypeOf I p ≠ jwPsiCoord k i := fun hi => hp ⟨i, hi⟩
      simp [jwPsiBigAt, jwPsiBig, hi]
    simp [hz]

/-- The squared norm of a slow-operation component is the weighted sum of its individual type
masses, with squared coefficient norms as weights. -/
theorem dataBad_type_mass_identity {N M r : ℕ} (D : CollisionDataStructure N M r)
    (k : ℕ) (x : Fin N → ZMod M) (I : Finset (Fin N))
    (a : Fin (2*k+1) → ℂ) (clock : ℕ) (scale : ℂ) :
    let bad := fun z : JRState N r × Fin (2^D.seedBits) =>
      if dataOperationsFast D x z.1.val.1 z.2 clock then 0
      else (∑ i, a i * jwPsiBigAt k N r I i z.1) * scale
    ‖toEuclidean_fromVec bad‖^2 =
      ∑ i, ‖a i‖^2 * ∑ z : JRState N r × Fin (2^D.seedBits),
        ‖if dataOperationsFast D x z.1.val.1 z.2 clock then 0
          else jwPsiBigAt k N r I i z.1 * scale‖^2 := by
  (try dsimp only)
  rw [norm_toEuclidean_fromVec_sq]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : dataOperationsFast D x z.1.val.1 z.2 clock
  · simp [hz]
  · simp only [hz, ↓reduceIte, norm_mul, mul_pow]
    rw [typeExpansion_normSq_pointwise, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- For normalized coefficients, bounds of `ε^2` on every bad type mass imply a bad-state norm
bound of `ε` when `ε` is nonnegative. -/
theorem dataBad_bound_of_type_masses {N M r : ℕ} (D : CollisionDataStructure N M r)
    (k : ℕ) (x : Fin N → ZMod M) (I : Finset (Fin N))
    (a : Fin (2*k+1) → ℂ) (ha : Normalized a) (clock : ℕ) (scale : ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hmass : ∀ i : Fin (2*k+1),
      (∑ z : JRState N r × Fin (2^D.seedBits),
        ‖if dataOperationsFast D x z.1.val.1 z.2 clock then 0
          else jwPsiBigAt k N r I i z.1 * scale‖^2) ≤ ε^2) :
    let bad := fun z : JRState N r × Fin (2^D.seedBits) =>
      if dataOperationsFast D x z.1.val.1 z.2 clock then 0
      else (∑ i, a i * jwPsiBigAt k N r I i z.1) * scale
    ‖toEuclidean_fromVec bad‖ ≤ ε := by
  (try dsimp only)
  have hsq := dataBad_type_mass_identity D k x I a clock scale
  (try dsimp only at hsq)
  have hsum : (∑ i, ‖a i‖^2 * ∑ z : JRState N r × Fin (2^D.seedBits),
      ‖if dataOperationsFast D x z.1.val.1 z.2 clock then 0
        else jwPsiBigAt k N r I i z.1 * scale‖^2) ≤ ε^2 := by
    calc
      _ ≤ ∑ i, ‖a i‖^2 * ε^2 := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hmass i) (sq_nonneg _))
      _ = ε^2 := by rw [← Finset.sum_mul, ha]; simp
  rw [← hsq] at hsum
  exact (sq_le_sq₀ (norm_nonneg _) hε).mp hsum

end Qatlib.Concepts.WalkFind.QRAMModel
