/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.QcmaDephasingVerifier

/-!
# Acceptance probabilities after witness dephasing

Copying a computational-basis witness into fresh ancillas removes its off-diagonal contributions
to the verifier acceptance functional. The module proves this directly from circuit matrices and
readout sums, using the standard dephasing mechanism described in [NielsenChuang2010].

`frontier1` gives the diagonal formula for arbitrary witness matrices. For density matrices it
transfers classical-witness soundness bounds to the dephased verifier, while preserving
classical-witness completeness, oracle counts, and uniform-family witness width.

## Main statements

* `acceptProb_dephase_classical`: preserve acceptance on each classical basis witness.
* `frontier1`: express acceptance using only diagonal witness entries.
* `dephase_soundness_bound`: transfer a classical-witness bound to arbitrary witness density
  matrices.
* `dephaseFamily`: lift dephasing to uniform witness families with polynomial resource bounds.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.LocalMachine.LocalTransport.QcmaDephasingAcceptProbability

open scoped Classical BigOperators
open scoped ComplexOrder
open Qatlib
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexity
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
open Qatlib
open Qatlib
open Qatlib.Concepts.LocalMachine.LocalTransport.UniformWitness
open Qatlib.Concepts.LocalMachine.LocalTransport.UniformWitness
open Qatlib
open Matrix

/-- Each witness-copy instruction is legal on the workspace of the dephased verifier. -/
theorem copyInstruction_legal (p : WitnessVerifierProgram) (i : Fin p.witnessBits) :
    instructionLegal (programQubits (dephaseProgram p)) (copyInstruction p i) := by
  have hq := dephase_qubits p
  have hw : p.witnessBits ≤ programQubits p := by simp only [programQubits]; omega
  have hc : (witnessWire p i : ℕ) < programQubits (dephaseProgram p) := by
    have h := (witnessWire p i).isLt
    simp only [witnessWire] at h
    omega
  have ht : programQubits p + (i : ℕ) < programQubits (dephaseProgram p) := by
    have h := i.isLt
    omega
  have hne : (witnessWire p i : ℕ) ≠ programQubits p + (i : ℕ) := by
    have h := (witnessWire p i).isLt
    simp only [witnessWire] at h
    omega
  show finiteCodeLegal (programQubits (dephaseProgram p))
      (FiniteGateCode.cx (witnessWire p i).val (programQubits p + (i : ℕ))) = true
  simp only [finiteCodeLegal, decide_eq_true_eq]
  exact ⟨hc, ht, hne⟩

/-- Every instruction in a partial witness-copy word is legal on the dephased verifier
workspace. -/
theorem copyInstrs_legal (p : WitnessVerifierProgram) :
    ∀ (m : ℕ) (hm : m ≤ p.witnessBits),
      ∀ i ∈ copyInstrs p m hm, instructionLegal (programQubits (dephaseProgram p)) i := by
  intro m
  induction m with
  | zero => intro _ i hi; simp only [copyInstrs, List.not_mem_nil] at hi
  | succ m ih =>
      intro hm i hi
      simp only [copyInstrs, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact copyInstruction_legal p ⟨m, hm⟩
      · exact ih (Nat.le_of_lt hm) i hi

/-- The full witness-copy word has one instruction per witness bit. -/
theorem copyInstructions_length (p : WitnessVerifierProgram) :
    (copyInstructions p).length = p.witnessBits := by
  have h : ∀ (m : ℕ) (hm : m ≤ p.witnessBits), (copyInstrs p m hm).length = m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
        intro hm
        simp only [copyInstrs, List.length_cons, ih (Nat.le_of_lt hm)]
  exact h p.witnessBits (Nat.le_refl p.witnessBits)

/-- Every instruction in a partial witness-copy word is a fixed gate instruction. -/
theorem copyInstrs_mem_fixed (p : WitnessVerifierProgram) :
    ∀ (m : ℕ) (hm : m ≤ p.witnessBits), ∀ i ∈ copyInstrs p m hm,
      ∃ gate : FiniteGateCode, i = WitnessInstruction.fixed gate := by
  intro m
  induction m with
  | zero => intro _ i hi; simp only [copyInstrs, List.not_mem_nil] at hi
  | succ m ih =>
      intro hm i hi
      simp only [copyInstrs, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact ⟨_, rfl⟩
      · exact ih (Nat.le_of_lt hm) i hi

/-- Filtering a list of fixed instructions gives the empty list when the filter returns `none`
on every fixed gate. -/
theorem list_filterMap_fixed_eq_nil {α : Type*} (l : List WitnessInstruction)
    (hl : ∀ i ∈ l, ∃ gate : FiniteGateCode, i = WitnessInstruction.fixed gate)
    (g : WitnessInstruction → Option α)
    (hg : ∀ gate : FiniteGateCode, g (WitnessInstruction.fixed gate) = none) :
    l.filterMap g = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      obtain ⟨gate, rfl⟩ := hl a (by simp)
      simp only [List.filterMap_cons, hg gate, ih (fun i hi => hl i (by simp [hi]))]

/-- A Boolean predicate true on every fixed gate is true on all entries of a list consisting of
fixed instructions. -/
theorem list_all_fixed (l : List WitnessInstruction)
    (hl : ∀ i ∈ l, ∃ gate : FiniteGateCode, i = WitnessInstruction.fixed gate)
    (f : WitnessInstruction → Bool)
    (hf : ∀ gate : FiniteGateCode, f (WitnessInstruction.fixed gate) = true) :
    l.all f = true := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      obtain ⟨gate, rfl⟩ := hl a (by simp)
      simp only [List.all_cons, hf gate, Bool.true_and,
        ih (fun i hi => hl i (by simp [hi]))]

/-- Dephasing preserves legality of a witness verifier program. -/
theorem dephaseProgram_legal (p : WitnessVerifierProgram)
    (hlegal : witnessProgramLegal p) : witnessProgramLegal (dephaseProgram p) := by
  have hq := dephase_qubits p
  have hout := hlegal.1
  refine ⟨?_, ?_⟩
  · show p.outputWire < programQubits (dephaseProgram p)
    omega
  · intro i hi
    rw [dephaseProgram_instructions, List.mem_append] at hi
    rcases hi with hi | hi
    · exact copyInstrs_legal p p.witnessBits (Nat.le_refl p.witnessBits) i hi
    · have horig := hlegal.2 i hi
      have hmono := instructionLegal_mono (q := programQubits p) (n := p.witnessBits) i horig
      rwa [hq.symm] at hmono

/-- Dephasing adds exactly one instruction per witness bit to the original instruction count. -/
theorem dephase_instruction_count (p : WitnessVerifierProgram) :
    (dephaseProgram p).instructions.length
      = p.witnessBits + p.instructions.length := by
  rw [dephaseProgram_instructions, List.length_append, copyInstructions_length]

/-- Dephasing preserves the number of oracle queries. -/
theorem dephase_oracleQueryCount (p : WitnessVerifierProgram) :
    oracleQueryCount (dephaseProgram p) = oracleQueryCount p := by
  simp only [oracleQueryCount, dephaseProgram_instructions, copyInstructions,
    List.filterMap_append]
  rw [list_filterMap_fixed_eq_nil (copyInstrs p p.witnessBits (Nat.le_refl p.witnessBits))
    (copyInstrs_mem_fixed p p.witnessBits (Nat.le_refl p.witnessBits)) _ (by intro gate; rfl)]
  simp

/-- Dephasing preserves the oracle address-bit ledger. -/
theorem dephase_addressBitLedger (p : WitnessVerifierProgram) :
    addressBitLedger (dephaseProgram p) = addressBitLedger p := by
  simp only [addressBitLedger, dephaseProgram_instructions, copyInstructions,
    List.filterMap_append]
  rw [list_filterMap_fixed_eq_nil (copyInstrs p p.witnessBits (Nat.le_refl p.witnessBits))
    (copyInstrs_mem_fixed p p.witnessBits (Nat.le_refl p.witnessBits)) _ (by intro gate; rfl)]
  simp

/-- The dephased program is oracle free if and only if the original program is oracle free. -/
theorem dephaseProgram_oracleFree {p : WitnessVerifierProgram} :
    oracleFree (dephaseProgram p) ↔ oracleFree p := by
  simp only [oracleFree, dephaseProgram_instructions, copyInstructions, List.all_append]
  rw [list_all_fixed (copyInstrs p p.witnessBits (Nat.le_refl p.witnessBits))
    (copyInstrs_mem_fixed p p.witnessBits (Nat.le_refl p.witnessBits)) _ (by intro gate; rfl)]
  simp

/-- The front coordinates of a glued register are the coordinates of its first component. -/
theorem wireGlue_front {q n : ℕ} (y : Reg q) (c : Reg n) (i : Fin q) :
    wireGlue y c (Fin.castAdd n i) = y i := by
  simp only [wireGlue, Fin.append_left]

/-- The back coordinates of a glued register are the coordinates of its second component. -/
theorem wireGlue_back {q n : ℕ} (y : Reg q) (c : Reg n) (j : Fin n) :
    wireGlue y c (Fin.natAdd q j) = c j := by
  simp only [wireGlue, Fin.append_right]

/-- The dephased input configuration is the original embedded input with zeroed copy ancillas,
transported by `toDephase`. -/
theorem embedConfig_toDephase (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (e : Reg p.witnessBits) :
    embedConfig (dephaseProgram p) x e
      = toDephase p (wireGlue (embedConfig p x e) (fun _ => false)) := by
  have hq := dephase_qubits p
  have hw : p.witnessBits ≤ programQubits p := by simp only [programQubits]; omega
  have hwidth : programQubits p = p.witnessBits + p.inputBits + p.ancillaBits := rfl
  have hembD : ∀ (k : Fin (programQubits (dephaseProgram p))),
      embedConfig (dephaseProgram p) x e k
        = if h : (k : ℕ) < p.witnessBits then e ⟨(k : ℕ), h⟩
          else if h2 : (k : ℕ) < p.witnessBits + p.inputBits then
            x ⟨(k : ℕ) - p.witnessBits, by omega⟩
          else false := fun k => rfl
  have hemb : ∀ (i : Fin (programQubits p)),
      embedConfig p x e i
        = if h : (i : ℕ) < p.witnessBits then e ⟨(i : ℕ), h⟩
          else if h2 : (i : ℕ) < p.witnessBits + p.inputBits then
            x ⟨(i : ℕ) - p.witnessBits, by omega⟩
          else false := fun i => rfl
  funext k
  have hshow : toDephase p (wireGlue (embedConfig p x e) (fun _ => false)) k
      = (wireGlue (embedConfig p x e) (fun _ => false)) (Fin.cast (dephase_qubits p) k) := rfl
  rw [hshow, hembD]
  rcases wire_cases (Fin.cast (dephase_qubits p) k) with ⟨i, hki⟩ | ⟨j, hkj⟩
  · rw [hki, wireGlue_front, hemb]
    have hk : (k : ℕ) = (i : ℕ) := by
      have hv := congrArg Fin.val hki
      simp only [Fin.val_castAdd] at hv
      exact hv
    by_cases hi : (i : ℕ) < p.witnessBits
    · have hk1 : (k : ℕ) < p.witnessBits := by omega
      rw [dif_pos hk1, dif_pos hi]
      exact congrArg e (Fin.ext hk)
    · have hk1 : ¬((k : ℕ) < p.witnessBits) := by omega
      rw [dif_neg hk1, dif_neg hi]
      by_cases hj : (i : ℕ) < p.witnessBits + p.inputBits
      · have hk2 : (k : ℕ) < p.witnessBits + p.inputBits := by omega
        rw [dif_pos hk2, dif_pos hj]
        exact congrArg x
          (Fin.ext (show (k : ℕ) - p.witnessBits = (i : ℕ) - p.witnessBits by omega))
      · have hk2 : ¬((k : ℕ) < p.witnessBits + p.inputBits) := by omega
        rw [dif_neg hk2, dif_neg hj]
  · have hk : (k : ℕ) = programQubits p + (j : ℕ) := by
      have hv := congrArg Fin.val hkj
      simp only [Fin.val_natAdd] at hv
      exact hv
    have hk1 : ¬((k : ℕ) < p.witnessBits) := by omega
    have hk2 : ¬((k : ℕ) < p.witnessBits + p.inputBits) := by omega
    rw [hkj, wireGlue_back, dif_neg hk1, dif_neg hk2]

/-- Copying the witness in an embedded dephased input places the witness bits in the appended
copy register. -/
theorem copyUpdate_embedConfig (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (e : Reg p.witnessBits) :
    copyUpdate p (embedConfig (dephaseProgram p) x e)
      = toDephase p (wireGlue (embedConfig p x e) e) := by
  rw [embedConfig_toDephase, copyUpdate_toDephase p (embedConfig p x e) (fun _ => false)]
  have hfun : (fun j : Fin p.witnessBits =>
      embedConfig p x e (witnessWire p j) ^^ (fun _ : Fin p.witnessBits => false) j) = e := by
    funext j
    simp only [Bool.xor_false]
    have hlt : (witnessWire p j : ℕ) < p.witnessBits := by
      simp only [witnessWire]
      omega
    have hdif : embedConfig p x e (witnessWire p j) = e ⟨(witnessWire p j : ℕ), hlt⟩ := by
      simp only [embedConfig]
      rw [dif_pos hlt]
    rw [hdif]
    exact congrArg e (Fin.ext rfl)
  rw [hfun]

/-- On coordinates belonging to the original workspace, `toDephase` of a glued register agrees
with its first component. -/
theorem toDephase_val_front (p : WitnessVerifierProgram)
    {k : Fin (programQubits (dephaseProgram p))}
    (hk : (k : ℕ) < programQubits p) (y : Reg (programQubits p)) (c : Reg p.witnessBits) :
    toDephase p (wireGlue y c) k = y ⟨(k : ℕ), hk⟩ := by
  show (wireGlue y c) (Fin.cast (dephase_qubits p) k) = y ⟨(k : ℕ), hk⟩
  rw [cast_eq_castAdd (dephase_qubits p) hk]
  exact wireGlue_front y c ⟨(k : ℕ), hk⟩

/-- For a legal verifier, summing over the dephased output event separates into a sum over the
original output event and all copy-register values. -/
theorem sum_programOutputEvent_dephase (p : WitnessVerifierProgram)
    (hlegal : witnessProgramLegal p) {M : Type*} [AddCommMonoid M]
    (g : Reg (programQubits (dephaseProgram p)) → M) :
    ∑ z ∈ programOutputEvent (dephaseProgram p), g z
      = ∑ y ∈ programOutputEvent p, ∑ c : Reg p.witnessBits,
          g (toDephase p (wireGlue y c)) := by
  classical
  have hq := dephase_qubits p
  have hout := hlegal.1
  have hout' : p.outputWire < programQubits (dephaseProgram p) := by omega
  have hE' : programOutputEvent (dephaseProgram p)
      = (Finset.univ : Finset (Reg (programQubits (dephaseProgram p)))).filter
          (fun z => z ⟨p.outputWire, hout'⟩ = true) := by
    show (if h : p.outputWire < programQubits (dephaseProgram p) then
        (Finset.univ : Finset (Reg (programQubits (dephaseProgram p)))).filter
          (fun z => z ⟨p.outputWire, h⟩ = true)
      else ∅) = _
    rw [dif_pos hout']
  have hE : programOutputEvent p
      = (Finset.univ : Finset (Reg (programQubits p))).filter
          (fun y => y ⟨p.outputWire, hout⟩ = true) := by
    simp only [programOutputEvent]
    rw [dif_pos hout]
  rw [hE', hE, Finset.sum_filter, Finset.sum_filter]
  have hphi : ∀ z : Reg (programQubits (dephaseProgram p)),
      toDephase p (wireGlue (wireTake (ofDephase p z)) (wireDrop (ofDephase p z))) = z := by
    intro z
    rw [wireTake_drop, toDephase_ofDephase]
  let E : Reg (programQubits (dephaseProgram p)) ≃ (Reg (programQubits p) × Reg p.witnessBits) :=
    { toFun := fun z => (wireTake (ofDephase p z), wireDrop (ofDephase p z))
      invFun := fun yc => toDephase p (wireGlue yc.1 yc.2)
      left_inv := hphi
      right_inv := fun yc => by
        simp only [ofDephase_toDephase, wireGlue_take, wireGlue_drop] }
  have hconv : ∑ z : Reg (programQubits (dephaseProgram p)),
      (if z ⟨p.outputWire, hout'⟩ = true then g z else 0)
      = ∑ yc : Reg (programQubits p) × Reg p.witnessBits,
          (if toDephase p (wireGlue yc.1 yc.2) ⟨p.outputWire, hout'⟩ = true
            then g (toDephase p (wireGlue yc.1 yc.2)) else 0) :=
    Fintype.sum_equiv E _ _ (fun z => by
      show (if z ⟨p.outputWire, hout'⟩ = true then g z else 0)
          = (if toDephase p (wireGlue (wireTake (ofDephase p z)) (wireDrop (ofDephase p z)))
                ⟨p.outputWire, hout'⟩ = true
              then g (toDephase p (wireGlue (wireTake (ofDephase p z))
                  (wireDrop (ofDephase p z))))
              else 0)
      rw [hphi z])
  rw [hconv, Fintype.sum_prod_type]
  have hval : ∀ (y : Reg (programQubits p)) (c : Reg p.witnessBits),
      toDephase p (wireGlue y c) ⟨p.outputWire, hout'⟩ = y ⟨p.outputWire, hout⟩ :=
    fun y c => toDephase_val_front p hout y c
  simp only [hval]
  have hpush : ∀ y : Reg (programQubits p),
      ∑ c : Reg p.witnessBits,
          (if y ⟨p.outputWire, hout⟩ = true
            then g (toDephase p (wireGlue y c)) else 0)
        = if y ⟨p.outputWire, hout⟩ = true
            then ∑ c : Reg p.witnessBits, g (toDephase p (wireGlue y c)) else 0 := by
    intro y
    by_cases hy : y ⟨p.outputWire, hout⟩ = true
    · have hL : ∑ c : Reg p.witnessBits,
          (if y ⟨p.outputWire, hout⟩ = true
            then g (toDephase p (wireGlue y c)) else 0)
        = ∑ c : Reg p.witnessBits, g (toDephase p (wireGlue y c)) :=
        Finset.sum_congr rfl (fun c _ => if_pos hy)
      rw [hL, if_pos hy]
    · have hL : ∑ c : Reg p.witnessBits,
          (if y ⟨p.outputWire, hout⟩ = true
            then g (toDephase p (wireGlue y c)) else 0) = 0 :=
        Finset.sum_eq_zero (fun c _ => if_neg hy)
      rw [hL, if_neg hy]
  rw [Finset.sum_congr rfl (fun y _ => hpush y), ← Finset.sum_filter]

/-- The readout matrix retaining the original verifier amplitude only when the appended copy
register equals the basis witness index. -/
noncomputable def dephaseReadout (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) :
    Matrix (Reg (programQubits (dephaseProgram p))) (Reg p.witnessBits) ℂ :=
  Matrix.of fun z e =>
    if wireDrop (ofDephase p z) = e
    then programMatrix A p (wireTake (ofDephase p z)) (embedConfig p x e)
    else 0

/-- In glued coordinates, the dephasing readout equals the original verifier amplitude when the
copy value equals the witness and is zero otherwise. -/
theorem dephaseReadout_apply (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (y : Reg (programQubits p)) (c e : Reg p.witnessBits) :
    dephaseReadout A p x (toDephase p (wireGlue y c)) e
      = if c = e then programMatrix A p y (embedConfig p x e) else 0 := by
  simp only [dephaseReadout, Matrix.of_apply, ofDephase_toDephase, wireGlue_drop,
    wireGlue_take]

/-- For a legal verifier, the dephased program matrix composed with witness embedding equals
`dephaseReadout`. -/
theorem programMatrix_mul_witnessEmbed_dephase (A : ClassicalOracle)
    (p : WitnessVerifierProgram) (hlegal : witnessProgramLegal p) (x : Reg p.inputBits) :
    programMatrix A (dephaseProgram p) * witnessEmbed (dephaseProgram p) x
      = dephaseReadout A p x := by
  have hz : ∀ z : Reg (programQubits (dephaseProgram p)),
      z = toDephase p (wireGlue (wireTake (ofDephase p z)) (wireDrop (ofDephase p z))) := by
    intro z
    rw [wireTake_drop, toDephase_ofDephase]
  ext z e₀
  obtain ⟨e, hee⟩ : ∃ e : Reg p.witnessBits, e = e₀ := ⟨e₀, rfl⟩
  subst hee
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (embedConfig (dephaseProgram p) x e)]
  · rw [witnessEmbed_apply, if_pos rfl, mul_one]
    rw [programMatrix_dephase_split, Matrix.mul_apply]
    have hpm0 : ∀ b : Reg (programQubits (dephaseProgram p)),
        permMatrix (copyUpdate p) b (embedConfig (dephaseProgram p) x e)
          = if b = copyUpdate p (embedConfig (dephaseProgram p) x e)
              then (1 : ℂ) else 0 := fun b => rfl
    rw [Finset.sum_eq_single (copyUpdate p (embedConfig (dephaseProgram p) x e))]
    · rw [hpm0 _, if_pos rfl, mul_one]
      rw [copyUpdate_embedConfig, hz z, dephaseOrigProd_entry A p hlegal
          (wireTake (ofDephase p z)) (embedConfig p x e) (wireDrop (ofDephase p z)) e]
      rw [dephaseReadout_apply A p x (wireTake (ofDephase p z))
          (wireDrop (ofDephase p z)) e]
    · intro b _ hb
      rw [hpm0 b, if_neg hb, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  · intro k _ hk
    rw [witnessEmbed_apply, if_neg hk, mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

/-- Acceptance on a classical basis witness is the sum of squared verifier amplitudes over the
output event. -/
theorem acceptProb_classical_eq (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (e : Reg p.witnessBits) :
    acceptProb A p x (classicalWitnessDensity e)
      = ∑ y ∈ programOutputEvent p,
          ‖programMatrix A p y (embedConfig p x e)‖ ^ 2 := by
  have h1 : classicalWitnessDensity e = pureWitnessDensity (Ket e) := rfl
  rw [h1, acceptProb_born A p x (Ket e), verifierInitialState_ket p x e]
  have hval : ∀ y : Reg (programQubits p),
      BornProb (programMatrix A p *ᵥ Ket (embedConfig p x e)) y
        = ‖programMatrix A p y (embedConfig p x e)‖ ^ 2 := by
    intro y
    have hket : ∀ v : Reg (programQubits p),
        (Ket (embedConfig p x e)) v = if v = embedConfig p x e then (1 : ℂ) else 0 :=
      fun v => rfl
    have hrow : (programMatrix A p *ᵥ Ket (embedConfig p x e)) y
        = programMatrix A p y (embedConfig p x e) := by
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single (embedConfig p x e)]
      · rw [hket, if_pos rfl, mul_one]
      · intro v _ hv
        rw [hket, if_neg hv, mul_zero]
      · intro hcon
        exact absurd (Finset.mem_univ _) hcon
    show ‖(programMatrix A p *ᵥ Ket (embedConfig p x e)) y‖ ^ 2
        = ‖programMatrix A p y (embedConfig p x e)‖ ^ 2
    rw [hrow]
  unfold MeasureProb programRun
  refine Finset.sum_congr rfl (fun y _ => ?_)
  exact hval y

/-- Rewrite evolution of an embedded matrix as conjugation by the product of the evolution and
embedding matrices. -/
private theorem matrix_assoc_push {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (M : Matrix ι ι ℂ) (S : Matrix ι κ ℂ) (ρ : Matrix κ κ ℂ) :
    M * (S * ρ * Sᴴ) * Mᴴ = M * S * ρ * (M * S)ᴴ := by
  have h1 : M * (S * ρ * Sᴴ) * Mᴴ = M * ((S * ρ * Sᴴ) * Mᴴ) :=
    Matrix.mul_assoc M _ Mᴴ
  have h2 : (S * ρ * Sᴴ) * Mᴴ = (S * ρ) * (Sᴴ * Mᴴ) :=
    Matrix.mul_assoc _ _ _
  have h3 : M * ((S * ρ) * (Sᴴ * Mᴴ)) = M * (S * (ρ * (Sᴴ * Mᴴ))) := by
    rw [Matrix.mul_assoc S ρ (Sᴴ * Mᴴ)]
  have h4 : M * (S * (ρ * (Sᴴ * Mᴴ))) = (M * S) * ρ * (Sᴴ * Mᴴ) := by
    rw [← Matrix.mul_assoc M S (ρ * (Sᴴ * Mᴴ)),
      ← Matrix.mul_assoc (M * S) ρ (Sᴴ * Mᴴ)]
  rw [h1, h2, h3, h4, Matrix.conjTranspose_mul]

/-- For a legal verifier, dephasing preserves acceptance probability on every classical basis
witness. -/
theorem acceptProb_dephase_classical (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (hlegal : witnessProgramLegal p) (x : Reg p.inputBits) (e : Reg p.witnessBits) :
    acceptProb A (dephaseProgram p) x (classicalWitnessDensity e)
      = acceptProb A p x (classicalWitnessDensity e) := by
  rw [acceptProb_classical_eq A (dephaseProgram p) x e, acceptProb_classical_eq A p x e]
  rw [sum_programOutputEvent_dephase p hlegal
    (fun z => ‖programMatrix A (dephaseProgram p) z (embedConfig (dephaseProgram p) x e)‖ ^ 2)]
  have hval : ∀ (y : Reg (programQubits p)) (c : Reg p.witnessBits),
      programMatrix A (dephaseProgram p) (toDephase p (wireGlue y c))
          (embedConfig (dephaseProgram p) x e)
        = if c = e then programMatrix A p y (embedConfig p x e) else 0 := by
    intro y c
    rw [programMatrix_dephase_split, Matrix.mul_apply]
    have hpm0 : ∀ b : Reg (programQubits (dephaseProgram p)),
        permMatrix (copyUpdate p) b (embedConfig (dephaseProgram p) x e)
          = if b = copyUpdate p (embedConfig (dephaseProgram p) x e)
              then (1 : ℂ) else 0 := fun b => rfl
    rw [Finset.sum_eq_single (copyUpdate p (embedConfig (dephaseProgram p) x e))]
    · rw [hpm0 _, if_pos rfl, mul_one, copyUpdate_embedConfig]
      rw [dephaseOrigProd_entry A p hlegal y (embedConfig p x e) c e]
    · intro b _ hb
      rw [hpm0 b, if_neg hb, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  refine Finset.sum_congr rfl (fun y _ => ?_)
  simp only [hval y]
  rw [Finset.sum_eq_single e]
  · rw [if_pos rfl]
  · intro c _ hc
    rw [if_neg hc]
    simp
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

/-- The real part of `z * c * conj z` equals the real part of `c` times the squared norm of `z`. -/
private theorem re_mul_conj_mul_self (z c : ℂ) :
    (z * c * (starRingEnd ℂ) z).re = c.re * ‖z‖ ^ 2 := by
  have h1 : z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [show z * c * (starRingEnd ℂ) z = c * (z * (starRingEnd ℂ) z) from by ring, h1]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The dephased legal verifier satisfies the classical acceptance functional identity. -/
theorem dephase_classicalAcceptFunctional (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (hlegal : witnessProgramLegal p) (x : Reg p.inputBits) :
    WcClassicalAcceptFunctional A (dephaseProgram p) x := by
  intro σ₀
  obtain ⟨σ, hσσ⟩ : ∃ σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ,
      σ = σ₀ := ⟨σ₀, rfl⟩
  subst hσσ
  have key := programMatrix_mul_witnessEmbed_dephase A p hlegal x
  conv_lhs => unfold acceptProb
  rw [verifierInputDensity_eq_mul (dephaseProgram p) x σ, matrix_assoc_push, key]
  rw [sum_programOutputEvent_dephase p hlegal]
  have hentry : ∀ (y : Reg (programQubits p)) (c : Reg p.witnessBits),
      ((dephaseReadout A p x * σ * (dephaseReadout A p x)ᴴ)
          (toDephase p (wireGlue y c)) (toDephase p (wireGlue y c)))
        = programMatrix A p y (embedConfig p x c) * σ c c
            * (starRingEnd ℂ) (programMatrix A p y (embedConfig p x c)) := by
    intro y c
    have hR : ∀ v : Reg p.witnessBits, dephaseReadout A p x (toDephase p (wireGlue y c)) v
        = if c = v then programMatrix A p y (embedConfig p x v) else 0 :=
      dephaseReadout_apply A p x y c
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Finset.sum_eq_single c]
    · rw [Finset.sum_eq_single c]
      · rw [hR c, if_pos (rfl : c = c)]
        rfl
      · intro v _ hv
        rw [hR v, if_neg (Ne.symm hv), zero_mul]
      · intro hcon
        exact absurd (Finset.mem_univ _) hcon
    · intro v _ hv
      rw [hR v, if_neg (Ne.symm hv), star_zero, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  have hgoal : ∑ y ∈ programOutputEvent p, ∑ c : Reg p.witnessBits,
      ((dephaseReadout A p x * σ * (dephaseReadout A p x)ᴴ)
        (toDephase p (wireGlue y c)) (toDephase p (wireGlue y c))).re
    = ∑ w : Reg p.witnessBits,
        (σ w w).re * acceptProb A (dephaseProgram p) x (classicalWitnessDensity w) := by
    have hre : ∀ (y : Reg (programQubits p)) (c : Reg p.witnessBits),
        (programMatrix A p y (embedConfig p x c) * σ c c
            * (starRingEnd ℂ) (programMatrix A p y (embedConfig p x c))).re
          = (σ c c).re * ‖programMatrix A p y (embedConfig p x c)‖ ^ 2 :=
      fun y c => re_mul_conj_mul_self _ _
    have hsum : ∑ y ∈ programOutputEvent p, ∑ c : Reg p.witnessBits,
        ((dephaseReadout A p x * σ * (dephaseReadout A p x)ᴴ)
          (toDephase p (wireGlue y c)) (toDephase p (wireGlue y c))).re
      = ∑ c : Reg p.witnessBits,
          (σ c c).re * ∑ y ∈ programOutputEvent p,
            ‖programMatrix A p y (embedConfig p x c)‖ ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun y _ => by rw [hentry y c, hre y c])
    rw [hsum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [acceptProb_dephase_classical A p hlegal x w, acceptProb_classical_eq A p x w]
  exact hgoal

/-- For any witness matrix, acceptance by the dephased legal verifier is the sum of the real
diagonal entries times the original classical-witness acceptance probabilities. -/
theorem frontier1 (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (hlegal : witnessProgramLegal p) (x : Reg p.inputBits)
    (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ) :
    acceptProb A (dephaseProgram p) x σ
      = ∑ e : Reg p.witnessBits,
          (σ e e).re * acceptProb A p x (classicalWitnessDensity e) := by
  rw [(dephase_classicalAcceptFunctional A p hlegal x) σ]
  exact Finset.sum_congr rfl (fun e _ => by
    rw [acceptProb_dephase_classical A p hlegal x e])

/-- A uniform upper bound on acceptance for all classical witnesses bounds acceptance of every
witness density matrix after dephasing. -/
theorem dephase_soundness_bound (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (hlegal : witnessProgramLegal p) (x : Reg p.inputBits) {b : ℝ}
    (hsound : ∀ e : Reg p.witnessBits,
      acceptProb A p x (classicalWitnessDensity e) ≤ b)
    {σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ}
    (hσ : IsWitnessDensity σ) :
    acceptProb A (dephaseProgram p) x σ ≤ b := by
  have hpsd : ∀ e : Reg p.witnessBits, 0 ≤ σ e e := fun e => hσ.2.1.diag_nonneg (i := e)
  have hnonneg : ∀ e : Reg p.witnessBits, 0 ≤ (σ e e).re :=
    fun e => (Complex.nonneg_iff.mp (hpsd e)).1
  have hdiag_sum : (∑ e : Reg p.witnessBits, (σ e e).re) ≤ 1 := by
    have htr : Matrix.trace σ = ∑ e : Reg p.witnessBits, σ e e := by
      simp [Matrix.trace, Matrix.diag_apply]
    have htrle := Complex.le_def.mp hσ.2.2
    have hre_sum : (∑ e : Reg p.witnessBits, (σ e e).re) = (Matrix.trace σ).re := by
      rw [htr, Complex.re_sum]
    rw [hre_sum]
    simpa using htrle.1
  by_cases hb : 0 ≤ b
  · rw [frontier1 A p hlegal x σ]
    have hterm : ∀ e : Reg p.witnessBits,
        (σ e e).re * acceptProb A p x (classicalWitnessDensity e)
          ≤ (σ e e).re * b := fun e => mul_le_mul_of_nonneg_left (hsound e) (hnonneg e)
    calc ∑ e : Reg p.witnessBits, (σ e e).re * acceptProb A p x (classicalWitnessDensity e)
        ≤ ∑ e : Reg p.witnessBits, (σ e e).re * b :=
          Finset.sum_le_sum fun e _ => hterm e
      _ = (∑ e : Reg p.witnessBits, (σ e e).re) * b := by rw [Finset.sum_mul]
      _ ≤ 1 * b := mul_le_mul_of_nonneg_right hdiag_sum hb
      _ = b := by ring
  · exfalso
    have hnn := acceptProb_nonneg A p x (classicalWitnessDensity (fun _ => false))
      (classicalWitnessDensity_isWitnessDensity (fun _ => false))
    have hsb := hsound (fun _ => false)
    exact absurd (hnn.trans hsb) hb

/-- If every classical witness has acceptance probability at most `1 / 3`, every witness density
matrix has acceptance probability at most `1 / 3` after dephasing. -/
theorem dephase_soundness_third (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (hlegal : witnessProgramLegal p) (x : Reg p.inputBits)
    (hsound : ∀ e : Reg p.witnessBits,
      acceptProb A p x (classicalWitnessDensity e) ≤ 1 / 3)
    {σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ}
    (hσ : IsWitnessDensity σ) :
    acceptProb A (dephaseProgram p) x σ ≤ 1 / 3 :=
  dephase_soundness_bound A p hlegal x hsound hσ

/-- Any acceptance lower bound for a classical witness remains valid for that witness in the
dephased verifier. -/
theorem dephase_completeness_preserved (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (hlegal : witnessProgramLegal p) (x : Reg p.inputBits) (e : Reg p.witnessBits)
    {t : ℝ} (hacc : t ≤ acceptProb A p x (classicalWitnessDensity e)) :
    t ≤ acceptProb A (dephaseProgram p) x (classicalWitnessDensity e) :=
  hacc.trans (acceptProb_dephase_classical A p hlegal x e).symm.le

/-- The dephased program bit ledger is `(witnessBits + instructions.length) * (4 + 2 *
(programQubits p + witnessBits))`. -/
theorem programBitLedger_dephase (p : WitnessVerifierProgram) :
    programBitLedger (dephaseProgram p)
      = (p.witnessBits + p.instructions.length)
          * (4 + 2 * (programQubits p + p.witnessBits)) := by
  rw [programBitLedger_eq, dephase_instruction_count, dephase_qubits]

/-- Apply program dephasing to a uniform witness family, preserving witness width and supplying
updated polynomial gate, space, and bit-ledger bounds. -/
def dephaseFamily (f : UniformWitnessFamily) : UniformWitnessFamily where
  witnessWidth := f.witnessWidth
  generator := fun x => dephaseProgram (f.generator x)
  gateCoefficient := f.gateCoefficient + f.spaceCoefficient
  gateDegree := max f.gateDegree f.spaceDegree
  bitCoefficient := (f.gateCoefficient + f.spaceCoefficient) * (4 + 4 * f.spaceCoefficient)
  bitDegree := max f.gateDegree f.spaceDegree + f.spaceDegree
  spaceCoefficient := 2 * f.spaceCoefficient
  spaceDegree := f.spaceDegree
  generatorWidths := by
    intro x
    exact ⟨(f.generatorWidths x).1, (f.generatorWidths x).2⟩
  generatorLegal := fun x => dephaseProgram_legal _ (f.generatorLegal x)
  generatorGateBound := by
    intro x
    have hw : (f.generator x).witnessBits ≤ programQubits (f.generator x) := by
      simp only [programQubits]
      omega
    have hspace := f.generatorSpaceBound x
    have hgate := f.generatorGateBound x
    simp only [witnessPolynomialBound] at hspace hgate ⊢
    have hN : 1 ≤ x.length + 1 := by omega
    have hdeg1 : (x.length + 1) ^ f.gateDegree
        ≤ (x.length + 1) ^ max f.gateDegree f.spaceDegree :=
      Nat.pow_le_pow_right hN (Nat.le_max_left _ _)
    have hdeg2 : (x.length + 1) ^ f.spaceDegree
        ≤ (x.length + 1) ^ max f.gateDegree f.spaceDegree :=
      Nat.pow_le_pow_right hN (Nat.le_max_right _ _)
    have h1 : (f.generator x).witnessBits
        ≤ f.spaceCoefficient * (x.length + 1) ^ max f.gateDegree f.spaceDegree := by
      calc (f.generator x).witnessBits ≤ programQubits (f.generator x) := hw
        _ ≤ f.spaceCoefficient * (x.length + 1) ^ f.spaceDegree := hspace
        _ ≤ f.spaceCoefficient * (x.length + 1) ^ max f.gateDegree f.spaceDegree :=
          Nat.mul_le_mul_left _ hdeg2
    have h2 : (f.generator x).instructions.length
        ≤ f.gateCoefficient * (x.length + 1) ^ max f.gateDegree f.spaceDegree :=
      le_trans hgate (Nat.mul_le_mul_left _ hdeg1)
    rw [dephase_instruction_count]
    calc (f.generator x).witnessBits + (f.generator x).instructions.length
        ≤ f.spaceCoefficient * (x.length + 1) ^ max f.gateDegree f.spaceDegree
            + f.gateCoefficient * (x.length + 1) ^ max f.gateDegree f.spaceDegree :=
          add_le_add h1 h2
      _ = (f.gateCoefficient + f.spaceCoefficient)
            * (x.length + 1) ^ max f.gateDegree f.spaceDegree := by ring
  generatorSpaceBound := by
    intro x
    have hq := dephase_qubits (f.generator x)
    have hw : (f.generator x).witnessBits ≤ programQubits (f.generator x) := by
      simp only [programQubits]
      omega
    have hspace := f.generatorSpaceBound x
    simp only [witnessPolynomialBound] at hspace ⊢
    rw [hq]
    calc programQubits (f.generator x) + (f.generator x).witnessBits
        ≤ f.spaceCoefficient * (x.length + 1) ^ f.spaceDegree
            + (f.generator x).witnessBits := add_le_add hspace le_rfl
      _ ≤ f.spaceCoefficient * (x.length + 1) ^ f.spaceDegree
            + f.spaceCoefficient * (x.length + 1) ^ f.spaceDegree :=
          add_le_add le_rfl (le_trans hw hspace)
      _ = 2 * f.spaceCoefficient * (x.length + 1) ^ f.spaceDegree := by ring
  generatorBitBound := by
    intro x
    have hw : (f.generator x).witnessBits ≤ programQubits (f.generator x) := by
      simp only [programQubits]
      omega
    have hspace := f.generatorSpaceBound x
    have hgate := f.generatorGateBound x
    simp only [witnessPolynomialBound] at hspace hgate ⊢
    have hN : 1 ≤ x.length + 1 := by omega
    have hdeg1 : (x.length + 1) ^ f.gateDegree
        ≤ (x.length + 1) ^ max f.gateDegree f.spaceDegree :=
      Nat.pow_le_pow_right hN (Nat.le_max_left _ _)
    have hdeg2 : (x.length + 1) ^ f.spaceDegree
        ≤ (x.length + 1) ^ max f.gateDegree f.spaceDegree :=
      Nat.pow_le_pow_right hN (Nat.le_max_right _ _)
    have hNpos : 1 ≤ (x.length + 1) ^ f.spaceDegree :=
      Nat.one_le_pow _ _ (by omega)
    have hw' : (f.generator x).witnessBits
        ≤ f.spaceCoefficient * (x.length + 1) ^ f.spaceDegree := le_trans hw hspace
    have hlen : (f.generator x).instructions.length
        ≤ f.gateCoefficient * (x.length + 1) ^ max f.gateDegree f.spaceDegree :=
      le_trans hgate (Nat.mul_le_mul_left _ hdeg1)
    have hsum : (f.generator x).witnessBits + (f.generator x).instructions.length
        ≤ (f.gateCoefficient + f.spaceCoefficient)
            * (x.length + 1) ^ max f.gateDegree f.spaceDegree := by
      calc (f.generator x).witnessBits + (f.generator x).instructions.length
          ≤ f.spaceCoefficient * (x.length + 1) ^ f.spaceDegree
              + f.gateCoefficient * (x.length + 1) ^ max f.gateDegree f.spaceDegree :=
            add_le_add hw' hlen
        _ ≤ f.spaceCoefficient * (x.length + 1) ^ max f.gateDegree f.spaceDegree
              + f.gateCoefficient * (x.length + 1) ^ max f.gateDegree f.spaceDegree :=
            add_le_add (Nat.mul_le_mul_left _ hdeg2) le_rfl
        _ = (f.gateCoefficient + f.spaceCoefficient)
              * (x.length + 1) ^ max f.gateDegree f.spaceDegree := by ring
    have hfactor : 4 + 2 * (programQubits (f.generator x) + (f.generator x).witnessBits)
        ≤ (4 + 4 * f.spaceCoefficient) * (x.length + 1) ^ f.spaceDegree := by
      have hT1 : 1 ≤ (x.length + 1) ^ f.spaceDegree := hNpos
      have hA : 4 ≤ 4 * ((x.length + 1) ^ f.spaceDegree) :=
        Nat.le_mul_of_pos_right 4 (by omega)
      have hB : 2 * (programQubits (f.generator x) + (f.generator x).witnessBits)
          ≤ 4 * f.spaceCoefficient * ((x.length + 1) ^ f.spaceDegree) := by
        calc 2 * (programQubits (f.generator x) + (f.generator x).witnessBits)
            ≤ 2 * (2 * (f.spaceCoefficient * (x.length + 1) ^ f.spaceDegree)) := by omega
          _ = 4 * f.spaceCoefficient * (x.length + 1) ^ f.spaceDegree := by ring
      have hC : 4 * ((x.length + 1) ^ f.spaceDegree)
          + 4 * f.spaceCoefficient * ((x.length + 1) ^ f.spaceDegree)
          = (4 + 4 * f.spaceCoefficient) * ((x.length + 1) ^ f.spaceDegree) := by ring
      calc 4 + 2 * (programQubits (f.generator x) + (f.generator x).witnessBits)
          ≤ 4 * ((x.length + 1) ^ f.spaceDegree)
              + 4 * f.spaceCoefficient * ((x.length + 1) ^ f.spaceDegree) :=
            add_le_add hA hB
        _ = (4 + 4 * f.spaceCoefficient) * ((x.length + 1) ^ f.spaceDegree) := hC
    rw [programBitLedger_dephase]
    calc ((f.generator x).witnessBits + (f.generator x).instructions.length)
          * (4 + 2 * (programQubits (f.generator x) + (f.generator x).witnessBits))
        ≤ ((f.gateCoefficient + f.spaceCoefficient)
              * (x.length + 1) ^ max f.gateDegree f.spaceDegree)
            * ((4 + 4 * f.spaceCoefficient) * (x.length + 1) ^ f.spaceDegree) :=
          Nat.mul_le_mul hsum hfactor
      _ = ((f.gateCoefficient + f.spaceCoefficient) * (4 + 4 * f.spaceCoefficient))
            * (x.length + 1) ^ (max f.gateDegree f.spaceDegree + f.spaceDegree) := by
          rw [Nat.pow_add]
          ring

/-- The generator of the dephased family returns the dephased program generated by the original
family. -/
theorem dephaseFamily_generator (f : UniformWitnessFamily) (x : List Bool) :
    (dephaseFamily f).generator x = dephaseProgram (f.generator x) := rfl

/-- Dephasing a uniform witness family preserves its witness-width function. -/
theorem dephaseFamily_width (f : UniformWitnessFamily) (n : ℕ) :
    (dephaseFamily f).witnessWidth n = f.witnessWidth n := rfl

/-- Dephasing preserves oracle freeness of a uniform witness family. -/
theorem dephaseFamily_oracleFree (f : UniformWitnessFamily)
    (h : f.OracleFree) : (dephaseFamily f).OracleFree := by
  intro x
  rw [dephaseFamily_generator, dephaseProgram_oracleFree]
  exact h x

end Qatlib.Concepts.LocalMachine.LocalTransport.QcmaDephasingAcceptProbability
