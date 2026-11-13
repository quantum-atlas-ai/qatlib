/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.WalkAccessConstructionDefs

/-!
# Finite circuit laws for lazy matching access

This module proves execution and register identities for the CNOT blocks used in lazy matching
access. It connects finite gate codes with their matrices, evaluates legal words on basis
states, and computes the setup, update, and check word lengths.

The register lemmas describe concatenation and zero padding, while `cnotFold_target_val`
isolates the XOR update at a uniquely targeted coordinate. These access constructions support
the quantum walk framework of [Szegedy2004].

## Main statements

* `run_cnot_block_code`: Basis state execution of a CNOT block encoded by finite gate codes.
* `finiteWordRun_of_legal`: Successful execution of legal finite words.
* `lazy_word_lengths`: Exact lengths of the lazy matching access words.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false

open Matrix
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib
open scoped Classical BigOperators

universe u v

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

/-- Membership in `highCnotPairs m` is equivalent to having control `i` and target `m + i` for
some `i < m - 1`. -/
lemma mem_highCnotPairs {m : ℕ} (p : Fin (m + m) × Fin (m + m)) :
    p ∈ highCnotPairs m ↔ ∃ i : Fin (m - 1), p.1.val = i.val ∧ p.2.val = m + i.val := by
  constructor
  · intro hp
    obtain ⟨i, he⟩ := List.mem_ofFn.mp hp
    have h1 : p.1.val = i.val := by
      have hh := congrArg (fun q : Fin (m + m) × Fin (m + m) => q.1.val) he
      simpa using! hh.symm
    have h2 : p.2.val = m + i.val := by
      have hh := congrArg (fun q : Fin (m + m) × Fin (m + m) => q.2.val) he
      simpa using! hh.symm
    exact ⟨⟨i.val, by omega⟩, h1, h2⟩
  · rintro ⟨i, h1, h2⟩
    refine List.mem_ofFn.mpr ⟨i, ?_⟩
    apply Prod.ext
    · apply Fin.ext; exact h1.symm
    · apply Fin.ext; exact h2.symm

/-- The list of CNOT control-target pairs used in lazy matching has no duplicates. -/
lemma highCnotPairs_nodup (m : ℕ) : (highCnotPairs m).Nodup := by
  unfold highCnotPairs
  show List.Pairwise (· ≠ ·) (List.ofFn _)
  rw [List.pairwise_ofFn]
  intro i j hij heq
  have hh := congrArg Prod.fst heq
  simp at hh
  omega

/-- The CNOT targets in `highCnotPairs m` are pairwise distinct. -/
lemma highCnotPairs_targets_nodup (m : ℕ) : ((highCnotPairs m).map Prod.snd).Nodup := by
  unfold highCnotPairs
  rw [List.map_ofFn]
  show List.Pairwise (· ≠ ·) (List.ofFn _)
  rw [List.pairwise_ofFn]
  intro i j hij heq
  simp at heq
  omega

/-- A coordinate that is never a target of the CNOT list is unchanged by `cnotFold`. -/
lemma cnotFold_other {n : ℕ} : ∀ (L : List (Fin n × Fin n)) (r : Reg n) (t : Fin n),
    (∀ p ∈ L, p.2 ≠ t) → cnotFold L r t = r t := by
  intro L
  induction L with
  | nil => intro r t _; rfl
  | cons q L ih =>
    intro r t h
    have hL : ∀ p ∈ L, p.2 ≠ t := fun p hp => h p (List.mem_cons_of_mem _ hp)
    show cnotFold (q :: L) r t = r t
    rw [show cnotFold (q :: L) r = cnotFold L (Function.update r q.2 ((r q.2 ^^ r q.1))) from rfl]
    rw [ih _ _ hL]
    have hne : t ≠ q.2 := fun hh => h q List.mem_cons_self hh.symm
    simp [Function.update, hne]

/-- If `(c, t)` is the unique pair targeting `t`, all targets are distinct, and `c` is never
targeted, the final target bit is the original target bit XOR the original control bit. -/
lemma cnotFold_target_val {n : ℕ} : ∀ (L : List (Fin n × Fin n)) (r : Reg n) {c t : Fin n},
    (c, t) ∈ L →
    (L.map Prod.snd).Nodup →
    (∀ q ∈ L, q.2 = t → q = (c, t)) →
    (∀ q ∈ L, c ≠ q.2) →
    cnotFold L r t = (r t ^^ r c) := by
  intro L
  induction L with
  | nil => intro r c t h; simp at h
  | cons p L ih =>
    intro r c t hp hnodup huniq hnotc
    have hnodup' := List.nodup_cons.mp hnodup
    have hnotp : p.2 ∉ (L.map Prod.snd) := hnodup'.1
    have huniq' : ∀ q ∈ L, q.2 = t → q = (c, t) := fun q hq => huniq q (List.mem_cons_of_mem _ hq)
    have hnotc' : ∀ q ∈ L, c ≠ q.2 := fun q hq => hnotc q (List.mem_cons_of_mem _ hq)
    have hnotc_head : c ≠ p.2 := hnotc p List.mem_cons_self
    rw [show cnotFold (p :: L) r = cnotFold L (Function.update r p.2 ((r p.2 ^^ r p.1))) from rfl]
    rcases List.mem_cons.mp hp with heq | hpL
    · subst heq
      have hnot : ∀ q ∈ L, q.2 ≠ t := by
        intro q hq hh
        have hmem : t ∈ (L.map Prod.snd) := List.mem_map.mpr ⟨q, hq, hh⟩
        exact hnotp hmem
      rw [cnotFold_other L _ t hnot]
      simp
    · have hp2 : p.2 ≠ t := by
        intro hh
        have h1 : p = (c, t) := huniq p List.mem_cons_self hh
        have hmem : p.2 ∈ (L.map Prod.snd) := by
          refine List.mem_map.mpr ⟨(c, t), hpL, ?_⟩
          exact congrArg Prod.snd h1.symm
        exact hnotp hmem
      have hp2' : t ≠ p.2 := fun hh => hp2 hh.symm
      have hst : Function.update r p.2 ((r p.2 ^^ r p.1)) t = r t := by
        simp [Function.update, hp2']
      have hsc : Function.update r p.2 ((r p.2 ^^ r p.1)) c = r c := by
        simp [Function.update, hnotc_head]
      have hrec := ih (Function.update r p.2 ((r p.2 ^^ r p.1))) hpL hnodup'.2 huniq' hnotc'
      rw [hst, hsc] at hrec
      exact hrec

/-- Executing a list of CNOT gates with distinct control and target wires on a basis state
yields the basis state obtained by `cnotFold`. -/
lemma run_cnot_block {n : ℕ} : ∀ (L : List (Fin n × Fin n)) (r : Reg n),
    (∀ p ∈ L, p.1 ≠ p.2) →
    Run 1 (L.map fun p => Step.gate (cnotGate n p.1 p.2)) (Qatlib.Foundations.PureStateMath.Ket r) = Qatlib.Foundations.PureStateMath.Ket (cnotFold L r) := by
  intro L
  induction L with
  | nil => intro r _; rfl
  | cons p L ih =>
    intro r hc
    have hp : p.1 ≠ p.2 := hc p List.mem_cons_self
    have hL : ∀ q ∈ L, q.1 ≠ q.2 := fun q hq => hc q (List.mem_cons_of_mem _ hq)
    rw [List.map_cons, run_gate, applyGate_cnotGate_ket n p.1 p.2 hp, ih _ hL]
    rfl

/-- A legal finite CNOT code denotes the corresponding CNOT gate matrix. -/
lemma finiteCodeMatrix_cx (n : ℕ) (c t : ℕ) (h : c < n ∧ t < n ∧ c ≠ t) :
    finiteCodeMatrix n (.cx c t) = cnotGate n ⟨c, h.1⟩ ⟨t, h.2.1⟩ := by
  simp [finiteCodeMatrix, h]

/-- A legal finite Hadamard code denotes a Hadamard gate on the indicated wire. -/
lemma finiteCodeMatrix_h (n : ℕ) (w : ℕ) (h : w < n) :
    finiteCodeMatrix n (.h w) = wireGate n ⟨w, h⟩ Hadamard := by
  simp [finiteCodeMatrix, h]

/-- Executing the finite gate codes of a valid CNOT list on a basis state yields the basis state
obtained by folding the corresponding bit updates. -/
lemma run_cnot_block_code {n : ℕ} : ∀ (L : List (Fin n × Fin n)) (r : Reg n),
    (∀ p ∈ L, p.1 ≠ p.2) →
    (∀ p ∈ L, p.1.val < n ∧ p.2.val < n) →
    Run 1 (L.map fun p => Step.gate (finiteCodeMatrix n (.cx p.1.val p.2.val))) (Qatlib.Foundations.PureStateMath.Ket r)
      = Qatlib.Foundations.PureStateMath.Ket (cnotFold L r) := by
  intro L
  induction L with
  | nil => intro r _ _; rfl
  | cons p L ih =>
    intro r h1 h2
    have hp : p.1 ≠ p.2 := h1 p List.mem_cons_self
    have hpv : p.1.val ≠ p.2.val := by
      intro hh
      exact hp (Fin.ext hh)
    have hp2 : p.1.val < n ∧ p.2.val < n := h2 p List.mem_cons_self
    have hL1 : ∀ q ∈ L, q.1 ≠ q.2 := fun q hq => h1 q (List.mem_cons_of_mem _ hq)
    have hL2 : ∀ q ∈ L, q.1.val < n ∧ q.2.val < n := fun q hq => h2 q (List.mem_cons_of_mem _ hq)
    rw [List.map_cons, run_gate]
    rw [finiteCodeMatrix_cx n p.1.val p.2.val ⟨hp2.1, hp2.2, hpv⟩]
    rw [applyGate_cnotGate_ket n p.1 p.2 hp, ih _ hL1 hL2]
    rfl

/-- Executing a concatenated circuit applies the first circuit and then the second circuit. -/
lemma run_append {n : ℕ} : ∀ (A B : Circuit (Reg n)) (ψ : QState (Reg n)),
    Run 1 (A ++ B) ψ = Run 1 B (Run 1 A ψ) := by
  intro A
  induction A with
  | nil => intro B ψ; rfl
  | cons s A ih =>
    intro B ψ
    cases s with
    | gate U =>
      rw [List.cons_append, run_gate]
      exact ih B _
    | query =>
      rw [List.cons_append, run_query]
      exact ih B _

/-- A legal finite gate word executes successfully and returns the state produced by its decoded
circuit. -/
lemma finiteWordRun_of_legal {n : ℕ} {gs : List FiniteGateCode} (h : finiteWordLegal n gs = true)
    (ψ : QState (Reg n)) :
    finiteWordRun n gs ψ = some (Run 1 (finiteCodeCircuit n gs) ψ) := by
  rw [finiteWordRun]
  rw [if_pos h]

/-- The lazy setup word has one more instruction than `highCnotPairs m`, the update word has the
same length as that list, and the check word has length one. -/
theorem lazy_word_lengths (m : ℕ) :
    (lazySetupWord m).length = (highCnotPairs m).length + 1 ∧
    (lazyUpdateWord m).length = (highCnotPairs m).length ∧
    (lazyCheckWord m).length = 1 := by
  simp [lazySetupWord, lazyUpdateWord, lazyCheckWord]

/-- A coordinate in the left part of a concatenated register is the corresponding coordinate of
the first register. -/
lemma regCat_apply_left {a b : ℕ} (r : Reg a) (s : Reg b) (i : Fin (a + b)) (h : i.val < a) :
    regCat r s i = r ⟨i.val, h⟩ := by
  unfold regCat
  cases he : finSumFinEquiv.symm i with
  | inl x =>
    have hi : i = finSumFinEquiv (Sum.inl x) := finSumFinEquiv.symm_apply_eq.mp he
    have hv : i.val = x.val := by
      rw [hi, finSumFinEquiv_apply_left]
      exact Fin.val_castAdd b x
    have hx : x.val < a := by omega
    have hxeq : x = ⟨i.val, h⟩ := by
      refine Fin.ext ?_
      rw [hv]
    rw [hxeq]
    rfl
  | inr y =>
    have hi : i = finSumFinEquiv (Sum.inr y) := finSumFinEquiv.symm_apply_eq.mp he
    have hv : i.val = a + y.val := by
      rw [hi, finSumFinEquiv_apply_right]
      exact Fin.val_natAdd a y
    omega

/-- A coordinate in the right part of a concatenated register is the coordinate of the second
register at the offset index. -/
lemma regCat_apply_right {a b : ℕ} (r : Reg a) (s : Reg b) (i : Fin (a + b)) (h : a ≤ i.val) :
    regCat r s i = s ⟨i.val - a, by omega⟩ := by
  unfold regCat
  cases he : finSumFinEquiv.symm i with
  | inl x =>
    have hi : i = finSumFinEquiv (Sum.inl x) := finSumFinEquiv.symm_apply_eq.mp he
    have hv : i.val = x.val := by
      rw [hi, finSumFinEquiv_apply_left]
      exact Fin.val_castAdd b x
    omega
  | inr y =>
    have hi : i = finSumFinEquiv (Sum.inr y) := finSumFinEquiv.symm_apply_eq.mp he
    have hv : i.val = a + y.val := by
      rw [hi, finSumFinEquiv_apply_right]
      exact Fin.val_natAdd a y
    have hyval : y.val = i.val - a := by omega
    have hyeq : y = ⟨i.val - a, by omega⟩ := by
      refine Fin.ext ?_
      rw [hyval]
    rw [hyeq]
    rfl

/-- A right-hand coordinate of a concatenated register can be read using any index with the
corresponding offset value. -/
lemma regCat_apply_right' {a b : ℕ} (r : Reg a) (s : Reg b) (i : Fin (a + b)) (h : a ≤ i.val)
    (j : Fin b) (hj : j.val = i.val - a) : regCat r s i = s j := by
  rw [regCat_apply_right r s i h]
  congr 1
  exact Fin.ext hj.symm

/-- Zero padding reads the original register within its width and returns false at all other
coordinates. -/
lemma regPad_apply' {w a : ℕ} (r : Reg a) (j : Fin w) :
    regPad w a r j = if h : j.val < a then r ⟨j.val, h⟩ else false := rfl

/-- Reading a padded register at a coordinate within the original width returns the original
bit. -/
lemma regPad_apply {w a : ℕ} (r : Reg a) (j : Fin w) (h : j.val < a) :
    regPad w a r j = r ⟨j.val, h⟩ := by
  rw [regPad_apply']
  rw [dif_pos h]

/-- Padding a register to its own width leaves it unchanged. -/
lemma regPad_self {n : ℕ} (r : Reg n) : regPad n n r = r := by
  funext i
  have h := regPad_apply r i i.isLt
  rw [h]
end Qatlib.Concepts.WalkSearch.FrameSpectral
