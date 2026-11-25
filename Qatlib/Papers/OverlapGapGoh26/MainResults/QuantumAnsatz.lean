/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.OverlapGapGoh26.Resources.ParityGadget
public import Qatlib.Papers.OverlapGapGoh26.TensorModel.SparseXorsat
public import Qatlib.Papers.QAOACSP16.TypicalQaoa.QaoaState.SourceQaoaState

@[expose] public section

/-!
# The QAOA circuit and its computational-basis distribution

Equation (5) of Goh and Müller (arXiv:2609.35131v1) alternates a diagonal
phase with one Pauli-X rotation on each qubit. Emit these gates in time order
on `N` qubits for any `p` layers and interpret the emitted list on complex
amplitudes. For Eq. (33), the cost phase factors into its sparse clause phases.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Qatlib.Papers.QAOACSP16.TypicalQaoa.QaoaState
open Qatlib.Papers.OverlapGapGoh26.Resources
open Qatlib.Papers.OverlapGapGoh26.TensorModel

namespace Qatlib.Papers.OverlapGapGoh26.MainResults

/-- A diagonal problem phase or an X rotation on one of the typed circuit wires. -/
inductive AnsatzGate (N : ℕ) where
  | problem (angle : ℝ)
  | xRotation (wire : Fin N) (angle : ℝ)

/-- Interpret each gate on the computational-basis amplitudes. -/
def runAnsatzGate {N : ℕ} (H : (Fin N → Bool) → ℝ) (ψ : Amp (Fin N)) :
    AnsatzGate N → Amp (Fin N)
  | .problem γ => fun z => ParityGadget.phaseFactor γ (H z) * ψ z
  | .xRotation j β => mixerStep β j ψ

/-- Emit one cost phase followed by the rotations of all mixer wires. -/
def layerGates (N : ℕ) (γ β : ℝ) : List (AnsatzGate N) :=
  .problem γ :: (List.finRange N).map (fun j => .xRotation j β)

/-- Emit the QAOA circuit in execution order, beginning with layer zero. -/
def qaoaWord (N : ℕ) {p : ℕ} (γ β : Fin p → ℝ) : List (AnsatzGate N) :=
  (List.finRange p).flatMap (fun k => layerGates N (γ k) (β k))

/-- Interpret the emitted QAOA word on the uniform superposition. -/
def qaoaAmplitude {N p : ℕ} (H : (Fin N → Bool) → ℝ) (γ β : Fin p → ℝ) : Amp (Fin N) :=
  (qaoaWord N γ β).foldl (runAnsatzGate H) uniformAmp

/-- The last cost and mixer layer is applied to the output of its preceding prefix. -/
theorem qaoa_amplitude_succ {N p : ℕ} (H : (Fin N → Bool) → ℝ) (γ β : Fin (p + 1) → ℝ) :
    qaoaAmplitude H γ β =
      (layerGates N (γ (Fin.last p)) (β (Fin.last p))).foldl (runAnsatzGate H)
        (qaoaAmplitude H (fun k => γ k.castSucc) (fun k => β k.castSucc)) := by
  unfold qaoaAmplitude qaoaWord
  rw [List.finRange_succ_last, List.flatMap_append, List.foldl_append]
  simp [List.flatMap_map]

private theorem ansatzGate_preserves {N : ℕ} (H : (Fin N → Bool) → ℝ)
    (g : AnsatzGate N) (ψ : Amp (Fin N)) :
    (∑ z, Complex.normSq (runAnsatzGate H ψ g z)) = ∑ z, Complex.normSq (ψ z) := by
  cases g with
  | problem γ =>
      apply Finset.sum_congr rfl
      intro z _
      rw [runAnsatzGate, Complex.normSq_mul, Complex.normSq_eq_norm_sq
        (ParityGadget.phaseFactor γ (H z)), ParityGadget.phaseFactor_norm, one_pow, one_mul]
  | xRotation j β =>
      exact sum_normSq_mixerStep β j ψ

private theorem ansatzWord_preserves {N : ℕ} (H : (Fin N → Bool) → ℝ)
    (word : List (AnsatzGate N)) (ψ : Amp (Fin N)) :
    (∑ z, Complex.normSq (word.foldl (runAnsatzGate H) ψ z)) =
      ∑ z, Complex.normSq (ψ z) := by
  induction word generalizing ψ with
  | nil => rfl
  | cons g word ih =>
      rw [List.foldl_cons, ih, ansatzGate_preserves]

/-- The Born probability assigned to a computational-basis outcome by the circuit. -/
def qaoaBasisProb {N p : ℕ} (H : (Fin N → Bool) → ℝ)
    (γ β : Fin p → ℝ) (z : Fin N → Bool) : ℝ :=
  Complex.normSq (qaoaAmplitude H γ β z)

/-- Every computational-basis probability of the emitted program is nonnegative. -/
theorem qaoa_basis_prob_nonneg {N p : ℕ} (H : (Fin N → Bool) → ℝ)
    (γ β : Fin p → ℝ) (z : Fin N → Bool) : 0 ≤ qaoaBasisProb H γ β z :=
  Complex.normSq_nonneg _

/-- The computational-basis probabilities of the emitted program sum to one for every
number of qubits, depth, and sequence of angles. -/
theorem qaoa_basis_prob_sum_one {N p : ℕ} (H : (Fin N → Bool) → ℝ)
    (γ β : Fin p → ℝ) : (∑ z, qaoaBasisProb H γ β z) = 1 := by
  unfold qaoaBasisProb qaoaAmplitude
  rw [ansatzWord_preserves]
  simp only [uniformAmp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : 0 < (Fintype.card (Fin N → Bool) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.normSq_ofReal,
    ← pow_two, div_pow, one_pow,
    Real.sq_sqrt hcard.le, mul_one_div_cancel hcard.ne']

/-- The diagonal cost used by the ansatz for Eq. (33), with four sites in each clause. -/
def xorsatCost {N : ℕ} {E : Type} [Fintype E]
    (ends : E → Fin 4 → Fin N) (coupling : E → ℝ) (z : Fin N → Bool) : ℝ :=
  SparseXorsat.reward ends coupling (SparseXorsat.bitSpin z)

/-- Acting on any state, Eq. (33)'s diagonal problem gate factors into the product of its
four-spin clause phases at each basis configuration. -/
theorem xorsat_problem_factor {N : ℕ} {E : Type} [Fintype E]
    (ends : E → Fin 4 → Fin N) (coupling : E → ℝ) (γ : ℝ)
    (ψ : Amp (Fin N)) (z : Fin N → Bool) :
    runAnsatzGate (xorsatCost ends coupling) ψ (.problem γ) z =
      (∏ e, ParityGadget.phaseFactor γ
        ((1 + coupling e * ∏ j, SparseXorsat.bitSpin z (ends e j)) / 2)) * ψ z := by
  simp only [runAnsatzGate, xorsatCost, SparseXorsat.reward, ParityGadget.phaseFactor,
    Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]

/-- The four-bit view of a clause, transported to the parity gadget's spin convention. -/
def clauseBasis {N : ℕ} (sites : Fin 4 → Fin N) (z : Fin N → Bool) : ParityGadget.Basis :=
  (!z (sites 0), !z (sites 1), !z (sites 2), !z (sites 3))

/-- Each factor of the sparse phase equals the action of the six-CNOT parity word on that
clause, with the global phase for the constant part of its reward included. -/
theorem xorsat_clause_gadget {N : ℕ} (sites : Fin 4 → Fin N) (J γ : ℝ) (z : Fin N → Bool) :
    ParityGadget.phaseFactor γ ((1 + J * ∏ j, SparseXorsat.bitSpin z (sites j)) / 2) =
      ParityGadget.phaseFactor (γ / 2) 1 *
        ParityGadget.runWord (ParityGadget.word (γ * J / 2)) (fun _ => 1) (clauseBasis sites z) := by
  have hspin (i : Fin N) : ParityGadget.spin (!z i) = SparseXorsat.bitSpin z i := by
    cases h : z i <;> simp [h, ParityGadget.spin, SparseXorsat.bitSpin]
  have hparity : ParityGadget.parityZ (clauseBasis sites z) =
      ∏ j, SparseXorsat.bitSpin z (sites j) := by
    simp only [clauseBasis, ParityGadget.parityZ, hspin, Fin.prod_univ_four]
  simp only [ParityGadget.actual_parity_word, mul_one]
  have h := ParityGadget.actual_cost_phase γ J (clauseBasis sites z)
  rw [ParityGadget.actual_quartic_energy] at h
  simpa only [hparity] using h

end Qatlib.Papers.OverlapGapGoh26.MainResults
