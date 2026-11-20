/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
public import Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecoding
public import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Ancillary parity circuits and location-indexed bit flips

Each gate is a CNOT from a data wire to an ancillary wire. Preparing the ancillary register in
zero, applying the ordered gate word, and reading and resetting the ancillary register gives
one Kraus operator per joint syndrome. Bit flips are inserted after actual gates. Their
propagated data and syndrome shifts are computed by the same circuit execution on zero input.
-/

namespace Qatlib.Concepts.CodingDecoding.CssRecovery

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecoding
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix

variable {n m : ℕ}

/-- Computational basis labels of a binary register. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The data register and its ancillary readout register. -/
abbrev Joint (n m : ℕ) := Bits n × Bits m

/-- A CNOT connects one data wire to one ancillary wire. -/
structure ParityGate (n m : ℕ) where
  /-- The data control wire. -/
  control : Fin n
  /-- The ancillary target wire. -/
  target : Fin m

/-- The contribution of one CNOT to the measured check matrix. -/
def gateCheck (g : ParityGate n m) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  Matrix.single g.target g.control 1

/-- Execute the CNOT on data and ancillary basis labels. -/
def parityStep (g : ParityGate n m) (v : Joint n m) : Joint n m :=
  (v.1, v.2 + gateCheck g *ᵥ v.1)

/-- The CNOT leaves data unchanged and toggles exactly its ancillary target by the control bit. -/
theorem step_target (g : ParityGate n m) (v : Joint n m) :
    (parityStep g v).2 = v.2 + Function.update (0 : Bits m) g.target (v.1 g.control) := by
  rw [parityStep, gateCheck, Matrix.single_mulVec, one_mul]

/-- Apply a parity circuit in gate order. -/
def parityRun : List (ParityGate n m) → Joint n m → Joint n m
  | [], v => v
  | g :: gs, v => parityRun gs (parityStep g v)

/-- Sum the binary incidences implemented by a parity circuit. -/
def circuitCheck : List (ParityGate n m) → Matrix (Fin m) (Fin n) (ZMod 2)
  | [] => 0
  | g :: gs => gateCheck g + circuitCheck gs

/-- The circuit accumulates precisely the check-matrix syndrome into the ancillary register. -/
theorem parity_run (gs : List (ParityGate n m)) (v : Joint n m) :
    parityRun gs v = (v.1, v.2 + circuitCheck gs *ᵥ v.1) := by
  induction gs generalizing v with
  | nil => simp [parityRun, circuitCheck]
  | cons g gs ih => simp [parityRun, circuitCheck, ih, parityStep, Matrix.add_mulVec, add_assoc]

/-- The finite matrix of the ordered circuit on computational basis labels. -/
noncomputable def parityOp (gs : List (ParityGate n m)) : Matrix (Joint n m) (Joint n m) ℂ :=
  fun y x => if y = parityRun gs x then 1 else 0

/-- Applying the same CNOT word twice cancels its parity addition. -/
private theorem parity_invol (gs : List (ParityGate n m)) :
    Function.Involutive (parityRun gs) := by
  intro v
  rw [parity_run, parity_run]
  change (v.1, (v.2 + circuitCheck gs *ᵥ v.1) + circuitCheck gs *ᵥ v.1) = v
  rw [add_assoc, binary_add_self, add_zero]

/-- The computed permutation matrix of any parity gate word is unitary. -/
theorem parity_unitary (gs : List (ParityGate n m)) :
    parityOp gs ∈ Matrix.unitaryGroup (Joint n m) ℂ :=
  permMatrix_unitary (parity_invol gs)

/-- Prepending a gate acts by composing its actual matrix with the remaining gates. -/
theorem parity_cons (g : ParityGate n m) (gs : List (ParityGate n m)) :
    parityOp (g :: gs) = parityOp gs * parityOp [g] := by
  ext y x
  simp only [parityOp, parityRun, Matrix.mul_apply]
  rw [Finset.sum_eq_single (parityStep g x)]
  · by_cases h : y = parityRun gs (parityStep g x) <;> simp [h]
  · intro i _ hi
    simp [hi]
  · simp

/-- Prepare the ancillary register in the zero basis state. -/
noncomputable def prepZero : Matrix (Joint n m) (Bits n) ℂ :=
  fun v x => if v = (x, 0) then 1 else 0

/-- Read a specified syndrome and discard the measured ancillary label. -/
noncomputable def readReset (η : Bits m) : Matrix (Bits n) (Joint n m) ℂ :=
  fun x v => if v = (x, η) then 1 else 0

/-- Compose zero preparation, a joint operator, and the indicated readout and reset. -/
noncomputable def readAfter (U : Matrix (Joint n m) (Joint n m) ℂ) (η : Bits m) :
    Matrix (Bits n) (Bits n) ℂ :=
  Matrix.addMonoidHomMulLeft (n := Bits n) (readReset (n := n) η)
    (Matrix.addMonoidHomMulLeft (n := Bits n) U (prepZero (n := n) (m := m)))

/-- Preparation and readout select the corresponding entry of a joint operator. -/
private theorem read_entry (U : Matrix (Joint n m) (Joint n m) ℂ)
    (η : Bits m) (x y : Bits n) :
    readAfter U η x y = U (x, η) (y, 0) := by
  change (∑ j : Joint n m, readReset η x j * ∑ k : Joint n m, U j k * prepZero k y) = _
  have hinner (j : Joint n m) : (∑ k : Joint n m, U j k * prepZero k y) = U j (y, 0) := by
    rw [Finset.sum_eq_single (y, 0)]
    · simp [prepZero]
    · intro k _ hk
      simp [prepZero, hk]
    · simp
  simp_rw [hinner]
  rw [Finset.sum_eq_single (x, η)]
  · simp [readReset]
  · intro j _ hj
    simp [readReset, hj]
  · simp

/-- The actual preparation, gate word, and readout yield the joint-syndrome projection. -/
theorem parity_branch (gs : List (ParityGate n m)) (η : Bits m) :
    readAfter (parityOp gs) η =
      Matrix.diagonal (fun x : Bits n => if circuitCheck gs *ᵥ x = η then (1 : ℂ) else 0) := by
  ext x y
  rw [read_entry, parityOp, parity_run]
  by_cases h : x = y
  · subst y
    simp [eq_comm]
  · simp [h]

/-- An explicit finite indexing of the data basis for the public instrument interface. -/
noncomputable def dataIndex (n : ℕ) : Bits n ≃ Fin (Fintype.card (Bits n)) :=
  Fintype.equivFin _

/-- Kraus operator for one outcome of the executed parity circuit. -/
noncomputable def parityKraus (gs : List (ParityGate n m)) (η : Bits m) :
    Operator (Fintype.card (Bits n)) :=
  Matrix.reindex (dataIndex n) (dataIndex n) (readAfter (parityOp gs) η)

/-- Each outcome retains the basis states with its measured syndrome. -/
theorem parity_diag (gs : List (ParityGate n m)) (η : Bits m) :
    parityKraus gs η = Matrix.diagonal (fun i =>
      if circuitCheck gs *ᵥ (dataIndex n).symm i = η then 1 else 0) := by
  rw [parityKraus, parity_branch]
  ext i j
  simp [Matrix.reindex_apply, Matrix.diagonal_apply]

/-- Every data basis state contributes to exactly one measured syndrome. -/
theorem parity_complete (gs : List (ParityGate n m)) :
    ∑ η : Bits m, (parityKraus gs η)ᴴ * parityKraus gs η = 1 := by
  have idem (η : Bits m) : (parityKraus gs η)ᴴ * parityKraus gs η = parityKraus gs η := by
    rw [parity_diag, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    by_cases h : circuitCheck gs *ᵥ (dataIndex n).symm i = η <;> simp [h]
  simp_rw [idem, parity_diag]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.sum_apply]
  · simp [Matrix.sum_apply, hij]

/-- The public joint-syndrome instrument for the given CNOT word. -/
noncomputable def parityInstr (gs : List (ParityGate n m)) :
    Instrument (Bits m) (Fintype.card (Bits n)) (Fintype.card (Bits n)) :=
  Instrument.ofKraus (parityKraus gs) (parity_complete gs)

/-- The instrument branch acts by conjugation with the syndrome projector derived from the
actual circuit. -/
theorem parity_outcome (gs : List (ParityGate n m)) (η : Bits m)
    (ρ : Operator (Fintype.card (Bits n))) :
    (parityInstr gs).branch η ρ = parityKraus gs η * ρ * (parityKraus gs η)ᴴ :=
  Instrument.ofKraus_branch _ _ _ _

/-- Insert bit flips after actual gate locations and follow the resulting basis label. -/
def faultRun : (gs : List (ParityGate n m)) → (Fin gs.length → Joint n m) →
    Joint n m → Joint n m
  | [], _, v => v
  | g :: gs, f, v => faultRun gs (fun i => f i.succ) (parityStep g v + f 0)

/-- Ideal parity execution is additive on basis labels. -/
private theorem parity_add (gs : List (ParityGate n m)) (u v : Joint n m) :
    parityRun gs (u + v) = parityRun gs u + parityRun gs v := by
  simp only [parity_run]
  apply Prod.ext
  · rfl
  · change (u.2 + v.2) + circuitCheck gs *ᵥ (u.1 + v.1) =
      (u.2 + circuitCheck gs *ᵥ u.1) + (v.2 + circuitCheck gs *ᵥ v.1)
    rw [Matrix.mulVec_add]
    abel

/-- The propagated shift is the execution of the same faulty circuit on zero input. -/
theorem fault_shift (gs : List (ParityGate n m)) (f : Fin gs.length → Joint n m) (v : Joint n m) :
    faultRun gs f v = parityRun gs v + faultRun gs f 0 := by
  induction gs generalizing v with
  | nil => simp [faultRun, parityRun]
  | cons g gs ih =>
    simp only [faultRun, parityRun]
    have hz : parityStep g (0 : Joint n m) = 0 := by simp [parityStep]
    rw [hz, zero_add, ih _ (parityStep g v + f 0), ih _ (f 0), parity_add, add_assoc]

/-- Cascading two faulty runs adds the first shift after propagation through the second word
and the shift created by the second word. -/
theorem fault_comp (gs hs : List (ParityGate n m))
    (f : Fin gs.length → Joint n m) (h : Fin hs.length → Joint n m) (v : Joint n m) :
    faultRun hs h (faultRun gs f v) =
      parityRun hs (parityRun gs v) + (parityRun hs (faultRun gs f 0) + faultRun hs h 0) := by
  conv_lhs =>
    rw [fault_shift hs h, fault_shift gs f, parity_add]
  rw [add_assoc]

/-- A parity CNOT never increases the data support of a bit flip, so the data shift is the sum
of exactly the local data flips. -/
theorem fault_data (gs : List (ParityGate n m)) (f : Fin gs.length → Joint n m)
    (v : Joint n m) : (faultRun gs f v).1 = v.1 + ∑ i, (f i).1 := by
  induction gs generalizing v with
  | nil => simp [faultRun]
  | cons g gs ih =>
    rw [faultRun, ih]
    change v.1 + (f 0).1 + (∑ i : Fin gs.length, (f i.succ).1) =
      v.1 + ∑ i : Fin (gs.length + 1), (f i).1
    rw [Fin.sum_univ_succ (fun i : Fin (gs.length + 1) => (f i).1), add_assoc]

/-- The resolved syndrome of a noisy run is the ideal syndrome plus the propagated readout
shift, paired with the actual propagated data shift. -/
theorem fault_readout (gs : List (ParityGate n m)) (f : Fin gs.length → Joint n m) (x : Bits n) :
    faultRun gs f (x, 0) = (x + (faultRun gs f 0).1,
      circuitCheck gs *ᵥ x + (faultRun gs f 0).2) := by
  rw [fault_shift, parity_run]
  change (x + (faultRun gs f 0).1, (0 + circuitCheck gs *ᵥ x) + (faultRun gs f 0).2) = _
  rw [zero_add]

/-- The true final parity and the measured parity differ by a syndrome discrepancy determined
entirely by the gate faults, for every initial data label. -/
theorem fault_syndrome (gs : List (ParityGate n m)) (f : Fin gs.length → Joint n m)
    (x : Bits n) :
    (faultRun gs f (x, 0)).2 - circuitCheck gs *ᵥ (faultRun gs f (x, 0)).1 =
      (faultRun gs f 0).2 - circuitCheck gs *ᵥ (faultRun gs f 0).1 := by
  rw [fault_readout, Matrix.mulVec_add, add_sub_add_left_eq_sub]

/-- The executed circuit matrix with bit flips inserted at the specified locations. -/
noncomputable def faultyOp (gs : List (ParityGate n m)) (f : Fin gs.length → Joint n m) :
    Matrix (Joint n m) (Joint n m) ℂ :=
  fun y x => if y = faultRun gs f x then 1 else 0

/-- The executed noisy measurement branch reports the propagated syndrome shift and applies
the propagated data flip. -/
theorem faulty_branch (gs : List (ParityGate n m)) (f : Fin gs.length → Joint n m)
    (η : Bits m) (x y : Bits n) :
    readAfter (faultyOp gs f) η x y =
      if x = y + (faultRun gs f 0).1 ∧ η = circuitCheck gs *ᵥ y + (faultRun gs f 0).2
      then 1 else 0 := by
  rw [read_entry, faultyOp, fault_readout]
  simp only [Prod.mk.injEq]

/-- The executed noisy branch is an ideal branch at a shifted outcome, followed by the
actual propagated data flip. -/
theorem faulty_operator (gs : List (ParityGate n m)) (f : Fin gs.length → Joint n m)
    (η : Bits m) :
    readAfter (faultyOp gs f) η = cssPauliX (faultRun gs f 0).1 *
      readAfter (parityOp gs) (η - (faultRun gs f 0).2) := by
  ext x y
  rw [faulty_branch, parity_branch, Matrix.mul_diagonal]
  change (if x = y + (faultRun gs f 0).1 ∧
    η = circuitCheck gs *ᵥ y + (faultRun gs f 0).2 then (1 : ℂ) else 0) =
    (if x = y + (faultRun gs f 0).1 then 1 else 0) *
      (if circuitCheck gs *ᵥ y = η - (faultRun gs f 0).2 then 1 else 0)
  have h : (η = circuitCheck gs *ᵥ y + (faultRun gs f 0).2) ↔
      circuitCheck gs *ᵥ y = η - (faultRun gs f 0).2 :=
    eq_comm.trans eq_sub_iff_add_eq.symm
  by_cases hx : x = y + (faultRun gs f 0).1
  · by_cases hy : circuitCheck gs *ᵥ y = η - (faultRun gs f 0).2
    · have hyes := And.intro hx (h.mpr hy)
      rw [ite_eq_left hyes, ite_eq_left hx, ite_eq_left hy, one_mul]
    · have hnot : ¬(x = y + (faultRun gs f 0).1 ∧
          η = circuitCheck gs *ᵥ y + (faultRun gs f 0).2) := fun he => hy (h.mp he.2)
      rw [ite_eq_right hnot, ite_eq_left hx, ite_eq_right hy, mul_zero]
  · have hnot : ¬(x = y + (faultRun gs f 0).1 ∧
        η = circuitCheck gs *ᵥ y + (faultRun gs f 0).2) := fun he => hx he.1
    rw [ite_eq_right hnot, ite_eq_right hx, zero_mul]

/-- Treat a set of faulty gates as selecting the local flip specified at each location. -/
def faultsAt (gs : List (ParityGate n m)) (flip : Fin gs.length → Joint n m)
    (F : Finset (Fin gs.length)) : Fin gs.length → Joint n m :=
  fun i => if i ∈ F then flip i else 0

/-- The CSS gadget interface consumes the data component propagated by the actual gate word. -/
def parityGadget {κX κZ : Type*} (c : CssData (Fin n) κX κZ)
    (gs : List (ParityGate n m)) (flip : Fin gs.length → Joint n m) : GadgetSpec c where
  kind := .syndromeRound
  locations := gs.length
  space := n + m
  time := gs.length
  ideal := 0
  residual F := ((faultRun gs (faultsAt gs flip F) 0).1, 0)

/-- With no faulty locations the propagated gadget residual is the zero Pauli label. -/
theorem gadget_empty {κX κZ : Type*} (c : CssData (Fin n) κX κZ)
    (gs : List (ParityGate n m)) (flip : Fin gs.length → Joint n m) :
    (parityGadget c gs flip).residual ∅ = 0 := by
  have h (w : List (ParityGate n m)) : faultRun w (fun _ => 0) 0 = 0 := by
    induction w with
    | nil => rfl
    | cons g w ih =>
      have hz : parityStep g (0 : Joint n m) = 0 := by simp [parityStep]
      rw [faultRun, hz, add_zero]
      exact ih
  change ((faultRun gs (faultsAt gs flip ∅) 0).1, 0) = 0
  rw [show faultsAt gs flip ∅ = fun _ => 0 by funext i; simp [faultsAt], h]
  rfl

/-- The number of affected data bits in a sum is bounded by the sum of the input weights. -/
private theorem bitWeight_sum {L : Type*} (F : Finset L) (x : L → Bits n) :
    bitWeight (∑ i ∈ F, x i) ≤ ∑ i ∈ F, bitWeight (x i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [bitWeight]
  | insert i F hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have h := pauliWeight_add_le (x i) (∑ j ∈ F, x j) (0 : Bits n) 0
    have ha : bitWeight (x i + ∑ j ∈ F, x j) ≤
        bitWeight (x i) + bitWeight (∑ j ∈ F, x j) := by
      simpa only [add_zero, pauliWeight_zero_right] using h
    exact ha.trans (Nat.add_le_add_left ih _)

/-- If each possible gate fault flips at most one data bit, any set of faulty gates creates
a data residual whose weight is bounded by the number of faulty locations. -/
theorem fault_weight (gs : List (ParityGate n m)) (flip : Fin gs.length → Joint n m)
    (hloc : ∀ i, bitWeight (flip i).1 ≤ 1) (F : Finset (Fin gs.length)) :
    bitWeight (faultRun gs (faultsAt gs flip F) 0).1 ≤ F.card := by
  rw [fault_data]
  change bitWeight (0 + ∑ i, (faultsAt gs flip F i).1) ≤ F.card
  rw [zero_add]
  have hsum : (∑ i : Fin gs.length, (faultsAt gs flip F i).1) = ∑ i ∈ F, (flip i).1 := by
    calc
      _ = ∑ i ∈ F, (faultsAt gs flip F i).1 := by
        symm
        apply Finset.sum_subset (Finset.subset_univ F)
        intro i _ hi
        simp [faultsAt, hi]
      _ = _ := Finset.sum_congr rfl fun i hi => by simp [faultsAt, hi]
  rw [hsum]
  apply (bitWeight_sum F _).trans
  simpa using (Finset.sum_le_sum fun i (_ : i ∈ F) => hloc i)

/-- The executed parity circuit satisfies the public gadget contract for every fault budget
when the local fault model flips at most one data bit per location. -/
theorem gadget_bound {κX κZ : Type*} (c : CssData (Fin n) κX κZ)
    (gs : List (ParityGate n m)) (flip : Fin gs.length → Joint n m)
    (hloc : ∀ i, bitWeight (flip i).1 ≤ 1) (t : ℕ) :
    (parityGadget c gs flip).IsFaultTolerantAt t := by
  intro F hF
  change pauliWeight (faultRun gs (faultsAt gs flip F) 0).1 0 ≤ t
  rw [pauliWeight_zero_right]
  exact (fault_weight gs flip hloc F).trans hF

/-- For a Z-check round on clean input, a decoder whose syndrome tolerance covers the
propagated discrepancy leaves a stabilizer residual after the actual measured outcome. -/
theorem fault_decode (c : CssData (Fin n) (Fin 0) (Fin m)) (gs : List (ParityGate n m))
    (hz : circuitCheck gs = c.hZ) (flip : Fin gs.length → Joint n m)
    (hloc : ∀ i, bitWeight (flip i).1 ≤ 1) (F : Finset (Fin gs.length))
    {t s : ℕ} (hF : F.card ≤ t) (prog : RecoveryProgram c)
    (hprog : CorrectsSingleShotNoisyUpTo prog t s)
    (hobs : bitWeight (circuitCheck gs *ᵥ (faultRun gs (faultsAt gs flip F) 0).1 +
      (faultRun gs (faultsAt gs flip F) 0).2) ≤ s) :
    IsStabilizerLabel c (residualFromObserved prog
      ((faultRun gs (faultsAt gs flip F) 0).1, 0) (0, (faultRun gs (faultsAt gs flip F) 0).2)) := by
  apply hprog
  · rw [pauliWeight_zero_right]
    exact (fault_weight gs flip hloc F).trans hF
  · change bitWeight (c.hX *ᵥ (0 : Bits n) + 0) +
      bitWeight (c.hZ *ᵥ (faultRun gs (faultsAt gs flip F) 0).1 +
        (faultRun gs (faultsAt gs flip F) 0).2) ≤ s
    have hzero : bitWeight (0 : Bits 0) = 0 := by simp [bitWeight]
    rw [Matrix.mulVec_zero, add_zero, hzero, zero_add, ← hz]
    exact hobs

end Qatlib.Concepts.CodingDecoding.CssRecovery
