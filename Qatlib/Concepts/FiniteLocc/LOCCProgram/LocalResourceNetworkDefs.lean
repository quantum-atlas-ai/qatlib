/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCC
import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorRegisters
import Qatlib.Concepts.FiniteLocc.LOCCProgram.EntanglementDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCC
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCCDefs
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.FiniteLocc.LOCCProgram
namespace LocalResourceNetworkDefs

open Matrix
open scoped Classical BigOperators ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable def invSqrtTwo : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

theorem invSqrtTwo_sq : invSqrtTwo ^ 2 = (2 : ℂ)⁻¹ := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    norm_cast
    simpa using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [invSqrtTwo, inv_pow, h]

theorem invSqrtTwo_star : starRingEnd ℂ invSqrtTwo = invSqrtTwo := by
  rw [invSqrtTwo, map_inv₀, Complex.conj_ofReal]

theorem invSqrtTwo_mul : invSqrtTwo * invSqrtTwo = (2 : ℂ)⁻¹ := by
  rw [show invSqrtTwo * invSqrtTwo = invSqrtTwo ^ 2 from by ring, invSqrtTwo_sq]

noncomputable def bellVector : Fin 2 × Fin 2 → ℂ :=
  fun ij => if ij = (0, 0) then invSqrtTwo else if ij = (1, 1) then invSqrtTwo else 0

noncomputable def eprFactor : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  outerProduct bellVector

theorem eprFactor_psd : eprFactor.PosSemidef :=
  outerProduct_posSemidef _

theorem eprFactor_trace : Matrix.trace eprFactor = 1 := by
  simp only [eprFactor, Matrix.trace, Matrix.diag_apply, outerProduct_apply]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [bellVector, invSqrtTwo_star, invSqrtTwo_mul]
  ring

theorem eprFactor_canonical :
    eprFactor = (1 / 2 : ℂ) • outerProduct (fun ij => if ij.1 = ij.2 then 1 else 0) := by
  ext i j
  rcases i with ⟨i1, i2⟩
  rcases j with ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [eprFactor, outerProduct_apply, bellVector, Matrix.smul_apply, invSqrtTwo_star,
      invSqrtTwo_mul] <;>
    ring

noncomputable def eprInventory (m : ℕ) :
    Matrix (Fin m → (Fin 2 × Fin 2)) (Fin m → (Fin 2 × Fin 2)) ℂ :=
  productMatrix (fun _ => eprFactor)

theorem eprInventory_psd (m : ℕ) : (eprInventory m).PosSemidef :=
  productMatrix_psd (fun _ => eprFactor) (fun _ => eprFactor_psd)

theorem eprInventory_trace (m : ℕ) : Matrix.trace (eprInventory m) = 1 := by
  rw [eprInventory, productMatrix_trace]
  simp [eprFactor_trace]

noncomputable def slotAction (m : ℕ) (j : Fin m)
    (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin m → (Fin 2 × Fin 2)) (Fin m → (Fin 2 × Fin 2)) ℂ :=
  productMatrix (fun j' => if j' = j then A else 1)

private theorem productMatrix_congr {ι : Type} [Fintype ι] {S : ι → Type}
    (f g : ∀ i, Matrix (S i) (S i) ℂ) (h : ∀ i x y, f i x y = g i x y) :
    productMatrix f = productMatrix g := by
  ext x y
  simp only [productMatrix]
  exact Finset.prod_congr rfl fun i _ => h i (x i) (y i)

theorem slotAction_mul_inventory (m : ℕ) (j : Fin m)
    (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    slotAction m j A * eprInventory m
      = productMatrix (fun j' => (if j' = j then A else 1) * eprFactor) := by
  rw [slotAction, eprInventory, productMatrix_mul]

theorem slotAction_adjoint (m : ℕ) (j : Fin m)
    (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (slotAction m j A)ᴴ = productMatrix (fun j' => if j' = j then Aᴴ else 1) := by
  rw [slotAction, productMatrix_adjoint]
  refine productMatrix_congr _ _ ?_
  intro j' x y
  by_cases hj : j' = j
  · subst hj
    simp
  · rw [if_neg hj, if_neg hj]
    rw [Matrix.conjTranspose_one]

theorem slot_consumption (m : ℕ) (j : Fin m)
    (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    slotAction m j A * eprInventory m * (slotAction m j A)ᴴ
      = productMatrix (fun j' => if j' = j then A * eprFactor * Aᴴ else eprFactor) := by
  rw [slotAction_mul_inventory, slotAction_adjoint, productMatrix_mul]
  refine productMatrix_congr _ _ ?_
  intro j' x y
  by_cases hj : j' = j
  · subst hj
    simp
  · simp [hj]

theorem two_slot_consumption (m : ℕ) (j₁ j₂ : Fin m) (hne : j₁ ≠ j₂)
    (A₁ A₂ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    slotAction m j₂ A₂ * (slotAction m j₁ A₁ * eprInventory m * (slotAction m j₁ A₁)ᴴ)
        * (slotAction m j₂ A₂)ᴴ
      = productMatrix (fun j' =>
          if j' = j₁ then A₁ * eprFactor * A₁ᴴ else if j' = j₂ then A₂ * eprFactor * A₂ᴴ
          else eprFactor) := by
  rw [slot_consumption, slotAction_adjoint, slotAction, productMatrix_mul, productMatrix_mul]
  refine productMatrix_congr _ _ ?_
  intro j' x y
  by_cases h1 : j' = j₁
  · have h2 : j' ≠ j₂ := fun h2 => hne (h1.symm.trans h2)
    simp [h1, h2, hne, Ne.symm hne]
  · by_cases h2 : j' = j₂
    · simp [h1, h2, hne, Ne.symm hne]
    · simp [h1, h2]

abbrev LocalParty := ℕ

structure EPRRelease where

  first : LocalParty

  second : LocalParty
  deriving DecidableEq

structure EPRInventory where

  slots : ℕ

  release : Fin slots → EPRRelease

noncomputable def EPRInventory.state (inv : EPRInventory) :
    Matrix (Fin inv.slots → (Fin 2 × Fin 2)) (Fin inv.slots → (Fin 2 × Fin 2)) ℂ :=
  eprInventory inv.slots

theorem EPRInventory.state_psd (inv : EPRInventory) : (inv.state).PosSemidef :=
  eprInventory_psd inv.slots

theorem EPRInventory.state_trace (inv : EPRInventory) :
    Matrix.trace inv.state = 1 :=
  eprInventory_trace inv.slots

inductive EPRFactoryGate where

  | hadamard (slot : ℕ) (half : Bool)

  | cnot (slot : ℕ)
  deriving DecidableEq

def eprFactoryGates (m : ℕ) : List EPRFactoryGate :=
  (List.finRange m).flatMap (fun j => [.hadamard j false, .cnot j])

theorem eprFactoryGates_length (m : ℕ) : (eprFactoryGates m).length = 2 * m := by
  simp [eprFactoryGates, List.length_flatMap, List.length_finRange]
  ring

def EPRInventory.gateCost (inv : EPRInventory) : ℕ :=
  (eprFactoryGates inv.slots).length

theorem EPRInventory.gateCost_eq (inv : EPRInventory) :
    inv.gateCost = 2 * inv.slots :=
  eprFactoryGates_length inv.slots

noncomputable def hadamard2 : Operator 2 :=
  fun i j => if i = 0 then invSqrtTwo else if j = 0 then invSqrtTwo else -invSqrtTwo

def xorFin2 (a b : Fin 2) : Fin 2 := if a = b then 0 else 1

noncomputable def eprFactoryUnitary : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun i j => hadamard2 i.1 j.1 * if xorFin2 i.2 i.1 = j.2 then 1 else 0

def e00 : Fin 2 × Fin 2 → ℂ :=
  fun ij => if ij = (0, 0) then 1 else 0

theorem eprFactoryUnitary_e00 : eprFactoryUnitary *ᵥ e00 = bellVector := by
  funext i
  rcases i with ⟨i1, i2⟩
  fin_cases i1 <;> fin_cases i2 <;>
    simp [Matrix.mulVec, dotProduct, e00, eprFactoryUnitary, hadamard2, bellVector,
      xorFin2, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem eprFactoryOutput_eq : outerProduct (eprFactoryUnitary *ᵥ e00) = eprFactor := by
  rw [eprFactoryUnitary_e00]
  rfl

abbrev LocalJoint (D R : ℕ) := Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ

def localBlock {D R : ℕ} (ρ : LocalJoint D R) (r r' : Fin R) : Operator D :=
  fun a b => ρ (a, r) (b, r')

theorem localBlock_trace {D R : ℕ} (ρ : LocalJoint D R) (r r' : Fin R) :
    Matrix.trace (localBlock ρ r r') = partialTraceFirst ρ r r' := by
  simp only [localBlock, Matrix.trace, partialTraceFirst, Matrix.traceLeft, Matrix.of_apply]
  rfl

noncomputable def localConj {D : ℕ} (A : Operator D) {R : ℕ} (ρ : LocalJoint D R) :
    LocalJoint D R :=
  fun p q => ∑ b : Fin D,
    (∑ a : Fin D, A p.1 a * ρ (a, p.2) (b, q.2)) * starRingEnd ℂ (A q.1 b)

noncomputable def localChannel {D : ℕ} {s : ℕ} (K : Fin s → Operator D) {R : ℕ}
    (ρ : LocalJoint D R) : LocalJoint D R :=
  ∑ k, localConj (K k) ρ

private theorem localConj_block_apply {D R : ℕ} (A : Operator D) (ρ : LocalJoint D R)
    (r r' : Fin R) (i j : Fin D) :
    (localConj A ρ) (i, r) (j, r') = (A * localBlock ρ r r' * Aᴴ) i j := by
  simp only [localBlock, localConj, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rfl

private theorem localChannel_block {D R s : ℕ} (K : Fin s → Operator D)
    (ρ : LocalJoint D R) (r r' : Fin R) :
    localBlock (localChannel K ρ) r r'
      = ∑ k, (K k) * localBlock ρ r r' * (K k)ᴴ := by
  ext a b
  simp only [localBlock, localChannel, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [localConj_block_apply]

theorem localChannel_reference_preserved {D R s : ℕ} (K : Fin s → Operator D)
    (hK : ∑ k, (K k)ᴴ * (K k) = 1) (ρ : LocalJoint D R) :
    partialTraceFirst (localChannel K ρ) = partialTraceFirst ρ := by
  ext r r'
  calc partialTraceFirst (localChannel K ρ) r r'
      = Matrix.trace (localBlock (localChannel K ρ) r r') := (localBlock_trace _ _ _).symm
    _ = Matrix.trace (∑ k, (K k) * localBlock ρ r r' * (K k)ᴴ) := by
          rw [localChannel_block]
    _ = ∑ k, Matrix.trace ((K k) * localBlock ρ r r' * (K k)ᴴ) := by
          rw [Matrix.trace_sum]
    _ = ∑ k, Matrix.trace ((K k)ᴴ * (K k) * localBlock ρ r r') := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have h1 : ((K k) * localBlock ρ r r' * (K k)ᴴ).trace
              = ((K k)ᴴ * ((K k) * localBlock ρ r r')).trace :=
            Matrix.trace_mul_comm ((K k) * localBlock ρ r r') ((K k)ᴴ)
          rw [h1, ← Matrix.mul_assoc]
    _ = Matrix.trace ((∑ k, (K k)ᴴ * (K k)) * localBlock ρ r r') := by
          calc ∑ k, Matrix.trace ((K k)ᴴ * (K k) * localBlock ρ r r')
              = ∑ k, Matrix.trace (localBlock ρ r r' * ((K k)ᴴ * (K k))) := by
                    refine Finset.sum_congr rfl fun k _ => ?_
                    exact Matrix.trace_mul_comm ((K k)ᴴ * (K k)) (localBlock ρ r r')
              _ = Matrix.trace (∑ k, localBlock ρ r r' * ((K k)ᴴ * (K k))) := by
                    rw [Matrix.trace_sum]
              _ = Matrix.trace (localBlock ρ r r' * (∑ k, (K k)ᴴ * (K k))) := by
                    rw [Finset.mul_sum]
              _ = Matrix.trace ((∑ k, (K k)ᴴ * (K k)) * localBlock ρ r r') := by
                    exact Matrix.trace_mul_comm (localBlock ρ r r')
                      (∑ k, (K k)ᴴ * (K k))
    _ = Matrix.trace (localBlock ρ r r') := by rw [hK, Matrix.one_mul]
    _ = partialTraceFirst ρ r r' := localBlock_trace _ _ _

theorem localInstrument_reference_preserved {D R s : ℕ} (K : Fin s → Operator D)
    (hK : ∑ k, (K k)ᴴ * (K k) = 1) (ρ : LocalJoint D R) :
    partialTraceFirst (∑ k, localConj (K k) ρ) = partialTraceFirst ρ := by
  ext r r'
  have hblock : localBlock (∑ k, localConj (K k) ρ) r r'
      = ∑ k, (K k) * localBlock ρ r r' * (K k)ᴴ := by
    ext a b
    simp only [localBlock, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [localConj_block_apply]
  calc partialTraceFirst (∑ k, localConj (K k) ρ) r r'
      = Matrix.trace (localBlock (∑ k, localConj (K k) ρ) r r') :=
          (localBlock_trace _ _ _).symm
    _ = Matrix.trace (∑ k, (K k) * localBlock ρ r r' * (K k)ᴴ) := by
          rw [hblock]
    _ = ∑ k, Matrix.trace ((K k) * localBlock ρ r r' * (K k)ᴴ) := by
          rw [Matrix.trace_sum]
    _ = ∑ k, Matrix.trace ((K k)ᴴ * (K k) * localBlock ρ r r') := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have h1 : ((K k) * localBlock ρ r r' * (K k)ᴴ).trace
              = ((K k)ᴴ * ((K k) * localBlock ρ r r')).trace :=
            Matrix.trace_mul_comm ((K k) * localBlock ρ r r') ((K k)ᴴ)
          rw [h1, ← Matrix.mul_assoc]
    _ = Matrix.trace ((∑ k, (K k)ᴴ * (K k)) * localBlock ρ r r') := by
          calc ∑ k, Matrix.trace ((K k)ᴴ * (K k) * localBlock ρ r r')
              = ∑ k, Matrix.trace (localBlock ρ r r' * ((K k)ᴴ * (K k))) := by
                    refine Finset.sum_congr rfl fun k _ => ?_
                    exact Matrix.trace_mul_comm ((K k)ᴴ * (K k)) (localBlock ρ r r')
              _ = Matrix.trace (∑ k, localBlock ρ r r' * ((K k)ᴴ * (K k))) := by
                    rw [Matrix.trace_sum]
              _ = Matrix.trace (localBlock ρ r r' * (∑ k, (K k)ᴴ * (K k))) := by
                    rw [Finset.mul_sum]
              _ = Matrix.trace ((∑ k, (K k)ᴴ * (K k)) * localBlock ρ r r') := by
                    exact Matrix.trace_mul_comm (localBlock ρ r r')
                      (∑ k, (K k)ᴴ * (K k))
    _ = Matrix.trace (localBlock ρ r r') := by rw [hK, Matrix.one_mul]
    _ = partialTraceFirst ρ r r' := localBlock_trace _ _ _

theorem localUnitary_reference_preserved {D R : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (ρ : LocalJoint D R) :
    partialTraceFirst (localChannel (fun _ : Fin 1 => U) ρ) = partialTraceFirst ρ := by
  refine localChannel_reference_preserved (fun _ : Fin 1 => U) ?_ ρ
  have hunit : U.conjTranspose * U = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  simp [hunit]

structure InteractiveGuess (X : Type) [Fintype X] (rounds : ℕ) where

  alice : X → (i : Fin rounds) → (bobPast : Fin i → List Bool) → List Bool

  bob : (i : Fin rounds) → (alicePast : Fin i → List Bool) → List Bool

  guess : (Fin rounds → List Bool) → (Fin rounds → List Bool) → X

def before {n : ℕ} (arr : Fin n → List Bool) (j : Fin n) : Fin j → List Bool :=
  fun k => arr (Fin.castLE (Nat.le_of_lt j.isLt) k)

private theorem before_update {n : ℕ} (arr : Fin n → List Bool) (i : Fin n) (v : List Bool)
    (j : Fin n) (hj : j.val ≤ i.val) : before (Function.update arr i v) j = before arr j := by
  funext k
  simp only [before]
  have hne : (Fin.castLE (Nat.le_of_lt j.isLt) k) ≠ i := by
    intro hc
    have h1 := congrArg Fin.val hc
    have h2 : (Fin.castLE (Nat.le_of_lt j.isLt) k).val = k.val := rfl
    simp only [h2] at h1
    omega
  simp [Function.update, hne]

noncomputable def InteractiveGuess.run {X : Type} [Fintype X] {rounds : ℕ}
    (P : InteractiveGuess X rounds) (x : X) :
    (k : ℕ) → (hk : k < rounds) → (Fin rounds → List Bool) → (Fin rounds → List Bool) →
      (Fin rounds → List Bool) × (Fin rounds → List Bool)
  | 0, _, aprev, bprev =>
      (Function.update aprev ⟨0, by omega⟩ (P.alice x ⟨0, by omega⟩ (fun _ => [])),
        Function.update bprev ⟨0, by omega⟩ (P.bob ⟨0, by omega⟩ (fun _ => [])))
  | k + 1, hk, aprev, bprev =>
      let r := P.run x k (by omega) aprev bprev
      let anew := P.alice x ⟨k + 1, hk⟩ (before r.2 ⟨k + 1, hk⟩)
      let bnew := P.bob ⟨k + 1, hk⟩ (before r.1 ⟨k + 1, hk⟩)
      (Function.update r.1 ⟨k + 1, hk⟩ anew, Function.update r.2 ⟨k + 1, hk⟩ bnew)

noncomputable def InteractiveGuess.transcript {X : Type} [Fintype X] {rounds : ℕ}
    (P : InteractiveGuess X rounds) (x : X) :
    (Fin rounds → List Bool) × (Fin rounds → List Bool) :=
  match rounds with
  | 0 => (fun _ => [], fun _ => [])
  | r + 1 => P.run x r (by omega) (fun _ => []) (fun _ => [])

theorem InteractiveGuess.run_spec {X : Type} [Fintype X] {rounds : ℕ}
    (P : InteractiveGuess X rounds) (x : X) :
    ∀ (k : ℕ) (hk : k < rounds) (aprev bprev : Fin rounds → List Bool)
      (a b : Fin rounds → List Bool),
      P.run x k hk aprev bprev = (a, b) →
      (∀ j : Fin rounds, j.val ≤ k → a j = P.alice x j (before b j)) ∧
      (∀ j : Fin rounds, j.val ≤ k → b j = P.bob j (before a j)) := by
  intro k
  induction k with
  | zero =>
      intro hk aprev bprev a b hab
      have hrun : P.run x 0 hk aprev bprev = (a, b) := hab
      simp only [InteractiveGuess.run] at hrun
      have ha : a ⟨0, hk⟩ = P.alice x ⟨0, hk⟩ (fun _ => []) := by
        have h := congrArg (fun t => t.1 ⟨0, hk⟩) hrun
        simp [Function.update] at h
        exact h.symm
      have hb : b ⟨0, hk⟩ = P.bob ⟨0, hk⟩ (fun _ => []) := by
        have h := congrArg (fun t => t.2 ⟨0, hk⟩) hrun
        simp [Function.update] at h
        exact h.symm
      constructor
      · intro j hj
        have hjval : j.val = 0 := by omega
        have hjfin : j = ⟨0, hk⟩ := Fin.ext hjval
        subst hjfin
        rw [ha]
        have hbefore : before b ⟨0, hk⟩ = (fun _ => []) := by
          funext kk
          nomatch kk
        rw [hbefore]
      · intro j hj
        have hjval : j.val = 0 := by omega
        have hjfin : j = ⟨0, hk⟩ := Fin.ext hjval
        subst hjfin
        rw [hb]
        have hbefore : before a ⟨0, hk⟩ = (fun _ => []) := by
          funext kk
          nomatch kk
        rw [hbefore]
  | succ k ih =>
      intro hk aprev bprev a b hab
      have hk' : k < rounds := by omega
      let r := P.run x k hk' aprev bprev
      have hrun_k : r = (r.1, r.2) := rfl
      have hr := ih hk' aprev bprev r.1 r.2 hrun_k
      have hrun : P.run x (k + 1) hk aprev bprev = (a, b) := hab
      have hrun' :
          (Function.update r.1 ⟨k + 1, hk⟩
              (P.alice x ⟨k + 1, hk⟩ (before r.2 ⟨k + 1, hk⟩)),
            Function.update r.2 ⟨k + 1, hk⟩
              (P.bob ⟨k + 1, hk⟩ (before r.1 ⟨k + 1, hk⟩))) = (a, b) := by
        simpa [InteractiveGuess.run, r] using hrun
      have ha_eq : a = Function.update r.1 ⟨k + 1, hk⟩
          (P.alice x ⟨k + 1, hk⟩ (before r.2 ⟨k + 1, hk⟩)) := by
        have h := congrArg Prod.fst hrun'
        simpa using h.symm
      have hb_eq : b = Function.update r.2 ⟨k + 1, hk⟩
          (P.bob ⟨k + 1, hk⟩ (before r.1 ⟨k + 1, hk⟩)) := by
        have h := congrArg Prod.snd hrun'
        simpa using h.symm
      constructor
      · intro j hj
        by_cases hjeq : j.val = k + 1
        · have hjval : j.val = (⟨k + 1, hk⟩ : Fin rounds).val := by omega
          have hjfin : j = ⟨k + 1, hk⟩ := Fin.ext hjval
          subst hjfin
          rw [ha_eq, Function.update, dif_pos rfl]
          rw [hb_eq, before_update r.2 ⟨k + 1, hk⟩ _ ⟨k + 1, hk⟩ (by rfl)]
        · have hjne : j ≠ ⟨k + 1, hk⟩ := by
            intro hc
            have h := congrArg Fin.val hc
            simp only at h
            omega
          have hja : a j = r.1 j := by
            rw [ha_eq, Function.update, dif_neg hjne]
          have hjb : before b j = before r.2 j := by
            rw [hb_eq, before_update r.2 ⟨k + 1, hk⟩ _ j (by
              show j.val ≤ k + 1
              omega)]
          rw [hja, hjb]
          exact hr.1 j (by omega)
      · intro j hj
        by_cases hjeq : j.val = k + 1
        · have hjval : j.val = (⟨k + 1, hk⟩ : Fin rounds).val := by omega
          have hjfin : j = ⟨k + 1, hk⟩ := Fin.ext hjval
          subst hjfin
          rw [hb_eq, Function.update, dif_pos rfl]
          rw [ha_eq, before_update r.1 ⟨k + 1, hk⟩ _ ⟨k + 1, hk⟩ (by rfl)]
        · have hjne : j ≠ ⟨k + 1, hk⟩ := by
            intro hc
            have h := congrArg Fin.val hc
            simp only at h
            omega
          have hjb : b j = r.2 j := by
            rw [hb_eq, Function.update, dif_neg hjne]
          have hja : before a j = before r.1 j := by
            rw [ha_eq, before_update r.1 ⟨k + 1, hk⟩ _ j (by
              show j.val ≤ k + 1
              omega)]
          rw [hjb, hja]
          exact hr.2 j (by omega)

theorem InteractiveGuess.transcript_alice {X : Type} [Fintype X] {rounds : ℕ}
    (P : InteractiveGuess X rounds) (x : X) (j : Fin rounds) :
    (P.transcript x).1 j = P.alice x j (before (P.transcript x).2 j) := by
  cases rounds with
  | zero => exact absurd j.isLt (by simp)
  | succ r =>
      let rr := P.run x r (by omega) (fun _ => []) (fun _ => [])
      have hspec := P.run_spec x r (by omega) (fun _ => []) (fun _ => []) rr.1 rr.2 (by rfl)
      have h := hspec.1 j (by omega)
      simpa [InteractiveGuess.transcript, rr] using h

theorem InteractiveGuess.transcript_bob {X : Type} [Fintype X] {rounds : ℕ}
    (P : InteractiveGuess X rounds) (x : X) (j : Fin rounds) :
    (P.transcript x).2 j = P.bob j (before (P.transcript x).1 j) := by
  cases rounds with
  | zero => exact absurd j.isLt (by simp)
  | succ r =>
      let rr := P.run x r (by omega) (fun _ => []) (fun _ => [])
      have hspec := P.run_spec x r (by omega) (fun _ => []) (fun _ => []) rr.1 rr.2 (by rfl)
      have h := hspec.2 j (by omega)
      simpa [InteractiveGuess.transcript, rr] using h

theorem InteractiveGuess.transcript_deterministic {X : Type} [Fintype X]
    {rounds : ℕ} (P : InteractiveGuess X rounds) (x y : X) (h : x = y) :
    P.transcript x = P.transcript y := by
  subst h
  rfl

def treeKraftMass : BinaryMessageTree → ℕ → ℕ
  | .leaf, C => 2 ^ C
  | .fork l r, C => treeKraftMass l (C - 1) + treeKraftMass r (C - 1)

theorem tree_kraft_le_one : ∀ (C : ℕ) (T : BinaryMessageTree), T.depth ≤ C →
    treeKraftMass T C ≤ 2 ^ C := by
  intro C
  induction C with
  | zero =>
      intro T hT
      cases T with
      | leaf => simp [treeKraftMass]
      | fork l r =>
          simp only [BinaryMessageTree.depth] at hT
          omega
  | succ C ih =>
      intro T hT
      cases T with
      | leaf => simp [treeKraftMass]
      | fork l r =>
          have hl : l.depth ≤ C := by
            simp only [BinaryMessageTree.depth] at hT
            omega
          have hr : r.depth ≤ C := by
            simp only [BinaryMessageTree.depth] at hT
            omega
          have h1 := ih l hl
          have h2 := ih r hr
          simp only [treeKraftMass, Nat.succ_sub_one]
          omega

theorem tree_leaves_prefix_free (T : BinaryMessageTree) :
    ∀ p q : T.Path, p ≠ q → ¬ List.IsPrefix (T.encode p) (T.encode q) := by
  induction T with
  | leaf =>
      intro p q hne
      cases p
      cases q
      exact (hne rfl).elim
  | fork l r ihl ihr =>
      intro p q hne
      cases p with
      | inl p =>
          cases q with
          | inl q =>
              intro hp
              obtain ⟨t, ht⟩ := hp
              have hlen := ihl p q (fun h =>
                  hne (congrArg (fun w : l.Path => (Sum.inl w : l.Path ⊕ r.Path)) h))
              exact hlen ⟨t, by simpa [BinaryMessageTree.encode] using ht⟩
          | inr q =>
              intro hp
              obtain ⟨t, ht⟩ := hp
              simp only [List.cons_append, BinaryMessageTree.encode] at ht
              cases ht
      | inr p =>
          cases q with
          | inl q =>
              intro hp
              obtain ⟨t, ht⟩ := hp
              simp only [List.cons_append, BinaryMessageTree.encode] at ht
              cases ht
          | inr q =>
              intro hp
              obtain ⟨t, ht⟩ := hp
              have hlen := ihr p q (fun h =>
                  hne (congrArg (fun w : r.Path => (Sum.inr w : l.Path ⊕ r.Path)) h))
              exact hlen ⟨t, by simpa [BinaryMessageTree.encode] using ht⟩

theorem redundant_budget (r C : ℕ) (w : List Bool) (h : w.length = C) :
    (redundantEncode r w).length = r * C := by
  rw [redundantEncode_length, h]

theorem redundant_bound_degrades (r C : ℕ) :
    (2 : ℝ) ^ (C * r) = ((2 : ℝ) ^ C) ^ r := by
  rw [pow_mul (a := (2 : ℝ)) (m := C) (n := r)]

end LocalResourceNetworkDefs
