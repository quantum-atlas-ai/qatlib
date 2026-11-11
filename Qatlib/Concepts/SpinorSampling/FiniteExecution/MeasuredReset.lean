/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.FiniteExecution.ElementaryReadout
import Qatlib.Concepts.StoppingCore.InterruptBridge.QuerySpaceExtensions

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Measured cleanup preserving unmeasured quantum storage

Actual HT⁴H corrections clear the measured coordinates, including every
spectator, while preserving coherence on any omitted retained spin.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Concepts.SpinorSampling.FiniteExecution.MeasuredReset
open Qatlib
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
open Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge
/-- Four actual T primitives are exactly the existing Pauli-Z matrix, including its phase. -/
theorem paid_tgate_four : tGate*tGate*tGate*tGate=PauliZ := by
  unfold tGate Rz PauliZ
  rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext b
  cases b with
  | false => simp
  | true =>
    simp only [ite_true]
    rw [← Complex.exp_add,← Complex.exp_add,← Complex.exp_add]
    have he : ((Real.pi/4 : ℝ) : ℂ)*Complex.I+((Real.pi/4 : ℝ) : ℂ)*Complex.I+
        ((Real.pi/4 : ℝ) : ℂ)*Complex.I+((Real.pi/4 : ℝ) : ℂ)*Complex.I=(Real.pi : ℂ)*Complex.I := by
      push_cast
      ring
    rw [he,Complex.exp_pi_mul_I]

/-- A measured-one qubit is cleared by six paid native H/T gates; no X primitive is introduced. -/
def measuredXWord (n : ℕ) (w : Fin n) : List (MeasurementGate n) :=
  [.native (.h w),.native (.t w),.native (.t w),.native (.t w),.native (.t w),.native (.h w)]

/-- This is the actual existing native compilation of the six-gate reset correction. -/
def measuredXProgram (n : ℕ) (w : Fin n) : Circuit (Reg n) := measurementProgram (measuredXWord n w)

/-- The complete-register six-gate word equals the exact existing X action, without free spectator relocation. -/
theorem measuredXProgram_run (n : ℕ) (w : Fin n) (ψ : QState (Reg n)) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (measuredXProgram n w) ψ =
      ApplyGate (wireGate n w PauliX) ψ := by
  change ApplyGate (wireGate n w Hadamard) (ApplyGate (wireGate n w tGate)
    (ApplyGate (wireGate n w tGate) (ApplyGate (wireGate n w tGate)
      (ApplyGate (wireGate n w tGate) (ApplyGate (wireGate n w Hadamard) ψ))))) = _
  rw [← applyGate_mul,wireGate_mul,← applyGate_mul,wireGate_mul,
    ← applyGate_mul,wireGate_mul,← applyGate_mul,wireGate_mul,← applyGate_mul,wireGate_mul]
  have hm : Hadamard*tGate*tGate*tGate*tGate*Hadamard=PauliX := by
    calc _ = Hadamard*(tGate*tGate*tGate*tGate)*Hadamard := by simp only [Matrix.mul_assoc]
         _ = _ := by rw [paid_tgate_four,hadamard_z_conjugation]
  rw [hm]

/-- The actual correction always costs six elementary gates and no target queries. -/
theorem measuredXProgram_counts (n : ℕ) (w : Fin n) :
    GateCount (measuredXProgram n w)=6 ∧ QueryCount (measuredXProgram n w)=0 := by
  have he := measurement_program_counts (measuredXWord n w)
  exact ⟨he.2,he.1⟩

/-- The full-register X word flips exactly the measured wire on every basis state and preserves all other wires. -/
theorem measuredXProgram_basis (n : ℕ) (w : Fin n) (x : Reg n) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (measuredXProgram n w)
      (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x w (!(x w))) := by
  rw [measuredXProgram_run,applyGate_wireGate_ket]
  cases hx : x w <;> simp [PauliX,permMatrix]

/-- A reset correction is skipped on measured zero and uses the actual six-gate word on measured one. -/
def measuredResetProgram (n : ℕ) (w : Fin n) (outcome : Bool) : Circuit (Reg n) :=
  if outcome then measuredXProgram n w else []

/-- The actual measured correction clears its selected wire and preserves every spectator basis bit. -/
theorem measuredResetProgram_basis (n : ℕ) (w : Fin n) (x : Reg n) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (measuredResetProgram n w (x w))
      (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x w false) := by
  cases hx : x w with
  | false =>
    simp only [measuredResetProgram,Bool.false_eq_true,ite_false,Run]
    congr 1
    funext k
    by_cases hk : k=w
    · subst k; simp [hx]
    · simp [Function.update,hk]
  | true =>
    simp only [measuredResetProgram,ite_true]
    rw [measuredXProgram_basis]
    simp only [hx,Bool.not_true]

/-- The actual correction costs zero or six native gates according to the measured bit and never queries an input target. -/
theorem measuredResetProgram_counts (n : ℕ) (w : Fin n) (outcome : Bool) :
    GateCount (measuredResetProgram n w outcome)=(if outcome then 6 else 0) ∧
    QueryCount (measuredResetProgram n w outcome)=0 ∧
    GateCount (measuredResetProgram n w outcome)≤6 := by
  have h := measuredXProgram_counts n w
  cases outcome <;> simp [measuredResetProgram,h.1,h.2]

/-- Clear only the classically measured wires, leaving every omitted wire untouched. -/
def measuredClearBits {n : ℕ} : List (Fin n) → Reg n → Reg n
  | [], x => x
  | w::ws, x => measuredClearBits ws (Function.update x w false)

/-- The reset circuit uses the observed classical bits and the actual conditional native correction. -/
def measuredClearProgram {n : ℕ} : List (Fin n) → Reg n → Circuit (Reg n)
  | [], _ => []
  | w::ws, x => measuredResetProgram n w (x w) ++
      measuredClearProgram ws (Function.update x w false)

/-- Executing the concrete corrections clears exactly the measured basis wires. -/
theorem measuredClearProgram_basis {n : ℕ} (ws : List (Fin n)) (x : Reg n) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (measuredClearProgram ws x)
      (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (measuredClearBits ws x) := by
  induction ws generalizing x with
  | nil => rfl
  | cons w ws ih =>
    rw [measuredClearProgram, run_append, measuredResetProgram_basis]
    exact ih _

/-- Every reset word pays at most six elementary gates per measured wire and no target queries. -/
theorem measuredClearProgram_counts {n : ℕ} (ws : List (Fin n)) (x : Reg n) :
    GateCount (measuredClearProgram ws x) ≤ 6*ws.length ∧
      QueryCount (measuredClearProgram ws x)=0 := by
  induction ws generalizing x with
  | nil => exact ⟨by simp [measuredClearProgram],rfl⟩
  | cons w ws ih =>
    have h := ih (Function.update x w false)
    have hc := measuredResetProgram_counts n w (x w)
    rw [measuredClearProgram, gateCount_append, queryCount_append]
    exact ⟨by simpa only [List.length_cons] using (by omega :
      GateCount (measuredResetProgram n w (x w))+
        GateCount (measuredClearProgram ws (Function.update x w false))≤6*(ws.length+1)),
      by rw [hc.2.1,h.2]⟩

/-- Resetting classically observed wires commutes with changing an omitted retained-spin bit. -/
theorem measuredClearBits_retained {n : ℕ} (ws : List (Fin n)) (k : Fin n)
    (hk : k ∉ ws) (x : Reg n) (b : Bool) :
    measuredClearBits ws (Function.update x k b) =
      Function.update (measuredClearBits ws x) k b := by
  induction ws generalizing x with
  | nil => rfl
  | cons w ws ih =>
    have hkw : k≠w := by intro h; exact hk (by simp [h])
    have hks : k∉ws := by intro h; exact hk (List.mem_cons_of_mem w h)
    simp only [measuredClearBits]
    rw [Function.update_comm hkw,ih hks]

/-- The actual reset instructions are independent of the unknown bit on an omitted storage wire. -/
theorem measuredClearProgram_retained {n : ℕ} (ws : List (Fin n)) (k : Fin n)
    (hk : k ∉ ws) (x : Reg n) (b : Bool) :
    measuredClearProgram ws (Function.update x k b)=measuredClearProgram ws x := by
  induction ws generalizing x with
  | nil => rfl
  | cons w ws ih =>
    have hkw : k≠w := by intro h; exact hk (by simp [h])
    have hks : k∉ws := by intro h; exact hk (List.mem_cons_of_mem w h)
    simp only [measuredClearProgram,Function.update_of_ne (Ne.symm hkw)]
    rw [Function.update_comm hkw,ih hks]

/-- Circuit execution distributes over a finite sum of full-register states. -/
theorem measuredClear_run_sum {n : ℕ} {A : Type*} [Fintype A]
    (C : Circuit (Reg n)) (f : A → QState (Reg n)) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) C (∑ a, f a) =
      ∑ a, Run (1 : Matrix (Reg n) (Reg n) ℂ) C (f a) := by
  induction C generalizing f with
  | nil => rfl
  | cons s C ih =>
    have hg (U : Matrix (Reg n) (Reg n) ℂ) :
        ApplyGate U (∑ a, f a) = ∑ a, ApplyGate U (f a) := by
      simp only [ApplyGate,Matrix.mulVec_sum]
    cases s <;> simp only [Run,hg,ih]

/-- The measured reset preserves an arbitrary unknown retained spin, including its coherence and scalar weight. -/
theorem measuredClearProgram_quantum_retained {n : ℕ} (ws : List (Fin n))
    (k : Fin n) (hk : k∉ws) (x : Reg n) (u : Bool → ℂ) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (measuredClearProgram ws x)
      (∑ b : Bool, u b • Qatlib.Foundations.PureStateMath.Ket
        (Function.update x k b)) =
      ∑ b : Bool, u b • Qatlib.Foundations.PureStateMath.Ket
        (Function.update (measuredClearBits ws x) k b) := by
  rw [measuredClear_run_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Qatlib.Concepts.StoppingCore.InterruptBridge.run_smul]
  rw [← measuredClearProgram_retained ws k hk x b,measuredClearProgram_basis,
    measuredClearBits_retained ws k hk x b]


/-- The actual sequence of measured corrections clears precisely its listed coordinates. -/
theorem measuredClearBits_apply {n : ℕ} (ws : List (Fin n)) (x : Reg n) (k : Fin n) :
    measuredClearBits ws x k = if k∈ws then false else x k := by
  induction ws generalizing x with
  | nil => simp [measuredClearBits]
  | cons w ws ih =>
    rw [measuredClearBits,ih]
    by_cases hkw : k=w
    · subst k
      simp
    · simp [List.mem_cons,hkw]

/-- Physical wires are enumerated in increasing order with the retained storage slot filtered out. -/
def retainedCleanupWires {n : ℕ} (k : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun w => w != k)

/-- The first retained spin is never among the cleanup measurements or corrections. -/
theorem retainedCleanupWires_omits {n : ℕ} (k : Fin n) : k∉retainedCleanupWires k := by
  simp [retainedCleanupWires]

/-- Cleanup really clears every spectator while leaving a known-zero baseline on the retained wire. -/
theorem retainedCleanupBits_zero {n : ℕ} (k : Fin n) (x : Reg n) (hx : x k=false) :
    measuredClearBits (retainedCleanupWires k) x=(fun _ => false) := by
  funext w
  rw [measuredClearBits_apply]
  by_cases hw : w=k
  · subst w
    simp [retainedCleanupWires,hx]
  · simp [retainedCleanupWires,hw]



/-- The actual computational measurement event fixes exactly its listed physical bits and leaves every omitted wire unobserved. -/
def measuredMaskMatrix {n : ℕ} (ws : List (Fin n)) (x : Reg n) :
    Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal (fun q => if ∀ w∈ws,q w=x w then 1 else 0)

/-- The measurement event is the literal diagonal restriction, without conditional renormalization. -/
theorem measuredMaskMatrix_apply {n : ℕ} (ws : List (Fin n)) (x : Reg n)
    (φ : QState (Reg n)) (q : Reg n) :
    ApplyGate (measuredMaskMatrix ws x) φ q =
      if ∀ w∈ws,q w=x w then φ q else 0 := by
  simp [measuredMaskMatrix,ApplyGate,Matrix.mulVec,dotProduct,Matrix.diagonal_apply]

/-- Each computational-mask event is its own Kraus effect. -/
theorem measuredMaskMatrix_effect {n : ℕ} (ws : List (Fin n)) (x : Reg n) :
    (measuredMaskMatrix ws x).conjTranspose*measuredMaskMatrix ws x=measuredMaskMatrix ws x := by
  unfold measuredMaskMatrix
  rw [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
  congr 1
  funext q
  split_ifs <;> simp_all

/-- Measuring known spectator bits before their corrections preserves the arbitrary unmeasured retained spin and its exact scalar weight. -/
theorem measuredMaskMatrix_quantum_retained {n : ℕ} (ws : List (Fin n))
    (k : Fin n) (hk : k∉ws) (x : Reg n) (u : Bool → ℂ) :
    ApplyGate (measuredMaskMatrix ws x)
      (∑ b : Bool,u b • Ket (Function.update x k b)) =
      ∑ b : Bool,u b • Ket (Function.update x k b) := by
  funext q
  rw [measuredMaskMatrix_apply]
  by_cases hq : ∀ w∈ws,q w=x w
  · rw [ite_eq_left hq]
  · rw [ite_eq_right hq]
    symm
    have he (b : Bool) : Ket (Function.update x k b) q=(0 : ℂ) := by
      have hn : q≠Function.update x k b := by
        intro eq
        apply hq
        intro w hw
        have hwk : w≠k := by intro eq; subst w; exact hk hw
        rw [eq,Function.update_of_ne hwk]
      simp [Qatlib.Foundations.PureStateMath.Ket,hn]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,he,mul_zero,Finset.sum_const_zero]


end Qatlib.Concepts.SpinorSampling.FiniteExecution.MeasuredReset
