/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.RoutedWordLCUBridge
import Qatlib.Papers.Cbmd26.Algorithms.RegisterLCUBridge
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Circuit products with fresh signal registers

`FreshSignals` allocates an independent signal register to each factor of a matrix product.
`freshSignalProduct` and `freshQueryWord` realize these factors on shared system data while
routing each query through its own signal register, so compression yields the ordered product of
the encoded blocks.

`fresh_signal_product_counted` packages the resulting exact block encoding with `n` primitive
queries and `2 * n` fixed gates. `freshFlatWord` transports the construction to a
function-indexed signal register for use in the algorithms of [WangEtAl2026].

## Main statements

* `freshSignalProduct_compress`: factors compression into the ordered product of individual
  blocks.
* `fresh_signal_product_counted`: gives the exact product encoding and circuit costs.
* `fresh_flat_product_counted`: transports the counted construction to a flat signal workspace.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SharedAncilla.AncillaProduct
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.CoherentSim.TaylorEncoding

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator

/-- The recursively nested workspace of `n` independent registers of type `A`, with the empty
workspace represented by `Unit`. -/
@[reducible] def FreshSignals (A : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => A × FreshSignals A n

/-- Equality of two nonempty fresh signal workspaces is equivalent to equality of their head
registers and tails. -/
private theorem freshSignals_succ_eq_iff {A : Type} (n : ℕ) (a b : A)
    (s t : FreshSignals A n) :
    ((a, s) : FreshSignals A (n + 1)) = (b, t) ↔ a = b ∧ s = t :=
  Prod.ext_iff

instance freshSignalsFintype (A : Type) [Fintype A] : (n : ℕ) → Fintype (FreshSignals A n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => @instFintypeProd A (FreshSignals A n) _ (freshSignalsFintype A n)

instance freshSignalsDecidableEq (A : Type) [DecidableEq A] :
    (n : ℕ) → DecidableEq (FreshSignals A n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n + 1 => by
    letI := freshSignalsDecidableEq A n
    exact inferInstanceAs (DecidableEq (A × FreshSignals A n))

/-- The fresh signal workspace in which every register contains the distinguished value `a₀`. -/
def freshSignalsZero {A : Type} (a₀ : A) : (n : ℕ) → FreshSignals A n
  | 0 => ()
  | n + 1 => (a₀, freshSignalsZero a₀ n)

/-- The equivalence between recursively nested fresh signal registers and functions from `Fin n`
to `A`. -/
def freshSignalsEquiv (A : Type) : (n : ℕ) → FreshSignals A n ≃ (Fin n → A)
  | 0 => { toFun := fun _ i => Fin.elim0 i
           invFun := fun _ => ()
           left_inv := fun x => by cases x; rfl
           right_inv := fun _ => funext fun i => Fin.elim0 i }
  | n + 1 => (Equiv.prodCongr (Equiv.refl A) (freshSignalsEquiv A n)).trans
      (Fin.consEquiv (fun _ : Fin (n + 1) => A))

/-- Flattening the all-`a₀` fresh signal workspace gives the constant function with value `a₀`. -/
theorem freshSignalsEquiv_zero {A : Type} (a₀ : A) (n : ℕ) :
    freshSignalsEquiv A n (freshSignalsZero a₀ n) = fun _ => a₀ := by
  induction n with
  | zero => exact funext fun i => Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrFun ih j

variable {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]

/-- The ordered product of lifted matrices, each acting on its own fresh signal register and the
common system register. -/
def freshSignalProduct : (n : ℕ) →
    (Fin n → Matrix (A × I) (A × I) ℂ) →
    Matrix (FreshSignals A n × I) (FreshSignals A n × I) ℂ
  | 0, _ => 1
  | n + 1, U => independentLiftLeft (U 0) *
      independentLiftRight (freshSignalProduct n (fun j => U j.succ))

/-- The ordered matrix product with the factor at index zero on the left, and the identity for
zero factors. -/
def orderedBlockProduct : (n : ℕ) → (Fin n → Matrix I I ℂ) → Matrix I I ℂ
  | 0, _ => 1
  | n + 1, B => B 0 * orderedBlockProduct n (fun j => B j.succ)

/-- Compressing the product of two lifts on independent signal registers equals the product of
their separate compressions. -/
theorem freshSignalProduct_step_compress (a₀ : A) (n : ℕ)
    (U : Matrix (A × I) (A × I) ℂ)
    (V : Matrix (FreshSignals A n × I) (FreshSignals A n × I) ℂ) :
    compress (encodingFiber (a₀, freshSignalsZero a₀ n))
      (independentLiftLeft U * independentLiftRight V)
      (encodingFiber (a₀, freshSignalsZero a₀ n)) =
    compress (encodingFiber a₀) U (encodingFiber a₀) *
      compress (encodingFiber (freshSignalsZero a₀ n)) V
        (encodingFiber (freshSignalsZero a₀ n)) :=
  (independent_ancilla_lift_laws a₀ (freshSignalsZero a₀ n) U V).2.2.2.2

/-- Compression of a fresh signal product in the all-`a₀` fiber equals the ordered product of
the individually compressed factors. -/
theorem freshSignalProduct_compress (a₀ : A) (n : ℕ)
    (U : Fin n → Matrix (A × I) (A × I) ℂ) :
    compress (encodingFiber (freshSignalsZero a₀ n)) (freshSignalProduct n U)
      (encodingFiber (freshSignalsZero a₀ n)) =
      orderedBlockProduct n (fun j => compress (encodingFiber a₀) (U j)
        (encodingFiber a₀)) := by
  induction n with
  | zero =>
    ext i j
    simp [freshSignalProduct, orderedBlockProduct, compress_encodingFiber_eq,
      Matrix.one_apply]
  | succ n ih =>
    change compress (encodingFiber (a₀, freshSignalsZero a₀ n))
      (independentLiftLeft (U 0) *
        independentLiftRight (freshSignalProduct n (fun j => U j.succ)))
      (encodingFiber (a₀, freshSignalsZero a₀ n)) = _
    exact (freshSignalProduct_step_compress a₀ n (U 0)
      (freshSignalProduct n (fun j => U j.succ))).trans
      (congrArg (fun B => compress (encodingFiber a₀) (U 0) (encodingFiber a₀) * B)
        (ih (fun j => U j.succ)))

/-- A fresh signal product is unitary when each of its factor matrices is unitary. -/
theorem freshSignalProduct_unitary (n : ℕ)
    (U : Fin n → Matrix (A × I) (A × I) ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (A × I) ℂ) :
    freshSignalProduct n U ∈ Matrix.unitaryGroup (FreshSignals A n × I) ℂ := by
  induction n with
  | zero => exact (Matrix.unitaryGroup _ ℂ).one_mem
  | succ n ih =>
    exact (Matrix.unitaryGroup _ ℂ).mul_mem (independentLiftLeft_unitary (hU 0))
      (independentLiftRight_unitary (ih (fun j => U j.succ) (fun j => hU j.succ)))

section QueryWord
variable {J : Type} [Fintype J] [DecidableEq J]

/-- The workspace containing the fresh signal registers, a control bit, an address register, a
scratch signal register, and the system. -/
abbrev FreshQueryWorkspace (A J I : Type) (n : ℕ) :=
  FreshSignals A n × (Bool × (J × (A × I)))

/-- The routing map that swaps the first fresh signal with the scratch signal, swaps the
distinguished and selected addresses, and flips the control bit when active. -/
def freshHeadRoute (j₀ j : J) (active : Bool) (n : ℕ) :
    FreshQueryWorkspace A J I (n + 1) → FreshQueryWorkspace A J I (n + 1) :=
  fun x => ((x.2.2.2.1, x.1.2),
    (if active then !x.2.1 else x.2.1, taylorSwapAddr j₀ j x.2.2.1, (x.1.1, x.2.2.2.2)))

omit [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I] [Fintype J] in

/-- Applying the head routing map twice returns the original workspace. -/
theorem freshHeadRoute_involutive (j₀ j : J) (active : Bool) (n : ℕ) :
    Function.Involutive (freshHeadRoute (A := A) (I := I) j₀ j active n) := by
  rintro ⟨⟨a, t⟩, b, k, s, i⟩
  cases active <;> cases b <;>
    simp only [freshHeadRoute, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, taylorSwapAddr_involutive j₀ j k]

/-- The word consisting of a forward primitive query conjugated by the head routing permutation. -/
def freshHeadWord (j₀ j : J) (active : Bool) (n : ℕ) :
    List (AdjointStep (FreshQueryWorkspace A J I (n + 1))) :=
  [.gate (permMatrix (freshHeadRoute j₀ j active n)), .forward,
    .gate (permMatrix (freshHeadRoute j₀ j active n))]

/-- The lift of a shorter fresh-query word that leaves one additional signal register as a
spectator. -/
def freshTailWord (n : ℕ)
    (cs : List (AdjointStep (FreshQueryWorkspace A J I n))) :
    List (AdjointStep (FreshQueryWorkspace A J I (n + 1))) :=
  reindexAdjointWord (Equiv.prodAssoc A (FreshSignals A n) (Bool × (J × (A × I))))
    (spectatorLiftWord A cs)

/-- The recursive query word applying each chosen address through a separate fresh signal
register, with an activity bit for each factor. -/
def freshQueryWord (j₀ : J) : (n : ℕ) → (Fin n → Bool × J) →
    List (AdjointStep (FreshQueryWorkspace A J I n))
  | 0, _ => []
  | n + 1, choices => freshHeadWord j₀ (choices 0).2 (choices 0).1 n ++
      freshTailWord n (freshQueryWord j₀ n (fun k => choices k.succ))

/-- The controlled selected oracle acting in parallel over all fresh signal registers. -/
def freshPrimitiveQuery (n : ℕ) (U : J → Matrix (A × I) (A × I) ℂ) :
    Matrix (FreshQueryWorkspace A J I n) (FreshQueryWorkspace A J I n) ℂ :=
  parallelOracle (controlOracle (select U))

omit [Fintype A] [Fintype I] [Fintype J] in

/-- The fresh-query word with `n` choices uses exactly `n` queries and `2 * n` fixed gates. -/
theorem freshQueryWord_cost (j₀ : J) (n : ℕ) (choices : Fin n → Bool × J) :
    adjointQueryCount (freshQueryWord (A := A) (I := I) j₀ n choices) = n ∧
    adjointGateCount (freshQueryWord (A := A) (I := I) j₀ n choices) = 2 * n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    simp only [freshQueryWord, adjointQueryCount_append, adjointGateCount_append,
      freshHeadWord, adjointQueryCount, adjointGateCount, freshTailWord,
      (reindexAdjointWord_cost _ _).1, (reindexAdjointWord_cost _ _).2,
      (spectatorLiftWord_cost _ _).1, (spectatorLiftWord_cost _ _).2,
      (ih (fun k => choices k.succ)).1, (ih (fun k => choices k.succ)).2]
    constructor <;> omega

/-- Every fresh-query word is well formed. -/
theorem freshQueryWord_wellFormed (j₀ : J) (n : ℕ) (choices : Fin n → Bool × J) :
    WellFormedAdjointCircuit (freshQueryWord (A := A) (I := I) j₀ n choices) := by
  induction n with
  | zero => exact Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil
  | succ n ih =>
    apply Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append
    · simp only [freshHeadWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
        Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
      have hp := permMatrix_unitary
        (freshHeadRoute_involutive (A := A) (I := I) j₀ (choices 0).2 (choices 0).1 n)
      exact ⟨hp, hp⟩
    · exact reindexAdjointWord_wellFormed _ (spectatorLiftWord_wellFormed A
        (ih (fun k => choices k.succ)))

/-- The fresh primitive query is unitary whenever every selected input oracle is unitary. -/
theorem freshPrimitiveQuery_unitary (n : ℕ) (U : J → Matrix (A × I) (A × I) ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (A × I) ℂ) :
    freshPrimitiveQuery n U ∈ Matrix.unitaryGroup (FreshQueryWorkspace A J I n) ℂ :=
  select_unitary _ (fun _ => controlOracle_unitary (select_unitary U hU))

/-- The embedding that fixes the control to false, the address to `j₀`, and the scratch signal
to `a₀`, while retaining the fresh signals and system. -/
def freshScratchFrame (j₀ : J) (a₀ : A) (n : ℕ) :
    Matrix (FreshQueryWorkspace A J I n) (FreshSignals A n × I) ℂ :=
  fun x y => if x = (y.1, false, j₀, a₀, y.2) then 1 else 0

/-- Multiplication on the right by the scratch frame selects the matrix column with the fixed
scratch registers. -/
private theorem mul_freshScratchFrame (j₀ : J) (a₀ : A) (n : ℕ)
    (M : Matrix (FreshQueryWorkspace A J I n) (FreshQueryWorkspace A J I n) ℂ)
    (x : FreshQueryWorkspace A J I n) (y : FreshSignals A n × I) :
    (M * freshScratchFrame (I := I) j₀ a₀ n) x y = M x (y.1, false, j₀, a₀, y.2) := by
  simp [Matrix.mul_apply, freshScratchFrame, mul_ite]

omit [Fintype J] in

/-- Multiplication on the left by the scratch frame embeds a matrix on the fixed
scratch-register fiber and is zero off that fiber. -/
private theorem freshScratchFrame_mul {O : Type} (j₀ : J) (a₀ : A) (n : ℕ)
    (V : Matrix (FreshSignals A n × I) O ℂ)
    (x : FreshQueryWorkspace A J I n) (y : O) :
    (freshScratchFrame (I := I) j₀ a₀ n * V) x y =
      if x.2.1 = false ∧ x.2.2.1 = j₀ ∧ x.2.2.2.1 = a₀
      then V (x.1, x.2.2.2.2) y else 0 := by
  rcases x with ⟨s, b, j, a, i⟩
  cases b <;> by_cases hj : j = j₀ <;> by_cases ha : a = a₀
  · have hs : ∀ z : FreshSignals A n × I,
        freshScratchFrame (I := I) j₀ a₀ n (s, false, j, a, i) z =
          if z = (s, i) then 1 else 0 := by
      intro ⟨t, k⟩
      simp only [freshScratchFrame, Prod.mk.injEq, hj, ha, true_and]
      congr 1
      exact propext (and_congr eq_comm eq_comm)
    simp only [Matrix.mul_apply, hs]
    rw [sum_fiber_mul_left]
    simp [hj, ha]
  all_goals simp_all [Matrix.mul_apply, freshScratchFrame, Prod.mk.injEq]

/-- The scratch-register embedding is an isometry. -/
theorem freshScratchFrame_isometry (j₀ : J) (a₀ : A) (n : ℕ) :
    IsIsometry (freshScratchFrame (I := I) j₀ a₀ n) := by
  unfold IsIsometry
  ext ⟨s, i⟩ ⟨t, k⟩
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, freshScratchFrame,
    Matrix.one_apply, eq_comm]

/-- Conjugation by the permutation matrix of an involution reindexes both matrix arguments by
that involution. -/
private theorem fresh_perm_conjugate {X : Type} [Fintype X] [DecidableEq X]
    (σ : X → X) (hσ : Function.Involutive σ) (M : Matrix X X ℂ) (x y : X) :
    (permMatrix σ * M * permMatrix σ) x y = M (σ x) (σ y) := by
  have hx (z : X) : x = σ z ↔ z = σ x := by
    constructor
    · intro h
      rw [h, hσ]
    · intro h
      rw [h, hσ]
  simp [Matrix.mul_apply, permMatrix, hx, mul_ite, ite_mul]

omit [Fintype J] in

/-- The address swap sends `k` to `j` exactly when `k` is the distinguished address `j₀`. -/
private theorem fresh_swap_addr_fiber (j₀ j k : J) :
    taylorSwapAddr j₀ j k = j ↔ k = j₀ := by
  have he : taylorSwapAddr j₀ j j₀ = j := by simp [taylorSwapAddr]
  calc
    _ ↔ taylorSwapAddr j₀ j k = taylorSwapAddr j₀ j j₀ := by rw [he]
    _ ↔ k = j₀ := (taylorSwapAddr_involutive j₀ j).injective.eq_iff

/-- On the fixed scratch-register frame, the head word applies the selected oracle to the first
fresh signal when active and applies the identity otherwise. -/
theorem freshHeadWord_scratch (j₀ j : J) (a₀ : A) (active : Bool) (n : ℕ)
    (U : J → Matrix (A × I) (A × I) ℂ) :
    evaluate (freshPrimitiveQuery (n + 1) U) (freshHeadWord j₀ j active n) *
        freshScratchFrame (I := I) j₀ a₀ (n + 1) =
      freshScratchFrame (I := I) j₀ a₀ (n + 1) *
        independentLiftLeft (K := FreshSignals A n) (if active then U j else 1) := by
  ext ⟨⟨a, t⟩, b, k, s, i⟩ ⟨⟨a', t'⟩, i'⟩
  rw [mul_freshScratchFrame, freshScratchFrame_mul]
  simp only [freshHeadWord, evaluate, instructionMatrix, Matrix.mul_one,
    ← Matrix.mul_assoc]
  rw [fresh_perm_conjugate _ (freshHeadRoute_involutive j₀ j active n)]
  simp only [freshPrimitiveQuery, parallelOracle, controlOracle, select, freshHeadRoute,
    Matrix.of_apply, independentLiftLeft]
  have hbase : taylorSwapAddr j₀ j j₀ = j := by simp [taylorSwapAddr]
  simp only [hbase]
  cases active <;> cases b <;> by_cases hk : k = j₀ <;>
    by_cases hs : s = a₀ <;> by_cases ht : t = t' <;>
    simp [fresh_swap_addr_fiber, Matrix.one_apply, Prod.mk.injEq,
      freshSignals_succ_eq_iff n, hk, hs, ht, hbase]

/-- Evaluating the lifted tail word equals the independent right lift of the original word's
evaluation. -/
private theorem freshTailWord_evaluate (n : ℕ)
    (U : J → Matrix (A × I) (A × I) ℂ)
    (cs : List (AdjointStep (FreshQueryWorkspace A J I n))) :
    evaluate (freshPrimitiveQuery (n + 1) U) (freshTailWord n cs) =
      independentLiftRight (J := A) (evaluate (freshPrimitiveQuery n U) cs) := by
  let e := Equiv.prodAssoc A (FreshSignals A n) (Bool × (J × (A × I)))
  have hQ : (parallelOracle (J := A) (freshPrimitiveQuery n U)).submatrix e e =
      freshPrimitiveQuery (n + 1) U := by
    ext ⟨⟨a, t⟩, c⟩ ⟨⟨a', t'⟩, c'⟩
    by_cases ha : a = a' <;> by_cases ht : t = t' <;>
      simp [e, Equiv.prodAssoc, freshPrimitiveQuery, parallelOracle, select,
          freshSignals_succ_eq_iff n, ha, ht]
  rw [← hQ, freshTailWord, reindexAdjointWord_evaluate, spectatorLiftWord_evaluate]
  ext ⟨⟨a, t⟩, c⟩ ⟨⟨a', t'⟩, c'⟩
  by_cases ha : a = a' <;> simp [e, Equiv.prodAssoc, parallelOracle, select, independentLiftRight, ha]

/-- An intertwining identity on the scratch frame remains valid after adding a spectator signal
register. -/
private theorem freshTailWord_scratch (j₀ : J) (a₀ : A) (n : ℕ)
    (M : Matrix (FreshQueryWorkspace A J I n) (FreshQueryWorkspace A J I n) ℂ)
    (V : Matrix (FreshSignals A n × I) (FreshSignals A n × I) ℂ)
    (hM : M * freshScratchFrame (I := I) j₀ a₀ n = freshScratchFrame (I := I) j₀ a₀ n * V) :
    independentLiftRight (J := A) M * freshScratchFrame (I := I) j₀ a₀ (n + 1) =
      freshScratchFrame (I := I) j₀ a₀ (n + 1) * independentLiftRight (J := A) V := by
  ext ⟨⟨a, t⟩, b, k, s, i⟩ ⟨⟨a', t'⟩, i'⟩
  have hh := congrFun (congrFun hM (t, b, k, s, i)) (t', i')
  rw [mul_freshScratchFrame, freshScratchFrame_mul] at hh
  rw [mul_freshScratchFrame j₀ a₀ (n + 1) (independentLiftRight (J := A) M),
    freshScratchFrame_mul j₀ a₀ (n + 1)]
  simp only [independentLiftRight, Matrix.of_apply]
  rw [hh]
  by_cases ha : a = a' <;> by_cases hc : b = false ∧ k = j₀ ∧ s = a₀ <;>
    simp [ha, hc]

/-- On the fixed scratch frame, the fresh-query word acts as the fresh signal product of the
active selected oracles, with identities at inactive positions. -/
theorem freshQueryWord_scratch (j₀ : J) (a₀ : A) (n : ℕ)
    (choices : Fin n → Bool × J) (U : J → Matrix (A × I) (A × I) ℂ) :
    evaluate (freshPrimitiveQuery n U) (freshQueryWord j₀ n choices) *
        freshScratchFrame (I := I) j₀ a₀ n =
      freshScratchFrame (I := I) j₀ a₀ n *
        freshSignalProduct n (fun k => if (choices k).1 then U (choices k).2 else 1) := by
  induction n with
  | zero => simp [freshQueryWord, evaluate, freshSignalProduct]
  | succ n ih =>
    have ht := freshTailWord_scratch j₀ a₀ n
      (evaluate (freshPrimitiveQuery n U) (freshQueryWord j₀ n (fun k => choices k.succ)))
      (freshSignalProduct n (fun k => if (choices k.succ).1 then U (choices k.succ).2 else 1))
      (ih (fun k => choices k.succ))
    rw [freshQueryWord, evaluate_append, freshTailWord_evaluate, Matrix.mul_assoc, ht,
      ← Matrix.mul_assoc, freshHeadWord_scratch, Matrix.mul_assoc]
    rfl

/-- The system embedding fixing every fresh signal to `a₀` together with the scratch registers
specified by `freshScratchFrame`. -/
def freshWordFrame (j₀ : J) (a₀ : A) (n : ℕ) :
    Matrix (FreshQueryWorkspace A J I n) I ℂ :=
  freshScratchFrame (I := I) j₀ a₀ n * encodingFiber (freshSignalsZero a₀ n)

/-- The system embedding into the initialized fresh-query workspace is an isometry. -/
theorem freshWordFrame_isometry (j₀ : J) (a₀ : A) (n : ℕ) :
    IsIsometry (freshWordFrame (I := I) j₀ a₀ n) :=
  Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul (freshScratchFrame_isometry j₀ a₀ n) (encodingFiber_isIsometry _)

/-- Compressing a fresh-query word gives the ordered product of the active selected-oracle
blocks, with identity factors at inactive positions. -/
theorem freshQueryWord_compress (j₀ : J) (a₀ : A) (n : ℕ)
    (choices : Fin n → Bool × J) (U : J → Matrix (A × I) (A × I) ℂ) :
    compress (freshWordFrame j₀ a₀ n)
      (evaluate (freshPrimitiveQuery n U) (freshQueryWord j₀ n choices))
      (freshWordFrame j₀ a₀ n) =
      orderedBlockProduct n (fun k =>
        if (choices k).1 then compress (encodingFiber a₀) (U (choices k).2)
          (encodingFiber a₀) else 1) := by
  let S := freshScratchFrame (I := I) j₀ a₀ n
  let F := encodingFiber (I := I) (freshSignalsZero a₀ n)
  let W := evaluate (freshPrimitiveQuery n U) (freshQueryWord j₀ n choices)
  let V := freshSignalProduct n (fun k => if (choices k).1 then U (choices k).2 else 1)
  have hS : Sᴴ * S = 1 := freshScratchFrame_isometry j₀ a₀ n
  have hW : W * S = S * V := freshQueryWord_scratch j₀ a₀ n choices U
  have hcorner : compress (S * F) W (S * F) = compress F V F := by
    unfold compress
    rw [Matrix.conjTranspose_mul]
    calc
      Fᴴ * Sᴴ * W * (S * F) = Fᴴ * Sᴴ * (W * S) * F := by
        simp only [Matrix.mul_assoc]
      _ = Fᴴ * (Sᴴ * S) * V * F := by rw [hW]; simp only [Matrix.mul_assoc]
      _ = Fᴴ * V * F := by rw [hS, Matrix.mul_one]
  change compress (S * F) W (S * F) = _
  rw [hcorner]
  change compress (encodingFiber (freshSignalsZero a₀ n))
    (freshSignalProduct n (fun k => if (choices k).1 then U (choices k).2 else 1))
    (encodingFiber (freshSignalsZero a₀ n)) = _
  rw [freshSignalProduct_compress]
  congr 1
  funext k
  cases (choices k).1
  · simpa [compress] using! (encodingFiber_isIsometry (I := I) a₀)
  · rfl

/-- Exact projected unitary encodings of the input blocks induce an exact projected unitary
encoding of their active ordered product through the fresh-query word. -/
theorem freshQueryWord_projectedEncoding (j₀ : J) (a₀ : A) (n : ℕ)
    (choices : Fin n → Bool × J) (B : J → Matrix I I ℂ)
    (U : J → Matrix (A × I) (A × I) ℂ)
    (henc : ∀ j, ProjectedUnitaryEncoding (B j) (U j) (encodingFiber a₀) (encodingFiber a₀)) :
    ProjectedUnitaryEncoding
      (orderedBlockProduct n (fun k => if (choices k).1 then B (choices k).2 else 1))
      (evaluate (freshPrimitiveQuery n U) (freshQueryWord j₀ n choices))
      (freshWordFrame j₀ a₀ n) (freshWordFrame j₀ a₀ n) := by
  refine ⟨(freshQueryWord_wellFormed j₀ n choices).evaluate_unitary
    (freshPrimitiveQuery_unitary n U (fun j => (henc j).unitary)),
    freshWordFrame_isometry j₀ a₀ n, freshWordFrame_isometry j₀ a₀ n, ?_⟩
  rw [freshQueryWord_compress]
  congr 1
  funext k
  rw [(henc (choices k).2).encoded]

/-- Exact projected encodings yield a well-formed fresh-query word and a unitary primitive
oracle encoding the active ordered block product with scale one and zero error. The word
uses `n` queries and `2 * n` fixed gates. -/
theorem fresh_signal_product_counted (j₀ : J) (a₀ : A) (n : ℕ)
    (choices : Fin n → Bool × J) (B : J → Matrix I I ℂ)
    (U : J → Matrix (A × I) (A × I) ℂ)
    (henc : ∀ j, ProjectedUnitaryEncoding (B j) (U j) (encodingFiber a₀) (encodingFiber a₀)) :
    WellFormedAdjointCircuit (freshQueryWord (A := A) (I := I) j₀ n choices) ∧
    freshPrimitiveQuery n U ∈ Matrix.unitaryGroup (FreshQueryWorkspace A J I n) ℂ ∧
    BlockEncoding
      (orderedBlockProduct n (fun k => if (choices k).1 then B (choices k).2 else 1))
      (evaluate (freshPrimitiveQuery n U) (freshQueryWord j₀ n choices))
      (freshWordFrame j₀ a₀ n) (freshWordFrame j₀ a₀ n) 1 0 ∧
    adjointQueryCount (freshQueryWord (A := A) (I := I) j₀ n choices) = n ∧
    adjointGateCount (freshQueryWord (A := A) (I := I) j₀ n choices) = 2 * n :=
  ⟨freshQueryWord_wellFormed j₀ n choices,
    freshPrimitiveQuery_unitary n U (fun j => (henc j).unitary),
    (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding (freshQueryWord_projectedEncoding j₀ a₀ n choices B U henc)),
    freshQueryWord_cost j₀ n choices⟩

/-- The equivalence replacing a function-indexed signal workspace by recursively nested fresh
signal registers. -/
def freshFlatWorkspaceEquiv (n : ℕ) :
    ((Fin n → A) × (Bool × (J × (A × I)))) ≃ FreshQueryWorkspace A J I n :=
  Equiv.prodCongr (freshSignalsEquiv A n).symm (Equiv.refl _)

/-- The fresh-query word transported to a workspace whose signal registers are indexed by
functions on `Fin n`. -/
def freshFlatWord (j₀ : J) (n : ℕ) (choices : Fin n → Bool × J) :
    List (AdjointStep ((Fin n → A) × (Bool × (J × (A × I))))) :=
  reindexAdjointWord (freshFlatWorkspaceEquiv n) (freshQueryWord j₀ n choices)

omit [Fintype A] [Fintype I] [Fintype J] in

/-- Reindexing the fresh primitive query to the flat signal workspace gives the controlled
selected oracle with the signal function as a spectator. -/
theorem freshFlatPrimitiveQuery_eq (n : ℕ) (U : J → Matrix (A × I) (A × I) ℂ) :
    (freshPrimitiveQuery n U).submatrix (freshFlatWorkspaceEquiv n)
      (freshFlatWorkspaceEquiv n) =
      parallelOracle (J := Fin n → A) (controlOracle (select U)) := by
  ext ⟨s, c⟩ ⟨t, d⟩
  change (if (freshSignalsEquiv A n).symm s = (freshSignalsEquiv A n).symm t
    then controlOracle (select U) c d else 0) =
      if s = t then controlOracle (select U) c d else 0
  simp only [(freshSignalsEquiv A n).symm.injective.eq_iff]

/-- The flat fresh-query word is well formed and exactly block-encodes the active ordered
product with scale one in the reindexed frame. It uses `n` queries and `2 * n` fixed gates. -/
theorem fresh_flat_product_counted (j₀ : J) (a₀ : A) (n : ℕ)
    (choices : Fin n → Bool × J) (B : J → Matrix I I ℂ)
    (U : J → Matrix (A × I) (A × I) ℂ)
    (henc : ∀ j, ProjectedUnitaryEncoding (B j) (U j) (encodingFiber a₀) (encodingFiber a₀)) :
    WellFormedAdjointCircuit (freshFlatWord (A := A) (I := I) j₀ n choices) ∧
    BlockEncoding
      (orderedBlockProduct n (fun k => if (choices k).1 then B (choices k).2 else 1))
      (evaluate (parallelOracle (J := Fin n → A) (controlOracle (select U)))
        (freshFlatWord j₀ n choices))
      (reindexFrame (freshFlatWorkspaceEquiv n) (freshWordFrame j₀ a₀ n))
      (reindexFrame (freshFlatWorkspaceEquiv n) (freshWordFrame j₀ a₀ n)) 1 0 ∧
    adjointQueryCount (freshFlatWord (A := A) (I := I) j₀ n choices) = n ∧
    adjointGateCount (freshFlatWord (A := A) (I := I) j₀ n choices) = 2 * n := by
  refine ⟨reindexAdjointWord_wellFormed _ (freshQueryWord_wellFormed j₀ n choices), ?_, ?_⟩
  · rw [← freshFlatPrimitiveQuery_eq n U, freshFlatWord, reindexAdjointWord_evaluate]
    exact reindexWorkspace_blockEncoding _ _ _ _ 1 0
      (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding (freshQueryWord_projectedEncoding j₀ a₀ n choices B U henc))
  · simpa only [freshFlatWord, (reindexAdjointWord_cost _ _).1,
      (reindexAdjointWord_cost _ _).2] using!
      freshQueryWord_cost (A := A) (I := I) j₀ n choices

end QueryWord
end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
