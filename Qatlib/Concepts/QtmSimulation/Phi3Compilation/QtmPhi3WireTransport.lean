/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.Phi3Compile.FiniteBasisPhi3PaddingQuan

/-!
# Wire transport and Φ3 translation

This module translates legal one-wire and controlled-NOT reflection gates into three-wire Φ3
gates using added dummy wires. It also transports states and legal reflection programs through
arbitrary wire embeddings with a fixed exterior context, supporting the compilation framework of
[Yao1993].

## Main statements

* `qtmPhi3_translate_table`: Length-preserving translation of legal reflection tables.
* `qtmWireGateMap_context_embed`: A transported gate intertwines with context embedding.
* `qtmWireProgram_context`: The corresponding transport identity for a whole program.

## References

* [Yao, 1993][Yao1993]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitImpl.Phi3Universal

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.QtmSimulation.Phi3Compilation

open Matrix
noncomputable section

/-- For three distinct selected wires, agreement off the selection and on its two inactive wires
is equivalent to agreement off the active wire. -/
private theorem phi3Off_local {n : ℕ} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (x y : Reg n) :
    ((∀ k : Fin n, (∀ q : Fin 3, w q ≠ k) → x k = y k) ∧
      (∀ q : Fin 3, q ≠ 0 → x (w q) = y (w q))) ↔
      (∀ k : Fin n, k ≠ w 0 → x k = y k) := by
  constructor
  · rintro ⟨hoff, hlocal⟩ k hk
    by_cases hr : k ∈ Set.range w
    · obtain ⟨q, rfl⟩ := hr
      exact hlocal q (fun h => hk (congrArg w h))
    · exact hoff k (fun q hq => hr ⟨q, hq⟩)
  · intro h
    constructor
    · intro k hk
      exact h k (Ne.symm (hk 0))
    · intro q hq
      exact h (w q) (hw.ne hq)

/-- A Φ3 gate acting only on its first local wire equals the corresponding one-wire gate on the
full register. -/
private theorem phi3One_matrix {n : ℕ} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ) :
    phi3GateMatrix (⟨w, hw, wireGate 3 0 U, wireGate_unitary 3 0 U hU⟩ : Phi3Gate n) =
      wireGate n (w 0) U := by
  classical
  ext x y
  simp only [phi3GateMatrix, Matrix.of_apply, wireGate_apply]
  rw [← ite_and]
  simp only [phi3Off_local w hw]

/-- For three distinct selected wires, the local target-update condition together with exterior
agreement is equivalent to the full-register update at the target wire. -/
private theorem phi3Off_update {n : ℕ} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (x y : Reg n) (v : Bool) :
    ((∀ k : Fin n, (∀ q : Fin 3, w q ≠ k) → x k = y k) ∧
      (fun q => x (w q)) = Function.update (fun q => y (w q)) (1 : Fin 3) v) ↔
      x = Function.update y (w 1) v := by
  have hu : (fun q => Function.update y (w 1) v (w q)) =
      Function.update (fun q => y (w q)) (1 : Fin 3) v :=
    Function.update_comp_eq_of_injective' y hw 1 v
  constructor
  · rintro ⟨hoff, hlocal⟩
    funext k
    by_cases hr : k ∈ Set.range w
    · obtain ⟨q, rfl⟩ := hr
      exact (congrFun hlocal q).trans (congrFun hu q).symm
    · rw [Function.update_of_ne (fun h => hr ⟨1, h.symm⟩)]
      exact hoff k (fun q hq => hr ⟨q, hq⟩)
  · intro h
    constructor
    · intro k hk
      rw [h, Function.update_of_ne (Ne.symm (hk 1))]
    · rw [h]
      exact hu

/-- A Φ3 gate with local controlled-NOT matrix equals the full-register controlled-NOT on its
first two selected wires. -/
private theorem phi3Cnot_matrix {n : ℕ} (w : Fin 3 → Fin n) (hw : Function.Injective w) :
    phi3GateMatrix (⟨w, hw, cnotGate 3 0 1,
      cnotGate_unitary 3 0 1 (by decide)⟩ : Phi3Gate n) = cnotGate n (w 0) (w 1) := by
  classical
  ext x y
  simp only [phi3GateMatrix, cnotGate, permMatrix, Matrix.of_apply]
  rw [← ite_and]
  simp only [phi3Off_update w hw]

/-- The three-wire selection sending the local positions to `a`, `b`, and `c`. -/
private def threeWires {n : ℕ} (a b c : Fin n) : Fin 3 → Fin n := ![a, b, c]

/-- A three-wire selection is injective when its selected wires are pairwise distinct. -/
private theorem threeWires_injective {n : ℕ} (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Function.Injective (threeWires a b c) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [threeWires]

/-- The first added dummy wire in a register extended from `n` to `n + 3` wires. -/
private def dummyZero (n : ℕ) : Fin (n + 3) := ⟨n, by omega⟩
/-- The second added dummy wire in a register extended from `n` to `n + 3` wires. -/
private def dummyOne (n : ℕ) : Fin (n + 3) := ⟨n + 1, by omega⟩

/-- A data wire embedded in the prefix differs from the first added dummy wire. -/
private theorem data_ne_dummyZero {n : ℕ} (w : Fin n) :
    knownPrefixWires n 3 w ≠ dummyZero n := by
  intro h
  have hv := congrArg Fin.val h
  change w.val = n at hv
  omega

/-- A data wire embedded in the prefix differs from the second added dummy wire. -/
private theorem data_ne_dummyOne {n : ℕ} (w : Fin n) :
    knownPrefixWires n 3 w ≠ dummyOne n := by
  intro h
  have hv := congrArg Fin.val h
  change w.val = n + 1 at hv
  omega

/-- Translate a legal reflection gate into a Φ3 gate on the prefix data wires and added dummy
wires. -/
private def phi3Translate {n : ℕ} (g : ReflectionGate n) (hg : reflectionGateLegal g) : Phi3Gate (n + 3) :=
  match g with
  | .inl (w, U) =>
    { wires := threeWires (knownPrefixWires n 3 w) (dummyZero n) (dummyOne n)
      wires_inj := threeWires_injective _ _ _ (data_ne_dummyZero w) (data_ne_dummyOne w)
        (by intro h; have hv := congrArg Fin.val h; change n = n + 1 at hv; omega)
      localMatrix := wireGate 3 0 U
      localMatrix_unitary := wireGate_unitary 3 0 U hg }
  | .inr (c, t) =>
    { wires := threeWires (knownPrefixWires n 3 c) (knownPrefixWires n 3 t) (dummyZero n)
      wires_inj := threeWires_injective _ _ _ ((knownPrefixWires n 3).injective.ne hg)
        (data_ne_dummyZero c) (data_ne_dummyZero t)
      localMatrix := cnotGate 3 0 1
      localMatrix_unitary := cnotGate_unitary 3 0 1 (by decide) }

/-- The matrix of a translated Φ3 gate equals the matrix of the original reflection gate
transported to the data prefix. -/
private theorem phi3Translate_matrix {n : ℕ} (g : ReflectionGate n) (hg : reflectionGateLegal g) :
    phi3GateMatrix (phi3Translate g hg) = reflectionGateMatrix (knownWireGateMap (knownPrefixWires n 3) g) := by
  rcases g with ⟨w, U⟩ | ⟨c, t⟩
  · have h := phi3One_matrix (phi3Translate (.inl (w, U)) hg).wires
      (phi3Translate (.inl (w, U)) hg).wires_inj U hg
    simpa only [phi3Translate, threeWires, Matrix.cons_val_zero, knownWireGateMap,
      reflectionGateMatrix] using! h
  · have h := phi3Cnot_matrix (phi3Translate (.inr (c, t)) hg).wires
      (phi3Translate (.inr (c, t)) hg).wires_inj
    simpa only [phi3Translate, threeWires, Matrix.cons_val_zero, Matrix.cons_val_one,
      knownWireGateMap, reflectionGateMatrix] using! h

/-- A legal reflection list has a Φ3 translation of equal length whose compiled circuit equals
the transported reflection circuit. -/
private theorem phi3Translate_list {n : ℕ} (gs : List (ReflectionGate n)) (hgs : reflectionLegal gs) :
    ∃ ts : List (Phi3Gate (n + 3)), ts.length = gs.length ∧
      phi3Compile ts = reflectionCompile (gs.map (knownWireGateMap (knownPrefixWires n 3))) := by
  induction gs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons g gs ih =>
    have hg := hgs g List.mem_cons_self
    obtain ⟨ts, hlen, hcompile⟩ := ih (fun t ht => hgs t (List.mem_cons_of_mem _ ht))
    refine ⟨phi3Translate g hg :: ts, by simpa using! hlen, ?_⟩
    simp only [phi3Compile, List.map_cons, reflectionCompile]
    rw [phi3Translate_matrix]
    exact congrArg (List.cons _) hcompile

/-- Translate a legal reflection table to a Φ3 table with the same length and the same compiled
circuit after prefix wire transport. -/
theorem qtmPhi3_translate_table {n : ℕ} (gs : List (ReflectionGate n))
    (hgs : reflectionLegal gs) :
    ∃ ts : List (Phi3Gate (n+3)), ts.length = gs.length ∧
      phi3Compile ts = reflectionCompile (gs.map (knownWireGateMap (knownPrefixWires n 3))) :=
  phi3Translate_list gs hgs

open Qatlib
open scoped Classical BigOperators

/-- Extend a local bit assignment along a wire embedding, retaining the supplied context outside
its image. -/
def qtmWireContextExtend {a b : ℕ} (e : Fin a ↪ Fin b) (ctx : Reg b) (x : Reg a) : Reg b :=
  Function.extend e x ctx

/-- At an embedded wire `e i`, the context extension returns the local bit `x i`. -/
@[simp] theorem qtmWireContextExtend_at {a b : ℕ} (e : Fin a ↪ Fin b)
    (ctx : Reg b) (x : Reg a) (i : Fin a) : qtmWireContextExtend e ctx x (e i) = x i :=
  e.injective.extend_apply _ _ _

/-- Updating an embedded target wire commutes with extending the corresponding local update into
the fixed context. -/
theorem qtmWireContextExtend_update {a b : ℕ} (e : Fin a ↪ Fin b)
    (ctx : Reg b) (x : Reg a) (t : Fin a) (v : Bool) :
    Function.update (qtmWireContextExtend e ctx x) (e t) v =
      qtmWireContextExtend e ctx (Function.update x t v) := by
  funext j
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i,rfl⟩ := hj
    by_cases hi : i = t
    · subst i; simp
    · rw [Function.update_of_ne (fun h => hi (e.injective h)),
        qtmWireContextExtend_at, qtmWireContextExtend_at, Function.update_of_ne hi]
  · have hne : j ≠ e t := fun h => hj ⟨t,h.symm⟩
    rw [Function.update_of_ne hne]
    simp only [qtmWireContextExtend, Function.extend_apply' _ _ j hj]

/-- Embed a local state as the superposition of its context-extended basis assignments. -/
def qtmWireContextEmbed {a b : ℕ} (e : Fin a ↪ Fin b) (ctx : Reg b)
    (ψ : QState (Reg a)) : QState (Reg b) :=
  ∑ x, ψ x • Qatlib.Foundations.PureStateMath.Ket (qtmWireContextExtend e ctx x)

/-- Context embedding sends a basis state to the basis state of its context extension. -/
theorem qtmWireContextEmbed_ket {a b : ℕ} (e : Fin a ↪ Fin b)
    (ctx : Reg b) (x : Reg a) :
    qtmWireContextEmbed e ctx (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (qtmWireContextExtend e ctx x) := by
  simp [qtmWireContextEmbed, Qatlib.Foundations.PureStateMath.Ket]

/-- Context embedding commutes with complex scalar multiplication. -/
theorem qtmWireContextEmbed_smul {a b : ℕ} (e : Fin a ↪ Fin b)
    (ctx : Reg b) (z : ℂ) (ψ : QState (Reg a)) :
    qtmWireContextEmbed e ctx (z • ψ) = z • qtmWireContextEmbed e ctx ψ := by
  simp [qtmWireContextEmbed, Finset.smul_sum, smul_smul]

/-- Context embedding preserves finite sums of states. -/
theorem qtmWireContextEmbed_sum {a b : ℕ} {J : Type} [Fintype J] (e : Fin a ↪ Fin b)
    (ctx : Reg b) (ψ : J → QState (Reg a)) :
    qtmWireContextEmbed e ctx (∑ j, ψ j) = ∑ j, qtmWireContextEmbed e ctx (ψ j) := by
  simp only [qtmWireContextEmbed, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

/-- Context embedding preserves addition of states. -/
theorem qtmWireContextEmbed_add {a b : ℕ} (e : Fin a ↪ Fin b)
    (ctx : Reg b) (ψ φ : QState (Reg a)) :
    qtmWireContextEmbed e ctx (ψ+φ) =
      qtmWireContextEmbed e ctx ψ + qtmWireContextEmbed e ctx φ := by
  simp [qtmWireContextEmbed, add_smul, Finset.sum_add_distrib]

/-- Applying a transported legal reflection gate to a context-extended basis state equals
context embedding of the original gate's basis-state output. -/
theorem qtmWireGateMap_context_ket {a b : ℕ} (e : Fin a ↪ Fin b)
    (ctx : Reg b) (g : ReflectionGate a) (hg : reflectionGateLegal g) (x : Reg a) :
    ApplyGate (reflectionGateMatrix (knownWireGateMap e g)) (Qatlib.Foundations.PureStateMath.Ket (qtmWireContextExtend e ctx x)) =
      qtmWireContextEmbed e ctx (ApplyGate (reflectionGateMatrix g) (Qatlib.Foundations.PureStateMath.Ket x)) := by
  rcases g with ⟨t,U⟩ | ⟨c,t⟩
  · simp only [knownWireGateMap, reflectionGateMatrix, applyGate_wireGate_ket,
      qtmWireContextExtend_at, qtmWireContextExtend_update, qtmWireContextEmbed_add,
      qtmWireContextEmbed_smul, qtmWireContextEmbed_ket]
  · simp only [knownWireGateMap, reflectionGateMatrix]
    rw [applyGate_cnotGate_ket b (e c) (e t) (fun h => hg (e.injective h)),
      applyGate_cnotGate_ket a c t hg, qtmWireContextEmbed_ket,
      qtmWireContextExtend_at, qtmWireContextExtend_update]
    simp only [qtmWireContextExtend_at]

/-- Application of a legal reflection gate commutes with fixed-context state embedding and wire
transport. -/
theorem qtmWireGateMap_context_embed {a b : ℕ} (e : Fin a ↪ Fin b)
    (ctx : Reg b) (g : ReflectionGate a) (hg : reflectionGateLegal g) (ψ : QState (Reg a)) :
    ApplyGate (reflectionGateMatrix (knownWireGateMap e g)) (qtmWireContextEmbed e ctx ψ) =
      qtmWireContextEmbed e ctx (ApplyGate (reflectionGateMatrix g) ψ) := by
  conv_rhs => arg 3; arg 2; rw [state_ket_expansion ψ]
  simp only [ApplyGate, Matrix.mulVec_sum, Matrix.mulVec_smul, qtmWireContextEmbed_sum,
    qtmWireContextEmbed_smul]
  change reflectionGateMatrix (knownWireGateMap e g) *ᵥ
    (∑ x, ψ x • Qatlib.Foundations.PureStateMath.Ket (qtmWireContextExtend e ctx x)) = _
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul]
  apply Finset.sum_congr rfl
  intro x _
  rw [show reflectionGateMatrix (knownWireGateMap e g) *ᵥ Qatlib.Foundations.PureStateMath.Ket (qtmWireContextExtend e ctx x) =
    qtmWireContextEmbed e ctx (reflectionGateMatrix g *ᵥ Qatlib.Foundations.PureStateMath.Ket x) from
      qtmWireGateMap_context_ket e ctx g hg x]

/-- Running a transported legal reflection program on a context-embedded state equals context
embedding of the original program's output. -/
theorem qtmWireProgram_context {a b : ℕ} (e : Fin a ↪ Fin b) (ctx : Reg b)
    (gs : List (ReflectionGate a)) (hgs : reflectionLegal gs) (ψ : QState (Reg a)) :
    Run 1 (reflectionCompile (gs.map (knownWireGateMap e))) (qtmWireContextEmbed e ctx ψ) =
      qtmWireContextEmbed e ctx (Run 1 (reflectionCompile gs) ψ) := by
  induction gs generalizing ψ with
  | nil => simp [reflectionCompile]
  | cons g gs ih =>
    simp only [List.map_cons, reflectionCompile, List.map_cons, run_gate]
    rw [qtmWireGateMap_context_embed e ctx g (hgs g List.mem_cons_self)]
    exact ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg)) _

end
end Qatlib.Concepts.QtmSimulation.Phi3Compilation
