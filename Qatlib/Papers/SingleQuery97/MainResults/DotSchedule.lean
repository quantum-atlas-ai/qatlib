/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SingleQuery97.MainResults.DatabaseDefs
public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-!
# Parallel reversible dot-product reduction

Section I of arXiv:quant-ph/9705041v4 describes parallel Toffoli products
and XOR reduction. Construct the two operations at the leaves and parent
nodes of a balanced tree. The two disjoint workspaces of a parallel
operation are represented by the two components of its product type.
-/

set_option autoImplicit false

open scoped BigOperators
open Qatlib.Papers.SingleQuery97.MainResults.DatabaseDefs
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Papers.SingleQuery97.MainResults

/-- A reversible Boolean instruction with the same action in both directions. -/
structure DotGate (S : Type) where
  /-- The action on a basis label. -/
  act : S → S
  /-- Every primitive is its own inverse. -/
  involutive : Function.Involutive act

/-- Lift a gate to the left component of two disjoint registers. -/
def DotGate.left {S T : Type} (g : DotGate S) : DotGate (S × T) :=
  ⟨fun w => (g.act w.1, w.2), fun w => Prod.ext (g.involutive w.1) rfl⟩

/-- Lift a gate to the right component of two disjoint registers. -/
def DotGate.right {S T : Type} (g : DotGate T) : DotGate (S × T) :=
  ⟨fun w => (w.1, g.act w.2), fun w => Prod.ext rfl (g.involutive w.2)⟩

/-- The execution of a list of reversible primitives in time order. -/
def runDotGates {S : Type} (gs : List (DotGate S)) (s : S) : S :=
  gs.foldl (fun w g => g.act w) s

/-- Sequential execution of concatenated lists. -/
theorem runDotGates_append {S : Type} (gs hs : List (DotGate S)) (s : S) :
    runDotGates (gs ++ hs) s = runDotGates hs (runDotGates gs s) := by
  simp only [runDotGates, List.foldl_append]

private theorem run_left {S T : Type} (gs : List (DotGate S)) (s : S) (t : T) :
    runDotGates (gs.map DotGate.left) (s, t) = (runDotGates gs s, t) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih => exact ih (g.act s)

private theorem run_right {S T : Type} (gs : List (DotGate T)) (s : S) (t : T) :
    runDotGates (gs.map DotGate.right) (s, t) = (s, runDotGates gs t) := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih => exact ih (g.act t)

/-- A schedule of primitive instructions with explicit sequential and disjoint
parallel composition. -/
inductive DotNetwork : Type → Type 1
  | idle {S : Type} : DotNetwork S
  | gate {S : Type} (g : DotGate S) : DotNetwork S
  | seq {S : Type} (p q : DotNetwork S) : DotNetwork S
  | par {S T : Type} (p : DotNetwork S) (q : DotNetwork T) : DotNetwork (S × T)

/-- The sequential instruction list of a network. -/
def DotNetwork.emit {S : Type} : DotNetwork S → List (DotGate S)
  | .idle => []
  | .gate g => [g]
  | .seq p q => p.emit ++ q.emit
  | .par p q => p.emit.map DotGate.left ++ q.emit.map DotGate.right

/-- Parallel depth, counting a disjoint composition by the longer of its two depths. -/
def DotNetwork.depth {S : Type} : DotNetwork S → ℕ
  | .idle => 0
  | .gate _ => 1
  | .seq p q => p.depth + q.depth
  | .par p q => max p.depth q.depth

/-- Executing the two disjoint branches of the emitted list applies each branch to its own
register and gives exactly the parallel operation. -/
theorem DotNetwork.run_par {S T : Type} (p : DotNetwork S) (q : DotNetwork T) (s : S) (t : T) :
    runDotGates (DotNetwork.par p q).emit (s, t) = (runDotGates p.emit s, runDotGates q.emit t) := by
  simp only [DotNetwork.emit, runDotGates_append, run_left, run_right]

/-- Invert a schedule by reversing its sequential stages and each of its disjoint branches. -/
def DotNetwork.inverse {S : Type} : DotNetwork S → DotNetwork S
  | .idle => .idle
  | .gate g => .gate g
  | .seq p q => .seq q.inverse p.inverse
  | .par p q => .par p.inverse q.inverse

/-- The inverse schedule uncomputes the forward schedule on every basis label. -/
theorem DotNetwork.run_inverse {S : Type} (p : DotNetwork S) (s : S) :
    runDotGates p.inverse.emit (runDotGates p.emit s) = s := by
  induction p with
  | idle => rfl
  | gate g => exact g.involutive s
  | seq p q hp hq =>
      simp only [DotNetwork.inverse, DotNetwork.emit, runDotGates_append, hq, hp]
  | par p q hp hq =>
      obtain ⟨x, y⟩ := s
      simp only [DotNetwork.inverse, DotNetwork.run_par, hp, hq]

/-- Inversion preserves the scheduled parallel depth. -/
theorem DotNetwork.depth_inverse {S : Type} (p : DotNetwork S) : p.inverse.depth = p.depth := by
  induction p with
  | idle => rfl
  | gate => rfl
  | seq p q hp hq => simp only [DotNetwork.inverse, DotNetwork.depth, hp, hq, Nat.add_comm]
  | par p q hp hq => simp only [DotNetwork.inverse, DotNetwork.depth, hp, hq]

/-- Inversion preserves the number of emitted primitives. -/
theorem DotNetwork.count_inverse {S : Type} (p : DotNetwork S) :
    p.inverse.emit.length = p.emit.length := by
  induction p with
  | idle => rfl
  | gate => rfl
  | seq p q hp hq =>
      simp only [DotNetwork.inverse, DotNetwork.emit, List.length_append, hp, hq, Nat.add_comm]
  | par p q hp hq =>
      simp only [DotNetwork.inverse, DotNetwork.emit, List.length_append, List.length_map, hp, hq]

/-- Each leaf stores its two input bits and one work bit. A node partitions its leaves into two
equal disjoint blocks. -/
abbrev DotWork : ℕ → Type
  | 0 => ZMod 2 × ZMod 2 × ZMod 2
  | h + 1 => DotWork h × DotWork h

instance instFintypeDotWork (h : ℕ) : Fintype (DotWork h) := by
  induction h with
  | zero => change Fintype (ZMod 2 × ZMod 2 × ZMod 2); infer_instance
  | succ h ih =>
      letI : Fintype (DotWork h) := ih
      change Fintype (DotWork h × DotWork h)
      infer_instance

instance instDecidableEqDotWork (h : ℕ) : DecidableEq (DotWork h) := by
  induction h with
  | zero => change DecidableEq (ZMod 2 × ZMod 2 × ZMod 2); infer_instance
  | succ h ih =>
      letI : DecidableEq (DotWork h) := ih
      change DecidableEq (DotWork h × DotWork h)
      infer_instance

/-- The leftmost work bit stores the aggregate at each node. -/
def dotRoot : (h : ℕ) → DotWork h → ZMod 2
  | 0, w => w.2.2
  | h + 1, w => dotRoot h w.1

/-- Toggle the node's leftmost work bit. -/
def toggleDotRoot : (h : ℕ) → ZMod 2 → DotWork h → DotWork h
  | 0, x, w => (w.1, w.2.1, w.2.2 + x)
  | h + 1, x, w => (toggleDotRoot h x w.1, w.2)

private theorem bit_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

/-- Adding the same bit twice restores the root register. -/
theorem toggleDotRoot_involutive (h : ℕ) (x : ZMod 2) :
    Function.Involutive (toggleDotRoot h x) := by
  induction h with
  | zero =>
      rintro ⟨u, v, s⟩
      change (u, v, (s + x) + x) = (u, v, s)
      rw [add_assoc, bit_add_self, add_zero]
  | succ h ih =>
      rintro ⟨a, b⟩
      exact Prod.ext (ih a) rfl

private theorem dotRoot_toggle (h : ℕ) (x : ZMod 2) (w : DotWork h) :
    dotRoot h (toggleDotRoot h x w) = dotRoot h w + x := by
  induction h with
  | zero => rfl
  | succ h ih => exact ih w.1

/-- The leaf Toffoli writes the product to a zero work bit. -/
def dotLeafGate : DotGate (DotWork 0) :=
  ⟨fun w => toggleDotRoot 0 (w.1 * w.2.1) w,
    by
      rintro ⟨x, y, s⟩
      change (x, y, (s + x * y) + x * y) = (x, y, s)
      rw [add_assoc, bit_add_self, add_zero]⟩

/-- The parent CNOT adds the right root bit to the left root bit. -/
def dotJoinGate (h : ℕ) : DotGate (DotWork (h + 1)) :=
  ⟨fun w => (toggleDotRoot h (dotRoot h w.2) w.1, w.2),
    fun w => Prod.ext (toggleDotRoot_involutive h _ w.1) rfl⟩

/-- Compute leaf products in parallel, then combine each pair of subtree parities with one CNOT. -/
def dotNetwork : (h : ℕ) → DotNetwork (DotWork h)
  | 0 => .gate dotLeafGate
  | h + 1 => .seq (.par (dotNetwork h) (dotNetwork h)) (.gate (dotJoinGate h))

/-- One Toffoli layer and one XOR layer at each of the subsequent tree levels. -/
theorem dotNetwork_depth (h : ℕ) : (dotNetwork h).depth = h + 1 := by
  induction h with
  | zero => rfl
  | succ h ih => simp only [dotNetwork, DotNetwork.depth, ih, max_self]

/-- A complete tree emits one primitive at each leaf and each internal node. -/
theorem dotNetwork_count (h : ℕ) : (dotNetwork h).emit.length = 2 * 2 ^ h - 1 := by
  induction h with
  | zero => rfl
  | succ h ih =>
      have hp : 0 < (2 : ℕ) ^ h := by positivity
      let gs : List (DotGate (DotWork (h + 1))) :=
        (DotNetwork.par (dotNetwork h) (dotNetwork h)).emit
      change (gs ++ [dotJoinGate h]).length = _
      simp only [gs, DotNetwork.emit, List.length_append, List.length_map, List.length_cons, List.length_nil, ih,
        pow_succ]
      omega

/-- The split of a complete leaf set into its two contiguous halves. -/
def dotSplit (h : ℕ) : Fin (2 ^ h) ⊕ Fin (2 ^ h) ≃ Fin (2 ^ (h + 1)) :=
  finSumFinEquiv.trans (finCongr (by rw [pow_succ, Nat.mul_two]))

/-- Load a pair of vectors into the leaves with all work bits clear. -/
def dotInput : (h : ℕ) → (Fin (2 ^ h) → ZMod 2) → (Fin (2 ^ h) → ZMod 2) → DotWork h
  | 0, x, y => (x 0, y 0, 0)
  | h + 1, x, y =>
      (dotInput h (fun j => x (dotSplit h (.inl j))) (fun j => y (dotSplit h (.inl j))),
       dotInput h (fun j => x (dotSplit h (.inr j))) (fun j => y (dotSplit h (.inr j))))

/-- The emitted network writes the binary dot product into the root work bit. -/
theorem dotNetwork_root (h : ℕ) (x y : Fin (2 ^ h) → ZMod 2) :
    dotRoot h (runDotGates (dotNetwork h).emit (dotInput h x y)) = ∑ j, x j * y j := by
  induction h with
  | zero =>
      change 0 + x 0 * y 0 = _
      simp
  | succ h ih =>
      let gs : List (DotGate (DotWork (h + 1))) :=
        (DotNetwork.par (dotNetwork h) (dotNetwork h)).emit
      change dotRoot (h + 1) (runDotGates (gs ++ [dotJoinGate h])
        (dotInput (h + 1) x y)) = _
      rw [runDotGates_append]
      simp only [dotInput, gs, DotNetwork.run_par]
      change dotRoot h (toggleDotRoot h (dotRoot h (runDotGates _ _)) (runDotGates _ _)) = _
      rw [dotRoot_toggle]
      rw [ih, ih]
      have hsum := Equiv.sum_comp (dotSplit h) (fun j => x j * y j)
      simpa only [Fintype.sum_sum_type, Function.comp_def] using hsum

/-- Copy the computed parity to the answer using a CNOT. -/
def copyDotRoot (h : ℕ) : DotGate (DotWork h × ZMod 2) :=
  ⟨fun s => (s.1, s.2 + dotRoot h s.1),
    by rintro ⟨w, b⟩; simp only [add_assoc, bit_add_self, add_zero]⟩

/-- Compute the reduction, copy its root to the answer, and reverse the reduction. -/
def cleanDotNetwork (h : ℕ) : DotNetwork (DotWork h × ZMod 2) :=
  .seq (.par (dotNetwork h) .idle)
    (.seq (.gate (copyDotRoot h)) (.par (dotNetwork h).inverse .idle))

/-- The clean word preserves both operands and restores all the work bits to zero. -/
theorem cleanDotGates_run (h : ℕ) (x y : Fin (2 ^ h) → ZMod 2) (b : ZMod 2) :
    runDotGates (cleanDotNetwork h).emit (dotInput h x y, b) =
      (dotInput h x y, b + ∑ j, x j * y j) := by
  change runDotGates
    ((DotNetwork.par (dotNetwork h) (.idle : DotNetwork (ZMod 2))).emit ++
      ([copyDotRoot h] ++ (DotNetwork.par (dotNetwork h).inverse (.idle : DotNetwork (ZMod 2))).emit))
    (dotInput h x y, b) = _
  rw [runDotGates_append, runDotGates_append]
  rw [DotNetwork.run_par (dotNetwork h) (.idle : DotNetwork (ZMod 2)) (dotInput h x y) b]
  change runDotGates (DotNetwork.par (dotNetwork h).inverse (.idle : DotNetwork (ZMod 2))).emit
    (runDotGates (dotNetwork h).emit (dotInput h x y),
      b + dotRoot h (runDotGates (dotNetwork h).emit (dotInput h x y))) = _
  rw [DotNetwork.run_par, DotNetwork.run_inverse, dotNetwork_root]
  rfl

/-- Each reversible primitive is emitted as its permutation matrix on the basis labels. -/
noncomputable def dotToCircuit {S : Type} [DecidableEq S]
    (gs : List (DotGate S)) : Circuit S :=
  gs.map (fun g => Step.gate (permMatrix g.act))

/-- The emitted fixed-gate word is unitary and contains no oracle-query instruction. -/
theorem dotToCircuit_valid {S : Type} [Fintype S] [DecidableEq S] (gs : List (DotGate S)) :
    IsUnitaryCircuit (dotToCircuit gs) ∧ QueryCount (dotToCircuit gs) = 0 ∧
      GateCount (dotToCircuit gs) = gs.length := by
  induction gs with
  | nil => exact ⟨isUnitaryCircuit_nil, rfl, rfl⟩
  | cons g gs ih =>
      rcases ih with ⟨hu, hq, hg⟩
      exact ⟨(isUnitaryCircuit_gate _ _).mpr ⟨permMatrix_unitary g.involutive, hu⟩,
        hq, congrArg (· + 1) hg⟩

/-- Executing the emitted quantum word on a ket agrees with reversible basis execution. -/
theorem dotToCircuit_run {S : Type} [Fintype S] [DecidableEq S] (gs : List (DotGate S)) (s : S) :
    Run 1 (dotToCircuit gs) (Ket s) = Ket (runDotGates gs s) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
      simp only [dotToCircuit, List.map_cons, run_gate, applyGate_permMatrix_ket g.involutive]
      exact ih (g.act s)

/-- Extend a bit vector with zeros on the unused leaves of the balanced tree. -/
def padDotBits {n m : ℕ} (x : Fin n → ZMod 2) (j : Fin m) : ZMod 2 :=
  if hj : j.val < n then x ⟨j.val, hj⟩ else 0

private theorem sum_padded_dot {n m : ℕ} (h : n ≤ m) (x y : Fin n → ZMod 2) :
    (∑ j : Fin m, padDotBits x j * padDotBits y j) = ∑ j, x j * y j := by
  let s := (Finset.univ : Finset (Fin n)).map (Fin.castLEEmb h)
  have hsubset : s ⊆ (Finset.univ : Finset (Fin m)) := Finset.subset_univ _
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin m)), j ∉ s →
      padDotBits x j * padDotBits y j = 0 := by
    intro j _ hj
    have hnot : ¬j.val < n := by
      intro hjn
      apply hj
      apply Finset.mem_map.mpr
      exact ⟨⟨j.val, hjn⟩, Finset.mem_univ _, Fin.ext rfl⟩
    simp [padDotBits, hnot]
  rw [← Finset.sum_subset hsubset hzero]
  simp only [s, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro j _
  simp [padDotBits, Fin.castLEEmb, j.isLt]

/-- Place the original database and query bits at the occupied leaves, padding
the remaining leaves to the next power of two. -/
def directDotInput {n : ℕ} (x y : DbVec n) : DotWork (Nat.clog 2 n) :=
  dotInput (Nat.clog 2 n) (padDotBits (fun j => (bitVal (x j) : ZMod 2)))
    (padDotBits (fun j => (bitVal (y j) : ZMod 2)))

/-- The direct binary database word from the typed balanced network. -/
noncomputable def directDotCircuit (n : ℕ) :
    Circuit (DotWork (Nat.clog 2 n) × ZMod 2) :=
  dotToCircuit (cleanDotNetwork (Nat.clog 2 n)).emit

/-- The clean circuit implements the source dot-product answer modulo two on every input,
with the original database, query, and every work bit restored. -/
theorem directDotCircuit_run {n : ℕ} (x y : DbVec n) (b : ZMod 2) :
    Run 1 (directDotCircuit n) (Ket (directDotInput x y, b)) =
      Ket (directDotInput x y, b + (dot x y : ZMod 2)) := by
  rw [directDotCircuit, dotToCircuit_run]
  unfold directDotInput
  rw [cleanDotGates_run, sum_padded_dot (Nat.le_pow_clog (by decide : 1 < 2) n)]
  simp only [dot, Nat.cast_sum, Nat.cast_mul]

/-- The clean implementation charges its actual emitted gates and the forward network has
logarithmic parallel depth, including for vectors whose length is not a power of two. -/
theorem directDotCircuit_resources (n : ℕ) :
    IsUnitaryCircuit (directDotCircuit n) ∧ QueryCount (directDotCircuit n) = 0 ∧
      GateCount (directDotCircuit n) = 4 * 2 ^ Nat.clog 2 n - 1 ∧
      (dotNetwork (Nat.clog 2 n)).depth = Nat.clog 2 n + 1 := by
  obtain ⟨hu, hq, hg⟩ := dotToCircuit_valid (cleanDotNetwork (Nat.clog 2 n)).emit
  refine ⟨hu, hq, hg.trans ?_, dotNetwork_depth _⟩
  have hp : 0 < (2 : ℕ) ^ Nat.clog 2 n := by positivity
  have hc := DotNetwork.count_inverse (dotNetwork (Nat.clog 2 n))
  simp only [cleanDotNetwork, DotNetwork.emit, List.length_append, List.length_map, List.length_cons,
    List.length_nil, hc, dotNetwork_count]
  omega

/-- The complete clean schedule, including the reverse reduction, has logarithmic depth. -/
theorem directDotCircuit_depth (n : ℕ) :
    (cleanDotNetwork (Nat.clog 2 n)).depth = 2 * Nat.clog 2 n + 3 := by
  simp only [cleanDotNetwork, DotNetwork.depth, DotNetwork.depth_inverse, Nat.max_zero,
    dotNetwork_depth]
  omega

/-- Padding to the next power of two preserves a linear primitive count for positive inputs. -/
theorem directDotCircuit_linear {n : ℕ} (hn : 0 < n) :
    GateCount (directDotCircuit n) ≤ 8 * n := by
  rw [(directDotCircuit_resources n).2.2.1]
  by_cases h : n = 1
  · subst n
    simp
  · have hn' : 1 < n := by omega
    have hc := Nat.clog_pos (by decide : 1 < 2) hn'
    have hpow : (2 : ℕ) ^ Nat.clog 2 n = 2 ^ (Nat.clog 2 n - 1) * 2 := by
      conv_lhs => rw [← Nat.sub_add_cancel hc, pow_succ]
    have hp : (2 : ℕ) ^ (Nat.clog 2 n - 1) < n := by
      simpa only [Nat.pred_eq_sub_one] using Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hn'
    omega

end Qatlib.Papers.SingleQuery97.MainResults
