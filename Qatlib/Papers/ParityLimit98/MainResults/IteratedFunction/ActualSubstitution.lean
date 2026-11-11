/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ParityLimit98.MainResults.IteratedFunction.ParityIterateReduction
import Qatlib.Papers.ParityLimit98.MainResults.LowerBound.PhysicalReadout
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationProtocol

/-!
# Oracle substitution for hard permutations

`hardPermutation` combines an input-dependent answer-bit flip with a known cyclic address shift.
Its oracle factors into one bit-oracle query followed by `knownShift`, and `substituteForward`
implements this replacement while preserving query count and unitarity, enabling the
iteration-to-parity reduction in [FarhiEtAl1998].

## Main statements

* `hardOracle_factor`: the hard permutation oracle factors into the known shift and the bit
  oracle.
* `hardOracle_substitution`: the substituted bit-oracle circuit has exactly the original
  hard-oracle behavior.

## References

* [Farhi et al., 1998][FarhiEtAl1998]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ParityLimit98.MainResults.IteratedFunction
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Papers.ParityLimit98.MainResults.LowerBound

/-- The cyclic successor permutation on `Fin N`, obtained from addition by one modulo nonzero
`N`. -/
def cycleNext (N : ℕ) [NeZero N] : Fin N ≃ Fin N :=
  (zmodEquivFin N).trans ((Equiv.addRight (1 : ZMod N)).trans (zmodEquivFin N).symm)

/-- The reversible transformation keeping the address and replacing the answer bit by its
exclusive-or with `f` at that address. -/
def bitFlipEquiv {N : ℕ} (f : Fin N → Bool) : (Fin N × Bool) ≃ (Fin N × Bool) where
  toFun := BitFlip f
  invFun := BitFlip f
  left_inv := by
    rintro ⟨x,b⟩
    cases h : f x <;> cases b <;> simp [BitFlip,h]
  right_inv := by
    rintro ⟨x,b⟩
    cases h : f x <;> cases b <;> simp [BitFlip,h]

/-- The permutation that flips the answer bit according to `f` and then advances the address
cyclically. -/
def hardPermutation {N : ℕ} [NeZero N] (f : Fin N → Bool) :
    (Fin N × Bool) ≃ (Fin N × Bool) :=
  (bitFlipEquiv f).trans ((cycleNext N).prodCongr (Equiv.refl Bool))

/-- The hard permutation sends `(x, b)` to `(cycleNext N x, b ^^ f x)`. -/
theorem hardPermutation_apply {N : ℕ} [NeZero N] (f : Fin N → Bool) (x : Fin N) (b : Bool) :
    hardPermutation f (x,b) = (cycleNext N x, b ^^ f x) := rfl

/-- The matrix of the composite equivalence `e.trans d` is `permMatrix d * permMatrix e`. -/
theorem permutation_trans_matrix {H : Type} [Fintype H] [DecidableEq H] (e d : H ≃ H) :
    permMatrix (e.trans d) = permMatrix d * permMatrix e := by
  have hs : ∀ ψ : QState H, ApplyGate (permMatrix (e.trans d)) ψ =
      ApplyGate (permMatrix d * permMatrix e) ψ := by
    intro ψ
    funext x
    rw [applyGate_mul, qudit_perm_apply, qudit_perm_apply, qudit_perm_apply]
    rfl
  ext x y
  simpa only [applyGate_eq_mulVec_ket] using congrFun (hs (Ket y)) x

/-- The workspace-extended permutation matrix advancing the address cyclically while preserving
the answer bit. -/
def knownShift (N : ℕ) [NeZero N] (W : Type) [Fintype W] [DecidableEq W] :
    Matrix (PolynomialWorkspace (Fin N) W) (PolynomialWorkspace (Fin N) W) ℂ :=
  TensorGate (permMatrix ((cycleNext N).prodCongr (Equiv.refl Bool))) 1

/-- The workspace-extended permutation oracle associated with `hardPermutation f`. -/
def hardOracle {N : ℕ} [NeZero N] {W : Type} [Fintype W] [DecidableEq W]
    (f : Fin N → Bool) : Matrix (PolynomialWorkspace (Fin N) W) (PolynomialWorkspace (Fin N) W) ℂ :=
  TensorGate (permMatrix (hardPermutation f)) 1

/-- The hard permutation oracle equals the known cyclic shift applied after the
workspace-extended bit oracle. -/
theorem hardOracle_factor {N : ℕ} [NeZero N] {W : Type} [Fintype W] [DecidableEq W]
    (f : Fin N → Bool) :
    hardOracle (W := W) f = knownShift N W * TensorGate (BitOracleOn f) 1 := by
  unfold hardOracle hardPermutation knownShift
  rw [permutation_trans_matrix, tensorGate_mul, Matrix.one_mul]
  rfl

/-- The known cyclic shift belongs to the unitary group. -/
theorem knownShift_unitary (N : ℕ) [NeZero N] (W : Type) [Fintype W] [DecidableEq W] :
    knownShift N W ∈ Matrix.unitaryGroup (PolynomialWorkspace (Fin N) W) ℂ :=
  tensorGate_unitary (qudit_equiv_perm_unitary _) (Matrix.unitaryGroup W ℂ).one_mem

/-- The hard permutation oracle belongs to the unitary group. -/
theorem hardOracle_unitary {N : ℕ} [NeZero N] {W : Type} [Fintype W] [DecidableEq W]
    (f : Fin N → Bool) :
    hardOracle (W := W) f ∈ Matrix.unitaryGroup (PolynomialWorkspace (Fin N) W) ℂ :=
  tensorGate_unitary (qudit_equiv_perm_unitary _) (Matrix.unitaryGroup W ℂ).one_mem

/-- The circuit transformation inserting gate `K` immediately after every query and preserving
all existing gates. -/
def substituteForward {H : Type} (K : Matrix H H ℂ) : Circuit H → Circuit H
  | [] => []
  | Step.gate U :: C => Step.gate U :: substituteForward K C
  | Step.query :: C => Step.query :: Step.gate K :: substituteForward K C

/-- Running the substituted circuit with oracle `O` equals running the original circuit with
oracle `K * O`. -/
theorem substituteForward_run {H : Type} [Fintype H] [DecidableEq H]
    (O K : Matrix H H ℂ) (C : Circuit H) (ψ : QState H) :
    Run O (substituteForward K C) ψ = Run (K * O) C ψ := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s <;> simp only [substituteForward, Run, ih, applyGate_mul]

/-- Substitution preserves the query count and increases the gate count by exactly the original
query count. See [FarhiEtAl1998]. -/
theorem substituteForward_cost {H : Type} (K : Matrix H H ℂ) (C : Circuit H) :
    QueryCount (substituteForward K C) = QueryCount C ∧
      GateCount (substituteForward K C) = GateCount C + QueryCount C := by
  induction C with
  | nil => exact ⟨rfl,rfl⟩
  | cons s C ih =>
    cases s <;> simp [substituteForward, QueryCount, GateCount, ih.1, ih.2,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Inserting a unitary gate after every query preserves the property of being a unitary
circuit. -/
theorem substituteForward_unitary {H : Type} [Fintype H] [DecidableEq H]
    (K : Matrix H H ℂ) (hK : K ∈ Matrix.unitaryGroup H ℂ)
    (C : Circuit H) (hC : IsUnitaryCircuit C) : IsUnitaryCircuit (substituteForward K C) := by
  induction C with
  | nil => exact hC
  | cons s C ih =>
    have ht : IsUnitaryCircuit C := fun U hU => hC U (List.mem_cons_of_mem s hU)
    cases s with
    | gate U =>
      intro V hV
      rcases List.mem_cons.mp hV with heq | hV
      · cases heq
        exact hC U (List.mem_cons_self)
      · exact ih ht V hV
    | query =>
      intro V hV
      simp only [substituteForward, List.mem_cons] at hV
      rcases hV with hV | hV | hV
      · cases hV
      · cases hV
        exact hK
      · exact ih ht V hV

/-- Replacing every hard-oracle query by a bit-oracle query followed by the known shift
preserves the circuit's output state exactly. See [FarhiEtAl1998]. -/
theorem hardOracle_substitution {N : ℕ} [NeZero N] {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin N) W))
    (ψ : QState (PolynomialWorkspace (Fin N) W)) (f : Fin N → Bool) :
    Run (TensorGate (BitOracleOn f) 1) (substituteForward (knownShift N W) C) ψ =
      Run (hardOracle f) C ψ := by
  rw [substituteForward_run, ← hardOracle_factor]

end Qatlib.Papers.ParityLimit98.MainResults.IteratedFunction
