/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# The light-cone / Pauli-support bound of Appendix D

Fixed version: arXiv:2608.15545v1 (2026-08-16), Appendix D (p.11) and the
first paragraph of Section II (p.2).  Paper: *Quantum Advantage with Adaptive
Shallow Circuits*.

The paper's causal bound is

> if an adaptive circuit has total two-qubit circuit depth `d` and uses `m`
> intermediate measurement outcomes as classical feedback, then the final local
> readout is supported on at most `O((m + 1) 2^d)` input qubits.

This file proves the bound with the sharp constant `(m + 1) * 2^d` from an
explicit wire-level circuit model, without any quantum-mechanical assumption
beyond locality of the gates.

**Model.**  A depth-one layer on `N` wires is an involution `partner` of
`Fin N` (`partner i = i` for an idle wire, `partner i = j ≠ i` when a
two-qubit gate acts on `{i, j}`).  The gate itself only has to satisfy the
locality condition that the *post*-layer value at wire `i` is a function of the
*pre*-layer values at `i` and `partner i`; no linearity, unitarity or
positivity is used.  This is exactly the Heisenberg-picture support growth of
Appendix D.

**Result.**  A two-qubit gate can only merge two supports, so one layer at most
doubles the support (`Layer.step_card_le`).  Pulling a support back through `d`
layers therefore multiplies its size by at most `2^d`
(`pullback_card_le`), and a protocol with `M + 1` readout wires ends up with
support at most `(M + 1) * 2^d` (`lightCone_bound`).
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShallowAdvWu26.ShallowPower.LightCone

/-- **Input dependence.**  A Boolean function on `N` input bits depends on the
set `S` if two inputs that agree on `S` have the same value.  This is the
paper-layer counterpart of the effective input support of the Heisenberg-picture
observable `A = C†(Z)` (Appendix D, p.11). -/
def DependsOn {N : ℕ} (f : (Fin N → Bool) → Bool) (S : Finset (Fin N)) : Prop :=
  ∀ x y : Fin N → Bool, (∀ i ∈ S, x i = y i) → f x = f y

/-- Monotonicity: a function depending on `S` also depends on any superset. -/
theorem DependsOn.mono {N : ℕ} {f : (Fin N → Bool) → Bool} {S T : Finset (Fin N)}
    (h : DependsOn f S) (hST : S ⊆ T) : DependsOn f T :=
  fun x y hxy => h x y (fun i hi => hxy i (hST hi))

/-- A depth-one layer of disjoint one- and two-qubit gates on `N` wires.
`partner i = i` for an idle wire; `partner i = j ≠ i` when `i` and `j` sit under
the same two-qubit gate. -/
structure Layer (N : ℕ) where
  /-- The wire paired with each wire (`partner i = i` when idle). -/
  partner : Fin N → Fin N
  /-- Two-qubit gates are symmetric, so the pairing is an involution. -/
  involutive : ∀ i, partner (partner i) = i

/-- Backward light cone of a wire set through one layer: a two-qubit gate on
`{i, partner i}` makes the post-layer value at `i` depend on both pre-layer
values, so both wires enter the pre-layer support. -/
def Layer.step {N : ℕ} (L : Layer N) (S : Finset (Fin N)) : Finset (Fin N) :=
  S ∪ S.image L.partner

/-- The backward step never loses wires. -/
theorem Layer.subset_step {N : ℕ} (L : Layer N) (S : Finset (Fin N)) :
    S ⊆ L.step S := Finset.subset_union_left

/-- One layer at most doubles the support: the partner map is an involution, so
the partner set has the same cardinality as the original support. -/
theorem Layer.step_card_le {N : ℕ} (L : Layer N) (S : Finset (Fin N)) :
    (L.step S).card ≤ 2 * S.card := by
  have h1 : (S ∪ S.image L.partner).card ≤ S.card + (S.image L.partner).card :=
    Finset.card_union_le _ _
  have h2 : (S.image L.partner).card ≤ S.card := Finset.card_image_le
  show (S ∪ S.image L.partner).card ≤ 2 * S.card
  omega

/-- A layer together with its gate map: the post-layer value at wire `i`
depends only on the pre-layer values at `i` and `partner i`. -/
structure LayerGate (N : ℕ) extends Layer N where
  /-- The map implemented by the layer on wire assignments. -/
  gate : (Fin N → Bool) → (Fin N → Bool)
  /-- Locality: wire `i` may only read itself and its partner. -/
  locality : ∀ i (x y : Fin N → Bool), x i = y i → x (partner i) = y (partner i) →
    gate x i = gate y i

/-- Composite map of a list of layers; the head of the list is applied first. -/
def composeMap {N : ℕ} : List (LayerGate N) → (Fin N → Bool) → (Fin N → Bool)
  | [], x => x
  | L :: Ls, x => composeMap Ls (L.gate x)

/-- Backward pullback of a support through a list of layers (head first). -/
def pullback {N : ℕ} : List (LayerGate N) → Finset (Fin N) → Finset (Fin N)
  | [], S => S
  | L :: Ls, S => L.step (pullback Ls S)

/-- **One-layer propagation.**  If `g` depends on `S`, then `g` after one layer
depends on the pulled-back set. -/
theorem dependsOn_layerStep {N : ℕ} (L : LayerGate N) (S : Finset (Fin N))
    {g : (Fin N → Bool) → Bool} (h : DependsOn g S) :
    DependsOn (g ∘ L.gate) (L.step S) := by
  intro x y hxy
  exact h (L.gate x) (L.gate y) (fun i hi => L.locality i x y
    (hxy i (L.subset_step S hi))
    (hxy (L.partner i) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi))))

/-- **Appendix-D light-cone propagation.**  A function computed by the circuit
depends only on the pulled-back support. -/
theorem dependsOn_compose {N : ℕ} (Ls : List (LayerGate N)) :
    ∀ (g : (Fin N → Bool) → Bool) (S : Finset (Fin N)),
      DependsOn g S → DependsOn (g ∘ composeMap Ls) (pullback Ls S)
  | g, S, h => by
    cases Ls with
    | nil => simpa [composeMap, pullback, Function.comp_def] using h
    | cons L Ls =>
      have ih := dependsOn_compose Ls g S h
      exact dependsOn_layerStep L (pullback Ls S) ih

/-- **Support growth.**  A depth-`d` circuit turns a support of `N₀` wires into
one of at most `N₀ * 2^d` wires. -/
theorem pullback_card_le {N : ℕ} (Ls : List (LayerGate N)) (S : Finset (Fin N)) :
    (pullback Ls S).card ≤ 2 ^ Ls.length * S.card := by
  induction Ls generalizing S with
  | nil => simp [pullback]
  | cons L Ls ih =>
    have h1 : (pullback (L :: Ls) S).card ≤ 2 * (pullback Ls S).card :=
      L.step_card_le (pullback Ls S)
    have h2 : 2 * (pullback Ls S).card ≤ 2 * (2 ^ Ls.length * S.card) :=
      Nat.mul_le_mul_left 2 (ih S)
    have h3 : 2 * (2 ^ Ls.length * S.card) = 2 ^ (L :: Ls).length * S.card := by
      rw [List.length_cons, pow_succ]
      ring
    calc (pullback (L :: Ls) S).card ≤ 2 * (pullback Ls S).card := h1
      _ ≤ 2 * (2 ^ Ls.length * S.card) := h2
      _ = 2 ^ (L :: Ls).length * S.card := h3

/-- **Theorem 1 / Appendix D, light-cone bound.**  Let a depth-`d` protocol read
out `M + 1` wires (one output wire and `M` measurement outcomes).  Then the
computed Boolean function depends on a set of at most `(M + 1) * 2^d` input
wires. -/
theorem lightCone_bound {N : ℕ} (Ls : List (LayerGate N)) (readout : Finset (Fin N))
    (M : ℕ) (hread : readout.card ≤ M + 1) (g : (Fin N → Bool) → Bool)
    (hg : DependsOn g readout) :
    ∃ S : Finset (Fin N), S.card ≤ (M + 1) * 2 ^ Ls.length ∧
      DependsOn (g ∘ composeMap Ls) S := by
  refine ⟨pullback Ls readout, ?_, dependsOn_compose Ls g readout hg⟩
  have h := pullback_card_le Ls readout
  have hmono : 2 ^ Ls.length * readout.card ≤ 2 ^ Ls.length * (M + 1) :=
    Nat.mul_le_mul_left _ hread
  calc (pullback Ls readout).card ≤ 2 ^ Ls.length * readout.card := h
    _ ≤ 2 ^ Ls.length * (M + 1) := hmono
    _ = (M + 1) * 2 ^ Ls.length := Nat.mul_comm _ _

/-- **Appendix D, feedback budget form.**  If every dependence set of the
computed function is the whole input, then the readout cannot be confined to
`M + 1` wires when `(M + 1) * 2^d < N`: a depth-`d`, `M`-feedback protocol
needs `(M + 1) * 2^d ≥ N`. -/
theorem feedback_budget_needed {N : ℕ} (Ls : List (LayerGate N))
    (readout : Finset (Fin N)) (M : ℕ) (hread : readout.card ≤ M + 1)
    (g : (Fin N → Bool) → Bool) (hg : DependsOn g readout)
    (hfull : ∀ S : Finset (Fin N), DependsOn (g ∘ composeMap Ls) S → S = Finset.univ)
    (hN : (M + 1) * 2 ^ Ls.length < N) : False := by
  obtain ⟨S, hcard, hdep⟩ := lightCone_bound Ls readout M hread g hg
  have huniv := hfull S hdep
  have hS : S.card = N := by rw [huniv, Finset.card_univ, Fintype.card_fin]
  omega

/-- **Appendix D, explicit form.**  In the situation of
`feedback_budget_needed` the budget obeys `N ≤ (M + 1) * 2^d`. -/
theorem support_le_budget {N : ℕ} (Ls : List (LayerGate N))
    (readout : Finset (Fin N)) (M : ℕ) (hread : readout.card ≤ M + 1)
    (g : (Fin N → Bool) → Bool) (hg : DependsOn g readout)
    (hfull : ∀ S : Finset (Fin N), DependsOn (g ∘ composeMap Ls) S → S = Finset.univ) :
    N ≤ (M + 1) * 2 ^ Ls.length := by
  obtain ⟨S, hcard, hdep⟩ := lightCone_bound Ls readout M hread g hg
  have huniv := hfull S hdep
  have hS : S.card = N := by rw [huniv, Finset.card_univ, Fintype.card_fin]
  omega

end Qatlib.Papers.ShallowAdvWu26.ShallowPower.LightCone
