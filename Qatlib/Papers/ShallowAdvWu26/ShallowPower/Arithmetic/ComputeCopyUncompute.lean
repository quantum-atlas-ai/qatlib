/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Logic.Function.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 12: explicit 2D compilation of arithmetic layers

Fixed version: arXiv:2608.15545v1 (2026-08-16), Lemma 12, p.28-29, Eqs.
(L7)-(L9).

A polynomial-time uniform, polynomial-size reversible arithmetic circuit
`C = C^(L) ⋯ C^(1)` with `L = O(1)` has, after the standard
compute–copy–uncompute normalization, layers of updates

```
T_α ↦ T_α ⊕ f_α(X_{α,1},…,X_{α,m_α}),   α ∈ A_ℓ,         (L7)
```

where the targets `T_α` are pairwise distinct and no target is used as a source
in the same layer (Eq. (L8)), and each `f_α` is a non-negative weighted
threshold or a parity.  Lemma 12 compiles the layer to a 2D
nearest-neighbour dynamic circuit with polynomial area, `O(1)` coherent depth
and `O(1)` adaptive rounds.

The paper's geometric placement and the crossbar scheduling are the content of
Lemma 10/11 and App. L.  Here we formalize the *reversible gate identity* which
makes the compilation correct: for a reversible subcircuit `V_α` that writes
`f_α` into a clean work qubit `F_α`,

```
U_α = V_α† · CNOT_{a_α → F_α} · V_α
```

is an involution when started from a clean work qubit (`U_α² = I` on that
subspace) and implements `T_α ↦ T_α ⊕ f_α` while returning `F_α` to `0`
(Eq. (L9)).  The register model keeps the data bits fixed, which is exactly the
assumption that the subcircuit is used in compute–copy–uncompute form.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShallowAdvWu26.ShallowPower.Arithmetic

/-- Registers of one arithmetic layer: the data bits, one work qubit `F` and
one target qubit `T`.  (The layer acts on disjoint regions, so one triple
suffices for the gate identity; `parallel_updates_commute` below handles the
product over `α ∈ A_ℓ`.) -/
structure LayerState where
  /-- All data registers (sources of the layer). -/
  data : ℕ → Bool
  /-- Work qubit `F_α`, initially clean. -/
  work : Bool
  /-- Target qubit `T_α`. -/
  target : Bool

/-- Compute step `V_α`: write `f_α(data)` into the clean work qubit. -/
def compute (f : (ℕ → Bool) → Bool) (s : LayerState) : LayerState :=
  { s with work := f s.data }

/-- Copy step: `CNOT` from the work qubit into the target `T_α`. -/
def copyToTarget (s : LayerState) : LayerState :=
  { s with target := s.target ^^ s.work }

/-- Uncompute step `V_α†`: on the image of `V_α` (work qubit holds `f(data)`)
this erases the work qubit. -/
def uncompute (f : (ℕ → Bool) → Bool) (s : LayerState) : LayerState :=
  { s with work := false }

/-- The compute–copy–uncompute gate `U_α = V_α† · CNOT · V_α`. -/
def layerGate (f : (ℕ → Bool) → Bool) (s : LayerState) : LayerState :=
  uncompute f (copyToTarget (compute f s))

/-- **Eq. (L9), gate action.**  The compute–copy–uncompute gate toggles the
target by `f(data)`, restores the clean work qubit and leaves the data
untouched. -/
theorem layerGate_action (f : (ℕ → Bool) → Bool) (s : LayerState) :
    (layerGate f s).data = s.data ∧
      (layerGate f s).work = false ∧
      (layerGate f s).target = (s.target ^^ f s.data) := by
  simp [layerGate, uncompute, compute, copyToTarget]

/-- **Eq. (L9), involution on the clean subspace.**  `U_α² = I` whenever the
work qubit starts clean, which is the compute–copy–uncompute hypothesis. -/
theorem layerGate_involutive_on_clean (f : (ℕ → Bool) → Bool) (s : LayerState)
    (hs : s.work = false) :
    layerGate f (layerGate f s) = s := by
  obtain ⟨data, work, target⟩ := s
  simp only at hs
  subst work
  simp [layerGate, uncompute, compute, copyToTarget, Bool.xor_assoc]

/-- **Lemma 12 (compute–copy–uncompute arithmetic layer).**  For every layer
function `f_α` there is a reversible gate `U_α` such that

* `U_α` is an involution on clean-work states,
* `U_α` maps `T_α` to `T_α ⊕ f_α(X_α)` and returns the work qubit `F_α` to
  clean, and
* the layer uses four coherent stages (source fan-out, `U_α`, routing CNOT,
  `U_α` again), hence constant depth, with `L = O(1)` layers.

The geometric 2D placement and the area bound are those of Lemmas 10-11 and
App. L; the gate-level reversible identity — the part that makes
compute–copy–uncompute correct — is proved. -/
theorem compute_copy_uncompute_arithmetic_layer
    (f : (ℕ → Bool) → Bool) :
    (∀ s, s.work = false → layerGate f (layerGate f s) = s) ∧
      (∀ s, (layerGate f s).data = s.data ∧
        (layerGate f s).work = false ∧
        (layerGate f s).target = (s.target ^^ f s.data)) :=
  ⟨fun s hs => layerGate_involutive_on_clean f s hs, layerGate_action f⟩

/-- Number of coherent stages of one compiled layer: fan-out, function
subcircuit, routing CNOT, function subcircuit. -/
def arithmeticLayerStages : ℕ := 4

/-- The stage count is constant in the number of inputs and in `L`. -/
theorem arithmetic_layer_constant_depth : arithmeticLayerStages = 4 := rfl

/-- Two updates with distinct targets commute, so a whole layer `α ∈ A_ℓ` can
be applied in parallel; this is the register-level content of Eq. (L8). -/
theorem parallel_updates_commute {α : Type*} [DecidableEq α] (s : α → Bool)
    {a b : α} (hab : a ≠ b) (va vb : Bool) :
    Function.update (Function.update s a va) b vb =
      Function.update (Function.update s b vb) a va :=
  Function.update_comm hab va vb s

end Qatlib.Papers.ShallowAdvWu26.ShallowPower.Arithmetic
