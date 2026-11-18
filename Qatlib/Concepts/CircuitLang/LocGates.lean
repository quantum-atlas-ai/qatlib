/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitLang.WireReg
public import Qatlib.Foundations.PureStateMath.Tensor
public import Mathlib.LinearAlgebra.Matrix.Reindex

@[expose] public section

/-!
# Located gates: injective wire selection and disjoint-block placement

A located gate names its target wires through an injective selection `LocSel`; a selection
that repeats a target wire is rejected by injectivity, with the duplicate selection
`dupSel` as a satisfiable negative example. Placement on the canonical split of a register
into consecutive blocks is defined by reindexing a tensor gate along `regAppendEquiv`, so a
gate on one block acts as the identity on the disjoint complement block. Completing an
arbitrary injective selection into such a wire split, general controlled gates, and wire
permutations are deferred to the next wave.

## Main statements

* `dupSel_not_inj`: the duplicated selection is rejected.
* `placedLast_uni` / `placedFirst_uni`: block placement preserves unitarity.
* `placedTensor`: gates on the two disjoint blocks compose to the reindexed tensor gate.
* `placedComm`: gates on disjoint blocks commute.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitLang.WireReg

namespace Qatlib.Concepts.CircuitLang.LocGates

/-- An injective selection of `k` target wires out of `n`; injectivity rejects selections
that hit the same wire twice. -/
structure LocSel (n k : ℕ) where
  /-- The selected wire numbers, in target order. -/
  sel : Fin k → Wire n
  /-- Injectivity: no wire is targeted twice. -/
  inj : Function.Injective sel

/-- Distinct indices of an injective selection hit distinct wires. -/
theorem locSel_ne {n k : ℕ} {s : LocSel n k} {i j : Fin k} (hij : i ≠ j) :
    s.sel i ≠ s.sel j := fun h => hij (s.inj h)

/-- The duplicate selection that targets wire zero twice. -/
def dupSel : Fin 2 → Wire 2 := fun _ => 0

/-- The duplicate selection is not injective, so it is rejected by `LocSel`. -/
theorem dupSel_not_inj : ¬ Function.Injective dupSel := by
  intro h
  have h01 : dupSel 0 = dupSel 1 := rfl
  exact absurd (h h01) (by decide)

/-- The canonical selection of the last `k` wires of an `(m + k)`-wire register. -/
def lastSel (m k : ℕ) : LocSel (m + k) k where
  sel j := Fin.natAdd m j
  inj := by
    intro a b h
    have h' : m + a.val = m + b.val := by
      simpa [Fin.natAdd] using congrArg Fin.val h
    exact Fin.ext (Nat.add_left_cancel h')

/-- Place a `Reg k`-gate on the last `k` wires of `Reg (m + k)`, acting as the identity on
the first `m` wires. -/
noncomputable def PlacedLast (m k : ℕ) (U : Matrix (Reg k) (Reg k) ℂ) :
    Matrix (Reg (m + k)) (Reg (m + k)) ℂ :=
  Matrix.reindex (regAppendEquiv m k).symm (regAppendEquiv m k).symm (TensorGate 1 U)

/-- Place a `Reg m`-gate on the first `m` wires of `Reg (m + k)`, acting as the identity on
the last `k` wires. -/
noncomputable def PlacedFirst (m k : ℕ) (U : Matrix (Reg m) (Reg m) ℂ) :
    Matrix (Reg (m + k)) (Reg (m + k)) ℂ :=
  Matrix.reindex (regAppendEquiv m k).symm (regAppendEquiv m k).symm (TensorGate U 1)

/-- Placement entries: the `U` entry on the selected wires, times the identity indicator on
the untouched prefix wires. -/
theorem placedL_entry (m k : ℕ) (U : Matrix (Reg k) (Reg k) ℂ) (x y : Reg (m + k)) :
    PlacedLast m k U x y =
      (if (regAppendEquiv m k x).1 = (regAppendEquiv m k y).1 then (1 : ℂ) else 0) *
        U (regAppendEquiv m k x).2 (regAppendEquiv m k y).2 := by
  simp only [PlacedLast, reidx_apply]
  rw [show regAppendEquiv m k x = ((regAppendEquiv m k x).1, (regAppendEquiv m k x).2) from rfl,
    show regAppendEquiv m k y = ((regAppendEquiv m k y).1, (regAppendEquiv m k y).2) from rfl]
  rw [tensorGate_apply]
  simp [Matrix.one_apply]

/-- Entry form on raw wire reads: the identity indicator vanishes unless the untouched
prefix bits agree, and `U` sees exactly the wires of the `lastSel` selection. -/
theorem placedLast_bits (m k : ℕ) (U : Matrix (Reg k) (Reg k) ℂ) (x y : Reg (m + k)) :
    PlacedLast m k U x y =
      (if ∀ i : Wire m, x (Fin.castAdd k i) = y (Fin.castAdd k i) then (1 : ℂ) else 0) *
        U (fun j => x ((lastSel m k).sel j)) (fun j => y ((lastSel m k).sel j)) := by
  rw [placedL_entry]
  have h1 : (regAppendEquiv m k x).1 = fun i : Wire m => x (Fin.castAdd k i) := by
    funext i; rfl
  have h2 : (regAppendEquiv m k y).1 = fun i : Wire m => y (Fin.castAdd k i) := by
    funext i; rfl
  have h3 : (regAppendEquiv m k x).2 = fun j : Wire k => x ((lastSel m k).sel j) := by
    funext j; rfl
  have h4 : (regAppendEquiv m k y).2 = fun j : Wire k => y ((lastSel m k).sel j) := by
    funext j; rfl
  rw [h1, h2, h3, h4]
  simp only [funext_iff]

/-- Placing a unitary gate on the last wires preserves unitarity. -/
theorem placedLast_uni {m k : ℕ} {U : Matrix (Reg k) (Reg k) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Reg k) ℂ) :
    PlacedLast m k U ∈ Matrix.unitaryGroup (Reg (m + k)) ℂ :=
  reidxUnitary _ (tensorGate_unitary (Submonoid.one_mem _) hU)

/-- Placing a unitary gate on the first wires preserves unitarity. -/
theorem placedFirst_uni {m k : ℕ} {U : Matrix (Reg m) (Reg m) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Reg m) ℂ) :
    PlacedFirst m k U ∈ Matrix.unitaryGroup (Reg (m + k)) ℂ :=
  reidxUnitary _ (tensorGate_unitary hU (Submonoid.one_mem _))

/-- Gates placed on the two disjoint blocks of a register split compose to the tensor gate
reindexed along the split. -/
theorem placedTensor (m k : ℕ) (U : Matrix (Reg m) (Reg m) ℂ) (V : Matrix (Reg k) (Reg k) ℂ) :
    PlacedFirst m k U * PlacedLast m k V
      = Matrix.reindex (regAppendEquiv m k).symm (regAppendEquiv m k).symm (TensorGate U V) := by
  rw [PlacedFirst, PlacedLast, ← reidxMul, tensorGate_mul, Matrix.mul_one, Matrix.one_mul]

/-- Gates on disjoint wire blocks commute. -/
theorem placedComm (m k : ℕ) (U : Matrix (Reg m) (Reg m) ℂ) (V : Matrix (Reg k) (Reg k) ℂ) :
    PlacedFirst m k U * PlacedLast m k V = PlacedLast m k V * PlacedFirst m k U := by
  rw [placedTensor, PlacedLast, PlacedFirst, ← reidxMul, tensorGate_mul, Matrix.one_mul,
    Matrix.mul_one]

end Qatlib.Concepts.CircuitLang.LocGates
