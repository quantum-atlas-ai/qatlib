/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinModels08.MainResults.Defs

/-!
# Vertex-model partition contractions and circuits

This module defines a transfer column by summing products of local vertex weights over the
internal vertical spins. It proves that the recursive partition contraction `vmPartition` equals
the corresponding entry and computational basis matrix element of the column product
`vmCircuit`, giving the vertex-model identity of [VanDenNestEtAl2009].

## Main statements

* `vmPartition_eq_vmCircuit`: the partition contraction equals the circuit entry.
* `matElem_vmCircuit_eq_vmPartition`: the computational basis matrix element equals the
  partition contraction.

## References

* [Van den Nest et al., 2009][VanDenNestEtAl2009]
-/

set_option warningAsError false

noncomputable section

open scoped BigOperators Matrix

namespace Qatlib.Papers.SpinModels08.MainResults.VertexModel

open Qatlib.Papers.SpinModels08.MainResults

/-- The transfer matrix for a column, obtained by summing products of vertex weights over all
vertical spin assignments. -/
def vmColumn {q N M : ℕ} (w : Fin M → Fin N → QWeight q) (c : Fin M) :
    Matrix (Config q N) (Config q N) ℂ :=
  fun l j => ∑ V : Fin (N + 1) → Fin q,
    ∏ r : Fin N, w c r (V (Fin.castSucc r)) (j r) (V (Fin.succ r)) (l r)

/-- The vertex-model partition contraction, defined recursively by summing over intermediate
configurations and vertical spins. -/
def vmPartition {q N : ℕ} :
    (M : ℕ) → (Fin M → Fin N → QWeight q) → Config q N → Config q N → ℂ
  | 0, _, L, R => if L = R then 1 else 0
  | M + 1, w, L, R =>
      ∑ j : Config q N, ∑ V : Fin (N + 1) → Fin q,
        (∏ r : Fin N, w (Fin.last M) r (V (Fin.castSucc r)) (R r) (V (Fin.succ r)) (j r)) *
          vmPartition M (fun c r => w (Fin.castSucc c) r) L j

/-- The ordered product of vertex-model column matrices, with the identity for zero columns. -/
def vmCircuit {q N : ℕ} :
    (M : ℕ) → (Fin M → Fin N → QWeight q) → Matrix (Config q N) (Config q N) ℂ
  | 0, _ => 1
  | M + 1, w => vmCircuit M (fun c r => w (Fin.castSucc c) r) * vmColumn w (Fin.last M)

/-- The recursively defined vertex-model partition contraction equals the corresponding circuit
matrix entry [VanDenNestEtAl2009]. -/
theorem vmPartition_eq_vmCircuit {q N : ℕ} :
    ∀ (M : ℕ) (w : Fin M → Fin N → QWeight q) (L R : Config q N),
      vmPartition M w L R = vmCircuit M w L R := by
  intro M
  induction M with
  | zero =>
      intro w L R
      show (if L = R then 1 else 0) = (1 : Matrix (Config q N) (Config q N) ℂ) L R
      exact Matrix.one_apply.symm
  | succ M ih =>
      intro w L R
      simp only [vmPartition, vmCircuit]
      rw [Matrix.mul_apply]
      rw [show (∑ j : Config q N, ∑ V : Fin (N + 1) → Fin q,
            (∏ r : Fin N, w (Fin.last M) r (V (Fin.castSucc r)) (R r)
              (V (Fin.succ r)) (j r)) *
              vmPartition M (fun c r => w (Fin.castSucc c) r) L j)
          = ∑ j : Config q N,
              (∑ V : Fin (N + 1) → Fin q,
                ∏ r : Fin N, w (Fin.last M) r (V (Fin.castSucc r)) (R r)
                  (V (Fin.succ r)) (j r)) *
              vmPartition M (fun c r => w (Fin.castSucc c) r) L j from by
        simp_rw [Finset.sum_mul]]
      rw [show (∑ j : Config q N,
              (∑ V : Fin (N + 1) → Fin q,
                ∏ r : Fin N, w (Fin.last M) r (V (Fin.castSucc r)) (R r)
                  (V (Fin.succ r)) (j r)) *
              vmPartition M (fun c r => w (Fin.castSucc c) r) L j)
          = ∑ j : Config q N,
              (∑ V : Fin (N + 1) → Fin q,
                ∏ r : Fin N, w (Fin.last M) r (V (Fin.castSucc r)) (R r)
                  (V (Fin.succ r)) (j r)) *
              vmCircuit M (fun c r => w (Fin.castSucc c) r) L j from by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ih (fun c r => w (Fin.castSucc c) r) L j]]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm (∑ V : Fin (N + 1) → Fin q,
        ∏ r : Fin N, w (Fin.last M) r (V (Fin.castSucc r)) (R r)
          (V (Fin.succ r)) (j r))]
      rfl

/-- The computational basis matrix element of the vertex-model circuit equals the partition
contraction [VanDenNestEtAl2009]. -/
theorem matElem_vmCircuit_eq_vmPartition {q N : ℕ}
    (M : ℕ) (w : Fin M → Fin N → QWeight q) (L R : Config q N) :
    matElem (vmCircuit M w) L R = vmPartition M w L R := by
  rw [matElem_eq_apply, vmPartition_eq_vmCircuit]

/-- The expanded computational basis sum for the circuit matrix element equals the partition
contraction. -/
theorem vmCircuit_matElem_eq {q N : ℕ}
    (M : ℕ) (w : Fin M → Fin N → QWeight q) (L R : Config q N) :
    ∑ a, ∑ b, basisVec L a * vmCircuit M w a b * basisVec R b = vmPartition M w L R :=
  matElem_vmCircuit_eq_vmPartition M w L R

/-- The entries of the local two-site gate recover the supplied vertex weights. -/
theorem vm_localGate_entries {q : ℕ} (w : QWeight q) (i j k l : Fin q) :
    twoLocalGate w (i, j) (k, l) = w i j k l :=
  twoLocalGate_apply w i j k l

end Qatlib.Papers.SpinModels08.MainResults.VertexModel
