/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinModels08.MainResults.Defs

/-!
# Edge-model partition functions as circuit entries

This module defines edge weights, nearest-neighbor bond products, and transfer layers for a
finite spin system. The recursive contraction `emPartition0` and matrix product `emCircuit` give
the edge-model correspondence of [VanDenNestEtAl2009], with optional factors at the two
boundaries.

## Main statements

* `emPartition0_eq_emCircuit`: the recursive partition contraction equals the circuit entry.
* `emPartition_eq_circuit_of_unitBoundary`: unit boundary factors yield the corresponding matrix
  element.

## References

* [Van den Nest et al., 2009][VanDenNestEtAl2009]
-/

noncomputable section

open scoped BigOperators Matrix

namespace Qatlib.Papers.SpinModels08.MainResults.EdgeModel

open Qatlib.Papers.SpinModels08.MainResults

/-- Complex edge weights indexed by two `q`-valued spins. -/
abbrev EdgeW (q : ℕ) := Fin q → Fin q → ℂ

/-- The product of weights along consecutive sites of `a`, with no bond beyond the last site. -/
def bondProd {q N : ℕ} (v : (r : Fin N) → EdgeW q) (a : Config q N) : ℂ :=
  ∏ r : Fin N, if h : r.val + 1 < N then v r (a r) (a ⟨r.val + 1, h⟩) else 1

/-- The transfer layer obtained by multiplying the horizontal site weights and the outgoing
configuration's bond product. -/
def emLayer {q N M : ℕ} (hW : Fin M → Fin N → EdgeW q)
    (vW : Fin M → (r : Fin N) → EdgeW q) (x : Fin M) :
    Matrix (Config q N) (Config q N) ℂ :=
  fun l j => (∏ r : Fin N, hW x r (l r) (j r)) * bondProd (vW x) j

/-- The edge-model partition contraction, defined recursively by summing over intermediate
configurations. -/
def emPartition0 {q N : ℕ} :
    (M : ℕ) → (Fin M → Fin N → EdgeW q) → (Fin M → (r : Fin N) → EdgeW q) →
      Config q N → Config q N → ℂ
  | 0, _, _, L, R => if L = R then 1 else 0
  | M + 1, hW, vW, L, R =>
      ∑ j : Config q N,
        emPartition0 M (fun c r => hW (Fin.castSucc c) r)
          (fun c r => vW (Fin.castSucc c) r) L j *
        emLayer hW vW (Fin.last M) j R

/-- The ordered product of edge-model transfer layers, with the identity for zero layers. -/
def emCircuit {q N : ℕ} :
    (M : ℕ) → (Fin M → Fin N → EdgeW q) → (Fin M → (r : Fin N) → EdgeW q) →
      Matrix (Config q N) (Config q N) ℂ
  | 0, _, _ => 1
  | M + 1, hW, vW =>
      emCircuit M (fun c r => hW (Fin.castSucc c) r)
        (fun c r => vW (Fin.castSucc c) r) * emLayer hW vW (Fin.last M)

/-- The recursive edge-model contraction equals the corresponding circuit matrix entry,
realizing the identity in [VanDenNestEtAl2009]. -/
theorem emPartition0_eq_emCircuit {q N : ℕ} :
    ∀ (M : ℕ) (hW : Fin M → Fin N → EdgeW q) (vW : Fin M → (r : Fin N) → EdgeW q)
      (L R : Config q N),
      emPartition0 M hW vW L R = emCircuit M hW vW L R := by
  intro M
  induction M with
  | zero =>
      intro hW vW L R
      show (if L = R then 1 else 0) = (1 : Matrix (Config q N) (Config q N) ℂ) L R
      exact Matrix.one_apply.symm
  | succ M ih =>
      intro hW vW L R
      simp only [emPartition0, emCircuit]
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ih (fun c r => hW (Fin.castSucc c) r) (fun c r => vW (Fin.castSucc c) r) L j]

/-- The nearest-neighbor bond product associated with a boundary configuration. -/
def emBoundaryFactor {q N : ℕ} (v : (r : Fin N) → EdgeW q) (a : Config q N) : ℂ :=
  bondProd v a

/-- Multiplying the partition contraction by left and right boundary factors gives the same
result as multiplying the circuit entry by those factors. -/
theorem emPartition_eq_circuit {q N : ℕ}
    (M : ℕ) (hW : Fin M → Fin N → EdgeW q) (vW : Fin M → (r : Fin N) → EdgeW q)
    (vL vR : (r : Fin N) → EdgeW q) (L R : Config q N) :
    emBoundaryFactor vL L * emPartition0 M hW vW L R * emBoundaryFactor vR R =
      emBoundaryFactor vL L * emCircuit M hW vW L R * emBoundaryFactor vR R := by
  rw [emPartition0_eq_emCircuit]

/-- If both boundary factors equal one, the boundary-weighted partition contraction equals the
circuit matrix element, as in [VanDenNestEtAl2009]. -/
theorem emPartition_eq_circuit_of_unitBoundary {q N : ℕ}
    (M : ℕ) (hW : Fin M → Fin N → EdgeW q) (vW : Fin M → (r : Fin N) → EdgeW q)
    (vL vR : (r : Fin N) → EdgeW q) (L R : Config q N)
    (hL : emBoundaryFactor vL L = 1) (hR : emBoundaryFactor vR R = 1) :
    emBoundaryFactor vL L * emPartition0 M hW vW L R * emBoundaryFactor vR R =
      matElem (emCircuit M hW vW) L R := by
  rw [emPartition_eq_circuit, hL, hR, matElem_eq_apply, one_mul, mul_one]

/-- The circuit matrix element equals the recursive edge-model partition contraction. -/
theorem matElem_emCircuit_eq {q N : ℕ}
    (M : ℕ) (hW : Fin M → Fin N → EdgeW q) (vW : Fin M → (r : Fin N) → EdgeW q)
    (L R : Config q N) :
    matElem (emCircuit M hW vW) L R = emPartition0 M hW vW L R :=
  (emPartition0_eq_emCircuit M hW vW L R).symm ▸ matElem_eq_apply _ _ _

end Qatlib.Papers.SpinModels08.MainResults.EdgeModel
