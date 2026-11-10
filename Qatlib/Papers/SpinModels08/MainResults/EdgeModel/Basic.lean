/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinModels08.MainResults.Defs
set_option warningAsError false

noncomputable section

open scoped BigOperators Matrix

namespace Qatlib.Papers.SpinModels08.MainResults.EdgeModel

open Qatlib.Papers.SpinModels08.MainResults

abbrev EdgeW (q : ℕ) := Fin q → Fin q → ℂ

def bondProd {q N : ℕ} (v : (r : Fin N) → EdgeW q) (a : Config q N) : ℂ :=
  ∏ r : Fin N, if h : r.val + 1 < N then v r (a r) (a ⟨r.val + 1, h⟩) else 1

def emLayer {q N M : ℕ} (hW : Fin M → Fin N → EdgeW q)
    (vW : Fin M → (r : Fin N) → EdgeW q) (x : Fin M) :
    Matrix (Config q N) (Config q N) ℂ :=
  fun l j => (∏ r : Fin N, hW x r (l r) (j r)) * bondProd (vW x) j

def emPartition0 {q N : ℕ} :
    (M : ℕ) → (Fin M → Fin N → EdgeW q) → (Fin M → (r : Fin N) → EdgeW q) →
      Config q N → Config q N → ℂ
  | 0, _, _, L, R => if L = R then 1 else 0
  | M + 1, hW, vW, L, R =>
      ∑ j : Config q N,
        emPartition0 M (fun c r => hW (Fin.castSucc c) r)
          (fun c r => vW (Fin.castSucc c) r) L j *
        emLayer hW vW (Fin.last M) j R

def emCircuit {q N : ℕ} :
    (M : ℕ) → (Fin M → Fin N → EdgeW q) → (Fin M → (r : Fin N) → EdgeW q) →
      Matrix (Config q N) (Config q N) ℂ
  | 0, _, _ => 1
  | M + 1, hW, vW =>
      emCircuit M (fun c r => hW (Fin.castSucc c) r)
        (fun c r => vW (Fin.castSucc c) r) * emLayer hW vW (Fin.last M)

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

def emBoundaryFactor {q N : ℕ} (v : (r : Fin N) → EdgeW q) (a : Config q N) : ℂ :=
  bondProd v a

theorem emPartition_eq_circuit {q N : ℕ}
    (M : ℕ) (hW : Fin M → Fin N → EdgeW q) (vW : Fin M → (r : Fin N) → EdgeW q)
    (vL vR : (r : Fin N) → EdgeW q) (L R : Config q N) :
    emBoundaryFactor vL L * emPartition0 M hW vW L R * emBoundaryFactor vR R =
      emBoundaryFactor vL L * emCircuit M hW vW L R * emBoundaryFactor vR R := by
  rw [emPartition0_eq_emCircuit]

theorem emPartition_eq_circuit_of_unitBoundary {q N : ℕ}
    (M : ℕ) (hW : Fin M → Fin N → EdgeW q) (vW : Fin M → (r : Fin N) → EdgeW q)
    (vL vR : (r : Fin N) → EdgeW q) (L R : Config q N)
    (hL : emBoundaryFactor vL L = 1) (hR : emBoundaryFactor vR R = 1) :
    emBoundaryFactor vL L * emPartition0 M hW vW L R * emBoundaryFactor vR R =
      matElem (emCircuit M hW vW) L R := by
  rw [emPartition_eq_circuit, hL, hR, matElem_eq_apply, one_mul, mul_one]

theorem matElem_emCircuit_eq {q N : ℕ}
    (M : ℕ) (hW : Fin M → Fin N → EdgeW q) (vW : Fin M → (r : Fin N) → EdgeW q)
    (L R : Config q N) :
    matElem (emCircuit M hW vW) L R = emPartition0 M hW vW L R :=
  (emPartition0_eq_emCircuit M hW vW L R).symm ▸ matElem_eq_apply _ _ _

end Qatlib.Papers.SpinModels08.MainResults.EdgeModel
