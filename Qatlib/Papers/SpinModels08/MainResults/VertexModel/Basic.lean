/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinModels08.MainResults.Defs
set_option warningAsError false

noncomputable section

open scoped BigOperators Matrix

namespace Qatlib.Papers.SpinModels08.MainResults.VertexModel

open Qatlib.Papers.SpinModels08.MainResults

def vmColumn {q N M : ℕ} (w : Fin M → Fin N → QWeight q) (c : Fin M) :
    Matrix (Config q N) (Config q N) ℂ :=
  fun l j => ∑ V : Fin (N + 1) → Fin q,
    ∏ r : Fin N, w c r (V (Fin.castSucc r)) (j r) (V (Fin.succ r)) (l r)

def vmPartition {q N : ℕ} :
    (M : ℕ) → (Fin M → Fin N → QWeight q) → Config q N → Config q N → ℂ
  | 0, _, L, R => if L = R then 1 else 0
  | M + 1, w, L, R =>
      ∑ j : Config q N, ∑ V : Fin (N + 1) → Fin q,
        (∏ r : Fin N, w (Fin.last M) r (V (Fin.castSucc r)) (R r) (V (Fin.succ r)) (j r)) *
          vmPartition M (fun c r => w (Fin.castSucc c) r) L j

def vmCircuit {q N : ℕ} :
    (M : ℕ) → (Fin M → Fin N → QWeight q) → Matrix (Config q N) (Config q N) ℂ
  | 0, _ => 1
  | M + 1, w => vmCircuit M (fun c r => w (Fin.castSucc c) r) * vmColumn w (Fin.last M)

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

theorem matElem_vmCircuit_eq_vmPartition {q N : ℕ}
    (M : ℕ) (w : Fin M → Fin N → QWeight q) (L R : Config q N) :
    matElem (vmCircuit M w) L R = vmPartition M w L R := by
  rw [matElem_eq_apply, vmPartition_eq_vmCircuit]

theorem vmCircuit_matElem_eq {q N : ℕ}
    (M : ℕ) (w : Fin M → Fin N → QWeight q) (L R : Config q N) :
    ∑ a, ∑ b, basisVec L a * vmCircuit M w a b * basisVec R b = vmPartition M w L R :=
  matElem_vmCircuit_eq_vmPartition M w L R

theorem vm_localGate_entries {q : ℕ} (w : QWeight q) (i j k l : Fin q) :
    twoLocalGate w (i, j) (k, l) = w i j k l :=
  twoLocalGate_apply w i j k l

end Qatlib.Papers.SpinModels08.MainResults.VertexModel
