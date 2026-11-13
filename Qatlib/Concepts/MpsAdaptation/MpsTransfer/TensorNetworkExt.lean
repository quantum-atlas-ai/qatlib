/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.TensorNetworkDefs
import Qatlib.Concepts.TensorNetwork.GaugeInvariance

/-!
# Count bounds for tensor-network evaluators

This module proves exact accumulated counts and upper budgets for the MPS vector,
mixed-transfer, and PEPS strip recurrences. It then establishes the bundled propositions
`Clause18Claim` and `Clause19Claim` using these bounds and the imported representation and
sampling results. The contraction framework is motivated by MPS methods in [PerezGarciaEtAl2007]
and [Schollwock2011].

## Main statements

* `mpsEvalWithCount_op_le`: the MPS evaluation count fits its stated budget.
* `mpsInnerEvalWithCount_op_le`: the mixed-transfer count fits its stated budget.
* `pepsStripEvalWithCount_op_le`: the PEPS strip count fits its stated budget.
* `g1` and `g3`: the bundled representation, invariance, cost, and sampling claims.

## References

* [Perez-Garcia et al., 2007][PerezGarciaEtAl2007]
* [Schollwock, 2011][Schollwock2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib
open Qatlib.Concepts.TensorNetwork.GaugeInvariance

/-- The operation count of the MPS evaluation vector at site `k` is `k * (2 * D * D)`. -/
theorem mpsEvalVectorCount_snd_k {n d D : ℕ} {R : Type} [CommRing R] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) R) (x : Fin n → Fin d) :
    ∀ k (hk : k < n), (mpsEvalVectorCount A x ⟨k, hk⟩).2 = k * (2 * D * D) := by
  intro k
  induction k with
  | zero =>
      intro hk
      rw [mpsEvalVectorCount]
      simp
  | succ k ih =>
      intro hk
      have hprev : k < n := by omega
      have hstep : (mpsEvalVectorCount A x ⟨k + 1, hk⟩).2 =
          (mpsEvalVectorCount A x ⟨k, hprev⟩).2 + 2 * D * D := by
        rw [mpsEvalVectorCount]
      rw [hstep, ih hprev]
      ring

/-- The count returned by the MPS evaluator is at most `mpsEvalOpCount n D`. -/
theorem mpsEvalWithCount_op_le (n d D : ℕ) (hn : NeZero n) (hD : NeZero D) {R : Type} [CommRing R]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) R) (x : Fin n → Fin d) :
    (@mpsEvalWithCount n d D R _ hn hD A x).2 ≤ mpsEvalOpCount n D := by
  dsimp [mpsEvalWithCount, mpsEvalOpCount]
  have hnpos : 0 < n := NeZero.pos n
  have hsub : n - 1 < n := Nat.sub_lt hnpos one_pos
  rw [mpsEvalVectorCount_snd_k A x (n - 1) hsub]
  have hle : (n - 1) * (2 * D * D) ≤ n * (2 * D * D) := by
    apply Nat.mul_le_mul_right
    omega
  omega

/-- The mixed transfer count at site `k` is `(k + 1) * (d * (2 * D * D * D)) + k * (2 * D * D)`. -/
theorem mpsInnerTransferCount_snd_k {n d D : ℕ} [NeZero D]
    (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    ∀ k (hk : k < n),
      (mpsInnerTransferCount A B ⟨k, hk⟩).2 = (k + 1) * (d * (2 * D * D * D)) + k * (2 * D * D) := by
  intro k
  induction k with
  | zero =>
      intro hk
      rw [mpsInnerTransferCount]
      dsimp
      ring
  | succ k ih =>
      intro hk
      have hprev : k < n := by omega
      have hstep : (mpsInnerTransferCount A B ⟨k + 1, hk⟩).2 =
          (mpsInnerTransferCount A B ⟨k, hprev⟩).2 + d * (2 * D * D * D) + 2 * D * D := by
        rw [mpsInnerTransferCount]
      rw [hstep, ih hprev]
      ring

/-- The count returned by the mixed-transfer evaluator is at most `mpsInnerOpCount n d D`. -/
theorem mpsInnerEvalWithCount_op_le (n d D : ℕ) (hn : NeZero n) (hD : NeZero D)
    (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    (@mpsInnerEvalWithCount n d D hn hD A B).2 ≤ mpsInnerOpCount n d D := by
  dsimp [mpsInnerEvalWithCount, mpsInnerOpCount]
  have hnpos : 0 < n := NeZero.pos n
  have hsub : n - 1 < n := Nat.sub_lt hnpos one_pos
  rw [mpsInnerTransferCount_snd_k A B (n - 1) hsub]
  have hcancel : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
  rw [hcancel]
  have hDpos : 1 ≤ D := NeZero.pos D
  have h1 : (n - 1) * (2 * D * D) + D ≤ n * (2 * D * D) := by
    cases n with
    | zero => contradiction
    | succ n =>
        simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
        have hdle : D ≤ 2 * D * D := by
          have h2D : 1 ≤ 2 * D := by omega
          have hm : 1 * D ≤ (2 * D) * D := Nat.mul_le_mul_right D h2D
          omega
        calc n * (2 * D * D) + D ≤ n * (2 * D * D) + 2 * D * D := Nat.add_le_add_left hdle _
             _ = (n + 1) * (2 * D * D) := by ring
  rw [add_assoc]
  have h2 : n * (d * (2 * D * D * D)) + ((n - 1) * (2 * D * D) + D) ≤
         n * (2 * d * D * D * D + 2 * D * D) := by
    calc
      n * (d * (2 * D * D * D)) + ((n - 1) * (2 * D * D) + D)
        ≤ n * (d * (2 * D * D * D)) + n * (2 * D * D) := Nat.add_le_add_left h1 _
      _ = n * (2 * d * D * D * D + 2 * D * D) := by ring
  exact h2

/-- After `j` PEPS strip steps, the accumulated count is `j * ((D ^ a) ^ 3 * (a + 2))`. -/
theorem pepsStripFold_snd {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d) (j : ℕ) :
    (pepsStripFold T x j).2 = j * ((D ^ a) ^ 3 * (a + 2)) := by
  induction j with
  | zero =>
      simp [pepsStripFold]
  | succ j ih =>
      rw [pepsStripFold]
      dsimp
      rw [ih]
      ring

/-- The count returned by PEPS strip evaluation is at most `pepsStripOpCount a b D`. -/
theorem pepsStripEvalWithCount_op_le (a b d D : ℕ) (hD : NeZero D)
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d) :
    (@pepsStripEvalWithCount a b d D hD T x).2 ≤ pepsStripOpCount a b D := by
  dsimp [pepsStripEvalWithCount, pepsStripOpCount]
  rw [pepsStripFold_snd]
  have : b * ((D ^ a) ^ 3 * (a + 2)) ≤ b * ((D ^ a) ^ 3 * (a + 2) + 1) := by
    apply Nat.mul_le_mul_left
    omega
  exact this

/-- Establish the bundled tensor-network invariance, representation, example, and contraction
properties in `Clause18Claim`. -/
theorem g1 : Clause18Claim :=
  Qatlib.Concepts.TensorNetwork.GaugeInvariance.g1

/-- Establish the bundled evaluation-count bounds and finite-bit MPS sampling approximation in
`Clause19Claim`. -/
theorem g3 : Clause19Claim := by
  refine ⟨fun n d D hn hD R _ A x => mpsEvalWithCount_op_le n d D hn hD A x,
          fun n d D hn hD A B => mpsInnerEvalWithCount_op_le n d D hn hD A B,
          clause3_clause6,
          fun a b d D hD T x => pepsStripEvalWithCount_op_le a b d D hD T x⟩

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
