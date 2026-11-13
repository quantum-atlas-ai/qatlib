/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.CharacterSum

/-!
# Walsh phase states and proposed preparation costs

This module proves the inner-product and projection identities that distinguish binary Walsh
phase states. It also defines the proposed preparation, quantum-time, and classical-time
expressions of [TerhalSmolin1998] and checks that two preparation passes plus one query cost
reproduce the quantum-time expression when the database size is even.

## Main statements

* `walsh_character_projectors`: The Walsh phase states satisfy both the Kronecker-delta
  inner-product identity and the corresponding projection identity.
* `proposedWalshTime_decomposition_pow`: For positive `k`, the proposed time decomposition holds
  at database size `walshCount k`.

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

namespace Qatlib.Papers.SingleQuery97.MainResults.WalshSearch

open Qatlib.Papers.SingleQuery97.MainResults.CharacterSum

/-- The number `2^k` of binary labels of length `k`. -/
def walshCount (k : ℕ) : ℕ := 2 ^ k

/-- The Walsh label count is divisible by two when `k` is positive. -/
theorem two_dvd_walshCount {k : ℕ} (hk : 0 < k) : 2 ∣ walshCount k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  unfold walshCount
  rw [pow_succ]
  exact ⟨2 ^ j, mul_comm _ _⟩

/-- The binary character phase state labeled by `z`. -/
noncomputable def walshState {k : ℕ} (z : Fin k → ZMod 2) :
    (Fin k → ZMod 2) → ℂ :=
  stateAmp (A := 2) (m := k) z

/-- Walsh phase states have inner product `1` for equal labels and `0` for distinct labels. -/
theorem walshStates_orthonormal {k : ℕ} (z z' : Fin k → ZMod 2) :
    inner (walshState z) (walshState z') = if z = z' then 1 else 0 :=
  inner_stateAmp (A := 2) (m := k) (by norm_num) z z'

/-- Projection onto a Walsh phase state preserves the equal-labeled state and annihilates
distinct-labeled states. -/
theorem walshMeasurement_distinguishes {k : ℕ} (z z' : Fin k → ZMod 2) :
    proj (walshState z) (walshState z') =
      if z = z' then walshState z' else 0 :=
  proj_family_diagonal walshState
    (fun i j => inner_stateAmp (A := 2) (m := k) (by norm_num) i j) z z'

/-- The Walsh phase states satisfy both the Kronecker-delta inner-product identity and the
corresponding projection identity. -/
theorem walsh_character_projectors {k : ℕ} (z z' : Fin k → ZMod 2) :
    (inner (walshState z) (walshState z') = if z = z' then 1 else 0) ∧
      (proj (walshState z) (walshState z') =
        if z = z' then walshState z' else 0) :=
  ⟨walshStates_orthonormal z z', walshMeasurement_distinguishes z z'⟩

/-- The proposed Walsh preparation-step count `1 + (n / 2) * k`. -/
def proposedWalshPrepSteps (n k : ℕ) : ℕ := 1 + n / 2 * k

/-- For even `n`, two proposed preparation passes total `2 + n*k` steps. -/
theorem proposedWalshPrepSteps_double {n k : ℕ} (hn : 2 ∣ n) :
    proposedWalshPrepSteps n k + proposedWalshPrepSteps n k = 2 + n * k := by
  obtain ⟨t, rfl⟩ := hn
  have h2 : (2 * t) / 2 = t := by omega
  unfold proposedWalshPrepSteps
  rw [h2]
  ring

/-- The proposed Walsh quantum time expression `2 + n*k + T`. -/
def proposedWalshQuantumTime (n k T : ℕ) : ℕ := 2 + n * k + T

/-- The proposed Walsh classical time expression `k / 2 + T*k`, with natural-number division. -/
def proposedWalshClassicalTime (k T : ℕ) : ℕ := k / 2 + T * k

/-- For even `n`, two proposed preparation passes plus query cost `T` equal the proposed Walsh
quantum time. -/
theorem proposedWalshTime_decomposition {n k T : ℕ} (hn : 2 ∣ n) :
    proposedWalshPrepSteps n k + proposedWalshPrepSteps n k + T = proposedWalshQuantumTime n k T := by
  rw [proposedWalshPrepSteps_double hn]
  rfl

/-- For positive `k`, the proposed time decomposition holds at database size `walshCount k`. -/
theorem proposedWalshTime_decomposition_pow {k T : ℕ} (hk : 0 < k) :
    proposedWalshPrepSteps (walshCount k) k + proposedWalshPrepSteps (walshCount k) k + T =
      proposedWalshQuantumTime (walshCount k) k T :=
  proposedWalshTime_decomposition (two_dvd_walshCount hk)

end Qatlib.Papers.SingleQuery97.MainResults.WalshSearch
