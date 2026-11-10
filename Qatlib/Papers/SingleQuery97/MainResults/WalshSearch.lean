/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.CharacterSum
set_option warningAsError false

namespace Qatlib.Papers.SingleQuery97.MainResults.WalshSearch

open Qatlib.Papers.SingleQuery97.MainResults.CharacterSum

def walshCount (k : ℕ) : ℕ := 2 ^ k

theorem two_dvd_walshCount {k : ℕ} (hk : 0 < k) : 2 ∣ walshCount k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  unfold walshCount
  rw [pow_succ]
  exact ⟨2 ^ j, mul_comm _ _⟩

noncomputable def walshState {k : ℕ} (z : Fin k → ZMod 2) :
    (Fin k → ZMod 2) → ℂ :=
  stateAmp (A := 2) (m := k) z

theorem walshStates_orthonormal {k : ℕ} (z z' : Fin k → ZMod 2) :
    inner (walshState z) (walshState z') = if z = z' then 1 else 0 :=
  inner_stateAmp (A := 2) (m := k) (by norm_num) z z'

theorem walshMeasurement_distinguishes {k : ℕ} (z z' : Fin k → ZMod 2) :
    proj (walshState z) (walshState z') =
      if z = z' then walshState z' else 0 :=
  proj_family_diagonal walshState
    (fun i j => inner_stateAmp (A := 2) (m := k) (by norm_num) i j) z z'

theorem walsh_character_projectors {k : ℕ} (z z' : Fin k → ZMod 2) :
    (inner (walshState z) (walshState z') = if z = z' then 1 else 0) ∧
      (proj (walshState z) (walshState z') =
        if z = z' then walshState z' else 0) :=
  ⟨walshStates_orthonormal z z', walshMeasurement_distinguishes z z'⟩

def proposedWalshPrepSteps (n k : ℕ) : ℕ := 1 + n / 2 * k

theorem proposedWalshPrepSteps_double {n k : ℕ} (hn : 2 ∣ n) :
    proposedWalshPrepSteps n k + proposedWalshPrepSteps n k = 2 + n * k := by
  obtain ⟨t, rfl⟩ := hn
  have h2 : (2 * t) / 2 = t := by omega
  unfold proposedWalshPrepSteps
  rw [h2]
  ring

def proposedWalshQuantumTime (n k T : ℕ) : ℕ := 2 + n * k + T

def proposedWalshClassicalTime (k T : ℕ) : ℕ := k / 2 + T * k

theorem proposedWalshTime_decomposition {n k T : ℕ} (hn : 2 ∣ n) :
    proposedWalshPrepSteps n k + proposedWalshPrepSteps n k + T = proposedWalshQuantumTime n k T := by
  rw [proposedWalshPrepSteps_double hn]
  rfl

theorem proposedWalshTime_decomposition_pow {k T : ℕ} (hk : 0 < k) :
    proposedWalshPrepSteps (walshCount k) k + proposedWalshPrepSteps (walshCount k) k + T =
      proposedWalshQuantumTime (walshCount k) k T :=
  proposedWalshTime_decomposition (two_dvd_walshCount hk)

end Qatlib.Papers.SingleQuery97.MainResults.WalshSearch
