/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.ElementDistinctnessDefs

/-!
# Verified collision-search endpoints

`dev_verified_collision_algorithm` proves verified-collision correctness with `N` queries and `N
* dataBits N M` work bits, while `dev_uniform_success_law` gives the exact success law for
native read-all search. These endpoints accompany the quantum-walk element-distinctness
framework of [Ambainis2007ElementDistinctness].

The clause endpoints also provide a conditional QRAM implementation bridge, a compact-memory
result imported from the walk-spectrum development, and a prime-square existence bound `N ≤ p^2
≤ 4 * (N + 1)^2`. The precise specifications are defined in `ElementDistinctnessDefs`.

## Main statements

* `dev_verified_collision_algorithm`: correct collision search with read-all resource bounds.
* `dev_uniform_success_law`: exact average success characterized by collision existence.
* `dev_near_prime_power_window`: a prime square in the stated window.
* `clause28_endpoint`–`clause33_endpoint`: the corresponding specification endpoints.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.WalkFind.UniqueCollision
open Qatlib.Concepts.WalkFind.WalkSpectrum

namespace Qatlib.Concepts.WalkFind.SearchAlgorithm

open Qatlib
open scoped Classical BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- For `k ≥ 2` and positive input and value-domain sizes, there exists a correct
verified-collision query algorithm using at most `N` queries per seed and at most `N *
dataBits N M` work bits. -/
theorem dev_verified_collision_algorithm : CoreVerifiedCollisionAlgorithm := by
  intro k N M _ hk hN hM
  by_cases h : N < k
  · refine ⟨nativeReject N M k hN, nativeReject_correct N M k hN h, ?_, ?_⟩
    · intro s
      rw [nativeReject_queries]
      exact_mod_cast Nat.zero_le _
    · have hbits : (nativeReject N M k hN).workBits ≤ N * dataBits N M := by
        simp [nativeReject]
      exact_mod_cast hbits
  · refine ⟨nativeReadAll N M k hN, nativeReadAll_correct N M k hN, ?_, ?_⟩
    · intro s
      rw [nativeReadAll_queries]
    · exact_mod_cast (nativeReadAll_memory N M k hN)

/-- The native read-all algorithm has average success `1` exactly when the input has a
`k`-collision, and `0` otherwise. -/
theorem dev_uniform_success_law : CoreUniformSuccessLaw := by
  intro k N M _ hN x
  exact nativeReadAll_probability N M k hN x

/-- For every `N ≥ 2`, there is a prime `p` with `N ≤ p^2 ≤ 4 * (N + 1)^2`. -/
theorem dev_near_prime_power_window : CoreNearPrimePowerWindow := by
  intro N hN
  have hN1 : 1 ≤ N := by omega
  set m := Nat.sqrt N + 1 with hm
  have hm0 : 0 < m := by omega
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
  refine ⟨p, hp, ?_, ?_⟩
  · have hlt : N < (Nat.sqrt N + 1) ^ 2 := Nat.lt_succ_sqrt' N
    have hsq : N ≤ m ^ 2 := by
      rw [hm]
      omega
    have hp2' : m ^ 2 ≤ p ^ 2 := by
      have : m ≤ p := by omega
      gcongr
    omega
  · have hsqrtle : Nat.sqrt N ≤ N := Nat.sqrt_le_self N
    have hmle : m ≤ N + 1 := by
      rw [hm]
      omega
    calc
      p ^ 2 ≤ (2 * m) ^ 2 := by
        have : p ≤ 2 * m := hp2
        gcongr
      _ = 4 * m ^ 2 := by ring
      _ = 4 * (Nat.sqrt N + 1) ^ 2 := by rw [hm]
      _ ≤ 4 * (N + 1) ^ 2 := by
        have : Nat.sqrt N + 1 ≤ N + 1 := by omega
        gcongr

/-- Establishes the clause 28 specification of correct verified-collision search with the
read-all query and memory bounds. -/
theorem clause28_endpoint : clause28Spec := dev_verified_collision_algorithm

/-- An effective QRAM implementation contract implies the QRAM implementation contract. -/
theorem clause29_endpoint : clause29Spec := fun h => qRAMImplementation_of_effective h

/-- Establishes the effective-to-QRAM bridge, the near-prime-power consequence of
`Algorithm3NativeContract`, and the stated obstruction to a narrow binary prime-power
window. -/
theorem clause30_endpoint : clause30Spec := by
  refine ⟨fun h => qRAMImplementation_of_effective h, ?_, ?_⟩
  · intro h k hk
    exact algorithm3Native_near_primepower h k hk
  · intro a
    exact binaryPrimePower_near_failure a

/-- Establishes the clause 31 uniform success law for the native read-all collision algorithm. -/
theorem clause31_endpoint : clause31Spec := dev_uniform_success_law

/-- Establishes the existing `CompactMemorySpec` through the walk-spectrum compact-memory
result. -/
theorem clause32_endpoint : clause32Spec := Qatlib.Concepts.WalkFind.WalkSpectrum.clause32

/-- Establishes the clause 33 prime-square window `N ≤ p^2 ≤ 4 * (N + 1)^2` for `N ≥ 2`. -/
theorem clause33_endpoint : clause33Spec := dev_near_prime_power_window

end Qatlib.Concepts.WalkFind.SearchAlgorithm
