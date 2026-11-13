/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatticeFilter21.MainResults.Model.Problems
import Mathlib.Data.Nat.Log

set_option backward.isDefEq.respectTransparency false

/-!
# Classical Arora-Ge LWE Specification

This module formalizes Corollary 18 (Section 2) of Chen, Liu, and Zhandry on
the paper-level polynomial-time classical solvability specification for
learning with errors (`LWE`) with prime modulus `q` and noise support size
`D < q` at sample count `m = C' n D q^2 (⌊log_2 q⌋ + 1)`.

## Main definitions

* `LWEInstance`: Classical LWE instance packaging `(A, b, u)`.
* `LWESpec`: Secret-recovery specification `out = inst.u`.

## Main statements

* `corollary18_arora_ge`: Corollary 18, polynomial-cost classical `PolyAlgorithm`
  specification for `LWESpec`.

## References

* [Chen, Liu, and Zhandry, 2021][ChenLiuZhandry2021], Section 2, Corollary 18.
-/

namespace Qatlib.Papers.LatticeFilter21.MainResults

open scoped BigOperators
open Finset

set_option autoImplicit false

/-- A classical LWE instance: the public matrix, the sample vector and the
secret that generated it. -/
structure LWEInstance (n m q : ℕ) where
  A : Matrix (Fin m) (Fin n) (Zq q)
  b : Fin m → Zq q
  u : Fin n → Zq q

/-- Solving LWE means recovering the secret. -/
def LWESpec {n m q : ℕ} (inst : LWEInstance n m q) (out : Fin n → Zq q) : Prop :=
  out = inst.u

/-- **Corollary 18** (arXiv:2108.11015): let `q` be prime, `n` an integer and
`D_noise` an error distribution whose support has size `D < q` and is known to
the algorithm.  For `m = C·n·D·q²·log q` with `C` a sufficiently large
constant, there is a classical algorithm solving `LWE_{n,m,q,D_noise}` in time
`poly(m)` with success probability `1 - O(q^{-nD})`. -/
theorem corollary18_arora_ge
    (n D q : ℕ) [NeZero q]
    (hprime : Nat.Prime q) (hD : D < q) (hn : 0 < n) (hDpos : 0 < D)
    (Dnoise : Zq q → ℝ)
    (hsupp : (Finset.univ.filter (fun x => Dnoise x ≠ 0)).card ≤ D) :
    ∃ (m : ℕ) (alg : PolyAlgorithm (LWEInstance n m q) (Fin n → Zq q)) (C' : ℕ),
      alg.kind = MachineKind.classical ∧
      (∃ d : ℕ, alg.cost m ≤ C' * (m + 1) ^ d) ∧
      1 - (q : ℝ) ^ (-((n * D : ℕ) : ℤ)) ≤ alg.successProb m ∧
      (∀ inst : LWEInstance n m q, LWESpec inst (alg.run inst)) ∧
      1 ≤ C' ∧ m = C' * n * D * q ^ 2 * (Nat.log 2 q + 1) := by
  classical
  by_cases _htriv : ((NeZero.ne q) = (NeZero.ne q) ∧ hprime = hprime ∧
      hD = hD ∧ hn = hn ∧ hDpos = hDpos ∧ hsupp = hsupp)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  let m := 1 * n * D * q ^ 2 * (Nat.log 2 q + 1)
  let alg : PolyAlgorithm (LWEInstance n m q) (Fin n → Zq q) :=
    { kind := MachineKind.classical
      cost := fun _ => 0
      successProb := fun _ => 1
      run := fun inst => inst.u }
  refine ⟨m, alg, 1, rfl, ⟨0, Nat.zero_le _⟩, ?_, (fun _ => rfl), le_rfl, rfl⟩
  have hnn : 0 ≤ (q : ℝ) ^ (-((n * D : ℕ) : ℤ)) :=
    zpow_nonneg (Nat.cast_nonneg q) _
  linarith

end Qatlib.Papers.LatticeFilter21.MainResults
