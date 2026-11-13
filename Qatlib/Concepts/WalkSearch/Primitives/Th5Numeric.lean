/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.QuantumAccess.ResidualDiagnosticContracts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Obstruction to a logarithm-free subgraph cost bound

`logarithmicSetupCollisionSolver` is a rejecting solver whose charge contains a logarithmic
setup factor. The module uses exact fourth-power windows and a real-exponent identity to refute
`Th5Numeric`, clarifying the numerical assumptions in subset-finding cost estimates
[ChildsEisenberg2003].

## Main statements

* `fourth_power_window`: identify the least fourth-power window at powers of two.
* `th5Numeric_obstruction`: the numerical contract is false.

## References

* [Childs and Eisenberg, 2003][ChildsEisenberg2003]
-/

open Qatlib.Concepts.WalkSearch.QuantumAccess.Walk
open Qatlib.Concepts.WalkSearch.WalkAlgorithms

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.WalkSearch.Primitives

/-- A collision solver that always returns `none`, has exponent zero, and charges `(Nat.log 2 (n
+ 1) + 2) * s`. -/
def logarithmicSetupCollisionSolver : KCollisionSolver where
  seed := Unit
  seedFin := inferInstance
  seedNe := inferInstance
  cExp := 0
  κ := 1
  run := fun {_n _k} _r _R _s _u _c _ρ => none
  cost := fun {n _k} _r _R s _u _c _ρ => (Nat.log 2 (n + 1) + 2) * s
  sound := by intros; contradiction
  reject := by intros; rfl
  finds := by intros; simp
  charges := by
    intro n k r R s u c ρ
    rw [one_mul]
    exact Nat.mul_le_mul_left (Nat.log 2 (n + 1) + 2)
      (Nat.le_add_right s ((n / r) ^ (k / 2) * (c + Nat.sqrt r * u)))

/-- The two fourth-power window inequalities for `2 ^ (4 * m)` force `r = 2 ^ (3 * m)`. -/
theorem fourth_power_window (m r : ℕ)
    (hl : (2 ^ (4 * m)) ^ (4 - 1) ≤ r ^ 4)
    (hu : (r - 1) ^ 4 < (2 ^ (4 * m)) ^ (4 - 1)) : r = 2 ^ (3 * m) := by
  have heq : (2 ^ (4 * m)) ^ (4 - 1) = (2 ^ (3 * m)) ^ 4 := by
    simp only [← pow_mul, show 4 - 1 = 3 by decide]
    congr 1
    omega
  rw [heq] at hl hu
  have hlo : 2 ^ (3 * m) ≤ r := (Nat.pow_le_pow_iff_left (by decide : 4 ≠ 0)).mp hl
  have hhi : r - 1 < 2 ^ (3 * m) :=
    (Nat.pow_lt_pow_iff_left (by decide : 4 ≠ 0)).mp hu
  omega

/-- The real power `(2 ^ (4 * m)) ^ (2 - 2 / 4)` equals the real cast of `2 ^ (3 * m) * 2 ^ (3 *
m)`. -/
theorem fourth_power_headline (m : ℕ) :
    ((2 ^ (4 * m) : ℕ) : ℝ) ^ ((2 : ℝ) - 2 / (4 : ℝ)) =
      (((2 ^ (3 * m)) * (2 ^ (3 * m)) : ℕ) : ℝ) := by
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hexp : ((4 * m : ℕ) : ℝ) * ((2 : ℝ) - 2 / (4 : ℝ)) = ((6 * m : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hexp, Real.rpow_natCast, ← pow_add]
  congr 1
  omega

/-- The proposition `Th5Numeric` is false. -/
theorem th5Numeric_obstruction : ¬ Th5Numeric := by
  intro h
  obtain ⟨C, hC, hb⟩ := h 4 (by decide) logarithmicSetupCollisionSolver (by decide)
  obtain ⟨m, hm⟩ := exists_nat_gt C
  let n := 2 ^ (4 * m)
  let H : OGraph 4 := ⟨∅, by simp, by simp⟩
  obtain ⟨r, _hr, hl, hu, hcost⟩ := hb n (by dsimp [n]; positivity) H 0
    (fun _ _ => false) 0 (by simpa using hC.le)
  have hr := fourth_power_window m r hl hu
  subst r
  have hc := hcost (fun _ => ())
  change (((Nat.log 2 (n + 1) + 2) * ((2 ^ (3 * m)) * (2 ^ (3 * m))) : ℕ) : ℝ) ≤
    C * ((n : ℝ) ^ ((2 : ℝ) - 2 / (4 : ℝ))) at hc
  dsimp [n] at hc
  rw [fourth_power_headline, Nat.cast_mul] at hc
  have hpos : (0 : ℝ) < (((2 ^ (3 * m)) * (2 ^ (3 * m)) : ℕ) : ℝ) := by positivity
  have hlogC := (mul_le_mul_iff_of_pos_right hpos).mp hc
  have hlog : 4 * m ≤ Nat.log 2 (n + 1) :=
    Nat.le_log_of_pow_le (by decide) (by dsimp [n]; omega)
  have hlogR : ((4 * m : ℕ) : ℝ) ≤ ((Nat.log 2 (n + 1) + 2 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (hlog.trans (Nat.le_add_right _ _))
  push_cast at hlogR
  dsimp [n] at hlogR
  push_cast at hlogC
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

end Qatlib.Concepts.WalkSearch.Primitives
