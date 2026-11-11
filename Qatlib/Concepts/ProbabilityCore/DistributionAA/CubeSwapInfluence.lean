/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeSymmetry
import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeDistribution

/-!
# Swap energy controlled by flip influences

The module bounds the expected squared change under a coordinate swap by twice the sum of the
two coordinate flip influences under `nuWeight`. The proof uses slice symmetry and the two flip
path between an input and its swap.

This estimate supplies a variance comparison tool for Boolean cube functions in the polynomial
query setting of [BealsEtAl2001].

## Main statements

* `cube_swap_influence_le`: swap energy is at most twice the sum of the two flip influences for
  `0 < p < 1`.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open scoped Classical BigOperators

/-- For `0 < p < 1`, the expected squared change under swapping coordinates `i` and `j` on the
selected slice is at most twice the sum of their flip influences. -/
theorem cube_swap_influence_le {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {f : (Fin n → Bool) → ℝ} (i j : Fin n) :
    cubeExpect n (nuWeight p n) (fun x => (f x-f (cubeSwap x i j))^2) ≤
      2*(cubeInf n (nuWeight p n) f i+cubeInf n (nuWeight p n) f j) := by
  have hw := nuWeight_cubeWeight hp0 hp1 n
  have hpoint (x : Fin n → Bool) : (f x-f (cubeSwap x i j))^2 ≤
      2*((f x-f (cubeFlip x i))^2+
        (f (cubeSwap x i j)-f (cubeFlip (cubeSwap x i j) j))^2) := by
    by_cases hx : x i=x j
    · rw [cube_swap_same_bits x i j hx]
      nlinarith [sq_nonneg (f x-f (cubeFlip x i)), sq_nonneg (f x-f (cubeFlip x j))]
    · rw [cube_swap_flip_path x i j hx]
      nlinarith only [sq_nonneg (f x+f (cubeSwap x i j)-2*f (cubeFlip x i))]
  calc
    _ ≤ cubeExpect n (nuWeight p n) (fun x => 2*((f x-f (cubeFlip x i))^2+
          (f (cubeSwap x i j)-f (cubeFlip (cubeSwap x i j) j))^2)) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (hw.1 x)
    _ = _ := by
      rw [cube_expect_const_mul, cube_expect_add,
        cube_expect_swap p (fun x => (f x-f (cubeFlip x j))^2) i j]
      rfl

end Qatlib.Concepts.ProbabilityCore.DistributionAA
