/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QActiveLearn14.NativeReflect

@[expose] public section

/-!
# Error accumulation in the reflecting agent's deliberation word

In [PaparoEtAl2014], Figure 2, each round checks the flags and then reflects about the
coherent input. The approximate reflection acts on a joint system with ancillas. An isometric
embedding represents the initialized ancillas, and the implemented word keeps the joint state
between rounds. The one-call estimate is needed only at checked ideal inputs. This module
derives the hybrid estimate and the precision allocation in Equation (26), given the
per-call estimate that must be supplied by the approximate-reflection construction.

[Fixed arXiv version](https://arxiv.org/abs/1401.4997v2)
-/

namespace Qatlib.Papers.QActiveLearn14.ApproxBudget

open Qatlib.Foundations.MatrixGeometry.FlagProjection

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y]

/-- Given a uniform one-call Euclidean error at each checked ideal input, every prefix of the
implemented joint word has error at most its length times that tolerance. The exact joint flag
check agrees with the paper's check on states with initialized ancillas. -/
theorem reflecting_word_error (S : Finset X) (v : EuclideanSpace ℂ X)
    (embed : EuclideanSpace ℂ X →ₗᵢ[ℂ] EuclideanSpace ℂ Y)
    (check approx : EuclideanSpace ℂ Y →ₗᵢ[ℂ] EuclideanSpace ℂ Y)
    (hcheck : ∀ x, check (embed x) = embed (checkFig S x))
    (ε : ℝ) (m : ℕ)
    (hcall : ∀ j < m,
      ‖approx (embed (checkFig S (runFig S v j))) -
        embed (reflect v (checkFig S (runFig S v j)))‖ ≤ ε) :
    ∀ n ≤ m, ‖((approx.comp check)^[n]) (embed v) - embed (runFig S v n)‖ ≤ n * ε := by
  intro n
  induction n with
  | zero => simp [runFig]
  | succ n ih =>
    intro hn
    let next := approx.comp check
    let x := (next^[n]) (embed v)
    let y := embed (runFig S v n)
    let z := embed (runFig S v (n + 1))
    have hstep : ‖next y - z‖ ≤ ε := by
      change ‖approx (check (embed (runFig S v n))) -
        embed (reflect v (checkFig S (runFig S v n)))‖ ≤ ε
      rw [hcheck]
      exact hcall n (by omega)
    rw [Function.iterate_succ_apply']
    change ‖next x - z‖ ≤ (↑(n + 1) : ℝ) * ε
    calc
      ‖next x - z‖ ≤ ‖next x - next y‖ + ‖next y - z‖ := by
        rw [← sub_add_sub_cancel (next x) (next y) z]
        exact norm_add_le _ _
      _ = ‖x - y‖ + ‖next y - z‖ := by rw [← map_sub, LinearIsometry.norm_map]
      _ ≤ (n : ℝ) * ε + ε := add_le_add (ih (by omega)) hstep
      _ = (↑(n + 1) : ℝ) * ε := by push_cast; ring

/-- If at most `2^r` rounds can be selected, `r + c` reflection repetitions suffice for the
terminal Euclidean error `2 · (1/2)^c` of [PaparoEtAl2014], Equation (26), uniformly over the
allowed round counts. The per-call tolerance is the error scale of Theorem 3. -/
theorem reflecting_word_precision (S : Finset X) (v : EuclideanSpace ℂ X)
    (embed : EuclideanSpace ℂ X →ₗᵢ[ℂ] EuclideanSpace ℂ Y)
    (check approx : EuclideanSpace ℂ Y →ₗᵢ[ℂ] EuclideanSpace ℂ Y)
    (hcheck : ∀ x, check (embed x) = embed (checkFig S x))
    (r c : ℕ)
    (hcall : ∀ j < 2 ^ r,
      ‖approx (embed (checkFig S (runFig S v j))) -
        embed (reflect v (checkFig S (runFig S v j)))‖ ≤ 2 * (1 / 2 : ℝ) ^ (r + c)) :
    ∀ n ≤ 2 ^ r,
      ‖((approx.comp check)^[n]) (embed v) - embed (runFig S v n)‖ ≤ 2 * (1 / 2 : ℝ) ^ c := by
  intro n hn
  have hcast : (n : ℝ) ≤ (2 : ℝ) ^ r := by exact_mod_cast hn
  calc
    _ ≤ (n : ℝ) * (2 * (1 / 2 : ℝ) ^ (r + c)) :=
      reflecting_word_error S v embed check approx hcheck _ _ hcall n hn
    _ ≤ (2 : ℝ) ^ r * (2 * (1 / 2 : ℝ) ^ (r + c)) := by gcongr
    _ = _ := by
      rw [pow_add]
      calc
        _ = ((2 : ℝ) ^ r * (1 / 2) ^ r) * (2 * (1 / 2) ^ c) := by ring
        _ = _ := by rw [← mul_pow]; norm_num

end Qatlib.Papers.QActiveLearn14.ApproxBudget
