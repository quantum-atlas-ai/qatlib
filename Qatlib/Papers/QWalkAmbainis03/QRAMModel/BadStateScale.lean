/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.WalkFind.QRAMModel.QRAMClaims
public import Qatlib.Concepts.WalkFind.QRAMModel.TruncationHybridQuan
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The `N^(-3/2)` scale of the truncated data-structure bad state

Fixed source: [Ambainis2007ElementDistinctness], Lemmas 5 and 6 (quant-ph/0311001v9,
Section 5). Lemma 5 bounds the Euclidean distance between the ideal and
truncated evolutions by `sum_t 2||psi_bad t||`, and Lemma 6 asserts
`||psi_bad t|| = O(N^(-3/2))` for every step `t`.

The public library proves both ingredients in Euclidean form: the hybrid
bound `truncationHybrid_answer` for `toEuclidean_fromVec` vectors, and the
norm step of Lemma 6 (`lemma6`), which from a per-type slow-operation
fraction at most `1/N^3` concludes `||bad|| ≤ 1/sqrt(N^3)`. Missing were the
explicit power form of that scale and its accumulation through the hybrid.
This module records both, with the true Euclidean norm throughout: no
coordinate maximum or other weaker norm is used.

Concretely, `1/sqrt(N^3) = N^(-3/2)` as a real power, the squared Euclidean
norm is at most `1/N^3`, and `T` steps each obeying the `N^(-3/2)` bound
accumulate to at most `2T * N^(-3/2)`. Deriving the `1/N^3` slow-operation
fraction for the source's hash/skip-list structure itself remains open,
exactly as recorded for Lemma 6; this module only consumes the proved norm
step at its stated hypotheses.

## Main statements

* `one_div_sqrt_cube_eq_rpow`: `1/sqrt(N^3) = N^(-3/2)`.
* `lemma6_rpow_form`: Lemma 6's norm step in real-power form.
* `lemma6_norm_sq_le`: the squared Euclidean bound `||bad||^2 ≤ 1/N^3`.
* `hybrid_error_le_of_bad_bounds`: the hybrid accumulation at the
  `N^(-3/2)` scale.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Papers.QWalkAmbainis03.QRAMModel.BadStateScale

open Qatlib.Concepts.WalkFind.QRAMModel
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.WalkFind.UniqueCollision
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.QueryWordCore.Circuit
open Matrix
open scoped BigOperators Classical

noncomputable section

/-- The Lemma 6 scale as a real power: `1/sqrt(N^3) = N^(-3/2)` for positive
`N`. -/
theorem one_div_sqrt_cube_eq_rpow (N : ℕ) (hN : 0 < N) :
    1 / Real.sqrt ((N : ℝ) ^ 3) = (N : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsqrt : Real.sqrt ((N : ℝ) ^ 3) = (N : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow ((N : ℝ) ^ 3)]
    rw [← Real.rpow_natCast (N : ℝ) 3, ← Real.rpow_mul hNpos.le]
    norm_num
  rw [hsqrt, Real.rpow_neg hNpos.le, one_div]

/-- Lemma 6 of [Ambainis2007ElementDistinctness] in real-power form: under the same
per-type slow-operation fraction bound `1/N^3` as the library's norm step,
the Euclidean norm of the bad state is at most `N^(-3/2)`, the source's
`O(N^(-1.5))` scale with constant one. -/
theorem lemma6_rpow_form (k N M r : ℕ) (D : CollisionDataStructure N M r)
    (x : Fin N → ZMod M) (I : Finset (Fin N))
    (a : Fin (2 * k + 1) → ℂ) (clock : ℕ)
    (hN : 0 < N) (hM : 0 < M) (_hk : 0 < k) (hkr : k ≤ r) (hkNr : k < N - r)
    (_hI : I.card = k)
    (ha : Normalized a)
    (hfail : ∀ i : Fin (2 * k + 1),
      ((Finset.univ.filter (fun z : JRState N r × Fin (2 ^ D.seedBits) =>
          jwTypeOf I z.1 = jwPsiCoord k i ∧
            ¬ dataOperationsFast D x z.1.val.1 z.2 clock)).card : ℝ) /
        ((jwCnt k N r (jwPsiCoord k i).1 (jwPsiCoord k i).2 : ℝ) *
          (2 ^ D.seedBits : ℝ)) ≤ 1 / (N : ℝ) ^ 3) :
    ‖toEuclidean_fromVec (fun z : JRState N r × Fin (2 ^ D.seedBits) =>
      if dataOperationsFast D x z.1.val.1 z.2 clock then 0
      else (∑ i, a i * jwPsiBigAt k N r I i z.1) *
        ((1 / Real.sqrt (2 ^ D.seedBits : ℝ) : ℝ) : ℂ))‖ ≤
      (N : ℝ) ^ (-(3 / 2 : ℝ)) :=
  (Qatlib.Concepts.WalkFind.QRAMModel.lemma6 k N M r D x I a clock
    hN hM hkr hkNr ha hfail).trans_eq (one_div_sqrt_cube_eq_rpow N hN)

/-- The squared Euclidean form of Lemma 6: under the same hypotheses, the
squared Euclidean norm of the bad state is at most `1/N^3`. -/
theorem lemma6_norm_sq_le (k N M r : ℕ) (D : CollisionDataStructure N M r)
    (x : Fin N → ZMod M) (I : Finset (Fin N))
    (a : Fin (2 * k + 1) → ℂ) (clock : ℕ)
    (hN : 0 < N) (hM : 0 < M) (hk : 0 < k) (hkr : k ≤ r) (hkNr : k < N - r)
    (hI : I.card = k)
    (ha : Normalized a)
    (hfail : ∀ i : Fin (2 * k + 1),
      ((Finset.univ.filter (fun z : JRState N r × Fin (2 ^ D.seedBits) =>
          jwTypeOf I z.1 = jwPsiCoord k i ∧
            ¬ dataOperationsFast D x z.1.val.1 z.2 clock)).card : ℝ) /
        ((jwCnt k N r (jwPsiCoord k i).1 (jwPsiCoord k i).2 : ℝ) *
          (2 ^ D.seedBits : ℝ)) ≤ 1 / (N : ℝ) ^ 3) :
    ‖toEuclidean_fromVec (fun z : JRState N r × Fin (2 ^ D.seedBits) =>
      if dataOperationsFast D x z.1.val.1 z.2 clock then 0
      else (∑ i, a i * jwPsiBigAt k N r I i z.1) *
        ((1 / Real.sqrt (2 ^ D.seedBits : ℝ) : ℝ) : ℂ))‖ ^ 2 ≤
      1 / (N : ℝ) ^ 3 := by
  have h := lemma6_rpow_form k N M r D x I a clock hN hM hk hkr hkNr hI ha hfail
  rw [← one_div_sqrt_cube_eq_rpow N hN] at h
  have hsq : (1 / Real.sqrt ((N : ℝ) ^ 3)) ^ 2 = 1 / (N : ℝ) ^ 3 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 3)]
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq hsq

/-- Hybrid accumulation at the Lemma 6 scale (Lemmas 5 and 6 of
[Ambainis2007ElementDistinctness] composed): if two `T`-step unitary evolutions agree on
every ideal prefix minus its bad component, and every bad component has
Euclidean norm at most `N^(-3/2)`, then the final Euclidean distance is at
most `2T * N^(-3/2)`. The norm is the true Euclidean norm of
`toEuclidean_fromVec` throughout. -/
theorem hybrid_error_le_of_bad_bounds {H : Type} [Fintype H] [DecidableEq H] [Nonempty H]
    (T N : ℕ) (_hT : 0 < T) (_hN : 0 < N)
    (U V : Fin T → Matrix H H ℂ) (bad : Fin T → QState H)
    (ψ : QState H)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup H ℂ)
    (hV : ∀ i, V i ∈ Matrix.unitaryGroup H ℂ)
    (hagree : ∀ i, let ideal := Run 1 ((List.ofFn U).take i.val |>.map Step.gate) ψ
      U i *ᵥ (ideal - bad i) = V i *ᵥ (ideal - bad i))
    (hbad : ∀ i, ‖toEuclidean_fromVec (bad i)‖ ≤ (N : ℝ) ^ (-(3 / 2 : ℝ))) :
    ‖toEuclidean_fromVec (Run 1 ((List.ofFn U).map Step.gate) ψ -
      Run 1 ((List.ofFn V).map Step.gate) ψ)‖ ≤
      2 * (T : ℝ) * (N : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hhyb := Qatlib.Concepts.WalkFind.QRAMModel.truncationHybrid_answer
    H T U V bad ψ hU hV hagree
  refine hhyb.trans ?_
  calc (∑ i, 2 * ‖toEuclidean_fromVec (bad i)‖)
      ≤ ∑ _i : Fin T, 2 * (N : ℝ) ^ (-(3 / 2 : ℝ)) :=
        Finset.sum_le_sum (fun i _ => by
          exact mul_le_mul_of_nonneg_left (hbad i) (by norm_num))
    _ = 2 * (T : ℝ) * (N : ℝ) ^ (-(3 / 2 : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end

end Qatlib.Papers.QWalkAmbainis03.QRAMModel.BadStateScale
