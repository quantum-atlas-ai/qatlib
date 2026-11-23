module

public import Qatlib.Papers.QWalkAmbainis03.Algorithm3.IsolationLittleO
public import Qatlib.Papers.QWalkAmbainis03.Algorithm3.CollisionPackingLog
public import Qatlib.Papers.QWalkAmbainis03.QRAMModel.BadStateScale
public import Qatlib.Concepts.WalkFind.SearchAlgorithm.EfficientPermutationFamily
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Consumer regression tests for the QWalkAmbainis03 increments

Ordinary `module` consumers of the three incremental results for
[Ambainis2007ElementDistinctness]: the little-o isolation bridge (Lemma 4), the
logarithmic collision-packing threshold (Claim 8) and the `N^(-3/2)`
bad-state scale with its hybrid accumulation (Lemmas 5 and 6). Each test
exercises the corresponding theorem on an inhabited domain: isolation with
the uniform permutation family, a four-point collision input, a five-point
QRAM counting estimate, and a two-step unitary evolution.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace QatlibTests.QWalkAmbainis03WalkBoundsRegression

open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.WalkFind.QRAMModel
open Qatlib.Concepts.WalkFind.UniqueCollision
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Papers.QWalkAmbainis03.Algorithm3.IsolationLittleO
open Qatlib.Papers.QWalkAmbainis03.Algorithm3.CollisionPackingLog
open Qatlib.Papers.QWalkAmbainis03.QRAMModel.BadStateScale
open scoped Classical BigOperators

noncomputable section

/-- At collision size `k = 2` the isolation error is eventually positive and
below the `N^(-1/4)` scale: the little-o bridge is non-vacuous. -/
theorem isolationError_eventually_positive_and_small :
    ∃ N : ℕ, 0 < isolationError 2 N ∧
      isolationError 2 N ≤ (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨N0, hN0⟩ := isolationError_eventually_le 2 (show (0 : ℝ) < 1 by norm_num)
  refine ⟨max N0 1, ?_, by simpa using hN0 _ (Nat.le_max_left N0 1)⟩
  have hNpos : (0 : ℝ) < (max N0 1 : ℕ) := by exact_mod_cast (by omega : 0 < max N0 1)
  have hA : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (Nat.floor (Real.log ((max N0 1 : ℕ) : ℝ))) :=
    pow_nonneg (by norm_num) _
  have hB : (0 : ℝ) < 4 / ((max N0 1 : ℕ) : ℝ) := by positivity
  have hC : (0 : ℝ) ≤ 16 * (2 : ℝ) ^ 2 *
      (Real.log ((max N0 1 : ℕ) : ℝ) + 1) ^ 2 / Real.sqrt ((max N0 1 : ℕ) : ℝ) := by
    positivity
  unfold isolationError
  linarith

/-- The strict probability comparison applies at a positive scale with a
retained-prefix model on two or more indices and a uniform permutation family. -/
theorem isolation_uniform_permutation_example :
    ∃ N : ℕ, 0 < N ∧
      let q := N + 2
      let x : Fin q → ZMod 5 := fun _ => 0
      let π := allPermutationFamily q
      eventProbability (fun s => ¬ ∃ S, CollisionIn 2 x (retained 2 Finset.univ π s) S) -
          (N : ℝ) ^ (-(1 / 4 : ℝ)) <
        eventProbability (fun s => ∃! S, CollisionIn 2 x (retained 2 Finset.univ π s) S) := by
  obtain ⟨N0, hN0⟩ := lemma4_strict_eventually 2 (by norm_num) 1 (by norm_num)
  let N := N0 + 1
  let q := N + 2
  have hN : 0 < N := by dsimp [N]; omega
  have hsize : Real.sqrt (N : ℝ) ≤ ((Finset.univ : Finset (Fin q)).card : ℝ) := by
    simp only [Finset.card_univ, Fintype.card_fin]
    exact (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hN))).trans
      (by exact_mod_cast Nat.le_add_right N 2)
  have hcollision : ∃ S, CollisionIn 2 (fun _ : Fin q => (0 : ZMod 5)) Finset.univ S := by
    refine ⟨{0, 1}, Finset.subset_univ _, ?_, 0, fun _ _ => rfl⟩
    rw [Finset.card_insert_of_notMem]
    · simp
    · simp
  refine ⟨N, hN, ?_⟩
  simpa only [one_mul] using hN0 N q q.factorial 5 (by dsimp [N]; omega)
    (Nat.factorial_pos _) (by norm_num) (fun _ => 0) Finset.univ (allPermutationFamily q)
    hsize (allPermutationFamily_approxIndependent q _ N hN) hcollision

/-- The logarithmic packing threshold at `N = 8` is three disjoint collisions. -/
theorem logPackingThreshold_eight : logPackingThreshold 8 = 3 := by
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    have h : (8 : ℝ) = 2 ^ 3 := by norm_num
    rw [h, Real.log_pow]
    norm_num
  rw [logPackingThreshold, Nat.ceil_eq_iff (by decide : (3 : ℕ) ≠ 0)]
  norm_num
  rw [h8]
  constructor <;> linarith

/-- A concrete four-point input over `ZMod 5` with the single colliding pair
`{0, 1}` and distinct remaining values. -/
def pairInput : Fin 4 → ZMod 5 :=
  fun i => if i.val < 2 then 0 else (i.val : ZMod 5)

/-- No three pairwise disjoint pairs fit into a four-point domain, whatever
the input values: an injective packing would embed `Fin 3 × Fin 2` into
`Fin 4`. -/
theorem pairInput_no_log_packing :
    ¬ ∃ i : Fin (logPackingThreshold 8) → Fin 2 → Fin 4,
      Function.Injective (fun z : Fin (logPackingThreshold 8) × Fin 2 => i z.1 z.2) ∧
        ∀ a, CollisionIn 2 pairInput Finset.univ (Finset.univ.image (i a)) := by
  rw [logPackingThreshold_eight]
  rintro ⟨i, hinj, -⟩
  have hcard := Fintype.card_le_of_injective _ hinj
  norm_num [Fintype.card_prod, Fintype.card_fin] at hcard

/-- Claim 8 on the concrete pair input: the collision support, which is the
pair `{0, 1}`, obeys the logarithmic bound `4 log 8` at `k = 2`. -/
theorem pairInput_support_lt_log :
    ((collisionSupport 2 pairInput Finset.univ).card : ℝ) <
      2 * (2 : ℝ) * Real.log (8 : ℝ) :=
  collisionSupport_card_lt_log 2 (by norm_num) pairInput Finset.univ 8 (by norm_num)
    pairInput_no_log_packing

/-- The Lemma 6 scale at `N = 4`: both `1/sqrt(4^3)` and the real power
`4^(-3/2)` equal `1/8`. -/
theorem badState_scale_four :
    1 / Real.sqrt ((4 : ℝ) ^ 3) = 1 / 8 ∧ (4 : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / 8 := by
  have hsqrt : Real.sqrt ((4 : ℝ) ^ 3) = 8 := by
    rw [show ((4 : ℝ) ^ 3) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs : 1 / Real.sqrt ((4 : ℝ) ^ 3) = 1 / 8 := by rw [hsqrt]
  exact ⟨hs, (one_div_sqrt_cube_eq_rpow 4 (by norm_num)).symm.trans hs⟩

/-- The squared bad-state bound consumes actual counts of slow operations
at the five-point Johnson-walk parameters `k = r = 2`. -/
theorem badState_sq_example (D : CollisionDataStructure 5 5 2)
    (x : Fin 5 → ZMod 5) (I : Finset (Fin 5)) (hI : I.card = 2)
    (a : Fin 5 → ℂ) (ha : Normalized a) (clock : ℕ)
    (hfail : ∀ i : Fin 5,
      ((Finset.univ.filter (fun z : JRState 5 2 × Fin (2 ^ D.seedBits) =>
        jwTypeOf I z.1 = jwPsiCoord 2 i ∧
          ¬ dataOperationsFast D x z.1.val.1 z.2 clock)).card : ℝ) /
        ((jwCnt 2 5 2 (jwPsiCoord 2 i).1 (jwPsiCoord 2 i).2 : ℝ) *
          (2 ^ D.seedBits : ℝ)) ≤ 1 / (5 : ℝ) ^ 3) :
    ‖toEuclidean_fromVec (fun z : JRState 5 2 × Fin (2 ^ D.seedBits) =>
      if dataOperationsFast D x z.1.val.1 z.2 clock then 0
      else (∑ i, a i * jwPsiBigAt 2 5 2 I i z.1) *
        ((1 / Real.sqrt (2 ^ D.seedBits : ℝ) : ℝ) : ℂ))‖ ^ 2 ≤ 1 / (5 : ℝ) ^ 3 :=
  lemma6_norm_sq_le 2 5 5 2 D x I a clock
    (by decide) (by decide) (by decide) (by decide) (by decide) hI ha hfail

/-- A two-step identity evolution on a two-dimensional space with zero bad
components has Euclidean error below the hybrid bound
`2 * 2 * 4^(-3/2) = 1/2`, by direct application of the accumulated
`N^(-3/2)` hybrid estimate at `T = 2`, `N = 4`. -/
theorem hybrid_identity_example :
    ‖Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec
      (Qatlib.Foundations.QueryWordCore.Circuit.Run 1
          ((List.ofFn (fun _ : Fin 2 => (1 : Matrix (Fin 2) (Fin 2) ℂ))).map
            Qatlib.Foundations.QueryWordCore.Circuit.Step.gate)
          (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0) -
        Qatlib.Foundations.QueryWordCore.Circuit.Run 1
          ((List.ofFn (fun _ : Fin 2 => (1 : Matrix (Fin 2) (Fin 2) ℂ))).map
            Qatlib.Foundations.QueryWordCore.Circuit.Step.gate)
          (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0))‖ ≤
      2 * (2 : ℝ) * (4 : ℝ) ^ (-(3 / 2 : ℝ)) :=
  hybrid_error_le_of_bad_bounds 2 4 (by decide) (by decide)
    (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (fun _ => (0 : Qatlib.Foundations.PureStateMath.QState (Fin 2)))
    (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0)
    (fun _ => by
      rw [Matrix.mem_unitaryGroup_iff]
      simp)
    (fun _ => by
      rw [Matrix.mem_unitaryGroup_iff]
      simp)
    (fun _ => rfl)
    (fun _ => by
      have hz : Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec
          (0 : Qatlib.Foundations.PureStateMath.QState (Fin 2)) = 0 := by
        simp [Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec]
      rw [hz, norm_zero]
      exact Real.rpow_nonneg (by norm_num) _)

end

end QatlibTests.QWalkAmbainis03WalkBoundsRegression
