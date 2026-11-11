/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Filter Asymptotics

namespace Qatlib.Papers.DepthGrover19.MainResults

/-- Database size `N = 2^n`. -/
def dbSize (n : ℕ) : ℝ := (2 : ℝ) ^ n

/-- The Grover angle: `sin θ = 1/√N` (Eq. (6)). -/
def groverTheta (n : ℕ) : ℝ := Real.arcsin (1 / Real.sqrt (dbSize n))

/-- Eq. (6): the success probability of `j` Grover iterations,
`P_n(j) = |<t|Gn^j|sn>|² = sin²((2j+1)θ)`. -/
def groverProb (n j : ℕ) : ℝ := Real.sin ((2 * (j : ℝ) + 1) * groverTheta n) ^ 2

/-- The per-iteration Grover depth `d(Gn^j) = (α+1) j d(Dn)` (Eq. (12), numerator). -/
def groverStepDepth (dD : ℕ → ℝ) (α : ℝ) (n j : ℕ) : ℝ :=
  (α + 1) * (j : ℝ) * dD n

/-- The depth-to-success ratio minimised in Eq. (12). -/
def groverRatio (dD : ℕ → ℝ) (α : ℝ) (n : ℕ) (j : ℕ) : ℝ :=
  groverStepDepth dD α n j / groverProb n j

/-- Eq. (12): Grover's minimal expected depth `dG(α) = min_j d(Gn^j)/P_n(j)`.
The minimum runs over the non-trivial iteration counts `j ≥ 1` (`j = 0` has zero
depth and is not a search).  Iterations with `P_n(j) = 0` are excluded: Lean's
total division would turn `0 / 0` into the spurious ratio `0`, whereas a
zero-success iteration has infinite MED. -/
def groverMED (dD : ℕ → ℝ) (α : ℝ) (n : ℕ) : ℝ :=
  sInf { r : ℝ | ∃ j : ℕ, groverProb n (j + 1) ≠ 0 ∧
    r = groverRatio dD α n (j + 1) }

/-- Eq. (6): the success probability is non-negative (it is a square). -/
theorem groverProb_nonneg (n j : ℕ) : 0 ≤ groverProb n j := by
  unfold groverProb
  exact sq_nonneg _

/-- Eq. (6): the success probability is at most one (`sin² ≤ 1`). -/
theorem groverProb_le_one (n j : ℕ) : groverProb n j ≤ 1 := by
  unfold groverProb
  simpa using Real.sin_sq_le_one ((2 * (j : ℝ) + 1) * groverTheta n)

/-- `√(2^n)` is nonzero, so the Grover angle is well defined. -/
lemma sqrt_dbSize_ne_zero (n : ℕ) : Real.sqrt (dbSize n) ≠ 0 := by
  apply ne_of_gt
  apply Real.sqrt_pos.2
  unfold dbSize
  positivity

/-- `3·2^n - 4 ≠ 0`: the one-step Grover probability does not vanish. -/
lemma three_dbSize_sub_four_ne_zero (n : ℕ) : 3 * dbSize n - 4 ≠ 0 := by
  unfold dbSize
  cases n with
  | zero => norm_num
  | succ k =>
    have hpow : (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 := by rw [pow_succ]
    have h2 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    rw [hpow]
    nlinarith

/-- Closed form of the one-step success probability:
`P_n(1) = (3·2^n - 4)² / (2^n)³` (from `sin 3θ = 3 sin θ - 4 sin³ θ`). -/
lemma groverProb_one_eq (n : ℕ) :
    groverProb n 1 = (3 * dbSize n - 4) ^ 2 / (dbSize n) ^ 3 := by
  unfold groverProb groverTheta
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (dbSize n) := by
    apply Real.sqrt_pos.2; unfold dbSize; positivity
  have hs : Real.sin (Real.arcsin (1 / Real.sqrt (dbSize n))) = 1 / Real.sqrt (dbSize n) := by
    rw [Real.sin_arcsin]
    · linarith [div_nonneg zero_le_one hsqrt_pos.le]
    · rw [div_le_iff₀ hsqrt_pos, one_mul]
      have h1 : (1 : ℝ) ≤ dbSize n := by
        unfold dbSize
        exact one_le_pow₀ (by norm_num)
      simpa using Real.sqrt_le_sqrt h1
  have harg : (2 * ((1 : ℕ) : ℝ) + 1) * Real.arcsin (1 / Real.sqrt (dbSize n)) =
      3 * Real.arcsin (1 / Real.sqrt (dbSize n)) := by norm_num
  rw [harg, Real.sin_three_mul, hs]
  have hN : dbSize n ≠ 0 := by unfold dbSize; positivity
  have hs2 : Real.sqrt (dbSize n) * Real.sqrt (dbSize n) = dbSize n := by
    rw [Real.mul_self_sqrt]; unfold dbSize; positivity
  field_simp
  have hpos : (0:ℝ) ≤ dbSize n := by unfold dbSize; positivity
  have h2 : Real.sqrt (dbSize n) ^ 2 = dbSize n := Real.sq_sqrt hpos
  have h6 : Real.sqrt (dbSize n) ^ 6 = (dbSize n)^3 := by
    rw [show (6:ℕ) = 2 * 3 by norm_num, pow_mul, h2]
  rw [h2, h6]
  ring

/-- The one-step Grover success probability is nonzero, so the guarded MED sets
used below are nonempty. -/
lemma groverProb_one_ne_zero (n : ℕ) : groverProb n 1 ≠ 0 := by
  rw [groverProb_one_eq]
  apply div_ne_zero
  · apply pow_ne_zero
    exact three_dbSize_sub_four_ne_zero n
  · exact pow_ne_zero 3 (by unfold dbSize; positivity)

/-- The Grover angle is non-negative. -/
lemma groverTheta_nonneg (n : ℕ) : 0 ≤ groverTheta n := by
  unfold groverTheta
  rw [Real.arcsin_nonneg]
  apply div_nonneg zero_le_one
  exact Real.sqrt_nonneg _

/-- `sin θ2 = 1/√b` with block size `b = 2^m` (Eq. (34)). -/
def sinTheta2 (m : ℕ) : ℝ := 1 / Real.sqrt ((2 : ℝ) ^ m)

/-- `θ2 = arcsin(1/√b)`. -/
def theta2 (m : ℕ) : ℝ := Real.arcsin (sinTheta2 m)

/-- The initial state `|sn>` in the basis `{|t>, |ntt>, |u>}` of Eq. (9), with
`N = 2^n`, block size `b = 2^m`: target coordinate `1/√N`, block-sum coordinate
`sin γ cos θ2`, rest coordinate `cos γ`, where `sin γ = √(b/N)`. -/
def v0 (n m : ℕ) : Fin 3 → ℝ :=
  ![ 1 / Real.sqrt ((2 : ℝ) ^ n),
     Real.sqrt ((2 : ℝ) ^ m / (2 : ℝ) ^ n) * Real.sqrt (1 - 1 / (2 : ℝ) ^ m),
     Real.sqrt (1 - (2 : ℝ) ^ m / (2 : ℝ) ^ n) ]

/-- Outer product `v wᵀ`. -/
def outerVec (v w : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of (fun i j => v i * w j)

/-- Global Grover operator `Gn = Dn Ut = (2|sn><sn| - 1)·diag(-1,1,1)` in the
basis of Eq. (9). -/
def globalStepMatrix (n m : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (2 • outerVec (v0 n m) (v0 n m) - 1) * Matrix.diagonal ![(-1 : ℝ), 1, 1]

/-- Local Grover operator `Gm` of Eq. (32) at `j = 1`: rotation by `2θ2` in the
target / block-sum plane, leaving `|u>` fixed. -/
def localStepMatrix (m : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![Real.cos (2 * theta2 m), Real.sin (2 * theta2 m), 0],
    ![-Real.sin (2 * theta2 m), Real.cos (2 * theta2 m), 0],
    ![0, 0, 1]]

/-- Matrix of one step (`true` = global `Gn`, `false` = local `Gm`). -/
def stepMatrix (n m : ℕ) : Bool → Matrix (Fin 3) (Fin 3) ℝ
  | true => globalStepMatrix n m
  | false => localStepMatrix m

/-- Product matrix of a word of steps in application order. -/
def planMatrix (n m : ℕ) : List Bool → Matrix (Fin 3) (Fin 3) ℝ
  | [] => 1
  | s :: rest => planMatrix n m rest * stepMatrix n m s

/-- Success probability `|<t|S|sn>|²` of a plan word. -/
def planProb (n m : ℕ) (w : List Bool) : ℝ :=
  ((planMatrix n m w).mulVec (v0 n m)) 0 ^ 2

/-- Depth of a plan word: `(g+l)·α·d(Dn) + g·d(Dn) + l·d(Dm)`. -/
def planDepth (dD : ℕ → ℝ) (α : ℝ) (n m : ℕ) (w : List Bool) : ℝ :=
  (w.length : ℝ) * (α * dD n)
    + (w.countP (fun b => b) : ℝ) * dD n
    + ((w.length - w.countP (fun b => b) : ℕ) : ℝ) * dD m

/-- A one-stage plan: block size `m` (`2 ≤ m < n`) and a word of Grover steps. -/
structure OneStagePlan where
  block : ℕ
  word : List Bool

/-- Admissibility `2 ≤ block < n`. -/
def validOneStageBlock (n : ℕ) (p : OneStagePlan) : Prop :=
  2 ≤ p.block ∧ p.block < n

/-- Success probability of a one-stage plan. -/
def oneStagePlanProb (n : ℕ) (p : OneStagePlan) : ℝ :=
  planProb n p.block p.word

/-- Depth of a one-stage plan. -/
def oneStagePlanDepth (dD : ℕ → ℝ) (α : ℝ) (n : ℕ) (p : OneStagePlan) : ℝ :=
  planDepth dD α n p.block p.word

/-- Depth-to-success ratio of a one-stage plan. -/
def oneStagePlanRatio (dD : ℕ → ℝ) (α : ℝ) (n : ℕ) (p : OneStagePlan) : ℝ :=
  oneStagePlanDepth dD α n p / oneStagePlanProb n p

/-- Eq. (17): the one-stage optimised MED — infimum of `d(S)/P(S)` over pure-global
(Grover) sequences and over mixed global/local sequences.  A sequence is non-empty
(the empty sequence has zero depth and is not a search), and zero-success sequences
are excluded as in `groverMED`. -/
def oneStageMED (dD : ℕ → ℝ) (α : ℝ) (n : ℕ) : ℝ :=
  sInf ({ r : ℝ | ∃ j : ℕ, groverProb n (j + 1) ≠ 0 ∧
      r = groverRatio dD α n (j + 1) } ∪
    { r : ℝ | ∃ p : OneStagePlan, validOneStageBlock n p ∧ p.word ≠ [] ∧
        oneStagePlanProb n p ≠ 0 ∧ r = oneStagePlanRatio dD α n p })

/-- Eq. (31): `α_{c,1} = max{α | d1(α) < dG(α)}`. -/
def alphaCriticalOneStage (dD : ℕ → ℝ) (n : ℕ) : ℝ :=
  sSup { α : ℝ | oneStageMED dD α n < groverMED dD α n }

/-- A two-stage plan. -/
structure TwoStagePlan where
  m2 : ℕ
  m0 : ℕ
  word1 : List Bool
  word2 : List Bool

/-- Admissibility of a two-stage plan. -/
def validTwoStageBlock (n : ℕ) (p : TwoStagePlan) : Prop :=
  2 ≤ p.m2 ∧ p.m2 < n ∧ 2 ≤ p.m0 ∧ p.m0 < p.m2

/-- Eq. (26) probability: product of the two independent stage probabilities. -/
def twoStagePlanProb (n : ℕ) (p : TwoStagePlan) : ℝ :=
  planProb n p.m2 p.word1 * planProb p.m2 p.m0 p.word2

/-- Eq. (26) depth: sum of the two stage depths. -/
def twoStagePlanDepth (dD : ℕ → ℝ) (α : ℝ) (n : ℕ) (p : TwoStagePlan) : ℝ :=
  planDepth dD α n p.m2 p.word1 + planDepth dD α p.m2 p.m0 p.word2

/-- Depth-to-success ratio of a two-stage plan. -/
def twoStagePlanRatio (dD : ℕ → ℝ) (α : ℝ) (n : ℕ) (p : TwoStagePlan) : ℝ :=
  twoStagePlanDepth dD α n p / twoStagePlanProb n p

/-- Eq. (26): the two-stage optimised MED.  Both stages are non-empty sequences and
zero-success plans are excluded (`0 / 0 = 0` in Lean's total division would otherwise
make the infimum trivial). -/
def twoStageMED (dD : ℕ → ℝ) (α : ℝ) (n : ℕ) : ℝ :=
  sInf { r : ℝ | ∃ p : TwoStagePlan, validTwoStageBlock n p ∧
      p.word1 ≠ [] ∧ p.word2 ≠ [] ∧ twoStagePlanProb n p ≠ 0 ∧
      r = twoStagePlanRatio dD α n p }

/-- Eq. (48): `α_{c,2} = max{α | d2(α) < dG(α)}`. -/
def alphaCriticalTwoStage (dD : ℕ → ℝ) (n : ℕ) : ℝ :=
  sSup { α : ℝ | twoStageMED dD α n < groverMED dD α n }

/-- Eq. (21): the depth-optimised one-stage MED never exceeds Grover's MED — the
optimised family contains the pure-global sequences `S_{n,m}(j,0) = Gn^j` whose
ratios are exactly Grover's.  Stated for `α ≥ 0` and a non-negative depth model,
which make every ratio non-negative. -/
theorem oneStageMED_le_groverMED
    (dD : ℕ → ℝ) (α : ℝ) (n : ℕ)
    (hα : 0 ≤ α) (hdD : ∀ k, 0 ≤ dD k) :
    oneStageMED dD α n ≤ groverMED dD α n := by
  unfold oneStageMED groverMED
  apply csInf_le_csInf
  · -- the union is bounded below by `0`
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with hr | hr
    · -- a pure-global (Grover) ratio
      obtain ⟨j, _hP, rfl⟩ := hr
      unfold groverRatio groverStepDepth
      apply div_nonneg
      · exact mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg (j + 1))) (hdD n)
      · exact groverProb_nonneg n (j + 1)
    · -- a mixed-plan ratio
      obtain ⟨p, _hv, _hne, _hP, rfl⟩ := hr
      unfold oneStagePlanRatio oneStagePlanDepth oneStagePlanProb planProb planDepth
      apply div_nonneg
      · have h1 : 0 ≤ (p.word.length : ℝ) * (α * dD n) :=
          mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hα (hdD n))
        have h2 : 0 ≤ (p.word.countP (fun b => b) : ℝ) * dD n :=
          mul_nonneg (Nat.cast_nonneg _) (hdD n)
        have h3 : 0 ≤ ((p.word.length - p.word.countP (fun b => b) : ℕ) : ℝ) * dD p.block :=
          mul_nonneg (Nat.cast_nonneg _) (hdD p.block)
        linarith
      · exact sq_nonneg _
  · -- the one-step Grover ratio makes the Grover set nonempty
    exact ⟨groverRatio dD α n (0 + 1), 0, by simpa using groverProb_one_ne_zero n, rfl⟩
  · exact Set.subset_union_left

/-- The algebra of Eq. (46) → (47).  With a linear diffusion depth `d(Dn) = c·n`
and a probability gap `δ = c'·2^{-n/2}`, the sandwich-sequence threshold
`2(d(Dn)-d(Dn-1))·P / (3·d(Dn)·δ)` equals `(2/(3c'))·P·2^{n/2}/n`.  This is the
exact algebraic reduction that, combined with `P ≤ 1`, gives `O(n^{-1}2^{n/2})`. -/
theorem sandwich_threshold_eq
    (c c' : ℝ) (hc : 0 < c) (hc' : 0 < c') (P : ℕ → ℝ) :
    ∀ n : ℕ, 1 ≤ n →
      2 * (c * (n : ℝ) - c * ((n - 1 : ℕ) : ℝ)) * P n
          / (3 * (c * (n : ℝ)) * (c' * (Real.sqrt (dbSize n))⁻¹))
        = (2 / (3 * c')) * P n * (Real.sqrt (dbSize n) / (n : ℝ)) := by
  intro n hn
  have hnne : n ≠ 0 := by omega
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h := Nat.cast_pred (R := ℝ) (show 0 < n by omega)
    simpa using h
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnne
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hc'0 : c' ≠ 0 := ne_of_gt hc'
  have hs : Real.sqrt (dbSize n) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    unfold dbSize
    positivity
  rw [hn1]
  field_simp
  ring

/-- The limiting algebra of Eq. (55) → (57).  If `d(Dn) → ∞` and the `O(2^{-n/2})`
success-probability correction `e n → 0`, then the two-stage threshold
`1 + √3 - 3/d(Dn) + e n` tends to `1 + √3`. -/
theorem twoStage_threshold_tendsto
    (dD : ℕ → ℝ) (e : ℕ → ℝ)
    (hdD : Tendsto dD atTop atTop)
    (he : Tendsto e atTop (nhds 0)) :
    Tendsto (fun n : ℕ => 1 + Real.sqrt 3 + ((-3) / dD n + e n))
      atTop (nhds (1 + Real.sqrt 3)) := by
  have hinv : Tendsto (fun n : ℕ => (dD n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hdD
  have h3 : Tendsto (fun n : ℕ => (-3) * (dD n)⁻¹) atTop (nhds 0) := by
    have h := hinv.const_mul (-3 : ℝ)
    simpa using h
  have hcorr : Tendsto (fun n : ℕ => (-3) / dD n + e n) atTop (nhds 0) := by
    have hdiv : Tendsto (fun n : ℕ => (-3) / dD n) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using h3
    simpa using hdiv.add he
  simpa using tendsto_const_nhds.add hcorr

/-- The local angle at `m = 4`: `sin (2 θ2) = √15 / 8`. -/
lemma theta2_four_sin : Real.sin (2 * theta2 4) = Real.sqrt 15 / 8 := by
  unfold theta2 sinTheta2
  norm_num
  rw [Real.sin_two_mul]
  have h1 : Real.sin (Real.arcsin (1 / 4 : ℝ)) = 1 / 4 := by
    rw [Real.sin_arcsin] <;> norm_num
  have h2 : Real.cos (Real.arcsin (1 / 4 : ℝ)) = Real.sqrt 15 / 4 := by
    rw [Real.cos_arcsin] <;> norm_num
  rw [h1, h2]
  ring

/-- The local angle at `m = 4`: `cos (2 θ2) = 7 / 8`. -/
lemma theta2_four_cos : Real.cos (2 * theta2 4) = 7 / 8 := by
  unfold theta2 sinTheta2
  norm_num
  rw [Real.cos_two_mul]
  have h2 : Real.cos (Real.arcsin (1 / 4 : ℝ)) = Real.sqrt 15 / 4 := by
    rw [Real.cos_arcsin] <;> norm_num
  rw [h2, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 15)]
  norm_num

/-- The initial state `|s6>` in the basis of Eq. (9) at `m = 4`. -/
lemma v0_six_four : v0 6 4 = ![1/8, Real.sqrt 15 / 8, Real.sqrt 3 / 2] := by
  ext i
  fin_cases i <;> simp [v0] <;> norm_num [Real.sqrt_div_self] <;> ring

/-- Action of the local operator of Eq. (32) on a general vector. -/
lemma local_mulVec (m : ℕ) (w : Fin 3 → ℝ) :
    (localStepMatrix m).mulVec w =
      ![Real.cos (2 * theta2 m) * w 0 + Real.sin (2 * theta2 m) * w 1,
        -Real.sin (2 * theta2 m) * w 0 + Real.cos (2 * theta2 m) * w 1,
        w 2] := by
  funext i
  fin_cases i <;>
    simp [localStepMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- Action of the local operator at `m = 4` with the exact entries `7/8` and `√15/8`. -/
lemma local_six_four_mulVec (w : Fin 3 → ℝ) :
    (localStepMatrix 4).mulVec w =
      ![7/8 * w 0 + Real.sqrt 15 / 8 * w 1,
        -(Real.sqrt 15 / 8) * w 0 + 7/8 * w 1,
        w 2] := by
  rw [local_mulVec, theta2_four_sin, theta2_four_cos]

/-- The global Grover operator `G6` in the basis of Eq. (9) at `m = 4`, with
exact entries in `ℚ(√3, √15)`. -/
lemma global_six_four :
    globalStepMatrix 6 4 =
      !![31/32, Real.sqrt 15 / 32, Real.sqrt 3 / 8;
         -(Real.sqrt 15 / 32), -17/32, Real.sqrt 15 * Real.sqrt 3 / 8;
         -(Real.sqrt 3 / 8), Real.sqrt 15 * Real.sqrt 3 / 8, 1/2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [globalStepMatrix, outerVec, v0_six_four, Matrix.mul_apply, Matrix.diagonal,
      Fin.sum_univ_three] <;>
    ring_nf <;>
    norm_num [Real.sq_sqrt (show (0:ℝ) ≤ 15 by norm_num),
      Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]

/-- Action of the global operator at `n = 6, m = 4` on a general vector. -/
lemma global_six_four_mulVec (w : Fin 3 → ℝ) :
    (globalStepMatrix 6 4).mulVec w =
      ![31/32 * w 0 + Real.sqrt 15 / 32 * w 1 + Real.sqrt 3 / 8 * w 2,
        -(Real.sqrt 15 / 32) * w 0 + (-17/32) * w 1 + Real.sqrt 15 * Real.sqrt 3 / 8 * w 2,
        -(Real.sqrt 3 / 8) * w 0 + Real.sqrt 15 * Real.sqrt 3 / 8 * w 1 + 1/2 * w 2] := by
  rw [global_six_four]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- First local step of `S_{6,4}(1,1,2) = G4 G6 G4²`. -/
lemma v1_eq :
    (localStepMatrix 4).mulVec (v0 6 4) = ![11/32, 3 * Real.sqrt 15 / 32, Real.sqrt 3 / 2] := by
  rw [local_six_four_mulVec, v0_six_four]
  ext i
  fin_cases i <;> simp <;> ring_nf <;>
    norm_num [Real.sq_sqrt (show (0:ℝ) ≤ 15 by norm_num)]

/-- Second local step of `S_{6,4}(1,1,2)`. -/
lemma v2_eq :
    (localStepMatrix 4).mulVec ![11/32, 3 * Real.sqrt 15 / 32, Real.sqrt 3 / 2] =
      ![61/128, 5 * Real.sqrt 15 / 128, Real.sqrt 3 / 2] := by
  rw [local_six_four_mulVec]
  ext i
  fin_cases i <;> simp <;> ring_nf <;>
    norm_num [Real.sq_sqrt (show (0:ℝ) ≤ 15 by norm_num)]

/-- The global step of `S_{6,4}(1,1,2)`. -/
lemma v3_eq :
    (globalStepMatrix 6 4).mulVec ![61/128, 5 * Real.sqrt 15 / 128, Real.sqrt 3 / 2] =
      ![1367/2048, 311 * Real.sqrt 15 / 2048, 135 * Real.sqrt 3 / 512] := by
  rw [global_six_four_mulVec]
  ext i
  fin_cases i <;> simp <;> ring_nf <;>
    norm_num [Real.sq_sqrt (show (0:ℝ) ≤ 15 by norm_num),
      Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)] <;> ring

/-- The final local step of `S_{6,4}(1,1,2)`: the target amplitude is `7117/8192`. -/
lemma v4_eq :
    (localStepMatrix 4).mulVec ![1367/2048, 311 * Real.sqrt 15 / 2048, 135 * Real.sqrt 3 / 512] =
      ![7117/8192, 405 * Real.sqrt 15 / 8192, 135 * Real.sqrt 3 / 512] := by
  rw [local_six_four_mulVec]
  ext i
  fin_cases i <;> simp <;> ring_nf <;>
    norm_num [Real.sq_sqrt (show (0:ℝ) ≤ 15 by norm_num),
      Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)] <;> ring

/-- Eq. (20) exactly: the success probability of `S_{6,4}(1,1,2) = G4 G6 G4²` is
`(7117/8192)² = 50651689/67108864 ≈ 0.75477`, matching the paper's `0.755`.
The word `[false,false,true,false]` is the application order local, local,
global, local. -/
lemma planProb_witness :
    planProb 6 4 [false, false, true, false] = 50651689 / 67108864 := by
  unfold planProb
  simp only [planMatrix, stepMatrix, Matrix.one_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [v1_eq, v2_eq, v3_eq, v4_eq]
  norm_num

/-- `θ = arcsin (1/8) ≤ 2/15` at `n = 6`. -/
lemma groverTheta_six_le : groverTheta 6 ≤ 2/15 := by
  unfold groverTheta dbSize
  norm_num
  exact (Real.arcsin_le_iff_le_sin (x := 1/8) (y := 2/15) (by norm_num) (by
    constructor
    · linarith [Real.pi_gt_three]
    · linarith [Real.pi_gt_three])).mpr (by
      have h := Real.sin_gt_sub_cube (show (0:ℝ) < 2/15 by norm_num)
      norm_num at h ⊢
      linarith)

/-- For `j ≤ 3`, `P_6(j) = sin²((2j+1)θ) ≤ ((2j+1)·2/15)²`. -/
lemma groverProb_six_le_sq {j : ℕ} (hj : j ≤ 3) :
    groverProb 6 j ≤ ((2 * (j:ℝ) + 1) * (2/15))^2 := by
  unfold groverProb
  have ht_nonneg : 0 ≤ (2 * (j:ℝ) + 1) * groverTheta 6 :=
    mul_nonneg (by positivity) (groverTheta_nonneg 6)
  have ht_le : (2 * (j:ℝ) + 1) * groverTheta 6 ≤ (2 * (j:ℝ) + 1) * (2/15) := by
    have h := groverTheta_six_le
    have hj0 : (0:ℝ) ≤ 2 * (j:ℝ) + 1 := by positivity
    nlinarith
  have ht_le_pi : (2 * (j:ℝ) + 1) * groverTheta 6 ≤ Real.pi := by
    have hj3 : (j:ℝ) ≤ 3 := by exact_mod_cast hj
    have h1 : (2 * (j:ℝ) + 1) ≤ 7 := by linarith
    have h2 : (2 * (j:ℝ) + 1) * (2/15) ≤ 14/15 := by nlinarith
    linarith [Real.pi_gt_three]
  have hsin_nonneg : 0 ≤ Real.sin ((2 * (j:ℝ) + 1) * groverTheta 6) :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht_nonneg ht_le_pi
  have hsin_le : Real.sin ((2 * (j:ℝ) + 1) * groverTheta 6) ≤ (2 * (j:ℝ) + 1) * (2/15) :=
    le_trans (Real.sin_le ht_nonneg) ht_le
  have hsq := mul_self_le_mul_self hsin_nonneg hsin_le
  simpa [sq] using hsq

/-- Every non-vanishing Grover ratio at `n = 6`, `α = 1/2`, `d(Dn) = 2^n` is at
least `330`.  For `j ≤ 3` this uses `P_6(j) ≤ ((2j+1)·2/15)²`; for `j ≥ 4` the
numerator `96j ≥ 384` alone suffices because `P_6(j) ≤ 1`. -/
lemma groverRatio_six_ge (k : ℕ) (hk : 1 ≤ k) (hP : groverProb 6 k ≠ 0) :
    330 ≤ groverRatio (fun i => (2:ℝ)^i) (1/2) 6 k := by
  unfold groverRatio groverStepDepth
  have hdD : (fun i : ℕ => (2:ℝ)^i) 6 = 64 := by norm_num
  have hnum : (1/2 + 1) * (k : ℝ) * (fun i : ℕ => (2:ℝ)^i) 6 = 96 * (k : ℝ) := by
    rw [hdD]; ring
  rw [hnum]
  have hPpos : 0 < groverProb 6 k := lt_of_le_of_ne (groverProb_nonneg 6 k) (Ne.symm hP)
  have hPle : groverProb 6 k ≤ 1 := groverProb_le_one 6 k
  by_cases hk3 : k ≤ 3
  · have hbound := groverProb_six_le_sq hk3
    have hdiv_le : 96 * (k:ℝ) / ((2 * (k:ℝ) + 1) * (2/15))^2 ≤
        96 * (k:ℝ) / groverProb 6 k :=
      div_le_div_of_nonneg_left (by positivity) hPpos hbound
    interval_cases k <;> norm_num at hdiv_le ⊢ <;> linarith
  · push Not at hk3
    have hk4 : (4:ℝ) ≤ k := by exact_mod_cast hk3
    have hratio_ge : 96 * (k:ℝ) ≤ 96 * (k:ℝ) / groverProb 6 k := by
      rw [le_div_iff₀ hPpos]
      nlinarith
    nlinarith

/-- The depth-to-success ratio of the witness plan is `240 / (50651689/67108864)`. -/
lemma planRatio_witness :
    oneStagePlanRatio (fun i => (2:ℝ)^i) (1/2) 6 ⟨4, [false, false, true, false]⟩ =
      16106127360 / 50651689 := by
  unfold oneStagePlanRatio oneStagePlanDepth oneStagePlanProb
  rw [show planProb 6 4 [false,false,true,false] = 50651689/67108864 from planProb_witness]
  unfold planDepth
  norm_num

/-- The witness plan has ratio strictly below `330`. -/
lemma planRatio_lt_330 :
    oneStagePlanRatio (fun i => (2:ℝ)^i) (1/2) 6 ⟨4, [false, false, true, false]⟩ < 330 := by
  rw [planRatio_witness]
  norm_num

/-- **Main result** (abstract, p. 1; Sec. IV after Eq. (47)): *Grover's algorithm
is not optimal in depth*.  Instantiated with the paper's numerical depth model
`d(Dn) = 2^n` (so `d(D6) = 64`, `d(D4) = 16`, p. 4), database size `n = 6` and
oracle-to-diffusion ratio `α = 1/2`: the depth-optimised one-stage MED `d1(α)`
(Eq. (17)) is strictly below Grover's MED `dG(α)` (Eq. (12)).

The witness is the paper's sequence `S_{6,4}(1,1,2) = G4 G6 G4²` (Eq. (19)),
encoded in application order as `[false,false,true,false]`.  Its success
probability is exactly `(7117/8192)² = 50651689/67108864 ≈ 0.75477` (Eq. (20)),
and its depth-to-success ratio is `≈ 317.98`, while every Grover ratio at
`α = 1/2` is at least `330` (the minimum, at `j = 4`, is `≈ 470.6`).  This is the
strict form of Eq. (21) `d1(α) ≤ dG(α)` (`oneStageMED_le_groverMED`) and matches
the paper's numerical statement that the sequence wins for `α < 2.029`.

The statement is the concrete numerical instance; the general Theorem 1 route
(`α_{c,1} = O(n^{-1}2^{n/2}) > 0`) remains the documented gap of the Theorem 1
statement above. -/
theorem grover_not_optimal_in_depth :
    ∃ (n : ℕ) (α : ℝ), 3 ≤ n ∧ 0 < α ∧
      oneStageMED (fun k => (2 : ℝ) ^ k) α n <
        groverMED (fun k => (2 : ℝ) ^ k) α n := by
  refine ⟨6, 1/2, by norm_num, by norm_num, ?_⟩
  have hle : oneStageMED (fun i => (2:ℝ)^i) (1/2) 6 ≤
      oneStagePlanRatio (fun i => (2:ℝ)^i) (1/2) 6 ⟨4, [false, false, true, false]⟩ := by
    unfold oneStageMED
    apply csInf_le
    · refine ⟨0, ?_⟩
      intro r hr
      rcases hr with hr | hr
      · obtain ⟨j, _hP, rfl⟩ := hr
        unfold groverRatio groverStepDepth
        apply div_nonneg
        · positivity
        · exact groverProb_nonneg 6 (j+1)
      · obtain ⟨p, _hv, _hne, _hP, rfl⟩ := hr
        unfold oneStagePlanRatio oneStagePlanDepth oneStagePlanProb planDepth planProb
        apply div_nonneg
        · positivity
        · exact sq_nonneg _
    · right
      refine ⟨⟨4, [false, false, true, false]⟩, ?_, ?_, ?_, rfl⟩
      · unfold validOneStageBlock
        norm_num
      · simp
      · unfold oneStagePlanProb
        rw [show planProb 6 4 [false,false,true,false] = 50651689/67108864 from planProb_witness]
        norm_num
  have hlt : oneStagePlanRatio (fun i => (2:ℝ)^i) (1/2) 6 ⟨4, [false, false, true, false]⟩ <
      groverMED (fun i => (2:ℝ)^i) (1/2) 6 := by
    have h330 : (330:ℝ) ≤ groverMED (fun i => (2:ℝ)^i) (1/2) 6 := by
      unfold groverMED
      apply le_csInf
      · exact ⟨_, 0, by simpa using groverProb_one_ne_zero 6, rfl⟩
      · intro r hr
        obtain ⟨j, hP, rfl⟩ := hr
        exact groverRatio_six_ge (j+1) (by omega) hP
    linarith [planRatio_lt_330]
  linarith

end Qatlib.Papers.DepthGrover19.MainResults
