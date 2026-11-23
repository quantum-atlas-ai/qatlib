/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.WalkSearch06.ReverseWalk.ConditionalStates
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section

/-!
# WalkSearch06 — the discriminant of the directed cycle at matrix level

Source: [MagniezNayakRolandSantha2011], Definition 1 and Theorem 4, p. 7 of
[arXiv:quant-ph/0608026v4](https://arxiv.org/abs/quant-ph/0608026v4).

Definition 1 builds the quantum walk `W(P) = ref(B) * ref(A)` of a finite Markov chain
from the forward and time-reversed conditional distributions, and Theorem 4 transports
the spectrum of the discriminant matrix `D(P)` to the two-reflection walk on the
Szegedy subspaces.

For the directed cycle `i ↦ i + 1` on `Fin n` with uniform stationary weights,
time reversal is the transpose cycle and the discriminant is the transition matrix.
The cycle shift is a Euclidean isometry, giving operator norm `1` at every nonempty
size. The all-ones vector lies in the direction of the entrywise square root of the
uniform distribution and is fixed by the discriminant. Each nonzero discriminant
entry pairs two equal conditional states. The forward and reversed families therefore
span the same subspace, making their product of reflections the identity.

## Main statements

* `directedCyclePi_stationary`: the uniform weight vector is stationary for the
  directed cycle.
* `directedCycle_timeReversal`: with uniform weights the time reversal of the directed
  cycle is its transpose.
* `directedCycle_discriminant_eq`: the discriminant of the directed cycle equals the
  transition matrix itself.
* `directedCycle_norm`: the Euclidean operator norm of the directed cycle transition
  matrix is exactly `1` for every nonempty size.
* `directedCycle_discriminant_norm`: the Euclidean operator norm of the discriminant is
  exactly `1` for every non-degenerate size.
* `directedCycle_discriminant_norm_le_uniform`: a single positive constant, fixed
  before the dimension, bounds every non-degenerate cycle discriminant in the Euclidean
  operator norm.
* `directedCycle_discriminant_mulVec_const_one`: the all-ones vector is fixed by the
  discriminant.
* `directedCycle_lifts_eq_of_discriminant_entry_one`: an entry equal to one identifies
  the matching forward and reversed conditional states.
* `directedCycle_reflection_product_apply`: the walk on the two conditional spans
  fixes every vector of the Euclidean walk space.

## References

* [Magniez, Nayak, Roland, Santha, 2006][MagniezNayakRolandSantha2011]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WalkSearch06.ReverseWalk.CycleDiscriminant

open Matrix
open Qatlib.Papers.WalkSearch06.ReverseWalk.ConditionalStates (liftA liftB)
open Qatlib.Papers.WalkSearch06.ReverseWalk.TimeReversal
open scoped BigOperators Matrix.Norms.L2Operator

/-- The transition matrix of the directed cycle `i ↦ i + 1` on `Fin n`, written with
the cyclic permutation `finRotate n` so that every size, including the degenerate
`n = 0`, is covered. -/
def directedCycle (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if j = finRotate n i then 1 else 0

/-- The uniform weight vector on `Fin n`, assigning `n⁻¹` to every state. -/
def directedCyclePi (n : ℕ) : Fin n → ℝ := fun _ => (n : ℝ)⁻¹

/-- Every entry of the directed cycle transition matrix is nonnegative. -/
theorem directedCycle_nonneg (n : ℕ) (x y : Fin n) : 0 ≤ directedCycle n x y := by
  simp only [directedCycle]
  split_ifs with h
  · exact zero_le_one
  · exact le_rfl

/-- Every row of the directed cycle sums to one. -/
theorem directedCycle_row_sum (n : ℕ) (x : Fin n) : ∑ y, directedCycle n x y = 1 := by
  refine (Finset.sum_eq_single (finRotate n x) ?_ ?_).trans ?_
  · intro y _ hy
    simp only [directedCycle, hy, ite_false]
  · intro hmem
    exact absurd (Finset.mem_univ (finRotate n x)) hmem
  · simp only [directedCycle, ite_true]

/-- The directed cycle is row-stochastic for every size. -/
theorem directedCycle_rowStochastic (n : ℕ) :
    directedCycle n ∈ Matrix.rowStochastic ℝ (Fin n) :=
  Matrix.mem_rowStochastic_iff_sum.mpr ⟨directedCycle_nonneg n, directedCycle_row_sum n⟩

/-- Every column of the directed cycle sums to one. -/
theorem directedCycle_col_sum (n : ℕ) (y : Fin n) :
    ∑ x, directedCycle n x y = 1 := by
  refine (Finset.sum_eq_single ((finRotate n).symm y) ?_ ?_).trans ?_
  · intro x _ hx
    have hxy : ¬(y = finRotate n x) := by
      intro hxy
      apply hx
      apply (finRotate n).injective
      rw [Equiv.apply_symm_apply]
      exact hxy.symm
    simp only [directedCycle, hxy, ite_false]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem
  · simp only [directedCycle]
    split_ifs with h
    · rfl
    · exact absurd (Equiv.apply_symm_apply (finRotate n) y).symm h

/-- The uniform weight is strictly positive on every state of a nonempty cycle. -/
theorem directedCyclePi_pos {n : ℕ} (hn : 0 < n) (x : Fin n) :
    0 < directedCyclePi n x := by
  rw [directedCyclePi, inv_pos]
  exact_mod_cast hn

/-- The uniform weight is nonzero on every state of a nonempty cycle. -/
theorem directedCyclePi_ne_zero {n : ℕ} (hn : 0 < n) (x : Fin n) :
    directedCyclePi n x ≠ 0 :=
  (directedCyclePi_pos hn x).ne'

/-- The uniform weight vector is stationary for the directed cycle. -/
theorem directedCyclePi_stationary (n : ℕ) (y : Fin n) :
    ∑ x, directedCyclePi n x * directedCycle n x y = directedCyclePi n y :=
  calc
    ∑ x, directedCyclePi n x * directedCycle n x y
        = directedCyclePi n y * ∑ x, directedCycle n x y := by
          simp only [directedCyclePi]
          exact (Finset.mul_sum _ _ _).symm
    _ = directedCyclePi n y := by rw [directedCycle_col_sum n y, mul_one]

/-- The uniform stationary weights have total mass one on a nonempty cycle. -/
theorem directedCyclePi_sum (n : ℕ) (hn : 0 < n) : ∑ x, directedCyclePi n x = 1 := by
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [directedCyclePi, hne]

/-- With uniform weights, the time-reversed transition probability from `x` to `y`
equals the forward probability from `y` to `x`. -/
theorem directedCycle_timeReversal_apply (n : ℕ) (hn : 0 < n) (x y : Fin n) :
    timeReversal (directedCycle n) (directedCyclePi n) x y = directedCycle n y x := by
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [timeReversal_apply]
  simp only [directedCyclePi, mul_div_cancel_left₀ _ (inv_ne_zero hne)]

/-- With uniform weights the time reversal of the directed cycle is its transpose. -/
theorem directedCycle_timeReversal (n : ℕ) (hn : 0 < n) :
    timeReversal (directedCycle n) (directedCyclePi n) = (directedCycle n)ᵀ := by
  funext x y
  rw [directedCycle_timeReversal_apply n hn x y, Matrix.transpose_apply]

/-- The discriminant of the directed cycle with uniform weights equals the transition
matrix itself. -/
theorem directedCycle_discriminant_eq (n : ℕ) (hn : 0 < n) :
    discriminant (directedCycle n) (directedCyclePi n) = directedCycle n := by
  funext x y
  simp only [discriminant, directedCycle_timeReversal_apply n hn y x, ← pow_two,
    Real.sqrt_sq (directedCycle_nonneg n x y)]

/-- The directed cycle acts on `EuclideanSpace ℝ (Fin n)` by the coordinate shift
`x ↦ x ∘ finRotate n`. -/
private noncomputable def directedCycleCLM (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (directedCycle n)

private theorem directedCycleCLM_apply (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    directedCycleCLM n x i = x (finRotate n i) := by
  rw [directedCycleCLM, Matrix.ofLp_toEuclideanCLM]
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [directedCycle]
  refine (Finset.sum_eq_single (finRotate n i) ?_ ?_).trans ?_
  · intro j _ hj
    simp only [hj, ite_false, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem
  · simp only [ite_true, one_mul]

/-- The coordinate shift of the directed cycle preserves the Euclidean norm. -/
private theorem directedCycleCLM_norm (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : ‖directedCycleCLM n x‖ = ‖x‖ := by
  have hsq : ‖directedCycleCLM n x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simpa only [directedCycleCLM_apply] using
      (Equiv.sum_comp (finRotate n) fun i => x i ^ 2)
  calc
    ‖directedCycleCLM n x‖ = Real.sqrt (‖directedCycleCLM n x‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖x‖ ^ 2) := by rw [hsq]
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

/-- The Euclidean operator norm of the directed cycle transition matrix is exactly one
for every nonempty size: the cycle shift is a Euclidean isometry. -/
theorem directedCycle_norm (n : ℕ) [NeZero n] : ‖directedCycle n‖ = 1 := by
  have hbridge : ‖directedCycle n‖ = ‖directedCycleCLM n‖ := by
    simpa only [directedCycleCLM] using
      (Matrix.l2_opNorm_toEuclideanCLM (directedCycle n)).symm
  rw [hbridge]
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul, directedCycleCLM_norm n x]
  · have hr := (directedCycleCLM n).ratio_le_opNorm (EuclideanSpace.single (0 : Fin n) 1)
    have hsingle : ‖(EuclideanSpace.single (0 : Fin n) (1 : ℝ) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      simp
    rw [directedCycleCLM_norm, hsingle, div_one] at hr
    exact hr

/-- The Euclidean operator norm of the discriminant of the directed cycle is exactly
one for every non-degenerate size. -/
theorem directedCycle_discriminant_norm (n : ℕ) (hn : 0 < n) :
    ‖discriminant (directedCycle n) (directedCyclePi n)‖ = 1 := by
  have : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
  rw [directedCycle_discriminant_eq n hn, directedCycle_norm n]

/-- There is a single positive constant, fixed before the dimension, that bounds the
Euclidean operator norm of the discriminant of every non-degenerate directed cycle.
The constant is `1`; the sharper exact theorem above gives norm `1`. -/
theorem directedCycle_discriminant_norm_le_uniform :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 2 ≤ n →
      ‖discriminant (directedCycle n) (directedCyclePi n)‖ ≤ C := by
  refine ⟨1, one_pos, fun n hn => ?_⟩
  rw [directedCycle_discriminant_norm n (by omega : 0 < n)]

/-- The constant all-ones vector on `Fin n` is fixed by the discriminant of the
directed cycle. Multiplying it by `√(n⁻¹)` gives the entrywise square root of the
uniform stationary distribution. -/
theorem directedCycle_discriminant_mulVec_const_one (n : ℕ) (hn : 0 < n) :
    discriminant (directedCycle n) (directedCyclePi n) *ᵥ (fun _ => (1 : ℝ)) =
      fun _ => 1 := by
  rw [directedCycle_discriminant_eq n hn]
  funext i
  rw [Matrix.mulVec]
  calc
    ∑ j, directedCycle n i j * (1 : ℝ) = ∑ y, directedCycle n i y := by simp
    _ = 1 := directedCycle_row_sum n i

/-- A unit entry of the directed-cycle discriminant identifies equal forward and
reversed conditional states supported on the corresponding directed edge. -/
theorem directedCycle_lifts_eq_of_discriminant_entry_one (n : ℕ) (hn : 0 < n)
    (x y : Fin n) (h : discriminant (directedCycle n) (directedCyclePi n) x y = 1) :
    liftA (directedCycle n) x = liftB (directedCycle n) (directedCyclePi n) y := by
  rw [directedCycle_discriminant_eq n hn] at h
  have hy : y = finRotate n x := by
    by_contra hne
    simp only [directedCycle, ite_eq_right hne, zero_ne_one] at h
  subst y
  funext p
  obtain ⟨i, j⟩ := p
  rw [liftA, liftB, directedCycle_timeReversal_apply n hn]
  change (if i = x then (Real.sqrt (directedCycle n x j) : ℂ) else 0) =
    (if j = finRotate n x then (Real.sqrt (directedCycle n i (finRotate n x)) : ℂ) else 0)
  by_cases hi : i = x
  · subst i
    by_cases hj : j = finRotate n x
    · subst j
      simp only [directedCycle]
    · simp only [directedCycle, ite_eq_right hj, Real.sqrt_zero, Complex.ofReal_zero, ite_self]
  · have hne : finRotate n x ≠ finRotate n i :=
      fun he => hi ((finRotate n).injective he.symm)
    simp only [directedCycle, ite_eq_right hi, ite_eq_right hne, Real.sqrt_zero, Complex.ofReal_zero, ite_self]

/-- The span of the forward conditional states in the Euclidean walk space. -/
def directedCycleForwardSpan (n : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin n × Fin n)) :=
  Submodule.span ℂ (Set.range fun x => WithLp.toLp 2 (liftA (directedCycle n) x))

/-- The span of the time-reversed conditional states in the Euclidean walk space. -/
def directedCycleReverseSpan (n : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin n × Fin n)) :=
  Submodule.span ℂ
    (Set.range fun y => WithLp.toLp 2 (liftB (directedCycle n) (directedCyclePi n) y))

/-- The directed-cycle forward and reversed spans agree because the nonzero entries of
the discriminant pair their generators by a cyclic permutation. -/
theorem directedCycle_forwardSpan_eq_reverseSpan (n : ℕ) (hn : 0 < n) :
    directedCycleForwardSpan n = directedCycleReverseSpan n := by
  have hpair (x : Fin n) :
      liftA (directedCycle n) x = liftB (directedCycle n) (directedCyclePi n) (finRotate n x) :=
    directedCycle_lifts_eq_of_discriminant_entry_one n hn x (finRotate n x) (by
      rw [directedCycle_discriminant_eq n hn]
      simp [directedCycle])
  unfold directedCycleForwardSpan directedCycleReverseSpan
  congr 1
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨finRotate n x, congrArg (WithLp.toLp 2) (hpair x).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := (finRotate n).surjective y
    exact ⟨x, congrArg (WithLp.toLp 2) (hpair x)⟩

/-- For a nonempty directed cycle, the reflections of Definition 1 through the forward
and reversed conditional spans compose to the identity on the entire walk space. -/
theorem directedCycle_reflection_product_apply (n : ℕ) (hn : 0 < n)
    (v : EuclideanSpace ℂ (Fin n × Fin n)) :
    (directedCycleReverseSpan n).reflection ((directedCycleForwardSpan n).reflection v) = v := by
  rw [directedCycle_forwardSpan_eq_reverseSpan n hn]
  exact Submodule.reflection_reflection _ v

end Qatlib.Papers.WalkSearch06.ReverseWalk.CycleDiscriminant
