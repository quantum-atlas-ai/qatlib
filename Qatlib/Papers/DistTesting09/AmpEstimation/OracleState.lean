/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The quantum oracle state of a finite distribution

Section 2 of [BravyiHarrowHassidim2011] fixes an oracle `O : [S] → [N]` generating the
distribution `p`, with `p i = #(O ⁻¹ i) / S`, and defines the reversible quantum oracle on
`C^S ⊗ C^(N+1)` by `|s⟩|0⟩ ↦ |s⟩|O s⟩`.  This module constructs that state, proves that it is a
unit vector of the *complex Euclidean space* `EuclideanSpace ℂ (Fin S × Fin (N+1))`, and proves
that the squared Euclidean norm of its projection onto a subset `A` of outcomes is exactly the
mass `p_A = ∑ i ∈ A, p i`.  The projection is a diagonal `0/1` matrix, and its
`Matrix.Norms.L2Operator` norm is proved to be at most one, and exactly one whenever both the
input register and `A` are nonempty. The Euclidean norm of the projected state is the
amplitude `sqrt p_A` that underlies the probability-estimation algorithm in Theorem 5.

The domain and the outcome set are both non-degenerate: `S` is positive and the statements
about the mass use the distribution `oracleDist`, whose masses sum to one only because `S > 0`.

## Main statements

* `norm_oracleState`: the oracle state has Euclidean norm one.
* `norm_sq_goodSubstate_eq_oracleMass`: the projected squared norm is the `p_A` mass.
* `norm_goodProjector_le_one` and `norm_goodProjector_eq_one`: the diagonal projection has
  `L2Operator` norm at most one, and exactly one on a nonempty outcome set.

## References

* [Bravyi et al., 2011][BravyiHarrowHassidim2011], Section 2
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped Matrix.Norms.L2Operator BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.DistTesting09.AmpEstimation

variable {N S : ℕ}

/-- The output register `{0} ∪ [N]` of the reversible oracle, with `[N]` embedded as the
nonzero values. -/
def regIncl (i : Fin N) : Fin (N + 1) := i.succ

/-- The embedding shifts the zero-based label by one, reserving zero for the blank register. -/
@[simp] theorem regIncl_val (i : Fin N) : (regIncl i).1 = i.1 + 1 := rfl

/-- Distinct outcomes are distinct elements of the oracle output register. -/
theorem regIncl_injective : Function.Injective (regIncl (N := N)) := by
  exact Fin.succ_injective _

/-- The quantum oracle state `S^(-1/2) ∑ s, |s⟩ |O s⟩` of Section 2, as a vector in the complex
Euclidean space indexed by the pair of registers. -/
def oracleState (O : Fin S → Fin N) : EuclideanSpace ℂ (Fin S × Fin (N + 1)) :=
  WithLp.toLp 2 fun p =>
    if p.2 = regIncl (O p.1) then ((Real.sqrt (S : ℝ) : ℂ))⁻¹ else 0

/-- The amplitude of the oracle state at a pair of register values. -/
@[simp] theorem oracleState_apply (O : Fin S → Fin N) (p : Fin S × Fin (N + 1)) :
    oracleState O p =
      if p.2 = regIncl (O p.1) then ((Real.sqrt (S : ℝ) : ℂ))⁻¹ else 0 := rfl

/-- The squared Euclidean norm of the oracle state is `S` times the squared amplitude. -/
theorem norm_sq_oracleState (O : Fin S → Fin N) :
    ‖oracleState O‖ ^ 2 = (S : ℝ) * ‖((Real.sqrt (S : ℝ) : ℂ))⁻¹‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  have hinner : ∀ s : Fin S,
      (∑ i : Fin (N + 1), ‖oracleState O (s, i)‖ ^ 2)
        = ‖((Real.sqrt (S : ℝ) : ℂ))⁻¹‖ ^ 2 := by
    intro s
    rw [Finset.sum_eq_single (regIncl (O s))]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun s _ => hinner s, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- The oracle state is a unit vector of the complex Euclidean space when the domain is
nonempty. -/
theorem norm_oracleState (O : Fin S → Fin N) (hS : 0 < S) : ‖oracleState O‖ = 1 := by
  have hSpos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hc : ‖((Real.sqrt (S : ℝ) : ℂ))⁻¹‖ = (Real.sqrt (S : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg (S : ℝ))]
  have hsq : ‖oracleState O‖ ^ 2 = 1 := by
    rw [norm_sq_oracleState, hc, inv_pow, Real.sq_sqrt hSpos.le, mul_inv_cancel₀ hSpos.ne']
  rw [← Real.sqrt_sq (norm_nonneg _), hsq, Real.sqrt_one]

/-- The number of oracle inputs whose value lies in the outcome set `A`. -/
def fiberCount (O : Fin S → Fin N) (A : Finset (Fin N)) : ℕ :=
  (Finset.univ.filter fun s => O s ∈ A).card

/-- The component of the oracle state whose output register holds a value in `A`. -/
def goodSubstate (O : Fin S → Fin N) (A : Finset (Fin N)) :
    EuclideanSpace ℂ (Fin S × Fin (N + 1)) :=
  WithLp.toLp 2 fun p =>
    if O p.1 ∈ A then
      (if p.2 = regIncl (O p.1) then ((Real.sqrt (S : ℝ) : ℂ))⁻¹ else 0)
    else 0

/-- The squared norm of the projected oracle state is the number of accepted oracle inputs
times the squared amplitude. -/
theorem norm_sq_goodSubstate (O : Fin S → Fin N) (A : Finset (Fin N)) :
    ‖goodSubstate O A‖ ^ 2 =
      (fiberCount O A : ℝ) * ‖((Real.sqrt (S : ℝ) : ℂ))⁻¹‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  have hinner : ∀ s : Fin S,
      (∑ i : Fin (N + 1), ‖goodSubstate O A (s, i)‖ ^ 2)
        = if O s ∈ A then ‖((Real.sqrt (S : ℝ) : ℂ))⁻¹‖ ^ 2 else 0 := by
    intro s
    by_cases hs : O s ∈ A
    · have hterm : ∀ i : Fin (N + 1), goodSubstate O A (s, i)
          = if i = regIncl (O s) then ((Real.sqrt (S : ℝ) : ℂ))⁻¹ else 0 := by
        intro i
        simp [goodSubstate, hs]
      simp only [hterm]
      rw [Finset.sum_eq_single (regIncl (O s))]
      · simp [hs]
      · intro b _ hb
        simp [hb]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have hterm : ∀ i : Fin (N + 1), goodSubstate O A (s, i) = 0 := by
        intro i
        simp [goodSubstate, hs]
      simp only [hterm, norm_zero]
      simp [hs]
  rw [Finset.sum_congr rfl fun s _ => hinner s, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul]
  rfl

/-- With a nonempty domain the projected squared norm is the fraction of accepted oracle
inputs. -/
theorem norm_sq_goodSubstate_eq_fraction (O : Fin S → Fin N) (A : Finset (Fin N))
    (hS : 0 < S) :
    ‖goodSubstate O A‖ ^ 2 = (fiberCount O A : ℝ) / (S : ℝ) := by
  have hSpos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hc : ‖((Real.sqrt (S : ℝ) : ℂ))⁻¹‖ = (Real.sqrt (S : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg (S : ℝ))]
  rw [norm_sq_goodSubstate, hc, inv_pow, Real.sq_sqrt hSpos.le]
  field_simp

/-- The distribution generated by the oracle `O`, whose mass at `i` is the fraction of inputs
mapped to `i`. -/
def oracleDist (O : Fin S → Fin N) (hS : 0 < S) : FinDist (Fin N) where
  prob i := ((Finset.univ.filter fun s => O s = i).card : ℝ) / (S : ℝ)
  nonneg _ := by positivity
  sum_one := by
    have hSpos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
    have hcard := Finset.card_eq_sum_card_fiberwise (f := O)
      (s := (Finset.univ : Finset (Fin S))) (t := (Finset.univ : Finset (Fin N)))
      (fun s _ => Finset.mem_univ (O s))
    have hsum : (∑ i : Fin N, ((Finset.univ.filter fun s => O s = i).card : ℝ)) = (S : ℝ) := by
      have := congrArg (fun n : ℕ => (n : ℝ)) hcard
      simpa using this.symm
    rw [← Finset.sum_div, hsum]
    exact div_self hSpos.ne'

/-- The mass of a subset of outcomes is the number of accepted oracle inputs divided by the
domain size. -/
theorem fiberCount_eq_sum_fiber (O : Fin S → Fin N) (A : Finset (Fin N)) :
    fiberCount O A = ∑ i ∈ A, (Finset.univ.filter fun s => O s = i).card := by
  unfold fiberCount
  rw [Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter fun s => O s ∈ A) (t := A) (f := O)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    apply congrArg Finset.card
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      exact ⟨by rw [h]; exact hi, h⟩
  · intro s hs
    exact (Finset.mem_filter.mp hs).2

/-- The mass assigned by `oracleDist` to `A` is the accepted-input fraction. -/
theorem oracleDist_mass (O : Fin S → Fin N) (hS : 0 < S) (A : Finset (Fin N)) :
    (∑ i ∈ A, (oracleDist O hS).prob i) = (fiberCount O A : ℝ) / (S : ℝ) := by
  have hprob : ∀ i : Fin N, (oracleDist O hS).prob i
      = ((Finset.univ.filter fun s => O s = i).card : ℝ) / (S : ℝ) := fun i => rfl
  have hsum : (∑ i ∈ A, ((Finset.univ.filter fun s => O s = i).card : ℝ))
      = (fiberCount O A : ℝ) := by
    have hnat : (∑ i ∈ A, (Finset.univ.filter fun s => O s = i).card) = fiberCount O A := by
      rw [fiberCount_eq_sum_fiber]
    rw [← Nat.cast_sum, hnat]
  simp only [hprob, ← Finset.sum_div, hsum]

/-- The squared norm of the projected oracle state is exactly the `p_A` mass of
[BravyiHarrowHassidim2011], Section 2. -/
theorem norm_sq_goodSubstate_eq_oracleMass (O : Fin S → Fin N) (A : Finset (Fin N))
    (hS : 0 < S) :
    ‖goodSubstate O A‖ ^ 2 = ∑ i ∈ A, (oracleDist O hS).prob i := by
  rw [norm_sq_goodSubstate_eq_fraction O A hS, oracleDist_mass O hS A]

/-- The Euclidean norm of the projected oracle state is the square root of the `p_A` mass, i.e.
the amplitude whose estimation is the subject of Theorem 5. -/
theorem norm_goodSubstate_eq_sqrt_oracleMass (O : Fin S → Fin N) (A : Finset (Fin N))
    (hS : 0 < S) :
    ‖goodSubstate O A‖ = Real.sqrt (∑ i ∈ A, (oracleDist O hS).prob i) := by
  rw [← norm_sq_goodSubstate_eq_oracleMass O A hS,
    Real.sqrt_sq (norm_nonneg (goodSubstate O A))]

/-- The diagonal `0/1` projection onto basis vectors whose output register encodes an accepted
outcome. It acts on every register state and depends only on the outcome set. -/
def goodProjector (S : ℕ) (A : Finset (Fin N)) :
    Matrix (Fin S × Fin (N + 1)) (Fin S × Fin (N + 1)) ℂ :=
  Matrix.diagonal fun p => if p.2 ∈ A.image regIncl then 1 else 0

/-- The projection matrix cuts the oracle state down to `goodSubstate`. -/
theorem goodProjector_mulVec_oracleState (O : Fin S → Fin N) (A : Finset (Fin N)) :
    (goodProjector S A).mulVec (fun p => oracleState O p) = fun p => goodSubstate O A p := by
  funext p
  rw [goodProjector, Matrix.mulVec_diagonal, oracleState_apply]
  by_cases hp : p.2 = regIncl (O p.1)
  · have hmem : p.2 ∈ A.image regIncl ↔ O p.1 ∈ A := by
      rw [hp, Finset.mem_image]
      constructor
      · rintro ⟨i, hi, heq⟩
        rwa [regIncl_injective heq] at hi
      · intro h
        exact ⟨O p.1, h, rfl⟩
    simp only [hmem]
    by_cases h : O p.1 ∈ A <;> simp [hp, goodSubstate, h]
  · simp [hp, goodSubstate]

/-- The `L2Operator` norm of the diagonal projection is at most one. -/
theorem norm_goodProjector_le_one (_hS : 0 < S) (A : Finset (Fin N)) :
    ‖goodProjector S A‖ ≤ 1 := by
  rw [goodProjector, Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg zero_le_one]
  intro p
  by_cases h : p.2 ∈ A.image regIncl <;> simp [h]

/-- A nonempty input register and outcome set give a basis vector on which the projection
acts as the identity, so its `L2Operator` norm is exactly one. -/
theorem norm_goodProjector_eq_one (hS : 0 < S) (A : Finset (Fin N)) (hA : A.Nonempty) :
    ‖goodProjector S A‖ = 1 := by
  refine le_antisymm (norm_goodProjector_le_one hS A) ?_
  rw [goodProjector, Matrix.l2_opNorm_diagonal]
  obtain ⟨i, hi⟩ := hA
  have hle := norm_le_pi_norm (fun p : Fin S × Fin (N + 1) =>
    if p.2 ∈ A.image regIncl then (1 : ℂ) else 0)
    (⟨⟨0, hS⟩, regIncl i⟩ : Fin S × Fin (N + 1))
  have hval : (if regIncl i ∈ A.image regIncl then (1 : ℂ) else 0) = 1 :=
    ite_eq_left (Finset.mem_image_of_mem regIncl hi)
  rw [hval, norm_one] at hle
  exact hle

end Qatlib.Papers.DistTesting09.AmpEstimation
