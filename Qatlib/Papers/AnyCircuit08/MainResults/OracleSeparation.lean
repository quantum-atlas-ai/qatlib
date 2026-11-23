/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AnyCircuit08.MainResults.BitQueryTree
public import Qatlib.Papers.AnyCircuit08.MainResults.PhaseOracle

/-!
# Quantum and classical readout of the same Boolean oracle

[HallgrenHarrow2008], Theorem 9, constructs a Boolean oracle from a pseudo-dispersing
circuit. The circuit here is a linear isometry on the query subspace, which permits an
output register and workspace. The success probability is the Born marginal on the
output register. The classical conclusion concerns uniform secrets and arbitrary finite
randomized mixtures of adaptive Boolean query trees.

[arXiv:0805.0007v2](https://arxiv.org/abs/0805.0007v2)
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.AnyCircuit08.MainResults

open Qatlib.Papers.AnyCircuit08.MainResults

/-- The column amplitudes of the circuit on computational basis inputs. -/
def circuitAmplitudes {X M W : Type} [Fintype X] [Fintype M] [Fintype W]
    (V : EuclideanSpace ℂ X →ₗᵢ[ℂ] EuclideanSpace ℂ (M × W)) (a : M) (w : W) (x : X) : ℂ :=
  V (EuclideanSpace.basisFun X ℂ x) (a, w)

/-- The Born probability of observing `a` when the workspace is ignored. -/
def outputProbability {M W : Type} [Fintype M] [Fintype W]
    (state : EuclideanSpace ℂ (M × W)) (a : M) : ℝ :=
  ∑ w, ‖state (a, w)‖ ^ 2

/-- Output probabilities sum to the squared Euclidean norm of the state. -/
theorem sum_outputProbability {M W : Type} [Fintype M] [Fintype W]
    (state : EuclideanSpace ℂ (M × W)) :
    ∑ a, outputProbability state a = ‖state‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

/-- A unit auxiliary vector's squared overlap is bounded by the Born marginal at `a`. -/
private theorem overlap_le_outputProbability {M W : Type} [Fintype M] [Fintype W]
    (state : EuclideanSpace ℂ (M × W)) (a : M)
    (ψ : W → ℂ) (hψ : IsUnitVector ψ) :
    ‖∑ w, ψ w * state (a, w)‖ ^ 2 ≤ outputProbability state a := by
  let witness : EuclideanSpace ℂ W := WithLp.toLp 2 (fun w => star (ψ w))
  let slice : EuclideanSpace ℂ W := WithLp.toLp 2 (fun w => state (a, w))
  have hwitness : ‖witness‖ = 1 := by
    have hsq : ‖witness‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simpa [witness, IsUnitVector] using hψ
    nlinarith [norm_nonneg witness]
  have hinner : inner ℂ witness slice = ∑ w, ψ w * state (a, w) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [RCLike.inner_apply']
    change star (star (ψ w)) * state (a, w) = _
    rw [star_star]
  have hcauchy := norm_inner_le_norm (𝕜 := ℂ) witness slice
  rw [hinner, hwitness, one_mul] at hcauchy
  rw [← show ‖slice‖ ^ 2 = outputProbability state a from EuclideanSpace.norm_sq_eq slice]
  exact pow_le_pow_left₀ (norm_nonneg _) hcauchy 2

/-- A circuit applied to signed uniform amplitudes has the corresponding computational
basis expansion at each output coordinate. -/
private theorem apply_oracleState {A X M W : Type} [Fintype X] [Fintype M] [Fintype W]
    (V : EuclideanSpace ℂ X →ₗᵢ[ℂ] EuclideanSpace ℂ (M × W))
    (f : A → X → Bool) (a : A) (b : M) (w : W) :
    V (WithLp.toLp 2 (oracleState f a)) (b, w) =
      ∑ x, oracleState f a x * circuitAmplitudes V b w x := by
  let v : EuclideanSpace ℂ X := WithLp.toLp 2 (oracleState f a)
  have hv := (EuclideanSpace.basisFun X ℂ).sum_repr v
  let coord : EuclideanSpace ℂ (M × W) →ₗ[ℂ] ℂ := PiLp.projₗ 2 (fun _ : M × W => ℂ) (b, w)
  have heq := congrArg (coord.comp V.toLinearMap) hv
  change (V v) (b, w) = ∑ x, v x * V (EuclideanSpace.basisFun X ℂ x) (b, w)
  simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr, LinearMap.comp_apply,
    coord, PiLp.projₗ_apply, LinearIsometry.coe_toLinearMap, smul_eq_mul] using heq.symm

/-- For each secret, the quantum procedure executes one phase query and then the given
circuit, before observing the output register. -/
def oracleOutput {A X M W : Type} [Fintype X] [DecidableEq X] [Fintype M] [Fintype W]
    (V : EuclideanSpace ℂ X →ₗᵢ[ℂ] EuclideanSpace ℂ (M × W))
    (f : A → X → Bool) (a : A) : EuclideanSpace ℂ (M × W) :=
  V (Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ) (phaseOracle f a) (uniformQueryState X))

/-- The oracle and circuit preserve normalization of the output state. -/
theorem norm_oracleOutput {A X M W : Type} [Fintype X] [Nonempty X] [DecidableEq X]
    [Fintype M] [Fintype W]
    (V : EuclideanSpace ℂ X →ₗᵢ[ℂ] EuclideanSpace ℂ (M × W))
    (f : A → X → Bool) (a : A) : ‖oracleOutput V f a‖ = 1 := by
  rw [oracleOutput, phaseOracle_uniformQueryState, V.norm_map]
  exact norm_oracleState f a

/-- The query separation of [HallgrenHarrow2008], Theorem 9, in the phase-query model.
For a pseudo-dispersing circuit on an `n`-qubit query register, a single Boolean oracle
family gives the uniform quantum success guarantee and the randomized classical lower
bound. The circuit need only be specified on the subspace where its input workspace
is initialized. -/
theorem exists_booleanOracle_separation {X M W : Type} [Fintype X] [DecidableEq X]
    [Fintype M] [DecidableEq M] [Fintype W]
    (V : EuclideanSpace ℂ X →ₗᵢ[ℂ] EuclideanSpace ℂ (M × W))
    {n : ℕ} (hn : 0 < n) (hX : Fintype.card X = 2 ^ n)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hV : IsPseudoDispersing (circuitAmplitudes V) α β) :
    ∃ (S : Finset M) (P : SingleLevelOracleProblem S X),
      1 < S.card ∧ (2 : ℝ) ^ (α * (n : ℝ)) ≤ S.card ∧
      (∀ a : S, (2 / Real.pi * β) ^ 2 ≤ outputProbability (oracleOutput V P.f a) a.1) ∧
      ∀ ⦃q : ℕ⦄ ⦃δ : ℝ⦄, 0 < δ →
        ∀ {R : Type} [Fintype R] (trees : R → BitQueryTree X S q) (weight : R → ℝ),
          (∀ r, 0 ≤ weight r) → (∑ r, weight r = 1) →
          δ ≤ (∑ r, weight r * (trees r).successProbability P.f) →
          α * (n : ℝ) + Real.logb 2 δ ≤ (q : ℝ) := by
  classical
  have : Nonempty X := Fintype.card_pos_iff.mp (by rw [hX]; positivity)
  obtain ⟨S, hS, hsigns⟩ := theorem9_quantum_part (circuitAmplitudes V) hβ.le hV
  have hsize : (2 : ℝ) ^ (α * (n : ℝ)) ≤ S.card := by
    rw [hX, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at hS
    simpa only [mul_comm (n : ℝ) α] using hS
  have hSnontriv : 1 < S.card := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hexp := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (mul_pos hα hn')
    exact_mod_cast hexp.trans_le hsize
  have hex (a : S) := hsigns a.1 a.2
  choose θ hθ ψ hψ hb using hex
  let f : S → X → Bool := fun a x => decide (θ a x = -1)
  have hf (a : S) (x : X) : oracleSign f a x = (θ a x : ℂ) := by
    rcases hθ a x with h | h <;> simp [oracleSign, f, h]
  refine ⟨S, ⟨f⟩, hSnontriv, hsize, ?_, ?_⟩
  · intro a
    let state := oracleOutput V f a
    have hcalc : (∑ w, ψ a w * state (a.1, w)) =
        (1 / (Real.sqrt (Fintype.card X) : ℂ)) *
          ∑ x, (θ a x : ℂ) * ∑ w, ψ a w * circuitAmplitudes V a.1 w x := by
      simp only [state, oracleOutput, phaseOracle_uniformQueryState, apply_oracleState,
        oracleState, hf, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => by ring
    calc
      _ ≤ ‖∑ w, ψ a w * state (a.1, w)‖ ^ 2 := by rw [hcalc]; exact hb a
      _ ≤ _ := overlap_le_outputProbability state a.1 (ψ a) (hψ a)
  · intro q δ hδ R _ trees weight hw hsum hsucc
    exact BitQueryTree.randomized_queries_ge (by simpa using hsize)
      hδ trees f weight hw hsum hsucc

end Qatlib.Papers.AnyCircuit08.MainResults
