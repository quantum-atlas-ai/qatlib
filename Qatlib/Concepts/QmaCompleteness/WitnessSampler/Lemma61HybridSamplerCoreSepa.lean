/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.QmaCompleteness.WitnessSampler.Lemma61HybridSamplerCoreStat
import Qatlib.Concepts.QueryWordCore.QueryMachinery.NegativeAdversary
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.PureStateTV
import Qatlib.Concepts.QmaCompleteness.WitnessSampler.TwoOracleDefs

/-!
# Hybrid bound for witness sampling

This module proves `lemma6_1HybridSamplerCore` for circuits with two controlled phase oracles.
Replacing the predicate `S` by a subpredicate `Δ` changes the final state by at most a sum of
square roots of the query-state mass on the differing controlled fibers.

Unitary norm preservation, the hybrid bound, and Cauchy-Schwarz convert a
measurement-probability gap into the quantitative query-mass lower bound. The hybrid method is
standard in quantum query lower bounds; see [BennettEtAl1997].

## Main statements

* `lemma6_1HybridSamplerCore`: average controlled query mass is at least `1 / (36 * (t : ℝ) ^
  2)` under the stated distinguishing gap.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025

namespace Qatlib.Concepts.QmaCompleteness.WitnessSampler

set_option autoImplicit false

open Matrix

/-- The controlled phase oracle `forrPhaseOracleS n S W` belongs to the unitary group on
`ForrSpace n W`. -/
private theorem forrPhaseOracleS_unitary (n : ℕ) (S : Reg n → Bool) (W : Type)
    [Fintype W] [DecidableEq W] :
    forrPhaseOracleS n S W ∈ Matrix.unitaryGroup (ForrSpace n W) ℂ :=
  tensorGate_unitary (phaseOracle_unitary _) (Submonoid.one_mem _)

/-- The controlled phase oracle `forrPhaseOracleU n U W` belongs to the unitary group on
`ForrSpace n W`. -/
private theorem forrPhaseOracleU_unitary (n : ℕ) (U : Reg n → Bool) (W : Type)
    [Fintype W] [DecidableEq W] :
    forrPhaseOracleU n U W ∈ Matrix.unitaryGroup (ForrSpace n W) ℂ := by
  unfold forrPhaseOracleU
  exact tensorGate_unitary (Submonoid.one_mem _)
    (tensorGate_unitary (phaseOracle_unitary _) (Submonoid.one_mem _))

/-- Applying `forrPhaseOracleS n S W` multiplies the amplitude at `p` by negative one when both
the `S` control bit and `S` evaluated on its address are true, and by one otherwise. -/
private theorem applyGate_forrPhaseOracleS (n : ℕ) (S : Reg n → Bool) (W : Type)
    [Fintype W] [DecidableEq W] (φ : QState (ForrSpace n W)) (p : ForrSpace n W) :
    ApplyGate (forrPhaseOracleS n S W) φ p
      = (if p.1.2 && S p.1.1 then (-1 : ℂ) else 1) * φ p := by
  unfold ApplyGate forrPhaseOracleS
  rw [advTensor_mulVec,
    show (∑ q : Reg n × Bool,
        PhaseOracle (fun q => q.2 && S q.1) p.1 q * φ (q, p.2)) =
      ApplyGate (PhaseOracle (fun q => q.2 && S q.1)) (fun q => φ (q, p.2)) p.1 from rfl,
    applyGate_phaseOracle]

/-- Multiplication by a unitary matrix `U` preserves the Euclidean norm of every vector `v`
represented by `toEuclidean_fromVec`. -/
private theorem norm_applyGate_sq_eq {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (v : QState I) :
    ‖toEuclidean_fromVec (U *ᵥ v)‖ = ‖toEuclidean_fromVec v‖ := by
  show ‖toEuclidean_fromVec (ApplyGate U v)‖ = ‖toEuclidean_fromVec v‖
  rw [← toEuclideanCLM_applyGate]
  exact norm_toEuclideanCLM_of_mem_unitaryGroup hU (toEuclidean_fromVec v)

/-- Executing `TORun` with unitary oracle matrices and a circuit satisfying `IsUnitaryTOCircuit`
preserves `Normalized` states. -/
private theorem normalized_torun {I : Type} [Fintype I] [DecidableEq I]
    (oS oU : Matrix I I ℂ) (hS : oS ∈ Matrix.unitaryGroup I ℂ)
    (hU : oU ∈ Matrix.unitaryGroup I ℂ) (C : TOCircuit I) (hC : IsUnitaryTOCircuit C)
    (ψ : QState I) (hψ : Normalized ψ) : Normalized (TORun oS oU C ψ) := by
  induction C generalizing ψ with
  | nil => exact hψ
  | cons s C ih =>
    cases s with
    | gate U' =>
      show Normalized (TORun oS oU C (ApplyGate U' ψ))
      exact ih (fun V hV => hC V (List.mem_cons_of_mem _ hV))
        (ApplyGate U' ψ)
        (normalized_applyGate (hC U' List.mem_cons_self) hψ)
    | queryS =>
      show Normalized (TORun oS oU C (ApplyGate oS ψ))
      exact ih (fun V hV => hC V (List.mem_cons_of_mem _ hV))
        (ApplyGate oS ψ) (normalized_applyGate hS hψ)
    | queryU =>
      show Normalized (TORun oS oU C (ApplyGate oU ψ))
      exact ih (fun V hV => hC V (List.mem_cons_of_mem _ hV))
        (ApplyGate oU ψ) (normalized_applyGate hU hψ)

/-- Executing the same circuit with unitary gates and unitary oracle matrices on two initial
vectors preserves the Euclidean norm of their difference under `TORun`. -/
private theorem norm_torun_sub {I : Type} [Fintype I] [DecidableEq I]
    (oS oU : Matrix I I ℂ) (hS : oS ∈ Matrix.unitaryGroup I ℂ)
    (hU : oU ∈ Matrix.unitaryGroup I ℂ) (C : TOCircuit I) (hC : IsUnitaryTOCircuit C)
    (φ χ : QState I) :
    ‖toEuclidean_fromVec (TORun oS oU C φ - TORun oS oU C χ)‖
      = ‖toEuclidean_fromVec (φ - χ)‖ := by
  induction C generalizing φ χ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U' =>
      show ‖toEuclidean_fromVec (TORun oS oU C (ApplyGate U' φ)
        - TORun oS oU C (ApplyGate U' χ))‖ = _
      rw [ih (fun V hV => hC V (List.mem_cons_of_mem _ hV))
          (ApplyGate U' φ) (ApplyGate U' χ)]
      show ‖toEuclidean_fromVec (U' *ᵥ φ - U' *ᵥ χ)‖ = _
      rw [← Matrix.mulVec_sub]
      exact norm_applyGate_sq_eq U' (hC U' List.mem_cons_self) (φ - χ)
    | queryS =>
      show ‖toEuclidean_fromVec (TORun oS oU C (ApplyGate oS φ)
        - TORun oS oU C (ApplyGate oS χ))‖ = _
      rw [ih (fun V hV => hC V (List.mem_cons_of_mem _ hV))
          (ApplyGate oS φ) (ApplyGate oS χ)]
      show ‖toEuclidean_fromVec (oS *ᵥ φ - oS *ᵥ χ)‖ = _
      rw [← Matrix.mulVec_sub]
      exact norm_applyGate_sq_eq oS hS (φ - χ)
    | queryU =>
      show ‖toEuclidean_fromVec (TORun oS oU C (ApplyGate oU φ)
        - TORun oS oU C (ApplyGate oU χ))‖ = _
      rw [ih (fun V hV => hC V (List.mem_cons_of_mem _ hV))
          (ApplyGate oU φ) (ApplyGate oU χ)]
      show ‖toEuclidean_fromVec (oU *ᵥ φ - oU *ᵥ χ)‖ = _
      rw [← Matrix.mulVec_sub]
      exact norm_applyGate_sq_eq oU hU (φ - χ)

/-- For a circuit with `TOQueryCountS C = 0`, replacing the `S` oracle matrix leaves `TORun`
unchanged for every initial vector. -/
private theorem torun_noS {I : Type} [Fintype I] [DecidableEq I]
    (oS oS' oU : Matrix I I ℂ) (C : TOCircuit I) (hC : TOQueryCountS C = 0)
    (ψ : QState I) : TORun oS oU C ψ = TORun oS' oU C ψ := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U' =>
      have h1 : TOQueryCountS C = 0 := by
        have h2 := hC
        rw [show TOQueryCountS (TOStep.gate U' :: C) = TOQueryCountS C from rfl] at h2
        exact h2
      show TORun oS oU C (ApplyGate U' ψ) = TORun oS' oU C (ApplyGate U' ψ)
      exact ih h1 (ApplyGate U' ψ)
    | queryS =>
      have h1 : TOQueryCountS C + 1 = 0 := by
        have h2 := hC
        rw [show TOQueryCountS (TOStep.queryS :: C) = TOQueryCountS C + 1 from rfl] at h2
        exact h2
      omega
    | queryU =>
      have h1 : TOQueryCountS C = 0 := by
        have h2 := hC
        rw [show TOQueryCountS (TOStep.queryU :: C) = TOQueryCountS C from rfl] at h2
        exact h2
      show TORun oS oU C (ApplyGate oU ψ) = TORun oS' oU C (ApplyGate oU ψ)
      exact ih h1 (ApplyGate oU ψ)

/-- For real functions `a` and `b` on a finite type, their dot product is at most the product of
the square roots of their sums of squares. -/
private theorem sum_mul_le_sqrt_mul_sqrt {ι : Type} [Fintype ι] (a b : ι → ℝ) :
    ∑ i, a i * b i ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) := by
  classical
  set A : EuclideanSpace ℝ ι := WithLp.toLp 2 a with hA
  set B : EuclideanSpace ℝ ι := WithLp.toLp 2 b with hB
  have h : inner ℝ A B = ∑ i, a i * b i := by
    simp [hA, hB, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hcs := norm_inner_le_norm (𝕜 := ℝ) A B
  rw [Real.norm_eq_abs, h] at hcs
  have hn : ∀ (c : ι → ℝ), ‖(WithLp.toLp 2 c : EuclideanSpace ℝ ι)‖
      = Real.sqrt (∑ i, c i ^ 2) := by
    intro c
    rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.norm_sq_eq]
    refine congrArg Real.sqrt ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [show ‖A‖ = Real.sqrt (∑ i, a i ^ 2) from by rw [hA]; exact hn a,
    show ‖B‖ = Real.sqrt (∑ i, b i ^ 2) from by rw [hB]; exact hn b] at hcs
  exact (le_abs_self _).trans hcs

/-- The sum of `f` mapped over a list `L` equals the finite sum of `f L[i]` over indices `i :
Fin L.length`, in any additive commutative monoid. -/
private theorem list_sum_map_eq_fin {α : Type} {β : Type} [AddCommMonoid β]
    (f : α → β) (L : List α) :
    (L.map f).sum = ∑ i : Fin L.length, f L[i] := by
  induction L with
  | nil => simp
  | cons a L ih =>
    show f a + (L.map f).sum
        = ∑ i : Fin (List.length L + 1), f (a :: L)[i]
    rw [ih, Fin.sum_univ_succ]
    have h0 : f ((a :: L)[(0 : Fin (List.length L + 1))]) = f a := rfl
    have hs : ∀ i : Fin (List.length L), f ((a :: L)[i.succ]) = f L[i] := fun _ => rfl
    rw [h0, Finset.sum_congr rfl (fun i _ => hs i)]

/-- For a nonnegative real function `f`, the square of its sum over a list `L` is at most the
length of `L` times the sum of its squared values. -/
private theorem list_cs {α : Type} (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (L : List α) :
    ((L.map f).sum) ^ 2 ≤ (L.length : ℝ) * (L.map (fun x => f x ^ 2)).sum := by
  rw [list_sum_map_eq_fin, list_sum_map_eq_fin (fun x => f x ^ 2)]
  have h1 := sum_mul_le_sqrt_mul_sqrt (a := fun i : Fin L.length => f L[i])
    (b := fun _ : Fin L.length => 1)
  have h2 : ∑ i : Fin L.length, (1 : ℝ) ^ 2 = L.length := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_pow, mul_one]
  have h3 : (0 : ℝ) ≤ Real.sqrt (∑ i : Fin L.length, f L[i] ^ 2) * Real.sqrt (L.length : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h4 : (0 : ℝ) ≤ ∑ i : Fin L.length, f L[i] :=
    Finset.sum_nonneg fun i _ => hf L[i]
  have hA : Real.sqrt (∑ i : Fin L.length, f L[i] ^ 2) ^ 2 = ∑ i : Fin L.length, f L[i] ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hk2 : Real.sqrt (L.length : ℝ) ^ 2 = L.length := Real.sq_sqrt (by positivity)
  rw [Finset.sum_congr rfl (fun i _ => mul_one (f L[i])),
    show (∑ i : Fin L.length, (1 : ℝ) ^ 2) = L.length from h2] at h1
  nlinarith [h1, h3, h4, hA, hk2]

/-- The sum of `f` mapped over any list `L` is nonnegative when `f` is pointwise nonnegative. -/
private theorem list_map_sum_nonneg {α : Type} (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (L : List α) : (0 : ℝ) ≤ (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons]; linarith [hf a, ih]

/-- Pointwise equal functions `f` and `g` have equal mapped sums over every list `L` in an
additive commutative monoid. -/
private theorem list_map_sum_congr {α : Type} {β : Type} [AddCommMonoid β]
    (f g : α → β) (L : List α) (h : ∀ x, f x = g x) :
    (L.map f).sum = (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [h a, ih]

section Diff

variable {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]

/-- When `Δ` is contained in `S`, the difference between applying their `S` phase oracles has
amplitude `(-2 : ℂ) * φ p` on the controlled address fiber in `S` outside `Δ`, and zero
elsewhere. -/
private theorem oracle_diff_apply (S Δ : Reg n → Bool) (hΔ : ∀ x, Δ x → S x)
    (φ : QState (ForrSpace n W)) (p : ForrSpace n W) :
    (forrPhaseOracleS n S W *ᵥ φ - forrPhaseOracleS n Δ W *ᵥ φ) p
      = if p.1.2 = true ∧ S p.1.1 ∧ ¬Δ p.1.1 then (-2 : ℂ) * φ p else 0 := by
  show ApplyGate (forrPhaseOracleS n S W) φ p - ApplyGate (forrPhaseOracleS n Δ W) φ p = _
  rw [applyGate_forrPhaseOracleS n S W, applyGate_forrPhaseOracleS n Δ W]
  by_cases hbs : p.1.2 = true ∧ S p.1.1 = true
  · by_cases hD : Δ p.1.1 = true
    · have e1 : (p.1.2 && S p.1.1) = true := by
        rw [Bool.and_eq_true]; exact hbs
      have e2 : (p.1.2 && Δ p.1.1) = true := by
        rw [Bool.and_eq_true]; exact ⟨hbs.1, hD⟩
      have e3 : ¬(p.1.2 = true ∧ S p.1.1 ∧ ¬Δ p.1.1) := fun h => h.2.2 hD
      rw [ite_eq_left e1, ite_eq_left e2, ite_eq_right e3]
      ring
    · have e1 : (p.1.2 && S p.1.1) = true := by
        rw [Bool.and_eq_true]; exact hbs
      have e2 : ¬((p.1.2 && Δ p.1.1) = true) := by
        rw [Bool.and_eq_true]; intro hc2; exact hD hc2.2
      rw [ite_eq_left e1, ite_eq_right e2, ite_eq_left ⟨hbs.1, hbs.2, hD⟩]
      ring
  · have e1 : ¬((p.1.2 && S p.1.1) = true) := by
      rw [Bool.and_eq_true]; intro hc2; exact hbs hc2
    have e2 : ¬((p.1.2 && Δ p.1.1) = true) := by
      rw [Bool.and_eq_true]; intro hc2; exact hbs ⟨hc2.1, hΔ p.1.1 hc2.2⟩
    rw [ite_eq_right e1, ite_eq_right e2, ite_eq_right (fun h => hbs ⟨h.1, h.2.1⟩)]
    ring

omit [DecidableEq W] in

/-- The controlled fiber measurement mass `controlFiberMass n S Δ W φ` is nonnegative for every
vector `φ`. -/
private theorem controlFiberMass_nonneg (S Δ : Reg n → Bool)
    (φ : QState (ForrSpace n W)) : (0 : ℝ) ≤ controlFiberMass n S Δ W φ := by
  unfold controlFiberMass MeasureProb
  exact Finset.sum_nonneg fun p _ => sq_nonneg (‖φ p‖)

/-- When `Δ` is contained in `S`, the squared Euclidean norm of the difference between their
phase oracle outputs on `φ` equals four times `controlFiberMass n S Δ W φ`. -/
private theorem oracle_diff_norm_sq (S Δ : Reg n → Bool) (hΔ : ∀ x, Δ x → S x)
    (φ : QState (ForrSpace n W)) :
    ‖toEuclidean_fromVec (forrPhaseOracleS n S W *ᵥ φ - forrPhaseOracleS n Δ W *ᵥ φ)‖ ^ 2
      = 4 * controlFiberMass n S Δ W φ := by
  classical
  rw [norm_toEuclidean_fromVec_sq]
  have hpt : ∀ p : ForrSpace n W,
      ‖(forrPhaseOracleS n S W *ᵥ φ - forrPhaseOracleS n Δ W *ᵥ φ) p‖ ^ 2
        = if p.1.2 = true ∧ S p.1.1 ∧ ¬Δ p.1.1 then 4 * ‖φ p‖ ^ 2 else 0 := by
    intro p
    rw [oracle_diff_apply S Δ hΔ φ p]
    by_cases hc : p.1.2 = true ∧ S p.1.1 ∧ ¬Δ p.1.1
    · rw [ite_eq_left hc, ite_eq_left hc]
      have h2 : ‖(-2 : ℂ) * φ p‖ = 2 * ‖φ p‖ := by
        rw [norm_mul, norm_neg]
        norm_num
      rw [h2]
      ring
    · rw [ite_eq_right hc, ite_eq_right hc]
      simp
  unfold controlFiberMass MeasureProb
  rw [Finset.mul_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl (fun p _ => hpt p)

/-- When `Δ` is contained in `S`, the Euclidean norm of the difference between their phase
oracle outputs on `φ` equals twice the square root of `controlFiberMass n S Δ W φ`. -/
private theorem oracle_diff_norm (S Δ : Reg n → Bool) (hΔ : ∀ x, Δ x → S x)
    (φ : QState (ForrSpace n W)) :
    ‖toEuclidean_fromVec (forrPhaseOracleS n S W *ᵥ φ - forrPhaseOracleS n Δ W *ᵥ φ)‖
      = 2 * Real.sqrt (controlFiberMass n S Δ W φ) := by
  have h := oracle_diff_norm_sq S Δ hΔ φ
  have h0 : (0 : ℝ) ≤ controlFiberMass n S Δ W φ := controlFiberMass_nonneg S Δ φ
  have h1 : (0 : ℝ) ≤ ‖toEuclidean_fromVec
      (forrPhaseOracleS n S W *ᵥ φ - forrPhaseOracleS n Δ W *ᵥ φ)‖ := norm_nonneg _
  rw [← Real.sqrt_sq h1, h, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
    show Real.sqrt 4 = 2 from by norm_num]

/-- For a circuit with unitary gates and `Δ` contained in `S`, replacing the `S` phase oracle by
the `Δ` phase oracle changes the final vector by at most twice the sum of square roots of
`controlFiberMass` over the `S` query states of the `Δ` execution. -/
private theorem hybrid_bound (S Δ U : Reg n → Bool) (hΔ : ∀ x, Δ x → S x)
    (C : TOCircuit (ForrSpace n W)) (hC : IsUnitaryTOCircuit C)
    (ψ : QState (ForrSpace n W)) :
    ‖toEuclidean_fromVec (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ
        - TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ)‖
      ≤ 2 * ((sQueryStates (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ).map
          (fun φ => Real.sqrt (controlFiberMass n S Δ W φ))).sum := by
  induction C generalizing ψ with
  | nil => simp [TORun, sQueryStates, toEuclidean_fromVec]
  | cons s C ih =>
    cases s with
    | gate U' =>
      show ‖toEuclidean_fromVec (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C
        (ApplyGate U' ψ) - TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C
        (ApplyGate U' ψ))‖
        ≤ 2 * ((sQueryStates (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C
          (ApplyGate U' ψ)).map (fun φ => Real.sqrt (controlFiberMass n S Δ W φ))).sum
      exact ih (fun V hV => hC V (List.mem_cons_of_mem _ hV)) (ApplyGate U' ψ)
    | queryU =>
      show ‖toEuclidean_fromVec (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C
        (ApplyGate (forrPhaseOracleU n U W) ψ)
        - TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C
        (ApplyGate (forrPhaseOracleU n U W) ψ))‖
        ≤ 2 * ((sQueryStates (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C
          (ApplyGate (forrPhaseOracleU n U W) ψ)).map
          (fun φ => Real.sqrt (controlFiberMass n S Δ W φ))).sum
      exact ih (fun V hV => hC V (List.mem_cons_of_mem _ hV))
        (ApplyGate (forrPhaseOracleU n U W) ψ)
    | queryS =>
      show ‖toEuclidean_fromVec (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C
        (ApplyGate (forrPhaseOracleS n S W) ψ)
        - TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C
        (ApplyGate (forrPhaseOracleS n Δ W) ψ))‖
        ≤ 2 * (Real.sqrt (controlFiberMass n S Δ W ψ)
          + ((sQueryStates (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C
            (ApplyGate (forrPhaseOracleS n Δ W) ψ)).map
            (fun φ => Real.sqrt (controlFiberMass n S Δ W φ))).sum)
      set XS := TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C
        (ApplyGate (forrPhaseOracleS n S W) ψ) with hXS
      set X0 := TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C
        (ApplyGate (forrPhaseOracleS n Δ W) ψ) with hX0
      set XD := TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C
        (ApplyGate (forrPhaseOracleS n Δ W) ψ) with hXD
      set traj := sQueryStates (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C
        (ApplyGate (forrPhaseOracleS n Δ W) ψ) with htraj
      have hsplit : XS - XD = (XS - X0) + (X0 - XD) := by abel
      have h1 : ‖toEuclidean_fromVec (XS - X0)‖
          = 2 * Real.sqrt (controlFiberMass n S Δ W ψ) :=
        (norm_torun_sub (forrPhaseOracleS n S W) (forrPhaseOracleU n U W)
          (forrPhaseOracleS_unitary n S W) (forrPhaseOracleU_unitary n U W) C
          (fun V hV => hC V (List.mem_cons_of_mem _ hV)) _ _).trans
          (oracle_diff_norm S Δ hΔ ψ)
      have h2 := ih (fun V hV => hC V (List.mem_cons_of_mem _ hV))
        (ApplyGate (forrPhaseOracleS n Δ W) ψ)
      rw [hsplit, show toEuclidean_fromVec ((XS - X0) + (X0 - XD))
        = toEuclidean_fromVec (XS - X0) + toEuclidean_fromVec (X0 - XD) from rfl]
      calc ‖toEuclidean_fromVec (XS - X0) + toEuclidean_fromVec (X0 - XD)‖
          ≤ ‖toEuclidean_fromVec (XS - X0)‖ + ‖toEuclidean_fromVec (X0 - XD)‖ :=
              norm_add_le _ _
        _ = 2 * Real.sqrt (controlFiberMass n S Δ W ψ)
            + ‖toEuclidean_fromVec (X0 - XD)‖ := by rw [h1]
        _ ≤ 2 * Real.sqrt (controlFiberMass n S Δ W ψ)
            + 2 * ((traj).map (fun φ => Real.sqrt (controlFiberMass n S Δ W φ))).sum :=
              add_le_add le_rfl h2
        _ = 2 * (Real.sqrt (controlFiberMass n S Δ W ψ)
            + ((traj).map (fun φ => Real.sqrt (controlFiberMass n S Δ W φ))).sum) := by
              ring

/-- For a normalized initial state and a circuit with unitary gates, the squared Euclidean
distance between the executions using `S` and `Δ` phase oracles equals two minus twice the
real part of their final states' `Inner` product. -/
private theorem final_diff_norm_sq (S Δ U : Reg n → Bool)
    (C : TOCircuit (ForrSpace n W)) (hC : IsUnitaryTOCircuit C)
    (ψ : QState (ForrSpace n W)) (hψ : Normalized ψ) :
    ‖toEuclidean_fromVec (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ
        - TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ)‖ ^ 2
      = 2 - 2 * (Inner (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ)
          (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ)).re := by
  classical
  have hnS : Normalized (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ) :=
    normalized_torun _ _ (forrPhaseOracleS_unitary n S W) (forrPhaseOracleU_unitary n U W)
      C hC ψ hψ
  have hnD : Normalized (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) :=
    normalized_torun _ _ (forrPhaseOracleS_unitary n Δ W) (forrPhaseOracleU_unitary n U W)
      C hC ψ hψ
  have hconjre : ∀ a b : ℂ,
      (a * (starRingEnd ℂ) b).re = ((starRingEnd ℂ) a * b).re := by
    intro a b
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  rw [norm_toEuclidean_fromVec_sq]
  have hper : ∀ z : ForrSpace n W,
      ‖(TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ
            - TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z‖ ^ 2
        = ‖TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ z‖ ^ 2
            + ‖TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ z‖ ^ 2
            - 2 * ((starRingEnd ℂ) (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W)
                C ψ z)
                * TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ z).re := by
    intro z
    rw [Pi.sub_apply, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_sub, hconjre]
  have hSsum : ∑ z, ‖TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ z‖ ^ 2
      = 1 := hnS
  have hDsum : ∑ z, ‖TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ z‖ ^ 2
      = 1 := hnD
  have hre : ∑ z, ((starRingEnd ℂ) (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W)
          C ψ z) * TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ z).re
      = (Inner (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ)
          (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ)).re := by
    rw [inner_apply, Complex.re_sum]
  rw [Finset.sum_congr rfl (fun z _ => hper z), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, hSsum, hDsum, hre]
  ring

set_option maxHeartbeats 1000000 in

/-- Establishes `Lemma6_1HybridSamplerCore`: for unitary circuit gates and a normalized initial
state, a `2 / 3` versus `1 / 3` acceptance gap between `S` and a subset `Δ`, with at most
`t` queries to the first oracle, forces the `Δ` execution's summed controlled fiber mass
divided by `t` to be at least `1 / (36 * t ^ 2)`. -/
theorem lemma6_1HybridSamplerCore : Lemma6_1HybridSamplerCore := by
  intro n W _ _ S Δ U t C ψ E hC hψ hΔ hcount haccS haccΔ
  classical
  rcases Nat.eq_zero_or_pos (TOQueryCountS C) with hk0 | hkpos
  · exfalso
    have hrun : TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ
        = TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ :=
      torun_noS _ _ _ C hk0 ψ
    rw [hrun] at haccS
    linarith
  · have hbnd := hybrid_bound S Δ U hΔ C hC ψ
    have hnS : Normalized (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ) :=
      normalized_torun _ _ (forrPhaseOracleS_unitary n S W) (forrPhaseOracleU_unitary n U W)
        C hC ψ hψ
    have hnD : Normalized (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) :=
      normalized_torun _ _ (forrPhaseOracleS_unitary n Δ W) (forrPhaseOracleU_unitary n U W)
        C hC ψ hψ

    have hmp : MeasureProb (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ) E
        - MeasureProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) E
      = ∑ z ∈ E, (BornProb (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ) z
          - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z) := by
      rw [MeasureProb, MeasureProb, ← Finset.sum_sub_distrib]
    have hsub : (1 / 3 : ℝ)
        ≤ ∑ z ∈ E, (BornProb (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ) z
          - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z) := by
      rw [← hmp]
      linarith
    have hsum0 : ∑ z, (BornProb (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ) z
        - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z) = 0 := by
      have e1 : ∑ z, BornProb (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ) z
          = 1 := hnS
      have e2 : ∑ z, BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z
          = 1 := hnD
      rw [Finset.sum_sub_distrib, e1, e2]
      ring
    have hcomp : ∑ z ∈ Eᶜ,
        (BornProb (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ) z
          - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z)
      = -∑ z ∈ E, (BornProb (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ) z
          - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z) := by
      have hsplit : (∑ z ∈ E, (BornProb (TORun (forrPhaseOracleS n S W)
            (forrPhaseOracleU n U W) C ψ) z
            - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z))
          + (∑ z ∈ Eᶜ, (BornProb (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ) z
            - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z)) = 0 := by
        rw [Finset.sum_add_sum_compl]
        exact hsum0
      linarith
    have key : (1 / 3 : ℝ)
        ≤ (1 / 2) * ∑ z, |BornProb (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ) z
          - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z| := by
      have h1 : (1 / 3 : ℝ) ≤ |∑ z ∈ E, (BornProb (TORun (forrPhaseOracleS n S W)
            (forrPhaseOracleU n U W) C ψ) z
            - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z)| := by
        rw [abs_of_nonneg (by linarith)]
        exact hsub
      have hd2 : (∑ z ∈ E, (BornProb (TORun (forrPhaseOracleS n S W)
              (forrPhaseOracleU n U W) C ψ) z
              - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z))
            - (∑ z ∈ Eᶜ, (BornProb (TORun (forrPhaseOracleS n S W)
              (forrPhaseOracleU n U W) C ψ) z
              - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z))
          = 2 * ∑ z ∈ E, (BornProb (TORun (forrPhaseOracleS n S W)
              (forrPhaseOracleU n U W) C ψ) z
              - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z) := by
        rw [hcomp]
        ring
      have habsE : |∑ z ∈ E, (BornProb (TORun (forrPhaseOracleS n S W)
            (forrPhaseOracleU n U W) C ψ) z
            - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z)|
          ≤ ∑ z ∈ E, |BornProb (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ) z
            - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z| :=
        Finset.abs_sum_le_sum_abs _ _
      have habsC : |∑ z ∈ Eᶜ, (BornProb (TORun (forrPhaseOracleS n S W)
            (forrPhaseOracleU n U W) C ψ) z
            - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z)|
          ≤ ∑ z ∈ Eᶜ, |BornProb (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ) z
            - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z| :=
        Finset.abs_sum_le_sum_abs _ _
      calc (1 / 3 : ℝ)
          ≤ |∑ z ∈ E, (BornProb (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ) z
              - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z)| :=
            h1
        _ = (1 / 2) * |(∑ z ∈ E, (BornProb (TORun (forrPhaseOracleS n S W)
              (forrPhaseOracleU n U W) C ψ) z
              - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z))
            - (∑ z ∈ Eᶜ, (BornProb (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W)
              C ψ) z
              - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z))| := by
              rw [hd2, abs_mul, abs_two]
              ring
        _ ≤ (1 / 2) * ((∑ z ∈ E, |BornProb (TORun (forrPhaseOracleS n S W)
              (forrPhaseOracleU n U W) C ψ) z
              - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z|)
            + (∑ z ∈ Eᶜ, |BornProb (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W)
              C ψ) z
              - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z|)) := by
              refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) (by norm_num)
              exact add_le_add habsE habsC
        _ = (1 / 2) * ∑ z, |BornProb (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W)
              C ψ) z
            - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z| := by
              rw [← Finset.sum_add_sum_compl]

    have hfid : (1 / 2 : ℝ) * ∑ z, |BornProb (TORun (forrPhaseOracleS n S W)
          (forrPhaseOracleU n U W) C ψ) z
          - BornProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) z|
        ≤ Real.sqrt (1 - ‖Inner (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ)
            (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ)‖ ^ 2) := by
      have h := pureState_born_tv_le_sqrt_fidelity
        (1 : Matrix (ForrSpace n W) (ForrSpace n W) ℂ) (Submonoid.one_mem _)
        (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ)
        (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) hnS hnD
      simpa [ApplyGate, Matrix.one_mulVec] using h
    have hfid' : (1 / 3 : ℝ)
        ≤ Real.sqrt (1 - ‖Inner (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ)
            (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ)‖ ^ 2) :=
      key.trans hfid
    have hident := final_diff_norm_sq S Δ U C hC ψ hψ
    have hcabs : 1 - ‖Inner (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ)
          (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ)‖ ^ 2
        ≤ ‖toEuclidean_fromVec (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ
            - TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ)‖ ^ 2 := by
      have hnn : (0 : ℝ) ≤ ‖Inner (TORun (forrPhaseOracleS n S W)
            (forrPhaseOracleU n U W) C ψ)
            (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) - 1‖ ^ 2 :=
        sq_nonneg _
      have hsub1 : ‖Inner (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ)
            (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) - 1‖ ^ 2
          = ‖Inner (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ)
              (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ)‖ ^ 2
            + 1 - 2 * (Inner (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ)
              (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ)).re := by
        have h := Complex.normSq_sub
          (Inner (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ)
            (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ)) 1
        rw [Complex.normSq_one, map_one (starRingEnd ℂ), mul_one] at h
        rw [show ‖Inner (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ)
              (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) - 1‖ ^ 2
            = Complex.normSq (Inner (TORun (forrPhaseOracleS n S W)
                (forrPhaseOracleU n U W) C ψ)
                (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) - 1) from
            (Complex.normSq_eq_norm_sq _).symm, h, Complex.normSq_eq_norm_sq _]
      rw [hsub1] at hnn
      rw [hident]
      nlinarith [hnn]
    have hrad : (0 : ℝ) < 1 - ‖Inner (TORun (forrPhaseOracleS n S W)
          (forrPhaseOracleU n U W) C ψ)
          (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ)‖ ^ 2 :=
      Real.sqrt_pos.mp (by linarith)
    have hsq : (1 / 3 : ℝ) ^ 2
        ≤ 1 - ‖Inner (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ)
            (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ)‖ ^ 2 := by
      have h5 : Real.sqrt (1 - ‖Inner (TORun (forrPhaseOracleS n S W)
            (forrPhaseOracleU n U W) C ψ)
            (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ)‖ ^ 2) ^ 2
          = 1 - ‖Inner (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ)
            (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ)‖ ^ 2 :=
        Real.sq_sqrt hrad.le
      nlinarith [h5, hfid']
    have hdiff : (1 / 3 : ℝ)
        ≤ ‖toEuclidean_fromVec (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ
            - TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ)‖ := by
      have hnd : (0 : ℝ) ≤ ‖toEuclidean_fromVec
          (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ
            - TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ)‖ := norm_nonneg _
      nlinarith [hcabs, hsq, hnd]

    have hsm : (1 / 6 : ℝ)
        ≤ ((sQueryStates (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ).map
            (fun φ => Real.sqrt (controlFiberMass n S Δ W φ))).sum := by
      linarith

    have hmassnn : ∀ φ : QState (ForrSpace n W), (0 : ℝ) ≤ controlFiberMass n S Δ W φ := by
      intro φ
      exact controlFiberMass_nonneg S Δ φ
    have hcs := list_cs (fun φ => Real.sqrt (controlFiberMass n S Δ W φ))
      (fun φ => Real.sqrt_nonneg (controlFiberMass n S Δ W φ))
      (sQueryStates (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ)
    have hlen : (sQueryStates (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ).length
        = TOQueryCountS C := sQueryStates_length _ _ C ψ
    have hkposR : (0 : ℝ) < (TOQueryCountS C : ℝ) := by exact_mod_cast hkpos
    have hmapconv : ((sQueryStates (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ).map
          (fun φ => Real.sqrt (controlFiberMass n S Δ W φ) ^ 2)).sum
        = ((sQueryStates (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ).map
            (controlFiberMass n S Δ W)).sum := by
      exact list_map_sum_congr _ _ _ (fun φ => Real.sq_sqrt (hmassnn φ))
    rw [hmapconv, hlen] at hcs
    have hsumm : (1 : ℝ) / (36 * (TOQueryCountS C : ℝ))
        ≤ ((sQueryStates (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ).map
            (controlFiberMass n S Δ W)).sum := by
      have hsnn : (0 : ℝ) ≤ ((sQueryStates (forrPhaseOracleS n Δ W)
          (forrPhaseOracleU n U W) C ψ).map
          (fun φ => Real.sqrt (controlFiberMass n S Δ W φ))).sum :=
        list_map_sum_nonneg _ (fun φ => Real.sqrt_nonneg _) _
      have hsq2 : (1 / 6 : ℝ) ^ 2
          ≤ (((sQueryStates (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ).map
            (fun φ => Real.sqrt (controlFiberMass n S Δ W φ))).sum) ^ 2 :=
        by nlinarith [hsm, hsnn]
      have hmid : (1 / 6 : ℝ) ^ 2
          ≤ (TOQueryCountS C : ℝ) * (((sQueryStates (forrPhaseOracleS n Δ W)
            (forrPhaseOracleU n U W) C ψ).map
            (controlFiberMass n S Δ W)).sum) :=
        hsq2.trans hcs
      have hkinv : (TOQueryCountS C : ℝ) * (1 / (36 * (TOQueryCountS C : ℝ)))
          = 1 / 36 := by
        field_simp
      by_contra hcon
      push Not at hcon
      have hlt : (TOQueryCountS C : ℝ)
          * (((sQueryStates (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ).map
              (controlFiberMass n S Δ W)).sum)
          < (TOQueryCountS C : ℝ) * (1 / (36 * (TOQueryCountS C : ℝ))) :=
        mul_lt_mul_of_pos_left hcon hkposR
      rw [hkinv] at hlt
      linarith
    have htR : (0 : ℝ) < (t : ℝ) := by
      have : (0 : ℕ) < t := by omega
      exact_mod_cast this
    have htk : (TOQueryCountS C : ℝ) ≤ (t : ℝ) := by exact_mod_cast hcount
    have harith : ∀ (s k tt : ℝ), (0 : ℝ) < k → (0 : ℝ) < tt → k ≤ tt →
        1 / (36 * k) ≤ s → (1 / tt) * s ≥ 1 / (36 * tt ^ 2) := by
      intro s k tt hk ht htk hs
      have hp : (0 : ℝ) < 36 * tt * k := by nlinarith
      have hp2 : (0 : ℝ) < 36 * tt ^ 2 := by nlinarith
      calc (1 / tt) * s
          ≥ (1 / tt) * (1 / (36 * k)) := mul_le_mul_of_nonneg_left hs (by positivity)
        _ = 1 / (36 * tt * k) := by
            field_simp
        _ ≥ 1 / (36 * tt ^ 2) := by
            rw [ge_iff_le, div_le_div_iff₀ hp2 hp]
            nlinarith
    exact harith _ _ _ hkposR htR htk hsumm

end Diff

end Qatlib.Concepts.QmaCompleteness.WitnessSampler
