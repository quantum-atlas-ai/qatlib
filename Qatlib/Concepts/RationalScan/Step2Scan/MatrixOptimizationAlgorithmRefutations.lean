/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RationalScan.Step2Scan.MatrixOptimizationAlgorithmsDefs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Qatlib.Concepts.RationalScan.Step2Scan.MatrixOptimizationAlgorithms

/-!
# Counterexamples to frozen matrix optimization clauses

This module defines several universally quantified clauses for matrix optimization and proves
their negations by explicit counterexamples. The clauses concern mixture sampling, payoff
widths, sparsification, Step 2, and combined resource guarantees, in the SDP algorithm setting
of [BrandaoSvore2017]. These results concern the locally defined frozen propositions; corrected
statements are provided in `MatrixOptimizationAlgorithms`.

## Main statements

* `not_walkGoal_mixture`: failure of the frozen mixture clause with an arbitrary target vector.
* `not_clause14_frozen`: failure of the frozen payoff and certificate clause.
* `not_walkGoal_sparsify`: failure of the frozen sparsification clause.
* `not_clause13_frozen` and `not_clause16_frozen`: counterexamples to the remaining combined
  clauses.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.RationalScan.Step2Scan

set_option autoImplicit false

open Matrix Qatlib.Concepts.RationalScan.Step2Scan

open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.RationalScan.Step2Scan
noncomputable section

/-- The universal claim that the specified certificate mixture realizes any prescribed vector
`p`, together with a positive sampling ledger. -/
def mixtureClauseFrozen : Prop :=
  ∀ (m T : ℕ) (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (δ α R : ℝ) (p : Fin m → ℝ),
    0 < m → 0 < T → 0 < α → 0 < R → 0 < δ →
    (∀ t < T, ∀ i, 0 ≤ y t i) →
    (∀ t < T, 0 < ∑ i, y t i) →
    (0 < dualSampleScale m (dualCertificate m δ α R j₀ y T) →
      MixtureSamplingProcess m T (dualCertificate m δ α R j₀ y T) p
          (mixtureWeights m δ α R j₀ y T) (mixtureComponents m j₀ y T) ∧
        ∃ draws selectorDraws componentDraws : ℕ,
          0 < draws ∧ MixtureSampleLedger draws selectorDraws componentDraws)
end
noncomputable section

/-- The universally quantified proposition `mixtureClauseFrozen` is false. -/
theorem not_walkGoal_mixture : ¬ mixtureClauseFrozen := by
  intro h
  let y : ℕ → Fin 1 → ℝ := fun _ _ => 1
  have hf := h 1 1 y 0 1 1 1 (fun _ => 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro t _ i; norm_num) (by intro t _; norm_num)
  have hscale : (0 : ℝ) < dualSampleScale 1 (dualCertificate 1 1 1 1 0 y 1) := by
    norm_num [dualSampleScale, dualCertificate, y, Fin.sum_univ_one]
  have hconcl := hf hscale
  have hpe := hconcl.1.2.2.2.2.1
  have hpe0 := congrFun hpe 0
  norm_num [dualSampleDist, dualSampleScale, dualCertificate, y, Fin.sum_univ_one] at hpe0
end
noncomputable section

/-- The universal combined claim of bisection output correctness, lifted rescaling, runtime
bounds, and failure control under the stated instance and access assumptions. -/
def Clause16Frozen : Prop :=
  ∀ (D m K : ℕ) (Aext : Fin (m + 1) → Operator D) (A : Fin m → Operator D)
    (Cv : Operator D) (b : Fin m → ℝ) (j₀ : Fin m)
    (R r δ ξ cO soft softGh softGm softCor5 : ℝ)
    (opt optLift : ℝ) (B : AlphaBisectionRun K) (αmin αmax tol : ℝ) (s : ℕ)
    (yLift : Fin (m + 1) → ℝ) (sol : Fin m → ℝ)
    (X : Fin K → Operator D) (pOut : Fin K → Fin m → ℝ) (Lout : Fin K → ℝ)
    (G_h G_M T_Meas failProb time : ℝ),
    0 < D → 0 < m → 0 < K → 0 < R → 0 < r → 0 < δ → 0 < ξ → 1 < ξ →
    1 ≤ αmin → 0 < tol → 0 < s → 0 < G_h → 0 < G_M → 0 < T_Meas →
    SdpInstance D m A Cv b j₀ R →
    (∀ i : Fin m, Aext i.castSucc = A i) →
    Aext (Fin.last m) = Cv →
    SparseInputAccess D m Aext s →
    AlphaBisectionCorrect K B αmin αmax opt δ tol →
    (∀ k : Fin K, B.answerLarger k = true →
      LargerWitness D m A Cv b (X k) δ (B.guess k) R) ∧
    (∀ k : Fin K, B.answerLarger k = false →
      SampleOutput D m A Cv b (pOut k) (Lout k) δ (B.guess k)) ∧
    (Lemma2OptimalWitness D m A Cv b r opt →
      Lemma2LiftFeasible D m A Cv b R r δ optLift yLift →
      Lemma2Rescale D m A Cv b yLift opt δ) ∧
    (∀ k : Fin K, alphaRescaleAccuracy m b sol (B.guess k) δ) ∧
    SoftOWithin time (thm4TimeLedger R δ G_h G_M T_Meas) soft ∧
    SoftOWithin G_h (cor5GhBudget m R δ) softGh ∧
    SoftOWithin G_M (cor5GmBudget D s R δ) softGm ∧
    SoftOWithin time (cor5TimeLedger D m s R δ) softCor5 ∧
    RunFailureCharge D m R δ ξ cO failProb
end
noncomputable section

/-- The combined universally quantified proposition `Clause16Frozen` is false. -/
theorem not_clause16_frozen : ¬ Clause16Frozen := by
  intro h
  let A : Fin 1 → Operator 1 := fun _ => 1
  let Aext : Fin 2 → Operator 1 := fun _ => 1
  let B : AlphaBisectionRun 1 := {
    lo := fun _ => 1
    hi := fun _ => 2
    guess := fun _ => 2
    answerLarger := fun _ => true }
  have hSdp : SdpInstance 1 1 A (1 : Operator 1) (fun _ => 1) 0 1 := by
    refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact ⟨Matrix.isHermitian_one, by rw [norm_one]⟩
    · exact Matrix.isHermitian_one
    · rw [norm_one]
    · intro i
      norm_num
    · rfl
    · rfl
  have hAext : (∀ i : Fin 1, Aext i.castSucc = A i) ∧ Aext (Fin.last 1) = (1 : Operator 1) := by
    refine ⟨fun i => rfl, rfl⟩
  have hSparse : SparseInputAccess 1 1 Aext 1 := by
    refine ⟨by norm_num, ?_⟩
    intro j k
    have hfilter : (Finset.univ.filter (fun l : Fin 1 => Aext j k l ≠ 0)) =
        (Finset.univ : Finset (Fin 1)) := by
      apply Finset.filter_eq_self.mpr
      intro l _
      have hk : k = l := Subsingleton.elim k l
      have hAx : Aext j = (1 : Operator 1) := rfl
      rw [hk, hAx, Matrix.one_apply, if_pos rfl]
      exact one_ne_zero
    rw [hfilter]
    norm_num
  have hB : AlphaBisectionCorrect 1 B 1 2 (3 / 2 : ℝ) (1 / 2) 1 := by
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      refine ⟨by norm_num, by norm_num⟩
    · intro k hk
      refine ⟨by norm_num, by norm_num⟩
    · intro k hk
      simp [B] at hk
    · norm_num
    · norm_num
    · norm_num
  have hf := h 1 1 1 Aext A (1 : Operator 1) (fun _ => 1) 0
    1 1 (1 / 2) 2 1 0 1 1 1
    (3 / 2 : ℝ) 0 B 1 2 1 1
    (fun _ => 0) (fun _ => 0)
    (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0)
    1 1 1 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hSdp hAext.1 hAext.2 hSparse hB
  have hsoft := hf.2.2.2.2.1
  norm_num [SoftOWithin] at hsoft
end
noncomputable section

/-- The universal width and certificate claim requiring payoff bounds at every natural-numbered
round from assumptions restricted to rounds below `T`. -/
def Clause14Frozen : Prop :=
  ∀ (D m T : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (α R δ ε : ℝ),
    0 < D → 0 < m → 0 < T → 0 < α → 1 ≤ α → 0 < R → α ≤ R → 0 < δ → 0 < ε →
    2 * R * ε ≤ 1 / 2 → 2 * R * ε ≤ δ / 2 →
    SdpInstance D m A Cv b j₀ R →
    (∀ t < T, ∀ i, 0 ≤ y t i) →
    (∀ t < T, certificateObjective m b (y t) ≤ widthExact α →
      certificateObjective m b (y t) ≤ widthSampled α R ε) ∧
    (∀ t < T, certificateObjective m b (y t) ≤ widthSampled α R ε ↔
      certificateObjective m b (y t) ≤ widthExact α + widthBridgeSlack α R ε) ∧
    widthSampled α R ε = widthExact α + widthBridgeSlack α R ε ∧
    ((∀ t < T, certificateObjective m b (y t) ≤ widthExact α) →
      (∀ s, payoffUnitInterval D (dualPayoff D m A Cv α y s)) ∧
        certificateObjective m b (dualCertificate m δ α R j₀ y T) ≤ α * (1 + δ / 2) ∧
        certificateObjective m b (dualCertificate m δ α R j₀ y T) ≤ (1 + δ) * α) ∧
    ((∀ t < T, certificateObjective m b (y t) ≤ widthSampled α R ε) →
      (∀ s, payoffUnitInterval D (dualPayoff D m A Cv α y s)) ∧
        certificateObjective m b (dualCertificate m δ α R j₀ y T) ≤
          α * (1 + δ / 2 + 2 * R * ε) ∧
        certificateObjective m b (dualCertificate m δ α R j₀ y T) ≤ (1 + δ) * α)
end
noncomputable section

/-- The universally quantified payoff and certificate proposition `Clause14Frozen` is false. -/
theorem not_clause14_frozen : ¬ Clause14Frozen := by
  intro h
  let y : ℕ → Fin 1 → ℝ := fun t _ => if t = 0 then 0 else 100
  have hf := h 1 1 1 (fun _ => (1 : Operator 1)) 0 (fun _ => 1) y 0
    1 1 1 (1 / 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by
      refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        exact ⟨Matrix.isHermitian_one, by rw [norm_one]⟩
      · exact Matrix.isHermitian_zero
      · simp
      · intro i
        norm_num
      · rfl
      · rfl)
    (by
      intro t _ i
      have ht : t = 0 := by omega
      subst ht
      norm_num [y])
  have hA1 : ∀ t < 1, certificateObjective 1 (fun _ => 1) (y t) ≤ widthExact 1 := by
    intro t ht
    have ht0 : t = 0 := by omega
    subst ht0
    norm_num [certificateObjective, y, widthExact, Fin.sum_univ_one]
  have hB1 := hf.2.2.2.1 hA1
  have hbad := hB1.1 1
  obtain ⟨_, _, hle⟩ := hbad
  have hdiag := (Matrix.le_iff.mp hle).diag_nonneg (i := (0 : Fin 1))
  have hval : (((1 : Operator 1) -
      dualPayoff 1 1 (fun _ => (1 : Operator 1)) 0 1 y 1) 0 0) =
      ((-98 / 4 : ℝ) : ℂ) := by
    norm_num [dualPayoff, y, Fin.sum_univ_one, Matrix.one_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.add_apply]
  rw [hval] at hdiag
  rw [Complex.zero_le_real] at hdiag
  norm_num at hdiag
end
noncomputable section

/-- The universal claim that the sampled payoff deviation obeys the specified matrix tail bound
and that its sample budget implies the source failure bound. -/
def sparsifyClauseFrozen : Prop :=
  ∀ (D m Q Ndim Mdim : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (q : Fin m → ℝ)
    (y : ℕ → Fin m → ℝ) (t : ℕ) (α mass T R δ ξ : ℝ),
    0 < D → 0 < m → 0 < Q → 0 < Ndim → 0 < Mdim → 0 < α → 0 < mass → 0 < T →
    0 < ξ → 1 < ξ →
    IsSamplingLaw m q →
    mass = ∑ i, y t i →
    (∀ i, y t i = mass * q i) →
    qDrawEventProb m Q q
        (fun tab : Fin Q → Fin m =>
          sparsifyDeviation T <
            ‖dualPayoff D m A Cv α y t - scaledSparsifiedPayoff D m Q A Cv α mass tab‖) ≤
      matrixHoeffdingTail D Q (sparsifyDeviation T) (sparsifySummandBound mass α) ∧
    (Q = sparsifySamples Ndim Mdim R δ ξ →
      matrixHoeffdingTail D Q (sparsifyDeviation T) (sparsifySummandBound mass α) ≤
        sourceFailureTail ξ (Ndim : ℝ) (Mdim : ℝ))
end
noncomputable section

/-- The universally quantified sparsification proposition `sparsifyClauseFrozen` is false. -/
theorem not_walkGoal_sparsify : ¬ sparsifyClauseFrozen := by
  intro h
  let A : Fin 2 → Operator 1 := fun i => (if i = 0 then (10:ℝ) else (-10:ℝ)) • (1 : Operator 1)
  let q : Fin 2 → ℝ := fun _ => 1 / 2
  let y : ℕ → Fin 2 → ℝ := fun _ _ => 1 / 2
  have hf := h 1 2 1 1 1 A 0 q y 0 1 1 1 1 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by exact ⟨fun i => by norm_num, by norm_num [q, Fin.sum_univ_two]⟩)
    (by norm_num [y, Fin.sum_univ_two])
    (by intro i; norm_num [y, q])
  have hpay : dualPayoff 1 2 A 0 1 y 0 = (1 / 2 : ℝ) • (1 : Operator 1) := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [dualPayoff, A, y, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply,
      Matrix.add_apply, Matrix.sub_apply]
  have hnormJ : ∀ j : Fin 2,
      ‖dualPayoff 1 2 A 0 1 y 0 - scaledSparsifiedPayoff 1 2 1 A 0 1 1 (fun _ => j)‖ = 5 / 2 := by
    intro j
    have hj : j = 0 ∨ j = 1 := by
      obtain ⟨n, hn⟩ := j
      interval_cases n
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hj with hj | hj
    · subst hj
      rw [hpay]
      have hs : scaledSparsifiedPayoff 1 2 1 A 0 1 1 (fun _ => (0 : Fin 2)) =
          (3 : ℝ) • (1 : Operator 1) := by
        ext i j
        fin_cases i
        fin_cases j
        norm_num [scaledSparsifiedPayoff, A, Fin.sum_univ_one, Matrix.smul_apply,
          Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply]
      rw [hs, ← sub_smul, norm_smul, Real.norm_eq_abs, norm_one]
      norm_num
    · subst hj
      rw [hpay]
      have hs : scaledSparsifiedPayoff 1 2 1 A 0 1 1 (fun _ => (1 : Fin 2)) =
          (-2 : ℝ) • (1 : Operator 1) := by
        ext i j
        fin_cases i
        fin_cases j
        norm_num [scaledSparsifiedPayoff, A, Fin.sum_univ_one, Matrix.smul_apply,
          Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply]
      rw [hs, ← sub_smul, norm_smul, Real.norm_eq_abs, norm_one]
      norm_num
  have hnorm : ∀ tab : Fin 1 → Fin 2,
      ‖dualPayoff 1 2 A 0 1 y 0 - scaledSparsifiedPayoff 1 2 1 A 0 1 1 tab‖ = 5 / 2 := by
    intro tab
    have htab : tab = fun _ => tab 0 := funext fun i => by rw [Subsingleton.elim i 0]
    rw [htab]
    exact hnormJ (tab 0)
  have hP : ∀ tab : Fin 1 → Fin 2,
      sparsifyDeviation 1 <
        ‖dualPayoff 1 2 A 0 1 y 0 - scaledSparsifiedPayoff 1 2 1 A 0 1 1 tab‖ := by
    intro tab
    rw [hnorm tab]
    norm_num [sparsifyDeviation]
  have hqsum : (∑ tab : Fin 1 → Fin 2, q (tab 0)) = 1 := by
    have hrew : (∑ tab : Fin 1 → Fin 2, q (tab 0)) = ∑ i : Fin 2, q i :=
      Finset.sum_bij (fun tab _ => tab 0)
        (fun a _ => by simp)
        (fun a₁ a₂ _ _ heq => by
          funext i
          rw [Subsingleton.elim i 0]
          exact heq)
        (fun b _ => ⟨fun _ => b, by simp, rfl⟩)
        (fun a _ => rfl)
    rw [hrew, Fin.sum_univ_two]
    norm_num [q]
  have hprob1 : qDrawEventProb 2 1 q
      (fun tab : Fin 1 → Fin 2 =>
        sparsifyDeviation 1 <
          ‖dualPayoff 1 2 A 0 1 y 0 - scaledSparsifiedPayoff 1 2 1 A 0 1 1 tab‖) = 1 := by
    unfold qDrawEventProb qDrawWeight
    have hstep : (∑ tab : Fin 1 → Fin 2,
        (if sparsifyDeviation 1 <
            ‖dualPayoff 1 2 A 0 1 y 0 - scaledSparsifiedPayoff 1 2 1 A 0 1 1 tab‖
          then ∏ j : Fin 1, q (tab j) else 0)) =
        ∑ tab : Fin 1 → Fin 2, q (tab 0) := by
      apply Finset.sum_congr rfl
      intro tab _
      rw [if_pos (hP tab), Fin.prod_univ_one]
    rw [hstep, hqsum]
  have htail : matrixHoeffdingTail 1 1 (sparsifyDeviation 1) (sparsifySummandBound 1 1)
      = Real.exp (-1 / 32) := by
    simp only [matrixHoeffdingTail, sparsifyDeviation, sparsifySummandBound]
    push_cast
    rw [one_mul]
    congr 1
    norm_num
  rw [hprob1, htail] at hf
  have hfalse : ¬ ((1:ℝ) ≤ Real.exp (-1 / 32)) := by
    rw [not_le]
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  exact hfalse hf.1
end
noncomputable section

/-- The universal Step 2 claim combining a loop failure bound, accepted-candidate width and
separation guarantees, resource ledgers, and a no-output separator conclusion. -/
def Clause13Frozen : Prop :=
  ∀ (D m γ Nmax M L : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (ρ : Operator D) (j₀ : Fin m) (α R κ ν ξ : ℝ) (loop : Step2Loop m γ Nmax M),
    0 < D → 0 < m → 0 < γ → 0 < Nmax → 0 < M → 0 < L →
    0 < α → 1 ≤ α → 0 < R → α ≤ R → 0 < κ → 0 < ν → 1 < ξ →
    γ = step2Gamma m κ R →
    Nmax = step2GridMax α κ →
    M = step2SampleM D m R ξ (κ + ν) →
    L = step2SampleL D m ξ (κ + ν) →
    SdpInstance D m A Cv b j₀ R →
    IsDensityOperator ρ →
    Step2LoopLegal D m γ Nmax M A Cv b ρ loop κ R ν →
    loopEventProb m γ Nmax M (loop.law)
        (fun tab : Fin γ → Fin Nmax → Fin M → Fin m =>
          ¬ Step2GoodEvent m γ Nmax M b ⟨loop.law, tab, loop.estA, loop.estC⟩ κ R ν) ≤
      sourceFailureTail ξ (D : ℝ) (m : ℝ) ∧
    (Step2GoodEvent m γ Nmax M b loop κ R ν →
      (∀ k : Fin γ, ∀ N : Fin Nmax,
        step2Accepts m M b (loop.estA k N) (loop.estC k N) (loop.draws k N) α R κ ν
            (step2Mass κ N) →
          (∑ i, b i * step2RoundVector m (step2Mass κ N) (loop.law k) i ≤
            widthSampled α R (κ + ν)) ∧
          (separationSlack α (κ + ν) ≤
            (∑ i, step2RoundVector m (step2Mass κ N) (loop.law k) i *
              (Matrix.trace (A i * ρ)).re) - (Matrix.trace (Cv * ρ)).re) ∧
          ∃ pairs gibbsCopies qDraws stateCopies : ℕ,
            pairs = step2PairIndex k N ∧
              Step2SampleLedger γ Nmax M L pairs gibbsCopies qDraws stateCopies) ∧
      (Step2NoOutput m γ Nmax M b loop α R κ ν →
        (∃ pairs gibbsCopies qDraws stateCopies : ℕ,
          pairs = γ * Nmax ∧
            Step2SampleLedger γ Nmax M L pairs gibbsCopies qDraws stateCopies) ∧
        NoCheapSeparator D m A Cv b ρ α R (κ + ν)))
end
noncomputable section

/-- The universally quantified Step 2 proposition `Clause13Frozen` is false. -/
theorem not_clause13_frozen : ¬ Clause13Frozen := by
  intro h
  let A : Fin 2 → Operator 1 := fun _ => 1
  let Cv : Operator 1 := 1
  let b : Fin 2 → ℝ := fun _ => 1
  let ρ : Operator 1 := 1
  let law : Fin (step2Gamma 2 (1 / 2 : ℝ) 1) → Fin 2 → ℝ :=
    fun k => step2IdealLaw 1 2 A b ρ (1 / 2) 1 (step2Gamma 2 (1 / 2 : ℝ) 1) k
  let draws : Fin (step2Gamma 2 (1 / 2 : ℝ) 1) → Fin (step2GridMax 1 (1 / 2 : ℝ)) →
      Fin (step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)) → Fin 2 := fun _ _ _ => 0
  let estA : Fin (step2Gamma 2 (1 / 2 : ℝ) 1) → Fin (step2GridMax 1 (1 / 2 : ℝ)) →
      Fin 2 → ℝ := fun _ _ _ => 1
  let estC : Fin (step2Gamma 2 (1 / 2 : ℝ) 1) → Fin (step2GridMax 1 (1 / 2 : ℝ)) → ℝ :=
    fun _ _ => 1
  let loop : Step2Loop 2 (step2Gamma 2 (1 / 2 : ℝ) 1) (step2GridMax 1 (1 / 2 : ℝ))
      (step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)) := ⟨law, draws, estA, estC⟩
  have hγpos : 0 < step2Gamma 2 (1 / 2 : ℝ) 1 := by
    have hx : (0:ℝ) < 8 / (1 / 2 : ℝ) ^ 2 * Real.log 2 * 1 ^ 2 := by positivity
    exact Nat.ceil_pos.mpr hx
  have hNmax : step2GridMax 1 (1 / 2 : ℝ) = 2 := by norm_num [step2GridMax]
  have hNmaxpos : 0 < step2GridMax 1 (1 / 2 : ℝ) := by rw [hNmax]; norm_num
  have hMpos : 0 < step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4) := by
    have harg : (1:ℝ) < 8 * (1:ℝ) ^ 2 * ((1:ℕ):ℝ) * ((2:ℕ):ℝ) / ((1 / 2 : ℝ) + 1 / 4) := by
      norm_num
    have hlog : (0:ℝ) <
        Real.log (8 * (1:ℝ) ^ 2 * ((1:ℕ):ℝ) * ((2:ℕ):ℝ) / ((1 / 2 : ℝ) + 1 / 4)) :=
      Real.log_pos harg
    have hlog3 : (0:ℝ) < Real.log (1 + 2) := Real.log_pos (by norm_num)
    have hx : (0:ℝ) <
        80 * sourceLogOnePlus 2
          (8 * (1:ℝ) ^ 2 * ((1:ℕ):ℝ) * ((2:ℕ):ℝ) / ((1 / 2 : ℝ) + 1 / 4)) /
          ((1 / 2 : ℝ) + 1 / 4) ^ 2 := by
      unfold sourceLogOnePlus
      exact div_pos (mul_pos (by norm_num) (div_pos hlog hlog3)) (by norm_num)
    exact Nat.ceil_pos.mpr hx
  have hLpos : 0 < step2SampleL 1 2 2 ((1 / 2 : ℝ) + 1 / 4) := by
    have harg : (1:ℝ) < ((1:ℕ):ℝ) * ((2:ℕ):ℝ) := by norm_num
    have hlog : (0:ℝ) < Real.log (((1:ℕ):ℝ) * ((2:ℕ):ℝ)) := Real.log_pos harg
    have hlog3 : (0:ℝ) < Real.log (1 + 2) := Real.log_pos (by norm_num)
    have hx : (0:ℝ) <
        80 * sourceLogOnePlus 2 (((1:ℕ):ℝ) * ((2:ℕ):ℝ)) / ((1 / 2 : ℝ) + 1 / 4) ^ 2 := by
      unfold sourceLogOnePlus
      exact div_pos (mul_pos (by norm_num) (div_pos hlog hlog3)) (by norm_num)
    exact Nat.ceil_pos.mpr hx
  have hM0 : ((step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)):ℝ) ≠ 0 :=
    by exact_mod_cast (ne_of_gt hMpos)
  have htr : ∀ i : Fin 2, (Matrix.trace (A i * ρ)).re = 1 := by
    intro i
    simp [A, ρ]
  have htrC : (Matrix.trace (Cv * ρ)).re = 1 := by
    simp [Cv, ρ]
  have hl1 : ∀ {m' : ℕ} (q : Fin m' → ℝ), l1Dist q q = 0 := by
    intro m' q
    simp [l1Dist]
  have hSdp : SdpInstance 1 2 A Cv b 0 1 :=
    ⟨by norm_num, by norm_num, by norm_num,
      fun i => ⟨Matrix.isHermitian_one, by rw [norm_one]⟩,
      Matrix.isHermitian_one, by rw [norm_one],
      fun i => by norm_num [b], rfl, rfl⟩
  have hρ : IsDensityOperator ρ := ⟨Matrix.PosSemidef.one, by simp [ρ]⟩
  have hlegal : Step2LoopLegal 1 2 (step2Gamma 2 (1 / 2 : ℝ) 1) (step2GridMax 1 (1 / 2 : ℝ))
      (step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)) A Cv b ρ loop (1 / 2) 1 (1 / 4) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k
      exact step2IdealLaw_isSamplingLaw 1 2 A b ρ (1 / 2) 1 _ k (by norm_num)
    · intro k
      show l1Dist (step2IdealLaw 1 2 A b ρ (1 / 2) 1 _ k)
          (step2IdealLaw 1 2 A b ρ (1 / 2) 1 _ k) ≤ 1 / 4
      rw [hl1]
      norm_num
    · intro k N i
      show |(1:ℝ) - (Matrix.trace (A i * ρ)).re| ≤ 1 / 4
      rw [htr i]
      norm_num
    · intro k N
      show |(1:ℝ) - (Matrix.trace (Cv * ρ)).re| ≤ 1 / 4
      rw [htrC]
      norm_num
  have hf := h 1 2 (step2Gamma 2 (1 / 2 : ℝ) 1) (step2GridMax 1 (1 / 2 : ℝ))
    (step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)) (step2SampleL 1 2 2 ((1 / 2 : ℝ) + 1 / 4))
    A Cv b ρ 0 1 1 (1 / 2) (1 / 4) 2 loop
    (by norm_num) (by norm_num) hγpos hNmaxpos hMpos hLpos
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) rfl rfl rfl rfl hSdp hρ hlegal
  have hgood : Step2GoodEvent 2 (step2Gamma 2 (1 / 2 : ℝ) 1) (step2GridMax 1 (1 / 2 : ℝ))
      (step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)) b loop (1 / 2) 1 (1 / 4) := by
    intro k N
    have hlaw : IsSamplingLaw 2
        (step2IdealLaw 1 2 A b ρ (1 / 2) 1 (step2Gamma 2 (1 / 2 : ℝ) 1) k) :=
      step2IdealLaw_isSamplingLaw 1 2 A b ρ (1 / 2) 1 _ k (by norm_num)
    have hsum1 : (∑ j : Fin (step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)), (1:ℝ)) /
        ((step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)):ℝ) = 1 := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_one, div_self hM0]
    refine ⟨?_, ?_⟩
    · have h1 : (∑ i, loop.law k i * b i) = 1 := by
        show (∑ i, step2IdealLaw 1 2 A b ρ (1 / 2) 1
            (step2Gamma 2 (1 / 2 : ℝ) 1) k i * (1:ℝ)) = 1
        simp only [mul_one]
        exact hlaw.2
      have h2 : (∑ j, b (loop.draws k N j)) /
          ((step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)):ℝ) = 1 := by
        show (∑ j : Fin (step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)), (1:ℝ)) /
          ((step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)):ℝ) = 1
        exact hsum1
      rw [h1, h2]
      norm_num
    · have h3 : (∑ j, loop.estA k N (loop.draws k N j)) /
          ((step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)):ℝ) = 1 := by
        show (∑ j : Fin (step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)), (1:ℝ)) /
          ((step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)):ℝ) = 1
        exact hsum1
      have h4 : (∑ i, loop.law k i * loop.estA k N i) = 1 := by
        show (∑ i, step2IdealLaw 1 2 A b ρ (1 / 2) 1
            (step2Gamma 2 (1 / 2 : ℝ) 1) k i * (1:ℝ)) = 1
        simp only [mul_one]
        exact hlaw.2
      rw [h3, h4]
      norm_num
  have hA := (hf.2 hgood).1
  let k : Fin (step2Gamma 2 (1 / 2 : ℝ) 1) := ⟨0, hγpos⟩
  let N : Fin (step2GridMax 1 (1 / 2 : ℝ)) := ⟨1, by rw [hNmax]; norm_num⟩
  have hmass : step2Mass (1 / 2 : ℝ) N = 1 := by norm_num [step2Mass]
  have hacc : step2Accepts 2 (step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)) b
      (estA k N) (estC k N) (draws k N) 1 1 (1 / 2) (1 / 4) (step2Mass (1 / 2) N) := by
    rw [hmass]
    have hsum1 : (∑ j : Fin (step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)), (1:ℝ)) /
        ((step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)):ℝ) = 1 := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_one, div_self hM0]
    refine ⟨?_, ?_⟩
    · show (1:ℝ) / 1 - (1 / 2 + 1 / 4) ≤
        (∑ j : Fin (step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)), (1:ℝ)) /
          ((step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)):ℝ)
      rw [hsum1]
      norm_num
    · show (∑ j : Fin (step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)), (1:ℝ)) /
          ((step2SampleM 1 2 1 2 ((1 / 2 : ℝ) + 1 / 4)):ℝ) ≤
        1 / 1 + 1 * (1 / 2 + 1 / 4)
      rw [hsum1]
      norm_num
  have hsep := (hA k N hacc).2.1
  have hsumy : (∑ i, step2RoundVector 2 (step2Mass (1 / 2) N) (loop.law k) i *
      (Matrix.trace (A i * ρ)).re) = 1 := by
    simp only [htr, mul_one, step2RoundVector]
    rw [← Finset.mul_sum]
    have hsum : (∑ i, loop.law k i) = 1 := by
      show (∑ i, step2IdealLaw 1 2 A b ρ (1 / 2) 1 (step2Gamma 2 (1 / 2 : ℝ) 1) k i) = 1
      exact (step2IdealLaw_isSamplingLaw 1 2 A b ρ (1 / 2) 1 _ k (by norm_num)).2
    rw [hsum, mul_one, hmass]
  have hfalse : ¬ (separationSlack (1:ℝ) ((1 / 2 : ℝ) + 1 / 4) ≤
      (∑ i, step2RoundVector 2 (step2Mass (1 / 2) N) (loop.law k) i *
        (Matrix.trace (A i * ρ)).re) - (Matrix.trace (Cv * ρ)).re) := by
    rw [hsumy, htrC]
    simp only [separationSlack]
    norm_num
  exact hfalse hsep
end
end Qatlib.Concepts.RationalScan.Step2Scan
