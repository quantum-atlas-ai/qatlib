/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationSharedDefs
import QuantumInfo.ForMathlib.HermitianMat.CFC
import Qatlib.Concepts.MatrixWeights.ApproxGibbs

/-!
# Counterexamples to SDP execution contracts

This module constructs finite counterexamples to four quantified execution contracts using
`MixedReceipt`, `Step2Search`, and `SamplerTree`. The examples expose a query budget smaller
than the number of required distinct queries, a recorded outcome law unsupported by an
atom-weight product condition, an invalid no-output implication, and an exact finite sampler
requirement for a non-dyadic law.

The contracts concern implementation details in the quantum SDP setting of [BrandaoSvore2017].
The refutations apply to the precise formal interfaces stated here, while the helper lemmas
establish the counting and probability facts needed by those counterexamples.

## Main statements

* `clause6_refuted`: Six required distinct queries cannot fit the access receipt's query
  allowance of four.
* `G7.clause7_refuted`: The stated joint-weight and filtration conditions do not force the
  claimed conditional Born law.
* `G8.clause8_refuted`: Exact search estimates and no output do not imply the stated
  no-cheap-separator conclusion.
* `G9.clause9_refuted`: An arbitrary mixture law cannot always be realized exactly by a finite
  fair-bit sampler tree.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.MatrixWeights.WeightsCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.MatrixWeights.ApproxGibbs

set_option autoImplicit false

open Qatlib.Concepts.SdpDuality.ConeSeparation Qatlib.Concepts.MatrixWeights.ApproxGibbs
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

noncomputable local instance : DecidableEq QuantumStep := Classical.decEq _
noncomputable local instance : DecidableEq QueryDesc := Classical.decEq _

namespace Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations
open Filter Topology
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.SdpMmwSolver.OracleError
open Qatlib

/-- An element belonging to a list has count at least one when its Boolean equality is lawful. -/
theorem one_le_count_of_mem {α : Type} [BEq α] [LawfulBEq α] {a : α} {l : List α}
    (h : a ∈ l) : 1 ≤ l.count a := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rw [List.count_cons]
    by_cases hb : b = a
    · rw [hb]; simp
    · rw [if_neg (by simp [hb])]
      rcases List.mem_cons.mp h with h | h
      · exact absurd h.symm hb
      · exact ih h

/-- The sum of the indicators that query descriptors equal `q₀` is the number of occurrences of
`q₀` in the list. -/
theorem sum_ite_eq_count (t : List QueryDesc) (q₀ : QueryDesc) :
    (t.map (fun q => if q = q₀ then (1:ℕ) else 0)).sum = t.count q₀ := by
  induction t with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, List.count_cons, ih]
    by_cases h : a = q₀
    · rw [h]; simp; omega
    · rw [if_neg h]; simp [h]

/-- For a list of distinct query descriptors, the total number of their query-step occurrences
is at most the total query count of the execution steps. -/
theorem sum_count_queries_le (l : List QuantumStep) (t : List QueryDesc) (ht : t.Nodup) :
    (t.map (fun q => l.count (QuantumStep.query q))).sum ≤ (l.map QuantumStep.queries).sum := by
  induction l with
  | nil => simp
  | cons s l ih =>
    have hc : ∀ q : QueryDesc,
        (s :: l).count (QuantumStep.query q)
          = (if s = QuantumStep.query q then 1 else 0) + l.count (QuantumStep.query q) := by
      intro q
      rw [List.count_cons]
      by_cases h : s = QuantumStep.query q
      · rw [h]; simp; omega
      · rw [if_neg (by simp [h])]; simp [h]
    have heq : (t.map (fun q => (s :: l).count (QuantumStep.query q)))
        = t.map (fun q => (if s = QuantumStep.query q then 1 else 0)
          + l.count (QuantumStep.query q)) :=
      congrArg (fun f => List.map f t) (funext fun q => hc q)
    rw [heq, List.sum_map_add]
    refine add_le_add ?_ ih
    cases s with
    | gateWord n gs =>
      have hz : ∀ q : QueryDesc,
          (if QuantumStep.gateWord n gs = QuantumStep.query q then (1:ℕ) else 0) = 0 := by
        intro q
        rw [if_neg (fun h => by cases h)]
      simp [QuantumStep.queries]
    | query q₀ =>
      have hif : ∀ q : QueryDesc,
          (if QuantumStep.query q₀ = QuantumStep.query q then (1:ℕ) else 0)
            = (if q = q₀ then 1 else 0) := by
        intro q
        by_cases h : q = q₀
        · rw [h]; simp
        · rw [if_neg (fun he => h (QuantumStep.query.inj he).symm), if_neg h]
      simp only [hif]
      rw [sum_ite_eq_count]
      have hq : (QuantumStep.query q₀).queries = 1 := rfl
      rw [hq]
      by_cases hm : q₀ ∈ t
      · rw [List.count_eq_one_of_mem ht hm]
      · have h0 : t.count q₀ = 0 := List.count_eq_zero.mpr hm
        omega
/-- The single zero constraint matrix in dimension two used by the clause 6 query-count
counterexample. -/
noncomputable def A0 : Fin 1 → Operator 2 := fun _ => 0
/-- The zero objective matrix in dimension two used by the clause 6 query-count counterexample. -/
noncomputable def Cv0 : Operator 2 := 0
/-- The zero Hamiltonian in dimension two used by the clause 6 execution contract
counterexample. -/
noncomputable def H0 : Operator 2 := 0
/-- The rational weight function assigning weight one to the sole constraint. -/
noncomputable def wt0 : Fin 1 → ℚ := fun _ => 1
/-- The sparse input for the sole zero constraint matrix, with sparsity and bit parameters both
equal to one. -/
noncomputable def encA0 : Fin 1 → SparseMatrixInput 2 := fun _ => ⟨1, 1, fun _ _ => 0⟩
/-- The sparse input for the zero objective matrix, with sparsity and bit parameters both equal
to one. -/
noncomputable def encC0 : SparseMatrixInput 2 := ⟨1, 1, fun _ _ => 0⟩
/-- The one-outcome POVM on dimension two whose sole effect is the identity. -/
noncomputable def Lam0 : POVM (Fin 1) (Fin 2) where
  mats := fun _ => (1 : HermitianMat (Fin 2) ℂ)
  nonneg := fun _ => HermitianMat.zero_le_iff.mpr (by
    rw [HermitianMat.mat_one]; exact Matrix.PosSemidef.one)
  normalized := by
    rw [Fin.sum_univ_one]
/-- The payoff function assigning zero to the only outcome of `Lam0`. -/
noncomputable def f0 : Fin 1 → ℝ := fun _ => 0

/-- The six required query descriptors consisting of all four objective-entry queries and the
two row queries for the sole constraint matrix. -/
noncomputable def q6 : List QueryDesc :=
  [QueryDesc.payoffEntry 2 Cv0 0 0, QueryDesc.payoffEntry 2 Cv0 0 1,
   QueryDesc.payoffEntry 2 Cv0 1 0, QueryDesc.payoffEntry 2 Cv0 1 1,
   QueryDesc.sparseRow 2 1 A0 0 0, QueryDesc.sparseRow 2 1 A0 0 1]

/-- The six query descriptors in `q6` are pairwise distinct. -/
theorem q6_nodup : q6.Nodup := by
  simp [q6, List.nodup_cons]

/-- The sparse input length used as the clause 6 access-query allowance evaluates to four for
the chosen dimension, constraint count, and encoding parameters. -/
theorem sparseInputLength_val :
    sparseInputLength 2 1 encC0.s encC0.bits = 4 := by
  show sparseInputLength 2 1 1 1 = 4
  norm_num [sparseInputLength]

/-- Refutes the stated universal receipt-construction contract because its access receipt must
contain six distinct queries while its query count is bounded by four. This contradiction is
independent of the proposed global cost function `B`. -/
theorem clause6_refuted : ¬
    (  ∃ B : ℕ → ℕ → ℕ → ℕ → ℚ → ℚ → IntCost,
    ∀ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
        (H : Operator D) (β : ℚ) (wt : Fin m → ℚ)
        (encA : Fin m → SparseMatrixInput D) (encC : SparseMatrixInput D)
        (O : Type) (_ : Fintype O) (_ : DecidableEq O)
        (Λ : POVM O (Fin D)) (f : O → ℝ) (oSize : ℕ) (εp δp : ℚ),
      0 < D → 0 < m → 0 < β → 0 < εp → 0 < δp → 0 < oSize →
      (Fintype.card O ≤ oSize) →
      (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
      (Cv.IsHermitian ∧ ‖Cv‖ ≤ 1) →
      (H.IsHermitian ∧ ‖H‖ ≤ 1) →
      (∀ i, 0 < (encA i).s ∧ 0 < (encA i).bits) →
      (0 < encC.s ∧ 0 < encC.bits) →
      (∀ i r c, ((encA i).entry r c : ℂ) = (A i) r c) →
      (∀ r c, (encC.entry r c : ℂ) = Cv r c) →
      (∀ i, 0 ≤ wt i) → ((∑ i, (wt i : ℝ)) = 1) →
      (∀ o, 0 ≤ f o ∧ f o ≤ 1) →
      ∃ (εacc εprep εgibbs εmeas εtrunc : ℝ)
          (δacc δprep δgibbs δmeas δtrunc : ℝ)
          (Racc : MixedReceipt Unit)
          (Rprep : MixedReceipt (Fin m)) (q : Fin m → ℝ)
          (Rgibbs : MixedReceipt Unit) (ρg : Operator D)
          (Rmeas Rmix : MixedReceipt O),
        0 ≤ εacc ∧ 0 ≤ εprep ∧ 0 ≤ εgibbs ∧ 0 ≤ εmeas ∧ 0 ≤ εtrunc ∧
        0 ≤ δacc ∧ 0 ≤ δprep ∧ 0 ≤ δgibbs ∧ 0 ≤ δmeas ∧ 0 ≤ δtrunc ∧
        εacc + εprep + εgibbs + εmeas + εtrunc ≤ (εp : ℝ) ∧
        δacc + δprep + δgibbs + δmeas + δtrunc ≤ (δp : ℝ) ∧
        (Racc.legal ∧
          (∀ i r, QuantumStep.query (QueryDesc.sparseRow D m A i r) ∈ Racc.steps) ∧
          (∀ r c, QuantumStep.query (QueryDesc.payoffEntry D Cv r c) ∈ Racc.steps) ∧
          (∀ n gs, QuantumStep.gateWord n gs ∈ Racc.steps →
            gateWordExecutes n gs ∧
            QuantumStep.gateWord n (finiteWordAdjoint gs) ∈ Racc.steps ∧
            gateWordAdjointExecutes n gs) ∧
          Racc.cost.queries ≤ sparseInputLength D m encC.s encC.bits ∧
          IntCost.le Racc.cost
            (B (totalInputLength D m encC.s encC.bits wt β) D encC.s oSize εp δp)) ∧
        (Rprep.legal ∧ Rprep.realizes q ∧
          (∀ i, 0 ≤ q i) ∧ ((∑ i, q i) = 1) ∧
          ((∑ i, |q i - (wt i : ℝ)|) ≤ εprep) ∧
          (∃ size bits, PaidPrim.argmax size bits ∈ Rprep.prims) ∧
          (∃ bits, PaidPrim.compare bits ∈ Rprep.prims) ∧
          IntCost.le Rprep.cost
            (B (totalInputLength D m encC.s encC.bits wt β) D encC.s oSize εp δp)) ∧
        (Rgibbs.legal ∧ IsDensityOperator ρg ∧
          Qatlib.Concepts.MixedFidelity.FidelityMetric.traceDistance ρg (gibbsState H β) ≤ εgibbs ∧
          (∃ bits, PaidPrim.expApprox bits ∈ Rgibbs.prims) ∧
          (∀ n gs, QuantumStep.gateWord n gs ∈ Rgibbs.steps →
            gateWordExecutes n gs ∧
            QuantumStep.gateWord n (finiteWordAdjoint gs) ∈ Rgibbs.steps ∧
            gateWordAdjointExecutes n gs) ∧
          IntCost.le Rgibbs.cost
            (B (totalInputLength D m encC.s encC.bits wt β) D encC.s oSize εp δp)) ∧
        (Rmeas.legal ∧
          (∃ qmeas : O → ℝ,
            Rmeas.realizes qmeas ∧
            (∑ o, |qmeas o - bornLaw Λ ρg o|) ≤ εmeas) ∧
          IntCost.le Rmeas.cost
            (B (totalInputLength D m encC.s encC.bits wt β) D encC.s oSize εp δp)) ∧
        (Rmix.legal ∧
          (∃ qmix : O → ℝ,
            Rmix.realizes qmix ∧
            (∑ o, |qmix o - bornLaw Λ ρg o|) ≤ εmeas + εgibbs) ∧
          Rmix.cost.queries ≤ Racc.cost.queries + Rgibbs.cost.queries ∧
          Rmix.cost.bitTime ≤ Racc.cost.bitTime + Rgibbs.cost.bitTime +
            Rmeas.cost.bitTime ∧
          IntCost.le Rmix.cost
            (B (totalInputLength D m encC.s encC.bits wt β) D encC.s oSize εp δp)) ∧
        ((∀ (target : Fin m → ℝ) (kbound : ℕ),
            (∀ i, ∃ z : ℤ, target i = (z : ℝ) / (2 ^ kbound : ℝ)) →
            (∀ i, 0 ≤ target i) → (∑ i, target i) = 1 →
            ∃ tree : SamplerTree (Fin m),
              treeRealizes target tree ∧ tree.maxDepth ≤ kbound)
          ∧
          (∀ (target : Fin m → ℝ) (qden : ℕ),
            0 < qden → (∀ i, ∃ z : ℤ, target i = (z : ℝ) / (qden : ℝ)) →
            (∀ i, 0 ≤ target i) → (∑ i, target i) = 1 →
            (∃ (S : RejectReceipt (Fin m)) (expBound : ℝ) (tailBound : ℕ → ℝ),
              S.target = target ∧ S.exactLaw ∧ S.aSFinite ∧
              S.trial.rejectProb < 1 ∧
              0 < expBound ∧ S.expectedBitTime ≤ expBound ∧
              (∀ k, S.tailMass k ≤ tailBound k) ∧
              tailBound 0 = 1 ∧
              (∀ k, tailBound (k + 1) = tailBound k * S.trial.rejectProb) ∧
              (0 < S.trial.rejectProb → ¬ S.hasWorstCaseTimeBound))
            ∨
            (∃ Tr : TruncatedReject (Fin m),
              Tr.timeoutMass ≤ δtrunc ∧
              (∑ i, |Tr.law i - target i|) ≤ εtrunc ∧
              Tr.timeoutMass = Tr.trial.rejectProb ^ Tr.cutoff ∧
              Tr.worstCaseBitTime = Tr.cutoff * Tr.trial.tree.maxDepth))
          ∧
          (∀ (tree : SamplerTree (Fin m)) (target : Fin m → ℝ),
            treeRealizes target tree → ∀ i, IsDyadic (target i))))    := by
  rintro ⟨B, hall⟩
  have hD : (0:ℕ) < 2 := by norm_num
  have hm : (0:ℕ) < 1 := by norm_num
  have hβ : (0:ℚ) < 1 := by norm_num
  have hεp : (0:ℚ) < 1 := by norm_num
  have hδp : (0:ℚ) < 1 := by norm_num
  have hoSize : (0:ℕ) < 1 := by norm_num
  have hcard : Fintype.card (Fin 1) ≤ 1 := by norm_num
  have hA : ∀ i : Fin 1, (A0 i).IsHermitian ∧ ‖A0 i‖ ≤ 1 := by
    intro i
    show (0 : Operator 2).IsHermitian ∧ ‖(0 : Operator 2)‖ ≤ 1
    exact ⟨Matrix.isHermitian_zero, by rw [norm_zero]; norm_num⟩
  have hCv : Cv0.IsHermitian ∧ ‖Cv0‖ ≤ 1 := by
    show (0 : Operator 2).IsHermitian ∧ ‖(0 : Operator 2)‖ ≤ 1
    exact ⟨Matrix.isHermitian_zero, by rw [norm_zero]; norm_num⟩
  have hH : H0.IsHermitian ∧ ‖H0‖ ≤ 1 := by
    show (0 : Operator 2).IsHermitian ∧ ‖(0 : Operator 2)‖ ≤ 1
    exact ⟨Matrix.isHermitian_zero, by rw [norm_zero]; norm_num⟩
  have hencA : ∀ i : Fin 1, 0 < (encA0 i).s ∧ 0 < (encA0 i).bits := by
    intro i; show (0:ℕ) < 1 ∧ (0:ℕ) < 1; exact ⟨by norm_num, by norm_num⟩
  have hencC : 0 < encC0.s ∧ 0 < encC0.bits := by
    show (0:ℕ) < 1 ∧ (0:ℕ) < 1
    exact ⟨by norm_num, by norm_num⟩
  have hentryA : ∀ (i : Fin 1) (r c : Fin 2), ((encA0 i).entry r c : ℂ) = (A0 i) r c := by
    intro i r c
    show ((0 : ℚ) : ℂ) = (0 : Operator 2) r c
    simp
  have hentryC : ∀ (r c : Fin 2), ((encC0.entry r c : ℂ) = Cv0 r c) := by
    intro r c
    show ((0 : ℚ) : ℂ) = (0 : Operator 2) r c
    simp
  have hwt : ∀ i : Fin 1, 0 ≤ wt0 i := by
    intro i; show (0:ℚ) ≤ 1; norm_num
  have hwtsum : (∑ i : Fin 1, (wt0 i : ℝ)) = 1 := by
    rw [Fin.sum_univ_one]; show ((1:ℚ) : ℝ) = 1; norm_num
  have hf : ∀ o : Fin 1, 0 ≤ f0 o ∧ f0 o ≤ 1 := by
    intro o; show 0 ≤ (0:ℝ) ∧ (0:ℝ) ≤ 1; exact ⟨le_rfl, by norm_num⟩
  have hex := hall 2 1 A0 Cv0 H0 (1:ℚ) wt0 encA0 encC0 (Fin 1) inferInstance inferInstance
    Lam0 f0 1 (1:ℚ) (1:ℚ)
    hD hm hβ hεp hδp hoSize hcard hA hCv hH hencA hencC hentryA hentryC hwt hwtsum hf
  obtain ⟨_, _, _, _, _, _, _, _, _, _, Racc, _, _, _, _, _, _, hconj⟩ := hex
  have ha := hconj.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨_, hrows, hpays, _, hq, _⟩ := ha
  have hmem : ∀ q ∈ q6, QuantumStep.query q ∈ Racc.steps := by
    intro q hq6
    simp only [q6, List.mem_cons] at hq6
    rcases hq6 with h | h | h | h | h | h | h
    · rw [h]; exact hpays 0 0
    · rw [h]; exact hpays 0 1
    · rw [h]; exact hpays 1 0
    · rw [h]; exact hpays 1 1
    · rw [h]; exact hrows 0 0
    · rw [h]; exact hrows 0 1
    · exact absurd h (by norm_num)
  have hcount : ∀ q ∈ q6, 1 ≤ Racc.steps.count (QuantumStep.query q) :=
    fun q hq6 => one_le_count_of_mem (hmem q hq6)
  have hsum6 : 6 ≤ (q6.map (fun q => Racc.steps.count (QuantumStep.query q))).sum := by
    have c1 := hcount (QueryDesc.payoffEntry 2 Cv0 0 0) (by simp [q6])
    have c2 := hcount (QueryDesc.payoffEntry 2 Cv0 0 1) (by simp [q6])
    have c3 := hcount (QueryDesc.payoffEntry 2 Cv0 1 0) (by simp [q6])
    have c4 := hcount (QueryDesc.payoffEntry 2 Cv0 1 1) (by simp [q6])
    have c5 := hcount (QueryDesc.sparseRow 2 1 A0 0 0) (by simp [q6])
    have c6 := hcount (QueryDesc.sparseRow 2 1 A0 0 1) (by simp [q6])
    simp only [q6, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    omega
  have hle : (q6.map (fun q => Racc.steps.count (QuantumStep.query q))).sum
      ≤ Racc.cost.queries := by
    show (q6.map (fun q => Racc.steps.count (QuantumStep.query q))).sum
      ≤ (Racc.steps.map QuantumStep.queries).sum
    exact sum_count_queries_le Racc.steps q6 q6_nodup
  have hbound : Racc.cost.queries ≤ 4 := by
    rw [sparseInputLength_val] at hq
    exact hq
  omega
end Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations
namespace Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G7
open Filter Topology
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.SdpMmwSolver.OracleError
open Qatlib

/-- The time-independent two-outcome POVM on dimension one with both effects equal to half the
identity. -/
noncomputable def Lam : ℕ → POVM (Fin 2) (Fin 1) := fun _ =>
  { mats := fun _ => (2:ℝ)⁻¹ • (1 : HermitianMat (Fin 1) ℂ)
    nonneg := fun _ => HermitianMat.zero_le_iff.mpr
      (by
        rw [HermitianMat.mat_smul, HermitianMat.mat_one]
        exact Matrix.PosSemidef.smul Matrix.PosSemidef.one (by positivity))
    normalized := by
      rw [Fin.sum_univ_two]
      have h : ((2:ℝ)⁻¹ + (2:ℝ)⁻¹) = (1:ℝ) := by ring
      rw [← add_smul, h, one_smul] }

/-- The time-independent payoff that is one at outcome zero and zero at outcome one. -/
noncomputable def f0 : ℕ → Fin 2 → ℝ := fun _ o => if o = 0 then (1:ℝ) else 0
/-- The payoff observable obtained from the half-identity POVM `Lam` and the indicator payoff
`f0` at each time. -/
noncomputable def M0 : ℕ → Operator 1 := fun t =>
  Qatlib.Concepts.SdpDuality.ConeSeparation.payoffObservable (Lam t) (f0 t)
/-- The constant identity state in dimension one used as the approximate state in the clause 7
counterexample. -/
noncomputable def approx0 : ℕ → Operator 1 := fun _ => 1

/-- The finite probability space on two atoms, each of probability one half. -/
noncomputable def S2 : FiniteSupportSpace (Fin 2) where
  prob := fun _ => (1:ℝ) / 2
  prob_nonneg := fun _ => by norm_num
  prob_sum := by
    rw [Fin.sum_univ_two]
    norm_num

/-- The record map that returns outcome zero for every time, sample index, and atom. -/
def Zrec0 : ℕ → Fin 1 → Fin 2 → Fin 2 := fun _ _ _ => 0

/-- The constant trivial filtration whose events are exactly the empty set and the whole
two-atom space. -/
def F0 : Filtration (Fin 2) where
  events := fun _ => {E | E = ∅ ∨ E = Set.univ}
  mono := fun _ _ _ E hE => hE
  univ_mem := fun _ => Or.inr rfl
  compl_mem := fun _ E hE => by
    rcases hE with h | h
    · rw [h, Set.diff_empty]; exact Or.inr rfl
    · rw [h, Set.diff_self]; exact Or.inl rfl
  union_mem := fun _ E F hE hF => by
    rcases hE with hE | hE <;> rcases hF with hF | hF
    · rw [hE, hF, Set.empty_union]; exact Or.inl rfl
    · rw [hE, hF, Set.empty_union]; exact Or.inr rfl
    · rw [hE, hF, Set.union_empty]; exact Or.inr rfl
    · rw [hE, hF, Set.union_self]; exact Or.inr rfl

/-- A time-independent receipt with no execution steps or paid primitives and a single fair-bit
output tree emitting zero or one. -/
noncomputable def Rprog0 : ℕ → MixedReceipt (Fin 2) := fun _ =>
  { width := 0, steps := [], prims := [],
    out := SamplerTree.bit (SamplerTree.emit 0) (SamplerTree.emit 1) }
/-- The identically zero state-approximation error allowance for the clause 7 counterexample. -/
noncomputable def xi0 : ℕ → ℝ := fun _ => 0
/-- The identically zero program-law error allowance for the clause 7 counterexample. -/
noncomputable def eprog0 : ℕ → ℝ := fun _ => 0

/-- The initial matrix multiplicative weights state in dimension one is the identity, for any
payoff history and learning rate. -/
theorem mmwState_one_zero (M : ℕ → Operator 1) (η : ℝ) :
    mmwState 1 M η 0 = (1 : Operator 1) := by
  have hwt : Qatlib.Concepts.MatrixWeights.WeightsCore.mmwWeight 1 M η 0 = (1 : Operator 1) := by
    unfold Qatlib.Concepts.MatrixWeights.WeightsCore.mmwWeight
    rw [Finset.range_zero, Finset.sum_empty, smul_zero, NormedSpace.exp_zero]
  unfold mmwState
  rw [hwt, Matrix.trace_fin_one]
  show (((1 : Operator 1) 0 0).re : ℂ)⁻¹ • (1 : Operator 1) = 1
  simp

/-- Each outcome of `Lam 0` has Born probability one half on the identity state in dimension
one. -/
theorem bornLaw_half : ∀ o : Fin 2, bornLaw (Lam 0) (1 : Operator 1) o = (1:ℝ) / 2 := by
  intro o
  show (Matrix.trace (((Lam 0).mats o).mat * (1 : Operator 1))).re = _
  rw [show ((Lam 0).mats o).mat = (2:ℝ)⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℂ) by
      simp [Lam, HermitianMat.mat_smul, HermitianMat.mat_one]]
  rw [Matrix.mul_one, Matrix.trace_fin_one]
  show (((2:ℝ)⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 0).re = _
  simp

/-- The probability of the whole two-atom space `S2` is one. -/
theorem S2_eventProb_univ : S2.eventProb Set.univ = 1 := by
  unfold FiniteSupportSpace.eventProb
  simp only [Set.mem_univ, if_true]
  show (∑ _ω : Fin 2, (1:ℝ) / 2) = 1
  rw [Fin.sum_univ_two]
  norm_num

/-- Conditioned on the whole space, the indicator that the constant record is zero has
expectation one. -/
theorem condExpect_univ_one :
    S2.condExpect Set.univ (fun ω : Fin 2 => if Zrec0 0 0 ω = 0 then (1:ℝ) else 0) = 1 := by
  have hZ : ∀ ω : Fin 2, (if Zrec0 0 0 ω = 0 then (1:ℝ) else 0) = 1 := by
    intro ω
    show (if (0:Fin 2) = 0 then (1:ℝ) else 0) = 1
    simp
  unfold FiniteSupportSpace.condExpect
  rw [S2_eventProb_univ]
  have h0 : (0:ℝ) < 1 := by norm_num
  simp only [if_pos h0, Set.mem_univ, if_true, inv_one, one_mul, hZ]
  show (∑ _ω : Fin 2, (1:ℝ) / 2 * 1) = 1
  rw [Fin.sum_univ_two]
  norm_num

/-- Refutes the stated universal sampling and concentration contract using a constant record on
two equiprobable atoms. The listed atom-weight product and filtration conditions hold, but
the claimed conditional outcome probability would equate one with one half. -/
theorem clause7_refuted : ¬
    (  ∀ (D T L : ℕ) (M : ℕ → Operator D) (approx : ℕ → Operator D)
      (O : Type) (_ : Fintype O) (_ : DecidableEq O)
      (Λ : ℕ → POVM O (Fin D)) (f : ℕ → O → ℝ)
      (Ω : Type) (_ : Fintype Ω) (S : FiniteSupportSpace Ω) (F : Filtration Ω)
      (Zrec : ℕ → Fin L → Ω → O)
      (Rprog : ℕ → MixedReceipt O)
      (η : ℝ) (ξ εprog : ℕ → ℝ) (εtot δtot : ℝ),
    0 < D → 0 < T → 0 < L → 0 < η → η ≤ 1 → 0 < εtot → 0 < δtot →
    (∀ t < T, IsDensityOperator (approx t)) →
    (∀ t < T, M t = Qatlib.Concepts.SdpDuality.ConeSeparation.payoffObservable (Λ t) (f t)) →
    (∀ t < T, ∀ o, 0 ≤ f t o ∧ f t o ≤ 1) →
    (∀ t < T, 0 ≤ ξ t) →
    (∀ t < T, 0 ≤ εprog t) →
    (∀ t < T, Qatlib.Concepts.MixedFidelity.FidelityMetric.traceDistance (approx t) (mmwState D M η t) ≤ ξ t) →
    (∀ t < T, (Rprog t).legal ∧
      (∃ qprog : O → ℝ,
        (Rprog t).realizes qprog ∧
        (∑ o, |qprog o - bornLaw (Λ t) (approx t) o|) ≤ εprog t)) →
    (∀ ω : Ω, S.prob ω =
      ∏ t ∈ Finset.range T, ∏ l : Fin L, bornLaw (Λ t) (approx t) (Zrec t l ω)) →
    (∀ t < T, ∀ E : Set Ω, E ∈ F.events t → ∀ ω ω' : Ω,
      (∀ s < t, ∀ l : Fin L, Zrec s l ω = Zrec s l ω') → (ω ∈ E ↔ ω' ∈ E)) →
    (∀ t < T, ∀ E : Set Ω, E ∈ F.events t → 0 < S.eventProb E →
      ∀ l : Fin L, ∀ o : O,
        S.condExpect E (fun ω => if Zrec t l ω = o then (1 : ℝ) else 0) =
          bornLaw (Λ t) (approx t) o) ∧
    (∀ t < T, ∀ E : Set Ω, E ∈ F.events t → 0 < S.eventProb E →
      ∀ l : Fin L,
        S.condExpect E (fun ω => f t (Zrec t l ω)) =
          (Matrix.trace (M t * approx t)).re) ∧
    (∀ t < T, ∀ E : Set Ω, E ∈ F.events t → 0 < S.eventProb E →
      S.condExpect E (fun ω => (∑ l : Fin L, f t (Zrec t l ω)) / L) =
        (Matrix.trace (M t * approx t)).re) ∧
    (∀ t < T, ∀ l : Fin L, ∀ ω : Ω,
      0 ≤ f t (Zrec t l ω) ∧ f t (Zrec t l ω) ≤ 1) ∧
    (∀ t < T, ∀ E : Set Ω, E ∈ F.events t → 0 < S.eventProb E →
      S.condExpect E (fun ω =>
        (∑ l : Fin L, f t (Zrec t l ω)) / L - (Matrix.trace (M t * approx t)).re) = 0) ∧
    (∀ t < T,
      ∑ ω : Ω, S.prob ω * ((∑ l : Fin L, f t (Zrec t l ω)) / L) =
        (Matrix.trace (M t * approx t)).re) ∧
    (∀ t < T, ∀ E : Set Ω, E ∈ F.events t → S.eventProb E = 0 →
      ∀ l : Fin L, ∀ o : O,
        S.condExpect E (fun ω => if Zrec t l ω = o then (1 : ℝ) else 0) = 0 ∧
        S.condExpect E (fun ω => f t (Zrec t l ω)) = 0) ∧
    (∃ (τ : ℕ → ℝ) (Led : ConcentrationLedger) (St : StopTimeoutLedger Ω),
      (∀ t < T, 0 < τ t) ∧
      0 ≤ Led.window ∧ 0 ≤ Led.failMass ∧ 0 ≤ Led.errorMass ∧
      (∀ t < T, τ t ≤ Led.window) ∧
      (∑ t ∈ Finset.range T, (τ t + εprog t) ≤ εtot) ∧
      (Led.errorMass = ∑ t ∈ Finset.range T, (τ t + εprog t)) ∧
      (∀ t < T,
        S.eventProb {ω : Ω |
          |(∑ l : Fin L, f t (Zrec t l ω)) / L -
            (Matrix.trace (M t * approx t)).re| ≥ τ t} ≤
          2 * Real.exp (-(2 : ℝ) * L * τ t ^ 2)) ∧
      (S.failProb {ω : Ω | ∀ t < T,
          |(∑ l : Fin L, f t (Zrec t l ω)) / L -
            (Matrix.trace (M t * approx t)).re| ≤ τ t} ≤
        ∑ t ∈ Finset.range T, 2 * Real.exp (-(2 : ℝ) * L * τ t ^ 2)) ∧
      (Led.failMass = ∑ t ∈ Finset.range T, 2 * Real.exp (-(2 : ℝ) * L * τ t ^ 2)) ∧
      (Led.failMass ≤ δtot) ∧
      (0 ≤ St.failMass) ∧
      (S.eventProb (St.stopped ∪ St.timedOut) ≤ St.failMass) ∧
      (St.failMass + Led.failMass ≤ δtot) ∧
      (∀ ω : Ω, (∀ t < T,
          |(∑ l : Fin L, f t (Zrec t l ω)) / L -
            (Matrix.trace (M t * approx t)).re| ≤ τ t) → ω ∉ (St.stopped ∪ St.timedOut) →
        ∀ σ : Operator D, IsDensityOperator σ →
          ((∑ t ∈ Finset.range T, (∑ l : Fin L, f t (Zrec t l ω)) / L) -
            ∑ t ∈ Finset.range T, (Matrix.trace (M t * σ)).re ≤
            η * T + Real.log D / η + ∑ t ∈ Finset.range T, (2 * ξ t + τ t))) ∧
      (∀ σ : Operator D, IsDensityOperator σ →
        ((∑ t ∈ Finset.range T,
            ∑ ω : Ω, S.prob ω * ((∑ l : Fin L, f t (Zrec t l ω)) / L)) -
          ∑ t ∈ Finset.range T, (Matrix.trace (M t * σ)).re ≤
          η * T + Real.log D / η + ∑ t ∈ Finset.range T, (2 * ξ t)))))    := by
  intro hall
  have hD : (0:ℕ) < 1 := by norm_num
  have hT : (0:ℕ) < 1 := by norm_num
  have hL : (0:ℕ) < 1 := by norm_num
  have hη : (0:ℝ) < 1 / 2 := by norm_num
  have hη1 : (1:ℝ) / 2 ≤ 1 := by norm_num
  have het : (0:ℝ) < 1 := by norm_num
  have hdt : (0:ℝ) < 1 := by norm_num
  have happ : ∀ t < 1, IsDensityOperator (approx0 t) := by
    intro t _
    show IsDensityOperator (1 : Operator 1)
    exact ⟨Matrix.PosSemidef.one, by simp⟩
  have hM : ∀ t < 1, M0 t = Qatlib.Concepts.SdpDuality.ConeSeparation.payoffObservable (Lam t) (f0 t) := by
    intro t _; rfl
  have hf : ∀ t < 1, ∀ o : Fin 2, 0 ≤ f0 t o ∧ f0 t o ≤ 1 := by
    intro t _ o
    fin_cases o <;> norm_num [f0]
  have hxi : ∀ t < 1, 0 ≤ xi0 t := by
    intro t _; show (0:ℝ) ≤ 0; exact le_rfl
  have hep : ∀ t < 1, 0 ≤ eprog0 t := by
    intro t _; show (0:ℝ) ≤ 0; exact le_rfl
  have hdist : ∀ t < 1,
      Qatlib.Concepts.MixedFidelity.FidelityMetric.traceDistance (approx0 t) (mmwState 1 M0 (1/2:ℝ) t) ≤ xi0 t := by
    intro t ht
    interval_cases t
    rw [mmwState_one_zero]
    show Qatlib.Concepts.MixedFidelity.FidelityMetric.traceDistance (1 : Operator 1)
        (1 : Operator 1) ≤ 0
    unfold Qatlib.Concepts.MixedFidelity.FidelityMetric.traceDistance
    rw [sub_self, Matrix.traceNorm_zero]
    norm_num
  have hprog : ∀ t < 1, (Rprog0 t).legal ∧
      (∃ qprog : Fin 2 → ℝ, (Rprog0 t).realizes qprog ∧
        (∑ o : Fin 2, |qprog o - bornLaw (Lam t) (approx0 t) o|) ≤ eprog0 t) := by
    intro t ht
    interval_cases t
    show (Rprog0 0).legal ∧ (∃ qprog : Fin 2 → ℝ, (Rprog0 0).realizes qprog ∧
        (∑ o : Fin 2, |qprog o - bornLaw (Lam 0) (1 : Operator 1) o|) ≤ 0)
    refine ⟨?_, fun _ => (1:ℝ) / 2, ?_, ?_⟩
    · show (∀ s ∈ ([] : List QuantumStep), s.legal = true) ∧
        (∀ p ∈ ([] : List PaidPrim), p.legal)
      simp
    · intro o
      fin_cases o <;> simp [Rprog0, SamplerTree.law]
    · have hb : ∀ o : Fin 2, |(1:ℝ) / 2 - bornLaw (Lam 0) (1 : Operator 1) o| = 0 := by
        intro o
        rw [bornLaw_half]
        norm_num
      simp only [hb, Finset.sum_const_zero]
      exact le_rfl
  have hjoint : ∀ ω : Fin 2, S2.prob ω =
      ∏ t ∈ Finset.range 1, ∏ l : Fin 1, bornLaw (Lam t) (approx0 t) (Zrec0 t l ω) := by
    intro ω
    rw [Finset.range_one, Finset.prod_singleton, Fin.prod_univ_one]
    show (1:ℝ) / 2 = bornLaw (Lam 0) (1 : Operator 1) 0
    exact (bornLaw_half 0).symm
  have hpast : ∀ t < 1, ∀ E : Set (Fin 2), E ∈ F0.events t → ∀ ω ω' : Fin 2,
      (∀ s < t, ∀ l : Fin 1, Zrec0 s l ω = Zrec0 s l ω') → (ω ∈ E ↔ ω' ∈ E) := by
    intro t _ E hE _ _ _
    rcases hE with h | h
    · rw [h]; simp
    · rw [h]; simp
  have hconj := hall 1 1 1 M0 approx0 (Fin 2) inferInstance inferInstance
    Lam f0 (Fin 2) inferInstance S2 F0 Zrec0 Rprog0 (1/2:ℝ) xi0 eprog0 1 1
    hD hT hL hη hη1 het hdt happ hM hf hxi hep hdist hprog hjoint hpast
  have h1 := hconj.1
  have h := h1 0 (by norm_num) Set.univ (Or.inr rfl)
    (by rw [S2_eventProb_univ]; norm_num) 0 0
  rw [show approx0 0 = (1 : Operator 1) from rfl] at h
  rw [condExpect_univ_one, bornLaw_half] at h
  norm_num at h
end Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G7
namespace Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8
open Filter Topology
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.SdpMmwSolver.OracleError
open Qatlib
/-- The sole scalar constraint matrix equal to minus the identity in the clause 8
counterexample. -/
noncomputable def A0 : Fin 1 → Operator 1 := fun _ => -(1 : Operator 1)
/-- The scalar identity objective matrix in the clause 8 counterexample. -/
noncomputable def Cv0 : Operator 1 := 1
/-- The constraint bound assigning value one to the sole scalar constraint. -/
noncomputable def b0 : Fin 1 → ℝ := fun _ => 1
/-- The identically zero history of constraint weights for the clause 8 counterexample. -/
noncomputable def yhist0 : ℕ → Fin 1 → ℝ := fun _ _ => 0

/-- The initial matrix multiplicative weights state for the clause 8 data, with target parameter
three and learning rate one half. -/
noncomputable def ρ8 : Operator 1 :=
  mmwState 1 (sdpDualPayoff 1 1 A0 Cv0 (3:ℝ) yhist0) (1/2:ℝ) 0

/-- The deterministic one-constraint search record with 300 grid points, one sample of each
kind, and exact constraint and objective measurements minus one and one. -/
noncomputable def S8 : Step2Search 1 1 300 1 1 1 where
  law := fun _ _ => 1
  draws := fun _ _ _ => 0
  measA := fun _ _ _ _ => -1
  measC := fun _ _ _ => 1
  idx := fun _ _ _ => 0

/-- The initial state `ρ8` equals the identity in dimension one. -/
theorem rho8_eq : ρ8 = (1 : Operator 1) := by
  have hwt : Qatlib.Concepts.MatrixWeights.WeightsCore.mmwWeight 1
      (sdpDualPayoff 1 1 A0 Cv0 (3:ℝ) yhist0) (1/2:ℝ) 0 = (1 : Operator 1) := by
    unfold Qatlib.Concepts.MatrixWeights.WeightsCore.mmwWeight
    rw [Finset.range_zero, Finset.sum_empty, smul_zero, NormedSpace.exp_zero]
  unfold ρ8 mmwState
  rw [hwt, Matrix.trace_fin_one]
  show (((1 : Operator 1) 0 0).re : ℂ)⁻¹ • (1 : Operator 1) = 1
  simp

/-- The real trace payoff of the sole constraint matrix against `ρ8` is minus one. -/
theorem trA (i : Fin 1) : (Matrix.trace (A0 i * ρ8)).re = (-1:ℝ) := by
  show (Matrix.trace (-(1 : Operator 1) * ρ8)).re = -1
  rw [rho8_eq, Matrix.mul_one]
  show (Matrix.trace (-(1 : Operator 1))).re = -1
  rw [Matrix.trace_neg, Matrix.trace_fin_one]
  simp

/-- The real trace payoff of the objective matrix against `ρ8` is one. -/
theorem trC : (Matrix.trace (Cv0 * ρ8)).re = (1:ℝ) := by
  rw [rho8_eq, Matrix.mul_one, Matrix.trace_fin_one]
  show ((1 : Operator 1) 0 0).re = 1
  simp

/-- For every grid point in `S8`, the sparsified scaled payoff equals the source scaled payoff
of the corresponding round vector exactly. -/
theorem scaled_eq (k : Fin 1) (N : Fin 300) :
    sdpScaledSparsifiedPayoff 1 1 1 A0 Cv0 (3:ℝ)
        (Step2Search.gridMass (1/100) N) (S8.idx k N)
      = sourceScaledPayoff A0 Cv0 (3:ℝ) (S8.roundVector (1/100) k N) := by
  unfold sdpScaledSparsifiedPayoff sourceScaledPayoff Step2Search.roundVector
  simp only [S8, Fin.sum_univ_one, Nat.cast_one, inv_one, one_smul, mul_one]

/-- The deterministic record `S8` satisfies its good-event inequalities for target three, grid
spacing `1 / 100`, radius one, and measurement tolerance `1 / 1000`. -/
theorem good_event :
    S8.goodEvent b0 A0 Cv0 ρ8 (3:ℝ) (1/100) (1:ℝ) (1/1000) := by
  intro k N
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [S8, b0, Fin.sum_univ_one]
  · norm_num [S8, b0, Step2Search.estA, Fin.sum_univ_one]
  · intro i
    rw [trA i]
    norm_num [S8, Fin.sum_univ_one]
  · rw [trC]
    norm_num [S8, Step2Search.estC, Fin.sum_univ_one]
  · rw [scaled_eq k N, sub_self, norm_zero]
    norm_num

/-- No grid point of `S8` is accepted for target three, radius one, grid spacing `1 / 100`, and
tolerance `1 / 1000`. -/
theorem no_output :
    S8.noOutput b0 (3:ℝ) (1:ℝ) (1/100) (1/1000) := by
  intro k N
  rintro ⟨ht1, _⟩
  have hC : S8.estC k N = (1:ℝ) := by
    norm_num [S8, Step2Search.estC, Fin.sum_univ_one]
  have hA : (∑ j : Fin 1, S8.estA k N j) = (-1:ℝ) := by
    norm_num [S8, Step2Search.estA, Fin.sum_univ_one]
  have hg : Step2Search.gridMass (1/100) N = (1/100) * (((N:ℕ):ℝ) + 1) := rfl
  rw [hC, hA, hg] at ht1
  have hg0 : (0:ℝ) < (1/100) * (((N:ℕ):ℝ) + 1) := by positivity
  have hpos : (0:ℝ) < 1 / ((1/100) * (((N:ℕ):ℝ) + 1)) := one_div_pos.mpr hg0
  push_cast at ht1
  linarith

/-- Refutes the stated universal search contract using a record with exact estimates, a good
event, and no output. A nonnegative weight of `1 / 4` meets `eq75Threshold` while its
objective lies below `noCheapWidth`, contradicting the required no-output conclusion. -/
theorem clause8_refuted : ¬
    (  ∀ (D m γ Nmax M L Q : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
      (b : Fin m → ℝ) (α R ε κ ν η δin : ℝ) (t : ℕ) (yhist : ℕ → Fin m → ℝ)
      (ρ : Operator D) (S : Step2Search m γ Nmax M L Q),
    0 < D → 0 < m → 0 < α → 0 < R → 0 < ε → 0 < κ → 0 < ν → 0 < η → 0 < δin →
    (3 * R * ε ≤ 1 / 2) → (κ + ν ≤ ε) →
    (Nmax = Nat.ceil (α / κ)) →
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
    (Cv.IsHermitian ∧ ‖Cv‖ ≤ 1) →
    (∀ i, 1 ≤ b i ∧ b i ≤ R) →
    S.lawsOk →
    (ρ = mmwState D (sdpDualPayoff D m A Cv α yhist) η t) →
    IsDensityOperator ρ →
    (∃ (Ω : Type) (_ : Fintype Ω) (SS : FiniteSupportSpace Ω)
        (rec : Ω → Step2Search m γ Nmax M L Q) (Led : GoodEventLedger Ω)
        (perFail : Fin (γ * Nmax * 3) → ℝ),
      (∀ ω : Ω, (rec ω).lawsOk) ∧
      (Led.good = {ω : Ω | (rec ω).goodEvent b A Cv ρ α κ R ν}) ∧
      (GoodEventLedger.legal SS Led) ∧
      (∀ i, 0 ≤ perFail i) ∧
      (Led.failBound = sumFailBound perFail) ∧
      (Led.failBound ≤ δin) ∧
      (SS.eventProb {ω : Ω |
          (rec ω).noOutput b α R κ ν ∧
            ¬ correctedNoCheapSeparator A Cv b ρ α R ε} ≤
        Led.failBound)) ∧
    ((S.goodEvent b A Cv ρ α κ R ν) →
      ∀ k : Fin γ, ∀ N : Fin Nmax, S.accepts b α R κ ν k N →
        (∀ i, 0 ≤ S.roundVector κ k N i) ∧
        (∑ i, b i * S.roundVector κ k N i ≤ sdpSampledWidthBudget α R κ ν) ∧
        (∑ i, b i * S.roundVector κ k N i ≤ sourceWidthBudget α R ε) ∧
        (sourcePayoffTarget D Cv ρ α (κ + ν) ≤
          ∑ i, S.roundVector κ k N i * (Matrix.trace (A i * ρ)).re) ∧
        (sourcePayoffTarget D Cv ρ α ε ≤
          ∑ i, S.roundVector κ k N i * (Matrix.trace (A i * ρ)).re)) ∧
    ((S.goodEvent b A Cv ρ α κ R ν) → S.noOutput b α R κ ν →
      (correctedNoCheapSeparator A Cv b ρ α R ε) ∧
      (∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
        (∑ i, z i * b i < noCheapWidth α R ε) →
        (∑ i, z i * (Matrix.trace (A i * ρ)).re < eq75Threshold Cv ρ α ε)) ∧
      (∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
        (eq75Threshold Cv ρ α ε ≤ ∑ i, z i * (Matrix.trace (A i * ρ)).re) →
        (noCheapWidth α R ε ≤ ∑ i, z i * b i)) ∧
      (∀ β : ℝ, β < noCheapWidth α R ε → ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
        (∑ i, z i * b i ≤ β) →
        (∑ i, z i * (Matrix.trace (A i * ρ)).re < eq75Threshold Cv ρ α ε))) ∧
    ((α ≤ κ * (Nmax : ℝ)) ∧ (κ * (Nmax : ℝ) < α + κ) ∧
      (∀ N : ℕ, N < Nmax → Step2Search.gridMass κ N ≤ α + κ) ∧
      (∀ y : Fin m → ℝ, (∀ i, 0 ≤ y i) →
        (∑ i, b i * y i ≤ noCheapWidth α R ε) →
        ∃ N : ℕ, N < Nmax ∧
          |(∑ i, y i) - Step2Search.gridMass κ N| ≤ κ ∧ Step2Search.gridMass κ N ≤ α + κ)) ∧
    ((0 < noCheapWidth α R ε) ∧ (noCheapWidth α R ε < α) ∧
      (α ≤ sourceWidthBudget α R ε) ∧
      (sdpSampledWidthBudget α R κ ν = sourceWidthBudget α R (κ + ν)) ∧
      (sdpSampledSeparationSlack α κ ν = 2 * α * (κ + ν)) ∧
      (sdpSampledWidthBudget α R κ ν ≤ sourceWidthBudget α R ε) ∧
      (sdpSampledSeparationSlack α κ ν ≤ 2 * α * ε) ∧
      (eq75Threshold Cv ρ α ε = (Matrix.trace (Cv * ρ)).re - 3 * α * ε) ∧
      (noCheapWidth α R ε = α * (1 - 3 * R * ε))))    := by
  intro hall
  have hD : (0:ℕ) < 1 := by norm_num
  have hm : (0:ℕ) < 1 := by norm_num
  have hα : (0:ℝ) < 3 := by norm_num
  have hR : (0:ℝ) < 1 := by norm_num
  have hε : (0:ℝ) < 1/6 := by norm_num
  have hκ : (0:ℝ) < 1/100 := by norm_num
  have hν : (0:ℝ) < 1/1000 := by norm_num
  have hη : (0:ℝ) < 1/2 := by norm_num
  have hδ : (0:ℝ) < 1/10 := by norm_num
  have h3Re : 3 * (1:ℝ) * (1/6) ≤ 1 / 2 := by norm_num
  have hκν : (1:ℝ)/100 + 1/1000 ≤ 1/6 := by norm_num
  have hNmax : (300:ℕ) = Nat.ceil ((3:ℝ) / (1/100)) := by norm_num
  have hA : ∀ i : Fin 1, (A0 i).IsHermitian ∧ ‖A0 i‖ ≤ 1 := by
    intro i
    refine ⟨?_, ?_⟩
    · show (-(1 : Operator 1)).IsHermitian
      exact Matrix.isHermitian_one.neg
    · rw [show A0 i = -(1 : Operator 1) from rfl, norm_neg]
      exact le_of_eq norm_one
  have hCv : Cv0.IsHermitian ∧ ‖Cv0‖ ≤ 1 :=
    ⟨Matrix.isHermitian_one, le_of_eq norm_one⟩
  have hb : ∀ i : Fin 1, 1 ≤ b0 i ∧ b0 i ≤ (1:ℝ) := by
    intro i
    show 1 ≤ (1:ℝ) ∧ (1:ℝ) ≤ 1
    exact ⟨le_rfl, le_rfl⟩
  have hlaws : S8.lawsOk := by
    intro k
    refine ⟨?_, ?_⟩
    · intro i; show (0:ℝ) ≤ (1:ℝ); norm_num
    · rw [Fin.sum_univ_one]; show (1:ℝ) = 1; norm_num
  have hρeq : ρ8 = mmwState 1 (sdpDualPayoff 1 1 A0 Cv0 (3:ℝ) yhist0) (1/2:ℝ) 0 := rfl
  have hρdens : IsDensityOperator ρ8 := by
    rw [rho8_eq]
    exact ⟨Matrix.PosSemidef.one, by simp⟩
  have hconj := hall 1 1 1 300 1 1 1 A0 Cv0 b0 (3:ℝ) (1:ℝ) (1/6) (1/100) (1/1000)
    (1/2:ℝ) (1/10:ℝ) 0 yhist0 ρ8 S8
    hD hm hα hR hε hκ hν hη hδ h3Re hκν hNmax hA hCv hb hlaws hρeq hρdens
  have h3 := hconj.2.2.1
  have hcorr := (h3 good_event no_output).1
  have hp : eq75Threshold Cv0 ρ8 (3:ℝ) (1/6) ≤
      (∑ i : Fin 1, ((1:ℝ)/4) * (Matrix.trace (A0 i * ρ8)).re) := by
    unfold eq75Threshold
    rw [trC, Fin.sum_univ_one, trA 0]
    norm_num
  have habs := hcorr (fun _ => (1:ℝ)/4) (fun i => by norm_num) hp
  rw [Fin.sum_univ_one] at habs
  exact habs (by
    norm_num [b0, noCheapWidth])
end Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8
namespace Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G9
open Filter Topology
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.SdpMmwSolver.OracleError
open Qatlib

/-- Every outcome mass of a finite sampler tree built from emission, failure, and fair-bit
branching is dyadic. -/
theorem samplerTree_law_dyadic {n : ℕ} (t : SamplerTree (Fin n)) (i : Fin n) :
    IsDyadic (t.law i) := by
  induction t with
  | emit o =>
    show IsDyadic (if i = o then (1:ℝ) else 0)
    by_cases h : i = o
    · rw [if_pos h]; exact ⟨1, 0, by norm_num⟩
    · rw [if_neg h]; exact ⟨0, 0, by norm_num⟩
  | fail =>
    show IsDyadic (0:ℝ)
    exact ⟨0, 0, by norm_num⟩
  | bit l r ihl ihr =>
    obtain ⟨z1, k1, h1⟩ := ihl
    obtain ⟨z2, k2, h2⟩ := ihr
    refine ⟨z1 * (2:ℤ) ^ k2 + z2 * (2:ℤ) ^ k1, k1 + k2 + 1, ?_⟩
    show (SamplerTree.law l i + SamplerTree.law r i) / 2 = _
    rw [h1, h2]
    have hp1 : (0:ℝ) < (2:ℝ) ^ k1 := pow_pos (by norm_num) k1
    have hp2 : (0:ℝ) < (2:ℝ) ^ k2 := pow_pos (by norm_num) k2
    push_cast
    field_simp [ne_of_gt hp1, ne_of_gt hp2]
    ring

/-- The real number one third has no representation as an integer divided by a natural power of
two. -/
theorem not_isDyadic_one_div_three : ¬ IsDyadic ((1:ℝ) / 3) := by
  rintro ⟨z, k, h⟩
  have hpow : (0:ℝ) < (2:ℝ) ^ k := pow_pos (by norm_num) k
  have h2 : (2:ℝ) ^ k = 3 * (z:ℝ) := by
    have h1 : ((1:ℝ) / 3) * 3 * (2:ℝ) ^ k = ((z:ℝ) / (2:ℝ) ^ k) * 3 * (2:ℝ) ^ k := by
      rw [h]
    have A : ((1:ℝ) / 3) * 3 * (2:ℝ) ^ k = (2:ℝ) ^ k := by field_simp
    have B : ((z:ℝ) / (2:ℝ) ^ k) * 3 * (2:ℝ) ^ k = 3 * (z:ℝ) := by
      field_simp [ne_of_gt hpow]
    rw [A, B] at h1
    exact h1
  have h4 : ((2 ^ k : ℕ) : ℤ) = 3 * z := by exact_mod_cast h2
  have h5 : (3:ℕ) ∣ 2 ^ k := by
    have : (3:ℤ) ∣ ((2 ^ k : ℕ) : ℤ) := ⟨z, h4⟩
    exact_mod_cast this
  have h6 : (3:ℕ) ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h5
  norm_num at h6

/-- The single-round distribution on two outcomes with masses one third and two thirds. -/
noncomputable def q0 : Fin 1 → Fin 2 → ℝ := fun _ i => if i = 0 then (1:ℝ) / 3 else (2:ℝ) / 3
/-- The grid-count function assigning one to the only round of the clause 9 counterexample. -/
def Nt0 : Fin 1 → ℕ := fun _ => 1
/-- The mixture mass function assigning one to the only round of the clause 9 counterexample. -/
noncomputable def mu0 : Fin 1 → ℝ := fun _ => 1
/-- The identically zero component-law error allowance for the clause 9 counterexample. -/
noncomputable def nus0 : Fin 1 → ℝ := fun _ => 0

/-- Each round distribution specified by `q0` is nonnegative and sums to one. -/
theorem q0_law : ∀ t : Fin 1, (∀ i : Fin 2, 0 ≤ q0 t i) ∧ (∑ i : Fin 2, q0 t i) = 1 := by
  intro t
  constructor
  · intro i
    fin_cases i <;> norm_num [q0]
  · rw [Fin.sum_univ_two]
    have h0 : q0 t (0:Fin 2) = (1:ℝ)/3 := by simp [q0]
    have h1 : q0 t (1:Fin 2) = (2:ℝ)/3 := by simp [q0]
    rw [h0, h1]
    norm_num

/-- Mixing the distinguished outcome zero with the single `q0` component, each with mass one
before normalization, gives outcome one probability one third. -/
theorem dualMixtureLaw_q0_one : dualMixtureLaw (0:Fin 2) (1:ℝ) mu0 q0 1 = (1:ℝ) / 3 := by
  have hif : ¬ ((1:Fin 2) = (0:Fin 2)) := by decide
  have hsum1 : (∑ t : Fin 1, mu0 t * q0 t 1) = (2:ℝ) / 3 := by
    rw [Fin.sum_univ_one]
    simp only [mu0, q0]
    rw [if_neg hif]
    norm_num
  have hsum0 : (∑ t : Fin 1, mu0 t) = (1:ℝ) := by
    rw [Fin.sum_univ_one]
    show (1:ℝ) = 1
    norm_num
  unfold dualMixtureLaw dualMixtureScale
  simp only [Fin.sum_univ_one]
  simp only [mu0, q0]
  rw [if_neg hif, if_neg hif]
  norm_num

/-- Refutes the stated universal mixture-sampling contract through its demand for an exact
finite receipt for an unrestricted approximate component law. Choosing zero component error
forces an output mass of one third, which no finite fair-bit sampler tree can realize. -/
theorem clause9_refuted : ¬
    (  ∀ (m T : ℕ) (q : Fin T → Fin m → ℝ) (Nt : Fin T → ℕ) (μ : Fin T → ℝ)
      (a δ α R ε : ℝ) (j₀ : Fin m) (νs : Fin T → ℝ),
    0 < m → 0 < T → 0 < δ → 0 < α → 0 < R → 0 < ε →
    (a = δ * α / (2 * R)) → 0 < a →
    (∀ t : Fin T, μ t = ε * (Nt t : ℝ)) →
    (∀ t : Fin T, 0 ≤ μ t) →
    (∀ t : Fin T, 0 ≤ νs t) →
    (∀ t : Fin T, (∀ i, 0 ≤ q t i) ∧ (∑ i : Fin m, q t i) = 1) →
    ((0 < dualMixtureScale a μ) ∧
      (∀ i : Fin m,
        dualMixtureVector j₀ a μ q i =
          dualMixtureScale a μ * dualMixtureLaw j₀ a μ q i) ∧
      (IsWeighting (dualMixtureWeights a μ)) ∧
      (dualMixtureLaw j₀ a μ q = mixtureLaw (dualMixtureWeights a μ)
        (fun k : Fin (T + 1) =>
          Fin.cases (fun i => if i = j₀ then (1 : ℝ) else 0) q k))) ∧
    ((weightsDyadic (dualMixtureWeights a μ) ∧
        (∀ t : Fin T, ∀ i : Fin m, IsDyadic (q t i))) →
      ∃ (choose : SamplerTree (Fin (T + 1)))
          (Rsampler : Fin T → MixedReceipt (Fin m))
          (R : MixedReceipt (Fin m)),
        (treeRealizes (dualMixtureWeights a μ) choose) ∧
        (∀ t : Fin T, (Rsampler t).legal ∧ treeRealizes (q t) (Rsampler t).out) ∧
        R.legal ∧
        (R.out = SamplerTree.bind choose
          (Fin.cases (SamplerTree.emit j₀) (fun t : Fin T => (Rsampler t).out))) ∧
        (R.realizes (dualMixtureLaw j₀ a μ q)) ∧
        (R.cost.queries ≤ Finset.univ.sup fun t : Fin T => (Rsampler t).cost.queries) ∧
        (R.cost.gates ≤ Finset.univ.sup fun t : Fin T => (Rsampler t).cost.gates) ∧
        (R.cost.bitTime ≤ choose.maxDepth +
          Finset.univ.sup fun t : Fin T => (Rsampler t).cost.bitTime) ∧
        (R.cost.peakSpace ≤
          max (Finset.univ.sup fun t : Fin T => (Rsampler t).cost.peakSpace)
            (choose.maxDepth + 1))) ∧
    (((∀ t : Fin T, ∀ i : Fin m, ∃ qt : ℚ, (qt : ℝ) = q t i) ∧
        (∀ k : Fin (T + 1), ∃ wk : ℚ, (wk : ℝ) = dualMixtureWeights a μ k)) →
      (∃ (S : RejectReceipt (Fin m)) (choose : SamplerTree (Fin (T + 1)))
          (Rsampler : Fin T → MixedReceipt (Fin m)),
        S.target = dualMixtureLaw j₀ a μ q ∧ S.exactLaw ∧ S.aSFinite ∧
        S.trial.rejectProb < 1 ∧
        (S.expectedBitTime ≤
          (Finset.univ.sup fun t : Fin T => (Rsampler t).cost.bitTime) +
            choose.maxDepth + 1) ∧
        (∀ k, S.tailMass k ≤ S.trial.rejectProb ^ k) ∧
        (0 < S.trial.rejectProb → ¬ S.hasWorstCaseTimeBound) ∧
        (∀ t : Fin T, (Rsampler t).legal ∧ treeRealizes (q t) (Rsampler t).out) ∧
        (S.trial.tree.maxDepth ≤ choose.maxDepth +
          Finset.univ.sup fun t : Fin T => (Rsampler t).cost.bitTime))
      ∨
      (∃ (Tr : TruncatedReject (Fin m)) (choose : SamplerTree (Fin (T + 1)))
          (Rsampler : Fin T → MixedReceipt (Fin m)),
        Tr.timeoutMass ≤ δ ∧
        (∑ i : Fin m, |Tr.law i - dualMixtureLaw j₀ a μ q i|) ≤ ε ∧
        (Tr.trial.tree.maxDepth ≤ choose.maxDepth +
          Finset.univ.sup fun t : Fin T => (Rsampler t).cost.bitTime) ∧
        (Tr.worstCaseBitTime = Tr.cutoff * Tr.trial.tree.maxDepth) ∧
        (∀ t : Fin T, (Rsampler t).legal ∧ treeRealizes (q t) (Rsampler t).out))) ∧
    (∀ qtil : Fin T → Fin m → ℝ,
      (∀ t : Fin T, (∀ i, 0 ≤ qtil t i) ∧ (∑ i : Fin m, qtil t i) = 1) →
      (∀ t : Fin T, ∑ i : Fin m, |qtil t i - q t i| ≤ νs t) →
      ∃ Rapprox : MixedReceipt (Fin m),
        Rapprox.legal ∧ Rapprox.realizes (dualMixtureLaw j₀ a μ qtil) ∧
        (∑ i : Fin m,
          |dualMixtureLaw j₀ a μ qtil i - dualMixtureLaw j₀ a μ q i| ≤
          ∑ t : Fin T, (μ t / (T * dualMixtureScale a μ)) * νs t)))    := by
  intro hall
  have hm : (0:ℕ) < 2 := by norm_num
  have hT : (0:ℕ) < 1 := by norm_num
  have hd : (0:ℝ) < 1 := by norm_num
  have hal : (0:ℝ) < 2 := by norm_num
  have hR : (0:ℝ) < 1 := by norm_num
  have heps : (0:ℝ) < 1 := by norm_num
  have ha : (1:ℝ) = 1 * 2 / (2 * 1) := by norm_num
  have ha0 : (0:ℝ) < 1 := by norm_num
  have hmueq : ∀ t : Fin 1, mu0 t = (1:ℝ) * ((Nt0 t : ℕ) : ℝ) := by
    intro t
    simp [mu0, Nt0]
  have hmun : ∀ t : Fin 1, 0 ≤ mu0 t := by
    intro t; show (0:ℝ) ≤ (1:ℝ); norm_num
  have hnus : ∀ t : Fin 1, 0 ≤ nus0 t := by
    intro t; show (0:ℝ) ≤ (0:ℝ); exact le_rfl
  have hres := hall 2 1 q0 Nt0 mu0 (1:ℝ) 1 2 1 1 0 nus0
  have hconj := hres hm hT hd hal hR heps ha ha0 hmueq hmun hnus q0_law
  have h4 := hconj.2.2.2
  have hcl : ∀ t : Fin 1, ∑ i : Fin 2, |q0 t i - q0 t i| ≤ nus0 t := by
    intro t
    show (∑ i : Fin 2, |q0 t i - q0 t i|) ≤ (0:ℝ)
    have hz : ∀ i : Fin 2, |q0 t i - q0 t i| = 0 := by
      intro i; rw [sub_self, abs_zero]
    simp only [hz, Finset.sum_const_zero]
    exact le_rfl
  obtain ⟨Rapprox, _, hreal, _⟩ := h4 q0 q0_law hcl
  have hd1 := samplerTree_law_dyadic Rapprox.out 1
  have hbad : IsDyadic ((1:ℝ) / 3) := by
    rw [← dualMixtureLaw_q0_one]
    rw [← hreal 1]
    exact hd1
  exact not_isDyadic_one_div_three hbad
end Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G9

#print axioms Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.clause6_refuted
#print axioms Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G7.clause7_refuted
#print axioms Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8.clause8_refuted
#print axioms Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G9.clause9_refuted
