/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.PreparedRepeat
import Qatlib.Papers.CrouzeixLS26.AccessLower.ConstructorReadout
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.BasisFrame
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.ConstructorPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.FrameTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.SlackPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.TranslatedPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.AnswerTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.TruncatedPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.ExpectedCost
import Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.MarkedColumns
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.BudgetTruncation
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.InputHybrid
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.OutputReadout
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.Program
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.SourceWordTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript
import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRange
import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRangeConvex

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
/-! Literal block-output guarantees feed the actual same-word Born samples,
constructor-path law and repeated reconstruction/majority execution. One fixed
classifier uses only known record frames and samples; hidden truth and target
matrices occur solely in guarantees. Bad constructor paths remain in every law.
The sample budget and all-path input/support costs belong to that same program.

This is the fixed finite-program, known coordinate-frame model. It does not
supply arbitrary original-algorithm normal forms, variable-width/frame padding,
expected-budget truncation, free M, coherent support access, or full primitive
costs. The old AE readout is preserved and its separate compiler is not proved
by this sampling backend. No original G1–G4 completion follows. -/

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport Qatlib.Foundations.OpCalculus.ContourCalc
namespace Qatlib.Papers.CrouzeixLS26.AccessLower.BlockSampling
open Qatlib ConstructorReadout Matrix Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
open scoped BigOperators Classical ComplexOrder

/-- The restricted-access construction satisfies `indicator_variance` under the complete displayed premises. -/
private theorem indicator_variance {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (C : X → Prop) [DecidablePred C] :
    p.variance (indicator C) ≤ 1/4 := by
  let μ := p.expect (indicator C)
  have hpoint (x : X) : p.prob x*(indicator C x-μ)^2=
      p.prob x*indicator C x-2*μ*(p.prob x*indicator C x)+μ^2*p.prob x := by
    dsimp [indicator]; split_ifs <;> ring
  have hv : p.variance (indicator C)=μ-μ^2 := by
    change (∑ x,p.prob x*(indicator C x-μ)^2)=_
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,p.sum_one]
    change μ-2*μ*μ+μ^2*1=μ-μ^2
    ring
  rw [hv]
  nlinarith [sq_nonneg (μ-1/2)]

/-- The restricted-access construction satisfies `indicator_sampling_tail` under the complete displayed premises. -/
theorem indicator_sampling_tail {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (C : X → Prop) [DecidablePred C]
    (τ : ℝ) (hτ : 0<τ) (n : ℕ) (hn : 0<n) (hbudget : 16/τ^2 ≤ (n : ℝ)) :
    p.probEvent (L := n) (fun ω => τ/3 < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (indicator C) ω-p.expect (indicator C)|) ≤ 9/64 := by
  have hnr : (0 : ℝ)<n := by exact_mod_cast hn
  have hden : 0<(n : ℝ)*(τ/3)^2 := by positivity
  have hnt : (16 : ℝ) ≤ (n : ℝ)*τ^2 := (div_le_iff₀ (sq_pos_of_pos hτ)).mp hbudget
  have hh := p.chebyshev_avg (indicator C) hn (τ/3) (by positivity)
  have hv := indicator_variance p C
  have hq : (1/4 : ℝ)/((n : ℝ)*(τ/3)^2) ≤ 9/64 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact hh.trans ((div_le_div_of_nonneg_right hv hden.le).trans hq)

/-- The restricted-access construction satisfies `baseline_samples_separated` under the complete displayed premises. -/
theorem baseline_samples_separated (τ μ x : ℝ) (hτ : 0<τ) (hτ1 : τ ≤ 1/4)
    (hμ : |μ-Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.baseProbability| ≤ 3*(τ/100)) (hx : |x-μ| ≤ τ/3) :
    Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.threshold τ<x := by
  have hg := Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.target_probability_gap τ hτ hτ1
  have hm := (abs_le.mp hμ).1
  have hl := (abs_le.mp hx).1
  dsimp [Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.threshold]
  linarith

/-- The restricted-access construction satisfies `hidden_samples_separated` under the complete displayed premises. -/
theorem hidden_samples_separated (τ μ x : ℝ) (hτ : 0<τ) (hτ1 : τ ≤ 1/4)
    (hμ : |μ-Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.hiddenProbability τ| ≤ 3*(τ/100)) (hx : |x-μ| ≤ τ/3) :
    x<Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.threshold τ := by
  have hg := Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.target_probability_gap τ hτ hτ1
  have hm := (abs_le.mp hμ).2
  have hu := (abs_le.mp hx).2
  dsimp [Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.threshold]
  linarith

/-- Construction for sample Vote in the block sampling readout model. -/
def sampleVote {X : Type} [Fintype X] (τ : ℝ) (C : X → Prop) [DecidablePred C]
    {n : ℕ} (ω : Fin n → X) : Bool := decide (Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.threshold τ<Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (indicator C) ω)

/-- The restricted-access construction satisfies `baseline_sampling_error` under the complete displayed premises. -/
theorem baseline_sampling_error {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (C : X → Prop) [DecidablePred C]
    (τ : ℝ) (hτ : 0<τ) (hτ1 : τ ≤ 1/4) (n : ℕ) (hn : 0<n)
    (hbudget : 16/τ^2 ≤ (n : ℝ))
    (hmean : |p.expect (indicator C)-Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.baseProbability| ≤ 3*(τ/100)) :
    p.probEvent (L := n) (fun ω => sampleVote τ C ω=false) ≤ 9/64 := by
  have hsub : (Finset.univ.filter (fun ω : Fin n → X => sampleVote τ C ω=false)) ⊆
      Finset.univ.filter (fun ω => τ/3 < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (indicator C) ω-p.expect (indicator C)|) := by
    intro ω hω
    have hv : ¬Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.threshold τ<Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (indicator C) ω := by
      simpa only [sampleVote,decide_eq_false_iff_not] using (Finset.mem_filter.mp hω).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    by_contra hh
    exact hv (baseline_samples_separated τ _ _ hτ hτ1 hmean (le_of_not_gt hh))
  have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := fun ω : Fin n → X => p.probOf ω) hsub
    (fun ω _ _ => Finset.prod_nonneg (fun i _ => p.nonneg (ω i)))
  exact hs.trans (indicator_sampling_tail p C τ hτ n hn hbudget)

/-- The restricted-access construction satisfies `hidden_sampling_error` under the complete displayed premises. -/
theorem hidden_sampling_error {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (C : X → Prop) [DecidablePred C]
    (τ : ℝ) (hτ : 0<τ) (hτ1 : τ ≤ 1/4) (n : ℕ) (hn : 0<n)
    (hbudget : 16/τ^2 ≤ (n : ℝ))
    (hmean : |p.expect (indicator C)-Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.hiddenProbability τ| ≤ 3*(τ/100)) :
    p.probEvent (L := n) (fun ω => sampleVote τ C ω=true) ≤ 9/64 := by
  have hsub : (Finset.univ.filter (fun ω : Fin n → X => sampleVote τ C ω=true)) ⊆
      Finset.univ.filter (fun ω => τ/3 < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (indicator C) ω-p.expect (indicator C)|) := by
    intro ω hω
    have hv : Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.threshold τ<Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (indicator C) ω := by
      simpa only [sampleVote,decide_eq_true_eq] using (Finset.mem_filter.mp hω).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    by_contra hh
    exact (not_lt_of_gt (hidden_samples_separated τ _ _ hτ hτ1 hmean (le_of_not_gt hh))) hv
  have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := fun ω : Fin n → X => p.probOf ω) hsub
    (fun ω _ _ => Finset.prod_nonneg (fun i _ => p.nonneg (ω i)))
  exact hs.trans (indicator_sampling_tail p C τ hτ n hn hbudget)

/-- The restricted-access construction satisfies `sampleLaw_indicator` under the complete displayed premises. -/
theorem sampleLaw_indicator {D : ℕ} (O : Bool → Operator D)
    (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (r b : Fin D)
    (gs : List (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.OutputGate D)) :
    (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.sampleLaw O hO r gs).expect (indicator (fun x => x=b))=
      Complex.normSq (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.wordMatrix O gs b r) := by
  simp [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect,indicator,Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.sampleLaw,mul_ite]

/-- The restricted-access construction satisfies `block_sample_mean` under the complete displayed premises. -/
theorem block_sample_mean {D : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ)
    (φ : I → Fin D) (gs : List (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.OutputGate D))
    (T : Matrix I I ℂ) (i j : I) (a ε : ℝ)
    (hb : BlockEncoding T (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.wordMatrix O gs) (basisFrame φ) (basisFrame φ) 1 ε)
    (hentry : T i j=(a : ℂ)) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hε1 : ε ≤ 1) :
    |(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.sampleLaw O hO (φ j) gs).expect (indicator (fun x => x=φ i))-a^2| ≤ 3*ε := by
  rw [sampleLaw_indicator,Complex.normSq_eq_norm_sq]
  have hh := Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.block_entry_probability T (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.wordMatrix O gs)
    (basisFrame φ) i j a ε hb hentry ha ha1 hε1
  rwa [basisFrame_compress] at hh

/-- The restricted-access construction satisfies `baseline_block_sampling_error` under the complete displayed premises. -/
theorem baseline_block_sampling_error {D : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ)
    (φ : I → Fin D) (gs : List (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.OutputGate D))
    (T : Matrix I I ℂ) (i j : I) (τ : ℝ) (hτ : 0<τ) (hτ1 : τ ≤ 1/4)
    (n : ℕ) (hn : 0<n) (hbudget : 16/τ^2 ≤ (n : ℝ))
    (hb : BlockEncoding T (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.wordMatrix O gs) (basisFrame φ) (basisFrame φ) 1 (τ/100))
    (hentry : T i j=(4/5 : ℂ)) :
    (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.sampleLaw O hO (φ j) gs).probEvent (L := n)
      (fun ω => sampleVote τ (fun x => x=φ i) ω=false) ≤ 9/64 := by
  apply baseline_sampling_error _ _ τ hτ hτ1 n hn hbudget
  have hh := block_sample_mean O hO φ gs T i j (4/5) (τ/100) hb (by simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using hentry)
    (by norm_num) (by norm_num) (by linarith)
  norm_num [Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.baseProbability] at hh ⊢
  exact hh

/-- The restricted-access construction satisfies `hidden_block_sampling_error` under the complete displayed premises. -/
theorem hidden_block_sampling_error {D : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ)
    (φ : I → Fin D) (gs : List (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.OutputGate D))
    (T : Matrix I I ℂ) (i j : I) (τ : ℝ) (hτ : 0<τ) (hτ1 : τ ≤ 1/4)
    (n : ℕ) (hn : 0<n) (hbudget : 16/τ^2 ≤ (n : ℝ))
    (hb : BlockEncoding T (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.wordMatrix O gs) (basisFrame φ) (basisFrame φ) 1 (τ/100))
    (hentry : T i j=(((4/(5*(1+2*τ)) : ℝ)) : ℂ)) :
    (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.sampleLaw O hO (φ j) gs).probEvent (L := n)
      (fun ω => sampleVote τ (fun x => x=φ i) ω=true) ≤ 9/64 := by
  have hd : 0<1+2*τ := by linarith
  have ha : (4/(5*(1+2*τ)) : ℝ) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<5*(1+2*τ))).mpr
    linarith
  apply hidden_sampling_error _ _ τ hτ hτ1 n hn hbudget
  have hh := block_sample_mean O hO φ gs T i j (4/(5*(1+2*τ))) (τ/100) hb hentry
    (by positivity) ha (by linarith)
  have he : (4/(5*(1+2*τ)))^2=Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.hiddenProbability τ := by
    dsimp [Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.hiddenProbability]
    field_simp
    ring
  rwa [he] at hh

/-- Construction for tuple Law in the block sampling readout model. -/
def tupleLaw {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X) (n : ℕ) :
    FinDist (Fin n → X) where
  prob := p.probOf
  nonneg ω := Finset.prod_nonneg (fun i _ => p.nonneg (ω i))
  sum_one := p.sum_probOf n

/-- The restricted-access construction satisfies `sampleVote_partition` under the complete displayed premises. -/
theorem sampleVote_partition {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (τ : ℝ) (C : X → Prop) [DecidablePred C] (n : ℕ) :
    p.probEvent (L := n) (fun ω => sampleVote τ C ω=true)+
      p.probEvent (L := n) (fun ω => sampleVote τ C ω=false)=1 := by
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
  rw [Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib]
  calc
    _ = ∑ ω : Fin n → X,p.probOf ω := by
      apply Finset.sum_congr rfl
      intro ω _
      cases sampleVote τ C ω <;> simp
    _ = 1 := p.sum_probOf n

/-- The restricted-access construction satisfies `constructor_repeat_expect` under the complete displayed premises. -/
theorem constructor_repeat_expect {D R : ℕ} (O : Bool → Operator D)
    (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (P : Program D R) (words : Path P → List (OutputGate D)) (r : Path P → Fin D)
    (n : ℕ) (ρ : Operator D) (hρ : ρ.PosSemidef) (ht : (Matrix.trace ρ).re=1)
    (E : Path P × (Fin n → Fin D) → Prop) [DecidablePred E] :
    (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S
      (bind P (fun p => repeatReadout R (r p) (words p) n)) ρ hρ ht).expect
        (indicator (fun q => E ((constructorReadoutEquiv P words r n).symm q)))=
      (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw
        (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S P ρ hρ ht)
        (fun p => tupleLaw (sampleLaw O hO (r p) (words p)) n)).expect (indicator E) := by
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
  have he := (constructorReadoutEquiv P words r n).sum_comp (fun q =>
    (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S
      (bind P (fun p => repeatReadout R (r p) (words p) n)) ρ hρ ht).prob q*
        indicator (fun q => E ((constructorReadoutEquiv P words r n).symm q)) q)
  rw [←he]
  apply Finset.sum_congr rfl
  intro pq _
  rcases pq with ⟨p,ω⟩
  rw [constructor_repeat_law]
  by_cases h : E (p,ω) <;> simp [indicator,Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw,tupleLaw,h]

/-- Construction for output Vote in the block sampling readout model. -/
def outputVote {D R : ℕ} {I : Type} (τ : ℝ) (P : Program D R)
    (words : Path P → List (OutputGate D)) (φ : Path P → I → Fin D) (i j : I) (n : ℕ)
    (q : Path (bind P (fun p => repeatReadout R (φ p j) (words p) n))) : Bool :=
  let pq := (constructorReadoutEquiv P words (fun p => φ p j) n).symm q
  sampleVote τ (fun b => b=φ pq.1 i) pq.2

/-- The restricted-access construction satisfies `constructor_vote_success` under the complete displayed premises. -/
theorem constructor_vote_success {D R : ℕ} {I : Type}
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (P : Program D R) (words : Path P → List (OutputGate D)) (φ : Path P → I → Fin D)
    (i j : I) (τ : ℝ) (n : ℕ) (truth : Bool)
    (ρ : Operator D) (hρ : ρ.PosSemidef) (ht : (Matrix.trace ρ).re=1)
    (G : Finset (Path P))
    (hG : 2/3 ≤ ∑ p∈G,(pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S P ρ hρ ht).prob p)
    (hgood : ∀ p∈G,4/5 ≤ (sampleLaw O hO (φ p j) (words p)).probEvent (L := n)
      (fun ω => sampleVote τ (fun b => b=φ p i) ω=truth)) :
    8/15 ≤ (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S
      (bind P (fun p => repeatReadout R (φ p j) (words p) n)) ρ hρ ht).expect
        (indicator (fun q => outputVote τ P words φ i j n q=truth)) := by
  let E : Path P × (Fin n → Fin D) → Prop := fun pq => sampleVote τ (fun b => b=φ pq.1 i) pq.2=truth
  change 8/15 ≤ (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S
    (bind P (fun p => repeatReadout R (φ p j) (words p) n)) ρ hρ ht).expect
      (indicator (fun q => E ((constructorReadoutEquiv P words (fun p => φ p j) n).symm q)))
  rw [constructor_repeat_expect O hO S P words (fun p => φ p j) n ρ hρ ht E]
  have hh := joint_success
    (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S P ρ hρ ht)
    (fun p => tupleLaw (sampleLaw O hO (φ p j) (words p)) n) E G (4/5) (2/3)
    (by norm_num) hG (by
      intro p hp
      simpa only [E,tupleLaw,Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent] using hgood p hp)
  norm_num at hh ⊢
  exact hh

/-- The restricted-access construction satisfies `baseline_constructor_success` under the complete displayed premises. -/
theorem baseline_constructor_success {D R : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (P : Program D R) (words : Path P → List (OutputGate D)) (φ : Path P → I → Fin D)
    (T : Matrix I I ℂ) (i j : I) (τ : ℝ) (hτ : 0<τ) (hτ1 : τ ≤ 1/4)
    (n : ℕ) (hn : 0<n) (hbudget : 16/τ^2 ≤ (n : ℝ))
    (ρ : Operator D) (hρ : ρ.PosSemidef) (ht : (Matrix.trace ρ).re=1)
    (G : Finset (Path P))
    (hG : 2/3 ≤ ∑ p∈G,(pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S P ρ hρ ht).prob p)
    (hgood : ∀ p∈G,BlockEncoding T (wordMatrix O (words p))
      (basisFrame (φ p)) (basisFrame (φ p)) 1 (τ/100))
    (hentry : T i j=(4/5 : ℂ)) :
    8/15 ≤ (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S
      (bind P (fun p => repeatReadout R (φ p j) (words p) n)) ρ hρ ht).expect
        (indicator (fun q => outputVote τ P words φ i j n q=true)) := by
  apply constructor_vote_success O hO S P words φ i j τ n true ρ hρ ht G hG
  intro p hp
  have hb := baseline_block_sampling_error O hO (φ p) (words p) T i j τ hτ hτ1 n hn hbudget (hgood p hp) hentry
  have hs := sampleVote_partition (sampleLaw O hO (φ p j) (words p)) τ (fun b => b=φ p i) n
  linarith

/-- The restricted-access construction satisfies `hidden_constructor_success` under the complete displayed premises. -/
theorem hidden_constructor_success {D R : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (P : Program D R) (words : Path P → List (OutputGate D)) (φ : Path P → I → Fin D)
    (T : Matrix I I ℂ) (i j : I) (τ : ℝ) (hτ : 0<τ) (hτ1 : τ ≤ 1/4)
    (n : ℕ) (hn : 0<n) (hbudget : 16/τ^2 ≤ (n : ℝ))
    (ρ : Operator D) (hρ : ρ.PosSemidef) (ht : (Matrix.trace ρ).re=1)
    (G : Finset (Path P))
    (hG : 2/3 ≤ ∑ p∈G,(pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S P ρ hρ ht).prob p)
    (hgood : ∀ p∈G,BlockEncoding T (wordMatrix O (words p))
      (basisFrame (φ p)) (basisFrame (φ p)) 1 (τ/100))
    (hentry : T i j=(((4/(5*(1+2*τ)) : ℝ)) : ℂ)) :
    8/15 ≤ (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S
      (bind P (fun p => repeatReadout R (φ p j) (words p) n)) ρ hρ ht).expect
        (indicator (fun q => outputVote τ P words φ i j n q=false)) := by
  apply constructor_vote_success O hO S P words φ i j τ n false ρ hρ ht G hG
  intro p hp
  have hb := hidden_block_sampling_error O hO (φ p) (words p) T i j τ hτ hτ1 n hn hbudget (hgood p hp) hentry
  have hs := sampleVote_partition (sampleLaw O hO (φ p j) (words p)) τ (fun b => b=φ p i) n
  linarith

/-- The restricted-access construction satisfies `baseline_majority_error` under the complete displayed premises. -/
theorem baseline_majority_error {D R : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (P : Program D R) (words : Path P → List (OutputGate D)) (φ : Path P → I → Fin D)
    (T : Matrix I I ℂ) (i j : I) (τ : ℝ) (hτ : 0<τ) (hτ1 : τ ≤ 1/4)
    (n : ℕ) (hn : 0<n) (hbudget : 16/τ^2 ≤ (n : ℝ)) (r0 : Fin D)
    (G : Finset (Path P))
    (hG : 2/3 ≤ ∑ p∈G,(preparedLaw (fun mode => unitaryChannel (O mode) (hO mode)) S r0 P).prob p)
    (hgood : ∀ p∈G,BlockEncoding T (wordMatrix O (words p))
      (basisFrame (φ p)) (basisFrame (φ p)) 1 (τ/100))
    (hentry : T i j=(4/5 : ℂ))
    (ρ : Operator D) (hρ : ρ.PosSemidef) (ht : (Matrix.trace ρ).re=1) :
    let C := bind P (fun p => repeatReadout R (φ p j) (words p) n)
    (∑ q∈Finset.univ.filter (fun q => programMajority r0 C (outputVote τ P words φ i j n) q≠true),
      (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S
        (repeatPrepared r0 C 1001) ρ hρ ht).prob q) ≤ 1/3 := by
  dsimp only
  apply programMajority_error
  exact baseline_constructor_success O hO S P words φ T i j τ hτ hτ1 n hn hbudget
    (basisDensity r0) (basisDensity_pos r0) (basisDensity_trace_re r0) G hG hgood hentry

/-- The restricted-access construction satisfies `hidden_majority_error` under the complete displayed premises. -/
theorem hidden_majority_error {D R : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (P : Program D R) (words : Path P → List (OutputGate D)) (φ : Path P → I → Fin D)
    (T : Matrix I I ℂ) (i j : I) (τ : ℝ) (hτ : 0<τ) (hτ1 : τ ≤ 1/4)
    (n : ℕ) (hn : 0<n) (hbudget : 16/τ^2 ≤ (n : ℝ)) (r0 : Fin D)
    (G : Finset (Path P))
    (hG : 2/3 ≤ ∑ p∈G,(preparedLaw (fun mode => unitaryChannel (O mode) (hO mode)) S r0 P).prob p)
    (hgood : ∀ p∈G,BlockEncoding T (wordMatrix O (words p))
      (basisFrame (φ p)) (basisFrame (φ p)) 1 (τ/100))
    (hentry : T i j=(((4/(5*(1+2*τ)) : ℝ)) : ℂ))
    (ρ : Operator D) (hρ : ρ.PosSemidef) (ht : (Matrix.trace ρ).re=1) :
    let C := bind P (fun p => repeatReadout R (φ p j) (words p) n)
    (∑ q∈Finset.univ.filter (fun q => programMajority r0 C (outputVote τ P words φ i j n) q≠false),
      (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S
        (repeatPrepared r0 C 1001) ρ hρ ht).prob q) ≤ 1/3 := by
  dsimp only
  apply programMajority_error
  exact hidden_constructor_success O hO S P words φ T i j τ hτ hτ1 n hn hbudget
    (basisDensity r0) (basisDensity_pos r0) (basisDensity_trace_re r0) G hG hgood hentry

/-- Construction for reduction Program in the block sampling readout model. -/
def reductionProgram {D R : ℕ} {I : Type} (P : Program D R)
    (words : Path P → List (OutputGate D)) (φ : Path P → I → Fin D)
    (j : I) (n : ℕ) (r0 : Fin D) : Program D R :=
  repeatPrepared r0 (bind P (fun p => repeatReadout R (φ p j) (words p) n)) 1001

/-- Construction for reduction Vote in the block sampling readout model. -/
def reductionVote {D R : ℕ} {I : Type} (τ : ℝ) (P : Program D R)
    (words : Path P → List (OutputGate D)) (φ : Path P → I → Fin D)
    (i j : I) (n : ℕ) (r0 : Fin D) (q : Path (reductionProgram P words φ j n r0)) : Bool :=
  programMajority r0 (bind P (fun p => repeatReadout R (φ p j) (words p) n))
    (outputVote τ P words φ i j n) q

/-- The restricted-access construction satisfies `reduction_depth` under the complete displayed premises. -/
theorem reduction_depth {D R : ℕ} {I : Type} (P : Program D R)
    (words : Path P → List (OutputGate D)) (φ : Path P → I → Fin D)
    (j : I) (n quse : ℕ) (r0 : Fin D) (hq : ∀ p,wordQueries (words p) ≤ quse) :
    queryDepth (reductionProgram P words φ j n r0) ≤ 1001*(queryDepth P+n*quse) :=
  (repeatPrepared_depth r0 _ 1001).trans (Nat.mul_le_mul_left 1001 (constructor_repeat_depth P words (fun p => φ p j) n quse hq))

/-- The restricted-access construction satisfies `reduction_support_cap` under the complete displayed premises. -/
theorem reduction_support_cap {D R : ℕ} {I : Type} (P : Program D R)
    (words : Path P → List (OutputGate D)) (φ : Path P → I → Fin D)
    (j : I) (n s : ℕ) (r0 : Fin D) (hs : ∀ p,(pathCharge P p).2 ≤ s) :
    ∀ q : Path (reductionProgram P words φ j n r0),
      (pathCharge (reductionProgram P words φ j n r0) q).2 ≤ 1001*s :=
  repeatPrepared_support_cap r0 _ 1001 s (constructor_repeat_support_cap P words (fun p => φ p j) n s hs)

/-- Construction for sampling Grid in the block sampling readout model. -/
def samplingGrid (k : ℕ) : ℕ := 16*(2^k)^2

/-- The restricted-access construction satisfies `dyadic_sampling_budget` under the complete displayed premises. -/
theorem dyadic_sampling_budget (k : ℕ) (hk : 2 ≤ k) :
    0<Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.dyadicTau k ∧ Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.dyadicTau k ≤ 1/4 ∧
      0<samplingGrid k ∧ 16/(Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.dyadicTau k)^2 ≤ (samplingGrid k : ℝ) := by
  have hh := Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.dyadic_readout_budget k hk
  refine ⟨hh.1,hh.2.1,by unfold samplingGrid; positivity,?_⟩
  simp only [samplingGrid,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
    Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.dyadicTau,one_div,inv_pow,div_inv_eq_mul,le_refl]

end Qatlib.Papers.CrouzeixLS26.AccessLower.BlockSampling
