/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.OutputReadout
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AdaptiveCP.BranchTrace
/-! Repeated execution of one finite adaptive program after explicit known
basis resets. Complete records are retained and their IID law is derived
from the same unnormalized CP execution, conditional on the same fixed input
oracles. All-path query/support costs and a single truth-independent Boolean
majority decoder are proved. No arbitrary-algorithm normal form, variable
width padding, expected-budget truncation or full primitive cost is supplied. -/

set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
open Qatlib Matrix
open scoped BigOperators Classical ComplexOrder

/-- Construction for basis Density in the prepared repeat model. -/
def basisDensity {D : ℕ} (r : Fin D) : Operator D := outerProduct (Qatlib.Foundations.PureStateMath.Ket r)
/-- The finite protocol identity or bound `basisDensity_pos` holds under exactly the displayed hypotheses. -/
theorem basisDensity_pos {D : ℕ} (r : Fin D) : (basisDensity r).PosSemidef := outerProduct_posSemidef _
/-- The finite protocol identity or bound `basisDensity_trace` holds under exactly the displayed hypotheses. -/
theorem basisDensity_trace {D : ℕ} (r : Fin D) : Matrix.trace (basisDensity r)=1 := by
  simp [basisDensity,outerProduct,Qatlib.Foundations.PureStateMath.Ket,Matrix.trace]
/-- The finite protocol identity or bound `basisDensity_trace_re` holds under exactly the displayed hypotheses. -/
theorem basisDensity_trace_re {D : ℕ} (r : Fin D) : (Matrix.trace (basisDensity r)).re=1 := by
  rw [basisDensity_trace]; rfl

/-- Construction for prepared Program in the prepared repeat model. -/
def preparedProgram {D R : ℕ} (r : Fin D) (P : Program D R) : Program D R :=
  .measure (resetInstrument r) (fun _ => P)
/-- Construction for prepared Path in the prepared repeat model. -/
def preparedPath {D R : ℕ} (r : Fin D) (P : Program D R) (p : Path P) : Path (preparedProgram r P) := ⟨0,p⟩

/-- The finite protocol identity or bound `preparedProgram_trace` holds under exactly the displayed hypotheses. -/
theorem preparedProgram_trace {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (r : Fin D) (P : Program D R) (p : Path P) (ρ : Operator D) :
    Matrix.trace (pathMap O S (preparedProgram r P) (preparedPath r P p) ρ)=
      Matrix.trace ρ*Matrix.trace (pathMap O S P p (basisDensity r)) := by
  change Matrix.trace (pathMap O S P p ((resetChannel r).map ρ))=_
  exact reset_follow_trace r ρ (pathMap O S P p)

/-- Construction for prepared Outcome in the prepared repeat model. -/
def preparedOutcome {D R : ℕ} (r : Fin D) (P : Program D R) (p : Path (preparedProgram r P)) : Path P := p.2

/-- Construction for prepared Path Equiv in the prepared repeat model. -/
def preparedPathEquiv {D R : ℕ} (r : Fin D) (P : Program D R) : Path P ≃ Path (preparedProgram r P) where
  toFun := preparedPath r P
  invFun := preparedOutcome r P
  left_inv := by intro p; rfl
  right_inv := by
    intro q
    rcases q with ⟨o,q⟩
    have ho : o=(0 : Fin 1) := Subsingleton.elim _ _
    subst o
    rfl

/-- Construction for prepared Law in the prepared repeat model. -/
def preparedLaw {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (r : Fin D) (P : Program D R) : FinDist (Path P) :=
  pathLaw O S P (basisDensity r) (basisDensity_pos r) (basisDensity_trace_re r)

/-- The finite protocol identity or bound `prepared_branch_trace` holds under exactly the displayed hypotheses. -/
theorem prepared_branch_trace {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (r : Fin D) (P : Program D R) (p : Path P) :
    Matrix.trace (pathMap O S P p (basisDensity r))=((preparedLaw O S r P).prob p : ℂ) := by
  exact trace_branch_eq (pathInstrument O S P) (basisDensity_pos r) p

/-- Construction for repeat Prepared in the prepared repeat model. -/
def repeatPrepared {D R : ℕ} (r : Fin D) (P : Program D R) : ℕ → Program D R
  | 0 => .halt
  | n+1 => bind (preparedProgram r P) (fun _ => repeatPrepared r P n)

/-- Construction for prepared Repeat Path in the prepared repeat model. -/
def preparedRepeatPath {D R : ℕ} (r : Fin D) (P : Program D R) :
    (n : ℕ) → (Fin n → Path P) → Path (repeatPrepared r P n)
  | 0, _ => ()
  | n+1, ω => joinPath (preparedProgram r P) (fun _ => repeatPrepared r P n)
      (preparedPath r P (ω 0)) (preparedRepeatPath r P n (fun i => ω i.succ))

/-- The actual finite repeated protocol satisfies `repeatPrepared_trace` without conditioning away failure records. -/
theorem repeatPrepared_trace {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (r : Fin D) (P : Program D R) (n : ℕ) (ω : Fin n → Path P) (ρ : Operator D) :
    Matrix.trace (pathMap O S (repeatPrepared r P n) (preparedRepeatPath r P n ω) ρ)=
      Matrix.trace ρ*∏ i : Fin n,((preparedLaw O S r P).prob (ω i) : ℂ) := by
  induction n generalizing ρ with
  | zero => simp [repeatPrepared,preparedRepeatPath,pathMap]
  | succ n ih =>
    change Matrix.trace (pathMap O S (bind (preparedProgram r P) (fun _ => repeatPrepared r P n))
      (joinPath (preparedProgram r P) (fun _ => repeatPrepared r P n)
        (preparedPath r P (ω 0)) (preparedRepeatPath r P n (fun i => ω i.succ))) ρ)=_
    rw [pathMap_bind]
    change Matrix.trace (pathMap O S (repeatPrepared r P n)
      (preparedRepeatPath r P n (fun i => ω i.succ))
      (pathMap O S (preparedProgram r P) (preparedPath r P (ω 0)) ρ))=_
    rw [ih,preparedProgram_trace,prepared_branch_trace,Fin.prod_univ_succ,mul_assoc]

/-- Construction for prepared Repeat Outcome in the prepared repeat model. -/
def preparedRepeatOutcome {D R : ℕ} (r : Fin D) (P : Program D R) :
    (n : ℕ) → Path (repeatPrepared r P n) → (Fin n → Path P)
  | 0, _ => Fin.elim0
  | n+1, q =>
    let pq := splitPath (preparedProgram r P) (fun _ => repeatPrepared r P n) q
    Fin.cons (preparedOutcome r P pq.1) (preparedRepeatOutcome r P n pq.2)

/-- The finite protocol identity or bound `preparedRepeatOutcome_path` holds under exactly the displayed hypotheses. -/
theorem preparedRepeatOutcome_path {D R : ℕ} (r : Fin D) (P : Program D R)
    (n : ℕ) (ω : Fin n → Path P) :
    preparedRepeatOutcome r P n (preparedRepeatPath r P n ω)=ω := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [preparedRepeatOutcome,preparedRepeatPath,split_join,Fin.cons_zero,preparedOutcome,preparedPath]
    · simp only [preparedRepeatOutcome,preparedRepeatPath,split_join,Fin.cons_succ,ih]

/-- The finite protocol identity or bound `preparedRepeatPath_outcome` holds under exactly the displayed hypotheses. -/
theorem preparedRepeatPath_outcome {D R : ℕ} (r : Fin D) (P : Program D R)
    (n : ℕ) (q : Path (repeatPrepared r P n)) :
    preparedRepeatPath r P n (preparedRepeatOutcome r P n q)=q := by
  induction n with
  | zero => cases q; rfl
  | succ n ih =>
    change joinPath (preparedProgram r P) (fun _ => repeatPrepared r P n)
      (preparedPath r P (preparedOutcome r P
        (splitPath (preparedProgram r P) (fun _ => repeatPrepared r P n) q).1))
      (preparedRepeatPath r P n (preparedRepeatOutcome r P n
        (splitPath (preparedProgram r P) (fun _ => repeatPrepared r P n) q).2))=q
    have he (p : Path (preparedProgram r P)) : preparedPath r P (preparedOutcome r P p)=p :=
      (preparedPathEquiv r P).right_inv p
    rw [he,ih]
    exact join_split (preparedProgram r P) (fun _ => repeatPrepared r P n) q

/-- Construction for prepared Repeat Path Equiv in the prepared repeat model. -/
def preparedRepeatPathEquiv {D R : ℕ} (r : Fin D) (P : Program D R) (n : ℕ) :
    (Fin n → Path P) ≃ Path (repeatPrepared r P n) where
  toFun := preparedRepeatPath r P n
  invFun := preparedRepeatOutcome r P n
  left_inv := preparedRepeatOutcome_path r P n
  right_inv := preparedRepeatPath_outcome r P n

/-- The actual finite repeated protocol satisfies `repeatPrepared_law` without conditioning away failure records. -/
theorem repeatPrepared_law {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (r : Fin D) (P : Program D R) (n : ℕ) (ω : Fin n → Path P)
    (ρ : Operator D) (hρ : ρ.PosSemidef) (ht : (Matrix.trace ρ).re=1) :
    (pathLaw O S (repeatPrepared r P n) ρ hρ ht).prob (preparedRepeatPath r P n ω)=
      (preparedLaw O S r P).probOf ω := by
  change (Matrix.trace (pathMap O S (repeatPrepared r P n) (preparedRepeatPath r P n ω) ρ)).re=_
  rw [repeatPrepared_trace]
  have he : (∏ i : Fin n,((preparedLaw O S r P).prob (ω i) : ℂ))=
      (((preparedLaw O S r P).probOf ω : ℝ) : ℂ) := by simp [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf]
  rw [he]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,ht,one_mul]

/-- The finite protocol identity or bound `preparedProgram_charge` holds under exactly the displayed hypotheses. -/
theorem preparedProgram_charge {D R : ℕ} (r : Fin D) (P : Program D R) (p : Path P) :
    pathCharge (preparedProgram r P) (preparedPath r P p)=pathCharge P p := rfl

/-- The actual finite repeated protocol satisfies `repeatPrepared_charge` without conditioning away failure records. -/
theorem repeatPrepared_charge {D R : ℕ} (r : Fin D) (P : Program D R)
    (n : ℕ) (ω : Fin n → Path P) :
    pathCharge (repeatPrepared r P n) (preparedRepeatPath r P n ω)=
      (∑ i : Fin n,(pathCharge P (ω i)).1,∑ i : Fin n,(pathCharge P (ω i)).2) := by
  induction n with
  | zero => simp [repeatPrepared,preparedRepeatPath,pathCharge]
  | succ n ih =>
    change pathCharge (bind (preparedProgram r P) (fun _ => repeatPrepared r P n))
      (joinPath (preparedProgram r P) (fun _ => repeatPrepared r P n)
        (preparedPath r P (ω 0)) (preparedRepeatPath r P n (fun i => ω i.succ)))=_
    rw [pathCharge_bind,preparedProgram_charge,ih]
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]

/-- The actual finite repeated protocol satisfies `repeatPrepared_support_cap` without conditioning away failure records. -/
theorem repeatPrepared_support_cap {D R : ℕ} (r : Fin D) (P : Program D R) (n s : ℕ)
    (hc : ∀ p,(pathCharge P p).2 ≤ s) :
    ∀ q : Path (repeatPrepared r P n),(pathCharge (repeatPrepared r P n) q).2 ≤ n*s := by
  intro q
  obtain ⟨ω,rfl⟩ := (preparedRepeatPathEquiv r P n).surjective q
  change (pathCharge (repeatPrepared r P n) (preparedRepeatPath r P n ω)).2 ≤ n*s
  rw [repeatPrepared_charge]
  calc
    (∑ i : Fin n,(pathCharge P (ω i)).2) ≤ ∑ _ : Fin n,s := Finset.sum_le_sum (fun i _ => hc (ω i))
    _ = n*s := by simp

/-- The finite protocol identity or bound `preparedProgram_depth` holds under exactly the displayed hypotheses. -/
theorem preparedProgram_depth {D R : ℕ} (r : Fin D) (P : Program D R) :
    queryDepth (preparedProgram r P) ≤ queryDepth P := Finset.sup_le (fun _ _ => Nat.le_refl _)

/-- The actual finite repeated protocol satisfies `repeatPrepared_depth` without conditioning away failure records. -/
theorem repeatPrepared_depth {D R : ℕ} (r : Fin D) (P : Program D R) (n : ℕ) :
    queryDepth (repeatPrepared r P n) ≤ n*queryDepth P := by
  induction n with
  | zero => simp [repeatPrepared,queryDepth]
  | succ n ih =>
    have hh := queryDepth_bind_le (preparedProgram r P) (fun _ => repeatPrepared r P n)
      (n*queryDepth P) (fun _ => ih)
    have hp := preparedProgram_depth r P
    change queryDepth (bind (preparedProgram r P) (fun _ => repeatPrepared r P n)) ≤ _
    calc
      _ ≤ queryDepth (preparedProgram r P)+n*queryDepth P := hh
      _ ≤ queryDepth P+n*queryDepth P := Nat.add_le_add_right hp _
      _ = (n+1)*queryDepth P := by rw [Nat.add_mul,Nat.one_mul]; omega

/-- The actual finite repeated protocol satisfies `repeatPrepared_event` without conditioning away failure records. -/
theorem repeatPrepared_event {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (r : Fin D) (P : Program D R) (n : ℕ)
    (ρ : Operator D) (hρ : ρ.PosSemidef) (ht : (Matrix.trace ρ).re=1)
    (E : (Fin n → Path P) → Prop) [DecidablePred E] :
    (∑ q∈Finset.univ.filter (fun q => E (preparedRepeatOutcome r P n q)),
      (pathLaw O S (repeatPrepared r P n) ρ hρ ht).prob q)=
      (preparedLaw O S r P).probEvent E := by
  rw [Finset.sum_filter]
  have he := (preparedRepeatPathEquiv r P n).sum_comp
    (fun q : Path (repeatPrepared r P n) => if E (preparedRepeatOutcome r P n q) then
      (pathLaw O S (repeatPrepared r P n) ρ hρ ht).prob q else 0)
  rw [←he]
  change (∑ ω : Fin n → Path P,if E (preparedRepeatOutcome r P n (preparedRepeatPath r P n ω)) then
    (pathLaw O S (repeatPrepared r P n) ρ hρ ht).prob (preparedRepeatPath r P n ω) else 0)=_
  simp_rw [preparedRepeatOutcome_path,repeatPrepared_law]
  exact (Finset.sum_filter ..).symm

/-- Majority concentration for the actual repeated reconstruction program,
not an assumed product distribution. The truth predicate is analysis-only. -/
theorem repeatPrepared_majority_failure {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (r : Fin D) (P : Program D R) (C : Path P → Prop) [DecidablePred C]
    (hmean : 8/15 ≤ (preparedLaw O S r P).expect (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify.indicator C))
    (ρ : Operator D) (hρ : ρ.PosSemidef) (ht : (Matrix.trace ρ).re=1) :
    (∑ q∈Finset.univ.filter (fun q =>
        Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify.indicator C) (preparedRepeatOutcome r P 1001 q) ≤ 1/2),
      (pathLaw O S (repeatPrepared r P 1001) ρ hρ ht).prob q) ≤ 1/3 := by
  rw [repeatPrepared_event O S r P 1001 ρ hρ ht
    (fun ω => Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify.indicator C) ω ≤ 1/2)]
  exact Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify.independent_majority_failure (preparedLaw O S r P) C hmean

/-- Construction for majority Vote in the prepared repeat model. -/
def majorityVote {X : Type} [Fintype X] (vote : X → Bool) {n : ℕ} (ω : Fin n → X) : Bool :=
  decide (1/2<Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify.indicator (fun x => vote x=true)) ω)

/-- The finite protocol identity or bound `bool_avg_complement` holds under exactly the displayed hypotheses. -/
private theorem bool_avg_complement {X : Type} [Fintype X] (vote : X → Bool)
    (n : ℕ) (hn : 0<n) (ω : Fin n → X) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify.indicator (fun x => vote x=false)) ω=
      1-Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify.indicator (fun x => vote x=true)) ω := by
  have hnr : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  have he (i : Fin n) : Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify.indicator (fun x => vote x=false) (ω i)=
      1-Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify.indicator (fun x => vote x=true) (ω i) := by
    cases hv : vote (ω i) <;> simp [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify.indicator,hv]
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  field_simp

/-- Execution uses one fixed vote. Hidden truth appears only in this bound. -/
theorem majority_wrong_small_correct {X : Type} [Fintype X] (vote : X → Bool)
    (truth : Bool) (n : ℕ) (hn : 0<n) (ω : Fin n → X) (hwrong : majorityVote vote ω≠truth) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify.indicator (fun x => vote x=truth)) ω ≤ 1/2 := by
  cases truth with
  | false =>
    have hm : 1/2<Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify.indicator (fun x => vote x=true)) ω := by
      by_contra hh
      have he : majorityVote vote ω=false := by
        simp only [majorityVote,decide_eq_false_iff_not]
        exact hh
      exact hwrong he
    rw [bool_avg_complement vote n hn ω]
    linarith
  | true =>
    have hm : ¬1/2<Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify.indicator (fun x => vote x=true)) ω := by
      intro hh
      have he : majorityVote vote ω=true := by
        simp only [majorityVote,decide_eq_true_eq]
        exact hh
      exact hwrong he
    exact le_of_not_gt hm

/-- Construction for program Majority in the prepared repeat model. -/
def programMajority {D R : ℕ} (r : Fin D) (P : Program D R) (vote : Path P → Bool)
    (q : Path (repeatPrepared r P 1001)) : Bool := majorityVote vote (preparedRepeatOutcome r P 1001 q)

/-- The actual finite repeated protocol satisfies `programMajority_error` without conditioning away failure records. -/
theorem programMajority_error {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (r : Fin D) (P : Program D R) (vote : Path P → Bool) (truth : Bool)
    (hmean : 8/15 ≤ (preparedLaw O S r P).expect (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify.indicator (fun p => vote p=truth)))
    (ρ : Operator D) (hρ : ρ.PosSemidef) (ht : (Matrix.trace ρ).re=1) :
    (∑ q∈Finset.univ.filter (fun q => programMajority r P vote q≠truth),
      (pathLaw O S (repeatPrepared r P 1001) ρ hρ ht).prob q) ≤ 1/3 := by
  have hsub : (Finset.univ.filter (fun q => programMajority r P vote q≠truth)) ⊆
      Finset.univ.filter (fun q =>
        Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify.indicator (fun p => vote p=truth))
          (preparedRepeatOutcome r P 1001 q) ≤ 1/2) := by
    intro q hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    exact majority_wrong_small_correct vote truth 1001 (by decide) _ (Finset.mem_filter.mp hq).2
  have hs := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun q => (pathLaw O S (repeatPrepared r P 1001) ρ hρ ht).prob q) hsub
    (fun q _ _ => (pathLaw O S (repeatPrepared r P 1001) ρ hρ ht).nonneg q)
  exact hs.trans (repeatPrepared_majority_failure O S r P (fun p => vote p=truth) hmean ρ hρ ht)

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
