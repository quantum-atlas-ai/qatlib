/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.InputHybrid

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AdaptiveCP.BranchTrace
/-! Separate query/support caps for the actual finite adaptive program.
The cut execution retains all instrument outcomes and coarsens complete source
records into completed paths or a failure marker. The trace-weighted identity
is unconditional; probability tails use the actual positive normalized law.
No arbitrary-machine or variable-width normal form is asserted. -/
set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
open Qatlib Matrix
open scoped BigOperators Classical ComplexOrder

/-- Stop before the first query/support occurrence exceeding its separate
budget. Measurement branches and their full finite alphabets remain. -/
def truncateProgram {D R : ℕ} : Program D R → ℕ → ℕ → Program D R
  | .halt, _, _ => .halt
  | .query _ _, 0, _ => .halt
  | .query mode next, q+1, s => .query mode (truncateProgram next q s)
  | .measure I next, q, s => .measure I (fun o => truncateProgram (next o) q s)
  | .support _ _, _, 0 => .halt
  | .support a next, q, s+1 => .support a (fun o => truncateProgram (next o) q s)

/-- Construction for finish Path in the budget truncation model. -/
def finishPath {D R : ℕ} : (P : Program D R) → (q s : ℕ) →
    Path (truncateProgram P q s) → Option (Path P)
  | .halt, _, _, _ => some ()
  | .query _ _, 0, _, _ => none
  | .query _ next, q+1, s, p => finishPath next q s p
  | .measure _ next, q, s, p => (finishPath (next p.1) q s p.2).map (fun t => ⟨p.1,t⟩)
  | .support _ _, _, 0, _ => none
  | .support _ next, q, s+1, p => (finishPath (next p.1) q s p.2).map (fun t => ⟨p.1,t⟩)

/-- Construction for within Budget in the budget truncation model. -/
def withinBudget {D R : ℕ} (P : Program D R) (q s : ℕ) (p : Path P) : Prop :=
  (pathCharge P p).1 ≤ q ∧ (pathCharge P p).2 ≤ s

/-- The actual truncated finite protocol satisfies `truncate_depth_le` while retaining its failure paths. -/
theorem truncate_depth_le {D R : ℕ} (P : Program D R) (q s : ℕ) :
    queryDepth (truncateProgram P q s) ≤ q := by
  induction P generalizing q s with
  | halt => exact Nat.zero_le _
  | query mode next ih =>
    cases q with
    | zero => exact Nat.le_refl 0
    | succ q => exact Nat.add_le_add_right (ih q s) 1
  | measure I next ih => exact Finset.sup_le (fun o _ => ih o q s)
  | support a next ih =>
    cases s with
    | zero => exact Nat.zero_le _
    | succ s => exact Finset.sup_le (fun o _ => ih o q s)

/-- The actual truncated finite protocol satisfies `truncate_support_le` while retaining its failure paths. -/
theorem truncate_support_le {D R : ℕ} (P : Program D R) (q s : ℕ)
    (p : Path (truncateProgram P q s)) : (pathCharge (truncateProgram P q s) p).2 ≤ s := by
  induction P generalizing q s with
  | halt => exact Nat.zero_le _
  | query mode next ih =>
    cases q with
    | zero => exact Nat.zero_le _
    | succ q => exact ih q s p
  | measure I next ih => exact ih p.1 q s p.2
  | support a next ih =>
    cases s with
    | zero => exact Nat.le_refl 0
    | succ s => exact Nat.add_le_add_right (ih p.1 q s p.2) 1

/-- Construction for budget Outcome in the budget truncation model. -/
def budgetOutcome {D R : ℕ} (P : Program D R) (q s : ℕ) (p : Path P) : Option (Path P) :=
  if withinBudget P q s p then some p else none

/-- The finite protocol identity or bound `trunc_support_weight_sum` holds under exactly the displayed hypotheses. -/
private theorem trunc_support_weight_sum {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (a : ℝ) (next : Fin R → Program D R) (ρ : Operator D) (f : Path (.support a next) → ℝ) :
    (∑ p,(Matrix.trace (pathMap O S (.support a next) p ρ)).re*f p)=
      ∑ p,(Matrix.trace (pathMap O S (next (S a)) p ρ)).re*f ⟨S a,p⟩ := by
  change (∑ p : (o : Fin R) × Path (next o),
    (Matrix.trace (pathMap O S (.support a next) p ρ)).re*f p)=_
  rw [Fintype.sum_sigma]
  have he (o : Fin R) : (∑ p : Path (next o),
      (Matrix.trace (pathMap O S (.support a next) ⟨o,p⟩ ρ)).re*f ⟨o,p⟩)=
      if o=S a then ∑ p : Path (next o),(Matrix.trace (pathMap O S (next o) p ρ)).re*f ⟨o,p⟩ else 0 := by
    by_cases ho : o=S a
    · simp only [pathMap_support_apply,ho,ite_true]
    · simp only [pathMap_support_apply,ho,ite_false,Matrix.trace_zero,Complex.zero_re,zero_mul,Finset.sum_const_zero]
  simp_rw [he]
  simp

/-- Exact trace-weighted coarsening of the actual unnormalized execution.
At a cut node the entire remaining source subtree is summed by its trace-
preservation theorem. This does not assume a coupling or discard records. -/
theorem truncate_weight_sum {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (P : Program D R) (q s : ℕ) (ρ : Operator D) (f : Option (Path P) → ℝ) :
    (∑ p,(Matrix.trace (pathMap O S (truncateProgram P q s) p ρ)).re*f (finishPath P q s p))=
    ∑ p,(Matrix.trace (pathMap O S P p ρ)).re*f (budgetOutcome P q s p) := by
  induction P generalizing q s ρ with
  | halt => simp [truncateProgram,finishPath,budgetOutcome,withinBudget,Path,pathCharge,pathMap]
  | query mode next ih =>
    cases q with
    | zero =>
      have he (p : Path (.query mode next)) : budgetOutcome (.query mode next) 0 s p=none := by
        simp [budgetOutcome,withinBudget,pathCharge]
      simp_rw [he]
      simp only [truncateProgram,finishPath,Path,pathMap,Fintype.sum_unique]
      change (Matrix.trace ρ).re*f none=∑ p : Path (.query mode next),
        (Matrix.trace (pathMap O S (.query mode next) p ρ)).re*f none
      rw [←Finset.sum_mul,path_mass_total]
    | succ q =>
      change (∑ p,(Matrix.trace (pathMap O S (truncateProgram next q s) p ((O mode).map ρ))).re*
        f (finishPath next q s p))=
        ∑ p,(Matrix.trace (pathMap O S next p ((O mode).map ρ))).re*f (budgetOutcome (.query mode next) (q+1) s p)
      rw [ih]
      apply Finset.sum_congr rfl
      intro p _
      congr 1
      simp only [budgetOutcome,withinBudget,pathCharge,Nat.add_le_add_iff_right]
      split_ifs <;> rfl
  | measure I next ih =>
    change (∑ p : (o : _) × Path (truncateProgram (next o) q s),
      (Matrix.trace (pathMap O S (truncateProgram (next p.1) q s) p.2 (I.branch p.1 ρ))).re*
        f ((finishPath (next p.1) q s p.2).map (fun t => ⟨p.1,t⟩)))=
      ∑ p : (o : _) × Path (next o),(Matrix.trace (pathMap O S (next p.1) p.2 (I.branch p.1 ρ))).re*
        f (budgetOutcome (.measure I next) q s p)
    rw [Fintype.sum_sigma,Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro o _
    have he := ih o q s (I.branch o ρ) (fun t => f (t.map (fun u => ⟨o,u⟩)))
    rw [he]
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    simp only [budgetOutcome,withinBudget,pathCharge]
    split_ifs <;> rfl
  | support a next ih =>
    cases s with
    | zero =>
      have he (p : Path (.support a next)) : budgetOutcome (.support a next) q 0 p=none := by
        simp [budgetOutcome,withinBudget,pathCharge]
      simp_rw [he]
      simp only [truncateProgram,finishPath,Path,pathMap,Fintype.sum_unique]
      change (Matrix.trace ρ).re*f none=∑ p : Path (.support a next),
        (Matrix.trace (pathMap O S (.support a next) p ρ)).re*f none
      rw [←Finset.sum_mul,path_mass_total]
    | succ s =>
      change (∑ p,(Matrix.trace (pathMap O S (.support a (fun o => truncateProgram (next o) q s)) p ρ)).re*
        f ((finishPath (next p.1) q s p.2).map (fun t => ⟨p.1,t⟩)))=
        ∑ p,(Matrix.trace (pathMap O S (.support a next) p ρ)).re*f (budgetOutcome (.support a next) q (s+1) p)
      rw [trunc_support_weight_sum,trunc_support_weight_sum]
      have he := ih (S a) q s ρ (fun t => f (t.map (fun u => ⟨S a,u⟩)))
      rw [he]
      apply Finset.sum_congr rfl
      intro p _
      congr 1
      simp only [budgetOutcome,withinBudget,pathCharge,Nat.add_le_add_iff_right]
      split_ifs <;> rfl


/-- Exact event pushforward, including cut records as none. -/
theorem truncate_event {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (P : Program D R) (q s : ℕ) (ρ : Operator D) (hρ : ρ.PosSemidef)
    (ht : (Matrix.trace ρ).re=1) (E : Path P → Prop) [DecidablePred E] :
    (∑ r∈Finset.univ.filter (fun r => ∃ p,finishPath P q s r=some p ∧ E p),
      (pathLaw O S (truncateProgram P q s) ρ hρ ht).prob r)=
    ∑ p∈Finset.univ.filter (fun p => withinBudget P q s p ∧ E p),
      (pathLaw O S P ρ hρ ht).prob p := by
  have he := truncate_weight_sum O S P q s ρ
    (fun o => if ∃ p,o=some p ∧ E p then (1 : ℝ) else 0)
  have hr (p : Path P) : (if ∃ p',budgetOutcome P q s p=some p' ∧ E p' then (1 : ℝ) else 0)=
      if withinBudget P q s p ∧ E p then 1 else 0 := by
    by_cases hb : withinBudget P q s p <;> simp [budgetOutcome,hb]
  simp_rw [hr] at he
  simp only [pathLaw,Finset.sum_filter]
  simpa only [mul_ite,mul_one,mul_zero] using he

/-- Natural-cost Markov bound on the actual full law. -/
theorem nat_cost_tail {X : Type} [Fintype X] (μ : FinDist X) (cost : X → ℕ) (K : ℕ) :
    ((K+1 : ℕ) : ℝ)*(∑ p∈Finset.univ.filter (fun p => K<cost p),μ.prob p) ≤
      μ.expect (fun p => (cost p : ℝ)) := by
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ p∈Finset.univ.filter (fun p => K<cost p),μ.prob p*(cost p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hk : ((K+1 : ℕ) : ℝ) ≤ cost p := by exact_mod_cast (Finset.mem_filter.mp hp).2
      nlinarith [mul_le_mul_of_nonneg_left hk (μ.nonneg p)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun p _ _ => mul_nonneg (μ.nonneg p) (Nat.cast_nonneg _))

/-- The finite protocol identity or bound `retained_good_mass` holds under exactly the displayed hypotheses. -/
theorem retained_good_mass {X : Type} [Fintype X] [DecidableEq X]
    (μ : FinDist X) (cost : X → ℕ) (G : Finset X) (B : ℝ) (K : ℕ)
    (hG : 2/3 ≤ ∑ p∈G,μ.prob p) (hcost : μ.expect (fun p => (cost p : ℝ)) ≤ B)
    (hK : 24*B ≤ (K : ℝ)) :
    5/8 ≤ ∑ p∈G.filter (fun p => cost p ≤ K),μ.prob p := by
  let bad := Finset.univ.filter (fun p => K<cost p)
  have ht := (nat_cost_tail μ cost K).trans hcost
  have hkpos : (0 : ℝ)<((K+1 : ℕ) : ℝ) := by positivity
  have htail : (∑ p∈bad,μ.prob p) ≤ 1/24 := by
    apply ((le_div_iff₀' hkpos).mpr ht).trans
    apply (div_le_iff₀ hkpos).mpr
    push_cast
    linarith
  have hcover : (∑ p∈G,μ.prob p) ≤
      (∑ p∈G.filter (fun p => cost p ≤ K),μ.prob p)+(∑ p∈bad,μ.prob p) := by
    have hpoint (p : X) : (if p∈G then μ.prob p else 0) ≤
        (if p∈G.filter (fun p => cost p ≤ K) then μ.prob p else 0)+
          (if p∈bad then μ.prob p else 0) := by
      by_cases hg : p∈G
      · by_cases hk : cost p ≤ K
        · simp only [Finset.mem_filter,hg,hk,and_self,ite_true]
          split_ifs <;> linarith [μ.nonneg p]
        · have hb : p∈bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
          simp [hg,hk,hb]
      · simp only [hg,ite_false,Finset.mem_filter,false_and]
        split_ifs <;> linarith [μ.nonneg p]
    have hs := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => hpoint p)
    simpa only [Finset.sum_add_distrib,Finset.sum_ite_mem,Finset.univ_inter] using hs
  linarith

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
