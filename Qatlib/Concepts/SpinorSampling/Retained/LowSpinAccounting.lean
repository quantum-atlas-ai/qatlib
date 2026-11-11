/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.LowSpinOriginal
import Qatlib.Concepts.SpinorSampling.Matching.HighConfidenceAccounting

set_option backward.isDefEq.respectTransparency false

/-!
# Low Spin Accounting

Low Spin Accounting constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.FiniteExecution Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Matched

/-- Data and invariants for Low Spin Receipt Q in the low spin accounting model. -/
structure LowSpinReceiptQ where
  value : ℚ
  velocityValue : ℚ
  velocityCopies : ℕ
  targetQueries : ℕ
  uniformSites : ℕ
  spin : List PlannedBellReceiptQ

/-- Construction for bell Receipt Sum in the low spin accounting model. -/
def bellReceiptSum (f : PlannedBellReceiptQ → ℕ) (rs : List PlannedBellReceiptQ) : ℕ :=
  (rs.map f).sum

/-- Construction for Low Spin Receipt Q.copies in the low spin accounting model. -/
def LowSpinReceiptQ.copies (r : LowSpinReceiptQ) : ℕ :=
  r.velocityCopies+bellReceiptSum (·.copies) r.spin

/-- Construction for low Spin Bell Scheduled Copies in the low spin accounting model. -/
def lowSpinBellScheduledCopies (d : ℕ) (spin : Option BellPlanQ) : ℕ :=
  match spin with | none => 0 | some q => d*q.copies

variable {S : Type} [DecidableEq S] {d : ℕ}

/-- Construction for low Spin Bell Receipts in the low spin accounting model. -/
def lowSpinBellReceipts (e : Fin d → Equiv.Perm S) (spin : Option BellPlanQ) :
    LowSpinBellData S d e spin → List PlannedBellReceiptQ :=
  match spin with
  | none => fun _ => []
  | some q => fun ω => List.ofFn (fun j : Fin d => executePlannedBellQ q (e j) (ω j))

/-- Complete original `low_spin_bell_wire_account` guarantee for `LowSpinAccounting`; all source hypotheses and output obligations are retained. -/
theorem low_spin_bell_wire_account (e : Fin d → Equiv.Perm S) (spin : Option BellPlanQ)
    (ω : LowSpinBellData S d e spin) :
    let rs := lowSpinBellReceipts e spin ω
    bellReceiptSum (·.copies) rs=bellReceiptSum (·.discards) rs+2*bellReceiptSum (·.bellTests) rs ∧
    bellReceiptSum (·.nativeBellGates) rs=2*bellReceiptSum (·.bellTests) rs ∧
    bellReceiptSum (·.nativeBellQueries) rs=0 := by
  cases spin with
  | none => simp [lowSpinBellReceipts,bellReceiptSum]
  | some q =>
    simp only [lowSpinBellReceipts,bellReceiptSum,List.map_ofFn,Function.comp_def,List.sum_ofFn]
    constructor
    · simp_rw [fun j => (executed_bell_wire_account q (e j) (ω j)).1]
      rw [Finset.sum_add_distrib,Finset.mul_sum]
    · constructor
      · simp_rw [fun j => (executed_bell_wire_account q (e j) (ω j)).2.1]
        rw [Finset.mul_sum]
      · simp_rw [fun j => (executed_bell_wire_account q (e j) (ω j)).2.2]
        exact Finset.sum_const_zero

-- This helper's consistency premise is proved from the literal constructor
-- below; it is not supplied by an execution caller or a success certificate.
/-- Complete original `low_spin_bell_copy_sum` guarantee for `LowSpinAccounting`; all source hypotheses and output obligations are retained. -/
theorem low_spin_bell_copy_sum (e : Fin d → Equiv.Perm S) (spin : Option BellPlanQ)
    (hplan : ∀ q,spin=some q → q.blocks*(q.records+q.records)=q.copies)
    (ω : LowSpinBellData S d e spin) :
    bellReceiptSum (·.copies) (lowSpinBellReceipts e spin ω)=lowSpinBellScheduledCopies d spin := by
  cases spin with
  | none => simp [lowSpinBellReceipts,bellReceiptSum,lowSpinBellScheduledCopies]
  | some q =>
    simp only [lowSpinBellReceipts,bellReceiptSum,List.map_ofFn,Function.comp_def,List.sum_ofFn,
      executePlannedBellQ,captured_address_records_length,hplan q rfl,lowSpinBellScheduledCopies]
    simp

omit [DecidableEq S] in
/-- Complete original `bell_plan_geometric_copies` guarantee for `LowSpinAccounting`; all source hypotheses and output obligations are retained. -/
theorem bell_plan_geometric_copies (side M : ℕ) (p ε δ : ℚ) :
    let q := bellPlanQ side M p ε δ
    q.blocks*(q.records+q.records)=q.copies := by
  by_cases hs : side≤2
  · simp [bellPlanQ,hs]
  · by_cases hm : p≤2*ε
    · simp [bellPlanQ,hs,hm]
    · by_cases hn : bellRecordsQ M p ε δ≤M
      · simp [bellPlanQ,hs,hm,hn]
        omega
      · simp only [bellPlanQ,ite_eq_right hs,ite_eq_right hm,ite_eq_right hn]
        ring

omit [DecidableEq S] in
/-- Complete original `low_spin_plan_bell_consistency` guarantee for `LowSpinAccounting`; all source hypotheses and output obligations are retained. -/
theorem low_spin_plan_bell_consistency (side d M : ℕ) (rootM α β U γ η δ p₀ : ℚ) :
    ∀ q,(lowSpinPlanQ side d M rootM α β U γ η δ p₀).spin=some q →
      q.blocks*(q.records+q.records)=q.copies := by
  intro q hq
  by_cases hγ : γ=0
  · simp only [lowSpinPlanQ,ite_eq_left hγ] at hq
    contradiction
  · simp only [lowSpinPlanQ,ite_eq_right hγ,Option.some.injEq] at hq
    subst q
    exact bell_plan_geometric_copies side M p₀ (η/(32*(d : ℚ)*γ)) (δ/(4*(d : ℚ)))

variable [Fintype S]

/-- Construction for low Spin Velocity Records in the low spin accounting model. -/
def lowSpinVelocityRecords (p : LowSpinPlanQ) (e : Fin d → Equiv.Perm S)
    (z : LowSpinData S d e p) (j : Fin d) : List (S × Bool) :=
  consumedCorrelationRecords p.velocity.current.mode p.velocity.current.records
    p.velocity.current.blocks (z.1 j).1 ++ List.ofFn (z.1 j).2.1

/-- Construction for low Spin Target Queries in the low spin accounting model. -/
def lowSpinTargetQueries [LinearOrder S] (p : LowSpinPlanQ) (e : Fin d → Equiv.Perm S)
    (z : LowSpinData S d e p) (j : Fin d) : List S :=
  crossTargetQueries (z.1 j).2.1 ++ targetNormQueries p.velocity.norm.mode
    p.velocity.norm.records p.velocity.norm.blocks (z.1 j).2.2

-- Counts come from the same observed lists and receipts as the return value.
-- Bell gates here count only the existing native two-gate words. Loading,
/-- address readout, routing, reset and classical work retain separate charges. -/
def executeLowSpinQ [LinearOrder S] (p : LowSpinPlanQ) (u : Fin d → S → ℚ)
    (e : Fin d → Equiv.Perm S) (α β U γ : ℚ) (z : LowSpinData S d e p) : LowSpinReceiptQ where
  value := lowSpinOutputQ p u e α β U γ z
  velocityValue := lowSpinVelocityValueQ p.velocity u α β U z.1
  velocityCopies := ∑ j : Fin d,(lowSpinVelocityRecords p e z j).length
  targetQueries := ∑ j : Fin d,(lowSpinTargetQueries p e z j).length
  uniformSites := if p.velocity.norm.mode=.sampled then
    ∑ j : Fin d,(targetNormQueries p.velocity.norm.mode p.velocity.norm.records
      p.velocity.norm.blocks (z.1 j).2.2).length else 0
  spin := lowSpinBellReceipts e p.spin z.2

/-- Complete original `executed_low_spin_copies` guarantee for `LowSpinAccounting`; all source hypotheses and output obligations are retained. -/
theorem executed_low_spin_copies [LinearOrder S] (side d : ℕ)
    (rootM α β U γ η δ p₀ : ℚ) (u : Fin d → S → ℚ) (e : Fin d → Equiv.Perm S)
    (z : LowSpinData S d e (lowSpinPlanQ side d (Fintype.card S) rootM α β U γ η δ p₀)) :
    let p := lowSpinPlanQ side d (Fintype.card S) rootM α β U γ η δ p₀
    (executeLowSpinQ p u e α β U γ z).copies=p.copies := by
  let p := lowSpinPlanQ side d (Fintype.card S) rootM α β U γ η δ p₀
  have hC : scheduledCopies p.velocity.current=p.velocity.current.copies :=
    high_plan_current_schedule_account d (Fintype.card S) rootM α β U γ η δ
  have hv (j : Fin d) : (lowSpinVelocityRecords p e z j).length=
      p.velocity.current.copies+p.velocity.crossRecords := by
    rw [lowSpinVelocityRecords,List.length_append,correlation_records_length_schedule,List.length_ofFn,hC]
  have hb := low_spin_bell_copy_sum e p.spin
    (low_spin_plan_bell_consistency side d (Fintype.card S) rootM α β U γ η δ p₀) z.2
  change (∑ j : Fin d,(lowSpinVelocityRecords p e z j).length)+
    bellReceiptSum (·.copies) (lowSpinBellReceipts e p.spin z.2)=p.copies
  simp_rw [hv]
  rw [hb,show p.copies=p.velocity.copies+(match p.spin with | none => 0 | some q => d*q.copies)
    from (low_plan_account_fields side d (Fintype.card S) rootM α β U γ η δ p₀).1]
  have hpv : p.velocity.copies=d*(p.velocity.current.copies+p.velocity.crossRecords) :=
    (low_plan_velocity_fields side d (Fintype.card S) rootM α β U γ η δ p₀).2.2.2.2
  rw [hpv]
  simp [lowSpinBellScheduledCopies]

/-- Complete original `executed_low_spin_query_bound` guarantee for `LowSpinAccounting`; all source hypotheses and output obligations are retained. -/
theorem executed_low_spin_query_bound [LinearOrder S] (side d : ℕ)
    (rootM α β U γ η δ p₀ : ℚ) (u : Fin d → S → ℚ) (e : Fin d → Equiv.Perm S)
    (z : LowSpinData S d e (lowSpinPlanQ side d (Fintype.card S) rootM α β U γ η δ p₀)) :
    let p := lowSpinPlanQ side d (Fintype.card S) rootM α β U γ η δ p₀
    (executeLowSpinQ p u e α β U γ z).targetQueries≤p.targetQueries := by
  let p := lowSpinPlanQ side d (Fintype.card S) rootM α β U γ η δ p₀
  have hN (j : Fin d) : (targetNormQueries p.velocity.norm.mode p.velocity.norm.records
      p.velocity.norm.blocks (z.1 j).2.2).length=p.velocity.norm.queries :=
    planned_norm_queries_length (β*U) (η/(8*(d : ℚ))) (δ/(4*(d : ℚ))) (z.1 j).2.2
  have hQ (j : Fin d) : (lowSpinTargetQueries p e z j).length≤
      min p.velocity.crossRecords (Fintype.card S)+p.velocity.norm.queries := by
    rw [lowSpinTargetQueries,List.length_append,hN]
    exact Nat.add_le_add_right (cross_target_queries_bound (z.1 j).2.1) _
  change (∑ j : Fin d,(lowSpinTargetQueries p e z j).length)≤p.targetQueries
  calc
    _ ≤ ∑ _j : Fin d,(min p.velocity.crossRecords (Fintype.card S)+p.velocity.norm.queries) :=
      Finset.sum_le_sum fun j _ => hQ j
    _ = _ := by
      change (∑ _j : Fin d,_)=d*min p.velocity.crossRecords (Fintype.card S)+d*p.velocity.norm.queries
      simp [Nat.mul_add]

/-- Complete original `executed_low_spin_uniform_sites` guarantee for `LowSpinAccounting`; all source hypotheses and output obligations are retained. -/
theorem executed_low_spin_uniform_sites [LinearOrder S] (side d : ℕ)
    (rootM α β U γ η δ p₀ : ℚ) (u : Fin d → S → ℚ) (e : Fin d → Equiv.Perm S)
    (z : LowSpinData S d e (lowSpinPlanQ side d (Fintype.card S) rootM α β U γ η δ p₀)) :
    let p := lowSpinPlanQ side d (Fintype.card S) rootM α β U γ η δ p₀
    (executeLowSpinQ p u e α β U γ z).uniformSites=
      if p.velocity.norm.mode=.sampled then d*p.velocity.norm.queries else 0 := by
  let p := lowSpinPlanQ side d (Fintype.card S) rootM α β U γ η δ p₀
  have hN (j : Fin d) : (targetNormQueries p.velocity.norm.mode p.velocity.norm.records
      p.velocity.norm.blocks (z.1 j).2.2).length=p.velocity.norm.queries :=
    planned_norm_queries_length (β*U) (η/(8*(d : ℚ))) (δ/(4*(d : ℚ))) (z.1 j).2.2
  change (if p.velocity.norm.mode=.sampled then
    ∑ j : Fin d,(targetNormQueries p.velocity.norm.mode p.velocity.norm.records
      p.velocity.norm.blocks (z.1 j).2.2).length else 0)=_
  simp_rw [hN]
  simp [p]

/-- Complete original `executed_low_spin_bell_wire_account` guarantee for `LowSpinAccounting`; all source hypotheses and output obligations are retained. -/
theorem executed_low_spin_bell_wire_account [LinearOrder S] (p : LowSpinPlanQ)
    (u : Fin d → S → ℚ) (e : Fin d → Equiv.Perm S) (α β U γ : ℚ) (z : LowSpinData S d e p) :
    let r := executeLowSpinQ p u e α β U γ z
    r.copies=r.velocityCopies+bellReceiptSum (·.discards) r.spin+2*bellReceiptSum (·.bellTests) r.spin ∧
    bellReceiptSum (·.nativeBellGates) r.spin=2*bellReceiptSum (·.bellTests) r.spin ∧
    bellReceiptSum (·.nativeBellQueries) r.spin=0 := by
  have h := low_spin_bell_wire_account e p.spin z.2
  dsimp only [executeLowSpinQ,LowSpinReceiptQ.copies]
  rw [h.1]
  exact ⟨by omega,h.2⟩

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_spin_bell_wire_account
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_spin_bell_copy_sum
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_plan_geometric_copies
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_spin_plan_bell_consistency
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.executed_low_spin_copies
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.executed_low_spin_query_bound
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.executed_low_spin_uniform_sites
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.executed_low_spin_bell_wire_account


open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Matched ParameterEncoding

variable {S : Type} [Fintype S] [LinearOrder S] {d : ℕ}

omit [Fintype S] in
/-- Complete original `low_spin_bell_value_receipts` guarantee for `LowSpinAccounting`; all source hypotheses and output obligations are retained. -/
theorem low_spin_bell_value_receipts (e : Fin d → Equiv.Perm S) (γ : ℚ) (hγ : 0≤γ)
    (spin : Option BellPlanQ) (ω : LowSpinBellData S d e spin) :
    lowSpinBellValueQ e γ spin ω=intervalClipQ 0 (2*(d : ℚ)*γ)
      (4*γ*((lowSpinBellReceipts e spin ω).map (·.value)).sum) := by
  cases spin with
  | none =>
    have hhi : (0 : ℚ)≤2*(d : ℚ)*γ := by positivity
    simp only [lowSpinBellValueQ,lowSpinBellReceipts,List.map_nil,List.sum_nil,mul_zero,
      intervalClipQ,max_self,min_eq_right hhi]
  | some q =>
    simp only [lowSpinBellValueQ,lowSpinBellReceipts,List.map_ofFn,Function.comp_def,List.sum_ofFn]

/-- Complete original `executed_low_spin_value` guarantee for `LowSpinAccounting`; all source hypotheses and output obligations are retained. -/
theorem executed_low_spin_value (p : LowSpinPlanQ) (u : Fin d → S → ℚ)
    (e : Fin d → Equiv.Perm S) (α β U γ : ℚ) (hγ : 0≤γ) (z : LowSpinData S d e p) :
    let r := executeLowSpinQ p u e α β U γ z
    r.value=r.velocityValue+intervalClipQ 0 (2*(d : ℚ)*γ)
      (4*γ*(r.spin.map (·.value)).sum) := by
  change lowSpinVelocityValueQ p.velocity u α β U z.1+lowSpinBellValueQ e γ p.spin z.2=_
  rw [low_spin_bell_value_receipts e γ hγ p.spin z.2]
  rfl

-- The data-dependent receipt and literal plan are the ones used by the
-- statistical endpoint. The order supplies classical enumeration only.
/-- Complete original `executed_low_spin_original_guarantees` guarantee for `LowSpinAccounting`; all source hypotheses and output obligations are retained. -/
theorem executed_low_spin_original_guarantees {d r : ℕ}
    [LinearOrder (Fin d → Fin (2^r))]
    (κ lam U η δ eb p₀ : ℚ) (coef : CoefficientCandidateQ)
    (hc : coefficientsGeneratedQ d (2^r) κ lam U η=some coef)
    (hd : 0<d) (hκ : 0<κ) (hU : 0≤U) (hη : 0<η) (hδ : 0<δ) (hδ1 : δ<1)
    (heb0 : 0≤eb) (heb : eb≤coef.maxTargetError)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → (Fin d → Fin (2^r)) → ℝ) (û : Fin d → (Fin d → Fin (2^r)) → ℚ)
    (hu : ∀ j x, |u j x|≤(U : ℝ)) (htarget : ∀ j x, |(û j x : ℝ)-u j x|≤(eb : ℝ))
    (hp : 0≤p₀) (hp1 : p₀≤1/2)
    (hmean : coef.gamma≠0 → ∀ j,bellMean a b c k (periodicDoubleShift d (2^r) j)≤(p₀ : ℝ)) :
    let p := lowSpinPlanQ (2^r) d (2^(d*r)) ((2^((d*r+1)/2) : ℕ) : ℚ)
      coef.alpha coef.beta (U+eb) coef.gamma η δ p₀
    (∀ z : LowSpinData (Fin d → Fin (2^r)) d (periodicDoubleShift d (2^r)) p,
      let out := executeLowSpinQ p û (periodicDoubleShift d (2^r))
        coef.alpha coef.beta (U+eb) coef.gamma z
      out.copies=p.copies ∧ out.targetQueries≤p.targetQueries ∧
        out.uniformSites=(if p.velocity.norm.mode=.sampled then d*p.velocity.norm.queries else 0)) ∧
    finiteBadMass (nativeLowSpinLaw d r p a b c k hz)
      (fun z => ((executeLowSpinQ p û (periodicDoubleShift d (2^r))
        coef.alpha coef.beta (U+eb) coef.gamma z).value : ℝ))
      (spinorDiscreteLoss a b c k u (periodicUnitShift d (2^r))
        (2*Real.pi/((2^r : ℕ) : ℝ)) (κ : ℝ) (lam : ℝ)) (η : ℝ)≤(δ : ℝ) := by
  let rootM : ℚ := ((2^((d*r+1)/2) : ℕ) : ℚ)
  let e := periodicDoubleShift d (2^r)
  have hledger (z : LowSpinData (Fin d → Fin (2^r)) d e
      (lowSpinPlanQ (2^r) d (Fintype.card (Fin d → Fin (2^r))) rootM
        coef.alpha coef.beta (U+eb) coef.gamma η δ p₀)) :=
    And.intro
      (executed_low_spin_copies (2^r) d rootM coef.alpha coef.beta (U+eb) coef.gamma η δ p₀ û e z)
      (And.intro
        (executed_low_spin_query_bound (2^r) d rootM coef.alpha coef.beta (U+eb) coef.gamma η δ p₀ û e z)
        (executed_low_spin_uniform_sites (2^r) d rootM coef.alpha coef.beta (U+eb) coef.gamma η δ p₀ û e z))
  rw [grid_cardinality] at hledger
  exact ⟨hledger,generated_low_spin_original_accuracy κ lam U η δ eb p₀ coef hc hd hκ hU hη
    hδ hδ1 heb0 heb a b c k hz u û hu htarget hp hp1 hmean⟩

/-- Complete original `executed_enclosed_low_spin_original_accuracy` guarantee for `LowSpinAccounting`; all source hypotheses and output obligations are retained. -/
theorem executed_enclosed_low_spin_original_accuracy {d r : ℕ}
    [LinearOrder (Fin d → Fin (2^r))] (box : PhysicalBoxQ) (U η0 δ0 eb p₀ : ℚ)
    (κ lam η δ : ℝ) (coef : CoefficientCandidateQ)
    (hc : coefficientsGeneratedQ d (2^r) (kappaApproxQ box) (lambdaApproxQ box) U (η0/2)=some coef)
    (hd : 0<d) (hklo : 0<box.kappa.lo) (hU : 0≤U) (hη0 : 0<η0) (hδ0 : 0<δ0) (hδ01 : δ0<1)
    (heb0 : 0≤eb) (heb : eb≤coef.maxTargetError)
    (hκlo : (box.kappa.lo : ℝ)≤κ) (hκhi : κ≤(box.kappa.hi : ℝ))
    (hlam0 : 0≤lam) (hlamlo : (box.lambda.lo : ℝ)≤lam) (hlamhi : lam≤(box.lambda.hi : ℝ))
    (hbudget : parameterBiasQ d r U box≤η0/2) (hη : (η0 : ℝ)≤η) (hδ : (δ0 : ℝ)≤δ)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → (Fin d → Fin (2^r)) → ℝ) (û : Fin d → (Fin d → Fin (2^r)) → ℚ)
    (hu : ∀ j x, |u j x|≤(U : ℝ)) (htarget : ∀ j x, |(û j x : ℝ)-u j x|≤(eb : ℝ))
    (hp : 0≤p₀) (hp1 : p₀≤1/2)
    (hmean : coef.gamma≠0 → ∀ j,bellMean a b c k (periodicDoubleShift d (2^r) j)≤(p₀ : ℝ)) :
    let p := lowSpinPlanQ (2^r) d (2^(d*r)) ((2^((d*r+1)/2) : ℕ) : ℚ)
      coef.alpha coef.beta (U+eb) coef.gamma (η0/2) δ0 p₀
    finiteBadMass (nativeLowSpinLaw d r p a b c k hz)
      (fun z => ((executeLowSpinQ p û (periodicDoubleShift d (2^r))
        coef.alpha coef.beta (U+eb) coef.gamma z).value : ℝ))
      (spinorDiscreteLoss a b c k u (periodicUnitShift d (2^r))
        (2*Real.pi/((2^r : ℕ) : ℝ)) κ lam) η≤δ :=
  enclosed_low_spin_original_accuracy box U η0 δ0 eb p₀ κ lam η δ coef hc hd hklo hU hη0
    hδ0 hδ01 heb0 heb hκlo hκhi hlam0 hlamlo hlamhi hbudget hη hδ
    a b c k hz u û hu htarget hp hp1 hmean

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_spin_bell_value_receipts
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.executed_low_spin_value
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.executed_low_spin_original_guarantees
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.executed_enclosed_low_spin_original_accuracy


set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open scoped BigOperators
open Matched

variable {S : Type} [DecidableEq S] {d : ℕ}

-- Evaluate the already proved counters without evaluating Classical.choose
-- in the analysis-only enumeration of selected physical wires. The equality
/-- theorem below identifies every field with the actual native-word receipt. -/
def executeBellExecutableQ (q : BellPlanQ) (τ : Equiv.Perm S)
    (ω : Fin q.blocks → CohortObservation q.records q.records τ) : PlannedBellReceiptQ where
  value := plannedBellMeanQ q τ ω
  copies := q.blocks*(q.records+q.records)
  discards := q.blocks*(q.records+q.records)-2*pooledMatches τ ω
  bellTests := pooledMatches τ ω
  nativeBellGates := 2*pooledMatches τ ω
  nativeBellQueries := 0

noncomputable section

/-- Complete original `bell_executable_eq` guarantee for `LowSpinAccounting`; all source hypotheses and output obligations are retained. -/
theorem bell_executable_eq (q : BellPlanQ) (τ : Equiv.Perm S)
    (ω : Fin q.blocks → CohortObservation q.records q.records τ) :
    executeBellExecutableQ q τ ω=executePlannedBellQ q τ ω := by
  have hd := observed_discard_account τ ω
  rw [captured_address_records_length] at hd
  have hsub : q.blocks*(q.records+q.records)-2*pooledMatches τ ω=observedDiscardCount τ ω := by
    omega
  have hg := (observed_native_bell_account τ ω).1
  have hq := (observed_native_bell_account τ ω).2
  simp only [executeBellExecutableQ,executePlannedBellQ,captured_address_records_length,hsub,hg,hq]

end

/-- Construction for low Spin Bell Executable Receipts in the low spin accounting model. -/
def lowSpinBellExecutableReceipts (e : Fin d → Equiv.Perm S) (spin : Option BellPlanQ) :
    LowSpinBellData S d e spin → List PlannedBellReceiptQ :=
  match spin with
  | none => fun _ => []
  | some q => fun ω => List.ofFn (fun j : Fin d => executeBellExecutableQ q (e j) (ω j))

/-- Construction for low Spin Bell Executable Value Q in the low spin accounting model. -/
def lowSpinBellExecutableValueQ (e : Fin d → Equiv.Perm S) (γ : ℚ) (spin : Option BellPlanQ) :
    LowSpinBellData S d e spin → ℚ :=
  match spin with
  | none => fun _ => 0
  | some q => fun ω => intervalClipQ 0 (2*(d : ℚ)*γ)
      (4*γ*(∑ j : Fin d,(executeBellExecutableQ q (e j) (ω j)).value))

variable [Fintype S] [LinearOrder S]

/-- Construction for execute Low Spin Executable Q in the low spin accounting model. -/
def executeLowSpinExecutableQ (p : LowSpinPlanQ) (u : Fin d → S → ℚ)
    (e : Fin d → Equiv.Perm S) (α β U γ : ℚ) (z : LowSpinData S d e p) : LowSpinReceiptQ where
  value := lowSpinVelocityValueQ p.velocity u α β U z.1+lowSpinBellExecutableValueQ e γ p.spin z.2
  velocityValue := lowSpinVelocityValueQ p.velocity u α β U z.1
  velocityCopies := ∑ j : Fin d,(lowSpinVelocityRecords p e z j).length
  targetQueries := ∑ j : Fin d,(lowSpinTargetQueries p e z j).length
  uniformSites := if p.velocity.norm.mode=.sampled then
    ∑ j : Fin d,(targetNormQueries p.velocity.norm.mode p.velocity.norm.records
      p.velocity.norm.blocks (z.1 j).2.2).length else 0
  spin := lowSpinBellExecutableReceipts e p.spin z.2

noncomputable section

omit [Fintype S] [LinearOrder S] in
/-- Complete original `low_spin_bell_executable_receipts_eq` guarantee for `LowSpinAccounting`; all source hypotheses and output obligations are retained. -/
theorem low_spin_bell_executable_receipts_eq (e : Fin d → Equiv.Perm S) (spin : Option BellPlanQ)
    (ω : LowSpinBellData S d e spin) :
    lowSpinBellExecutableReceipts e spin ω=lowSpinBellReceipts e spin ω := by
  cases spin with
  | none => rfl
  | some q =>
    simp only [lowSpinBellExecutableReceipts,lowSpinBellReceipts]
    congr 1
    funext j
    exact bell_executable_eq q (e j) (ω j)

omit [Fintype S] [LinearOrder S] in
/-- Complete original `low_spin_bell_executable_value_eq` guarantee for `LowSpinAccounting`; all source hypotheses and output obligations are retained. -/
theorem low_spin_bell_executable_value_eq (e : Fin d → Equiv.Perm S) (γ : ℚ) (spin : Option BellPlanQ)
    (ω : LowSpinBellData S d e spin) :
    lowSpinBellExecutableValueQ e γ spin ω=lowSpinBellValueQ e γ spin ω := by
  cases spin <;> rfl

/-- Complete original `low_spin_executable_eq` guarantee for `LowSpinAccounting`; all source hypotheses and output obligations are retained. -/
theorem low_spin_executable_eq (p : LowSpinPlanQ) (u : Fin d → S → ℚ)
    (e : Fin d → Equiv.Perm S) (α β U γ : ℚ) (z : LowSpinData S d e p) :
    executeLowSpinExecutableQ p u e α β U γ z=executeLowSpinQ p u e α β U γ z := by
  simp only [executeLowSpinExecutableQ,executeLowSpinQ,lowSpinOutputQ,
    low_spin_bell_executable_value_eq,low_spin_bell_executable_receipts_eq]

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_executable_eq
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_spin_bell_executable_receipts_eq
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_spin_bell_executable_value_eq
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_spin_executable_eq
