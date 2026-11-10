/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryAlgorithm
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.ResourceDerivation
import Qatlib.Foundations.PureStateMath.BornBridge.BornDistribution
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDistTV
import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsTransportImplBounds
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceSearchBounds
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
import Qatlib.Concepts.QueryComplexity.AdversarySearch.CountedParityAlgorithm
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBounds
open Matrix
open scoped Classical BigOperators ENNReal
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

variable {J Out X : Type} [Fintype J] [DecidableEq J] [Fintype Out] [DecidableEq Out]

structure MeasuredProgram (J Out : Type) [Fintype J] [DecidableEq J] where
  algorithm : QueryAlgorithm J
  readout : J→Out

structure OracleAccess (X J : Type) [Fintype J] [DecidableEq J] where
  oracle : X→Matrix J J ℂ
  unitary : ∀ x, oracle x ∈ Matrix.unitaryGroup J ℂ

def meteredRun (oracle : Matrix J J ℂ) : Circuit J→QState J→QState J×ResourceCost
  | [],ψ => (ψ,0)
  | .gate U::C,ψ =>
    let next := meteredRun oracle C (ApplyGate U ψ)
    (next.1,ResourceCost.ofMacroStep StepProfile.zero+next.2)
  | .query::C,ψ =>
    let next := meteredRun oracle C (ApplyGate oracle ψ)
    (next.1,ResourceCost.ofOracleStep+next.2)

omit [DecidableEq J] [Fintype Out] [DecidableEq Out] in

theorem meteredRun_projection (oracle : Matrix J J ℂ) (C : Circuit J) (ψ : QState J) :
    meteredRun oracle C ψ=(Run oracle C ψ,derive (fun _ => StepProfile.zero) C) := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih => cases s <;> simp [meteredRun,Run,derive,ih]

def runLaw (P : MeasuredProgram J Out) (A : OracleAccess X J) (x : X) : PMF Out :=
  (bornDistribution (Run (A.oracle x) P.algorithm.circuit P.algorithm.start)
    (P.algorithm.normalized_output (A.unitary x))).map P.readout

def realLaw {Y : Type} [Fintype Y] (p : PMF Y) : FinDist Y where
  prob y := (p y).toReal
  nonneg y := ENNReal.toReal_nonneg
  sum_one := by
    have h := congrArg ENNReal.toReal p.tsum_coe
    rw [tsum_fintype,ENNReal.toReal_sum (fun y _ => p.apply_ne_top y),ENNReal.toReal_one] at h
    exact h

def eventProb {Y : Type} [Fintype Y] (p : FinDist Y) (E : Y→Prop) : ℝ :=
  p.expect (fun y => if E y then 1 else 0)

def outputError {Y : Type} [Fintype Y] [DecidableEq Y] (p q : FinDist Y) : ℝ := 2*tvDist p q

theorem eventProb_nonneg {Y : Type} [Fintype Y] (p : FinDist Y) (E : Y→Prop) :
    0≤eventProb p E := by
  unfold eventProb FinDist.expect
  exact Finset.sum_nonneg
      (fun y _ => mul_nonneg (p.nonneg y) (by (try dsimp only); split_ifs <;> norm_num))

theorem eventProb_le_one {Y : Type} [Fintype Y] (p : FinDist Y) (E : Y→Prop) :
    eventProb p E≤1 := by
  rw [← p.sum_one]
  unfold eventProb FinDist.expect
  apply Finset.sum_le_sum
  intro y _
  (try dsimp only)
  by_cases he : E y
  · simp [he]
  · simpa [he] using! p.nonneg y

theorem eventProb_true {Y : Type} [Fintype Y] (p : FinDist Y) :
    eventProb p (fun _ => True)=1 := by
  simpa [eventProb,FinDist.expect] using! p.sum_one

theorem eventProb_difference {Y : Type} [Fintype Y] [DecidableEq Y]
    (p q : FinDist Y) (E : Y→Prop) : |eventProb p E-eventProb q E|≤outputError p q :=
  Qatlib.Concepts.MonteCarloMean.FinDistBounds.expect_sub_tvDist p q _ (fun _ => by split_ifs <;> norm_num)
    (fun _ => by split_ifs <;> norm_num)

theorem outputError_triangle {Y : Type} [Fintype Y] [DecidableEq Y]
    (p q r : FinDist Y) : outputError p r≤outputError p q+outputError q r := by
  simp only [outputError,Qatlib.Concepts.MonteCarloMean.FinDistBounds.tvDist]
  have h := Finset.sum_le_sum (s:=Finset.univ)
    (fun y _ => abs_sub_le (p.prob y) (q.prob y) (r.prob y))
  rw [Finset.sum_add_distrib] at h
  nlinarith

theorem outputError_self {Y : Type} [Fintype Y] [DecidableEq Y] (p : FinDist Y) :
    outputError p p=0 := by simp [outputError,Qatlib.Concepts.MonteCarloMean.FinDistBounds.tvDist]

def pointMass {Y : Type} [Fintype Y] (v : Y) : FinDist Y := realLaw (PMF.pure v)

theorem pointMass_prob {Y : Type} [Fintype Y] [DecidableEq Y] (v y : Y) :
    (pointMass v).prob y=if y=v then 1 else 0 := by
  by_cases he : y=v
  · subst y
    simp [pointMass,realLaw,PMF.pure_apply]
  · simp [pointMass,realLaw,PMF.pure_apply,he]

theorem eventProb_point {Y : Type} [Fintype Y] [DecidableEq Y] (p : FinDist Y) (v : Y) :
    eventProb p (fun y => y=v)=p.prob v := by
  simp [eventProb,FinDist.expect,mul_ite]

theorem outputError_pointMass {Y : Type} [Fintype Y] [DecidableEq Y] (p : FinDist Y) (v : Y) :
    outputError p (pointMass v)=2*(1-p.prob v) := by
  have hp : p.prob v≤1 := by
    rw [← p.sum_one]
    exact Finset.single_le_sum (fun y _ => p.nonneg y) (Finset.mem_univ v)
  have hrest : (∑ y ∈ Finset.univ.erase v, |p.prob y-(pointMass v).prob y|)=
      ∑ y ∈ Finset.univ.erase v, p.prob y := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [pointMass_prob,if_neg (Finset.mem_erase.mp hy).1,sub_zero,abs_of_nonneg (p.nonneg y)]
  have hs := Finset.add_sum_erase Finset.univ
    (fun y => |p.prob y-(pointMass v).prob y|) (Finset.mem_univ v)
  (try dsimp only at hs)
  rw [hrest,pointMass_prob,if_pos rfl,abs_of_nonpos (sub_nonpos.mpr hp)] at hs
  have hm := Finset.add_sum_erase Finset.univ p.prob (Finset.mem_univ v)
  rw [p.sum_one] at hm
  simp only [outputError,Qatlib.Concepts.MonteCarloMean.FinDistBounds.tvDist]
  linarith

omit [Fintype Out] in

theorem runLaw_point (P : MeasuredProgram J Out) (A : OracleAccess X J) (x : X) (y : Out) :
    runLaw P A x y = ENNReal.ofReal (MeasureProb
      (Run (A.oracle x) P.algorithm.circuit P.algorithm.start)
      (Finset.univ.filter (fun j => P.readout j=y))) := by
  unfold runLaw
  rw [PMF.map_apply,tsum_fintype]
  rw [← bornDistribution_event _ (P.algorithm.normalized_output (A.unitary x)) _]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases he : y=P.readout j <;> simp [he,eq_comm]

theorem runLaw_event (P : MeasuredProgram J Out) (A : OracleAccess X J) (x : X) (E : Out→Prop) :
    eventProb (realLaw (runLaw P A x)) E = MeasureProb
      (Run (A.oracle x) P.algorithm.circuit P.algorithm.start)
      (Finset.univ.filter (fun j => E (P.readout j))) := by
  have h (y : Out) := runLaw_point P A x y
  unfold eventProb FinDist.expect realLaw
  simp only
  simp_rw [h,ENNReal.toReal_ofReal (measureProb_nonneg _ _)]
  simp only [MeasureProb,Finset.sum_filter]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ite_mul,zero_mul]
  simp

structure Budget where
  queries : ℕ
  macroGates : ℕ
  depth : ℕ
  deriving DecidableEq, Repr

def ledger (P : MeasuredProgram J Out) : ResourceCost :=
  derive (fun _ => StepProfile.zero) P.algorithm.circuit

def executionLaw (P : MeasuredProgram J Out) (A : OracleAccess X J) (x : X) : PMF (Out×ResourceCost) :=
  let executed := meteredRun (A.oracle x) P.algorithm.circuit P.algorithm.start
  let hnorm : Normalized executed.1 := by
    dsimp only [executed]
    rw [meteredRun_projection]
    exact P.algorithm.normalized_output (A.unitary x)
  (bornDistribution executed.1 hnorm).map (fun j => (P.readout j,executed.2))

omit [Fintype Out] [DecidableEq Out] in

theorem executionLaw_eq (P : MeasuredProgram J Out) (A : OracleAccess X J) (x : X) :
    executionLaw P A x=(runLaw P A x).map (fun y => (y,ledger P)) := by
  simp only [executionLaw,meteredRun_projection,runLaw,PMF.map_comp,Function.comp_def,ledger]

omit [Fintype Out] [DecidableEq Out] in

theorem executionLaw_output (P : MeasuredProgram J Out) (A : OracleAccess X J) (x : X) :
    (executionLaw P A x).map Prod.fst=runLaw P A x := by
  rw [executionLaw_eq,PMF.map_comp]
  exact PMF.map_id _

omit [Fintype Out] [DecidableEq Out] in

theorem executionLaw_cost (P : MeasuredProgram J Out) (A : OracleAccess X J) (x : X)
    (z : Out×ResourceCost) (hz : z∈(executionLaw P A x).support) : z.2=ledger P := by
  rw [executionLaw_eq,PMF.mem_support_map_iff] at hz
  obtain ⟨y,_,hy⟩ := hz
  exact (congrArg Prod.snd hy).symm

def Within (P : MeasuredProgram J Out) (B : Budget) : Prop :=
  (ledger P).queries≤B.queries ∧ (ledger P).macroGates≤B.macroGates ∧ (ledger P).depth≤B.depth

omit [Fintype Out] [DecidableEq Out] in

theorem within_iff (P : MeasuredProgram J Out) (B : Budget) : Within P B ↔
    QueryCount P.algorithm.circuit≤B.queries ∧ GateCount P.algorithm.circuit≤B.macroGates ∧
      Size P.algorithm.circuit≤B.depth := by
  simp only [Within,ledger,derive_queries,derive_macroGates,derive_depth]

structure DistributionTask (X Out : Type) [Fintype Out] where
  legal : X→Prop
  target : X→FinDist Out
  good : X→Out→Prop
  error : X→ℝ
  failure : X→ℝ

def Implements (P : MeasuredProgram J Out) (A : OracleAccess X J)
    (T : DistributionTask X Out) (B : Budget) : Prop :=
  Within P B ∧ ∀ x, T.legal x →
    outputError (realLaw (runLaw P A x)) (T.target x)≤T.error x ∧
      1-T.failure x≤eventProb (realLaw (runLaw P A x)) (T.good x)

theorem implements_exact_counts (P : MeasuredProgram J Out) (A : OracleAccess X J)
    (T : DistributionTask X Out) (B : Budget) (h : Implements P A T B) :
    QueryCount P.algorithm.circuit≤B.queries ∧ GateCount P.algorithm.circuit≤B.macroGates ∧
      Size P.algorithm.circuit≤B.depth := (within_iff P B).mp h.1

theorem implements_transport {K : Type} [Fintype K] [DecidableEq K]
    (P : MeasuredProgram J Out) (Q : MeasuredProgram K Out)
    (A : OracleAccess X J) (A' : OracleAccess X K) (T : DistributionTask X Out) (B : Budget)
    (hlaw : ∀ x, runLaw Q A' x=runLaw P A x)
    (hq : (ledger Q).queries≤(ledger P).queries)
    (hg : (ledger Q).macroGates≤(ledger P).macroGates)
    (hd : (ledger Q).depth≤(ledger P).depth)
    (h : Implements P A T B) : Implements Q A' T B := by
  refine ⟨⟨hq.trans h.1.1,hg.trans h.1.2.1,hd.trans h.1.2.2⟩,?_⟩
  intro x hx
  rw [hlaw]
  exact h.2 x hx

def relax (T : DistributionTask X Out) (δ : X→ℝ) : DistributionTask X Out :=
  { T with error := fun x => T.error x+δ x, failure := fun x => T.failure x+δ x }

theorem implements_approximate {K : Type} [Fintype K] [DecidableEq K]
    (P : MeasuredProgram J Out) (Q : MeasuredProgram K Out)
    (A : OracleAccess X J) (A' : OracleAccess X K) (T : DistributionTask X Out)
    (B B' : Budget) (δ : X→ℝ) (h : Implements P A T B) (hbudget : Within Q B')
    (hdist : ∀ x, T.legal x → outputError (realLaw (runLaw Q A' x)) (realLaw (runLaw P A x))≤δ x) :
    Implements Q A' (relax T δ) B' := by
  refine ⟨hbudget,?_⟩
  intro x hx
  have hp := h.2 x hx
  have hδ := hdist x hx
  constructor
  · have ht := outputError_triangle (realLaw (runLaw Q A' x)) (realLaw (runLaw P A x)) (T.target x)
    change outputError (realLaw (runLaw Q A' x)) (T.target x)≤T.error x+δ x
    linarith [hp.1]
  · have he := (eventProb_difference (realLaw (runLaw Q A' x)) (realLaw (runLaw P A x))
      (T.good x)).trans hδ
    have hl := (abs_sub_le_iff.mp he).2
    change 1-(T.failure x+δ x)≤eventProb (realLaw (runLaw Q A' x)) (T.good x)
    linarith [hp.2]

def QueryLower (A : OracleAccess X J) (T : DistributionTask X Out) (bound : ℕ) : Prop :=
  ∀ P : MeasuredProgram J Out, (∃ B, Implements P A T B) → bound≤(ledger P).queries

theorem budget_lower (A : OracleAccess X J) (T : DistributionTask X Out) (bound : ℕ)
    (h : QueryLower A T bound) (P : MeasuredProgram J Out) (B : Budget)
    (hp : Implements P A T B) : bound≤B.queries :=
  (h P ⟨B,hp⟩).trans hp.1.1

theorem queryLower_exact_transport {K : Type} [Fintype K] [DecidableEq K]
    (A : OracleAccess X J) (A' : OracleAccess X K) (T : DistributionTask X Out) (bound : ℕ)
    (h : QueryLower A T bound)
    (refineProgram : MeasuredProgram K Out→MeasuredProgram J Out)
    (hlaw : ∀ Q x, runLaw (refineProgram Q) A x=runLaw Q A' x)
    (hquery : ∀ Q, (ledger (refineProgram Q)).queries≤(ledger Q).queries) :
    QueryLower A' T bound := by
  intro Q hQ
  obtain ⟨B,hB⟩ := hQ
  let R := refineProgram Q
  let BR : Budget := ⟨(ledger R).queries,(ledger R).macroGates,(ledger R).depth⟩
  have hr : Implements R A T BR := by
    refine ⟨⟨le_rfl,le_rfl,le_rfl⟩,?_⟩
    intro x hx
    dsimp only [R]
    rw [hlaw]
    exact hB.2 x hx
  exact (h R ⟨BR,hr⟩).trans (hquery Q)

theorem eventProb_disjoint {Y : Type} [Fintype Y] (p : FinDist Y) (E F : Y→Prop)
    (h : ∀ y, ¬(E y ∧ F y)) : eventProb p E+eventProb p F≤1 := by
  unfold eventProb FinDist.expect
  rw [← Finset.sum_add_distrib]
  conv_rhs => rw [← p.sum_one]
  apply Finset.sum_le_sum
  intro y _
  (try dsimp only)
  by_cases he : E y <;> by_cases hf : F y
  · exact (h y ⟨he,hf⟩).elim
  · simp [he,hf]
  · simp [he,hf]
  · simpa [he,hf] using! p.nonneg y

def Distinguishing (T : DistributionTask X Out) : Prop :=
  ∃ a b, T.legal a ∧ T.legal b ∧ (∀ y, ¬(T.good a y ∧ T.good b y)) ∧
    T.failure a+T.failure b<1

theorem constant_law_not_implements (P : MeasuredProgram J Out) (A : OracleAccess X J)
    (T : DistributionTask X Out) (B : Budget) (p : PMF Out)
    (hconst : ∀ x, runLaw P A x=p) (hnt : Distinguishing T) : ¬Implements P A T B := by
  intro h
  obtain ⟨a,b,ha,hb,hd,hf⟩ := hnt
  have hpa := (h.2 a ha).2
  have hpb := (h.2 b hb).2
  rw [hconst] at hpa hpb
  have hp := eventProb_disjoint (realLaw p) (T.good a) (T.good b) hd
  linarith

omit [Fintype Out] [DecidableEq Out] in

theorem zero_query_law (P : MeasuredProgram J Out) (A : OracleAccess X J)
    (hq : QueryCount P.algorithm.circuit=0) (a b : X) : runLaw P A a=runLaw P A b := by
  unfold runLaw
  congr 1
  apply PMF.ext
  intro j
  simp only [bornDistribution_apply,
    run_eq_of_queryCount_eq_zero (A.oracle a) (A.oracle b) P.algorithm.circuit hq P.algorithm.start]

theorem zero_query_not_implements (P : MeasuredProgram J Out) (A : OracleAccess X J)
    (T : DistributionTask X Out) (B : Budget) (hq : QueryCount P.algorithm.circuit=0)
    (hnt : Distinguishing T) : ¬Implements P A T B := by
  obtain ⟨a,b,ha,hb,hd,hf⟩ := hnt
  exact constant_law_not_implements P A T B (runLaw P A a)
    (fun x => zero_query_law P A hq x a) ⟨a,b,ha,hb,hd,hf⟩

omit [Fintype Out] [DecidableEq Out] in

theorem constant_readout_law (P : MeasuredProgram J Out) (A : OracleAccess X J)
    (v : Out) (h : ∀ j, P.readout j=v) (x : X) : runLaw P A x=PMF.pure v := by
  have he : P.readout=Function.const J v := funext h
  unfold runLaw
  rw [he,PMF.map_const]

theorem constant_readout_not_implements (P : MeasuredProgram J Out) (A : OracleAccess X J)
    (T : DistributionTask X Out) (B : Budget) (v : Out) (h : ∀ j, P.readout j=v)
    (hnt : Distinguishing T) : ¬Implements P A T B :=
  constant_law_not_implements P A T B (PMF.pure v) (constant_readout_law P A v h) hnt

def idleProgram (ψ : QState J) (hψ : Normalized ψ) (readout : J→Out) : MeasuredProgram J Out where
  algorithm := ⟨[],ψ,by simp [IsUnitaryCircuit],hψ⟩
  readout := readout

def idleTask (ψ : QState J) (hψ : Normalized ψ) (readout : J→Out) : DistributionTask X Out where
  legal _ := True
  target _ := realLaw ((bornDistribution ψ hψ).map readout)
  good _ _ := True
  error _ := 0
  failure _ := 0

theorem idle_implements (ψ : QState J) (hψ : Normalized ψ) (readout : J→Out)
    (A : OracleAccess X J) :
    Implements (idleProgram ψ hψ readout) A (idleTask ψ hψ readout) ⟨0,0,0⟩ := by
  refine ⟨(within_iff _ _).mpr ⟨le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro x _
  have hraw : runLaw (idleProgram ψ hψ readout) A x=(bornDistribution ψ hψ).map readout := rfl
  simp [idleTask,hraw,outputError_self,eventProb_true]

namespace Search

variable {W : Type} [Fintype W] [DecidableEq W]

def searchProgram (n : ℕ) (w : W) (hn : 2 ≤ n) :
    MeasuredProgram ((Reg n × Bool) × W) (Reg n) where
  algorithm :=
    { circuit := workspaceGroverCircuit (W := W) n (singletonSearchIterations n)
      start := Qatlib.Foundations.PureStateMath.Ket ((ZeroStr n, false), w)
      unitary :=
        (workspace_singleton_search_actual_upper (W := W) n w (ZeroStr n) hn).2.2.2.2.1
      normalized := normalized_ket _ }
  readout := fun j => j.1.1

def searchAccess (n : ℕ) : OracleAccess (Reg n) ((Reg n × Bool) × W) where
  oracle x := workspaceBitOracle (W := W) (fun y : Reg n => decide (y = x))
  unitary _ := workspaceBitOracle_unitary _

def searchTask (n : ℕ) : DistributionTask (Reg n) (Reg n) where
  legal _ := True
  target x := pointMass x
  good x y := y = x
  error _ := 2 / (Fintype.card (Reg n) : ℝ)
  failure _ := 1 / (Fintype.card (Reg n) : ℝ)

def searchNativeBudget (n : ℕ) : Budget where
  queries := singletonSearchIterations n
  macroGates := 3 * singletonSearchIterations n + 3
  depth := 4 * singletonSearchIterations n + 3

theorem search_counts (n : ℕ) (w : W) (hn : 2 ≤ n) :
    QueryCount (searchProgram n w hn).algorithm.circuit = singletonSearchIterations n ∧
    GateCount (searchProgram n w hn).algorithm.circuit =
      3 * singletonSearchIterations n + 3 ∧
    Size (searchProgram n w hn).algorithm.circuit =
      4 * singletonSearchIterations n + 3 := by
  rcases workspace_grover_bit_semantics_and_cost (W := W) n
      (singletonSearchIterations n) w (fun _ => false) with ⟨_, hq, hg, _⟩
  change QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) =
      singletonSearchIterations n ∧
    GateCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) =
      3 * singletonSearchIterations n + 3 ∧
    Size (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) =
      4 * singletonSearchIterations n + 3
  refine ⟨hq, hg, ?_⟩
  rw [size_eq_gateCount_add_queryCount, hg, hq]
  omega

theorem search_within (n : ℕ) (w : W) (hn : 2 ≤ n) :
    Within (searchProgram n w hn) (searchNativeBudget n) := by
  apply (within_iff _ _).2
  rcases search_counts n w hn with ⟨hq, hg, hd⟩
  exact ⟨hq.le, hg.le, hd.le⟩

theorem search_success (n : ℕ) (w : W) (hn : 2 ≤ n) (x : Reg n) :
    1 - 1 / (Fintype.card (Reg n) : ℝ) ≤
      eventProb (realLaw (runLaw (searchProgram n w hn) (searchAccess (W := W) n) x))
        (fun y => y = x) := by
  rw [runLaw_event]
  simpa only [searchProgram,searchAccess,workspaceQueryFiber] using!
    (workspace_singleton_search_actual_upper (W := W) n w x hn).1

theorem search_implements (n : ℕ) (w : W) (hn : 2 ≤ n) :
    Implements (searchProgram n w hn) (searchAccess (W := W) n)
      (searchTask n) (searchNativeBudget n) := by
  refine ⟨search_within n w hn, ?_⟩
  intro x _
  let p : FinDist (Reg n) :=
    realLaw (runLaw (searchProgram n w hn) (searchAccess (W := W) n) x)
  change outputError p (pointMass x) ≤ 2 / (Fintype.card (Reg n) : ℝ) ∧
    1 - 1 / (Fintype.card (Reg n) : ℝ) ≤ eventProb p (fun y => y = x)
  have hs : 1 - 1 / (Fintype.card (Reg n) : ℝ) ≤
      eventProb p (fun y => y = x) := search_success n w hn x
  have hp := hs
  rw [eventProb_point] at hp
  refine ⟨?_, hs⟩
  rw [outputError_pointMass]
  have hq : 1-p.prob x≤1/(Fintype.card (Reg n) : ℝ) := by linarith
  convert! mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ)≤2) using 1
  ring

theorem search_uniform_sqrt (n : ℕ) (w : W) (hn : 2 ≤ n) :
    ((ledger (searchProgram n w hn)).queries : ℝ) ≤
      Real.pi * Real.sqrt (Fintype.card (Reg n) : ℝ) / 4 := by
  simpa only [ledger, derive_queries, searchProgram] using!
    (workspace_singleton_search_actual_upper (W := W) n w (ZeroStr n) hn).2.1

theorem actual_search_implementation_and_bound (n : ℕ) (w : W) (hn : 2 ≤ n) :
    Implements (searchProgram n w hn) (searchAccess (W := W) n)
        (searchTask n) (searchNativeBudget n) ∧
      ((ledger (searchProgram n w hn)).queries : ℝ) ≤
        Real.pi * Real.sqrt (Fintype.card (Reg n) : ℝ) / 4 :=
  ⟨search_implements n w hn, search_uniform_sqrt n w hn⟩

theorem search_uniform_family (w : W) :
    ∃ c : ℝ, 0<c ∧ ∀ (n : ℕ) (hn : 2≤n),
      Implements (searchProgram n w hn) (searchAccess (W:=W) n) (searchTask n) (searchNativeBudget n) ∧
      ((ledger (searchProgram n w hn)).queries : ℝ)≤c*Real.sqrt (Fintype.card (Reg n) : ℝ) := by
  refine ⟨Real.pi/4,div_pos Real.pi_pos (by norm_num),?_⟩
  intro n hn
  refine ⟨search_implements n w hn,?_⟩
  convert! search_uniform_sqrt n w hn using 1
  ring

theorem search_distinguishing (n : ℕ) (hn : 2≤n) : Distinguishing (searchTask n) := by
  let a : Reg n := fun _ => false
  let b : Reg n := fun _ => true
  have hab : a≠b := by
    intro he
    have hh := congrFun he (⟨0,by omega⟩ : Fin n)
    exact Bool.false_ne_true hh
  have hN : (4:ℝ)≤(Fintype.card (Reg n) : ℝ) := by
    rw [card_reg n]
    have hp : (2:ℕ)^2≤2^n := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hn
    exact_mod_cast hp
  have hinv : 1/(Fintype.card (Reg n) : ℝ)≤1/4 :=
    one_div_le_one_div_of_le (by norm_num : (0:ℝ)<4) hN
  refine ⟨a,b,trivial,trivial,?_,?_⟩
  · intro y hy
    exact hab (hy.1.symm.trans hy.2)
  · change 1/(Fintype.card (Reg n) : ℝ)+1/(Fintype.card (Reg n) : ℝ)<1
    linarith

theorem search_nonzero_query (n : ℕ) (w : W) (hn : 2≤n) :
    1≤(ledger (searchProgram n w hn)).queries := by
  by_contra hq
  have hzero : QueryCount (searchProgram n w hn).algorithm.circuit=0 := by
    have hh : (ledger (searchProgram n w hn)).queries=0 := by omega
    simpa only [ledger,derive_queries] using! hh
  exact zero_query_not_implements (searchProgram n w hn) (searchAccess n) (searchTask n)
    (searchNativeBudget n) hzero (search_distinguishing n hn) (search_implements n w hn)

end Search

namespace Parity

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

def parityBit (f : I→Bool) : Bool :=
  decide ((Finset.univ.filter (fun i => f i=true)).card % 2=1)

def standardBitAccess (I W : Type) [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] : OracleAccess (I→Bool) ((I×Bool)×W) where
  oracle f := workspaceBitOracle (W:=W) f
  unitary f := workspaceBitOracle_unitary f

def parityTask (I : Type) [Fintype I] [DecidableEq I] : DistributionTask (I→Bool) Bool where
  legal _ := True
  target f := pointMass (parityBit f)
  good f y := y=parityBit f
  error _ := 2/3
  failure _ := 1/3

theorem bool_mass (p : FinDist Bool) : p.prob false+p.prob true=1 := by
  simpa only [Fintype.sum_bool,_root_.add_comm] using! p.sum_one

theorem parity_lower_from_success
    (P : MeasuredProgram ((I×Bool)×W) Bool)
    (hsuccess : ∀ f:I→Bool,
      1-(1/3:ℝ) ≤ eventProb (realLaw (runLaw P (standardBitAccess I W) f))
        (fun y => y=parityBit f)) :
    Fintype.card I ≤ 2*(ledger P).queries := by
  have hquery : Fintype.card I ≤ 2*QueryCount P.algorithm.circuit := by
    apply parity_actual_bounded_error_query_lower_bound
      P.algorithm.circuit P.algorithm.start
      (Finset.univ.filter (fun j => P.readout j=true))
      P.algorithm.unitary P.algorithm.normalized
    intro f
    let p := realLaw (runLaw P (standardBitAccess I W) f)
    have hs : 1-(1/3:ℝ) ≤ p.prob (parityBit f) := by
      simpa only [eventProb_point] using! hsuccess f
    have hsum := bool_mass p
    have hread := runLaw_event P (standardBitAccess I W) f (fun y => y=true)
    rw [eventProb_point] at hread
    change p.prob true=_ at hread
    simp only [standardBitAccess,workspaceBitOracle] at hread
    have hread' : MeasureProb
        (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ))
          P.algorithm.circuit P.algorithm.start)
        (Finset.univ.filter (fun j => P.readout j=true)) = p.prob true := by
      apply Eq.trans ?_ hread.symm
      congr 1
      ext j
      simp
    rw [hread']
    by_cases hodd : (Finset.univ.filter (fun i => f i=true)).card % 2=1
    · rw [if_pos hodd]
      have hs' : 1-(1/3:ℝ) ≤ p.prob true := by
        simpa only [parityBit,hodd,decide_true] using! hs
      apply abs_le.mpr
      constructor <;> linarith [p.nonneg false,p.nonneg true]
    · rw [if_neg hodd]
      have hs' : 1-(1/3:ℝ) ≤ p.prob false := by
        simpa only [parityBit,hodd,decide_false] using! hs
      apply abs_le.mpr
      constructor <;> linarith [p.nonneg false,p.nonneg true]
  simpa only [ledger,derive_queries] using! hquery

theorem parity_lower_of_implements
    (P : MeasuredProgram ((I×Bool)×W) Bool) (B : Budget)
    (h : Implements P (standardBitAccess I W) (parityTask I) B) :
    (Fintype.card I+1)/2 ≤ (ledger P).queries := by
  have hl := parity_lower_from_success P (fun f => (h.2 f trivial).2)
  omega

theorem parity_budget_lower
    (P : MeasuredProgram ((I×Bool)×W) Bool) (B : Budget)
    (h : Implements P (standardBitAccess I W) (parityTask I) B) :
    (Fintype.card I+1)/2 ≤ B.queries :=
  (parity_lower_of_implements P B h).trans h.1.1

theorem parity_universal_lower :
    QueryLower (standardBitAccess I W) (parityTask I) ((Fintype.card I+1)/2) := by
  intro P hp
  obtain ⟨B,h⟩ := hp
  exact parity_lower_of_implements P B h

theorem parity_fin2_nonconstant :
    parityBit (fun _ : Fin 2 => false)=false ∧
      parityBit (fun i : Fin 2 => decide (i=0))=true := by
  decide

abbrev TwoSpace := PolynomialWorkspace (Fin 2) (Reg 2×Bool)

def parityTwo : MeasuredProgram TwoSpace Bool where
  algorithm := {
    circuit := countedParityCircuit 2
    start := countedParityInitial 2 (by decide)
    unitary := isUnitaryCircuit_countedParityCircuit 2
    normalized := normalized_countedParityInitial 2 (by decide)
  }
  readout j := j.2.2

def parityTwoBudget : Budget :=
  ⟨1,GateCount (countedParityCircuit 2),Size (countedParityCircuit 2)⟩

theorem parityTwo_true_prob (f : Fin 2→Bool) :
    (realLaw (runLaw parityTwo (standardBitAccess (Fin 2) (Reg 2×Bool)) f)).prob true =
      if (Finset.univ.filter (fun i => f i=true)).card % 2=1 then 1 else 0 := by
  have h := runLaw_event parityTwo (standardBitAccess (Fin 2) (Reg 2×Bool)) f
    (fun y => y=true)
  rw [eventProb_point] at h
  refine h.trans ?_
  simpa only [parityTwo,standardBitAccess,workspaceBitOracle,countedParityAccept] using!
    countedParity_measureProb (by decide : 0<2) f

theorem parityTwo_correct_point (f : Fin 2→Bool) :
    (realLaw (runLaw parityTwo (standardBitAccess (Fin 2) (Reg 2×Bool)) f)).prob
      (parityBit f)=1 := by
  let p := realLaw (runLaw parityTwo (standardBitAccess (Fin 2) (Reg 2×Bool)) f)
  have ht := parityTwo_true_prob f
  have hsum := bool_mass p
  by_cases hodd : (Finset.univ.filter (fun i => f i=true)).card % 2=1
  · simpa only [parityBit,hodd,decide_true,if_true] using! ht
  · have hz : p.prob true=0 := by simpa only [hodd,if_false] using! ht
    have hf : p.prob false=1 := by linarith
    simpa only [parityBit,hodd,decide_false] using! hf

theorem parityTwo_implements :
    Implements parityTwo (standardBitAccess (Fin 2) (Reg 2×Bool))
      (parityTask (Fin 2)) parityTwoBudget := by
  refine ⟨(within_iff parityTwo parityTwoBudget).mpr ⟨?_,le_rfl,le_rfl⟩,?_⟩
  · norm_num [parityTwo,parityTwoBudget,queryCount_countedParityCircuit]
  · intro f _
    have hgood := parityTwo_correct_point f
    constructor
    · change outputError
        (realLaw (runLaw parityTwo (standardBitAccess (Fin 2) (Reg 2×Bool)) f))
        (pointMass (parityBit f)) ≤ (2/3:ℝ)
      rw [outputError_pointMass,hgood]
      norm_num
    · change 1-(1/3:ℝ) ≤ eventProb
        (realLaw (runLaw parityTwo (standardBitAccess (Fin 2) (Reg 2×Bool)) f))
        (fun y => y=parityBit f)
      rw [eventProb_point,hgood]
      norm_num

theorem parityTwo_exact_query : (ledger parityTwo).queries=1 := by
  simp [ledger,derive_queries,parityTwo,queryCount_countedParityCircuit]

theorem parityTwo_actual_nonconstant :
    (realLaw (runLaw parityTwo (standardBitAccess (Fin 2) (Reg 2×Bool))
      (fun _ : Fin 2 => false))).prob true=0 ∧
    (realLaw (runLaw parityTwo (standardBitAccess (Fin 2) (Reg 2×Bool))
      (fun i : Fin 2 => decide (i=0)))).prob true=1 := by
  have h0 : ¬ ((Finset.univ.filter (fun _ : Fin 2 => false=true)).card % 2=1) := by decide
  have h1 : (Finset.univ.filter (fun i : Fin 2 => decide (i=0)=true)).card % 2=1 := by decide
  constructor
  · simpa only [h0,if_false] using! parityTwo_true_prob (fun _ : Fin 2 => false)
  · simpa only [h1,if_true] using! parityTwo_true_prob (fun i : Fin 2 => decide (i=0))

theorem fin2_upper_lower_consumer :
    Implements parityTwo (standardBitAccess (Fin 2) (Reg 2×Bool))
      (parityTask (Fin 2)) parityTwoBudget ∧
    (ledger parityTwo).queries=1 ∧
    (∀ (P : MeasuredProgram TwoSpace Bool) (B : Budget),
      Implements P (standardBitAccess (Fin 2) (Reg 2×Bool)) (parityTask (Fin 2)) B →
        1≤(ledger P).queries ∧ 1≤B.queries) := by
  refine ⟨parityTwo_implements,parityTwo_exact_query,?_⟩
  intro P B h
  have hq := parity_lower_of_implements P B h
  have hb := parity_budget_lower P B h
  simpa using! And.intro hq hb

end Parity

theorem frontier1 :
    (∀ (W : Type) [Fintype W] [DecidableEq W] (w : W),
      ∃ c : ℝ, 0<c ∧ ∀ (n : ℕ) (hn : 2≤n),
        Implements (Search.searchProgram n w hn) (Search.searchAccess (W:=W) n)
          (Search.searchTask n) (Search.searchNativeBudget n) ∧
        ((ledger (Search.searchProgram n w hn)).queries : ℝ)≤c*Real.sqrt (Fintype.card (Reg n) : ℝ)) ∧
    (∀ (I W : Type) [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W],
      QueryLower (Parity.standardBitAccess I W) (Parity.parityTask I) ((Fintype.card I+1)/2)) ∧
    Implements Parity.parityTwo (Parity.standardBitAccess (Fin 2) (Reg 2×Bool))
      (Parity.parityTask (Fin 2)) Parity.parityTwoBudget ∧
    (ledger Parity.parityTwo).queries=1 ∧
    (realLaw (runLaw Parity.parityTwo (Parity.standardBitAccess (Fin 2) (Reg 2×Bool))
      (fun _ : Fin 2 => false))).prob true=0 ∧
    (realLaw (runLaw Parity.parityTwo (Parity.standardBitAccess (Fin 2) (Reg 2×Bool))
      (fun i : Fin 2 => decide (i=0)))).prob true=1 :=
  ⟨fun W _ _ w => @Search.search_uniform_family W _ _ w,
    fun I W _ _ _ _ => @Parity.parity_universal_lower I W _ _ _ _,
    Parity.parityTwo_implements,Parity.parityTwo_exact_query,
    Parity.parityTwo_actual_nonconstant.1,Parity.parityTwo_actual_nonconstant.2⟩

end
end Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBounds
