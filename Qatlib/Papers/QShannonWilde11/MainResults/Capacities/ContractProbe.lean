/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.Model.ProtocolCaps
public import Qatlib.Papers.QShannonWilde11.MainResults.Capacities.ClosedMath

@[expose] public section


/-! # Countermodels to unconstrained legacy information and resource interfaces

These records satisfy every literal field requirement. They are not physical
channels or operational resource theories. The counterexamples concern the old
formal contracts, never the corresponding results in arXiv:1106.1445v8.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Qatlib.Papers.QShannonWilde11.MainResults.Capacities.ContractProbe

open Qatlib.Papers.QShannonWilde11.MainResults.Model
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open Filter Topology

/-- A legal legacy record whose information fields are independent constants. -/
abbrev badInfo : QChanInfo where
  Ch := Unit
  tensor := fun _ _ => ()
  tensorPow := fun _ _ => ()
  mix := fun _ _ _ => ()
  mixSig := fun _ _ _ => ()
  I := fun _ => 1
  P := fun _ => 2
  Q := fun _ => 3
  chi := fun _ => 4
  chiPure := fun _ => 5
  capC := fun _ => 6
  capQ := fun _ => 7
  capP := fun _ => 8
  capEA := fun _ => 9
  dynCap := fun _ _ _ _ => 10
  Degradable := fun _ => True
  EntBreaking := fun _ => True
  Hadamard := fun _ => True
  Unital := fun _ => True
  PureInputSuffices := fun _ => True
  Erasure := fun _ _ _ => True
  Depolarizing := fun _ _ _ => True
  AmplitudeDamping := fun _ _ => True

/-- Literal additivity, private/coherent ordering and pure-input identities all fail. -/
theorem information_failures :
    badInfo.I (badInfo.tensor () ()) ≠ badInfo.I () + badInfo.I () ∧
    badInfo.P (badInfo.tensor () ()) ≠ badInfo.P () + badInfo.P () ∧
    badInfo.P () ≠ badInfo.I () - badInfo.chi () ∧
    badInfo.chi (badInfo.tensor () ()) ≠ badInfo.chi () + badInfo.chi () ∧
    badInfo.chi () ≠ badInfo.chiPure () ∧
    badInfo.Q (badInfo.tensor () ()) ≠ badInfo.Q () + badInfo.Q () ∧
    ¬ badInfo.Q () ≤ badInfo.P () ∧
    badInfo.P () ≠ badInfo.Q () ∧
    badInfo.dynCap (badInfo.tensor () ()) 1 0 0 ≠
      badInfo.dynCap () 1 0 0 + badInfo.dynCap () 1 0 0 := by
  norm_num [badInfo]

/-- The capacity fields have no connection to channel classes, entropies or each other. -/
theorem capacity_failures :
    badInfo.capEA () ≠ badInfo.I () ∧
    badInfo.capC () ≠ badInfo.I () ∧
    badInfo.capC () ≠ (1 - (0 : ℝ)) * Real.log (1 : ℝ) ∧
    badInfo.capC () ≠ Real.log (1 : ℝ) +
      (1 - (0 : ℝ) + 0 / 1) * Real.log (1 - (0 : ℝ) + 0 / 1) +
      ((1 : ℝ) - 1) * (0 / 1) * Real.log ((0 : ℝ) / 1) ∧
    badInfo.capEA () ≠ 2 * (1 - (0 : ℝ)) * Real.log (1 : ℝ) ∧
    badInfo.capQ () ≠ (if (0 : ℝ) ≤ 1 / 2 then
      (1 - 2 * (0 : ℝ)) * Real.log (1 : ℝ) else 0) ∧
    badInfo.capQ () ≠ (if (1 : ℝ) ≤ 1 / 2 then
      sSup {v : ℝ | ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧
        v = binEnt ((1 - (1 : ℝ)) * p) - binEnt ((1 : ℝ) * p)} else 0) ∧
    badInfo.Q (badInfo.tensor () ()) ≠ badInfo.P () / 2 := by
  norm_num [badInfo]

/-- Even achievability fails when the purported capacity is a freely chosen field. -/
theorem ea_bound_failure :
    let C := { badInfo with capEA := fun _ => 0 }
    ¬ C.I () ≤ C.capEA () := by
  norm_num [badInfo]

/-- A second legal record separates the regularized zero functionals from capacities. -/
abbrev zeroInfo : QChanInfo :=
  { badInfo with chi := fun _ => 0, P := fun _ => 0, Q := fun _ => 0 }

/-- A constant zero regularization cannot converge to a nonzero capacity field. -/
theorem zero_regularization (f : Unit → ℝ) (hf : ∀ n, f n = 0) (a : ℝ) (ha : a ≠ 0) :
    ¬ Tendsto (fun k => zeroInfo.reg f () k) atTop (nhds a) := by
  intro h
  have hz : Tendsto (fun k => zeroInfo.reg f () k) atTop (nhds (0 : ℝ)) := by
    simp [QChanInfo.reg, hf]
  exact ha (tendsto_nhds_unique h hz)

/-- The literal HSW, private-capacity and quantum-capacity limits have countermodels. -/
theorem coding_limit_failures :
    ¬ Tendsto (fun k => zeroInfo.reg zeroInfo.chi () k) atTop (nhds (zeroInfo.capC ())) ∧
    ¬ Tendsto (fun k => zeroInfo.reg zeroInfo.P () k) atTop (nhds (zeroInfo.capP ())) ∧
    ¬ Tendsto (fun k => zeroInfo.reg zeroInfo.Q () k) atTop (nhds (zeroInfo.capQ ())) := by
  refine ⟨zero_regularization _ (fun _ => rfl) _ ?_,
    zero_regularization _ (fun _ => rfl) _ ?_,
    zero_regularization _ (fun _ => rfl) _ ?_⟩ <;> norm_num [zeroInfo, badInfo]

/-- A compression rate can differ from its source entropy while satisfying every field. -/
theorem compression_failure {A : Type} [Fintype A] [DecidableEq A] (ρ : Dens A) :
    ∃ S : CompressionSource A, S.compLimit ≠ entropy S.ρ := by
  refine ⟨⟨ρ, entropy ρ + 1⟩, ?_⟩
  dsimp
  linarith

/-- Neither an entanglement conversion rate nor a distillation rate is constrained. -/
theorem entanglement_rate_failures {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (ψ φ : Dens (A × B)) :
    (∃ E : EntManipInfo A B,
      E.convRate ≠ entropy (marginR E.ψ) / entropy (marginR E.φ)) ∧
    (∃ D : DistillInfo A B, D.rate ≠ cohInfo D.ρ) := by
  constructor
  · refine ⟨⟨ψ, φ, entropy (marginR ψ) / entropy (marginR φ) + 1⟩, ?_⟩
    dsimp
    linarith
  · refine ⟨⟨ψ, cohInfo ψ + 1⟩, ?_⟩
    dsimp
    linarith

/-- The old coherent-rate identity and equality of capacity/achievable regions are false. -/
theorem resource_failures :
    let R : CoherentRates := ⟨0, 1, 0⟩
    let U : UnitResource := ⟨∅, Set.univ⟩
    2 * R.q2qq ≠ R.qq + R.q2q ∧ U.capRegion ≠ U.achRegion := by
  dsimp
  constructor
  · norm_num
  · let : Nonempty RateTriple := ⟨⟨0, 0, 0⟩⟩
    exact Set.empty_ne_univ

/-- The hashing-code interface does not constrain its rate by its Pauli probabilities. -/
theorem hashing_failure :
    let h : HashingCode := ⟨1, 0, 0, 0, 0⟩
    (0 ≤ h.pI ∧ 0 ≤ h.pX ∧ 0 ≤ h.pY ∧ 0 ≤ h.pZ) ∧
      h.pI + h.pX + h.pY + h.pZ = 1 ∧ h.rate ≠ 1 - pauliEnt h := by
  norm_num [pauliEnt]

/-- All left-hand resource fields can vanish while the requested outputs are positive. -/
def badRates : TradeoffRates where
  chan := 0
  stateRes := 0
  Wres := 0
  idRes := 1
  HA := 0
  HAX := 0
  IABc := 1
  IABq := 1
  IABq2q := 1
  IABqq := 1
  IAE := 0
  IARq := 0
  IARcc := 0
  cohABqq := 1
  coh := 1
  cmiABq := 1
  cmiABq2q := 1
  cmiAE := 0
  cohBX := 1
  IXBc := 1

/-- Each of the eleven old scalar resource inequalities has a legal countermodel. -/
theorem tradeoff_failures :
    ¬ badRates.chan + badRates.HA ≥ badRates.IABq ∧
    ¬ badRates.chan + (1 / 2) * badRates.IAE ≥ (1 / 2) * badRates.IABq2q ∧
    ¬ badRates.chan ≥ badRates.coh ∧
    ¬ badRates.stateRes + badRates.HA ≥ badRates.IABc ∧
    ¬ badRates.Wres + badRates.HA ≥ badRates.IABq + badRates.idRes ∧
    ¬ badRates.Wres + (1 / 2) * badRates.IARq ≥
      (1 / 2) * badRates.IABqq + badRates.idRes ∧
    ¬ badRates.Wres + badRates.IARcc ≥ badRates.cohABqq + badRates.idRes ∧
    ¬ badRates.chan + badRates.HAX ≥ badRates.IABc ∧
    ¬ badRates.chan + badRates.HAX ≥ badRates.cmiABq + badRates.IXBc ∧
    ¬ badRates.chan + (1 / 2) * badRates.cmiAE ≥
      (1 / 2) * badRates.cmiABq2q + badRates.IXBc ∧
    ¬ badRates.chan ≥ badRates.cohBX + badRates.IXBc := by
  norm_num [badRates]

/-- Independent feedback fields have no built-in operational relationships. -/
abbrev badFeedback : FeedbackCaps where
  Ch := Unit
  capNoFb := fun _ => 2
  capFb := fun _ => 1
  maxMutualInfo := fun _ => 0
  capEA := fun _ => 3
  capFbEA := fun _ => 4
  capFbInfEnt := fun _ => 5

/-- The three old feedback equalities fail on a legal singleton record. -/
theorem feedback_failures :
    badFeedback.capFb () ≠ badFeedback.maxMutualInfo () ∧
    badFeedback.capNoFb () ≠ badFeedback.maxMutualInfo () ∧
    badFeedback.capFbEA () ≠ badFeedback.capEA () ∧
    badFeedback.capFbInfEnt () ≠ badFeedback.capEA () := by
  norm_num [badFeedback]

/-- A legal dynamic-region record whose operational region is empty. -/
abbrev badDynamic : DynInfo where
  Ch := Unit
  tensorPow := fun _ _ => ()
  dynRegion := fun _ => ∅
  slRegion := fun _ => Set.univ
  IAXB := fun _ => 1
  coh := fun _ => 1
  IXB := fun _ => 1
  ent := fun _ => 1
  IAB := fun _ => 2
  cohPure := fun _ => 2
  IXBpure := fun _ => 3
  Hadamard := fun _ => True
  Dephasing := fun _ _ => True
  Erasure := fun _ _ _ => True

/-- The zero rate triple used to witness nonempty single-letter regions. -/
def zeroRate : RateTriple := ⟨0, 0, 0⟩

/-- A single-letter zero rate is also in the regularized union at block length one. -/
theorem zero_in_regularization (f : ℕ → Set RateTriple) (h : zeroRate ∈ f 1) :
    zeroRate ∈ regUnion f := by
  apply Set.mem_iUnion.mpr
  refine ⟨1, Set.mem_iUnion.mpr ⟨by simp, ?_⟩⟩
  exact ⟨zeroRate, h, by simp [zeroRate]⟩

/-- An empty operational field cannot equal any regularization containing the zero rate. -/
theorem region_failure (f : ℕ → Set RateTriple) (h : zeroRate ∈ f 1) :
    badDynamic.dynRegion () ≠ regUnion f := by
  intro heq
  have hmem := zero_in_regularization f h
  rw [← heq] at hmem
  exact hmem

/-- The five old specialized capacity-region targets fail independently of source coding. -/
theorem specialized_region_failures :
    badDynamic.dynRegion () ≠ regUnion (fun k => badDynamic.hswRegion (badDynamic.tensorPow () k)) ∧
    badDynamic.dynRegion () ≠ regUnion (fun k => badDynamic.qRegion (badDynamic.tensorPow () k)) ∧
    badDynamic.dynRegion () ≠ regUnion (fun k => badDynamic.qeRegion (badDynamic.tensorPow () k)) ∧
    badDynamic.dynRegion () ≠ regUnion (fun k => badDynamic.cqRegion (badDynamic.tensorPow () k)) ∧
    badDynamic.dynRegion () ≠ regUnion (fun k => badDynamic.ceRegion (badDynamic.tensorPow () k)) := by
  refine ⟨region_failure _ ?_, region_failure _ ?_, region_failure _ ?_,
    region_failure _ ?_, region_failure _ ?_⟩ <;>
    norm_num [badDynamic, zeroRate, DynInfo.hswRegion, DynInfo.qRegion,
      DynInfo.qeRegion, DynInfo.cqRegion, DynInfo.ceRegion]

/-- Free optimization fields violate all three old faces and Hadamard single-letterization. -/
theorem dynamic_face_failures :
    badDynamic.IAXB () ≠ badDynamic.IAB () ∧
    badDynamic.coh () ≠ badDynamic.cohPure () ∧
    badDynamic.coh () + badDynamic.IXB () ≠ badDynamic.IXBpure () ∧
    badDynamic.dynRegion () ≠ badDynamic.slRegionOf () ∧
    badDynamic.slRegion () ≠ badDynamic.slRegionOf () := by
  refine ⟨by norm_num [badDynamic], by norm_num [badDynamic],
    by norm_num [badDynamic], ?_, ?_⟩
  · intro h
    have hz : zeroRate ∈ badDynamic.slRegionOf () := by
      norm_num [DynInfo.slRegionOf, badDynamic, zeroRate]
    rw [← h] at hz
    exact hz
  · intro h
    have hz : (⟨2, 0, 0⟩ : RateTriple) ∈ badDynamic.slRegion () := Set.mem_univ _
    rw [h] at hz
    norm_num [DynInfo.slRegionOf, badDynamic] at hz

/-- A real-valued channel set with arbitrary mixture operations. -/
abbrev badMix : QChanInfo where
  Ch := ℝ
  tensor := fun _ _ => 0
  tensorPow := fun _ _ => 0
  mix := fun _ _ _ => 0
  mixSig := fun _ _ _ => 1
  I := id
  P := fun _ => 0
  Q := id
  chi := id
  chiPure := fun _ => 0
  capC := fun _ => 0
  capQ := fun _ => 0
  capP := fun _ => 0
  capEA := fun _ => 0
  dynCap := fun _ _ _ _ => 0
  Degradable := fun _ => True
  EntBreaking := fun _ => True
  Hadamard := fun _ => True
  Unital := fun _ => True
  PureInputSuffices := fun _ => True
  Erasure := fun _ _ _ => True
  Depolarizing := fun _ _ _ => True
  AmplitudeDamping := fun _ _ => True

/-- The old concavity and convexity targets fail for unconstrained mixtures. -/
theorem mixture_failures :
    ¬ (1 / 2) * badMix.I 1 + (1 - 1 / 2) * badMix.I 1 ≤ badMix.I (badMix.mix 1 1 (1 / 2)) ∧
    ¬ (1 / 2) * badMix.Q 1 + (1 - 1 / 2) * badMix.Q 1 ≤ badMix.Q (badMix.mix 1 1 (1 / 2)) ∧
    ¬ (1 / 2) * badMix.chi 1 + (1 - 1 / 2) * badMix.chi 1 ≤
      badMix.chi (badMix.mix 1 1 (1 / 2)) ∧
    ¬ badMix.chi (badMix.mixSig 0 0 (1 / 2)) ≤
      (1 / 2) * badMix.chi 0 + (1 - 1 / 2) * badMix.chi 0 := by
  norm_num [badMix]

/-- The old direct-coding scalar inequality fails for any supplied bipartite density. -/
theorem direct_coding_failure {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (ρ : Dens (A × B)) :
    ∃ C : QChanInfo, ∃ N : C.Ch, ¬ C.I N + H_A ρ ≥ mutualInfo ρ := by
  refine ⟨{ badInfo with I := fun _ => mutualInfo ρ - H_A ρ - 1 }, (), ?_⟩
  dsimp
  linarith

/-- At damping parameter one the old EA right-hand set is the singleton zero. -/
theorem damping_ea_failure :
    badInfo.capEA () ≠ sSup {v : ℝ | ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧
      v = binEnt p + binEnt ((1 - (1 : ℝ)) * p) - binEnt ((1 : ℝ) * p)} := by
  have hs : {v : ℝ | ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧
      v = binEnt p + binEnt ((1 - (1 : ℝ)) * p) - binEnt ((1 : ℝ) * p)} = {0} := by
    ext v
    simp only [sub_self, zero_mul, one_mul, binEnt, Real.log_zero,
      mul_zero, sub_zero, Real.log_one, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨p, _, _, hp⟩
      linarith
    · intro hv
      exact ⟨0, le_rfl, by norm_num, by linarith⟩
  rw [hs, csSup_singleton]
  norm_num [badInfo]

/-- An unconstrained secret-key region need not contain its single-letter zero rate. -/
abbrev badSecret : SkaInfo where
  Ch := Unit
  tensorPow := fun _ _ => ()
  capRegion := fun _ => ∅
  IXB := fun _ => 0
  IXE := fun _ => 0

/-- The old secret-key-assisted capacity identity has a legal countermodel. -/
theorem secret_region_failure :
    badSecret.capRegion () ≠ closure (regUnion2 (fun k => badSecret.slRegion (badSecret.tensorPow () k))) := by
  intro h
  have hz : (0, 0) ∈ regUnion2 (fun k => badSecret.slRegion (badSecret.tensorPow () k)) := by
    apply Set.mem_iUnion.mpr
    refine ⟨1, Set.mem_iUnion.mpr ⟨by simp, ?_⟩⟩
    refine ⟨(0, 0), ?_, by simp⟩
    norm_num [SkaInfo.slRegion, badSecret]
  have hm := subset_closure hz
  rw [← h] at hm
  exact hm

/-- Empty free regions contradict the old dephasing formula even at zero noise. -/
theorem dephasing_region_failure :
    badDynamic.dynRegion () ≠ ⋃ p ∈ Set.Icc (0 : ℝ) 1,
      {v : RateTriple | v.c + 2 * v.q ≤ 1 + binEnt 0 - binEnt 0 ∧
        v.q + v.e ≤ binEnt 0 - binEnt 0 ∧ v.c + v.q + v.e ≤ 1 - binEnt 0} := by
  intro h
  have hz : zeroRate ∈ ⋃ p ∈ Set.Icc (0 : ℝ) 1,
      {v : RateTriple | v.c + 2 * v.q ≤ 1 + binEnt 0 - binEnt 0 ∧
        v.q + v.e ≤ binEnt 0 - binEnt 0 ∧ v.c + v.q + v.e ≤ 1 - binEnt 0} := by
    apply Set.mem_iUnion.mpr
    refine ⟨0, Set.mem_iUnion.mpr ⟨by norm_num, ?_⟩⟩
    norm_num [zeroRate, binEnt]
  rw [← h] at hz
  exact hz

/-- At d=1 and epsilon=0 the old erasure formula still includes the zero triple. -/
theorem erasure_region_failure :
    badDynamic.dynRegion () ≠ ⋃ lam ∈ Set.Icc (0 : ℝ) 1,
      {v : RateTriple | v.c + 2 * v.q ≤ (1 - (0 : ℝ)) * (1 + lam) * Real.log (1 : ℝ) ∧
        v.q + v.e ≤ (1 - 2 * (0 : ℝ)) * lam * Real.log (1 : ℝ) ∧
        v.c + v.q + v.e ≤ (1 - (0 : ℝ) - 0 * lam) * Real.log (1 : ℝ)} := by
  intro h
  have hz : zeroRate ∈ ⋃ lam ∈ Set.Icc (0 : ℝ) 1,
      {v : RateTriple | v.c + 2 * v.q ≤ (1 - (0 : ℝ)) * (1 + lam) * Real.log (1 : ℝ) ∧
        v.q + v.e ≤ (1 - 2 * (0 : ℝ)) * lam * Real.log (1 : ℝ) ∧
        v.c + v.q + v.e ≤ (1 - (0 : ℝ) - 0 * lam) * Real.log (1 : ℝ)} := by
    apply Set.mem_iUnion.mpr
    refine ⟨0, Set.mem_iUnion.mpr ⟨by norm_num, ?_⟩⟩
    norm_num [zeroRate]
  rw [← h] at hz
  exact hz

/-- A legal zero-energy pure-loss record with an independent empty region. -/
abbrev badLoss : PureLossInfo where
  g := fun x => (x + 1) * Real.log (x + 1) - x * Real.log x
  dynRegion := ∅
  η := 1
  NS := 0

/-- Even the correct entropy function does not constrain a free bosonic region. -/
theorem pure_loss_region_failure :
    badLoss.dynRegion ≠ ⋃ lam ∈ Set.Icc (0 : ℝ) 1,
      {v : RateTriple |
        v.c + 2 * v.q ≤ badLoss.g (lam * badLoss.NS) + badLoss.g (badLoss.η * badLoss.NS) -
          badLoss.g ((1 - badLoss.η) * lam * badLoss.NS) ∧
        v.q + v.e ≤ badLoss.g (badLoss.η * lam * badLoss.NS) -
          badLoss.g ((1 - badLoss.η) * lam * badLoss.NS) ∧
        v.c + v.q + v.e ≤ badLoss.g (badLoss.η * badLoss.NS) -
          badLoss.g ((1 - badLoss.η) * lam * badLoss.NS)} := by
  intro h
  have hz : zeroRate ∈ ⋃ lam ∈ Set.Icc (0 : ℝ) 1,
      {v : RateTriple |
        v.c + 2 * v.q ≤ badLoss.g (lam * badLoss.NS) + badLoss.g (badLoss.η * badLoss.NS) -
          badLoss.g ((1 - badLoss.η) * lam * badLoss.NS) ∧
        v.q + v.e ≤ badLoss.g (badLoss.η * lam * badLoss.NS) -
          badLoss.g ((1 - badLoss.η) * lam * badLoss.NS) ∧
        v.c + v.q + v.e ≤ badLoss.g (badLoss.η * badLoss.NS) -
          badLoss.g ((1 - badLoss.η) * lam * badLoss.NS)} := by
    apply Set.mem_iUnion.mpr
    refine ⟨0, Set.mem_iUnion.mpr ⟨by norm_num, ?_⟩⟩
    norm_num [zeroRate, badLoss]
  rw [← h] at hz
  exact hz

end Qatlib.Papers.QShannonWilde11.MainResults.Capacities.ContractProbe
