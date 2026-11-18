/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ExactSimon97.SampleStopping
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Sum

@[expose] public section

/-!
# Complete expectation of the uncensored first-generation stopping time

Section 2 of [BrassardHoyer1997] (pp. 2–3) bounds the expected number of
independent uniform samples of a finite Abelian group `H` needed to generate `H` by
`2 log₂ |H|`. The module `Qatlib.Papers.ExactSimon97.SampleStopping` proved the
tail-sum decomposition for the window-censored generation time on finite sample
windows and left the *complete* expectation of the uncensored stopping time of an
infinite sampling process open (the uncensored-process boundary).

This module closes that boundary by constructing the infinite iid process and
transporting the window theory to it:

* the process law: `unifSubMeasure` realizes the idealized per-draw uniform law
  `unifOnSub H` as a genuine probability measure (a weighted sum of dirac masses),
  and `unifSubSeq` is the infinite-product law `MeasureTheory.Measure.infinitePi` on the sequence
  space `ℕ → G` — the projective limit of the finite-window product laws.
* the measure bridge `pi_probEvent`: the `unifSubSeq`-probability of any event
  depending on the first `k` draws equals its `Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent` value on the
  `k`-sample window. In particular the tail event `{spanInf ≠ H}` of the uncensored
  running span has probability exactly `failProbAt H k`, and the escape event
  (some draw leaving `H`) is null (`measure_escape_null`).
* the uncensored stopping time: `spanInf` is the running span of the infinite draw
  sequence and `stopGenInf` is the first moment at which it equals `H` (`⊤` when
  generation never happens). The finite-window censored time is its window truncation:
  `stopGen_windowOf` identifies `stopGen H (windowOf L ω)` with
  `min (stopGenInf H ω) L` pointwise, so the censored times increase monotonically
  to the uncensored time (`monotone_windowOf`, `stopGenInf_eq_iSup_windowOf`).
* the complete expectation: by monotone convergence (`lintegral_iSup`) and the exact
  layer-cake identity at each censored level, `stopGenInf_lintegral_eq` proves the
  exact series identity `E[T] = ∑' k, failProbAt H k` for the uncensored time, and
  `stopGenInf_lintegral_le` transports the uniform window bound
  `expected_le_two_log` through the limit to `E[T] ≤ 2 log₂ |H|` (with the
  real-valued corollary `stopGenInf_lintegral_toReal_le`).
* honesty of the limit object: `measure_stopGenInf_top` shows the uncensored time
  is finite almost surely (`P(T = ⊤) = 0`), so the complete expectation is the
  expectation of an almost-surely finite stopping time, and
  `lintegral_windowOf_expect` records that each censored level integrates to the
  finite-window window expectation `expectRecord (unifOnSub H) (stopGen H)`.

The measurable structure on the finite sample group is carried as
`[MeasurableSpace G] [DiscreteMeasurableSpace G]` (the power-set structure, matching
the FinDist framework in which every record has a mass); every finite group admits
it. The sibling module `Qatlib.Papers.ExactSimon97.SampleStoppingQuantum` identifies
this idealized per-sample law with the Born law of the executable coherent query-then-QFT
sampler and with its fresh-run product law, and proves that the composed sampling word makes
one oracle query per draw.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

open scoped BigOperators Classical ENNReal

namespace Qatlib.Papers.ExactSimon97.SampleStoppingInf

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.StabilizerAlg.NearUniformGen
open Qatlib.Papers.NoncommHSP98.MainResults
open Qatlib.Papers.ExactSimon97.MainResults
open Qatlib.Papers.ExactSimon97.SampleStopping
open MeasureTheory

/-! ## Real-to-extended-nonnegative bookkeeping -/

section Casts

variable {ι : Type*}

/-- Finite sums of nonnegative reals commute with the cast into `ℝ≥0∞`. -/
theorem ofReal_sum_finset (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    ENNReal.ofReal (∑ i ∈ s, f i) = ∑ i ∈ s, ENNReal.ofReal (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ih' := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hsnn : 0 ≤ ∑ i ∈ s, f i :=
      Finset.sum_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      ENNReal.ofReal_add (hf a (Finset.mem_insert_self a s)) hsnn, ih']

/-- Finite products of nonnegative reals commute with the cast into `ℝ≥0∞`. -/
theorem ofReal_prod_finset (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    ENNReal.ofReal (∏ i ∈ s, f i) = ∏ i ∈ s, ENNReal.ofReal (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ih' := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      ENNReal.ofReal_mul (hf a (Finset.mem_insert_self a s)), ih']

/-- Natural-number casts into `ℝ≥0∞` preserve and reflect strict order. -/
theorem natCast_lt_iff {m n : ℕ} : ((m : ℝ≥0∞) < (n : ℝ≥0∞)) ↔ m < n := by
  rw [← ENNReal.coe_natCast m, ← ENNReal.coe_natCast n, ENNReal.coe_lt_coe]
  exact Nat.cast_lt

/-- Natural-number casts into `ℝ≥0∞` preserve and reflect order. -/
theorem natCast_le_iff {m n : ℕ} : ((m : ℝ≥0∞) ≤ (n : ℝ≥0∞)) ↔ m ≤ n := by
  rw [← ENNReal.coe_natCast m, ← ENNReal.coe_natCast n, ENNReal.coe_le_coe]
  exact Nat.cast_le

/-- Every natural number is bounded by its own power of two. -/
theorem le_two_pow_self (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1pow : (1 : ℕ) ≤ 2 ^ n := Nat.succ_le_of_lt (Nat.two_pow_pos n)
    have hsplit : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
      rw [Nat.pow_succ]
      omega
    omega

/-- Events of the finite window framework have nonnegative `probEvent` mass. -/
theorem probEvent_nonneg {X : Type*} [Fintype X] {L : ℕ} (p : FinDist X)
    (E : (Fin L → X) → Prop) [DecidablePred E] : 0 ≤ p.probEvent E := by
  classical
  unfold FinDist.probEvent FinDist.probOf
  exact Finset.sum_nonneg fun ω _ => Finset.prod_nonneg fun i _ => p.nonneg _

/-- The generation-failure probabilities are nonnegative. -/
theorem failProbAt_nonneg {X : Type} [AddCommGroup X] [Fintype X]
    (H : AddSubgroup X) (k : ℕ) : 0 ≤ failProbAt H k :=
  probEvent_nonneg _ _

/-- Measurability of a finset sum of measurable `ℝ≥0∞`-valued functions. -/
theorem measurable_finset_sum' {α : Type*} [MeasurableSpace α] (s : Finset ι)
    (f : ι → α → ℝ≥0∞) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun a => ∑ i ∈ s, f i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Measurability of a finite union indexed by a finset. -/
theorem measurableSet_biUnion_finset' {α : Type*} [MeasurableSpace α] (s : Finset ι)
    (t : ι → Set α) (h : ∀ i ∈ s, MeasurableSet (t i)) :
    MeasurableSet (⋃ i ∈ s, t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact (h a (Finset.mem_insert_self a s)).union
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Measurability of a finite intersection indexed by a finset. -/
theorem measurableSet_biInter_finset' {α : Type*} [MeasurableSpace α] (s : Finset ι)
    (t : ι → Set α) (h : ∀ i ∈ s, MeasurableSet (t i)) :
    MeasurableSet (⋂ i ∈ s, t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biInter_insert]
    exact (h a (Finset.mem_insert_self a s)).inter
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Measure of a finite disjoint union of measurable sets: the additivity identity
used to evaluate cylinder events. -/
theorem measure_biUnion_disjoint {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Finset ι) (t : ι → Set α)
    (hmeas : ∀ i ∈ s, MeasurableSet (t i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (t i) (t j)) :
    μ (⋃ i ∈ s, t i) = ∑ i ∈ s, μ (t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hdisj' : Disjoint (t a) (⋃ i ∈ s, t i) := by
      rw [Set.disjoint_iff]
      by_contra hne
      obtain ⟨ω, hω, -⟩ := Set.not_subset.mp hne
      simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop] at hω
      obtain ⟨h1, i, hi, h2⟩ := hω
      have hI : (t a) ∩ (t i) ⊆ ∅ :=
        Set.disjoint_iff.mp (hdisj a (Finset.mem_insert_self a s) i
          (Finset.mem_insert_of_mem hi) (fun h => ha (h ▸ hi)))
      have hmem : ω ∈ (t a) ∩ (t i) := ⟨h1, h2⟩
      exact (hI hmem).elim
    rw [Finset.set_biUnion_insert,
      measure_union hdisj'
        (measurableSet_biUnion_finset' s t
          (fun i hi => hmeas i (Finset.mem_insert_of_mem hi))),
      Finset.sum_insert ha, ih (fun i hi => hmeas i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij => hdisj i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj) hij)]

end Casts

/-! ## The infinite iid process and the measure bridge -/

section Process

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- The idealized uniform subgroup law as a genuine probability measure on the
discrete sample group: a weighted sum of dirac masses with the `Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.prob`
weights of `unifOnSub H`. This is the one-draw marginal of the sampling process. -/
noncomputable def unifSubMeasure (H : AddSubgroup G) : Measure G :=
  Measure.sum fun g => ENNReal.ofReal ((unifOnSub H).prob g) • Measure.dirac g

/-- The one-draw law evaluated on a singleton: the measure of `{g}` is the
`Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.prob` weight of `g`. -/
theorem unifSubMeasure_singleton (H : AddSubgroup G) (g : G) :
    unifSubMeasure H {g} = ENNReal.ofReal ((unifOnSub H).prob g) := by
  classical
  have hterm : ∀ g' : G,
      (ENNReal.ofReal ((unifOnSub H).prob g') • Measure.dirac g') {g}
        = if g' = g then ENNReal.ofReal ((unifOnSub H).prob g) else 0 := by
    intro g'
    rw [Measure.smul_apply, Measure.dirac_apply]
    by_cases h : g' = g
    · simp [h]
    · simp [h]
  have hzero : ∀ b ∉ (Finset.univ : Finset G),
      (ENNReal.ofReal ((unifOnSub H).prob b) • Measure.dirac b) {g} = 0 := by
    intro b hb
    rw [hterm b]
    by_cases h : b = g
    · exact absurd (h ▸ Finset.mem_univ b) hb
    · simp [h]
  rw [unifSubMeasure, Measure.sum_apply_of_countable, tsum_eq_sum hzero,
    Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_ite_eq']
  simp

omit [DecidableEq G] in
/-- The one-draw law is a probability measure: total mass one, since the
`Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.prob` weights sum to one. -/
theorem isProbabilityMeasure_unifSubMeasure (H : AddSubgroup G) :
    IsProbabilityMeasure (unifSubMeasure H) := by
  classical
  refine ⟨?_⟩
  rw [unifSubMeasure, Measure.sum_apply_of_countable]
  have hterm : ∀ g : G,
      (ENNReal.ofReal ((unifOnSub H).prob g) • Measure.dirac g) Set.univ
        = ENNReal.ofReal ((unifOnSub H).prob g) := by
    intro g
    rw [Measure.smul_apply, Measure.dirac_apply]
    simp
  have hzero : ∀ b ∉ (Finset.univ : Finset G),
      (ENNReal.ofReal ((unifOnSub H).prob b) • Measure.dirac b) Set.univ = 0 := by
    intro b hb
    exact absurd (Finset.mem_univ b) hb
  rw [tsum_eq_sum hzero,
    Finset.sum_congr rfl (fun b _ => hterm b),
    ← ofReal_sum_finset _ _ (fun g _ => (unifOnSub H).nonneg g),
    (unifOnSub H).sum_one, ENNReal.ofReal_one]

/-- The law of the infinite iid sampling process: the infinite product
(`MeasureTheory.Measure.infinitePi`, the projective limit) of the one-draw uniform subgroup law
over the draw indices — the limit of the finite-window product laws of the
`FinDist` framework. -/
noncomputable def unifSubSeq (H : AddSubgroup G) : Measure (ℕ → G) :=
  Measure.infinitePi fun _ : ℕ => unifSubMeasure H

/-- The cylinder of a `k`-record: the set of infinite draw sequences whose first
`k` draws form the record `η`. -/
def cyl {k : ℕ} (η : Fin k → G) : Set (ℕ → G) :=
  {ω : ℕ → G | ∀ i : Fin k, ω i = η i}

omit [AddCommGroup G] [Fintype G] [DecidableEq G] in
/-- Cylinders are measurable: they are finite intersections of coordinate
preimages of singletons. -/
theorem measurableSet_cyl {k : ℕ} (η : Fin k → G) : MeasurableSet (cyl η) := by
  have hEq : cyl η = ⋂ i : Fin k, (fun ω : ℕ → G => ω (i : ℕ)) ⁻¹' {η i} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, cyl,
      Set.mem_ofPred_eq]
  rw [hEq]
  refine MeasurableSet.iInter fun i => ?_
  exact measurable_pi_apply (i : ℕ)
    (MeasurableSet.of_discrete : MeasurableSet ({η i} : Set G))

omit [Fintype G] [DecidableEq G] [MeasurableSpace G] [DiscreteMeasurableSpace G] in
/-- The cylinder of a record, written as a box: the set of sequences whose first
`k` coordinates are pinned to the record values. -/
theorem cyl_eq_pi {k : ℕ} (η : Fin k → G) :
    cyl η = (↑(Finset.range k) : Set ℕ).pi
      (fun j => {if h : j < k then η ⟨j, h⟩ else 0}) := by
  ext ω
  simp only [Set.mem_pi, Finset.mem_coe, Finset.mem_range, Set.mem_singleton_iff,
    Set.mem_ofPred_eq, cyl]
  constructor
  · intro h j hj
    have hjk : ω j = η ⟨j, hj⟩ := h ⟨j, hj⟩
    refine hjk.trans ?_
    rw [dite_eq_left hj]
  · intro h i
    have hi : ((i : ℕ)) < k := i.isLt
    refine (h (i : ℕ) hi).trans ?_
    rw [dite_eq_left hi]

/-- The mass of a cylinder is the `Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf` mass of its record. -/
theorem measure_cyl {k : ℕ} (H : AddSubgroup G) (η : Fin k → G) :
    unifSubSeq H (cyl η) = ENNReal.ofReal (FinDist.probOf (L := k) (unifOnSub H) η) := by
  classical
  have hmpi : (Measure.infinitePi fun _ : ℕ => unifSubMeasure H)
      ((↑(Finset.range k) : Set ℕ).pi (fun j => {if h : j < k then η ⟨j, h⟩ else 0}))
      = ∏ j ∈ Finset.range k, (unifSubMeasure H)
          {if h : j < k then η ⟨j, h⟩ else 0} :=
    Measure.infinitePi_pi (fun _ : ℕ => unifSubMeasure H)
      (hμ := fun _ => isProbabilityMeasure_unifSubMeasure H)
      (s := Finset.range k)
      (t := fun j => {if h : j < k then η ⟨j, h⟩ else 0})
      (fun j _ => MeasurableSet.of_discrete)
  rw [unifSubSeq, cyl_eq_pi η, hmpi]
  have hpt : ∀ j ∈ Finset.range k,
      (unifSubMeasure H) {if h : j < k then η ⟨j, h⟩ else 0}
        = ENNReal.ofReal ((unifOnSub H).prob (if h : j < k then η ⟨j, h⟩ else 0)) := by
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    rw [dite_eq_left hjk, unifSubMeasure_singleton H (η ⟨j, hjk⟩)]
  rw [Finset.prod_congr rfl (fun j hj => hpt j hj),
    ← ofReal_prod_finset _ _ (fun j _ => (unifOnSub H).nonneg _)]
  congr 1
  calc ∏ j ∈ Finset.range k, (unifOnSub H).prob (if h : j < k then η ⟨j, h⟩ else 0)
      = ∏ i : Fin k, (unifOnSub H).prob
          (if h : (i : ℕ) < k then η ⟨(i : ℕ), h⟩ else 0) :=
        (Fin.prod_univ_eq_prod_range
          (fun j => (unifOnSub H).prob (if h : j < k then η ⟨j, h⟩ else 0)) k).symm
    _ = ∏ i : Fin k, (unifOnSub H).prob (η i) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        have hi : ((i : ℕ)) < k := i.isLt
        have hval : (if h : (i : ℕ) < k then η ⟨(i : ℕ), h⟩ else 0) = η i := by
          rw [dite_eq_left hi]
        rw [hval]
    _ = FinDist.probOf (L := k) (unifOnSub H) η := rfl

omit [AddCommGroup G] [DecidableEq G] [MeasurableSpace G] [DiscreteMeasurableSpace G] in
/-- The cylinder decomposition of a prefix event: an event depending on the first
`k` draws is the disjoint union of the cylinders of the records satisfying it. -/
theorem set_prefix_eq_iUnion {k : ℕ} (Q : (Fin k → G) → Prop) [DecidablePred Q] :
    {ω : ℕ → G | Q (fun i => ω i)} =
      ⋃ η ∈ (Finset.univ.filter Q : Finset (Fin k → G)), cyl η := by
  ext ω
  constructor
  · intro hQ
    exact Set.mem_biUnion
      (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ⟩))
      (fun _ => rfl)
  · intro hmem
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨η, hη1, hη2⟩ := hmem
    have hf : (fun i : Fin k => ω i) = η := funext fun i => hη2 i
    have hQη : Q η := (Finset.mem_filter.mp (Finset.mem_coe.mp hη1)).2
    show Q (fun i : Fin k => ω i)
    rw [hf]
    exact hQη

omit [AddCommGroup G] [DecidableEq G] in
/-- Prefix events are measurable, being finite unions of cylinders. -/
theorem measurableSet_prefix {k : ℕ} (Q : (Fin k → G) → Prop) [DecidablePred Q] :
    MeasurableSet {ω : ℕ → G | Q (fun i => ω i)} := by
  rw [set_prefix_eq_iUnion Q]
  exact measurableSet_biUnion_finset' _ cyl (fun η _ => measurableSet_cyl η)

/-- The measure bridge between the infinite process and the FinDist window
framework: the `unifSubSeq`-probability of any event depending on the first `k`
draws equals its `Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent` value on the `k`-sample window. -/
theorem pi_probEvent {k : ℕ} (H : AddSubgroup G) (Q : (Fin k → G) → Prop)
    [DecidablePred Q] :
    unifSubSeq H {ω : ℕ → G | Q (fun i => ω i)} =
      ENNReal.ofReal (FinDist.probEvent (L := k) (unifOnSub H) Q) := by
  have hmeas : ∀ η ∈ (Finset.univ.filter Q : Finset (Fin k → G)),
      MeasurableSet (cyl η) := fun η _ => measurableSet_cyl η
  have hdisj : ∀ η ∈ (Finset.univ.filter Q : Finset (Fin k → G)), ∀ η' ∈
      (Finset.univ.filter Q : Finset (Fin k → G)), η ≠ η' →
      Disjoint (cyl η) (cyl η') := by
    intro η _ η' _ hne
    rw [Set.disjoint_iff]
    by_contra hne'
    obtain ⟨ω, hω, -⟩ := Set.not_subset.mp hne'
    obtain ⟨h1, h2⟩ := hω
    exact hne (funext fun i => (h1 i).symm.trans (h2 i))
  have hnn : ∀ η : Fin k → G, 0 ≤ FinDist.probOf (L := k) (unifOnSub H) η :=
    fun η => Finset.prod_nonneg (fun i _ => (unifOnSub H).nonneg (η i))
  rw [set_prefix_eq_iUnion Q, measure_biUnion_disjoint _ _ cyl hmeas hdisj,
    Finset.sum_congr rfl (fun η _ => measure_cyl H η),
    ← ofReal_sum_finset _ _ (fun η _ => hnn η)]
  congr 1

end Process

/-! ## The uncensored running span and stopping time -/

section Stopping

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- The subgroup generated by the first `k` draws of an infinite sampling
process: the uncensored running span. -/
def spanInf (ω : ℕ → G) (k : ℕ) : AddSubgroup G :=
  AddSubgroup.closure (Set.range fun i : Fin k => ω i)

omit [Fintype G] [DecidableEq G] [MeasurableSpace G] [DiscreteMeasurableSpace G] in
/-- The running span of the infinite process is monotone. -/
theorem spanInf_mono (ω : ℕ → G) : Monotone (spanInf ω) := by
  intro i j hij
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨i', rfl⟩
  exact ⟨Fin.castLE hij i', by simp⟩

omit [Fintype G] [DecidableEq G] [MeasurableSpace G] [DiscreteMeasurableSpace G] in
/-- If the first `k` draws all lie in a subgroup `K`, the running span after `k`
draws is contained in `K`. -/
theorem spanInf_le (ω : ℕ → G) (k : ℕ) (K : AddSubgroup G)
    (hmem : ∀ i : Fin k, ω i ∈ K) : spanInf ω k ≤ K := by
  refine (AddSubgroup.closure_le K).2 ?_
  rintro x ⟨i, rfl⟩
  exact hmem i

/-- The uncensored first-generation stopping time of the infinite sampling
process: the first moment at which the running span equals `H`, and `⊤` when
generation never happens. -/
noncomputable def stopGenInf (H : AddSubgroup G) (ω : ℕ → G) : ℝ≥0∞ :=
  if hex : ∃ j, spanInf ω j = H then (Nat.find hex : ℝ≥0∞) else ⊤

omit [Fintype G] [DecidableEq G] [MeasurableSpace G] [DiscreteMeasurableSpace G] in
/-- If the running span equals `H` after `k` draws, the uncensored stopping time
is at most `k`. -/
theorem stopGenInf_le_of_spanInf (H : AddSubgroup G) {ω : ℕ → G} {k : ℕ}
    (hspan : spanInf ω k = H) : stopGenInf H ω ≤ (k : ℝ≥0∞) := by
  unfold stopGenInf
  split_ifs with hex
  · exact natCast_le_iff.mpr (Nat.find_min' hex hspan)
  · exact absurd ⟨k, hspan⟩ hex

/-- The `L`-window of an infinite draw sequence: the finite record of its first
`L` draws, the bridge to the finite-window window framework. -/
def windowOf (L : ℕ) (ω : ℕ → G) : Fin L → G := fun i => ω i

omit [Fintype G] [DecidableEq G] [MeasurableSpace G] [DiscreteMeasurableSpace G] in
/-- The window running span is the truncation of the infinite running span:
`spanPrefix (windowOf L ω) k = spanInf ω k` for `k ≤ L`. -/
theorem spanPrefix_windowOf {L k : ℕ} (h : k ≤ L) (ω : ℕ → G) :
    spanPrefix (windowOf L ω) k = spanInf ω k := by
  have himg : (windowOf L ω) '' {i : Fin L | (i : ℕ) < k}
      = Set.range (fun i : Fin k => ω i) := by
    ext g
    constructor
    · rintro ⟨i, hi, hg⟩
      exact ⟨⟨(i : ℕ), hi⟩, hg⟩
    · rintro ⟨i, hg⟩
      exact ⟨Fin.castLE h i, i.isLt, hg⟩
  unfold spanPrefix spanInf
  rw [himg]

omit [Fintype G] [DecidableEq G] [MeasurableSpace G] [DiscreteMeasurableSpace G] in
/-- The censored window value realizes its generating span: whenever the window
stopping time is below the window length, the running span at that moment is
exactly `H`. -/
theorem spanPrefix_stopGen (H : AddSubgroup G) {L : ℕ} (w : Fin L → G)
    (hL : stopGen H w < L) : spanPrefix w (stopGen H w) = H := by
  unfold stopGen at hL ⊢
  split_ifs at hL ⊢ with hex
  · exact (Nat.find_spec hex).2
  · exact absurd hL (Nat.lt_irrefl L)

omit [Fintype G] [DecidableEq G] [MeasurableSpace G] [DiscreteMeasurableSpace G] in
/-- Pointwise censorship identity: the finite-window window-censored first-generation
time of the `L`-window of an infinite draw sequence is exactly the truncation
`min (stopGenInf H ω) L` of the uncensored stopping time. -/
theorem stopGen_windowOf (H : AddSubgroup G) (L : ℕ) (ω : ℕ → G) :
    ((stopGen H (windowOf L ω) : ℕ) : ℝ≥0∞) = min (stopGenInf H ω) (L : ℝ≥0∞) := by
  classical
  have hle := stopGen_le H (windowOf L ω)
  unfold stopGenInf
  split_ifs with hex
  · rcases lt_or_ge L (Nat.find hex) with hjL | hjL
    · have hne : stopGen H (windowOf L ω) = L := by
        rcases Nat.lt_or_ge (stopGen H (windowOf L ω)) L with hw | hw
        · exfalso
          have hspan : spanInf ω (stopGen H (windowOf L ω)) = H := by
            rw [← spanPrefix_windowOf hw.le ω]
            exact spanPrefix_stopGen H (windowOf L ω) hw
          have hbound := Nat.find_min' hex hspan
          omega
        · omega
      rw [hne, min_eq_right (natCast_le_iff.mpr hjL.le)]
    · have hspan : spanPrefix (windowOf L ω) (Nat.find hex) = H := by
        rw [spanPrefix_windowOf hjL ω]
        exact Nat.find_spec hex
      have h1 : stopGen H (windowOf L ω) ≤ Nat.find hex :=
        stopGen_le_of_span H (windowOf L ω) _ hjL hspan
      have h2 : Nat.find hex ≤ stopGen H (windowOf L ω) := by
        rcases Nat.lt_or_ge (stopGen H (windowOf L ω)) L with hw | hw
        · have hspan : spanInf ω (stopGen H (windowOf L ω)) = H := by
            rw [← spanPrefix_windowOf hw.le ω]
            exact spanPrefix_stopGen H (windowOf L ω) hw
          exact Nat.find_min' hex hspan
        · have hLe : stopGen H (windowOf L ω) = L := Nat.le_antisymm hle hw
          rw [hLe]
          exact hjL
      rw [Nat.le_antisymm h1 h2, min_eq_left (natCast_le_iff.mpr hjL)]
  · have hne : stopGen H (windowOf L ω) = L := by
      rcases Nat.lt_or_ge (stopGen H (windowOf L ω)) L with hw | hw
      · exfalso
        have hspan : spanInf ω (stopGen H (windowOf L ω)) = H := by
          rw [← spanPrefix_windowOf hw.le ω]
          exact spanPrefix_stopGen H (windowOf L ω) hw
        exact hex ⟨stopGen H (windowOf L ω), hspan⟩
      · omega
    rw [hne]
    simp

omit [Fintype G] [DecidableEq G] [MeasurableSpace G] [DiscreteMeasurableSpace G] in
/-- The uncensored stopping time is the pointwise supremum of its truncations. -/
theorem stopGenInf_eq_iSup_min (H : AddSubgroup G) (ω : ℕ → G) :
    stopGenInf H ω = ⨆ L : ℕ, min (stopGenInf H ω) (L : ℝ≥0∞) := by
  rcases eq_or_ne (stopGenInf H ω) ⊤ with htop | h
  · rw [htop]
    have hkey : (⊤ : ℝ≥0∞) ≤ ⨆ L : ℕ, min (⊤ : ℝ≥0∞) ((L : ℕ) : ℝ≥0∞) := by
      by_contra hne
      have hne' : (⨆ L : ℕ, min (⊤ : ℝ≥0∞) ((L : ℕ) : ℝ≥0∞)) ≠ ∞ := by
        intro h
        apply hne
        rw [h]
      have hlt : (⨆ L : ℕ, min (⊤ : ℝ≥0∞) ((L : ℕ) : ℝ≥0∞)) < ∞ :=
        lt_of_le_of_ne le_top hne'
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hlt.ne
      have hval : min (⊤ : ℝ≥0∞) ((n : ℕ) : ℝ≥0∞) = ((n : ℕ) : ℝ≥0∞) := by simp
      have hle : ((n : ℕ) : ℝ≥0∞)
          ≤ (⨆ L : ℕ, min (⊤ : ℝ≥0∞) ((L : ℕ) : ℝ≥0∞)) := by
        rw [← hval]
        exact le_iSup (fun L : ℕ => min (⊤ : ℝ≥0∞) ((L : ℕ) : ℝ≥0∞)) n
      exact absurd (lt_of_lt_of_le hn hle) (lt_irrefl _)
    exact (top_le_iff.mp hkey).symm
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h
    refine le_antisymm ?_ ?_
    · exact (min_eq_left hn.le).symm.trans_le
        (le_iSup (fun L : ℕ => min (stopGenInf H ω) ((L : ℕ) : ℝ≥0∞)) n)
    · exact iSup_le fun L => min_le_left (stopGenInf H ω) ((L : ℕ) : ℝ≥0∞)

omit [Fintype G] [DecidableEq G] [MeasurableSpace G] [DiscreteMeasurableSpace G] in
/-- The window-censored times increase pointwise with the window length. -/
theorem monotone_windowOf (H : AddSubgroup G) :
    Monotone (fun L : ℕ => fun ω : ℕ → G =>
      ((stopGen H (windowOf L ω) : ℕ) : ℝ≥0∞)) := by
  intro L1 L2 hL
  apply Pi.le_def.mpr
  intro ω
  show ((stopGen H (windowOf L1 ω) : ℕ) : ℝ≥0∞) ≤
      ((stopGen H (windowOf L2 ω) : ℕ) : ℝ≥0∞)
  rw [stopGen_windowOf H L1 ω, stopGen_windowOf H L2 ω]
  exact min_le_min (le_refl _) (natCast_le_iff.mpr hL)

omit [Fintype G] [DecidableEq G] [MeasurableSpace G] [DiscreteMeasurableSpace G] in
/-- The window-censored times converge pointwise to the uncensored stopping
time. -/
theorem stopGenInf_eq_iSup_windowOf (H : AddSubgroup G) (ω : ℕ → G) :
    stopGenInf H ω =
      ⨆ L : ℕ, ((stopGen H (windowOf L ω) : ℕ) : ℝ≥0∞) := by
  rw [stopGenInf_eq_iSup_min H ω]
  exact iSup_congr fun L => (stopGen_windowOf H L ω).symm

end Stopping

/-! ## Tail probabilities of the uncensored stopping time -/

section TailID

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- Under the infinite process law, every draw lies in `H`: the escape event, on
which some draw among the first `k` leaves the subgroup, is null. -/
theorem measure_escape_null (H : AddSubgroup G) (k : ℕ) :
    unifSubSeq H {ω : ℕ → G | ∃ i : Fin k, ω i ∉ H} = 0 := by
  classical
  have h := pi_probEvent H (Q := fun hs : Fin k → G => ∃ i, hs i ∉ H)
  have hzero : FinDist.probEvent (L := k) (unifOnSub H)
      (fun hs : Fin k → G => ∃ i, hs i ∉ H) = 0 := by
    unfold FinDist.probEvent
    rw [Finset.sum_eq_zero]
    intro η hη
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hη).2
    unfold FinDist.probOf
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [unifOnSub, hi])]
  refine h.trans ?_
  rw [hzero, ENNReal.ofReal_zero]

/-- Tail identification on the infinite process: the probability that the running
span after `k` draws is not yet `H` equals the generation-failure probability
`failProbAt H k` of the window framework. -/
theorem measure_spanInf_ne (H : AddSubgroup G) (k : ℕ) :
    unifSubSeq H {ω : ℕ → G | spanInf ω k ≠ H} = ENNReal.ofReal (failProbAt H k) := by
  classical
  exact pi_probEvent H (Q := fun hs : Fin k → G => AddSubgroup.closure (Set.range hs) ≠ H)

/-- Tail probability of the uncensored stopping time: `P(k < T) = failProbAt H k`,
exactly as for the window-censored time (`probEvent_stopGen_gt`). -/
theorem measure_stopGenInf_gt (H : AddSubgroup G) (k : ℕ) :
    unifSubSeq H {ω : ℕ → G | (k : ℝ≥0∞) < stopGenInf H ω}
      = ENNReal.ofReal (failProbAt H k) := by
  classical
  have hsub1 : {ω : ℕ → G | (k : ℝ≥0∞) < stopGenInf H ω} ⊆
      {ω : ℕ → G | spanInf ω k ≠ H} := by
    intro ω hω hspan
    have hle := stopGenInf_le_of_spanInf H hspan
    exact absurd (lt_of_lt_of_le hω hle) (lt_irrefl (k : ℝ≥0∞))
  have hsub2 : {ω : ℕ → G | spanInf ω k ≠ H} ⊆
      {ω : ℕ → G | (k : ℝ≥0∞) < stopGenInf H ω} ∪
        {ω : ℕ → G | ∃ i : Fin k, ω i ∉ H} := by
    intro ω hspan
    by_cases hex : ∃ j, spanInf ω j = H
    · rcases Nat.lt_or_ge k (Nat.find hex) with hkj | hjk
      · left
        have hklt : k < Nat.find hex := by
          rcases eq_or_ne k (Nat.find hex) with he | hne
          · exact absurd (by rw [he]; exact Nat.find_spec hex) hspan
          · omega
        have hT : stopGenInf H ω = ((Nat.find hex : ℕ) : ℝ≥0∞) := by
          unfold stopGenInf
          rw [dite_eq_left hex]
        show (k : ℝ≥0∞) < stopGenInf H ω
        rw [hT]
        exact natCast_lt_iff.mpr hklt
      · right
        by_contra hno
        have hall : ∀ i : Fin k, ω i ∈ H := by
          intro i
          by_contra hout
          exact hno ⟨i, hout⟩
        have hle := spanInf_le ω k H hall
        have hge : H ≤ spanInf ω k := by
          rw [← Nat.find_spec hex]
          exact spanInf_mono ω hjk
        exact hspan (le_antisymm hle hge)
    · left
      have hT : stopGenInf H ω = ⊤ := by
        unfold stopGenInf
        rw [dite_eq_right hex]
      show (k : ℝ≥0∞) < stopGenInf H ω
      rw [hT]
      exact ENNReal.natCast_lt_top k
  have h1 : unifSubSeq H {ω : ℕ → G | (k : ℝ≥0∞) < stopGenInf H ω}
      ≤ unifSubSeq H {ω : ℕ → G | spanInf ω k ≠ H} := measure_mono hsub1
  rw [measure_spanInf_ne H k] at h1
  have h2 : ENNReal.ofReal (failProbAt H k)
      ≤ unifSubSeq H {ω : ℕ → G | (k : ℝ≥0∞) < stopGenInf H ω} := by
    have hle1 : unifSubSeq H {ω : ℕ → G | spanInf ω k ≠ H}
        ≤ unifSubSeq H ({ω : ℕ → G | (k : ℝ≥0∞) < stopGenInf H ω} ∪
            {ω : ℕ → G | ∃ i : Fin k, ω i ∉ H}) := measure_mono hsub2
    have hle2 : unifSubSeq H ({ω : ℕ → G | (k : ℝ≥0∞) < stopGenInf H ω} ∪
            {ω : ℕ → G | ∃ i : Fin k, ω i ∉ H})
        ≤ unifSubSeq H {ω : ℕ → G | (k : ℝ≥0∞) < stopGenInf H ω} +
          unifSubSeq H {ω : ℕ → G | ∃ i : Fin k, ω i ∉ H} := measure_union_le _ _
    have hle := hle1.trans hle2
    rw [measure_escape_null H k] at hle
    rw [add_zero] at hle
    rwa [measure_spanInf_ne H k] at hle
  exact le_antisymm h1 h2

omit [DecidableEq G] in
/-- The strict tail level sets of the uncensored stopping time are measurable. -/
theorem measurableSet_stopGenInf_gt (H : AddSubgroup G) (k : ℕ) :
    MeasurableSet {ω : ℕ → G | (k : ℝ≥0∞) < stopGenInf H ω} := by
  classical
  have hEq : {ω : ℕ → G | (k : ℝ≥0∞) < stopGenInf H ω} =
      ⋂ j ∈ Finset.range (k + 1), {ω : ℕ → G | spanInf ω j ≠ H} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]
    constructor
    · intro hω j hj
      have hjk : j ≤ k := by omega
      intro hspan
      have hle := stopGenInf_le_of_spanInf H hspan
      exact absurd (lt_of_lt_of_le hω (le_trans hle (natCast_le_iff.mpr hjk)))
        (lt_irrefl (k : ℝ≥0∞))
    · intro hω
      show (k : ℝ≥0∞) < stopGenInf H ω
      unfold stopGenInf
      split_ifs with hex
      · refine natCast_lt_iff.mpr ?_
        by_contra hcon
        have hfk : Nat.find hex ≤ k := by omega
        exact hω (Nat.find hex) (by
          have hlt : Nat.find hex < k + 1 := by omega
          simpa using hlt) (Nat.find_spec hex)
      · exact ENNReal.natCast_lt_top k
  rw [hEq]
  exact measurableSet_biInter_finset' _
    (fun j => {ω : ℕ → G | spanInf ω j ≠ H})
    (fun j _ => measurableSet_prefix
      (Q := fun hs : Fin j → G => AddSubgroup.closure (Set.range hs) ≠ H))

end TailID

/-! ## The complete expectation of the uncensored stopping time -/

section Expectation

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

omit [Fintype G] [DecidableEq G] [MeasurableSpace G] [DiscreteMeasurableSpace G] in
/-- Exact layer-cake identity at each censored level: the truncation
`min (stopGenInf H ω) L` counts the strict tail events below `L`. -/
theorem stopGenInf_min_eq_sum (H : AddSubgroup G) (ω : ℕ → G) (L : ℕ) :
    min (stopGenInf H ω) (L : ℝ≥0∞) =
      ∑ k ∈ Finset.range L, (if (k : ℝ≥0∞) < stopGenInf H ω then (1 : ℝ≥0∞) else 0) := by
  rcases Classical.em (∃ j, spanInf ω j = H) with hex | hex
  · have hT : stopGenInf H ω = ((Nat.find hex : ℕ) : ℝ≥0∞) := by
      unfold stopGenInf
      rw [dite_eq_left hex]
    rw [hT]
    rcases lt_or_ge L (Nat.find hex) with h | h
    · have hmin : min ((Nat.find hex : ℕ) : ℝ≥0∞) (L : ℝ≥0∞)
          = (L : ℝ≥0∞) :=
        min_eq_right (natCast_le_iff.mpr h.le)
      have hcond : ∀ k ∈ Finset.range L,
          (if (k : ℝ≥0∞) < ((Nat.find hex : ℕ) : ℝ≥0∞) then (1 : ℝ≥0∞) else 0) = 1 := by
        intro k hk
        have h1 : ((k : ℝ≥0∞) < ((Nat.find hex : ℕ) : ℝ≥0∞)) :=
          natCast_lt_iff.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) h.le)
        simp only [h1, ite_true]
      rw [hmin, Finset.sum_congr rfl (fun k hk => hcond k hk), Finset.sum_const,
        Finset.card_range, Nat.smul_one_eq_cast]
    · have hmin : min ((Nat.find hex : ℕ) : ℝ≥0∞) (L : ℝ≥0∞)
          = ((Nat.find hex : ℕ) : ℝ≥0∞) :=
        min_eq_left (natCast_le_iff.mpr h)
      have hcond : ∀ k ∈ Finset.range L,
          (if (k : ℝ≥0∞) < ((Nat.find hex : ℕ) : ℝ≥0∞) then (1 : ℝ≥0∞) else 0)
            = ENNReal.ofReal (if k < Nat.find hex then (1 : ℝ) else 0) := by
        intro k _
        rcases lt_or_ge k (Nat.find hex) with hk | hk
        · have h1 : ((k : ℝ≥0∞) < ((Nat.find hex : ℕ) : ℝ≥0∞)) := natCast_lt_iff.mpr hk
          simp only [h1, hk, ite_true, ENNReal.ofReal_one]
        · have h1 : ¬((k : ℝ≥0∞) < ((Nat.find hex : ℕ) : ℝ≥0∞)) :=
            fun hcon => absurd (natCast_lt_iff.mp hcon) (Nat.not_lt.mpr hk)
          have h2 : ¬(k < Nat.find hex) := Nat.not_lt.mpr hk
          simp only [h1, h2, ite_false, ENNReal.ofReal_zero]
      have htermnn : ∀ k ∈ Finset.range L, 0 ≤ (if k < Nat.find hex then (1 : ℝ) else 0) := by
        intro k _
        by_cases hk : k < Nat.find hex
        · rw [ite_eq_left hk]
          norm_num
        · rw [ite_eq_right hk]
      rw [hmin, Finset.sum_congr rfl (fun k hk => hcond k hk),
        ← ofReal_sum_finset _ _ htermnn,
        ← count_indicator (Nat.find hex) L h, ENNReal.ofReal_natCast]
  · have hT : stopGenInf H ω = ⊤ := by
      unfold stopGenInf
      rw [dite_eq_right hex]
    rw [hT]
    have hmin : min (⊤ : ℝ≥0∞) (L : ℝ≥0∞) = (L : ℝ≥0∞) := by simp
    have hcond : ∀ k ∈ Finset.range L, (if (k : ℝ≥0∞) < (⊤ : ℝ≥0∞) then (1 : ℝ≥0∞) else 0)
        = 1 := by
      intro k _
      have h1 : ((k : ℝ≥0∞) < (⊤ : ℝ≥0∞)) := ENNReal.natCast_lt_top k
      simp only [h1, ite_true]
    rw [hmin, Finset.sum_congr rfl (fun k hk => hcond k hk), Finset.sum_const,
      Finset.card_range, Nat.smul_one_eq_cast]

omit [DecidableEq G] in
/-- Measurability of the strict tail indicators of the uncensored stopping time. -/
theorem measurable_stopGenInf_tail (H : AddSubgroup G) (k : ℕ) :
    Measurable (fun ω : ℕ → G => (if (k : ℝ≥0∞) < stopGenInf H ω then (1 : ℝ≥0∞) else 0)) := by
  have h1 : Measurable (Set.indicator {ω : ℕ → G | (k : ℝ≥0∞) < stopGenInf H ω}
      (fun _ => (1 : ℝ≥0∞))) :=
    Measurable.indicator measurable_const (measurableSet_stopGenInf_gt H k)
  have h2 : (Set.indicator {ω : ℕ → G | (k : ℝ≥0∞) < stopGenInf H ω} (fun _ => (1 : ℝ≥0∞)))
      = fun ω : ℕ → G => (if (k : ℝ≥0∞) < stopGenInf H ω then (1 : ℝ≥0∞) else 0) := by
    funext ω
    rw [Set.indicator_apply]
    by_cases h : (k : ℝ≥0∞) < stopGenInf H ω <;> simp [h]
  exact h2 ▸ h1

/-- The truncated expectations: integrating the censored level `min (stopGenInf H ·) L`
under the infinite process law yields the `L`-th partial tail sum, exactly the
window expectation of the finite-window censored time. -/
theorem lintegral_min_stopGenInf (H : AddSubgroup G) (L : ℕ) :
    ∫⁻ (ω : ℕ → G), min (stopGenInf H ω) (L : ℝ≥0∞) ∂(unifSubSeq H) =
      ∑ k ∈ Finset.range L, ENNReal.ofReal (failProbAt H k) := by
  have hfun : (fun ω : ℕ → G => min (stopGenInf H ω) (L : ℝ≥0∞))
      = fun ω => ∑ k ∈ Finset.range L,
          (if (k : ℝ≥0∞) < stopGenInf H ω then (1 : ℝ≥0∞) else 0) :=
    funext fun ω => stopGenInf_min_eq_sum H ω L
  rw [hfun, lintegral_finsetSum _ (fun k _ => measurable_stopGenInf_tail H k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hind : (fun ω : ℕ → G => (if (k : ℝ≥0∞) < stopGenInf H ω then (1 : ℝ≥0∞) else 0))
      = Set.indicator {ω : ℕ → G | (k : ℝ≥0∞) < stopGenInf H ω} (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    rw [Set.indicator_apply]
    by_cases h : (k : ℝ≥0∞) < stopGenInf H ω <;> simp [h]
  rw [hind, lintegral_indicator (measurableSet_stopGenInf_gt H k), setLIntegral_one,
    measure_stopGenInf_gt H k]

/-- THE COMPLETE EXPECTATION, exact series form: the expectation of the uncensored
first-generation stopping time under the infinite iid process law equals the sum of
the generation-failure probabilities over all `k`,
`E[T] = ∑' k, failProbAt H k`. This is the limit of the finite-window window identities
`E[stopGen] = Σ_{k<L} failProbAt H k`, obtained by monotone convergence over the
censored levels `min T L ↑ T`. -/
theorem stopGenInf_lintegral_eq (H : AddSubgroup G) :
    ∫⁻ (ω : ℕ → G), stopGenInf H ω ∂(unifSubSeq H) =
      ∑' k, ENNReal.ofReal (failProbAt H k) := by
  have hfi : (fun ω : ℕ → G => stopGenInf H ω)
      = fun ω => ⨆ L : ℕ, min (stopGenInf H ω) (L : ℝ≥0∞) :=
    funext fun ω => stopGenInf_eq_iSup_min H ω
  have hmeas : ∀ L : ℕ,
      Measurable (fun ω : ℕ → G => min (stopGenInf H ω) (L : ℝ≥0∞)) := by
    intro L
    have hfunL : (fun ω : ℕ → G => min (stopGenInf H ω) (L : ℝ≥0∞))
        = fun ω => ∑ k ∈ Finset.range L,
            (if (k : ℝ≥0∞) < stopGenInf H ω then (1 : ℝ≥0∞) else 0) :=
      funext fun ω => stopGenInf_min_eq_sum H ω L
    rw [hfunL]
    exact measurable_finset_sum' _ _ fun k _ => measurable_stopGenInf_tail H k
  have hmono : Monotone (fun L : ℕ => fun ω : ℕ → G =>
      min (stopGenInf H ω) ((L : ℕ) : ℝ≥0∞)) := by
    intro L1 L2 hL
    apply Pi.le_def.mpr
    intro ω
    exact min_le_min (le_refl _) (natCast_le_iff.mpr hL)
  rw [hfi, lintegral_iSup hmeas hmono,
    ENNReal.tsum_eq_iSup_nat (f := fun k => ENNReal.ofReal (failProbAt H k))]
  exact iSup_congr fun L => lintegral_min_stopGenInf H L

/-- THE COMPLETE EXPECTATION BOUND (Section 2 of the source): the
expected number of uniform samples needed to generate `H`, for the uncensored
stopping time of the infinite process, is at most `2 log₂ |H|` for every
`|H| ≥ 2`. The uniform window bound `expected_le_two_log` is transported through
the monotone limit. -/
theorem stopGenInf_lintegral_le (H : AddSubgroup G) (hH : 2 ≤ Fintype.card ↥H) :
    ∫⁻ (ω : ℕ → G), stopGenInf H ω ∂(unifSubSeq H) ≤
      ENNReal.ofReal (2 * Real.logb 2 (Fintype.card ↥H : ℝ)) := by
  rw [stopGenInf_lintegral_eq,
    ENNReal.tsum_eq_iSup_nat (f := fun k => ENNReal.ofReal (failProbAt H k))]
  refine iSup_le fun L => ?_
  rw [← ofReal_sum_finset (Finset.range L) (fun k => failProbAt H k)
    (fun k _ => failProbAt_nonneg H k)]
  exact ENNReal.ofReal_le_ofReal (expected_le_two_log H hH L)

/-- Real-valued form of the complete expectation bound. -/
theorem stopGenInf_lintegral_toReal_le (H : AddSubgroup G) (hH : 2 ≤ Fintype.card ↥H) :
    (∫⁻ (ω : ℕ → G), stopGenInf H ω ∂(unifSubSeq H)).toReal ≤
      2 * Real.logb 2 (Fintype.card ↥H : ℝ) := by
  have h1 := stopGenInf_lintegral_le H hH
  have hintne : (∫⁻ (ω : ℕ → G), stopGenInf H ω ∂(unifSubSeq H)) ≠ ⊤ := by
    intro h
    rw [h] at h1
    exact ENNReal.ofReal_ne_top (top_le_iff.mp h1)
  have h2 : (∫⁻ (ω : ℕ → G), stopGenInf H ω ∂(unifSubSeq H)).toReal
      ≤ (ENNReal.ofReal (2 * Real.logb 2 (Fintype.card ↥H : ℝ))).toReal :=
    (ENNReal.toReal_le_toReal hintne ENNReal.ofReal_ne_top).mpr h1
  rwa [ENNReal.toReal_ofReal (mul_nonneg zero_le_two
    (Real.logb_nonneg (by norm_num)
      (by exact_mod_cast (Nat.le_trans (by norm_num : (1:ℕ) ≤ 2) hH))))] at h2

omit [DecidableEq G] in
/-- Honesty of the limit object: the uncensored stopping time is finite almost
surely — the event that generation never happens is null (the failure
probabilities decay geometrically by `failProb_le`). -/
theorem measure_stopGenInf_top (H : AddSubgroup G) :
    unifSubSeq H {ω : ℕ → G | stopGenInf H ω = ⊤} = 0 := by
  classical
  have hsub : ∀ k : ℕ, {ω : ℕ → G | stopGenInf H ω = ⊤} ⊆
      {ω : ℕ → G | (k : ℝ≥0∞) < stopGenInf H ω} := by
    intro k ω hω
    show (k : ℝ≥0∞) < stopGenInf H ω
    rw [hω]
    exact ENNReal.natCast_lt_top k
  have hle : ∀ k : ℕ, unifSubSeq H {ω : ℕ → G | stopGenInf H ω = ⊤}
      ≤ ENNReal.ofReal (((Fintype.card ↥H - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) := by
    intro k
    have hmono : unifSubSeq H {ω : ℕ → G | stopGenInf H ω = ⊤}
        ≤ unifSubSeq H {ω : ℕ → G | (k : ℝ≥0∞) < stopGenInf H ω} := measure_mono (hsub k)
    rw [measure_stopGenInf_gt H k] at hmono
    exact hmono.trans (ENNReal.ofReal_le_ofReal (failProb_le H k))
  by_contra hne
  have h0 : 0 < unifSubSeq H {ω : ℕ → G | stopGenInf H ω = ⊤} := by
    rcases lt_or_ge (0 : ℝ≥0∞) (unifSubSeq H {ω : ℕ → G | stopGenInf H ω = ⊤}) with h | h
    · exact h
    · exact absurd (le_zero_iff.mp h) hne
  have hfin : unifSubSeq H {ω : ℕ → G | stopGenInf H ω = ⊤} ≠ ⊤ := by
    intro h
    rw [h] at hle
    exact absurd (hle 0) (by simp)
  set c : ℝ≥0∞ := unifSubSeq H {ω : ℕ → G | stopGenInf H ω = ⊤} with hc
  have htoR : ENNReal.ofReal c.toReal = c := ENNReal.ofReal_toReal hfin
  have htpos : 0 < c.toReal := ENNReal.toReal_pos (ne_of_gt h0) hfin
  have hbind : ∀ k : ℕ,
      c.toReal ≤ (((Fintype.card ↥H - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) := by
    intro k
    have hle2 : ENNReal.ofReal c.toReal
        ≤ ENNReal.ofReal (((Fintype.card ↥H - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) := by
      rw [htoR]
      exact hle k
    have hstep := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top).mpr hle2
    have hxnn : 0 ≤ (((Fintype.card ↥H - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) :=
      mul_nonneg (Nat.cast_nonneg _) (by positivity)
    rw [ENNReal.toReal_ofReal htpos.le, ENNReal.toReal_ofReal hxnn] at hstep
    exact hstep
  obtain ⟨N, hN⟩ := exists_nat_gt ((((Fintype.card ↥H - 1 : ℕ) : ℝ)) / c.toReal)
  have hN2 : (((Fintype.card ↥H - 1 : ℕ) : ℝ)) < ((2 : ℝ) ^ N) * c.toReal := by
    rw [← div_lt_iff₀ htpos]
    exact lt_of_lt_of_le hN (by exact_mod_cast (le_two_pow_self N))
  have hlt : (((Fintype.card ↥H - 1 : ℕ) : ℝ)) * (1 / 2 : ℝ) ^ N < c.toReal := by
    rw [show (1 / 2 : ℝ) ^ N = 1 / ((2 : ℝ) ^ N) from one_div_pow (2 : ℝ) N,
      mul_one_div, div_lt_iff₀ (pow_pos two_pos N), mul_comm]
    exact hN2
  exact absurd (hbind N) (not_le.mpr hlt)

/-- Bridge to the finite-window window expectation: integrating the window-censored time
(read through the window of an infinite draw sequence) under the infinite process
law yields exactly the window expectation `expectRecord (unifOnSub H) (stopGen H)`
of the finite framework. -/
theorem lintegral_windowOf_expect (H : AddSubgroup G) (L : ℕ) :
    ∫⁻ (ω : ℕ → G), ((stopGen H (windowOf L ω) : ℕ) : ℝ≥0∞) ∂(unifSubSeq H) =
      ENNReal.ofReal (expectRecord (L := L) (unifOnSub H) (stopGen H)) := by
  have hfun : (fun ω : ℕ → G => ((stopGen H (windowOf L ω) : ℕ) : ℝ≥0∞))
      = fun ω => min (stopGenInf H ω) (L : ℝ≥0∞) :=
    funext fun ω => stopGen_windowOf H L ω
  rw [hfun, lintegral_min_stopGenInf H L, stopGen_tailsum H L,
    ← ofReal_sum_finset (Finset.range L) (fun k => failProbAt H k)
      (fun k _ => failProbAt_nonneg H k)]

end Expectation

end Qatlib.Papers.ExactSimon97.SampleStoppingInf
