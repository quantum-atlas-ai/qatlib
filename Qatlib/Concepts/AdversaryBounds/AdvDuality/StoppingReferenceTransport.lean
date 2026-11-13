/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.StoppingReferenceTransportDefs

/-!
# Stopping, sampling, and instrument transport laws

This module relates finite-fuel stopping laws, accumulated charges, and exact fair-bit sampling
to their marginals and limiting masses. It proves truncation identities, resource-transport
statements, and concrete examples with zero costs, positive costs, and infinite zero-charge
evolution.

For quantum instruments, it identifies event branch maps with unnormalized post-measurement
states, proves the normalized mixture formula, and transports these descriptions through
coarsening and feed-forward composition. The instrument viewpoint follows the operational
framework of [DaviesLewis1970].

## Main statements

* `clause16_complete`: bundles exact sampling, tail truncation, and resource transport.
* `walkGoal_complete`: bundles event-state correspondence, mixtures, and downstream instrument
  laws.
* `clause14_complete`: bundles stopping semantics and charge-sensitive examples.

## References

* [Davies and Lewis, 1970][DaviesLewis1970]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ZeroCostLimit.FirstHitMass
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.ZeroCostLimit.FirstHitMass
open scoped ENNReal BigOperators Classical Matrix ComplexOrder

/-- Mapping a probability mass function first by `f` and then by `g` equals mapping it by their
composition. -/
theorem map_map_law {α β γ : Type} (p : PMF α) (f : α → β) (g : β → γ) :
    (p.map f).map g = p.map (fun a => g (f a)) := by
  simp only [PMF.map]
  rw [PMF.bind_bind]
  apply congrArg (PMF.bind p)
  funext a
  change (PMF.pure (f a)).bind (PMF.pure ∘ g) = PMF.pure (g (f a))
  rw [PMF.pure_bind]
  rfl

/-- Mapping a probability mass function by the identity leaves it unchanged. -/
theorem map_id_law {α : Type} (p : PMF α) : p.map (fun a => a) = p := by
  simpa only [PMF.map] using! PMF.bind_pure p

/-- The probability of an output decoded from fair bits is the number of bit assignments
decoding to it divided by `2 ^ Fintype.card R`. -/
theorem clause16_sampler_law {X R : Type} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
    (decode : (R → Bool) → X) (x : X) :
    bitDecodeSampler decode x =
      ((Finset.univ.filter (fun ω : R → Bool => decode ω = x)).card : ℝ≥0∞) /
        (2 ^ Fintype.card R) := by
  classical
  have hboole : (∑ ω : R → Bool, (if x = decode ω then 1 else 0 : ℝ≥0∞)) =
      ((Finset.univ.filter (fun ω : R → Bool => x = decode ω)).card : ℝ≥0∞) :=
    Finset.sum_boole _ _
  have hfilter :
      (Finset.univ.filter (fun ω : R → Bool => x = decode ω) : Finset (R → Bool)) =
        (Finset.univ.filter (fun ω : R → Bool => decode ω = x) : Finset (R → Bool)) := by
    apply Finset.filter_congr
    intro ω hω
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  unfold bitDecodeSampler
  rw [PMF.map_apply]
  simp only [PMF.ofFintype_apply]
  calc
    (∑' ω : R → Bool, if x = decode ω then (2 ^ Fintype.card R : ℝ≥0∞)⁻¹ else 0)
        = (2 ^ Fintype.card R : ℝ≥0∞)⁻¹ *
            ∑ ω : R → Bool, (if x = decode ω then 1 else 0 : ℝ≥0∞) := by
          rw [tsum_fintype]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω _
          by_cases h : x = decode ω <;> simp [h, mul_zero]
    _ = (2 ^ Fintype.card R : ℝ≥0∞)⁻¹ *
            ((Finset.univ.filter (fun ω : R → Bool => x = decode ω)).card : ℝ≥0∞) := by
          rw [hboole]
    _ = ((Finset.univ.filter (fun ω : R → Bool => decode ω = x)).card : ℝ≥0∞) /
          (2 ^ Fintype.card R) := by
          rw [hfilter, div_eq_mul_inv, mul_comm]

/-- Projecting away the constant sampling charge recovers the decoded fair-bit distribution. -/
theorem clause16_sampler_charge_marginal {X R : Type} [Fintype X] [DecidableEq X] [Fintype R]
    [DecidableEq R] (decode : (R → Bool) → X) :
    (samplerCharge (Fintype.card R) (bitDecodeSampler decode)).map Prod.fst =
      bitDecodeSampler decode := by
  classical
  rw [samplerCharge, map_map_law]
  exact map_id_law _

/-- Attaching constant charge `n` to every outcome of a probability mass function gives expected
cost `n`. -/
theorem expectedCost_const_charge {α : Type} (p : PMF α) (n : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (p.map (fun x => (x, n))) = (n : ℝ≥0∞) := by
  classical
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  have h : (fun a : α => (fun x : α × ℕ => (x.2 : ℝ≥0∞)) ((fun x : α => (x, n)) a)) =
      (fun _ => (n : ℝ≥0∞)) := by
    funext a
    simp
  rw [h, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const]

/-- The expected charge of the fair-bit decoder sampler is the number of available bit
positions. -/
theorem clause16_sampler_expected_cost {X R : Type} [Fintype X] [DecidableEq X] [Fintype R]
    [DecidableEq R] (decode : (R → Bool) → X) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (samplerCharge (Fintype.card R) (bitDecodeSampler decode)) =
      (Fintype.card R : ℝ≥0∞) := by
  classical
  unfold samplerCharge
  exact expectedCost_const_charge _ _

/-- Every supported outcome of the constantly charged fair-bit sampler has charge `Fintype.card
R`. -/
theorem clause16_sampler_support {X R : Type} [Fintype X] [DecidableEq X] [Fintype R]
    [DecidableEq R] (decode : (R → Bool) → X) :
    ∀ y ∈ (samplerCharge (Fintype.card R) (bitDecodeSampler decode)).support,
      y.2 = Fintype.card R := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
  rfl

/-- Finite-fuel halting mass plus pending mass equals one. A pending-mass bound `ε` therefore
gives halting mass at least `1 - ε`. -/
theorem clause16_tail_truncation :
    ∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
      (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S) (fuel : ℕ),
      (∑ o : O, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k) +
        pendingMass next cfg fuel = 1 ∧
      (∀ ε : ℝ≥0∞, pendingMass next cfg fuel ≤ ε →
        1 - ε ≤ ∑ o : O, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k) := by
  intro S O _ _ _ _ next cfg fuel
  have hpart : (∑ o : O, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k) +
      pendingMass next cfg fuel = 1 :=
    (unbounded_finite_halt_pending_partition next cfg fuel).2.1
  refine ⟨hpart, ?_⟩
  intro ε hε
  have hpend1 : pendingMass next cfg fuel ≤ 1 := by
    have hle : pendingMass next cfg fuel ≤
        pendingMass next cfg fuel + (∑ o : O, ∑ k ∈ Finset.range (fuel + 1),
          haltJoint next cfg o k) := by
      exact le_add_right (le_refl _)
    rw [add_comm, hpart] at hle
    exact hle
  have hne : pendingMass next cfg fuel ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hpend1 ENNReal.one_lt_top)
  have hsum : (∑ o : O, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k) +
      pendingMass next cfg fuel - pendingMass next cfg fuel =
      (∑ o : O, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k) :=
    ENNReal.add_sub_cancel_right hne
  have h1 : (1 : ℝ≥0∞) - pendingMass next cfg fuel =
      (∑ o : O, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k) := by
    rw [← hpart]
    exact hsum
  have h2 : (1 : ℝ≥0∞) - ε ≤ (1 : ℝ≥0∞) - pendingMass next cfg fuel :=
    tsub_le_tsub (le_refl 1) hε
  exact h2.trans h1.le

/-- Micro-executions compose across fuel splits and record the reversed consumed word prefix in
their log. Up to the word length, they preserve the reference and possess the stated bit,
time, space, and zero-error resource record. -/
theorem clause16_sampler_resource_transport :
    ∀ (I R : Type) [Fintype I] [DecidableEq I] (O : Matrix I I ℂ) (m n : ℕ)
      (cfg : InterruptConfig I R),
      runFor (microNext O) (m + n) (microLaunch cfg) =
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (runFor (microNext O) m (microLaunch cfg)) (runFor (microNext O) n) ∧
      (∀ k : ℕ, (microAfter O k cfg).log = (cfg.word.take k).reverse ++ cfg.log) ∧
      (∀ k : ℕ, k ≤ cfg.word.length →
        (microAfter O k cfg).ref = cfg.ref ∧
          ∃ r : SamplerResources,
            r.bits = k ∧ r.bitTime = k ∧ r.space = cfg.word.length ∧ r.error = 0) := by
  intro I R _ _ O m n cfg
  refine ⟨runFor_add (microNext O) m n (microLaunch cfg), ?_, ?_⟩
  · intro k
    rw [microAfter_spec]
  · intro k hk
    rw [microAfter_spec]
    exact ⟨rfl, ⟨⟨k, k, cfg.word.length, 0⟩, rfl, rfl, rfl, rfl⟩⟩

/-- The fair-bit decoder has its exact counting law and unchanged output marginal after
charging, with constant supported charge and expected cost equal to the number of bit
positions. -/
theorem clause16_sampler_exact :
    ∀ (X R : Type) [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
      (decode : (R → Bool) → X) (x : X),
      bitDecodeSampler decode x =
        ((Finset.univ.filter (fun ω : R → Bool => decode ω = x)).card : ℝ≥0∞) /
          (2 ^ Fintype.card R) ∧
      (samplerCharge (Fintype.card R) (bitDecodeSampler decode)).map Prod.fst =
        bitDecodeSampler decode ∧
      (∀ y ∈ (samplerCharge (Fintype.card R) (bitDecodeSampler decode)).support,
        y.2 = Fintype.card R) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (samplerCharge (Fintype.card R) (bitDecodeSampler decode)) =
        (Fintype.card R : ℝ≥0∞) := by
  intro X R _ _ _ _ decode x
  exact ⟨clause16_sampler_law decode x, clause16_sampler_charge_marginal decode,
    clause16_sampler_support decode, clause16_sampler_expected_cost decode⟩

/-- The bundled exact-sampling, finite-tail truncation, and sampler-resource transport claim
holds. -/
theorem clause16_complete : Clause16Claim :=
  ⟨clause16_sampler_exact, clause16_tail_truncation, clause16_sampler_resource_transport⟩

variable {X : Type}

/-- The output marginal of a `ChargedSampler`'s charged law is its original law. -/
theorem clause16_charged_sampler_marginal (C : ChargedSampler X) :
    C.chargedLaw.map Prod.fst = C.law := by
  classical
  rw [ChargedSampler.chargedLaw, map_map_law]
  have h : (fun a : X => Prod.fst (a, C.price a)) = (fun a : X => a) := by
    funext a
    rfl
  rw [h, map_id_law]

/-- Every supported outcome-charge pair of a charged sampler has charge equal to the outcome's
price. -/
theorem clause16_charged_sampler_cost (C : ChargedSampler X) :
    ∀ y ∈ C.chargedLaw.support, y.2 = C.price y.1 := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
  rfl

/-- The expected cost of a charged sampler is the sum of each outcome probability multiplied by
its price. -/
theorem clause16_charged_sampler_expected_cost (C : ChargedSampler X) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost C.chargedLaw =
      ∑' x, C.law x * (C.price x : ℝ≥0∞) := by
  classical
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
  unfold ChargedSampler.chargedLaw
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rfl

variable {X : Type} [Fintype X] [DecidableEq X] {D E : ℕ}

/-- Applying an instrument's event branch map equals summing its branches over the event. -/
theorem eventBranchMap_apply (I : Instrument X D E) (ρ : Operator D) (Ev : X → Prop)
    [DecidablePred Ev] :
    eventBranchMap I Ev ρ = ∑ x ∈ Finset.univ.filter Ev, I.branch x ρ := by
  rw [eventBranchMap, LinearMap.sum_apply]

/-- An instrument's event probability is the sum of its outcome probabilities over the event. -/
theorem eventProb_eq_sum (I : Instrument X D E) (ρ : Operator D) (Ev : X → Prop)
    [DecidablePred Ev] :
    eventProb I ρ Ev = ∑ x ∈ Finset.univ.filter Ev, instrumentProb I ρ x := rfl

/-- The trace of the event branch output equals the sum of the traces of its constituent branch
outputs. -/
theorem eventBranchMap_trace (I : Instrument X D E) (ρ : Operator D) (Ev : X → Prop)
    [DecidablePred Ev] :
    Matrix.trace (eventBranchMap I Ev ρ) =
      ∑ x ∈ Finset.univ.filter Ev, Matrix.trace (I.branch x ρ) := by
  rw [eventBranchMap_apply, Matrix.trace_sum]

/-- The real part of the event branch output's trace equals the event probability. -/
theorem eventBranchMap_trace_re (I : Instrument X D E) (ρ : Operator D) (Ev : X → Prop)
    [DecidablePred Ev] :
    (Matrix.trace (eventBranchMap I Ev ρ)).re = eventProb I ρ Ev := by
  rw [eventBranchMap_trace, Complex.re_sum, eventProb_eq_sum]
  apply Finset.sum_congr rfl
  intro x _
  rfl

/-- The event branch map of an instrument sends a positive semidefinite input to a positive
semidefinite output. -/
theorem eventBranchMap_posSemidef (I : Instrument X D E) (ρ : Operator D) (hρ : ρ.PosSemidef)
    (Ev : X → Prop) [DecidablePred Ev] :
    (eventBranchMap I Ev ρ).PosSemidef := by
  have hmain : ∀ (s : Finset X) (A : Operator D),
      (∀ x ∈ s, (I.branch x A).PosSemidef) →
        (∑ x ∈ s, I.branch x A).PosSemidef := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro A _
        exact Matrix.PosSemidef.zero
    | @insert x s hx ih =>
        intro A hA
        rw [Finset.sum_insert hx]
        exact Matrix.PosSemidef.add (hA x (Finset.mem_insert.mpr (Or.inl rfl)))
          (ih A fun y hy => hA y (Finset.mem_insert.mpr (Or.inr hy)))
  rw [eventBranchMap_apply]
  exact hmain _ _ fun x _ => (I.cp x).positive hρ

/-- For a positive semidefinite input, an event of zero probability has zero event branch
output. -/
theorem eventBranchMap_eq_zero (I : Instrument X D E) (ρ : Operator D) (hρ : ρ.PosSemidef)
    (Ev : X → Prop) [DecidablePred Ev] (hp : eventProb I ρ Ev = 0) :
    eventBranchMap I Ev ρ = 0 := by
  classical
  have hsum : ∑ x ∈ Finset.univ.filter Ev, instrumentProb I ρ x = 0 := by
    rw [← eventProb_eq_sum, hp]
  rw [eventBranchMap_apply]
  apply Finset.sum_eq_zero
  intro x hx
  have hle : instrumentProb I ρ x ≤ ∑ y ∈ Finset.univ.filter Ev, instrumentProb I ρ y :=
    Finset.single_le_sum (fun y _ => instrumentProb_nonneg I hρ y) hx
  rw [hsum] at hle
  have hz : instrumentProb I ρ x = 0 :=
    le_antisymm hle (instrumentProb_nonneg I hρ x)
  rw [(instrumentProb_eq_zero_iff I hρ x).mp hz]

/-- For a density input, the event branch output is the event probability times the normalized
post-measurement state, and its real trace is that probability. A zero-probability event has
zero branch output and normalized state, while a positive-probability event has a density
post-state. -/
theorem walkGoal_correspondence :
    ∀ (X : Type) [Fintype X] [DecidableEq X] (D E : ℕ) (I : Instrument X D E)
      (ρ : Operator D) (hρ : IsDensityOperator ρ) (Ev : X → Prop) [DecidablePred Ev],
      eventBranchMap I Ev ρ = ((eventProb I ρ Ev : ℝ) : ℂ) • normalizedPost I ρ Ev ∧
        (Matrix.trace (eventBranchMap I Ev ρ)).re = eventProb I ρ Ev ∧
        (eventProb I ρ Ev = 0 →
          eventBranchMap I Ev ρ = 0 ∧ normalizedPost I ρ Ev = 0) ∧
        (0 < eventProb I ρ Ev → IsDensityOperator (normalizedPost I ρ Ev)) := by
  intro X _ _ D E I ρ hρ Ev _
  have htrace : (Matrix.trace (eventBranchMap I Ev ρ)).re = eventProb I ρ Ev :=
    eventBranchMap_trace_re I ρ Ev
  by_cases hp : eventProb I ρ Ev = 0
  · have hnlt : ¬ 0 < eventProb I ρ Ev := by rw [hp]; exact lt_irrefl 0
    refine ⟨?_, htrace, ?_, ?_⟩
    · have hz := eventBranchMap_eq_zero I ρ hρ.1 Ev hp
      rw [hz, normalizedPost, if_neg hnlt]
      simp
    · intro _
      refine ⟨eventBranchMap_eq_zero I ρ hρ.1 Ev hp, ?_⟩
      rw [normalizedPost, if_neg hnlt]
    · intro hpos
      exact absurd hpos hnlt
  · have hnonneg : 0 ≤ eventProb I ρ Ev := by
      rw [eventProb_eq_sum]
      exact Finset.sum_nonneg fun x _ => instrumentProb_nonneg I hρ.1 x
    have hpos : 0 < eventProb I ρ Ev := by
      rcases lt_or_eq_of_le hnonneg with h | h
      · exact h
      · exact absurd h.symm hp
    have hne : ((eventProb I ρ Ev : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hpos
    have hinv : (0 : ℂ) ≤ (((eventProb I ρ Ev : ℝ) : ℂ))⁻¹ := by
      rw [← Complex.ofReal_inv]
      exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr hnonneg)
    refine ⟨?_, htrace, ?_, ?_⟩
    · rw [normalizedPost, if_pos hpos, smul_smul, mul_inv_cancel₀ hne, one_smul]
    · intro hzero
      exact absurd hzero hp
    · intro _
      rw [normalizedPost, if_pos hpos]
      refine ⟨Matrix.PosSemidef.smul (eventBranchMap_posSemidef I ρ hρ.1 Ev) hinv, ?_⟩
      rw [Matrix.trace_smul]
      have htr : (∑ x ∈ Finset.univ.filter Ev, Matrix.trace (I.branch x ρ)) =
          ((eventProb I ρ Ev : ℝ) : ℂ) := by
        calc
          (∑ x ∈ Finset.univ.filter Ev, Matrix.trace (I.branch x ρ)) =
              ∑ x ∈ Finset.univ.filter Ev, ((instrumentProb I ρ x : ℝ) : ℂ) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [trace_branch_eq I hρ.1 x]
          _ = ((∑ x ∈ Finset.univ.filter Ev, instrumentProb I ρ x : ℝ) : ℂ) :=
            Complex.ofReal_sum _ _ |>.symm
          _ = ((eventProb I ρ Ev : ℝ) : ℂ) := by rw [eventProb_eq_sum]
      rw [eventBranchMap_trace, htr, smul_eq_mul, inv_mul_cancel₀ hne]

/-- The sums of an extended-nonnegative-valued function over an event and its complement add to
its sum over the whole finite type. -/
theorem sum_filter_split {O : Type} [Fintype O] [DecidableEq O] (f : O → ℝ≥0∞)
    (Ev : O → Prop) [DecidablePred Ev] :
    (∑ o ∈ Finset.univ.filter Ev, f o) + (∑ o ∈ Finset.univ.filter (fun o => ¬ Ev o), f o)
      = ∑ o : O, f o := by
  have key : ∀ (g : O → ℝ≥0∞) (p : O → Prop) [DecidablePred p],
      (∑ o ∈ Finset.univ.filter p, g o) = ∑ o : O, (if p o then g o else 0) := by
    intro g p _
    have h := Finset.sum_subset (s₁ := Finset.univ.filter p) (s₂ := (Finset.univ : Finset O))
      (f := fun o => if o ∈ Finset.univ.filter p then g o else 0)
      (Finset.filter_subset _ _) (by intro x _ hx; simp [hx])
    have h' : (∑ x ∈ Finset.univ.filter p, (if x ∈ Finset.univ.filter p then g x else 0))
        = ∑ x ∈ Finset.univ.filter p, g x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [hx]
    rw [h'] at h
    calc
      (∑ o ∈ Finset.univ.filter p, g o)
          = ∑ o : O, (if o ∈ Finset.univ.filter p then g o else 0) := by
            exact h
      _ = ∑ o : O, (if p o then g o else 0) := by
        apply Finset.sum_congr rfl
        intro o _
        simp [Finset.mem_filter]
  rw [key f Ev, key f (fun o => ¬ Ev o), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro o _
  by_cases ho : Ev o <;> simp [ho]

/-- For a density input, the normalized post-state of an event is the mixture of its
positive-probability conditional branch states weighted by their probabilities divided by
the event probability. -/
theorem walkGoal_mixture :
    ∀ (X : Type) [Fintype X] [DecidableEq X] (D E : ℕ) (I : Instrument X D E)
      (ρ : Operator D) (hρ : IsDensityOperator ρ) (Ev : X → Prop) [DecidablePred Ev],
      normalizedPost I ρ Ev =
        ∑ x ∈ Finset.univ.filter Ev,
          if h : 0 < instrumentProb I ρ x then
            ((((instrumentProb I ρ x) / eventProb I ρ Ev : ℝ) : ℂ)) •
              I.conditionalState ρ x h
          else 0 := by
  intro X _ _ D E I ρ hρ Ev _
  by_cases hp : eventProb I ρ Ev = 0
  · have hnlt : ¬ 0 < eventProb I ρ Ev := by rw [hp]; exact lt_irrefl 0
    have hsum : ∑ x ∈ Finset.univ.filter Ev, instrumentProb I ρ x = 0 := by
      rw [← eventProb_eq_sum, hp]
    have hzero : ∀ x ∈ Finset.univ.filter Ev, instrumentProb I ρ x = 0 := by
      intro x hx
      have hle : instrumentProb I ρ x ≤ ∑ y ∈ Finset.univ.filter Ev, instrumentProb I ρ y :=
        Finset.single_le_sum (fun y _ => instrumentProb_nonneg I hρ.1 y) hx
      rw [hsum] at hle
      exact le_antisymm hle (instrumentProb_nonneg I hρ.1 x)
    rw [normalizedPost, if_neg hnlt]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    by_cases ho : 0 < instrumentProb I ρ x
    · exfalso
      have hz := hzero x hx
      rw [hz] at ho
      exact (lt_irrefl 0 ho)
    · rw [dif_neg ho]
  · have hnonneg : 0 ≤ eventProb I ρ Ev := by
      rw [eventProb_eq_sum]
      exact Finset.sum_nonneg fun x _ => instrumentProb_nonneg I hρ.1 x
    have hpos : 0 < eventProb I ρ Ev := by
      rcases lt_or_eq_of_le hnonneg with h | h
      · exact h
      · exact absurd h.symm hp
    have hne : ((eventProb I ρ Ev : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hpos
    let μ : ℝ := eventProb I ρ Ev
    rw [normalizedPost, if_pos hpos]
    change (μ : ℂ)⁻¹ • ((∑ x ∈ Finset.univ.filter Ev, I.branch x) ρ) = _
    rw [LinearMap.sum_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases ho : 0 < instrumentProb I ρ x
    · rw [dif_pos ho, ← (Qatlib.Concepts.QuditTeleport.TeleportCore.Instrument.conditionalState_reconstruction I ρ x ho).1, smul_smul]
      congr 1
      simp only [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]
      dsimp [μ]
      ring
    · have hz : instrumentProb I ρ x = 0 :=
        le_antisymm (not_lt.mp ho) (instrumentProb_nonneg I hρ.1 x)
      rw [dif_neg ho, (instrumentProb_eq_zero_iff I hρ.1 x).mp hz, smul_zero]

/-- An event defined by a coarsening fiber has the branch map and probability of that coarse
outcome. Finite-fuel halting masses for an event and its complement, together with pending
mass, sum to one. -/
theorem walkGoal_coarse_residual :
    (∀ (X P : Type) [Fintype X] [DecidableEq X] [Fintype P] [DecidableEq P]
      (D E : ℕ) (I : Instrument X D E) (f : X → P) (p : P),
        eventBranchMap I (fun x => f x = p) = (I.coarsen f).branch p ∧
          ∀ (ρ : Operator D),
            eventProb I ρ (fun x => f x = p) = instrumentProb (I.coarsen f) ρ p) ∧
    (∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
      (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S) (fuel : ℕ) (Ev : O → Prop) [DecidablePred Ev],
        (∑ o ∈ Finset.univ.filter Ev, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k) +
          (∑ o ∈ Finset.univ.filter (fun o => ¬ Ev o),
            ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k) +
          (residualsOf next cfg fuel 0).pending = 1) := by
  constructor
  · intro X P _ _ _ _ D E I f p
    refine ⟨?_, ?_⟩
    · show (∑ x ∈ Finset.univ.filter (fun x => f x = p), I.branch x)
          = ∑ o ∈ Finset.univ.filter (fun o => f o = p), I.branch o
      rfl
    · intro ρ
      rw [eventProb_eq_sum]
      rw [instrumentProb_coarsen I f ρ p]
  · intro S O _ _ _ _ next cfg fuel Ev _
    have hpart : (∑ o : O, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k) +
        pendingMass next cfg fuel = 1 :=
      (unbounded_finite_halt_pending_partition next cfg fuel).2.1
    have hsplit : (∑ o ∈ Finset.univ.filter Ev, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k) +
        (∑ o ∈ Finset.univ.filter (fun o => ¬ Ev o),
          ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k) =
        ∑ o : O, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k :=
      sum_filter_split (fun o => ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k) Ev
    rw [hsplit]
    have hpend : (residualsOf next cfg fuel 0).pending = pendingMass next cfg fuel := rfl
    rw [hpend, hpart]

/-- The Pauli X and Pauli Z matrices do not commute. -/
theorem pauliX_pauliZ_ne : PauliX * PauliZ ≠ PauliZ * PauliX := by
  intro h
  have h1 := congrArg (fun M : Matrix Bool Bool ℂ => M true false) h
  simp only [PauliX, PauliZ, permMatrix, Matrix.mul_apply, Matrix.of_apply,
    Matrix.diagonal_apply, Fintype.sum_bool] at h1
  norm_num at h1

/-- Applying Pauli X and Pauli Z in opposite orders gives different vectors on the basis ket
indexed by false. -/
theorem pauliX_pauliZ_ket_ne :
    ApplyGate PauliX (ApplyGate PauliZ (Qatlib.Foundations.PureStateMath.Ket false)) ≠
      ApplyGate PauliZ (ApplyGate PauliX (Qatlib.Foundations.PureStateMath.Ket false)) := by
  intro h
  have h1 := congrArg (fun v : QState Bool => v true) h
  simp only [ApplyGate, Matrix.mulVec, dotProduct, PauliX, PauliZ, permMatrix,
    Matrix.of_apply, Matrix.diagonal_apply, Fintype.sum_bool, Qatlib.Foundations.PureStateMath.Ket] at h1
  norm_num at h1

/-- Conjugating the outer product of the false basis ket by Pauli X gives a different operator
from conjugating it by Pauli Z. -/
theorem conjByX_outer_ne :
    conjByX (outerProduct (Qatlib.Foundations.PureStateMath.Ket false)) ≠ conjByZ (outerProduct (Qatlib.Foundations.PureStateMath.Ket false)) := by
  intro h
  have h1 := congrArg (fun M : Matrix Bool Bool ℂ => M true true) h
  simp only [conjByX, conjByZ, PauliX, PauliZ, permMatrix, outerProduct,
    Matrix.of_apply, Matrix.diagonal_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_bool, Qatlib.Foundations.PureStateMath.Ket] at h1
  norm_num at h1

/-- Feed-forward instrument branches compose in outcome order, event maps preserve addition and
real scalar multiplication, and pure-state event probabilities equal real branch traces. The
bundled examples also distinguish the stated Pauli operations. -/
theorem walkGoal_downstream :
    (∀ (X : Type) (Q : X → Type) [Fintype X] [∀ o, Fintype (Q o)]
      (D E F : ℕ) (I : Instrument X D E) (J : ∀ o, Instrument (Q o) E F)
      (ρ : Operator D) (o : X) (q : Q o),
        (I.feedForward J).branch ⟨o, q⟩ ρ = (J o).branch q (I.branch o ρ)) ∧
    (PauliX * PauliZ ≠ PauliZ * PauliX ∧
      ApplyGate PauliX (ApplyGate PauliZ (Qatlib.Foundations.PureStateMath.Ket false)) ≠
        ApplyGate PauliZ (ApplyGate PauliX (Qatlib.Foundations.PureStateMath.Ket false)) ∧
      conjByX (outerProduct (Qatlib.Foundations.PureStateMath.Ket false)) ≠ conjByZ (outerProduct (Qatlib.Foundations.PureStateMath.Ket false))) ∧
    (∀ (X : Type) [Fintype X] [DecidableEq X] (D E : ℕ) (I : Instrument X D E)
      (ψ : QState (Fin D)) (Ev : X → Prop) [DecidablePred Ev],
        eventProb I (outerProduct ψ) Ev =
          (Matrix.trace (eventBranchMap I Ev (outerProduct ψ))).re) ∧
    (∀ (X : Type) [Fintype X] [DecidableEq X] (D E : ℕ) (I : Instrument X D E)
      (ρ σ : Operator D) (c : ℝ) (Ev : X → Prop) [DecidablePred Ev],
        eventBranchMap I Ev (((c : ℝ) : ℂ) • ρ) = ((c : ℝ) : ℂ) • eventBranchMap I Ev ρ ∧
          eventBranchMap I Ev (ρ + σ) = eventBranchMap I Ev ρ + eventBranchMap I Ev σ) := by
  constructor
  · intro X Q _ _ D E F I J ρ o q
    rfl
  · constructor
    · constructor
      · exact pauliX_pauliZ_ne
      · constructor
        · exact pauliX_pauliZ_ket_ne
        · exact conjByX_outer_ne
    · constructor
      · intro X _ _ D E I ψ Ev _
        exact (eventBranchMap_trace_re I (outerProduct ψ) Ev).symm
      · intro X _ _ D E I ρ σ c Ev _
        exact ⟨map_smul (eventBranchMap I Ev) _ _, map_add (eventBranchMap I Ev) _ _⟩

/-- The bundled event-state correspondence, conditional mixture, coarsening, residual-mass, and
downstream instrument claim holds. -/
theorem walkGoal_complete : PaidWalkClaim :=
  ⟨walkGoal_correspondence, walkGoal_mixture, walkGoal_coarse_residual, walkGoal_downstream⟩

/-- Applying the charged event map equals summing event branch outputs weighted by their
natural-number prices. -/
theorem walkGoal_charged_map_apply {X : Type} [Fintype X] [DecidableEq X] {D E : ℕ}
    (I : Instrument X D E) (price : X → ℕ) (ρ : Operator D) (Ev : X → Prop) [DecidablePred Ev] :
    chargedEventMap I price Ev ρ = ∑ x ∈ Finset.univ.filter Ev, (price x : ℂ) • (I.branch x ρ) := by
  rw [chargedEventMap, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro x _
  rfl

/-- The real trace of the charged event map output equals the charged event mass. -/
theorem walkGoal_charged_mass_trace {X : Type} [Fintype X] [DecidableEq X] {D E : ℕ}
    (I : Instrument X D E) (price : X → ℕ) (ρ : Operator D) (Ev : X → Prop) [DecidablePred Ev] :
    (Matrix.trace (chargedEventMap I price Ev ρ)).re = chargedEventMass I price ρ Ev := by
  rw [walkGoal_charged_map_apply, Matrix.trace_sum, Complex.re_sum]
  calc
    (∑ x ∈ Finset.univ.filter Ev, ((price x : ℂ) • (I.branch x ρ)).trace.re)
        = ∑ x ∈ Finset.univ.filter Ev, ((price x : ℝ) * instrumentProb I ρ x : ℝ) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Matrix.trace_smul, smul_eq_mul, Complex.mul_re]
          have hre : (↑(price x : ℕ) : ℂ).re = ((price x : ℕ) : ℝ) := by
            exact_mod_cast rfl
          have him : (↑(price x : ℕ) : ℂ).im = 0 := by
            exact_mod_cast rfl
          rw [hre, him, zero_mul, sub_zero]
          rfl
    _ = chargedEventMass I price ρ Ev := rfl

/-- Giving every outcome price one makes the charged event map equal to the ordinary event
branch map. -/
theorem walkGoal_charged_map_unweighted {X : Type} [Fintype X] [DecidableEq X] {D E : ℕ}
    (I : Instrument X D E) (Ev : X → Prop) [DecidablePred Ev] :
    chargedEventMap I (fun _ => 1) Ev = eventBranchMap I Ev := by
  rw [chargedEventMap, eventBranchMap]
  apply Finset.sum_congr rfl
  intro x _
  rw [Nat.cast_one, one_smul]

/-- A charged event map with natural-number prices sends positive semidefinite inputs to
positive semidefinite outputs. -/
theorem walkGoal_charged_map_posSemidef {X : Type} [Fintype X] [DecidableEq X] {D E : ℕ}
    (I : Instrument X D E) (price : X → ℕ) (ρ : Operator D) (hρ : ρ.PosSemidef)
    (Ev : X → Prop) [DecidablePred Ev] :
    (chargedEventMap I price Ev ρ).PosSemidef := by
  have hmain : ∀ (s : Finset X) (A : Operator D),
      (∀ x ∈ s, (I.branch x A).PosSemidef) →
        (∑ x ∈ s, (price x : ℂ) • (I.branch x A)).PosSemidef := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro A _
        exact Matrix.PosSemidef.zero
    | @insert x s hx ih =>
        intro A hA
        rw [Finset.sum_insert hx]
        refine Matrix.PosSemidef.add ?_ (ih A fun y hy => hA y (Finset.mem_insert.mpr (Or.inr hy)))
        have hnonneg : (0 : ℂ) ≤ (price x : ℂ) := by
          exact_mod_cast Nat.zero_le (price x)
        exact Matrix.PosSemidef.smul (hA x (Finset.mem_insert.mpr (Or.inl rfl))) hnonneg
  rw [walkGoal_charged_map_apply]
  exact hmain _ _ fun x _ => (I.cp x).positive hρ

variable {S O : Type} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-- The bundled nontermination-mass semantics `ZeroCostNeverSemantics` holds. -/
theorem clause14_never_semantics : ZeroCostNeverSemantics := by
  intro S O _ _ _ _ next cost cfg
  exact Qatlib.Concepts.ZeroCostLimit.FirstHitMass.g1 S O next cost cfg

/-- The Boolean non-Zeno check succeeds exactly when every state's charge is positive. -/
theorem clause14_nonZenoCheck_iff (S : Type) [Fintype S] [DecidableEq S] (c : S → ℕ) :
    nonZenoCheck c = true ↔ positiveCharge c := by
  classical
  rw [nonZenoCheck, decide_eq_true_eq]
  constructor
  · intro h
    have heq : (Finset.univ.filter (fun s => 0 < c s) : Finset S) = Finset.univ := by
      apply Finset.Subset.antisymm
      · exact Finset.filter_subset _ _
      · intro s hs
        by_cases hpos : 0 < c s
        · exact Finset.mem_filter.mpr ⟨hs, hpos⟩
        · exfalso
          have hlt : ((Finset.univ.filter (fun s => 0 < c s) : Finset S) : Finset S).card
                < (Finset.univ : Finset S).card := by
            refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
              ⟨Finset.filter_subset _ _, ?_⟩)
            intro hcontra
            have hmem : s ∈ (Finset.univ.filter (fun s => 0 < c s) : Finset S) := by
              rw [hcontra]
              exact Finset.mem_univ s
            exact absurd ((Finset.mem_filter.mp hmem).2) hpos
          rw [h] at hlt
          omega
    intro s
    have hmem : s ∈ (Finset.univ.filter (fun s => 0 < c s) : Finset S) := by
      rw [heq]
      exact Finset.mem_univ s
    exact (Finset.mem_filter.mp hmem).2
  · intro h
    have hfilter : (Finset.univ.filter (fun s => 0 < c s) : Finset S) = Finset.univ := by
      apply Finset.ext
      intro s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro _
        trivial
      · intro _
        exact h s
    rw [hfilter]

/-- When every state costs at least one, the finite-fuel mass of a halted outcome with charge
`k` agrees with its weighted halting mass once the fuel is at least `k`. -/
theorem clause14_charge_stable :
    ∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
      (next : S → PMF (O ⊕ S)) (cost : S → ℕ) (hc : ∀ s, 1 ≤ cost s)
      (cfg : O ⊕ S) (o : O) (k fuel : ℕ), k ≤ fuel →
      weightedRunFor next cost fuel cfg (Sum.inl o, k) = weightedHaltJoint next cost cfg o k :=
  fun S O _ _ _ _ next cost hc cfg o k fuel h =>
    weightedRunFor_halt_stable next cost hc cfg o k fuel h

/-- The sum of halting masses through the fuel bound and the pending mass is one. -/
theorem clause14_truncation :
    ∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
      (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S) (fuel : ℕ),
      (∑ o : O, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k) +
        pendingMass next cfg fuel = 1 :=
  fun S O _ _ _ _ next cfg fuel => (unbounded_finite_halt_pending_partition next cfg fuel).2.1

/-- The first-stop mass at a fixed outcome and charge is the supremum of finite-fuel halted
masses, and each finite-fuel law has total halted-plus-running mass one. The finite-fuel
halted masses converge to that first-stop mass whenever it is positive. -/
theorem clause14_first_stop_joint :
    ∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
      (next : S → PMF (O ⊕ S)) (cost : S → ℕ) (cfg : O ⊕ S) (o : O) (k : ℕ),
      haltMass next cost cfg o k = ⨆ fuel : ℕ, weightedRunFor next cost fuel cfg (Sum.inl o, k) ∧
        (∀ fuel : ℕ,
          (∑' o' : O, ∑' k' : ℕ, weightedRunFor next cost fuel cfg (Sum.inl o', k')) +
            (∑ s : S, ∑' j : ℕ, weightedRunFor next cost fuel cfg (Sum.inr s, j)) = 1) ∧
        (0 < haltMass next cost cfg o k →
          Filter.Tendsto (fun fuel => weightedRunFor next cost fuel cfg (Sum.inl o, k))
            Filter.atTop (nhds (haltMass next cost cfg o k))) := by
  intro S O _ _ _ _ next cost cfg o k
  refine ⟨rfl, ?_, ?_⟩
  · intro fuel
    rw [← tsum_fintype (L := SummationFilter.unconditional S)]
    rw [← tsum_sum_type' (F := fun d : O ⊕ S => ∑' k, weightedRunFor next cost fuel cfg (d, k)),
      ← tsum_prod_type' (F := fun z : (O ⊕ S) × ℕ => weightedRunFor next cost fuel cfg z),
      PMF.tsum_coe]
  · intro hpos
    have hm : Monotone (fun fuel => weightedRunFor next cost fuel cfg (Sum.inl o, k)) :=
      weightedRunFor_halt_monotone next cost cfg o k
    simpa [haltMass] using! (tendsto_atTop_iSup hm)

/-- The bundled positive-charge check, charge-stability law, and finite-fuel truncation law
hold. -/
theorem clause14_nonZeno_laws : ZeroCostNonZenoLaws :=
  ⟨clause14_nonZenoCheck_iff, clause14_charge_stable, clause14_truncation⟩

/-- The zero-cost countdown starting from true halts deterministically after two steps with
output unit and zero charge. -/
theorem clause14_zero_countdown_two :
    weightedRunFor zeroCountdownNext (fun _ => 0) 2 (Sum.inr true) = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (Sum.inl ()) := by
  rw [weightedRunFor_succ_running]
  simp only [zeroCountdownNext, if_true, PMF.pure_bind,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_zero]
  rw [weightedRunFor_succ_running]
  simp only [zeroCountdownNext, Bool.false_eq_true, if_false, PMF.pure_bind,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_zero]
  rfl

/-- The zero-cost countdown has mass one at output unit and accumulated charge zero after two
steps. -/
theorem clause14_zero_countdown_mass :
    weightedRunFor zeroCountdownNext (fun _ => 0) 2 (Sum.inr true) (Sum.inl (), 0) = 1 := by
  rw [clause14_zero_countdown_two]
  simp [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_apply]

/-- The zero-cost countdown assigns zero halted mass to every nonzero accumulated charge at
every fuel and initial configuration. -/
theorem clause14_zero_countdown_positive_charge :
    ∀ (fuel : ℕ) (cfg : Unit ⊕ Bool) (k : ℕ), k ≠ 0 →
      weightedRunFor zeroCountdownNext (fun _ => 0) fuel cfg (Sum.inl (), k) = 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro cfg k hk
      simp [weightedRunFor, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_apply,
          hk]
  | succ fuel ih =>
      intro cfg k hk
      cases cfg with
      | inl o =>
          rw [weightedRunFor_halted]
          simp [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_apply, hk]
      | inr s =>
          cases s with
          | true =>
              rw [weightedRunFor_succ_running, zeroCountdownNext, if_pos (by simp)]
              simp only [PMF.pure_bind,
                  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_zero]
              exact ih (Sum.inr false) k hk
          | false =>
              rw [weightedRunFor_succ_running, zeroCountdownNext, if_neg (by simp)]
              simp only [PMF.pure_bind,
                  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_zero]
              exact ih (Sum.inl ()) k hk

/-- The zero-cost countdown starting from true has no pending mass after two steps. -/
theorem clause14_zero_countdown_pending :
    pendingMass zeroCountdownNext (Sum.inr true) 2 = 0 := by
  have hrun : runFor zeroCountdownNext 2 (Sum.inr true) = PMF.pure ((Sum.inl () : Unit ⊕ Bool), 2) := by
    simp only [runFor, tick, zeroCountdownNext, if_true, Bool.false_eq_true, if_false,
      PMF.pure_map, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind, PMF.pure_bind]
    rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_charge,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_ret]
  unfold pendingMass
  apply Finset.sum_eq_zero
  intro s _
  apply Finset.sum_eq_zero
  intro k _
  rw [hrun, PMF.pure_apply]
  simp

/-- The zero-cost countdown stops with total mass one at charge zero, has no mass at nonzero
charges, and has zero nontermination mass. -/
theorem clause14_zero_cost_consumers :
    haltMass zeroCountdownNext (fun _ => 0) (Sum.inr true) () 0 = 1 ∧
      (∀ k : ℕ, k ≠ 0 → haltMass zeroCountdownNext (fun _ => 0) (Sum.inr true) () k = 0) ∧
      nonterminationMass zeroCountdownNext (Sum.inr true) = 0 ∧
      weightedRunFor zeroCountdownNext (fun _ => 0) 2 (Sum.inr true) (Sum.inl (), 0) = 1 := by
  have hsup : (⨆ fuel : ℕ,
      weightedRunFor zeroCountdownNext (fun _ => 0) fuel (Sum.inr true) (Sum.inl (), 0)) = 1 := by
    refine le_antisymm (iSup_le fun fuel => PMF.coe_le_one _ _) ?_
    calc
      1 = (weightedRunFor zeroCountdownNext (fun _ => 0) 2 (Sum.inr true) (Sum.inl (), 0)) :=
        clause14_zero_countdown_mass.symm
      _ ≤ (⨆ fuel : ℕ,
          weightedRunFor zeroCountdownNext (fun _ => 0) fuel (Sum.inr true) (Sum.inl (), 0)) :=
        le_iSup (fun fuel =>
          weightedRunFor zeroCountdownNext (fun _ => 0) fuel (Sum.inr true) (Sum.inl (), 0)) 2
  refine ⟨?_, ?_, ?_, clause14_zero_countdown_mass⟩
  · rw [haltMass, hsup]
  · intro k hk
    refine le_antisymm (iSup_le fun fuel => ?_) bot_le
    exact (clause14_zero_countdown_positive_charge fuel (Sum.inr true) k hk).le
  · refine le_antisymm ?_ bot_le
    show (⨅ fuel : ℕ, pendingMass zeroCountdownNext (Sum.inr true) fuel) ≤ 0
    have h2 : pendingMass zeroCountdownNext (Sum.inr true) 2 = 0 := clause14_zero_countdown_pending
    rw [← sInf_range]
    have hle : (⨅ fuel : ℕ, pendingMass zeroCountdownNext (Sum.inr true) fuel)
        ≤ pendingMass zeroCountdownNext (Sum.inr true) 2 := iInf_le _ 2
    rw [h2] at hle
    exact hle

/-- The specified Zeno process has infinite zero-charge evolution and never stops with mass one. -/
theorem clause14_zeno_consumers :
    zenoZeroCharge zenoNext zenoCharge PUnit.unit ∧
      neverStopMass zenoNext (Sum.inr PUnit.unit) = 1 := by
  refine ⟨Qatlib.Concepts.StoppingCore.InterruptBridge.zenoZeroCharge_fixed, ?_⟩
  show (⨅ k : ℕ, pendingMass zenoNext (Sum.inr PUnit.unit) k) = 1
  simp only [Qatlib.Concepts.StoppingCore.InterruptBridge.pendingMass_zeno]
  simp

/-- The unit-charge function assigns a positive charge to every state. -/
theorem clause14_unit_charge_positive : positiveCharge unitCharge := by
  intro s
  simp [unitCharge]

/-- The countdown with unit charges stops at total charge two with mass one. Its budgeted law is
the initial state below budget one, the intermediate state at budget one, and the halted
output from budget two onward. -/
theorem clause14_positive_cost_consumers :
    positiveCharge unitCharge ∧
      weightedHaltJoint zeroCountdownNext unitCharge (Sum.inr true) () 2 = 1 ∧
      (∀ B : ℕ, weightedBudgetRun zeroCountdownNext unitCharge B (Sum.inr true) =
        if 2 ≤ B then Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 2 (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (Sum.inl ()))
        else if 1 ≤ B then Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (Sum.inr false))
        else Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (Sum.inr true)) := by
  have hhalt : weightedRunFor zeroCountdownNext unitCharge 2 (Sum.inr true) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 2 (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (Sum.inl ())) := by
    rw [weightedRunFor_succ_running]
    simp only [zeroCountdownNext, if_true, PMF.pure_bind]
    rw [weightedRunFor_succ_running]
    simp only [zeroCountdownNext, Bool.false_eq_true, if_false, PMF.pure_bind]
    rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_charge]
    rfl
  have hfalse : ∀ B : ℕ, weightedBudgetRun zeroCountdownNext unitCharge B (Sum.inr false) =
      if 1 ≤ B then Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (Sum.inl ()))
      else Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (Sum.inr false) := by
    intro B
    induction B with
    | zero =>
        rw [weightedBudgetRun]
        simp [unitCharge]
    | succ B ih =>
        rw [weightedBudgetRun]
        simp only [unitCharge]
        split
        · next h =>
            simp only [zeroCountdownNext, Bool.false_eq_true, if_false, PMF.pure_bind]
            rw [weightedBudgetRun_halted,
                Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_ret]
            rfl
        · next h => omega
  refine ⟨clause14_unit_charge_positive, ?_, ?_⟩
  · rw [weightedHaltJoint, hhalt, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_ret, PMF.pure_apply]
    simp
  · intro B
    induction B with
    | zero =>
        rw [weightedBudgetRun]
        simp [unitCharge]
    | succ B ih =>
        rw [weightedBudgetRun]
        simp only [unitCharge]
        split
        · next h =>
            simp only [zeroCountdownNext, if_true, PMF.pure_bind]
            rw [show weightedBudgetRun zeroCountdownNext unitCharge (B + 1 - 1) (Sum.inr false)
              = weightedBudgetRun zeroCountdownNext unitCharge B (Sum.inr false) by
                rw [Nat.add_sub_cancel]]
            by_cases hb1 : 1 ≤ B
            · rw [if_pos (by omega : 2 ≤ B + 1)]
              rw [hfalse B, if_pos hb1]
              exact Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_charge 1 1
                  (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (Sum.inl ()))
            · rw [if_neg (by omega : ¬ 2 ≤ B + 1), if_pos (by omega : 1 ≤ B + 1)]
              rw [hfalse B, if_neg hb1]
        · next h => omega

/-- The bundled nontermination semantics, positive-charge laws, first-stop joint laws, and
zero-cost, Zeno, and positive-cost examples hold. -/
theorem clause14_complete : Clause14Claim := by
  refine ⟨clause14_never_semantics, clause14_nonZeno_laws, clause14_first_stop_joint, ?_⟩
  exact And.intro clause14_zero_cost_consumers
    (And.intro clause14_zeno_consumers clause14_positive_cost_consumers)

end Qatlib.Concepts.AdversaryBounds.AdvDuality
