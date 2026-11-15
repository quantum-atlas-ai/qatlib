/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearchDefs

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AmplitudeCore.InvFreePhase Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout Qatlib.Concepts.WalkSearch.TwoLevelLower Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.StateBlockEncoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.TauEmbedding
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearchDefs

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra

open Matrix
open Qatlib.Concepts.GraphEnergy.ZeroEnergy
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped Classical BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- A state whose inner product with itself is zero is the zero state. -/
private theorem local_inner_self_zero {K : Type} [Fintype K] (w : QState K)
    (h : Qatlib.Foundations.PureStateMath.Inner w w = 0) : w = 0 := by
  let v : EuclideanSpace ℂ K := WithLp.toLp 2 w
  have hcomm : w ⬝ᵥ star w = 0 := by
    rw [dotProduct_comm]
    exact h
  have hi : @inner ℂ (EuclideanSpace ℂ K) _ v v = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact hcomm
  have hz : v = 0 := inner_self_eq_zero.mp hi
  ext x
  have he := congrArg (fun u : EuclideanSpace ℂ K => WithLp.ofLp u x) hz
  simpa only [v, WithLp.ofLp_toLp, Pi.zero_apply] using! he

/-- Both Szegedy isometry images of any state belong to the reachable span. -/
theorem devFrame_mem {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (v : QState I) :
    SzegedyIsometry P *ᵥ v ∈ devReachableSpan P ∧
      SzegedyIsometryB P *ᵥ v ∈ devReachableSpan P := by
  constructor
  · exact Submodule.subset_span (Or.inl ⟨v, rfl⟩)
  · exact Submodule.subset_span (Or.inr ⟨v, rfl⟩)

/-- For a transition matrix, the Szegedy walk preserves the reachable span. -/
theorem devWalk_preserves_span {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (hP : IsTransitionMatrix P) :
    ∀ ψ ∈ devReachableSpan P, SzegedyWalk P *ᵥ ψ ∈ devReachableSpan P := by
  have hA (ψ : QState (I × I)) (hψ : ψ ∈ devReachableSpan P) :
      ReflectionAbout (SzegedyIsometry P * (SzegedyIsometry P)ᴴ) *ᵥ ψ
        ∈ devReachableSpan P := by
    rw [reflectionAbout_mulVec, ← Matrix.mulVec_mulVec]
    exact (devReachableSpan P).sub_mem
      ((devReachableSpan P).smul_mem 2
        (devFrame_mem P ((SzegedyIsometry P)ᴴ *ᵥ ψ)).1) hψ
  have hB (ψ : QState (I × I)) (hψ : ψ ∈ devReachableSpan P) :
      ReflectionAbout (SzegedyIsometryB P * (SzegedyIsometryB P)ᴴ) *ᵥ ψ
        ∈ devReachableSpan P := by
    rw [reflectionAbout_mulVec, ← Matrix.mulVec_mulVec]
    exact (devReachableSpan P).sub_mem
      ((devReachableSpan P).smul_mem 2
        (devFrame_mem P ((SzegedyIsometryB P)ᴴ *ᵥ ψ)).2) hψ
  intro ψ hψ
  rw [szegedyWalk_eq_twoReflections P hP, ← Matrix.mulVec_mulVec]
  exact hB _ (hA _ hψ)

/-- For a transition matrix, the swap gate preserves the reachable span. -/
theorem devSwap_preserves_span {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (hP : IsTransitionMatrix P) :
    ∀ ψ ∈ devReachableSpan P, SwapGate *ᵥ ψ ∈ devReachableSpan P := by
  intro ψ hψ
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hψ
  · intro x hx
    rcases hx with (⟨v, rfl⟩ | ⟨v, rfl⟩)
    · change SwapGate *ᵥ (SzegedyIsometry P *ᵥ v) ∈ devReachableSpan P
      rw [Matrix.mulVec_mulVec]
      exact Submodule.subset_span (Or.inr ⟨v, rfl⟩)
    · change SwapGate *ᵥ (SzegedyIsometryB P *ᵥ v) ∈ devReachableSpan P
      have h1 : SzegedyIsometryB P *ᵥ v = SwapGate *ᵥ (SzegedyIsometry P *ᵥ v) := by
        rw [show SzegedyIsometryB P = SwapGate * SzegedyIsometry P from rfl]
        exact (Matrix.mulVec_mulVec v SwapGate (SzegedyIsometry P)).symm
      rw [h1]
      have hh := Matrix.mulVec_mulVec (SzegedyIsometry P *ᵥ v) SwapGate SwapGate
      rw [hh, swapGate_mul_self, Matrix.one_mulVec]
      exact Submodule.subset_span (Or.inl ⟨v, rfl⟩)
  · simp
  · intro x y _hx _hy hx hy
    rw [Matrix.mulVec_add]
    exact (devReachableSpan P).add_mem hx hy
  · intro c x _hx hx
    rw [Matrix.mulVec_smul]
    exact (devReachableSpan P).smul_mem c hx

/-- For two isometries with Hermitian cross Gram matrix, computes the product-of-reflections
action on both images of a cross Gram eigenvector. -/
theorem devTwoFrameEigenAction {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (A B : Matrix H I ℂ)
    (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) (hGram : (Aᴴ * B)ᴴ = Aᴴ * B)
    (v : I → ℂ) (z : ℂ) (hv : (Aᴴ * B) *ᵥ v = z • v) :
    (ReflectionAbout (B * Bᴴ) * ReflectionAbout (A * Aᴴ)) *ᵥ (A *ᵥ v) =
      (2 * z) • (B *ᵥ v) - A *ᵥ v ∧
    (ReflectionAbout (B * Bᴴ) * ReflectionAbout (A * Aᴴ)) *ᵥ (B *ᵥ v) =
      (-(2 * z)) • (A *ᵥ v) + (4 * z ^ 2 - 1) • (B *ᵥ v) := by
  have ha : Aᴴ *ᵥ (A *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  have hb : Bᴴ *ᵥ (B *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]
  have hab : Aᴴ *ᵥ (B *ᵥ v) = z • v := by
    rw [Matrix.mulVec_mulVec]
    exact hv
  have hba : Bᴴ *ᵥ (A *ᵥ v) = z • v := by
    rw [Matrix.mulVec_mulVec, show Bᴴ * A = Aᴴ * B by
      rw [← hGram, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]]
    exact hv
  have haa : ReflectionAbout (A * Aᴴ) *ᵥ (A *ᵥ v) = A *ᵥ v := by
    rw [reflectionAbout_mulVec, ← Matrix.mulVec_mulVec, ha]
    module
  have hbb : ReflectionAbout (B * Bᴴ) *ᵥ (B *ᵥ v) = B *ᵥ v := by
    rw [reflectionAbout_mulVec, ← Matrix.mulVec_mulVec, hb]
    module
  have hba' : ReflectionAbout (B * Bᴴ) *ᵥ (A *ᵥ v) = (2 * z) • (B *ᵥ v) - A *ᵥ v := by
    rw [reflectionAbout_mulVec, ← Matrix.mulVec_mulVec, hba, Matrix.mulVec_smul, smul_smul]
  have hab' : ReflectionAbout (A * Aᴴ) *ᵥ (B *ᵥ v) = (2 * z) • (A *ᵥ v) - B *ᵥ v := by
    rw [reflectionAbout_mulVec, ← Matrix.mulVec_mulVec, hab, Matrix.mulVec_smul, smul_smul]
  constructor
  · rw [← Matrix.mulVec_mulVec, haa, hba']
  · rw [← Matrix.mulVec_mulVec, hab', Matrix.mulVec_sub, Matrix.mulVec_smul, hba', hbb]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- A real discriminant eigenvector yields explicit Szegedy walk action formulas on its two
isometric lifts. -/
theorem devReachableTwoPlane {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (hP : IsTransitionMatrix P) :
    ∀ (u : I → ℝ) (lam : ℝ),
      SzegedyDiscriminant P *ᵥ u = lam • u →
        SzegedyWalk P *ᵥ (SzegedyIsometry P *ᵥ complexLift u) =
            ((2 * lam : ℝ) : ℂ) • (SzegedyIsometryB P *ᵥ complexLift u) -
              SzegedyIsometry P *ᵥ complexLift u ∧
        SzegedyWalk P *ᵥ (SzegedyIsometryB P *ᵥ complexLift u) =
          ((-(2 * lam) : ℝ) : ℂ) • (SzegedyIsometry P *ᵥ complexLift u) +
            ((4 * lam ^ 2 - 1 : ℝ) : ℂ) • (SzegedyIsometryB P *ᵥ complexLift u) := by
  intro u lam hu
  have he : ((SzegedyIsometry P)ᴴ * SzegedyIsometryB P) *ᵥ (complexLift u)
      = (lam : ℂ) • complexLift u := by
    rw [szegedy_gram_eq_discriminant P hP]
    ext i
    have hi := congrFun hu i
    simp only [Matrix.mulVec, dotProduct, complexLift, Matrix.map_apply,
      Pi.smul_apply, smul_eq_mul] at hi ⊢
    exact_mod_cast hi
  rw [szegedyWalk_eq_twoReflections P hP]
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_neg,
    Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_one] using!
    devTwoFrameEigenAction (SzegedyIsometry P) (SzegedyIsometryB P)
      (szegedyIsometry_conjTranspose_mul P hP) (szegedyIsometryB_conjTranspose_mul P hP)
      (szegedy_gram_hermitian P hP) (complexLift u) (lam : ℂ) he

/-- For a transition matrix, the reachable span is invariant under the walk and swap, with the
stated two-frame eigenvector action. -/
theorem dev_reachable_spectrum {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (hP : IsTransitionMatrix P) : CoreReachableSpectrum P :=
  ⟨devWalk_preserves_span P hP, devSwap_preserves_span P hP,
    devReachableTwoPlane P hP⟩

/-- A symmetric chain gap remains valid when its parameter is decreased. -/
theorem symmetricChainGap_mono {I : Type} [Fintype I] {P : I → I → ℝ} {δ δ' : ℝ}
    (h : SymmetricChainGap P δ) (h' : δ' ≤ δ) : SymmetricChainGap P δ' := by
  obtain ⟨hP, hsym, hray⟩ := h
  refine ⟨hP, hsym, ?_⟩
  intro v hv
  have hS : 0 ≤ (∑ i, (v i) ^ 2) := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hmul : (1 - δ) * (∑ i, (v i) ^ 2) ≤ (1 - δ') * (∑ i, (v i) ^ 2) := by
    have h1 : 1 - δ ≤ 1 - δ' := by linarith
    exact mul_le_mul_of_nonneg_right h1 hS
  have h2 := hray v hv
  linarith

/-- The regular kernel of a complete graph on at least two vertices admits a positive symmetric
chain gap parameter at most one. -/
theorem complete_graph_symmetric_chain_gap (n : ℕ) (hn : 2 ≤ n) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      SymmetricChainGap (regularKernel (completeGraph n) ((n : ℝ) - 1)) δ := by
  have hdpos : 0 < ((n : ℝ) - 1) := by
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hcard : 0 < (Fintype.card (Fin n) : ℝ) := by
    rw [Fintype.card_fin]
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hvol : volume (completeGraph n) ≠ 0 := by
    rw [completeGraph_volume n hn]
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : (1 : ℝ) ≤ ((n : ℝ) - 1) := by linarith
    nlinarith
  have hlazy : LazyChainGap (completeGraph n) ((n : ℝ) / (2 * ((n : ℝ) - 1))) :=
    complete_graph_lazyChainGap n hn
  have hle : (n : ℝ) / (2 * ((n : ℝ) - 1)) ≤ 1 := by
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : (1 : ℝ) ≤ ((n : ℝ) - 1) := by linarith
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * ((n : ℝ) - 1))]
    linarith
  have hgap : SymmetricChainGap (regularKernel (completeGraph n) ((n : ℝ) - 1))
      (2 * ((n : ℝ) / (2 * ((n : ℝ) - 1)))) :=
    symmetricChainGap_regularKernel (G := completeGraph n)
      (completeGraph_isDegreeRegular n hn) hdpos hcard hvol hle hlazy
  refine ⟨1, by norm_num, by norm_num, ?_⟩
  have h1 : 2 * ((n : ℝ) / (2 * ((n : ℝ) - 1))) = (n : ℝ) / ((n : ℝ) - 1) := by
    field_simp
  have hle' : 1 ≤ 2 * ((n : ℝ) / (2 * ((n : ℝ) - 1))) := by
    rw [h1]
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : (1 : ℝ) ≤ ((n : ℝ) - 1) := by linarith
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < ((n : ℝ) - 1))]
    linarith
  exact symmetricChainGap_mono hgap hle'

/-- Constructs a bipartite walk ledger with explicit setup, update, check, workspace, and
bit-time costs. -/
theorem bipartite_walk_ledger (a : ℕ) (ha : 0 < a) :
    ∃ L : WalkLedger,
      L.setupGates = (coherentRowWord a).length ∧
        L.setupQueries = 0 ∧
        L.updateGates = 4 ∧ L.updateQueries = 4 ∧
        L.checkGates = ((bipartiteCheckBlocks a ha).flatMap blockWord).length ∧
        L.checkQueries = 0 ∧
        L.spaceBits = a + a ∧
        L.bitTime = (a + 1) * (a + a + 1) + 4 * (a + a + 1) + 1 * (a + a + 1) := by
  obtain ⟨hsetup, hcheck, hq, hg⟩ :=
    bipartite_setup_update_check_ledger a ha 1
  refine ⟨{ setupGates := (coherentRowWord a).length, setupQueries := 0,
            updateGates := 4, updateQueries := 4,
            checkGates := ((bipartiteCheckBlocks a ha).flatMap blockWord).length,
            checkQueries := 0, spaceBits := a + a,
            bitTime := (coherentRowWord a).length * (a + a + 1) + 4 * (a + a + 1)
              + ((bipartiteCheckBlocks a ha).flatMap blockWord).length * (a + a + 1) }, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  rw [hsetup, hcheck]

/-- Measurement probability on a filtered finite universe equals the sum of Born probabilities
masked by the filtering predicate. -/
private lemma measureProb_filter {X : Type} [Fintype X] (ψ : QState X) (p : X → Prop)
    [DecidablePred p] :
    MeasureProb ψ ((Finset.univ : Finset X).filter p)
      = (Finset.univ : Finset X).sum (fun q => if p q then BornProb ψ q else 0) := by
  unfold MeasureProb
  rw [← Finset.sum_filter]

/-- A finite-set membership indicator splits into a sum of equality indicators. -/
private lemma indicator_split {X I : Type} [DecidableEq I] (g : X → I) (S : Finset I)
    (q : X) (f : ℝ) :
    (if g q ∈ S then f else 0) = ∑ x ∈ S, (if g q = x then f else 0) := by
  by_cases hq : g q ∈ S
  · rw [ite_eq_left hq]
    have h := Finset.sum_eq_single (s := S) (f := fun x => if g q = x then f else 0) (g q)
      (fun b _ hb => by
        show (if g q = b then f else 0) = 0
        by_cases hgb : g q = b
        · rw [ite_eq_left hgb]
          exact False.elim (absurd hgb.symm hb)
        · rw [ite_eq_right hgb])
      (fun h => absurd hq h)
    rw [h]
    simp
  · rw [ite_eq_right hq]
    refine (Finset.sum_eq_zero ?_).symm
    intro x hx
    have hne : ¬ (g q = x) := fun h => hq (by rw [h]; exact hx)
    simp [hne]

/-- Measurement probability for a finite set of output labels is the sum of the probabilities
for each individual label. -/
private lemma measureProb_split {X I : Type} [Fintype X] [DecidableEq I]
    (ψ : QState X) (g : X → I) (S : Finset I) :
    MeasureProb ψ ((Finset.univ : Finset X).filter (fun q => g q ∈ S))
      = ∑ x ∈ S, MeasureProb ψ ((Finset.univ : Finset X).filter (fun q => g q = x)) := by
  have hsplit : (Finset.univ : Finset X).sum (fun q => if g q ∈ S then BornProb ψ q else 0)
      = ∑ x ∈ S, (Finset.univ : Finset X).sum
          (fun q => if g q = x then BornProb ψ q else 0) := by
    calc
      (Finset.univ : Finset X).sum (fun q => if g q ∈ S then BornProb ψ q else 0)
          = (Finset.univ : Finset X).sum (fun q =>
              ∑ x ∈ S, (if g q = x then BornProb ψ q else 0)) := by
            apply Finset.sum_congr rfl
            intro q _
            exact indicator_split g S q (BornProb ψ q)
      _ = ∑ x ∈ S, (Finset.univ : Finset X).sum
              (fun q => if g q = x then BornProb ψ q else 0) := by
            exact Finset.sum_comm (f := fun q x => if g q = x then BornProb ψ q else 0)
  exact (measureProb_filter ψ (fun q => g q ∈ S)).trans
    (hsplit.trans
      (Finset.sum_congr rfl
        (fun x _ => (measureProb_filter ψ (fun q => g q = x)).symm)))

/-- The find-success filter on marked edges equals the filter on marked first endpoints. -/
private lemma find_success_filter {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (Mq k t : ℕ) :
    ((Finset.univ : Finset ((Fin (k * t) → Fin Mq) × (Bool × (I × I)))).filter
        (fun q => q.2.2 ∈ devEdgeMarkedSet S))
      = (Finset.univ : Finset ((Fin (k * t) → Fin Mq) × (Bool × (I × I)))).filter
        (fun q => q.2.2.1 ∈ S) := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, devEdgeMarkedSet]

/-- The find success mass decomposes into nonnegative per-element masses and vanishes for an
empty marked set. -/
theorem dev_find_endpoint {I : Type} [Fintype I] [DecidableEq I]
    (W : Matrix (I × I) (I × I) ℂ) (ψ : QState (I × I)) (S : Finset I)
    (Mq k t : ℕ) : CoreFindEndpoint W ψ S Mq k t := by
  refine ⟨?_, ?_, ?_⟩
  · unfold devFindSuccessMass devFindElementMass
    rw [find_success_filter S Mq k t]
    exact measureProb_split (phaseSearchState W ψ (devEdgeMarkedSet S) Mq k t)
      (fun q => q.2.2.1) S
  · intro x _
    unfold devFindElementMass MeasureProb
    have hq : ∀ q ∈ ((Finset.univ : Finset ((Fin (k * t) → Fin Mq) × (Bool × (I × I)))).filter
        (fun q => q.2.2.1 = x)),
        0 ≤ BornProb (phaseSearchState W ψ (devEdgeMarkedSet S) Mq k t) q := by
      intro q _
      show 0 ≤ (‖(phaseSearchState W ψ (devEdgeMarkedSet S) Mq k t) q‖ : ℝ) ^ 2
      exact sq_nonneg _
    exact Finset.sum_nonneg hq
  · intro hS
    subst hS
    unfold devFindSuccessMass MeasureProb devEdgeMarkedSet
    simp

/-- The Johnson kernel is symmetric. -/
theorem johnsonKernel_symm {X : Type} [Fintype X] [DecidableEq X] (k : ℕ)
    (s t : JohnsonVertex X k) : johnsonKernel X k s t = johnsonKernel X k t s := by
  unfold johnsonKernel
  congr 1
  rw [Finset.inter_comm]

/-- The Johnson kernel is nonnegative when the subset size is positive and at most half the
ground-set size. -/
theorem johnsonKernel_nonneg {X : Type} [Fintype X] [DecidableEq X] (k : ℕ)
    (hk : 0 < k) (h2k : 2 * k ≤ Fintype.card X)
    (s t : JohnsonVertex X k) : 0 ≤ johnsonKernel X k s t := by
  unfold johnsonKernel
  split
  · refine le_of_lt (inv_pos.mpr ?_)
    have hsub : 1 ≤ Fintype.card X - k := by omega
    have hpos : 0 < (k * (Fintype.card X - k) : ℕ) := by
      refine Nat.mul_pos (by omega) ?_
      omega
    exact_mod_cast hpos
  · exact le_rfl

/-- An input containing a collision has a nonempty collision-marked family at some positive
subset size. -/
theorem dev_collision_marked_nonempty (n : ℕ) (x : Fin n → ℕ)
    (h : ∃ a b : Fin n, a ≠ b ∧ x a = x b) :
    ∃ r : ℕ, 0 < r ∧ (devCollisionMarked n x r).Nonempty := by
  obtain ⟨a, b, hab, hx⟩ := h
  have hne : a.val ≠ b.val := fun e => hab (Fin.ext e)
  have htwo : 2 ≤ n := by
    by_contra hcon
    have hlt : n ≤ 1 := by omega
    have ha' : a.val < n := a.isLt
    have hb' : b.val < n := b.isLt
    have h1 : a.val = 0 := by omega
    have h2 : b.val = 0 := by omega
    exact hne (by omega)
  refine ⟨2, by norm_num, ?_⟩
  let s : Finset (Fin n) := {a, b}
  have hcard : s.card = 2 := by
    show ({a, b} : Finset (Fin n)).card = 2
    exact Finset.card_pair hab
  refine ⟨⟨s, hcard⟩, ?_⟩
  simp only [devCollisionMarked, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨a, b, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self b),
    hab, hx⟩

/-- Establishes Johnson kernel symmetry and nonnegativity in the specified range, together with
nonempty marked families for colliding inputs. -/
theorem dev_relation_carrier : CoreRelationCarrier := by
  refine ⟨?_, ?_⟩
  · intro X _ _ k hk h2k
    exact ⟨fun s t => johnsonKernel_symm k s t,
      fun s t => johnsonKernel_nonneg k hk h2k s t⟩
  · intro n x h
    obtain ⟨r, hr, hne⟩ := dev_collision_marked_nonempty n x h
    exact ⟨r, hr, hne⟩

/-- Two raised to `fairBitWidth` is at least the requested number of outcomes. -/
theorem fairBitWidth_spec (L : ℕ) : L ≤ 2 ^ fairBitWidth L := by
  exact Nat.find_spec (p := fun b => L ≤ 2 ^ b) ⟨L, nat_le_two_pow L⟩

/-- The fair bit width is no greater than any width whose binary range covers the requested
outcomes. -/
theorem fairBitWidth_min (L : ℕ) (m : ℕ) (h : L ≤ 2 ^ m) :
    fairBitWidth L ≤ m :=
  Nat.find_min' (p := fun b => L ≤ 2 ^ b) ⟨L, nat_le_two_pow L⟩ h

/-- The fair bit draw accepts a register whose encoded value is below the outcome count and
returns that value. -/
theorem fairBitDraw_accepts (L b : ℕ) (r : Reg b) (h : (bitVecEquiv b r).val < L) :
    fairBitDraw L b r = some ⟨(bitVecEquiv b r).val, h⟩ := by
  unfold fairBitDraw
  rw [dite_eq_left h]

/-- The fair bit draw rejects a register whose encoded value is not below the outcome count. -/
theorem fairBitDraw_reject (L b : ℕ) (r : Reg b) (h : ¬ (bitVecEquiv b r).val < L) :
    fairBitDraw L b r = none := by
  unfold fairBitDraw
  rw [dite_eq_right h]

/-- With sufficient width and a positive outcome count, each accepted outcome has exactly one
register preimage. -/
theorem fairBitDraw_fiber (L : ℕ) (hL : 0 < L) (b : ℕ) (hb : L ≤ 2 ^ b) (K : Fin L) :
    (∑ r : Reg b, if fairBitDraw L b r = some K then (1 : ℝ) else 0) = 1 := by
  classical
  have hkv : K.val < 2 ^ b := by omega
  let e : Reg b := (bitVecEquiv b).symm ⟨K.val, hkv⟩
  have hev : (bitVecEquiv b) e = ⟨K.val, hkv⟩ := by
    show (bitVecEquiv b) ((bitVecEquiv b).symm ⟨K.val, hkv⟩) = ⟨K.val, hkv⟩
    exact Equiv.apply_symm_apply _ _
  have hacc : fairBitDraw L b e = some K := by
    have hlt : (bitVecEquiv b e).val < L := by rw [hev]; exact K.isLt
    have hval : (bitVecEquiv b e).val = K.val := by rw [hev]
    rw [fairBitDraw_accepts L b e hlt]
    have hsub : (⟨(bitVecEquiv b e).val, hlt⟩ : Fin L) = K := Fin.ext hval
    rw [hsub]
  have hsingle : (∑ r : Reg b, if fairBitDraw L b r = some K then (1 : ℝ) else 0)
      = (if fairBitDraw L b e = some K then (1 : ℝ) else 0) := by
    refine Finset.sum_eq_single (s := (Finset.univ : Finset (Reg b)))
      (f := fun r => if fairBitDraw L b r = some K then (1 : ℝ) else 0) e ?_ ?_
    · intro r _ hne
      have hnd : fairBitDraw L b r ≠ some K := by
        intro hd
        by_cases hr : (bitVecEquiv b r).val < L
        · rw [fairBitDraw_accepts L b r hr] at hd
          have hd' : (⟨(bitVecEquiv b r).val, hr⟩ : Fin L) = K := by simpa using! hd
          have hv : (bitVecEquiv b r).val = K.val := congrArg Fin.val hd'
          have h2 : (bitVecEquiv b) r = ⟨K.val, hkv⟩ := Fin.ext hv
          have hr'' : r = (bitVecEquiv b).symm ((bitVecEquiv b) r) := by
            rw [Equiv.symm_apply_apply]
          have hr' : r = e := by
            show r = (bitVecEquiv b).symm ⟨K.val, hkv⟩
            rw [hr'', h2]
          exact hne hr'
        · rw [fairBitDraw_reject L b r hr] at hd
          simp at hd
      simp [hnd]
    · intro h
      exact False.elim (absurd (Finset.mem_univ e) h)
  rw [hsingle, hacc]
  simp

/-- Every positive finite outcome count admits an equal-fiber bit-register sampler accepting at
least half of all registers. -/
theorem dev_uniform_source : CoreUniformSource := by
  intro L hL
  have hb1 : L ≤ 2 ^ fairBitWidth L := fairBitWidth_spec L
  have hhalfN : 2 * L ≥ 2 ^ fairBitWidth L := by
    by_cases hb0 : fairBitWidth L = 0
    · have h1 : L ≤ 1 := by
        rw [hb0] at hb1
        simpa using! hb1
      rw [hb0]
      omega
    · have h2 : 2 ^ (fairBitWidth L - 1) < L := by
        by_contra hcon
        have hle : L ≤ 2 ^ (fairBitWidth L - 1) := le_of_not_gt hcon
        have := fairBitWidth_min L (fairBitWidth L - 1) hle
        omega
      have h3 : 2 ^ fairBitWidth L ≤ 2 ^ (fairBitWidth L - 1) * 2 := by
        rw [← Nat.pow_succ]
        have heq : fairBitWidth L = (fairBitWidth L - 1) + 1 := by omega
        rw [heq]
        exact Nat.le_refl _
      omega
  have hhalf : (2 ^ fairBitWidth L : ℝ) ≤ 2 * (L : ℝ) := by
    have hN : ((2 ^ fairBitWidth L : ℕ) : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hhalfN
    rwa [Nat.cast_pow] at hN
  refine ⟨fairBitWidth L, fairBitDraw L (fairBitWidth L), hb1, ?_, ?_⟩
  · intro K K'
    rw [fairBitDraw_fiber L hL (fairBitWidth L) hb1 K,
      fairBitDraw_fiber L hL (fairBitWidth L) hb1 K']
  · rw [Finset.sum_congr rfl
      (fun K _ => fairBitDraw_fiber L hL (fairBitWidth L) hb1 K)]
    norm_num
    exact hhalf

/-- For two isometries, both endpoint tau embeddings vanish on bipartite discriminant
eigenvectors with eigenvalue one. -/
theorem bipartite_tau_endpoint_vanishes_dev {H I J : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix H I ℂ) (B : Matrix H J ℂ) :
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry A → Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry B →
      ∀ u : QState (I ⊕ J),
        bipartiteDiscriminant A B *ᵥ u = ((1 : ℝ) : ℂ) • u →
          ∀ s : Bool, bipartiteTauLinear A B 1 s u = 0 := by
  intro hA hB u hu s
  let a : QState I := fun i => u (.inl i)
  let b : QState J := fun j => u (.inr j)
  have hd1 : (Aᴴ * B) *ᵥ b = a := by
    have hh := congrArg (fun v : QState (I ⊕ J) => fun i => v (.inl i)) hu
    simpa [bipartiteDiscriminant, Matrix.fromBlocks_mulVec] using! hh
  have hd2 : (Bᴴ * A) *ᵥ a = b := by
    have hh := congrArg (fun v : QState (I ⊕ J) => fun j => v (.inr j)) hu
    simpa [bipartiteDiscriminant, Matrix.fromBlocks_mulVec] using! hh
  have hcoeff : -(1 : ℂ) + (if s then Complex.I else -Complex.I) *
      (Real.sqrt (1 - (1 : ℝ) ^ 2) : ℂ) = -1 := by
    have h0 : (1 : ℝ) - 1 ^ 2 = 0 := by norm_num
    rw [h0, Real.sqrt_zero, Complex.ofReal_zero, mul_zero, add_zero]
  have htau : bipartiteTauLinear A B 1 s u = A *ᵥ a - B *ᵥ b := by
    change A *ᵥ a + (-(1 : ℂ) + (if s then Complex.I else -Complex.I) *
      (Real.sqrt (1 - (1 : ℝ) ^ 2) : ℂ)) • (B *ᵥ b) = _
    rw [hcoeff, neg_one_smul, sub_eq_add_neg]
  rw [htau]
  let w := A *ᵥ a - B *ᵥ b
  have hAw : Aᴴ *ᵥ w = 0 := by
    dsimp [w]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      show Aᴴ * A = 1 from hA, show (Aᴴ * B) *ᵥ b = a from hd1,
      Matrix.one_mulVec, sub_self]
  have hBw : Bᴴ *ᵥ w = 0 := by
    dsimp [w]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      show Bᴴ * B = 1 from hB, show (Bᴴ * A) *ᵥ a = b from hd2,
      Matrix.one_mulVec, sub_self]
  have hinner : Qatlib.Foundations.PureStateMath.Inner w w = 0 := by
    have hw : w = A *ᵥ a - B *ᵥ b := rfl
    have hsplit : Qatlib.Foundations.PureStateMath.Inner w w
        = Qatlib.Foundations.PureStateMath.Inner (A *ᵥ a) w - Qatlib.Foundations.PureStateMath.Inner (B *ᵥ b) w := by
      rw [hw, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_sub_left]
    rw [hsplit, inner_mulVec_left_rect, inner_mulVec_left_rect, hAw, hBw]
    simp [Qatlib.Foundations.PureStateMath.Inner, dotProduct_zero]
  exact local_inner_self_zero w hinner

/-- Establishes `clause5Spec`, combining reachable walk structure, a complete-graph gap,
effective bipartite neighbor access, and explicit resource accounting. -/
theorem clause5_endpoint : clause5Spec := by
  refine ⟨?_, ?_, ?_⟩
  · intro I _ _ _ P hP
    exact dev_reachable_spectrum P hP
  · intro n hn
    exact complete_graph_symmetric_chain_gap n hn
  · intro a ha
    refine ⟨bipartite_effectiveNeighborProgram a ha, ?_⟩
    exact bipartite_walk_ledger a ha

/-- Establishes `clause6Spec`, combining the find success decomposition with the Johnson
relation carrier. -/
theorem clause6_endpoint : clause6Spec := by
  refine ⟨?_, dev_relation_carrier⟩
  intro I _ _ W ψ S Mq k t
  exact dev_find_endpoint W ψ S Mq k t

/-- Establishes `clause7Spec`, combining a uniform finite-outcome source with vanishing endpoint
tau embeddings. -/
theorem clause7_endpoint : clause7Spec := by
  refine ⟨dev_uniform_source, ?_⟩
  intro H I J _ _ _ _ _ _ A B hA hB
  exact bipartite_tau_endpoint_vanishes_dev A B hA hB

end Qatlib.Concepts.QuantumGibbs.FormAlgebra
