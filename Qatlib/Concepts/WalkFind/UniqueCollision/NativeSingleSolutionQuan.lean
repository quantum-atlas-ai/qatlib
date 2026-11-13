/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.NativeSingleSolutionStat
import Qatlib.Concepts.WalkFind.UniqueCollision.NativeJohnsonDataQuan
import Mathlib.Tactic.Ring
import Qatlib.Foundations.InstrumentCore.Measurement.Basic
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Mathlib.Tactic.Linarith

/-!
# Native collision search with a unique solution

This module proves the semantics and query count of the native repeated Johnson-walk search.
Loading preserves inner products, and a supported unit vector bounds the probability of
measuring a stored collision from below.

`nativeSingleSolution_answer` establishes the native unique-collision contract associated with
the search analysis in [Ambainis2007ElementDistinctness]. Under its size assumptions, one
iteration count works for every collision set of the prescribed size, with an explicit success
bound; inputs with no collision have zero marked measurement probability.

## Main statements

* `nativeAlgorithm2_queries`: the exact query count `r + 2*t*jwT2 k r`.
* `nativeUniformClock`: a single bounded iteration count with a uniform marked-amplitude bound.
* `nativeSingleSolution_answer`: correctness of the native unique-solution search.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.WalkFind.GroverInterp
open Qatlib.Concepts.WalkFind.WalkSpectrum

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.WalkFind.UniqueCollision

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkFind.UniqueCollision
open Matrix Qatlib.Concepts.WalkFind.UniqueCollision
open scoped Classical BigOperators

/-- Repeating a circuit that implements `K` on loaded states implements `K^n` on those states. -/
theorem nativeLoadedRepeat_semantics {N M r : ℕ} [NeZero M]
    (x : Fin N → ZMod M) (C : Circuit (LoadedSpace N M r))
    (K : Matrix (JRState N r) (JRState N r) ℂ)
    (hC : ∀ ψ, Run (alphabetOracle x) C (loadedState x ψ) = loadedState x (K *ᵥ ψ))
    (n : ℕ) (ψ : QState (JRState N r)) :
    Run (alphabetOracle x) (RepeatCircuit C n) (loadedState x ψ) =
      loadedState x (K^n *ᵥ ψ) := by
  induction n generalizing ψ with
  | zero => simp [RepeatCircuit]
  | succ n ih =>
    rw [RepeatCircuit, run_append, hC, ih, Matrix.mulVec_mulVec, ← pow_succ]

/-- The native search circuit prepares the loaded state obtained by `t` repetitions of the input
flip followed by `jwT2 k r` full walk steps. -/
theorem nativeAlgorithm2_semantics {N M r k : ℕ} [NeZero M]
    (A : NativeJohnsonWitness N M r k) (t : ℕ) (x : Fin N → ZMod M) :
    Run (alphabetOracle x) (nativeAlgorithm2 A t) (Qatlib.Foundations.PureStateMath.Ket A.init) =
      loadedState x (((jwWalkBig N r^jwT2 k r)*inputFlip k x)^t *ᵥ jwStartBig N r) := by
  have hblock (ψ : QState (JRState N r)) :
      Run (alphabetOracle x) (A.flip ++ RepeatCircuit A.walk (jwT2 k r)) (loadedState x ψ) =
        loadedState x (((jwWalkBig N r^jwT2 k r)*inputFlip k x) *ᵥ ψ) := by
    rw [run_append, A.flipSemantics,
      nativeLoadedRepeat_semantics x A.walk (jwWalkBig N r) (A.walkSemantics x),
      Matrix.mulVec_mulVec]
  rw [nativeAlgorithm2, run_append, A.setupSemantics]
  exact nativeLoadedRepeat_semantics x _ _ hblock t _

/-- The native search circuit uses exactly `r + 2*t*jwT2 k r` oracle queries. -/
theorem nativeAlgorithm2_queries {N M r k : ℕ} [NeZero M]
    (A : NativeJohnsonWitness N M r k) (t : ℕ) :
    QueryCount (nativeAlgorithm2 A t) = r+2*t*jwT2 k r := by
  simp only [nativeAlgorithm2, queryCount_append, queryCount_repeatCircuit,
    A.setupQueries, A.flipQueries, A.walkQueries]
  ring

/-- If the input has no collision of size `k`, every loaded state has zero measurement
probability on stored collision labels. -/
theorem loadedState_no_collision_measure {N M r k : ℕ} [NeZero M]
    (x : Fin N → ZMod M) (ψ : QState (JRState N r)) (hx : ¬HasCollision k x) :
    MeasureProb (loadedState x ψ) (Finset.univ.filter (storedCollision k)) = 0 := by
  unfold MeasureProb
  apply Finset.sum_eq_zero
  intro q hq
  have hstored := (Finset.mem_filter.mp hq).2
  have hn : ∀ p, q ≠ loadedBasis x p := by
    intro p hp
    subst q
    obtain ⟨S, _, hS⟩ := (storedCollision_at_basis x p).mp hstored
    exact hx ⟨S, hS⟩
  simp [BornProb, loadedState, hn]

/-- On an input without a collision of size `k`, the native search circuit has zero probability
of measuring a stored collision. -/
theorem nativeAlgorithm2_no_collision {N M r k : ℕ} [NeZero M]
    (A : NativeJohnsonWitness N M r k) (t : ℕ) (x : Fin N → ZMod M)
    (hx : ¬HasCollision k x) :
    MeasureProb (Run (alphabetOracle x) (nativeAlgorithm2 A t) (Qatlib.Foundations.PureStateMath.Ket A.init))
      (Finset.univ.filter (storedCollision k)) = 0 := by
  rw [nativeAlgorithm2_semantics]
  exact loadedState_no_collision_measure x _ hx

/-- Loading a fixed input preserves the inner product of any two Johnson states. -/
theorem loadedState_inner {N M r : ℕ} [NeZero M] (x : Fin N → ZMod M)
    (ψ φ : QState (JRState N r)) : Qatlib.Foundations.PureStateMath.Inner (loadedState x ψ) (loadedState x φ) = Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  let E : Matrix (LoadedSpace N M r) (JRState N r) ℂ :=
    fun q p => if q = loadedBasis x p then 1 else 0
  have he (v : QState (JRState N r)) : loadedState x v = E *ᵥ v := by
    ext q
    simp [loadedState, E, Matrix.mulVec, dotProduct]
  rw [he, he]
  simp only [Qatlib.Foundations.PureStateMath.Inner, Matrix.star_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [show Eᴴ*E = 1 from loadedBasis_isometry x, Matrix.vecMul_one]

/-- The squared overlap with a normalized vector supported on `S` is at most the measurement
probability of `S`. -/
private theorem unit_supported_overlap_le {H : Type} [Fintype H] [DecidableEq H]
    (good ψ : QState H) (S : Finset H) (hgood : Normalized good)
    (hsupport : ∀ i ∉ S, good i = 0) : ‖Qatlib.Foundations.PureStateMath.Inner good ψ‖^2 ≤ MeasureProb ψ S := by
  have hi : Qatlib.Foundations.PureStateMath.Inner good ψ = Qatlib.Foundations.PureStateMath.Inner good (Collapse ψ S) := by
    unfold Qatlib.Foundations.PureStateMath.Inner
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S
    · simp [collapse_apply, hi]
    · simp [collapse_apply, hi, hsupport i hi]
  have h :=
      norm_inner_le_norm (𝕜 := ℂ) (toEuclidean_fromVec good) (toEuclidean_fromVec (Collapse ψ S))
  rw [inner_euclidean_fromVec, (normalized_iff_norm_toEuclidean_fromVec good).mp hgood,
      one_mul] at h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [norm_toEuclidean_fromVec_sq, sum_normSq_collapse, ← hi] at hsq
  exact hsq

/-- Under the stated size conditions, one iteration count bounded by `8/(jwEpsArc k r*jwAlpha k
N r)` gives marked amplitude at least `jwEpsArc k r^3/1000` for every `k`-element collision
set. -/
theorem nativeUniformClock (k N r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r) (hr : 2*k ≤ r+1)
    (hsize : (8*Real.pi^2*(k^3)*(r+1)*(2^(k+4))*(k+1)*k : ℝ) ≤ N-r) :
    ∃ t : ℕ, (t : ℝ) ≤ 8/(jwEpsArc k r*jwAlpha k N r) ∧
      ∀ I : Finset (Fin N), I.card = k →
        jwEpsArc k r^3/1000 ≤ ‖jwMarkedAmplitude k N r t (jwT2 k r) I‖ := by
  have hkNr := jwWalk_size_physical k N r hk hsize
  obtain ⟨hε, hε1⟩ := jwEpsArc_bounds k r hk hkr
  obtain ⟨_, _, _, hα, hα1⟩ := alphaFromInput k N r hk hkr hkNr
  obtain ⟨hcount, hsn, hsreal, hoverlap, hsfix, hU, hUreal⟩ :=
    jwNormalizedSearch_inputs k N r (jwT2 k r) hk hkr hkNr
  obtain ⟨hflipU, hgn, hgreal, hflipgood, hflipfix⟩ := jwReducedFlip_search_inputs k
  let start := fun i => jwStart k N r i / (Real.sqrt (jwStartNormSq k N r) : ℂ)
  have hsqrt : (Real.sqrt (jwStartNormSq k N r) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hcount)
  have hphase : ∀ (ν : ℂ) (v : Fin (2*k+1) → ℂ),
      jwWalk k N r^jwT2 k r *ᵥ v = ν • v →
      (∑ i, star (v i)*start i) = 0 → v ≠ 0 →
      ∃ θ : ℝ, jwEpsArc k r ≤ θ ∧ θ ≤ 2*Real.pi-jwEpsArc k r ∧
        θ ≠ Real.pi ∧ ν = Complex.exp (Complex.I*θ) := by
    intro ν v he ho hv
    have ho' : (∑ i, star (v i)*jwStart k N r i) = 0 := by
      change (∑ i, star (v i)*(jwStart k N r i/(Real.sqrt (jwStartNormSq k N r) : ℂ))) = 0 at ho
      simp only [← mul_div_assoc, ← Finset.sum_div] at ho
      exact (div_eq_zero_iff.mp ho).resolve_right hsqrt
    exact jwWalk_powered_phase_gap k N r hk hkr hr hsize ν v he ho' hv
  obtain ⟨t, ht, hamp⟩ := groverInterpolation (2*k+1) (jwEpsArc k r) (jwAlpha k N r)
    hε hε1 hα hα1 (jwFlipTilde k) (jwWalk k N r^jwT2 k r) start (jwGoodTilde k)
    hflipU hU hUreal hsreal hgreal hsn hgn hoverlap hflipgood hflipfix hsfix hphase
  refine ⟨t, ht, ?_⟩
  intro I hI
  rw [jwMarkedAmplitude_eq_reduced k N r hkr hkNr I hI t (jwT2 k r)]
  exact hamp

/-- When `I` is the unique collision set of size `k`, the input collision flip equals the full
phase flip for subsets containing `I`. -/
private theorem nativeFlip_unique {N M r k : ℕ} [NeZero M] (x : Fin N → ZMod M)
    (I : Finset (Fin N)) (hI : IsCollision k x I) (hunique : ∀ J, IsCollision k x J → J = I) :
    inputFlip (r:=r) k x = jwFlipBig k N r I := by
  have hmark (p : JRState N r) : markedInput k x p ↔ I ⊆ p.val.1 := by
    constructor
    · rintro ⟨J, hJ, hc⟩; simpa [hunique J hc] using! hJ
    · intro h; exact ⟨I, h, hI⟩
  simp only [inputFlip, jwFlipBig, hmark]

/-- The loaded good vector for a collision set vanishes outside the labels satisfying
`storedCollision k`. -/
private theorem nativeGood_supported {N M r k : ℕ} [NeZero M] (x : Fin N → ZMod M)
    (I : Finset (Fin N)) (hI : IsCollision k x I) (q : LoadedSpace N M r)
    (hq : q ∉ Finset.univ.filter (storedCollision k)) :
    loadedState x (jwGoodVec k N r I) q = 0 := by
  by_cases hex : ∃ p, q = loadedBasis x p
  · obtain ⟨p, rfl⟩ := hex
    rw [loadedState_at_basis]
    have hnot : ¬ I ⊆ p.val.1 := by
      intro h
      exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (storedCollision_at_basis x p).mpr ⟨I,h,hI⟩⟩)
    simp [jwGoodVec, hnot]
  · have hn : ∀ p, q ≠ loadedBasis x p := fun p hp => hex ⟨p,hp⟩
    simp [loadedState, hn]

/-- The native Johnson-walk search satisfies `NativeSingleSolution`, including the
unique-collision success bound and zero acceptance on collision-free inputs
[Ambainis2007ElementDistinctness]. -/
theorem nativeSingleSolution_answer : NativeSingleSolution := by
  intro k N M r _ hM hk hkr hr hsize
  have hkNr := jwWalk_size_physical k N r hk hsize
  have hrN : r < N := by omega
  obtain ⟨A⟩ := nativeJohnsonData_answer N M r k hM hkr hrN
  obtain ⟨t, ht, hamp⟩ := nativeUniformClock k N r hk hkr hr hsize
  refine ⟨t, A, nativeAlgorithm2_queries A t, ht, ?_⟩
  intro x
  constructor
  · intro I hI huniq
    have hgood : Normalized (jwGoodVec k N r I) := by
      rw [jwGoodVec_eq_typeLast k N r I hI.1]
      exact jwPsiBigAt_normSq k N r hkr hkNr I hI.1 _
    have hlower := unit_supported_overlap_le (loadedState x (jwGoodVec k N r I))
      (loadedState x (jwRunState k N r t (jwT2 k r) I)) (Finset.univ.filter (storedCollision k))
      (loadedState_normalized x hgood) (nativeGood_supported x I hI)
    rw [loadedState_inner] at hlower
    have hrun : Run (alphabetOracle x) (nativeAlgorithm2 A t) (Qatlib.Foundations.PureStateMath.Ket A.init) =
        loadedState x (jwRunState k N r t (jwT2 k r) I) := by
      rw [nativeAlgorithm2_semantics, nativeFlip_unique x I hI huniq]
      rfl
    rw [hrun]
    have hε : 0 ≤ jwEpsArc k r^3/1000 := by
      exact div_nonneg (pow_nonneg (jwEpsArc_bounds k r hk hkr).1.le _) (by norm_num)
    have hsquare := pow_le_pow_left₀ hε (hamp I hI.1) 2
    have hbound : jwEpsArc k r^6/1000000 ≤ ‖Qatlib.Foundations.PureStateMath.Inner (jwGoodVec k N r I) (jwRunState k N r t (jwT2 k r) I)‖^2 := by
      change jwEpsArc k r^6/1000000 ≤ ‖jwMarkedAmplitude k N r t (jwT2 k r) I‖^2
      convert! hsquare using 1
      ring
    exact hbound.trans hlower
  · exact nativeAlgorithm2_no_collision A t x

end Qatlib.Concepts.WalkFind.UniqueCollision
