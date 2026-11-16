/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.VariableTimeAmplificationDefs

@[expose] public section


/-! # Full old-program contract boundaries

These counterexamples retain the entire historical target types. They diagnose
missing normalization/nonempty-state premises and real/integer cost transport,
not the fixed paper's physical algorithms. Arbitrary known matrices are also
free in the old access-cost vocabulary, so source algorithms require an extra
uniform primitive/gate-cost bridge.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.ProgramAudit
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Foundations.PureStateMath

/-- A literal valid program record with a one-dimensional clock and empty word. -/
def blank (H : Type) : VtAmpProgram H := ⟨1, [], ∅⟩

/-- Every old word sends the unnormalized zero input to the actual zero output. -/
theorem zeroRun {H : Type} [Fintype H] [DecidableEq H] {r : ℕ} (hr : 0<r)
    (oracles : ℕ → Matrix H H ℂ) (C : Word H r) :
    run hr oracles C (0 : QState H)=0 := by
  have hc : clean r hr (0 : QState H)=0 := by ext p; simp [clean]
  rw [run,hc,Matrix.mulVec_zero]

/-- The real source interface charges no oracle time for any supplied known matrix. -/
theorem freeKnown {H : Type} {r : ℕ} (prices : ℕ → ℕ)
    (U : Matrix (Space H r) (Space H r) ℂ) : weightedCost prices [.known U]=0 := rfl

/-- Every actual unitary supplied as known data is a legal zero-query gate
with its full physical run equality in this historical cost vocabulary. -/
theorem knownRun {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (hr : 0 < r) (U : Matrix (Space H r) (Space H r) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Space H r) ℂ)
    (oracles : ℕ → Matrix H H ℂ) (ω : QState H) (prices : ℕ → ℕ) :
    legal 2 [.known U] ∧
      run hr oracles [.known U] ω = U *ᵥ clean r hr ω ∧
      weightedCost prices [.known U] = 0 := by
  refine ⟨?_, ?_, rfl⟩
  · intro s hs
    have he : s = Step.known U := by simpa using hs
    subst s
    exact hU
  · simp [run,wordMatrix]

/-- The entire universally quantified historical P0174 contract. -/
def OldEstimate : Prop :=
  ∀ {H : Type} [Fintype H] [DecidableEq H]
    (_A : VtAmpProgram H) (oracles : ℕ → Matrix H H ℂ) (ω : QState H)
    (c p : ℝ) (k : ℕ) (q : ℝ)
    (_hc0 : 0 < c) (_hc1 : c ≤ 1) (_hp : 0 < p) (_hk : 0 < k)
    (_hq : 0 ≤ q) (_hpromise : q = 0 ∨ p ≤ q),
    ∃ (prog : VtAmpProgram H) (hr : 0 < prog.r)
        (dec : Space H prog.r → ℝ) (good : Finset (Space H prog.r)) (K : ℝ),
      0 < K ∧
      (∀ s ∈ good, estimateAccurate c q (dec s)) ∧
      (1 - 1 / (2 : ℝ) ^ k ≤ MeasureProb (run hr oracles prog.word ω) good) ∧
      ((prog.accessTime (fun _ => 1) : ℝ) ≤ K * adaptiveEstimateBudget k p q)

/-- The entire universally quantified historical P0175 contract. -/
def OldAmplify : Prop :=
  ∀ {H : Type} [Fintype H] [DecidableEq H]
    (m : ℕ) (p t : Fin m → ℝ) (Tmax Tav psucc : ℝ) (prices : ℕ → ℕ)
    (_hstop : stopTimeData m p t Tmax Tav)
    (_hprice : ∀ j, 0 < prices j → (prices j : ℝ) ≤ Tmax)
    (_hp : 0 < psucc) (_hp1 : psucc ≤ 1),
    ∃ (P : VtAmpProgram H) (ψA ψgood : QState H) (pout K : ℝ),
      0 < K ∧
      (∃ good : Finset H, goodComponentData good ψA ψgood pout) ∧
      1 / 2 ≤ pout ∧
      ((P.accessTime prices : ℝ) ≤ K * tightAccessCost Tmax Tav psucc)

/-- The entire universally quantified historical P0176 contract. -/
def OldCascade : Prop :=
  ∀ {H : Type} [Fintype H] [DecidableEq H]
    (m : ℕ) (_hm : 1 ≤ m) (stageTime : ℕ → ℝ) (rounds : ℕ → ℕ)
    (_hrec : ∀ i, 1 ≤ i → i ≤ m →
      stageTime i = (2 * (rounds i : ℝ) + 1) *
        (stageTime (i - 1) + (2 : ℝ) ^ ((i : ℕ) - 1))),
    ∃ (P : VtAmpProgram H) (ψA ψgood : QState H) (pout : ℝ),
      (∃ good : Finset H, goodComponentData good ψA ψgood pout) ∧
      1 / 2 ≤ pout ∧
      ((P.accessTime (fun _ => 1) : ℝ) = stageTime m)

/-- The whole historical estimator fails on the allowed zero input, even on Unit. -/
theorem estimateFalse : ¬OldEstimate := by
  intro h
  obtain ⟨P, hr, _dec, good, _K, _hK, _ha, hp, _hc⟩ :=
    h (H := Unit) (blank Unit) (fun _ => 1) 0 1 1 1 0
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (Or.inl rfl)
  rw [zeroRun] at hp
  norm_num [MeasureProb,BornProb] at hp

/-- The whole historical amplification contract admits an empty output Hilbert space. -/
theorem amplifyFalse : ¬OldAmplify := by
  intro h
  have hs : stopTimeData 1 (fun _ => 1) (fun _ => 1) 1 1 := by
    norm_num [stopTimeData]
  obtain ⟨_P, a, _b, _p, _K, _hK, ⟨_good, hn, _⟩, _hp, _hc⟩ :=
    h (H := Empty) 1 (fun _ => 1) (fun _ => 1) 1 1 1 (fun _ => 0) hs
      (by intro j hj; simp at hj) (by norm_num) (by norm_num)
  simp [Normalized] at hn

/-- The whole old cascade accepts positive half-integral real stage costs,
although an actual word's unit-price access cost is a natural number. -/
theorem cascadeFalse : ¬OldCascade := by
  intro h
  let tm : ℕ → ℝ := fun i => if i=0 then 1/2 else 3/2
  have hr : ∀ (i : ℕ), 1 ≤ i → i ≤ 1 → tm i=(2*((0 : ℕ) : ℝ)+1)*
      (tm (i-1)+(2 : ℝ)^(i-1)) := by
    intro i hi hi1
    have he : i=1 := by omega
    subst i
    norm_num [tm]
  obtain ⟨P, _a, _b, _p, _hg, _hp, hc⟩ :=
    h (H := Unit) 1 (by norm_num) tm (fun _ => 0) hr
  have he : (P.accessTime (fun _ => 1) : ℝ)=3/2 := by simpa [tm] using hc
  have hn : P.accessTime (fun _ => 1)<2 := by exact_mod_cast (by linarith : (P.accessTime (fun _ => 1) : ℝ)<2)
  have hn1 : P.accessTime (fun _ => 1)≤1 := by omega
  have hr1 : (P.accessTime (fun _ => 1) : ℝ)≤1 := by exact_mod_cast hn1
  linarith

end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.ProgramAudit
