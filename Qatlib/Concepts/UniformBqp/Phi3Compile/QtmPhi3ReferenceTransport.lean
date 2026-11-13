/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.Phi3Compile.FiniteBasisPhi3PaddingQuan
import Qatlib.Foundations.StandardModel.WindowSim.GUnitExistenceQuan
import Qatlib.Foundations.StandardModel.WindowSim.OneRoundWindowSimulationQuan

/-!
# Transport of finite-window QTM simulations

This module proves that repeated local circuit rounds reproduce finite-window QTM evolution
under `windowEmbed`. Linearity and head-support bounds allow the one-round simulation to iterate
without reaching the boundary.

It also identifies known-wire embedding with basis padding and proves preservation of
normalization and amplitudes at encoded basis states.

For background, see [Yao1993].

## Main statements

* `qtmPhi3_reference_run`: repeated reference rounds simulate the window transition.
* `qtmKnownWireEmbed_normalized`: known-wire embedding preserves normalization.
* `qtmKnownWireEmbed_apply_image`: amplitudes are preserved on encoded basis states.

## References

* [Yao, 1993][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.WalkFind.SearchAlgorithm

namespace Qatlib.Concepts.UniformBqp.Phi3Compile
open Matrix
open scoped Classical BigOperators

/-- Matrix multiplication distributes over a finite sum of state vectors. -/
private theorem mulVec_sum {I : Type*} [Fintype I] {ι : Type*} [Fintype ι]
    (M : Matrix I I ℂ) (f : ι → QState I) :
    M *ᵥ (∑ i, f i) = ∑ i, M *ᵥ f i := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Circuit execution preserves addition of input states. -/
private theorem run_add {I : Type*} [Fintype I] (oracle : Matrix I I ℂ)
    (C : Circuit I) (ψ χ : QState I) :
    Run oracle C (ψ + χ) = Run oracle C ψ + Run oracle C χ := by
  induction C generalizing ψ χ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      simp only [run_gate, ApplyGate, Matrix.mulVec_add]
      exact ih _ _
    | query =>
      simp only [run_query, ApplyGate, Matrix.mulVec_add]
      exact ih _ _

/-- Circuit execution commutes with complex scalar multiplication. -/
private theorem run_smul {I : Type*} [Fintype I] (oracle : Matrix I I ℂ)
    (C : Circuit I) (a : ℂ) (ψ : QState I) :
    Run oracle C (a • ψ) = a • Run oracle C ψ := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      simp only [run_gate, ApplyGate, Matrix.mulVec_smul]
      exact ih _
    | query =>
      simp only [run_query, ApplyGate, Matrix.mulVec_smul]
      exact ih _

/-- Circuit execution distributes over a finite sum of input states. -/
private theorem run_sum {I : Type*} [Fintype I] (oracle : Matrix I I ℂ)
    (C : Circuit I) {ι : Type*} [Fintype ι] (f : ι → QState I) :
    Run oracle C (∑ i, f i) = ∑ i, Run oracle C (f i) := by
  induction C generalizing f with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      have h : U *ᵥ (∑ i, f i) = ∑ i, U *ᵥ f i := mulVec_sum U f
      simp only [run_gate, ApplyGate, h]
      exact ih _
    | query =>
      have h : oracle *ᵥ (∑ i, f i) = ∑ i, oracle *ᵥ f i := mulVec_sum oracle f
      simp only [run_query, ApplyGate, h]
      exact ih _

/-- Every finite state vector equals the sum of its amplitudes times the corresponding basis
kets. -/
private theorem ket_sum {I : Type*} [Fintype I] [DecidableEq I] (φ : QState I) :
    (∑ i, φ i • Qatlib.Foundations.PureStateMath.Ket i) = φ := by
  funext j
  have hsum : (∑ i, φ i • Qatlib.Foundations.PureStateMath.Ket i) j = ∑ i, φ i * Qatlib.Foundations.PureStateMath.Ket i j := by
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum, Finset.sum_eq_single j
    (fun b _ hb => by simp [ket_apply, Ne.symm hb, mul_zero])
    (fun hj => absurd (Finset.mem_univ j) hj)]
  simp

/-- The encoding of window configurations into cell registers is injective. -/
private theorem windowEncode_inj {t : ℕ} {Q A : Type*} :
    Function.Injective (windowEncode : WindowCfg t Q A → WReg t Q A) := by
  intro c c' h
  have hhead : c.head = c'.head := by
    by_cases hne : c.head = c'.head
    · exact hne
    · have hmarker := congrArg Prod.fst (congrFun h c.head)
      simp only [windowEncode] at hmarker
      simp [hne] at hmarker
  have hst : c.state = c'.state := by
    have hh := congrFun h c'.head
    simp only [windowEncode] at hh
    rw [hhead] at hh
    simp at hh
    exact hh.1
  have htp : c.tape = c'.tape := by
    funext j
    have hj := congrArg (fun p => p.2.2) (congrFun h j)
    simp only [windowEncode] at hj
    rw [← hhead] at hj
    split at hj <;> simp_all
  rcases c with ⟨hd, st, tp⟩
  rcases c' with ⟨hd', st', tp'⟩
  simp_all

/-- Evaluating an embedded window state at an encoded configuration recovers its original
amplitude. -/
private theorem windowEmbed_apply {t : ℕ} {Q A : Type*} (φ : QState (WindowCfg t Q A))
    (c : WindowCfg t Q A) : windowEmbed φ (windowEncode c) = φ c :=
  windowEncode_inj.extend_apply φ 0 c

/-- An embedded window state vanishes at a register outside the image of `windowEncode`. -/
private theorem windowEmbed_apply' {t : ℕ} {Q A : Type*} (φ : QState (WindowCfg t Q A))
    (z : WReg t Q A) (hz : ∀ c, windowEncode c ≠ z) : windowEmbed φ z = 0 :=
  Function.extend_apply' φ (0 : WReg t Q A → ℂ) z (fun ⟨c, he⟩ => hz c he)

/-- Embedding a configuration ket gives the ket of its encoded register. -/
private theorem windowEmbed_ket {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (c : WindowCfg t Q A) :
    windowEmbed (Qatlib.Foundations.PureStateMath.Ket c) = Qatlib.Foundations.PureStateMath.Ket (windowEncode c) := by
  funext z
  by_cases hz : ∃ c₀, windowEncode c₀ = z
  · obtain ⟨c₀, hzc⟩ := hz
    subst hzc
    rw [windowEmbed_apply]
    by_cases hc : c₀ = c
    · subst hc
      simp
    · simp [ket_apply, hc, windowEncode_inj.ne hc]
  · rw [windowEmbed_apply' _ _ (fun c₀ hc => hz ⟨c₀, hc⟩)]
    have hzne : z ≠ windowEncode c := fun h => hz ⟨c, h.symm⟩
    simp [ket_apply, hzne]

/-- An embedded window state is the sum of its configuration amplitudes times the encoded basis
kets. -/
private theorem windowEmbed_eq_sum {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (φ : QState (WindowCfg t Q A)) :
    windowEmbed φ = ∑ c, φ c • Qatlib.Foundations.PureStateMath.Ket (windowEncode c) := by
  have hsum : ∀ z : WReg t Q A,
      (∑ c, φ c • Qatlib.Foundations.PureStateMath.Ket (windowEncode c)) z = ∑ c, φ c * Qatlib.Foundations.PureStateMath.Ket (windowEncode c) z := by
    intro z
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  funext z
  by_cases hz : ∃ c₀, windowEncode c₀ = z
  · obtain ⟨c₀, hzc⟩ := hz
    subst hzc
    rw [windowEmbed_apply, hsum, Finset.sum_eq_single c₀
      (fun b _ hb => by
        simp [ket_apply, Ne.symm (windowEncode_inj.ne hb), mul_zero])
      (fun hj => absurd (Finset.mem_univ c₀) hj)]
    simp
  · rw [windowEmbed_apply' _ _ (fun c₀ hc => hz ⟨c₀, hc⟩), hsum, Finset.sum_eq_zero]
    intro c _
    have hzne : z ≠ windowEncode c := fun h => hz ⟨c, h.symm⟩
    simp [ket_apply, hzne]

/-- Window embedding distributes over finite sums of states. -/
private theorem windowEmbed_sum_gen {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] {ι : Type*} [Fintype ι]
    (F : ι → QState (WindowCfg t Q A)) :
    windowEmbed (∑ i, F i) = ∑ i, windowEmbed (F i) := by
  funext z
  by_cases hz : ∃ c₀, windowEncode c₀ = z
  · obtain ⟨c₀, hzc⟩ := hz
    subst hzc
    rw [windowEmbed_apply]
    simp [windowEmbed_apply]
  · rw [windowEmbed_apply' _ _ (fun c₀ hc => hz ⟨c₀, hc⟩), Finset.sum_apply,
      Finset.sum_eq_zero]
    intro i _
    rw [windowEmbed_apply' _ _ (fun c₀ hc => hz ⟨c₀, hc⟩)]

/-- Window embedding commutes with complex scalar multiplication. -/
private theorem windowEmbed_smul {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (a : ℂ)
    (φ : QState (WindowCfg t Q A)) :
    windowEmbed (a • φ) = a • windowEmbed φ := by
  funext z
  by_cases hz : ∃ c₀, windowEncode c₀ = z
  · obtain ⟨c₀, hzc⟩ := hz
    subst hzc
    simp only [windowEmbed_apply, Pi.smul_apply, smul_eq_mul]
  · rw [windowEmbed_apply' _ _ (fun c₀ hc => hz ⟨c₀, hc⟩)]
    simp only [Pi.smul_apply, smul_eq_mul,
      windowEmbed_apply' _ _ (fun c₀ hc => hz ⟨c₀, hc⟩), mul_zero]

/-- A successful cell move changes the head index by minus one, zero, or plus one according to
its direction. -/
private theorem moveCell_spec {t : ℕ} (d : QtmMove) (h h' : Fin (2 * t + 1))
    (hh : moveCell d h = some h') :
    (d = QtmMove.left → h'.val + 1 = h.val) ∧ (d = QtmMove.stay → h'.val = h.val) ∧
      (d = QtmMove.right → h'.val = h.val + 1) := by
  cases d with
  | left =>
    simp only [moveCell] at hh
    split at hh
    · exact absurd hh (by simp)
    · simp only [Option.some.injEq] at hh
      subst hh
      refine ⟨fun _ => by show h.val - 1 + 1 = h.val; omega,
        fun hc => QtmMove.noConfusion hc, fun hc => QtmMove.noConfusion hc⟩
  | stay =>
    simp only [moveCell, Option.some.injEq] at hh
    subst hh
    exact ⟨fun hc => QtmMove.noConfusion hc, fun _ => rfl,
      fun hc => QtmMove.noConfusion hc⟩
  | right =>
    simp only [moveCell] at hh
    split at hh
    · exact absurd hh (by simp)
    · simp only [Option.some.injEq] at hh
      subst hh
      exact ⟨fun hc => QtmMove.noConfusion hc, fun hc => QtmMove.noConfusion hc,
        fun _ => rfl⟩

/-- A nonzero amplitude after one window step comes from a supported configuration whose head
differs by at most one cell. -/
private theorem windowStep_support {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (M : LocalQTM Q A) (β : QState (WindowCfg t Q A))
    (c' : WindowCfg t Q A) (hβ : (windowStep M *ᵥ β) c' ≠ 0) :
    ∃ c : WindowCfg t Q A, β c ≠ 0 ∧
      c.head.val ≤ c'.head.val + 1 ∧ c'.head.val ≤ c.head.val + 1 := by
  have hsum : ∑ c : WindowCfg t Q A, windowStep M c' c * β c ≠ 0 := by
    simpa [Matrix.mulVec, dotProduct] using! hβ
  obtain ⟨c, _, hnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hne : windowStep M c' c ≠ 0 := fun h => hnz (by simp [h])
  have hb : c.head.val ≤ c'.head.val + 1 ∧ c'.head.val ≤ c.head.val + 1 := by
    simp only [windowStep, Matrix.of_apply] at hne
    obtain ⟨d, -, hd2⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨q', -, hq3⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd2
    obtain ⟨b, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq3
    by_cases hcond : moveCell d c.head = some c'.head ∧ c'.state = q' ∧
        ∀ j : Fin (2 * t + 1), c'.tape j = if j = c.head then b else c.tape j
    · rw [if_pos hcond] at hterm
      obtain ⟨hm, -, -⟩ := hcond
      rcases moveCell_spec d c.head c'.head hm with ⟨hl, hs, hr⟩
      cases d with
      | left =>
        have hlr := hl rfl
        omega
      | stay =>
        have hsr := hs rfl
        omega
      | right =>
        have hrr := hr rfl
        omega
    · rw [if_neg hcond] at hterm
      exact absurd hterm (by simp)
  exact ⟨c, fun h0 => hnz (by simp [h0]), hb.1, hb.2⟩

/-- A circuit round reproduces one window transition on an embedded state whose supported heads
lie strictly inside the window. -/
private theorem round_embed {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] {t : ℕ} (ht : 0 < t) (M : LocalQTM Q A)
    (G : Matrix (GWindow Q A) (GWindow Q A) ℂ)
    (hfix : GUnitFixesH M G) (hstep : GUnitSteps M G)
    (φ : QState (WindowCfg t Q A))
    (hgood : ∀ c, φ c ≠ 0 → 0 < c.head.val ∧ c.head.val < 2 * t) :
    Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) (kRoundCircuit t G) (windowEmbed φ)
      = windowEmbed (windowStep M *ᵥ φ) := by
  have key : ∀ c : WindowCfg t Q A,
      φ c • Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) (kRoundCircuit t G)
          (Qatlib.Foundations.PureStateMath.Ket (windowEncode c))
        = φ c • windowEmbed (windowStep M *ᵥ Qatlib.Foundations.PureStateMath.Ket c) := by
    intro c
    by_cases hc : φ c = 0
    · rw [hc, zero_smul, zero_smul]
    · rw [oneRoundWindowSimulation Q A M t ht G hfix hstep c
        (hgood c hc).1 (hgood c hc).2]
  calc Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) (kRoundCircuit t G) (windowEmbed φ)
      = Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) (kRoundCircuit t G)
          (∑ c, φ c • Qatlib.Foundations.PureStateMath.Ket (windowEncode c)) := by rw [windowEmbed_eq_sum]
    _ = ∑ c, Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) (kRoundCircuit t G)
          (φ c • Qatlib.Foundations.PureStateMath.Ket (windowEncode c)) := by rw [run_sum]
    _ = ∑ c, φ c • Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) (kRoundCircuit t G)
          (Qatlib.Foundations.PureStateMath.Ket (windowEncode c)) := by
          exact Finset.sum_congr rfl fun c _ => run_smul _ _ _ _
    _ = ∑ c, φ c • windowEmbed (windowStep M *ᵥ Qatlib.Foundations.PureStateMath.Ket c) :=
        Finset.sum_congr rfl fun c _ => key c
    _ = windowEmbed (∑ c, φ c • windowStep M *ᵥ Qatlib.Foundations.PureStateMath.Ket c) := by
          rw [windowEmbed_sum_gen]
          exact Finset.sum_congr rfl fun c _ => (windowEmbed_smul _ _).symm
    _ = windowEmbed (windowStep M *ᵥ ∑ c, φ c • Qatlib.Foundations.PureStateMath.Ket c) := by
          rw [mulVec_sum]
          exact congrArg _ (Finset.sum_congr rfl fun c _ =>
            (Matrix.mulVec_smul _ _ _).symm)
    _ = windowEmbed (windowStep M *ᵥ φ) := by rw [ket_sum]

/-- One window transition expands a head-support bound around the center by at most one cell. -/
private theorem good_step {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] {t : ℕ} (M : LocalQTM Q A) {r : ℕ}
    (φ : QState (WindowCfg t Q A))
    (hg : ∀ c, φ c ≠ 0 → t ≤ c.head.val + r ∧ c.head.val ≤ t + r) :
    ∀ c, (windowStep M *ᵥ φ) c ≠ 0 →
      t ≤ c.head.val + (r + 1) ∧ c.head.val ≤ t + (r + 1) := by
  intro c' hc'
  obtain ⟨c, hc0, hb1, hb2⟩ := windowStep_support M φ c' hc'
  obtain ⟨hA, hB⟩ := hg c hc0
  exact ⟨by omega, by omega⟩

/-- Repeated circuit rounds simulate the corresponding power of the window transition when the
initial head-support radius and number of rounds fit within the window. -/
private theorem sim_run {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] {t : ℕ} (ht : 0 < t) (M : LocalQTM Q A)
    (G : Matrix (GWindow Q A) (GWindow Q A) ℂ)
    (hfix : GUnitFixesH M G) (hstep : GUnitSteps M G) :
    ∀ (k : ℕ), k ≤ t → ∀ (r : ℕ), k + r ≤ t → ∀ φ : QState (WindowCfg t Q A),
      (∀ c, φ c ≠ 0 → t ≤ c.head.val + r ∧ c.head.val ≤ t + r) →
      Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ)
          (RepeatCircuit (kRoundCircuit t G) k) (windowEmbed φ)
        = windowEmbed (windowStep M ^ k *ᵥ φ) := by
  intro k
  induction k with
  | zero =>
    intro _ r _ φ _
    simp only [RepeatCircuit, run_nil, pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    intro hkle r hkr φ hg
    have hk : k ≤ t := Nat.le_trans (Nat.le_succ k) hkle
    have hgood : ∀ c, φ c ≠ 0 → 0 < c.head.val ∧ c.head.val < 2 * t := by
      intro c hc
      obtain ⟨hA, hB⟩ := hg c hc
      omega
    simp only [RepeatCircuit]
    rw [run_append, round_embed ht M G hfix hstep φ hgood,
      ih hk (r + 1) (by omega) (windowStep M *ᵥ φ) (good_step M φ hg),
      Matrix.mulVec_mulVec, pow_succ]

/-- Running `t` reference rounds on an encoded initial configuration equals the embedded state
obtained from `t` window transitions. -/
theorem qtmPhi3_reference_run (Q : Type) [Fintype Q] [DecidableEq Q]
    (A : Type) [Fintype A] [DecidableEq A] (M : LocalQTM Q A) (n t : ℕ) (ht : 0 < t)
    (G : Matrix (GWindow Q A) (GWindow Q A) ℂ)
    (hfix : GUnitFixesH M G) (hstep : GUnitSteps M G) (x : Fin n → A) :
    Run 1 (RepeatCircuit (kRoundCircuit t G) t) (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M n x))) =
      windowEmbed ((windowStep M)^t *ᵥ Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M n x)) := by
  have hgood0 : ∀ c, Qatlib.Foundations.PureStateMath.Ket (initWindowCfg (t := t) M n x) c ≠ 0 →
      t ≤ c.head.val + 0 ∧ c.head.val ≤ t + 0 := by
    intro c hc
    simp only [ket_apply] at hc
    by_cases hcc : c = initWindowCfg (t := t) M n x
    · subst hcc
      change t ≤ t+0 ∧ t ≤ t+0
      omega
    · rw [if_neg hcc] at hc
      exact absurd rfl hc
  have hrun := sim_run ht M G hfix hstep t (le_refl t) 0 (by omega)
    (Qatlib.Foundations.PureStateMath.Ket (initWindowCfg (t := t) M n x)) hgood0
  rw [windowEmbed_ket] at hrun
  exact hrun

/-- The amplitude of an embedded state at an encoded configuration equals its original
configuration amplitude. -/
theorem qtmPhi3_windowEmbed_image {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] {t : ℕ} (φ : QState (WindowCfg t Q A))
    (c : WindowCfg t Q A) : windowEmbed φ (windowEncode c) = φ c :=
  windowEmbed_apply φ c

/-- Known-wire embedding equals finite basis padding along `knownWireExtend`. -/
theorem qtmKnownWireEmbed_eq_pad {a b : ℕ} (e : Fin a ↪ Fin b) (ψ : QState (Reg a)) :
    knownWireEmbed e ψ = finiteBasisPadState (knownWireExtend e) ψ := by
  rw [state_ket_expansion ψ]
  simp only [knownWireEmbed_sum, knownWireEmbed_smul, knownWireEmbed_ket,
    finiteBasisPadState_sum, finiteBasisPadState_smul, finiteBasisPadState_ket]

/-- Extending a register along an injective wire map gives an injective map on basis registers. -/
theorem qtmKnownWireExtend_injective {a b : ℕ} (e : Fin a ↪ Fin b) :
    Function.Injective (knownWireExtend e) := by
  intro x y h
  funext i
  have hi := congrFun h (e i)
  simpa only [knownWireExtend_at] using! hi

/-- Known-wire embedding preserves normalization of a state. -/
theorem qtmKnownWireEmbed_normalized {a b : ℕ} (e : Fin a ↪ Fin b)
    {ψ : QState (Reg a)} (hψ : Normalized ψ) : Normalized (knownWireEmbed e ψ) := by
  rw [qtmKnownWireEmbed_eq_pad]
  exact finiteBasisPadState_normalized (knownWireExtend e) (qtmKnownWireExtend_injective e) hψ

/-- The amplitude at an extended basis register equals the amplitude at the original register. -/
theorem qtmKnownWireEmbed_apply_image {a b : ℕ} (e : Fin a ↪ Fin b)
    (ψ : QState (Reg a)) (x : Reg a) : knownWireEmbed e ψ (knownWireExtend e x) = ψ x := by
  rw [qtmKnownWireEmbed_eq_pad]
  exact finiteBasisPadState_apply_image (knownWireExtend e) (qtmKnownWireExtend_injective e) ψ x

end Qatlib.Concepts.UniformBqp.Phi3Compile
