/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.FixedGateCompilerDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedTactic false

noncomputable section

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.GuardedCounter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TinyTag

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib
open Qatlib

theorem one_le_pow_of_one_le {b : ℝ} (hb : 1 ≤ b) : ∀ n : ℕ, 1 ≤ b ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have hpos : 0 ≤ b ^ k := pow_nonneg (by linarith) _
      nlinarith [ih]

theorem one_le_pow_nat {b : ℕ} (hb : 1 ≤ b) : ∀ n : ℕ, 1 ≤ b ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have hmul : 1 * 1 ≤ b ^ k * b := Nat.mul_le_mul ih hb
      omega

theorem pow_le_pow_nat {x : ℕ} (hx : 1 ≤ x) : ∀ {m n : ℕ}, m ≤ n → x ^ m ≤ x ^ n := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
      rw [pow_succ]
      have hmul : x ^ k * 1 ≤ x ^ k * x := Nat.mul_le_mul_left (x ^ k) hx
      calc x ^ m ≤ x ^ k := ih
        _ ≤ x ^ k * x := by omega
        _ = x ^ (k + 1) := by rw [pow_succ]

theorem requestSize_pos {w : ℕ} (g : LocalQFTGate w) (k : ℕ) :
    1 ≤ requestSize w g k := by
  unfold requestSize
  omega

structure MiddleWindowSynthesizer where

  emit : (w : ℕ) → (a c : Fin w) → (e : ℕ) → (neg : Bool) → (k : ℕ) →
    List (LocalQFTGate (w + 1))

  legal : ∀ (w : ℕ) (a c : Fin w) (e k : ℕ) (neg : Bool) (h : LocalQFTGate (w + 1)),
    h ∈ emit w a c e neg k → IsFixedPrim h

  correct : ∀ (w : ℕ) (a c : Fin w) (e k : ℕ) (neg : Bool), 4 ≤ e → 1 ≤ k →
    approxUpToPhase (localProgramMatrix (emit w a c e neg k) * cleanEmbed w (w + 1))
      (cleanEmbed w (w + 1) * localGateMatrix (.cp a c e neg)) (tolerance k)

  clean : ∀ (w : ℕ) (a c : Fin w) (e k : ℕ) (neg : Bool), 4 ≤ e → 1 ≤ k →
    ancillaRestored w (localProgramMatrix (emit w a c e neg k) * cleanEmbed w (w + 1))
      (tolerance k)

  bounded : ∃ C D : ℕ, ∀ (w : ℕ) (a c : Fin w) (e k : ℕ) (neg : Bool), 4 ≤ e → 1 ≤ k →
    (emit w a c e neg k).length ≤ C * (requestSize w (.cp a c e neg) k) ^ D

def nextSegment (S : MiddleWindowSynthesizer) (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    SynthAnswer :=
  match g with
  | .h a => ⟨w, effectiveEmit w (.h a) k⟩
  | .swap a c => ⟨w, effectiveEmit w (.swap a c) k⟩
  | .cp a c e neg =>
      if 4 ≤ e then ⟨w + 1, S.emit w a c e neg k⟩ else ⟨w, effectiveEmit w (.cp a c e neg) k⟩

theorem nextSegment_cp_ge4 {w : ℕ} (S : MiddleWindowSynthesizer) (a c : Fin w) (e : ℕ)
    (neg : Bool) (k : ℕ) (he : 4 ≤ e) :
    nextSegment S w (.cp a c e neg) k = ⟨w + 1, S.emit w a c e neg k⟩ := by
  simp only [nextSegment]
  split
  · rfl
  · omega

theorem nextSegment_cp_lt4 {w : ℕ} (S : MiddleWindowSynthesizer) (a c : Fin w) (e : ℕ)
    (neg : Bool) (k : ℕ) (he : ¬ (4 ≤ e)) :
    nextSegment S w (.cp a c e neg) k = ⟨w, effectiveEmit w (.cp a c e neg) k⟩ := by
  simp only [nextSegment]
  split
  · omega
  · rfl

theorem nextSegment_width {w : ℕ} (S : MiddleWindowSynthesizer) (g : LocalQFTGate w) (k : ℕ) :
    ∃ a : ℕ, (nextSegment S w g k).width = w + a := by
  cases g with
  | h a => exact ⟨0, by simp [nextSegment, effectiveAnc]⟩
  | swap a c => exact ⟨0, by simp [nextSegment, effectiveAnc]⟩
  | cp a c e neg =>
      by_cases h4 : 4 ≤ e
      · refine ⟨1, ?_⟩
        rw [nextSegment_cp_ge4 S a c e neg k h4]
      · refine ⟨0, ?_⟩
        rw [nextSegment_cp_lt4 S a c e neg k h4]
        simp [effectiveAnc]

theorem nextSegment_zero_oracle {w : ℕ} (S : MiddleWindowSynthesizer) (g : LocalQFTGate w)
    (k : ℕ) : answerOracleCalls (nextSegment S w g k) = 0 := by
  cases g with
  | h a => simp [nextSegment, answerOracleCalls]
  | swap a c => simp [nextSegment, answerOracleCalls]
  | cp a c e neg =>
      by_cases h4 : 4 ≤ e
      · simp [nextSegment, h4, answerOracleCalls]
      · simp [nextSegment, h4, answerOracleCalls]

theorem nextSegment_legal {w : ℕ} (S : MiddleWindowSynthesizer) (g : LocalQFTGate w) (k : ℕ) :
    ∀ h ∈ (nextSegment S w g k).word, IsFixedPrim h := by
  cases g with
  | h a =>
      have hseg : nextSegment S w (.h a) k = ⟨w, [.h a]⟩ := by
        simp [nextSegment, effectiveEmit, effectiveAnc]
      rw [hseg]
      intro h hh
      have hh' : h = .h a := by simpa using hh
      subst hh'
      simp [IsFixedPrim]
  | swap a c =>
      have hseg : nextSegment S w (.swap a c) k = ⟨w, [.swap a c]⟩ := by
        simp [nextSegment, effectiveEmit, effectiveAnc]
      rw [hseg]
      intro h hh
      have hh' : h = .swap a c := by simpa using hh
      subst hh'
      simp [IsFixedPrim]
  | cp a c e neg =>
      by_cases h4 : 4 ≤ e
      · rw [nextSegment_cp_ge4 S a c e neg k h4]
        intro h hh
        exact S.legal w a c e k neg h hh
      · have he3 : e ≤ 3 := by omega
        rw [nextSegment_cp_lt4 S a c e neg k h4]
        have hlen : (effectiveEmit w (.cp a c e neg) k) = [.cp a c e neg] := by
          simp [effectiveEmit, effectiveAnc, he3]
        rw [hlen]
        intro h hh
        have hh' : h = .cp a c e neg := List.mem_singleton.mp hh
        subst hh'
        simp [IsFixedPrim, he3]

theorem nextSegment_accepts_primitive {w : ℕ} (S : MiddleWindowSynthesizer) (g : LocalQFTGate w)
    (k : ℕ) (hg : IsFixedPrim g) : Accepts w g k (nextSegment S w g k) := by
  cases g with
  | h a =>
      have hseg : nextSegment S w (.h a) k = ⟨w, [.h a]⟩ := by
        simp [nextSegment, effectiveEmit, effectiveAnc]
      rw [hseg]
      exact exactAccepts_of_isFixedPrim (.h a) k (by simp [IsFixedPrim])
  | swap a c =>
      have hseg : nextSegment S w (.swap a c) k = ⟨w, [.swap a c]⟩ := by
        simp [nextSegment, effectiveEmit, effectiveAnc]
      rw [hseg]
      exact exactAccepts_of_isFixedPrim (.swap a c) k (by simp [IsFixedPrim])
  | cp a c e neg =>
      have he3 : e ≤ 3 := hg
      have hnot4 : ¬ (4 ≤ e) := by omega
      rw [nextSegment_cp_lt4 S a c e neg k hnot4]
      have hlen : (effectiveEmit w (.cp a c e neg) k) = [.cp a c e neg] := by
        simp [effectiveEmit, effectiveAnc, he3]
      rw [hlen]
      exact exactAccepts_of_isFixedPrim (.cp a c e neg) k (by exact he3)

theorem nextSegment_accepts_middleWindow {w : ℕ} (S : MiddleWindowSynthesizer) (a c : Fin w)
    (e : ℕ) (neg : Bool) (k : ℕ) (hk : 1 ≤ k) (he : 4 ≤ e) :
    Accepts w (.cp a c e neg) k (nextSegment S w (.cp a c e neg) k) := by
  rw [nextSegment_cp_ge4 S a c e neg k he]
  show (∃ a : ℕ, w + 1 = w + a) ∧
    (∀ h ∈ (S.emit w a c e neg k : List (LocalQFTGate (w + 1))), IsFixedPrim h) ∧
    answerOracleCalls ⟨w + 1, S.emit w a c e neg k⟩ = 0 ∧
    approxUpToPhase (localProgramMatrix (S.emit w a c e neg k) * cleanEmbed w (w + 1))
      (cleanEmbed w (w + 1) * localGateMatrix (.cp a c e neg)) (tolerance k) ∧
    ancillaRestored w (localProgramMatrix (S.emit w a c e neg k) * cleanEmbed w (w + 1))
      (tolerance k)
  refine ⟨⟨1, by omega⟩, ?_, rfl, ?_, ?_⟩
  · intro h hh
    exact S.legal w a c e k neg h hh
  · exact S.correct w a c e k neg he hk
  · exact S.clean w a c e k neg he hk

theorem nextSegment_accepts_smallAngle {w : ℕ} (S : MiddleWindowSynthesizer) (a c : Fin w)
    (e : ℕ) (neg : Bool) (k : ℕ) (hk : 1 ≤ k) (he : k + 2 ≤ e) :
    Accepts w (.cp a c e neg) k (nextSegment S w (.cp a c e neg) k) := by
  by_cases h4 : 4 ≤ e
  · exact nextSegment_accepts_middleWindow S a c e neg k hk h4
  · have he3 : e ≤ 3 := by omega
    exact nextSegment_accepts_primitive S (.cp a c e neg) k (by exact he3)

theorem nextSegment_ledger (S : MiddleWindowSynthesizer) :
    ∃ C D : ℕ, ∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ), 1 ≤ k →
      (nextSegment S w g k).word.length ≤ C * (requestSize w g k) ^ D := by
  obtain ⟨C, D, hC⟩ := S.bounded
  refine ⟨C + 1, D + 1, ?_⟩
  intro w g k hk
  have hsize : 1 ≤ requestSize w g k := requestSize_pos g k
  have hpow : 1 ≤ (requestSize w g k) ^ (D + 1) := one_le_pow_nat hsize (D + 1)
  have hCD : 1 ≤ C + 1 := by omega
  have hprod : 1 ≤ (C + 1) * (requestSize w g k) ^ (D + 1) := by
    have := Nat.mul_le_mul hCD hpow
    omega
  cases g with
  | h a =>
      have hlen : (nextSegment S w (.h a) k).word.length ≤ 1 := by
        simp [nextSegment, effectiveEmit, effectiveAnc]
      calc (nextSegment S w (.h a) k).word.length ≤ 1 := hlen
        _ ≤ (C + 1) * (requestSize w (.h a) k) ^ (D + 1) := hprod
  | swap a c =>
      have hlen : (nextSegment S w (.swap a c) k).word.length ≤ 1 := by
        simp [nextSegment, effectiveEmit, effectiveAnc]
      calc (nextSegment S w (.swap a c) k).word.length ≤ 1 := hlen
        _ ≤ (C + 1) * (requestSize w (.swap a c) k) ^ (D + 1) := hprod
  | cp a c e neg =>
      by_cases h4 : 4 ≤ e
      · have hb := hC w a c e k neg h4 hk
        have hsize' : 1 ≤ requestSize w (.cp a c e neg) k := requestSize_pos _ k
        have hD : (requestSize w (.cp a c e neg) k) ^ D
            ≤ (requestSize w (.cp a c e neg) k) ^ (D + 1) :=
          pow_le_pow_nat hsize' (by omega)
        have h1 : C * (requestSize w (.cp a c e neg) k) ^ D
            ≤ C * (requestSize w (.cp a c e neg) k) ^ (D + 1) := by
          have := Nat.mul_le_mul (le_refl C) hD
          omega
        have h2 : C * (requestSize w (.cp a c e neg) k) ^ (D + 1)
            ≤ (C + 1) * (requestSize w (.cp a c e neg) k) ^ (D + 1) := by
          have hX : 0 ≤ (requestSize w (.cp a c e neg) k) ^ (D + 1) := Nat.zero_le _
          have heq : (C + 1) * (requestSize w (.cp a c e neg) k) ^ (D + 1)
              = C * (requestSize w (.cp a c e neg) k) ^ (D + 1)
                + (requestSize w (.cp a c e neg) k) ^ (D + 1) := by ring
          omega
        calc (nextSegment S w (.cp a c e neg) k).word.length
              = (S.emit w a c e neg k).length := by
                rw [nextSegment_cp_ge4 S a c e neg k h4]
          _ ≤ C * (requestSize w (.cp a c e neg) k) ^ D := hb
          _ ≤ C * (requestSize w (.cp a c e neg) k) ^ (D + 1) := h1
          _ ≤ (C + 1) * (requestSize w (.cp a c e neg) k) ^ (D + 1) := h2
      · have hlen : (nextSegment S w (.cp a c e neg) k).word.length ≤ 1 := by
          rw [nextSegment_cp_lt4 S a c e neg k h4]
          have he3 : e ≤ 3 := by omega
          simp [effectiveEmit, effectiveAnc, he3]
        calc (nextSegment S w (.cp a c e neg) k).word.length ≤ 1 := hlen
          _ ≤ (C + 1) * (requestSize w (.cp a c e neg) k) ^ (D + 1) := hprod

end Qatlib.Concepts.MatrixAccess.RitzPipeline
