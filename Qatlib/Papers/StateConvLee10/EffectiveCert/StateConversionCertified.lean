/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StateConvLee10.EffectiveCert.StateConversionCertifiedDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.NumericalWord.MixedWordError
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.ConversionCore.WitnessCompile.RationalRectFactorization
open Qatlib.Concepts.ConversionCore.WitnessCompile.StateConversionEffective
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

set_option autoImplicit false

namespace Qatlib.Papers.StateConvLee10.EffectiveCert

open Qatlib
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

theorem abs_rat_cast (q : ℚ) : ((|q| : ℚ) : ℝ) = |(q : ℝ)| := by
  by_cases h : 0 ≤ q
  · have h' : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h
    rw [abs_of_nonneg h, abs_of_nonneg h']
  · have h' : (q : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge h)
    rw [abs_of_nonpos (le_of_not_ge h), abs_of_nonpos h']
    norm_cast

theorem maxAbsRat_ge {X : Type} [Fintype X] [DecidableEq X] (a : X → ℚ) (r : X) :
    |a r| ≤ maxAbsRat a := by
  unfold maxAbsRat
  rw [Finset.le_fold_max]
  exact Or.inr ⟨r, Finset.mem_univ r, le_rfl⟩

theorem max_rat_cast (u v : ℚ) : ((max u v : ℚ) : ℝ) = max (u : ℝ) (v : ℝ) := by
  by_cases h : u ≤ v
  · rw [max_eq_right h, max_eq_right (by exact_mod_cast h)]
  · have h' : v ≤ u := le_of_not_ge h
    rw [max_eq_left h', max_eq_left (by exact_mod_cast h')]

theorem maxAbsRat_cast {X : Type} [Fintype X] [DecidableEq X] (a : X → ℚ) :
    ((maxAbsRat a : ℚ) : ℝ)
      = Finset.fold max 0 (fun r => ((|a r| : ℚ) : ℝ)) (Finset.univ : Finset X) := by
  classical
  unfold maxAbsRat
  induction (Finset.univ : Finset X) using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      rw [Finset.fold_insert hx, Finset.fold_insert hx, max_rat_cast, ih]

theorem maxAbsRat_le_scale {X : Type} [Fintype X] [DecidableEq X] (a : X → ℚ) :
    maxAbsRat a ≤ diagonalScaleReal a := by
  have hnonneg : (0 : ℝ) ≤ diagonalScaleReal a := norm_nonneg _
  rw [maxAbsRat_cast]
  rw [Finset.fold_max_le]
  refine ⟨hnonneg, ?_⟩
  intro x _
  have hcast : ((|a x| : ℚ) : ℝ) = |(a x : ℝ)| := abs_rat_cast _
  rw [hcast]
  exact abs_entry_le_diagonalScaleReal a x

theorem newtonScale_pos {M : ℚ} (hM : 0 ≤ M) : ∀ n, 0 < newtonScale M n := by
  intro n
  induction n with
  | zero =>
      simp only [newtonScale]
      linarith
  | succ n ih =>
      simp only [newtonScale]
      have h1 : 0 ≤ M / newtonScale M n := div_nonneg hM (le_of_lt ih)
      have h2 : 0 < newtonScale M n + M / newtonScale M n := add_pos_of_pos_of_nonneg ih h1
      exact div_pos h2 (by norm_num)

theorem newtonScale_identity {M : ℚ} {n : ℕ} (hpos : 0 < newtonScale M n) :
    ((newtonScale M n + M / newtonScale M n) / 2) ^ 2 - M
      = ((newtonScale M n - M / newtonScale M n) ^ 2) / 4 := by
  have hne : (newtonScale M n : ℚ) ≠ 0 := ne_of_gt hpos
  field_simp
  ring

theorem newtonScale_sq_ge {M : ℚ} (hM : 0 ≤ M) : ∀ n, M ≤ (newtonScale M n) ^ 2 := by
  intro n
  induction n with
  | zero =>
      simp only [newtonScale]
      have hsq : 0 ≤ (M + 1) * (M + 1) := mul_self_nonneg _
      nlinarith
  | succ n ih =>
      simp only [newtonScale]
      have hpos : 0 < newtonScale M n := newtonScale_pos hM n
      have hid := newtonScale_identity hpos
      have hnonneg : 0 ≤ ((newtonScale M n - M / newtonScale M n) ^ 2) / 4 := by positivity
      linarith

theorem newtonScale_sq_le {M : ℚ} (hM : 0 ≤ M) :
    ∀ n, (newtonScale M (n + 1)) ^ 2 ≤ (newtonScale M n) ^ 2 := by
  intro n
  have hpos : 0 < newtonScale M n := newtonScale_pos hM n
  have hge : M ≤ (newtonScale M n) ^ 2 := newtonScale_sq_ge hM n
  have hdiv : M / newtonScale M n ≤ newtonScale M n := by
    rw [div_le_iff₀ hpos]
    nlinarith
  have hhalf : (newtonScale M n + M / newtonScale M n) / 2 ≤ newtonScale M n := by
    linarith
  have hnonneg : 0 ≤ (newtonScale M n + M / newtonScale M n) / 2 := by
    positivity
  have hprod : 0 ≤ (newtonScale M n - (newtonScale M n + M / newtonScale M n) / 2) *
      (newtonScale M n + (newtonScale M n + M / newtonScale M n) / 2) :=
    mul_nonneg (sub_nonneg.mpr hhalf) (by linarith)
  simp only [newtonScale]
  nlinarith [hprod]

theorem newtonScale_err_nonneg {M : ℚ} (hM : 0 ≤ M) (n : ℕ) :
    0 ≤ (newtonScale M n) ^ 2 - M := by
  have h := newtonScale_sq_ge hM n
  linarith

theorem newtonScale_err_step {M : ℚ} (hM : 0 ≤ M) (n : ℕ) :
    (newtonScale M (n + 1)) ^ 2 - M ≤ ((newtonScale M n) ^ 2 - M) / 4 := by
  have hpos : 0 < newtonScale M n := newtonScale_pos hM n
  have herr : 0 ≤ (newtonScale M n) ^ 2 - M := newtonScale_err_nonneg hM n
  have hle : (newtonScale M n) ^ 2 - M ≤ (newtonScale M n) ^ 2 := by
    linarith
  simp only [newtonScale]
  rw [newtonScale_identity hpos]
  have hne : (newtonScale M n : ℚ) ≠ 0 := ne_of_gt hpos
  have hsq : ((newtonScale M n - M / newtonScale M n) ^ 2) / 4
      = ((newtonScale M n) ^ 2 - M) ^ 2 / (4 * (newtonScale M n) ^ 2) := by
    field_simp
  rw [hsq]
  have hmul : ((newtonScale M n) ^ 2 - M) ^ 2
      ≤ ((newtonScale M n) ^ 2 - M) * ((newtonScale M n) ^ 2) := by
    calc ((newtonScale M n) ^ 2 - M) ^ 2 = ((newtonScale M n) ^ 2 - M) * ((newtonScale M n) ^ 2 - M) := by ring
      _ ≤ ((newtonScale M n) ^ 2) * ((newtonScale M n) ^ 2 - M) :=
        mul_le_mul_of_nonneg_right hle herr
      _ = ((newtonScale M n) ^ 2 - M) * ((newtonScale M n) ^ 2) := by ring
  have hden : 0 < 4 * (newtonScale M n) ^ 2 := by positivity
  rw [div_le_div_iff₀ hden (by positivity)]
  nlinarith [hmul]

theorem newtonScale_err_le {M : ℚ} (hM : 0 ≤ M) :
    ∀ n, ((newtonScale M n) ^ 2 - M) * 4 ^ n ≤ (M + 1) ^ 2 - M := by
  intro n
  induction n with
  | zero =>
      simp only [newtonScale]
      have h4 : (4 : ℚ) ^ 0 = 1 := by norm_num
      rw [h4]
      simp
  | succ n ih =>
      have hstep := newtonScale_err_step hM n
      have h4 : (4 : ℚ) ^ (n + 1) = 4 ^ n * 4 := by rw [pow_succ]
      have hmul : ((newtonScale M (n + 1)) ^ 2 - M) * 4 ≤ (newtonScale M n) ^ 2 - M := by
        have h1 := (le_div_iff₀ (by norm_num : (0 : ℚ) < 4)).mp hstep
        linarith
      calc ((newtonScale M (n + 1)) ^ 2 - M) * 4 ^ (n + 1)
          = ((newtonScale M (n + 1)) ^ 2 - M) * (4 ^ n * 4) := by rw [h4]
        _ = (((newtonScale M (n + 1)) ^ 2 - M) * 4) * 4 ^ n := by ring
        _ ≤ ((newtonScale M n) ^ 2 - M) * 4 ^ n := by
            exact mul_le_mul_of_nonneg_right hmul (by positivity)
        _ ≤ (M + 1) ^ 2 - M := ih

theorem scaleSearch_sound {M δ : ℚ} (hM : 0 ≤ M) {fuel : ℕ} {t : ℚ}
    (h : scaleSearch M δ fuel = some t) :
    ∃ n : ℕ, t = newtonScale M n ∧ M ≤ t ^ 2 ∧ t ^ 2 - M ≤ δ ∧ 0 < t := by
  induction fuel with
  | zero =>
      simp [scaleSearch] at h
  | succ n ih =>
      simp only [scaleSearch] at h
      by_cases hc : newtonScale M n ^ 2 - M ≤ δ
      · simp only [if_pos hc] at h
        have ht : newtonScale M n = t := Option.some.inj h
        subst ht
        exact ⟨n, rfl, newtonScale_sq_ge hM n, hc, newtonScale_pos hM n⟩
      · simp only [if_neg hc] at h
        exact ih h

theorem nat_lt_four_pow (m : ℕ) : m < 4 ^ m := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have h1 : m + 1 ≤ 4 ^ m + 1 := by omega
      have h2 : 4 ^ m + 1 ≤ 4 * 4 ^ m := by
        have h3 : (0 : ℕ) ≤ 3 * 4 ^ m := by positivity
        nlinarith
      calc m + 1 ≤ 4 ^ m + 1 := h1
        _ < 4 * 4 ^ m := by linarith
        _ = 4 ^ (m + 1) := by rw [pow_succ]; ring

theorem scaleSearch_exists {M δ : ℚ} (hM : 0 ≤ M) (hδ : 0 < δ) :
    ∃ fuel t, scaleSearch M δ fuel = some t := by
  have he0 : 0 ≤ ((M + 1) ^ 2 - M : ℚ) := by nlinarith [hM]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((M + 1) ^ 2 - M : ℝ) ≤ (δ : ℝ) * 4 ^ n := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ((M + 1) ^ 2 - M : ℝ) / (δ : ℝ) < m :=
      exists_nat_gt _
    refine ⟨m, ?_⟩
    have h4 : (m : ℝ) < (4 ^ m : ℝ) := by exact_mod_cast (nat_lt_four_pow m)
    have hlt : ((M + 1) ^ 2 - M : ℝ) / (δ : ℝ) < (4 ^ m : ℝ) :=
      lt_of_lt_of_le hm (le_of_lt h4)
    have hpos : (0 : ℝ) < δ := by exact_mod_cast hδ
    have := (div_lt_iff₀ hpos).mp hlt
    linarith
  have hq : ((M + 1) ^ 2 - M : ℚ) ≤ δ * 4 ^ n := by exact_mod_cast hn
  have h4pos : (0 : ℚ) < 4 ^ n := by positivity
  have hmul := newtonScale_err_le hM n
  have herr : (newtonScale M n) ^ 2 - M ≤ ((M + 1) ^ 2 - M) / 4 ^ n := by
    rw [le_div_iff₀ h4pos]
    linarith
  have hquot : ((M + 1) ^ 2 - M) / 4 ^ n ≤ δ := by
    rw [div_le_iff₀ h4pos]
    linarith [hq]
  refine ⟨n + 1, newtonScale M n, ?_⟩
  simp only [scaleSearch]
  rw [if_pos (by linarith [herr, hquot])]

theorem sourceAccessWires_nodup (d : SourceRationalProblem) (w : ℕ)
    (hw : sourceAddressBits d + sourceValueBits d ≤ w) :
    (sourceAccessWires d w hw).Nodup := by
  unfold sourceAccessWires
  refine List.Nodup.map_on ?_ (List.nodup_finRange _)
  intro a ha b hb heq
  exact Fin.ext (congrArg (fun x : Fin w => x.val) heq)

theorem sourceAccessWires_length (d : SourceRationalProblem) (w : ℕ)
    (hw : sourceAddressBits d + sourceValueBits d ≤ w) :
    (sourceAccessWires d w hw).length = sourceAddressBits d + sourceValueBits d := by
  simp [sourceAccessWires]

theorem emittedWord_engine {w : ℕ} (g : LocalQFTGate w) (k : ℕ) :
    emittedWord w g k = (partialCompiler.emit w g k : List (LocalQFTGate w)) := by
  cases g <;> rfl

theorem emit_fixed {w : ℕ} (g : LocalQFTGate w) (k : ℕ) :
    ∀ h ∈ emittedWord w g k, sourceFixedGate h := by
  cases g with
  | h a =>
      intro h hmem
      simp only [emittedWord, List.mem_singleton] at hmem
      subst hmem
      simp [sourceFixedGate]
  | swap a c =>
      intro h hmem
      simp only [emittedWord, List.mem_singleton] at hmem
      subst hmem
      simp [sourceFixedGate]
  | cp a c e neg =>
      by_cases he : e ≤ 3
      · intro h hmem
        simp only [emittedWord] at hmem
        rw [if_pos he] at hmem
        simp only [List.mem_singleton] at hmem
        subst hmem
        simp only [sourceFixedGate]
        exact he
      · intro h hmem
        simp only [emittedWord] at hmem
        rw [if_neg he] at hmem
        simp at hmem

theorem sourceFixedGate_lift {w w' : ℕ} (hw : w ≤ w') {g : LocalQFTGate w}
    (hg : sourceFixedGate g) : sourceFixedGate (liftGateTo hw g) := by
  cases g with
  | h a =>
      simp [sourceFixedGate, liftGateTo]
  | swap a c =>
      simp [sourceFixedGate, liftGateTo]
  | cp a c k neg =>
      simp [sourceFixedGate, liftGateTo] at hg ⊢
      exact hg

theorem emit_lift_fixed {w w' : ℕ} (hw : w ≤ w') (g : LocalQFTGate w) (k : ℕ) :
    ∀ h ∈ liftWordTo hw (emittedWord w g k), sourceFixedGate h := by
  intro h hh
  obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hh
  exact sourceFixedGate_lift hw (emit_fixed g k h' hh')

theorem sourceFrameSynthesisProgram_legal (d : SourceRationalProblem) (w : ℕ)
    (g : LocalQFTGate w) (k : ℕ) (hw : w ≤ nativeFrameWidth d + k) :
    sourceNativeLegal d (sourceFrameSynthesisProgram d w g k hw) := by
  intro s hs
  have hs' : s = SourceNativeStep.query
        (sourceAccessWires d (nativeFrameWidth d + k) (by unfold nativeFrameWidth; omega)) false
      ∨ ∃ h, h ∈ liftWordTo hw (emittedWord w g k) ∧ SourceNativeStep.local h = s := by
    have hmem : s ∈ (SourceNativeStep.query
          (sourceAccessWires d (nativeFrameWidth d + k) (by unfold nativeFrameWidth; omega)) false ::
          (liftWordTo hw (emittedWord w g k)).map (fun h => SourceNativeStep.local h)) := by
      exact hs
    rcases List.mem_cons.mp hmem with hq | hl
    · exact Or.inl hq
    · exact Or.inr (List.mem_map.mp hl)
  rcases hs' with hq | ⟨h, hh, rfl⟩
  · subst hq
    exact ⟨sourceAccessWires_nodup d _ _, sourceAccessWires_length d _ _⟩
  · exact emit_lift_fixed hw g k h hh

theorem sourceFrameSynthesisProgram_calls (d : SourceRationalProblem) (w : ℕ)
    (g : LocalQFTGate w) (k : ℕ) (hw : w ≤ nativeFrameWidth d + k) :
    sourceNativeCalls (sourceFrameSynthesisProgram d w g k hw) = 1 := by
  simp [sourceFrameSynthesisProgram, sourceNativeCalls]

theorem sourceFrameSynthesisProgram_gates (d : SourceRationalProblem) (w : ℕ)
    (g : LocalQFTGate w) (k : ℕ) (hw : w ≤ nativeFrameWidth d + k) :
    sourceNativeGates (sourceFrameSynthesisProgram d w g k hw)
      = (emittedWord w g k).length := by
  simp [sourceFrameSynthesisProgram, sourceNativeGates, liftWordTo]

theorem sourceFrameSynthesisProgram_knownMatrix (d : SourceRationalProblem) (w : ℕ)
    (g : LocalQFTGate w) (k : ℕ) (hw : w ≤ nativeFrameWidth d + k) :
    sourceNativeKnownMatrix (sourceFrameSynthesisProgram d w g k hw)
      = localProgramMatrix (liftWordTo hw (emittedWord w g k)) := by
  simp [sourceFrameSynthesisProgram, sourceNativeKnownMatrix]

theorem sourceFrameSynthesisProgram_sameWord (d : SourceRationalProblem) (w : ℕ)
    (g : LocalQFTGate w) (k : ℕ) (hw : w ≤ nativeFrameWidth d + k) :
    (sourceFrameSynthesisProgram d w g k hw).steps.tail
      = (liftWordTo hw (emittedWord w g k)).map (fun h => SourceNativeStep.local h) := rfl

theorem sourceFrameSynthesisProgram_queryStep (d : SourceRationalProblem) (w : ℕ)
    (g : LocalQFTGate w) (k : ℕ) (hw : w ≤ nativeFrameWidth d + k) :
    (sourceFrameSynthesisProgram d w g k hw).steps.head?
      = some (SourceNativeStep.query
          (sourceAccessWires d (nativeFrameWidth d + k) (by unfold nativeFrameWidth; omega))
          false) := rfl

theorem clause94_sourceFrame_padded_error {w : ℕ} (g : LocalQFTGate w) (k : ℕ)
    (hg : IsFixedPrimitive g) :
    localProgramMatrix (emittedWord w g k) * padClean w w
      - padClean w w * localGateMatrix g = 0 := by
  have hemit : emittedWord w g k = [g] := by
    cases g with
    | h a => simp [emittedWord]
    | swap a c => simp [emittedWord]
    | cp a c e neg =>
        have he : e ≤ 3 := hg
        simp [emittedWord, he]
  rw [hemit]
  exact clause94_fixed_primitive_padded_error g

theorem rationalCertValid_diagonal {X : Type} [Fintype X] [DecidableEq X] (a : X → ℚ) (t : ℚ)
    (ht : 0 < t) (hb : ∀ r, |a r| ≤ t ^ 2) :
    RationalRectFactorization.rationalCertValid (diagonalRectFactorization a t) := by
  have ht0 : (t : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  refine ⟨?_, ?_, ?_⟩
  · intro r
    have h1 : RationalRectFactorization.massQRational (diagonalRectFactorization a t) r
        = (a r / t) * (a r / t) := by
      simp [RationalRectFactorization.massQRational, diagonalRectFactorization]
    rw [h1]
    have habs : |a r| ≤ t * t := by simpa [pow_two] using! hb r
    have h2 : (a r * a r) ≤ (t * t) * (t * t) := by
      calc a r * a r = |a r * a r| := (abs_of_nonneg (mul_self_nonneg (a r))).symm
        _ = |a r| * |a r| := abs_mul _ _
        _ ≤ (t * t) * (t * t) := mul_le_mul habs habs (abs_nonneg _) (by positivity)
    have h3 : 0 < t * t := by positivity
    have h4 : (a r * a r) / (t * t) ≤ ((t * t) * (t * t)) / (t * t) :=
      (div_le_div_iff_of_pos_right h3).mpr h2
    have h5 : ((t * t) * (t * t)) / (t * t) = t * t := by field_simp
    have h6 : (a r / t) * (a r / t) = (a r * a r) / (t * t) := by
      rw [← pow_two, div_pow]
      ring
    calc (a r / t) * (a r / t) = (a r * a r) / (t * t) := h6
      _ ≤ ((t * t) * (t * t)) / (t * t) := h4
      _ = t * t := h5
  · intro s
    have h1 : RationalRectFactorization.massVRational (diagonalRectFactorization a t) s
        = t * t := by
      simp [RationalRectFactorization.massVRational, diagonalRectFactorization]
    rw [h1]
    exact le_rfl
  · intro r s
    rw [RationalRectFactorization.rationalResidual]
    by_cases h : r = s
    · subst h
      have hcancel : ((a r / t) * t : ℚ) = a r := by
        field_simp
      simp [diagonalRectInstance, Matrix.diagonal, diagonalRectFactorization, hcancel]
    · simp [diagonalRectInstance, Matrix.diagonal, diagonalRectFactorization, h]

theorem clause90_search_certificate {X : Type} [Fintype X] [DecidableEq X] (a : X → ℚ) (δ : ℚ)
    (hδ : 0 < δ) :
    ∃ (fuel : ℕ) (t : ℚ) (C : DiagonalScaleCertificate a),
      scaleSearch (maxAbsRat a) δ fuel = some t ∧
      C.scale = t ∧ 0 < t ∧ (∀ r, |a r| ≤ t ^ 2) := by
  have hM : 0 ≤ maxAbsRat a := by
    unfold maxAbsRat
    rw [Finset.le_fold_max]
    exact Or.inl (le_refl 0)
  obtain ⟨fuel, t, hsearch⟩ := scaleSearch_exists hM hδ
  obtain ⟨n, hn, hge, htol, hpos⟩ := scaleSearch_sound hM hsearch
  have hbound : ∀ r, |a r| ≤ t ^ 2 := by
    intro r
    have h1 : |a r| ≤ maxAbsRat a := maxAbsRat_ge a r
    linarith
  have hvalid : RationalRectFactorization.rationalCertValid (diagonalRectFactorization a t) :=
    rationalCertValid_diagonal a t hpos hbound
  refine ⟨fuel, t, diagonalScaleCertificate a t hpos hvalid, hsearch, rfl, hpos, hbound⟩

theorem clause90_search_complete {X : Type} [Fintype X] [DecidableEq X]
    (a : X → ℚ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (δ : ℚ) (fuel : ℕ) (t : ℚ)
      (F : RationalRectFactorization 1 1 (diagonalRectInstance a).A (diagonalRectInstance a).Z),
      0 < δ ∧ (δ : ℝ) < ε ∧
      scaleSearch (maxAbsRat a) δ fuel = some t ∧
      0 < t ∧
      (∀ r, |(a r : ℝ)| ≤ (t : ℝ) ^ 2) ∧
      ((t : ℝ) ^ 2 ≤ diagonalScaleReal a + ε) ∧
      F.certValid ∧
      ENNReal.ofReal (diagonalScaleReal a) ≤
        sourceRectValue (rectComplex (diagonalRectInstance a).A)
          (rectComplexZ (diagonalRectInstance a).Z) ∧
      sourceRectValue (rectComplex (diagonalRectInstance a).A)
          (rectComplexZ (diagonalRectInstance a).Z) ≤ ENNReal.ofReal ((t : ℝ) ^ 2) := by
  obtain ⟨δ, hδ0, hδε⟩ := exists_rat_btwn (K := ℝ) hε
  have hδ0q : (0 : ℚ) < δ := by exact_mod_cast hδ0
  have hM : 0 ≤ maxAbsRat a := by
    unfold maxAbsRat
    rw [Finset.le_fold_max]
    exact Or.inl (le_refl 0)
  obtain ⟨fuel, t, hsearch⟩ := scaleSearch_exists hM hδ0q
  obtain ⟨n, hn, hge, htol, hpos⟩ := scaleSearch_sound hM hsearch
  have hscale : maxAbsRat a ≤ diagonalScaleReal a := maxAbsRat_le_scale a
  have hbound : ∀ r, |(a r : ℝ)| ≤ (t : ℝ) ^ 2 := by
    intro r
    have h1 : |a r| ≤ maxAbsRat a := maxAbsRat_ge a r
    have h1R : ((|a r| : ℚ) : ℝ) ≤ ((maxAbsRat a : ℚ) : ℝ) := by exact_mod_cast h1
    have h2 : ((|a r| : ℚ) : ℝ) = |(a r : ℝ)| := abs_rat_cast _
    have hgeR : ((maxAbsRat a : ℚ) : ℝ) ≤ ((t ^ 2 : ℚ) : ℝ) := by exact_mod_cast hge
    have hsqR : ((t ^ 2 : ℚ) : ℝ) = (t : ℝ) ^ 2 := by norm_cast
    linarith
  have hnear : (t : ℝ) ^ 2 ≤ diagonalScaleReal a + ε := by
    have hsqR : ((t ^ 2 : ℚ) : ℝ) = (t : ℝ) ^ 2 := by norm_cast
    have htolR : ((t ^ 2 - maxAbsRat a : ℚ) : ℝ) ≤ (δ : ℝ) := by exact_mod_cast htol
    have hsub : ((t ^ 2 - maxAbsRat a : ℚ) : ℝ)
        = ((t ^ 2 : ℚ) : ℝ) - ((maxAbsRat a : ℚ) : ℝ) := by norm_cast
    have hscaleR : ((maxAbsRat a : ℚ) : ℝ) ≤ diagonalScaleReal a := by exact_mod_cast hscale
    rw [← hsqR]
    linarith
  refine ⟨δ, fuel, t, diagonalRectFactorization a t, hδ0q, hδε, hsearch, hpos, hbound, hnear, ?_,
      ?_, ?_⟩
  · exact diagonalRectFactorization_certValid a t (by exact_mod_cast hpos) hbound
  · exact diagonal_value_lower_bound a
  · exact diagonal_value_upper_bound a t (by exact_mod_cast hpos) hbound

theorem clause90_complete {X : Type} [Fintype X] [DecidableEq X]
    (a : X → ℚ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (t : ℚ) (F : RationalRectFactorization 1 1 (diagonalRectInstance a).A
        (diagonalRectInstance a).Z),
      0 < t ∧
      (∀ r, |(a r : ℝ)| ≤ (t : ℝ) ^ 2) ∧
      ((t : ℝ) ^ 2 ≤ diagonalScaleReal a + ε) ∧
      F.certValid ∧
      ENNReal.ofReal (diagonalScaleReal a) ≤
        sourceRectValue (rectComplex (diagonalRectInstance a).A)
          (rectComplexZ (diagonalRectInstance a).Z) ∧
      sourceRectValue (rectComplex (diagonalRectInstance a).A)
          (rectComplexZ (diagonalRectInstance a).Z) ≤ ENNReal.ofReal ((t : ℝ) ^ 2) := by
  obtain ⟨δ, fuel, t, F, hδ0, hδε, hsearch, hpos, hbound, hnear, hcert, hlo, hhi⟩ :=
    clause90_search_complete a ε hε
  exact ⟨t, F, hpos, hbound, hnear, hcert, hlo, hhi⟩

theorem realCoordinateApprox_error (d : SourceRealProblem) (hacc : sourceRealAccess d)
    (x : Fin d.count) (h : Fin d.dimension) (target : Bool) (r : ℕ) :
    ‖ratCoordComplex (realCoordinateApprox d hacc x h target r) -
        (if target then d.target x h else d.start x h)‖ ≤ (1 / 2 : ℝ) ^ r := by
  have ht : sourceCoordinateAfter d x h target r (Classical.choose (hacc x h target r)) :=
    Classical.choose_spec (hacc x h target r)
  have hab : ∃ _ : ℚ, ∃ _ : ℚ, _ := sourceCoordinateAfter_pair ht
  have hb : ‖ratCoordComplex (Classical.choose hab, Classical.choose (Classical.choose_spec hab)) -
        (if target then d.target x h else d.start x h)‖ ≤ (1 / 2 : ℝ) ^ r := by
    simpa only [ratCoordComplex] using! (Classical.choose_spec (Classical.choose_spec hab))
  simpa [realCoordinateApprox] using! hb

theorem rationalizeReal_start_error (d : SourceRealProblem) (hacc : sourceRealAccess d) (R : ℕ)
    (x : Fin d.count) (h : Fin d.dimension) :
    ‖ratCoordComplex ((rationalizeReal d hacc R).start x h) - d.start x h‖ ≤ (1 / 2 : ℝ) ^ R := by
  have h1 : (rationalizeReal d hacc R).start x h = realCoordinateApprox d hacc x h false R := rfl
  rw [h1]
  exact realCoordinateApprox_error d hacc x h false R

theorem selectedComplexGram_eq (d : SourceRealProblem) (hacc : sourceRealAccess d) (R : ℕ)
    (x : Fin d.count) (y : Fin d.count) :
    selectedComplexGram d hacc R x y
      = ∑ h : Fin d.dimension,
          star (ratCoordComplex ((rationalizeReal d hacc R).start x h)) *
            (ratCoordComplex ((rationalizeReal d hacc R).start y h)) := rfl

theorem selectedComplexGram_error (d : SourceRealProblem) (hacc : sourceRealAccess d) (R : ℕ)
    (x : Fin d.count) (y : Fin d.count) :
    ‖selectedComplexGram d hacc R x y - trueComplexGram d x y‖
      ≤ (1 / 2 : ℝ) ^ R *
          ((∑ h : Fin d.dimension, ‖d.start y h‖) + (∑ h : Fin d.dimension, ‖d.start x h‖)) +
        (1 / 2 : ℝ) ^ R * (1 / 2 : ℝ) ^ R * d.dimension := by
  have herr : ∀ h : Fin d.dimension,
      ‖ratCoordComplex ((rationalizeReal d hacc R).start x h) - d.start x h‖
        ≤ (1 / 2 : ℝ) ^ R := by
    intro h
    have h1 : (rationalizeReal d hacc R).start x h = realCoordinateApprox d hacc x h false R := rfl
    rw [h1]
    exact realCoordinateApprox_error d hacc x h false R
  have hterm : ∀ h : Fin d.dimension,
      ‖star (ratCoordComplex ((rationalizeReal d hacc R).start x h)) *
          (ratCoordComplex ((rationalizeReal d hacc R).start y h)) -
        star (d.start x h) * (d.start y h)‖
        ≤ (1 / 2 : ℝ) ^ R * (‖d.start y h‖ + ‖d.start x h‖) +
          (1 / 2 : ℝ) ^ R * (1 / 2 : ℝ) ^ R := by
    intro h
    have hy : ‖ratCoordComplex ((rationalizeReal d hacc R).start y h) - d.start y h‖
        ≤ (1 / 2 : ℝ) ^ R := by
      have h1 : (rationalizeReal d hacc R).start y h = realCoordinateApprox d hacc y h false R :=
          rfl
      rw [h1]
      exact realCoordinateApprox_error d hacc y h false R
    have hns : ‖star (ratCoordComplex ((rationalizeReal d hacc R).start x h)) -
          star (d.start x h)‖ ≤ (1 / 2 : ℝ) ^ R := by
      rw [← star_sub, norm_star]
      exact herr h
    have hn : ‖star (ratCoordComplex ((rationalizeReal d hacc R).start x h))‖
        ≤ ‖d.start x h‖ + (1 / 2 : ℝ) ^ R := by
      calc ‖star (ratCoordComplex ((rationalizeReal d hacc R).start x h))‖
          = ‖ratCoordComplex ((rationalizeReal d hacc R).start x h)‖ := norm_star _
        _ = ‖(ratCoordComplex ((rationalizeReal d hacc R).start x h) - d.start x h) +
            d.start x h‖ := by congr 1; ring
        _ ≤ ‖ratCoordComplex ((rationalizeReal d hacc R).start x h) - d.start x h‖ +
            ‖d.start x h‖ := norm_add_le _ _
        _ ≤ (1 / 2 : ℝ) ^ R + ‖d.start x h‖ :=
            add_le_add_left (herr h) ‖d.start x h‖
        _ = ‖d.start x h‖ + (1 / 2 : ℝ) ^ R := by ring
    have e1 : ‖star (ratCoordComplex ((rationalizeReal d hacc R).start x h)) *
          (ratCoordComplex ((rationalizeReal d hacc R).start y h) - d.start y h)‖
        ≤ (‖d.start x h‖ + (1 / 2 : ℝ) ^ R) * ((1 / 2 : ℝ) ^ R) := by
      rw [norm_mul]
      calc ‖star (ratCoordComplex ((rationalizeReal d hacc R).start x h))‖ *
              ‖ratCoordComplex ((rationalizeReal d hacc R).start y h) - d.start y h‖
          ≤ (‖d.start x h‖ + (1 / 2 : ℝ) ^ R) * ‖ratCoordComplex
              ((rationalizeReal d hacc R).start y h) - d.start y h‖ :=
            mul_le_mul_of_nonneg_right hn (norm_nonneg _)
        _ ≤ (‖d.start x h‖ + (1 / 2 : ℝ) ^ R) * ((1 / 2 : ℝ) ^ R) :=
            mul_le_mul_of_nonneg_left hy (by positivity)
    have e2 : ‖(star (ratCoordComplex ((rationalizeReal d hacc R).start x h)) -
          star (d.start x h)) * (d.start y h)‖ ≤ ((1 / 2 : ℝ) ^ R) * ‖d.start y h‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hns (norm_nonneg _)
    have hdecomp : star (ratCoordComplex ((rationalizeReal d hacc R).start x h)) *
          (ratCoordComplex ((rationalizeReal d hacc R).start y h)) -
        star (d.start x h) * (d.start y h)
        = star (ratCoordComplex ((rationalizeReal d hacc R).start x h)) *
            (ratCoordComplex ((rationalizeReal d hacc R).start y h) - d.start y h) +
          (star (ratCoordComplex ((rationalizeReal d hacc R).start x h)) - star (d.start x h)) *
            (d.start y h) := by ring
    rw [hdecomp]
    calc ‖star (ratCoordComplex ((rationalizeReal d hacc R).start x h)) *
            (ratCoordComplex ((rationalizeReal d hacc R).start y h) - d.start y h) +
          (star (ratCoordComplex ((rationalizeReal d hacc R).start x h)) - star (d.start x h)) *
            (d.start y h)‖
        ≤ ‖star (ratCoordComplex ((rationalizeReal d hacc R).start x h)) *
            (ratCoordComplex ((rationalizeReal d hacc R).start y h) - d.start y h)‖ +
          ‖(star (ratCoordComplex ((rationalizeReal d hacc R).start x h)) - star (d.start x h)) *
            (d.start y h)‖ := norm_add_le _ _
        _ ≤ (‖d.start x h‖ + (1 / 2 : ℝ) ^ R) * ((1 / 2 : ℝ) ^ R) +
          ((1 / 2 : ℝ) ^ R) * ‖d.start y h‖ := by linarith [e1, e2]
        _ = (1 / 2 : ℝ) ^ R * (‖d.start y h‖ + ‖d.start x h‖) +
            (1 / 2 : ℝ) ^ R * (1 / 2 : ℝ) ^ R := by ring
  rw [selectedComplexGram_eq, trueComplexGram]
  calc ‖(∑ h : Fin d.dimension,
          star (ratCoordComplex ((rationalizeReal d hacc R).start x h)) *
            (ratCoordComplex ((rationalizeReal d hacc R).start y h))) -
        (∑ h : Fin d.dimension, star (d.start x h) * (d.start y h))‖
      = ‖∑ h : Fin d.dimension,
          (star (ratCoordComplex ((rationalizeReal d hacc R).start x h)) *
              (ratCoordComplex ((rationalizeReal d hacc R).start y h)) -
            star (d.start x h) * (d.start y h))‖ := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ h : Fin d.dimension,
          ‖star (ratCoordComplex ((rationalizeReal d hacc R).start x h)) *
              (ratCoordComplex ((rationalizeReal d hacc R).start y h)) -
            star (d.start x h) * (d.start y h)‖ := norm_sum_le _ _
      _ ≤ ∑ h : Fin d.dimension, ((1 / 2 : ℝ) ^ R * (‖d.start y h‖ + ‖d.start x h‖) +
          (1 / 2 : ℝ) ^ R * (1 / 2 : ℝ) ^ R) :=
        Finset.sum_le_sum fun h _ => hterm h
      _ = (1 / 2 : ℝ) ^ R *
            ((∑ h : Fin d.dimension, ‖d.start y h‖) + (∑ h : Fin d.dimension, ‖d.start x h‖)) +
          (1 / 2 : ℝ) ^ R * (1 / 2 : ℝ) ^ R * d.dimension := by
        have hcard : (∑ _h : Fin d.dimension, (1 : ℝ)) = d.dimension := by
          simp
        have hsum : (∑ _h : Fin d.dimension, (1 : ℝ) * ((1 / 2 : ℝ) ^ R * (1 / 2 : ℝ) ^ R))
            = (∑ _h : Fin d.dimension, (1 : ℝ)) * ((1 / 2 : ℝ) ^ R * (1 / 2 : ℝ) ^ R) := by
          rw [Finset.sum_mul]
        calc (∑ h : Fin d.dimension, ((1 / 2 : ℝ) ^ R * (‖d.start y h‖ + ‖d.start x h‖) +
              (1 / 2 : ℝ) ^ R * (1 / 2 : ℝ) ^ R))
            = (∑ h : Fin d.dimension, (1 / 2 : ℝ) ^ R * (‖d.start y h‖ + ‖d.start x h‖)) +
              ∑ _h : Fin d.dimension, (1 : ℝ) * ((1 / 2 : ℝ) ^ R * (1 / 2 : ℝ) ^ R) := by
                rw [Finset.sum_add_distrib]
                congr 1
                exact Finset.sum_congr rfl (fun h _ => by ring)
            _ = (1 / 2 : ℝ) ^ R * (∑ h : Fin d.dimension, (‖d.start y h‖ + ‖d.start x h‖)) +
                (∑ _h : Fin d.dimension, (1 : ℝ)) * ((1 / 2 : ℝ) ^ R * (1 / 2 : ℝ) ^ R) := by
                  rw [← Finset.mul_sum, hsum]
            _ = (1 / 2 : ℝ) ^ R *
                  ((∑ h : Fin d.dimension, ‖d.start y h‖) + (∑ h : Fin d.dimension, ‖d.start x h‖)) +
                (1 / 2 : ℝ) ^ R * (1 / 2 : ℝ) ^ R * d.dimension := by
                  rw [Finset.sum_add_distrib, hcard]
                  ring

end Qatlib.Papers.StateConvLee10.EffectiveCert
