/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeAutoPrep
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.CircuitImpl.ReflectionCompile
/-! Reuse the pinned per-wire Hadamard implementation for the actual native
Walsh word. Rounding an internal positive cutoff to a power of two changes
it by less than a factor two and leaves the full matrix-function goal intact. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical BigOperators

/-- Construction for walsh Cutoff Width in the native walsh model. -/
def walshCutoffWidth (b : ℕ) : ℕ := Nat.size (b-1)
/-- Construction for walsh Cutoff in the native walsh model. -/
def walshCutoff (b : ℕ) : ℕ := 2^walshCutoffWidth b

/-- The actual finite construction obeys the displayed quantitative bound with its parameter guards. -/
theorem walshCutoff_pos (b : ℕ) : 0<walshCutoff b := by unfold walshCutoff; positivity

/-- The actual finite construction obeys the displayed quantitative bound with its parameter guards. -/
theorem walshCutoff_ge (b : ℕ) (hb : 0<b) : b≤walshCutoff b := by
  have hh := nativeLabelCapacity (b-1)
  simpa only [show b-1+1=b by omega,nativeLabelWidth,walshCutoff,walshCutoffWidth] using hh

/-- The actual finite construction obeys the displayed quantitative bound with its parameter guards. -/
theorem walshCutoff_lt_double (b : ℕ) (hb : 0<b) : walshCutoff b<2*b := by
  generalize hw : Nat.size (b-1)=m
  cases m with
  | zero => simp only [walshCutoff,walshCutoffWidth,hw,pow_zero]; omega
  | succ m =>
    have hp : 2^m < b := by
      by_contra hn
      have hc : b-1+1≤2^m := by omega
      have hs := (nativeLabelWidth_minimal (b-1) m).mpr hc
      change Nat.size (b-1) ≤ m at hs
      rw [hw] at hs
      omega
    simp only [walshCutoff,walshCutoffWidth,hw,pow_succ]
    omega

/-- The actual finite construction obeys the displayed quantitative bound with its parameter guards. -/
theorem walshCutoff_query_bound (b : ℕ) (hb : 0<b) : 2*walshCutoff b-1≤2*(2*b-1) := by
  have hh := walshCutoff_lt_double b hb
  omega

/-- The actual finite construction obeys the displayed quantitative bound with its parameter guards. -/
theorem walshCutoff_reciprocalError (b : ℕ) (hb : 0<b) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) :
    Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalError δ (walshCutoff b)≤
      Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalError δ b := by
  unfold Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalError
  apply div_le_div_of_nonneg_right _ hδ.le
  apply pow_le_pow_of_le_one (by nlinarith : 0≤1-δ^2) (by nlinarith : 1-δ^2≤1)
  exact walshCutoff_ge b hb

/-- The actual finite construction obeys the displayed quantitative bound with its parameter guards. -/
theorem walshCutoff_square_error (b : ℕ) (hb : 0<b) (e : ℝ) (he : 0≤e) :
    (walshCutoff b : ℝ)^2*e≤4*(b : ℝ)^2*e := by
  have hnat := walshCutoff_lt_double b hb
  have hreal : (walshCutoff b : ℝ)<2*(b : ℝ) := by exact_mod_cast hnat
  have hsq : (walshCutoff b : ℝ)^2≤(2*(b : ℝ))^2 := by
    nlinarith [show 0≤(walshCutoff b : ℝ) by positivity,show 0≤(b : ℝ) by positivity]
  have hh := mul_le_mul_of_nonneg_right hsq he
  nlinarith

/-- Construction for native Walsh Ops in the native walsh model. -/
def nativeWalshOps {N : ℕ} (ws : List (Fin N)) : List (NativeKnown.Gate N) := ws.map NativeKnown.Gate.h

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem nativeWalshOps_legal {N : ℕ} (ws : List (Fin N)) : NativeKnown.wordLegal (nativeWalshOps ws) := by
  intro g hg
  obtain ⟨w,_,rfl⟩ := List.mem_map.mp hg
  trivial

/-- Evaluation of the emitted native word equals the stated concrete matrix semantics. -/
theorem nativeWalshOps_local_matrix {N : ℕ} (ws : List (Fin N)) :
    reflectionProgramMatrix (NativeKnown.wordCompile (nativeWalshOps ws))=
      localProgramMatrix (ws.map Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalQFTGate.h) := by
  have hm (w : Fin N) : NativeKnown.matrix (NativeKnown.Gate.h w)=localGateMatrix (Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalQFTGate.h w) := by
    ext x y
    change wireGate N w Hadamard x y=_
    rw [wireGate_apply]
    rfl
  rw [NativeKnown.wordCompile_matrix _ (nativeWalshOps_legal ws)]
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change NativeKnown.wordMatrix (nativeWalshOps ws)*NativeKnown.matrix (NativeKnown.Gate.h w)=_
    rw [hm,ih]
    rfl

/-- The concrete matrix entries have the displayed exact coordinate formula. -/
theorem nativeWalshOps_entry {N : ℕ} (ws : List (Fin N)) (hn : ws.Nodup) (y x : Reg N) :
    reflectionProgramMatrix (NativeKnown.wordCompile (nativeWalshOps ws)) y x=
      if ∀ k : Fin N,k∉ws → y k=x k then (ws.map (fun w => Hadamard (y w) (x w))).prod else 0 := by
  rw [nativeWalshOps_local_matrix]
  exact Qatlib.Concepts.QftPreparation.LocalQFTImplementation.localProgramMatrix_map_h ws hn y x

/-- The actual matrix or program has the displayed value on its origin column. -/
theorem nativeWalshOps_zero_column {N : ℕ} (ws : List (Fin N)) (hn : ws.Nodup)
    (x : Reg N) (hx : ∀ w∈ws,x w=false) (y : Reg N) :
    reflectionProgramMatrix (NativeKnown.wordCompile (nativeWalshOps ws)) y x=
      if ∀ k : Fin N,k∉ws → y k=x k then ((Real.sqrt 2 : ℂ)⁻¹)^ws.length else 0 := by
  rw [nativeWalshOps_entry ws hn y x]
  congr 1
  calc
    (ws.map (fun w => Hadamard (y w) (x w))).prod=(ws.map (fun _ => (Real.sqrt 2 : ℂ)⁻¹)).prod := by
      congr 1
      apply List.map_congr_left
      intro w hw
      rw [hx w hw,hadamard_apply_false]
    _ = _ := by simp

/-- The same emitted program has the displayed exact query and elementary-gate counts. -/
theorem nativeWalshOps_counts {N : ℕ} (ws : List (Fin N)) :
    QueryCount (reflectionCompile (NativeKnown.wordCompile (nativeWalshOps ws)))=0 ∧
    GateCount (reflectionCompile (NativeKnown.wordCompile (nativeWalshOps ws)))=ws.length := by
  have hh := NativeKnown.wordCompile_counts (nativeWalshOps ws)
  simpa [nativeWalshOps,List.map_map,Function.comp_def,NativeKnown.gateCost] using hh

/-- The actual native inverse or adjoint satisfies the displayed operator identity. -/
theorem nativeWalshOps_adjointWord {N : ℕ} (ws : List (Fin N)) :
    NativeKnown.adjointWord (nativeWalshOps ws)=nativeWalshOps ws.reverse := by
  simp [NativeKnown.adjointWord,nativeWalshOps,List.map_reverse,List.map_map,Function.comp_def,NativeKnown.inverse]

/-- The actual native inverse or adjoint satisfies the displayed operator identity. -/
theorem nativeWalshOps_selfadjoint {N : ℕ} (ws : List (Fin N)) (hn : ws.Nodup) :
    (reflectionProgramMatrix (NativeKnown.wordCompile (nativeWalshOps ws)))ᴴ=
      reflectionProgramMatrix (NativeKnown.wordCompile (nativeWalshOps ws)) := by
  rw [← NativeKnown.wordCompile_adjoint _ (nativeWalshOps_legal ws),nativeWalshOps_adjointWord]
  ext x y
  rw [nativeWalshOps_entry ws.reverse (List.nodup_reverse.mpr hn),nativeWalshOps_entry ws hn]
  simp only [List.mem_reverse,List.map_reverse,List.prod_reverse]

/-- Evaluation of the emitted native word equals the stated concrete matrix semantics. -/
theorem nativeWalshOps_all_matrix (m : ℕ) :
    reflectionProgramMatrix (NativeKnown.wordCompile (nativeWalshOps (List.finRange m)))=HadamardN m := by
  rw [nativeWalshOps_local_matrix]
  exact Qatlib.Concepts.QftPreparation.LocalQFTImplementation.localProgramMatrix_localHadamard m

/-- Construction for native Walsh Label Matrix in the native walsh model. -/
def nativeWalshLabelMatrix (m : ℕ) : Matrix (Fin (2^m)) (Fin (2^m)) ℂ :=
  relabelGate (sourceLEEquiv m) (reflectionProgramMatrix (NativeKnown.wordCompile (nativeWalshOps (List.finRange m))))

/-- The constructed finite matrix is unitary under the stated hypotheses. -/
theorem nativeWalshLabelMatrix_unitary (m : ℕ) : nativeWalshLabelMatrix m∈unitaryGroup (Fin (2^m)) ℂ :=
  relabelGate_mem_unitary (reflectionProgramMatrix_unitary _ (NativeKnown.wordCompile_legal _ (nativeWalshOps_legal _))) _

/-- The actual matrix or program has the displayed value on its origin column. -/
theorem nativeWalshLabelMatrix_column (m : ℕ) (i : Fin (2^m)) :
    nativeWalshLabelMatrix m i 0=((Real.sqrt 2 : ℂ)⁻¹)^m := by
  unfold nativeWalshLabelMatrix
  rw [nativeWalshOps_all_matrix]
  simp only [relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,sourceLEEquiv_decode_zero]
  exact hadamardN_apply_zero_right _

/-- The concrete column has the displayed exact Born probability. -/
theorem nativeWalshLabelMatrix_probability (m : ℕ) (i : Fin (2^m)) :
    Complex.normSq (nativeWalshLabelMatrix m i 0)=((2^m : ℕ) : ℝ)⁻¹ := by
  apply Complex.ofReal_injective
  rw [Complex.normSq_eq_conj_mul_self]
  rw [nativeWalshLabelMatrix_column]
  have hs : star ((Real.sqrt 2 : ℂ)⁻¹)=(Real.sqrt 2 : ℂ)⁻¹ := by simp [RCLike.star_def]
  change star (((Real.sqrt 2 : ℂ)⁻¹)^m)*((Real.sqrt 2 : ℂ)⁻¹)^m=_
  rw [star_pow,hs,← mul_pow,inv_sqrt2_mul_self,inv_pow]
  simp

/-- Construction for native Walsh Deviation in the native walsh model. -/
def nativeWalshDeviation (m : ℕ) : ℝ :=
  ∑ i : Fin (2^m),|Complex.normSq (nativeWalshLabelMatrix m i 0)-((2^m : ℕ) : ℝ)⁻¹|

/-- The exact finite Walsh column has zero deviation from the stated uniform probabilities. -/
theorem nativeWalshDeviation_zero (m : ℕ) : nativeWalshDeviation m=0 := by
  simp [nativeWalshDeviation,nativeWalshLabelMatrix_probability]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
