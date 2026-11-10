/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.StateConversionDefs
import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveInstrumentPurificationQuan
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.ConversionCore.WitnessCompile Matrix
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib
open Qatlib
open Qatlib.Concepts.GramQueryCore.ModelSemantics
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.ConversionCore.WitnessCompile

private def sourceWordToAdaptive {S : Type} : SourceWord S → SourceAdaptive S
  | [] => .finish
  | .inl U :: rest => .known U (sourceWordToAdaptive rest)
  | .inr adj :: rest => .query adj (sourceWordToAdaptive rest)

private noncomputable def sourceWordGate {S : Type} (O : Matrix S S ℂ) :
    Matrix S S ℂ ⊕ Bool → Matrix S S ℂ
  | .inl U => U
  | .inr adj => if adj then Oᴴ else O

private theorem sourceWordMatrix_cons {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (s : Matrix S S ℂ ⊕ Bool) (C : SourceWord S) :
    sourceWordMatrix O (s :: C) = sourceWordMatrix O C * sourceWordGate O s := by
  rcases s with U | adj <;>
    simp only [sourceWordMatrix, sourceWordGate, List.map_cons, List.reverse_cons,
      List.prod_append, List.prod_singleton]

private theorem sourceWordToAdaptive_legal {S : Type} [Fintype S] [DecidableEq S]
    (C : SourceWord S) (hC : sourceWordLegal C) :
    sourceAdaptiveLegal (sourceWordToAdaptive C) := by
  induction C with
  | nil => trivial
  | cons s rest ih =>
    have hrest : sourceWordLegal rest := fun s' hs' => hC s' (List.mem_cons_of_mem _ hs')
    have hs := hC s (by simp)
    rcases s with U | adj
    · exact ⟨hs, ih hrest⟩
    · exact ih hrest

private theorem sourceWordToAdaptive_calls {S : Type} (C : SourceWord S) :
    sourceAdaptiveCalls (sourceWordToAdaptive C) ≤ sourceWordCalls C := by
  induction C with
  | nil => exact le_refl _
  | cons s rest ih =>
    rcases s with U | adj
    · simp only [sourceWordToAdaptive, sourceAdaptiveCalls]
      simpa only [sourceWordCalls] using! ih
    · have hEq : sourceWordCalls (Sum.inr adj :: rest) = 1 + sourceWordCalls rest := by
        simp [sourceWordCalls]
        omega
      have hEq2 : sourceAdaptiveCalls (.query adj (sourceWordToAdaptive rest))
          = 1 + sourceAdaptiveCalls (sourceWordToAdaptive rest) := rfl
      show sourceAdaptiveCalls (.query adj (sourceWordToAdaptive rest)) ≤ _
      rw [hEq2, hEq]
      exact Nat.add_le_add_left ih _

private theorem sourceWordToAdaptive_density {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (C : SourceWord S) (ψ : QState S) :
    ∀ (p t : S), sourceAdaptiveDensity O (sourceWordToAdaptive C) ψ p t =
      (sourceWordMatrix O C *ᵥ ψ) p * star ((sourceWordMatrix O C *ᵥ ψ) t) := by
  induction C generalizing ψ with
  | nil =>
    intro p t
    simp only [sourceWordMatrix, List.map_nil, List.reverse_nil,
      List.prod_nil, Matrix.one_mulVec, sourceWordToAdaptive, sourceAdaptiveBranches,
      sourceAdaptiveDensity, List.map_singleton, List.sum_singleton, Matrix.of_apply]
  | cons s rest ih =>
    intro p t
    have ih' (φ : QState S) : (List.map (fun φ' => φ' p * star (φ' t))
        (sourceAdaptiveBranches O (sourceWordToAdaptive rest) φ)).sum =
        (sourceWordMatrix O rest *ᵥ φ) p * star ((sourceWordMatrix O rest *ᵥ φ) t) := by
      have h := ih φ p t
      simpa only [sourceAdaptiveDensity, Matrix.of_apply] using! h
    have hgate (φ : QState S) : sourceWordMatrix O (s :: rest) *ᵥ φ =
        sourceWordMatrix O rest *ᵥ (sourceWordGate O s *ᵥ φ) := by
      rw [sourceWordMatrix_cons, Matrix.mulVec_mulVec]
    rcases s with U | adj
    · rw [show sourceWordToAdaptive (Sum.inl U :: rest) =
          .known U (sourceWordToAdaptive rest) from rfl,
        sourceAdaptiveDensity, sourceAdaptiveBranches, Matrix.of_apply,
        ih' (U *ᵥ ψ), hgate ψ]
      simp only [sourceWordGate]
    · rw [show sourceWordToAdaptive (Sum.inr adj :: rest) =
          .query adj (sourceWordToAdaptive rest) from rfl,
        sourceAdaptiveDensity, sourceAdaptiveBranches, Matrix.of_apply,
        ih' ((if adj then Oᴴ else O) *ᵥ ψ), hgate ψ]
      simp only [sourceWordGate]

private theorem sourceWordAccounting : SourceWordAccountingSpec := by
  intro X H _ _ _ _ n q input ρ σ ε r hr C hC
  constructor
  · intro hcoh
    exact sInf_le ⟨r, hr, C, rfl, hC, hcoh⟩
  · intro hnoncoh
    exact sInf_le ⟨r, hr, C, rfl, hC, hnoncoh⟩

theorem clause91 : AdaptiveBridgeSpec :=
  ⟨Qatlib.Concepts.ConversionCore.WitnessCompile.adaptiveInstrumentPurification,
    sourceWordAccounting, fun _ _ _ C hC =>
      ⟨sourceWordToAdaptive C, sourceWordToAdaptive_legal C hC, sourceWordToAdaptive_calls C,
        fun O ψ p t => sourceWordToAdaptive_density O C ψ p t⟩⟩
end Qatlib.Concepts.ConversionCore.WitnessCompile
