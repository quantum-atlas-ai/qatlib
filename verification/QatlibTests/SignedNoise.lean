/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ErrorCorrection.Recovery.SignedBranch
public import Qatlib.Papers.PerfectQEC96.FiveQubit

@[expose] public section

/-! # The non-CSS five-qubit decoder consumes the correctable error space -/

namespace QatlibTests.SignedNoise

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.ErrorCorrection.ErrorClasses
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.PerfectQEC96
open Qatlib.Concepts.ErrorCorrection.Recovery
open scoped Matrix

/-- The actual perfect-code decoder corrects the complex span of the single-qubit Pauli
operators on every encoding into the five-qubit code. -/
theorem fiveErrorSpan (V : Matrix (Reg 5) (Fin 2) ℂ)
    (hV : ∀ j, (fun i => V i j) ∈ codeSpace fiveTab) :
    Submodule.span ℂ {A | ∃ v, sympWt v ≤ 1 ∧ A = regError v} ≤
      correctable (regEncoding V) (regRecovery fiveTab fiveProg) :=
  signed_span fiveTab five_cons (independent_of_row_linearIndependent fiveTab five_indep)
    fiveProg 1 five_res V hV

/-- The actual five-qubit recovery returns the encoded state for complete noise in the
single-qubit Pauli span, even with a finite reference system. -/
theorem fiveReference {q ref : ℕ} (V : Matrix (Reg 5) (Fin 2) ℂ)
    (hV : ∀ j, (fun i => V i j) ∈ codeSpace fiveTab)
    (hIso : (regEncoding V)ᴴ * regEncoding V = 1)
    (K : Fin q → Operator (2 ^ 5)) (hK : KrausComplete K)
    (hspan : ∀ i, K i ∈ Submodule.span ℂ {A | ∃ v, sympWt v ≤ 1 ∧ A = regError v})
    (A : Matrix (Fin 2 × Fin ref) (Fin 2 × Fin ref) ℂ) :
    tensorLeft (krausMap (regRecovery fiveTab fiveProg))
      (tensorLeft (krausMap K) (tensorLeft (conjBranch (regEncoding V)) A)) =
        tensorLeft (conjBranch (regEncoding V)) A :=
  signed_ref fiveTab five_cons (independent_of_row_linearIndependent fiveTab five_indep)
    fiveProg 1 five_res V hV hIso K hK hspan A

/-- The actual five-qubit code has a two-column encoding that the channel restores for all
complete correctable Kraus noise, with any finite reference system. -/
theorem fiveEncoding :
    ∃ V : Matrix (Reg 5) (Fin 2) ℂ,
      (∀ j, (fun i => V i j) ∈ codeSpace fiveTab) ∧
      (regEncoding V)ᴴ * regEncoding V = 1 ∧
      ∀ {q ref : ℕ} (K : Fin q → Operator (2 ^ 5)), KrausComplete K →
        (∀ i, K i ∈ Submodule.span ℂ {A | ∃ v, sympWt v ≤ 1 ∧ A = regError v}) →
        ∀ A : Matrix (Fin 2 × Fin ref) (Fin 2 × Fin ref) ℂ,
          tensorLeft (krausMap (regRecovery fiveTab fiveProg))
            (tensorLeft (krausMap K) (tensorLeft (conjBranch (regEncoding V)) A)) =
              tensorLeft (conjBranch (regEncoding V)) A := by
  obtain ⟨V, hV, hIso⟩ := exists_regEnc fiveTab five_params.1
  exact ⟨V, hV, hIso, fun K hK hspan A => fiveReference V hV hIso K hK hspan A⟩

end QatlibTests.SignedNoise
