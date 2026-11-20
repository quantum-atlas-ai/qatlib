/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ErrorCorrection.Recovery.CssChannel
public import Qatlib.Concepts.ErrorCorrection.Recovery.CssNoise
public import Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecodingDefs
import Qatlib.Concepts.CodingDecoding.CssRecovery.CodingDecoding

@[expose] public section

/-! # Steane consumes the full signed recovery channel bridge -/

namespace QatlibTests.CssChannel

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecoding
open Qatlib.Foundations.PureStateMath
open scoped Matrix
open Qatlib.Concepts.ErrorCorrection.Recovery
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.ErrorCorrection.Recovery

/-- The concrete Steane syndrome is invariant under transport to the signed tableau. -/
theorem steaneSyndrome (e : PauliLabel (Fin 7)) :
    tabSyn (cssTable steaneData) e = cssSynEquiv (Fin 3) (Fin 3) (pauliSyndrome steaneData e) :=
  cssSyn_eq steaneData e

/-- Steane's actual decoder gives the same recovery on arbitrary input matrices in either
representation. -/
theorem steaneChannel (ρ : Matrix (BooleanVec 7) (BooleanVec 7) ℂ) :
    toRegisters 7 (recoveryChannel steaneData steaneDecoder ρ) =
      stabRecCh (cssTable steaneData) (cssStabProg steaneData steaneDecoder)
        (toRegisters 7 ρ) :=
  cssRecovery_eq steaneData steaneDecoder ρ

/-- The actual Steane decoder restores an encoded qubit together with any finite reference
under complete noise in the single-qubit Pauli span. -/
theorem steaneReference :
    ∃ V : Matrix (BooleanVec 7) (Fin 2) ℂ,
      (∀ j, (fun i => V i j) ∈ cssCodespace steaneData) ∧
      (cssEmbedding V)ᴴ * cssEmbedding V = 1 ∧
      ∀ {q ref : ℕ} (K : Fin q → Operator (Fintype.card (BooleanVec 7))), KrausComplete K →
        (∀ i, K i ∈ Submodule.span ℂ
          {A | ∃ e : PauliLabel (Fin 7), pauliWeight e.1 e.2 ≤ 1 ∧ A = cssIndexed e}) →
        ∀ A : Matrix (Fin 2 × Fin ref) (Fin 2 × Fin ref) ℂ,
          tensorLeft (krausMap (cssKraus steaneData steaneDecoder))
            (tensorLeft (krausMap K) (tensorLeft (conjBranch (cssEmbedding V)) A)) =
              tensorLeft (conjBranch (cssEmbedding V)) A := by
  have hEnc : Nonempty (CssEncoding steaneData 1) := by
    simpa only [steaneData_encodedQubits] using exists_cssEncoding steaneData
  obtain ⟨E⟩ := hEnc
  let e : Fin 2 ≃ (Fin 1 → ZMod 2) :=
    ((ZMod.finEquiv 2).toEquiv).trans
      { toFun := fun b _ => b
        invFun := fun f => f 0
        left_inv := fun b => rfl
        right_inv := fun f => funext fun j => congrArg f (Subsingleton.elim 0 j) }
  let V : Matrix (BooleanVec 7) (Fin 2) ℂ := fun i j => E.enc (e j) i
  have hV (j : Fin 2) : (fun i => V i j) ∈ cssCodespace steaneData := E.mem_codespace (e j)
  have hIso : (cssEmbedding V)ᴴ * cssEmbedding V = 1 := cssEmbedding_iso E e
  refine ⟨V, hV, hIso, ?_⟩
  intro q ref K hK hspan A
  exact css_ref steaneData steaneDecoder 1
    Qatlib.Concepts.CodingDecoding.CssRecovery.steaneDecoder_correctsUpTo
    V hV hIso K hK hspan A

end QatlibTests.CssChannel
