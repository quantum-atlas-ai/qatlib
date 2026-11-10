/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HermitianMap26.Construction.MainResult
import Qatlib.Papers.HermitianMap26.Construction.Variance
import Qatlib.Concepts.KrausCompile.SignedChoi
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.DimInstruments.DimTreeExec
open Qatlib.Concepts.KrausCompile.BornMoments
open scoped ComplexOrder BigOperators

namespace Qatlib.Papers.HermitianMap26.Construction

def canonicalSignedKraus {d : ℕ} (T : Op d →ₗ[ℂ] Op d)
    (hHP : ∀ X : Op d, X.IsHermitian → (T X).IsHermitian)
    (hTP : TracePreserving T) : SignedKraus d (ChoiMatrix T).rank where
  K := Qatlib.Concepts.KrausCompile.SignedChoi.canonicalKraus T hHP
  α := Qatlib.Concepts.KrausCompile.SignedChoi.canonicalSign T hHP
  sign := (Qatlib.Concepts.KrausCompile.SignedChoi.canonical_signed_representation T hHP hTP).1
  tracePreserving :=
    (Qatlib.Concepts.KrausCompile.SignedChoi.canonical_signed_representation T hHP hTP).2.2.1

theorem canonicalSignedKraus_action {d : ℕ} (T : Op d →ₗ[ℂ] Op d)
    (hHP : ∀ X : Op d, X.IsHermitian → (T X).IsHermitian)
    (hTP : TracePreserving T) (X : Op d) :
    (canonicalSignedKraus T hHP hTP).action X = T X :=
  ((Qatlib.Concepts.KrausCompile.SignedChoi.canonical_signed_representation T hHP hTP).2.2.2 X).symm

theorem intrinsic_rank_compilation {d : ℕ} (hd : 0 < d) (T : Op d →ₗ[ℂ] Op d)
    (hHP : ∀ X : Op d, X.IsHermitian → (T X).IsHermitian)
    (hTP : TracePreserving T) :
    let D := canonicalSignedKraus T hHP hTP
    KrausComplete D.compiledFamily ∧
      CompletelyPositive (krausMap D.compiledFamily) ∧
      TracePreserving (krausMap D.compiledFamily) ∧
      Qatlib.Concepts.KrausCompile.BinaryTree.SingleQubit d (D.compiledProgram hd) ∧
      (∀ t ∈ leaves (D.compiledProgram hd), t.measurements = Nat.clog 2 ((ChoiMatrix T).rank+1)) ∧
      (∀ X O, (T X * O).trace = ∑ i,
        D.postProcessingWeight D.normalization i *
          (D.compiledFamily i * X * (D.compiledFamily i)ᴴ * O).trace) := by
  let D := canonicalSignedKraus T hHP hTP
  obtain ⟨hc, hp, ht, hq, hm⟩ := D.source_construction hd
  refine ⟨hc, hp, ht, hq, hm, ?_⟩
  intro X O
  rw [← canonicalSignedKraus_action T hHP hTP X]
  exact D.trace_completed_postprocessing hd X O

theorem intrinsic_rank_shot_mean {d : ℕ} (hd : 0 < d) (T : Op d →ₗ[ℂ] Op d)
    (hHP : ∀ X : Op d, X.IsHermitian → (T X).IsHermitian)
    (hTP : TracePreserving T) (ρ : Op d) (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1)
    (O : Op d) (hO : O.IsHermitian) :
    let D := canonicalSignedKraus T hHP hTP
    ∃ (V : Op d) (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (eig : Fin d → ℝ),
      O = observable V eig ∧
      (D.shotLaw hd ρ V hρ htρ hV).expect (readout D.shotWeight eig) = (T ρ * O).trace.re := by
  obtain ⟨V, hV, eig, hObs⟩ := hermitian_readout_exists O hO
  refine ⟨V, hV, eig, hObs, ?_⟩
  rw [SignedKraus.actual_shot_mean, ← hObs, SignedKraus.compiledMean,
    canonicalSignedKraus_action T hHP hTP]

end Qatlib.Papers.HermitianMap26.Construction
