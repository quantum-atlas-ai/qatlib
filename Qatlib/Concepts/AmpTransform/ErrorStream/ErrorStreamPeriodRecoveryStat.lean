/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.ErrorStreamSuccessMass
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Qatlib.Concepts.AmpTransform.SuccessRatio

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.ErrorStream

def ErrorStreamPeriodRecovery : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (s M L P B R : ℕ) (G : Finset (Fin N)) (h : Fin N → Bool),
    2 ≤ M → 2 ≤ P → s+(M-1)*P < N → M*P ≤ N → P ≤ B → 2*B^2 < N →
    G.card = L → Disjoint G (aqProgressionSet N s M P) →
    2*(M+L) ≤ N → (L:ℝ) < 2*(M:ℝ)/Real.pi → 0 < R →
    (∀ x, h x = decide (x ∈ aqProgressionSet N s M P ∪ G)) →
      let C := aqProgressionSet N s M P ∪ G
      let T := M+L
      let w : Fin N → ℝ := fun y => BornProb (aqState N hN T C) y
      let b : ℝ := ∑ y, if (aqAttempt h s M B y).1 = none then w y else 0
      let q := aqErrorSuccessLower N M L P
      let k := aqRounds N T
      (∑ ω : Fin R → Fin N, ∏ r, w (ω r)) = 1 ∧
      (∑ ω : Fin R → Fin N,
        if (aqRetry h s M B k (List.ofFn ω)).1 = none then ∏ r, w (ω r) else 0) = b^R ∧
      (∑ ω ∈ Finset.univ.filter (fun ω : Fin R → Fin N =>
        (aqRetry h s M B k (List.ofFn ω)).1 = some P), ∏ r, w (ω r)) ≥ q ∧
      (∀ ω : Fin R → Fin N, (aqRetry h s M B k (List.ofFn ω)).2 ≤ R*(k+3)) ∧
      (∑ ω : Fin R → Fin N, (∏ r, w (ω r))*((aqRetry h s M B k (List.ofFn ω)).2:ℝ)) ≤
        ((k+3:ℕ):ℝ)/q
end Qatlib.Concepts.AmpTransform.ErrorStream
