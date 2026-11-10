/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.PaidModels
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Matrix
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

def TunableQueryTunableActualQueryComplexity : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs prices : ℕ → ℕ)
    (B : ℝ), clockLegal m P bad → stageLegal m P U → Normalized ω → 0 ≤ B →
    let E := extendClock m P
    let a := plainAmplitude E bad U ω m
    0 < a → tunable m E bad U ω α rs →
    (∀ j : Fin m, α (j.val+1) ≤ 1) → (∑ j : Fin m, α (j.val+1)) ≤ B →
    let C := nestedWord E bad ω rs m
    legal (m+1) C ∧
    (calls C 0 : ℝ) ≤ (6/5 : ℝ).rpow B/a ∧
    ((Finset.univ.filter (fun j : Fin m => 0 < rs (j.val+1))).card : ℝ) ≤ (B*Real.log (6/5)+Real.log (1/a))/Real.log 3 ∧
    ∀ (l : ℕ) (s : Fin (l+2) → ℕ),
      s 0=0 → s ⟨l+1,by omega⟩=m+1 →
      (∀ j : Fin (l+1), s ⟨j.val,by omega⟩ < s ⟨j.val+1,by omega⟩) →
      (∀ j : Fin m, (0 < rs (j.val+1) ↔ ∃ v : Fin l, s ⟨v.val+1,by omega⟩=j.val+1)) →
      (weightedCost prices C : ℝ) ≤ 6*(6/5 : ℝ).rpow (2*B)/a*
        (((prices 0+blockFee prices m 0 (s 1) : ℕ) : ℝ)+
          ∑ v : Fin l,
            plainAmplitude E bad U ω (s ⟨v.val+1,by omega⟩)*
              blockFee prices m (s ⟨v.val+1,by omega⟩) (s ⟨v.val+2,by omega⟩)/
                Real.sqrt (α (s ⟨v.val+1,by omega⟩)))

end Qatlib.Concepts.QlsReadoutSpec.Amplification
