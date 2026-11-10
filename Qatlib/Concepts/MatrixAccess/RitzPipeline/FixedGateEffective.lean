/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.FixedGateSynthesis
import Qatlib.Concepts.MatrixAccess.RitzPipeline.FixedGateEffectiveDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

noncomputable section

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib

def effectiveAnc : (w : ℕ) → LocalQFTGate w → ℕ → ℕ := fun _ _ _ => 0

def effectiveEmit : (w : ℕ) → (g : LocalQFTGate w) → (k : ℕ) →
    List (LocalQFTGate (w + effectiveAnc w g k)) :=
  fun _ g _ =>
    match g with
    | .h a => [.h a]
    | .cp a c e neg => if e ≤ 3 then [.cp a c e neg] else []
    | .swap a c => [.swap a c]

def effectiveCompiler : Compiler := ⟨effectiveAnc, effectiveEmit⟩

theorem effectiveCompiler_eq_partial : effectiveCompiler = partialCompiler := rfl

theorem effectiveCompiler_accepts_primitive {w : ℕ} (g : LocalQFTGate w) (k : ℕ)
    (hg : IsFixedPrim g) : AcceptsAt effectiveCompiler w g k := by
  rw [effectiveCompiler_eq_partial]
  exact partialCompiler_accepts_primitive w g k hg

theorem effectiveCompiler_accepts_smallAngle {w : ℕ} (a c : Fin w) (e : ℕ) (neg : Bool)
    (k : ℕ) (hk : 1 ≤ k) (he : k + 2 ≤ e) :
    AcceptsAt effectiveCompiler w (.cp a c e neg) k := by
  rw [effectiveCompiler_eq_partial]
  exact partialCompiler_accepts_smallAngle a c e neg k hk he

theorem effectiveCompiler_legal (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    ∀ g' ∈ effectiveCompiler.emit w g k, IsFixedPrim g' := by
  rw [effectiveCompiler_eq_partial]
  exact partialCompiler_legal w g k

theorem effectiveCompiler_zero_oracle (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    answerOracleCalls (effectiveCompiler.Segment w g k) = 0 := by
  rw [effectiveCompiler_eq_partial]
  exact partialCompiler_zero_oracle w g k

theorem effectiveCompiler_width (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    ∃ a : ℕ, (effectiveCompiler.Segment w g k).width = w + a := by
  rw [effectiveCompiler_eq_partial]
  exact partialCompiler_width w g k

theorem effectiveCompiler_clean (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    ancillaRestored w
      (localProgramMatrix (effectiveCompiler.Segment w g k).word
        * cleanEmbed w (effectiveCompiler.Segment w g k).width) (tolerance k) := by
  rw [effectiveCompiler_eq_partial]
  exact partialCompiler_clean w g k

theorem effectiveCompiler_uniform : UniformLedger effectiveCompiler := by
  rw [effectiveCompiler_eq_partial]
  exact partialCompiler_uniform

theorem effectiveCompiler_machine_budget :
    ∃ (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1))) (C : ℕ), 0 < C ∧
      ∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ),
        let ans := effectiveCompiler.Segment w g k
        let p := answerPlan ans
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emit [] k [] p = answerBits ans ∧
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emitterInput p [] k) (answerBits ans)
          (C * requestSize w g k ^ 12) (C * requestSize w g k ^ 12) := by
  rw [effectiveCompiler_eq_partial]
  exact partialCompiler_machine_budget

theorem effectiveCompiler_emit_cpOnlyFixed {w : ℕ} (a c : Fin w) (e : ℕ) (neg : Bool)
    (k : ℕ) : cpOnlyFixed (effectiveCompiler.emit w (.cp a c e neg) k) := by
  by_cases he : e ≤ 3
  · have hemit : effectiveCompiler.emit w (.cp a c e neg) k = [.cp a c e neg] := by
      simp [effectiveCompiler, effectiveEmit, effectiveAnc, he]
    rw [hemit]
    intro g hg
    have hg' : g = .cp a c e neg := by simpa using hg
    subst hg'
    exact ⟨a, c, e, neg, rfl, he⟩
  · have hemit : effectiveCompiler.emit w (.cp a c e neg) k = [] := by
      simp [effectiveCompiler, effectiveEmit, effectiveAnc, he]
    rw [hemit]
    intro g hg
    exact (List.not_mem_nil hg).elim

theorem effectiveCompiler_emit_cp_phase_content {w : ℕ} (a c : Fin w) (e : ℕ) (neg : Bool)
    (k : ℕ) (x : Reg w) :
    ∃ m : ℤ,
      localProgramMatrix (effectiveCompiler.emit w (.cp a c e neg) k) x x = eighthRoot m := by
  have hfix := effectiveCompiler_emit_cpOnlyFixed a c e neg k
  have hcontent := cpOnlyFixed_phase_content _ hfix x
  refine hcontent

end Qatlib.Concepts.MatrixAccess.RitzPipeline
