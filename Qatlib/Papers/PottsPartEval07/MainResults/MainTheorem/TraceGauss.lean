/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem.GaussPotts
public import Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem.TraceClasses
public import Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem.UniformBridge

@[expose] public section

/-!
# Trace-code Gauss-query reduction for the physical Potts partition function

The input describes actual trace coordinates and multiplicative field orbits.
The circuit reads actual Gauss phases, the decoder rounds the observed labels,
and the output equals the original physical partition function on a successful
record. The two remaining source arithmetic obligations are the McEliece
phase-weight identity and its divisibility lattice. This theorem remains a
query reduction; it makes no unproved finite-gate runtime claim.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

open scoped BigOperators
open Qatlib.Papers.PottsPartEval07.CodeStructure
open Qatlib.Papers.PottsPartEval07.ExactRecovery
open Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod (ringChar F)) F] [NeZero (ringChar F)]
  {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [DecidableEq F] in
/-- A spanning trace representation transfers the actual field cardinality to its code. -/
theorem trace_code_card (g : E → F)
    (hspan : Submodule.span (ZMod (ringChar F)) (Set.range g) = ⊤) :
    Fintype.card (traceCode g) = Fintype.card F := by
  exact (Fintype.card_congr (traceWordEquiv g hspan).toEquiv).symm

/-- Success is measured against the original uniform-coupling physical Potts partition. -/
def actualUniformMass {classes terms : ℕ} (batch : GaussBatch F terms)
    (ends : E → V × V) (codeSize classSize M spacing : ℕ) (hM : 0 < M)
    (base scale : ℝ) (coefficient : Fin classes → Fin terms → ℂ) (coupling : ℝ) : ℝ :=
  ∑ record : Fin terms → Fin M,
    if recordedPotts (q := ringChar F) ends codeSize classSize M spacing base scale coefficient
        record (Real.exp (-coupling)) =
      (pottsPartition (ringChar F) ends (fun _ => coupling) : ℂ)
    then ∏ a, gaussMarginal M hM (batch.character a) batch.additive batch.frequency (record a)
    else 0

omit [Algebra (ZMod (ringChar F)) F] [DecidableEq E] in
/-- The graph/code identity transfers actual output success to the physical partition function. -/
theorem actualUniformMass_eq {classes terms : ℕ} (batch : GaussBatch F terms)
    (ends : E → V × V) (codeSize classSize M spacing : ℕ) (hM : 0 < M)
    (base scale : ℝ) (coefficient : Fin classes → Fin terms → ℂ) (coupling : ℝ) :
    actualUniformMass batch ends codeSize classSize M spacing hM base scale coefficient coupling =
      actualExactMass (q := ringChar F) batch ends codeSize classSize M spacing hM base scale
        coefficient (Real.exp (-coupling)) := by
  unfold actualUniformMass actualExactMass
  rw [uniform_partition]

/-- Actual trace-code orbits and local arithmetic certificates give a positive-query
Gauss-execution algorithm for the original uniform physical Potts value. -/
theorem trace_gauss_reduction {classes terms classSize : ℕ} (batch : GaussBatch F terms)
    (hd : 0 < terms) (ends : E → V × V) (g : E → F)
    (hspan : Submodule.span (ZMod (ringChar F)) (Set.range g) = ⊤)
    (orbits : TraceOrbits g classes classSize)
    (hdual : dualCode (traceCode g) = graphCode ends)
    (k : ℕ) (hfield : Fintype.card F = ringChar F ^ k)
    (spacing : ℕ) (hspacing : 0 < spacing) (base scale : ℝ) (hs : 0 ≤ scale)
    (coefficient : Fin classes → Fin terms → ℂ) (hc : ∀ i a, ‖coefficient i a‖ ≤ 1)
    (hformula : ∀ i, turnWeight base scale (coefficient i) (gaussPhases batch) =
      hammingWeight (traceWord g (orbits.representative i)))
    (hdiv : ∀ i, spacing ∣ hammingWeight (traceWord g (orbits.representative i)))
    (radius : ℝ) (hr : 0 < radius) (hr1 : radius < 1)
    (hp : scale * (terms * (2 * Real.pi * radius)) < spacing / 2) (coupling : ℝ) :
    ∃ hM : 0 < sampleSize terms radius,
      0 < batchQueries terms (sampleSize terms radius) ∧
      3 / 4 ≤ actualUniformMass batch ends (ringChar F ^ k) classSize
        (sampleSize terms radius) spacing hM base scale coefficient coupling ∧
      (batchQueries terms (sampleSize terms radius) : ℝ) ≤ 3 * (terms : ℝ) ^ 2 / radius := by
  have hcard : Fintype.card (traceCode g) = ringChar F ^ k :=
    (trace_code_card g hspan).trans hfield
  obtain ⟨hM, hpositive, hsuccess, hqueries⟩ := gauss_potts_reduction batch hd ends
    (traceCode g) (traceWeightClasses g hspan orbits) hdual k hcard spacing hspacing
    base scale hs coefficient hc hformula hdiv radius hr hr1 hp (Real.exp (-coupling))
    (Real.exp_ne_zero _)
  refine ⟨hM, hpositive, ?_, hqueries⟩
  rw [actualUniformMass_eq]
  exact hsuccess

end Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
