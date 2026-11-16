/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MUBSixOpenAI26.CartanBridge.ArithmeticObligations
public import Qatlib.Papers.MUBSixOpenAI26.CartanBridge.LocalCertificate

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# MUBSixOpenAI26 — Theorem `execute:finite-theorem`

Source: OpenAI, *The maximum number of mutually unbiased bases in dimension six*,
fixed Git source `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`,
`execution.tex` lines 239--281 (Section 6.3, "The finite-execution implication"),
Theorem `execute:finite-theorem`, with the accompanying `seed.tex`,
`phase-cover.tex`, `refinement.tex` and `exclusion.tex` coverage propositions.

The paper's proof is a chain of coverage implications:
1. `Proposition seed:cover` (`seed.tex`): after normalizing the first basis and
   writing the second as `H/√6`, the seed coordinates of an equivalent exact
   Hadamard matrix lie in a generated seed ball; equivalences preserve
   extendibility by two further bases.
2. `Proposition phase:A-cover` (`phase-cover.tex`): every seed ball is processed
   by the A shards and places an equivalent exact solution in a coarse Record.
3. `Proposition refine:cover-preservation` / `Corollary refine:batch-cover`
   (`refinement.tex`): B mid, B fine and the emitted batches preserve the same
   exact solution into `fine.bin`.
4. `Proposition exclude:local-certificate`: a negative C result for a final
   record contradicts extendibility by two bases.
5. The initial-failure fallback and the four modulo-4 shards partition all
   remaining records without omission.

The structure `FiniteExecutionContract` records exactly this chain. Each field is
one of the paper's propositions, with its equivalence relation restricted to the
paper's normalization. `final_negative` is the output of Stage C, converted to
"no extension" by `local_exclusion_certificate`; it is *record-local*, not the
global conclusion: the nontrivial content is that the seed/A/B refinement chain
covers every possible four-basis family by a final record. The arithmetic
contract of Appendix A is carried along (`arithmetic`) exactly as the theorem's
hypotheses require.

The proof below is the paper's composition: assume a four-basis family, follow it
through seed, record and final record, and contradict the final negative result.
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UnbiasedBases.ThreeBasis
open Qatlib.Concepts.UnbiasedBases.ThreeBasis

namespace Qatlib.Papers.MUBSixOpenAI26.CartanBridge
open Qatlib.Papers.MUBSixOpenAI26.CartanBridge

/-- The paper's finite-execution certificate chain (`execution.tex` Theorem
`execute:finite-theorem` and the geometric propositions it cites), with the
Stage C output made record-local. -/
structure FiniteExecutionContract where
  /-- Type of generated seed balls (`sec:seed`). -/
  Seed : Type
  /-- Type of Stage A coarse records (`sec:phase-cover`). -/
  Record : Type
  /-- Type of final B-fine / fallback records (`sec:refinement`, `sec:execution`). -/
  Final : Type
  seeds : Set Seed
  records : Set Record
  finals : Set Final
  /-- Extendibility-preserving equivalence of an exact Hadamard with a seed. -/
  SeedEquiv : Seed → Family 4 → Prop
  /-- Extendibility-preserving equivalence with a coarse record. -/
  RecordEquiv : Record → Family 4 → Prop
  /-- Extendibility-preserving equivalence with a final record. -/
  FinalEquiv : Final → Family 4 → Prop
  /-- Appendix A arithmetic/compiler contract. -/
  arithmetic : ArithmeticCompilerObligations
  /-- `seed:cover`: every MUB family's second basis is equivalent to a seed. -/
  seed_cover : ∀ B : Family 4, IsFamily B → ∃ s ∈ seeds, SeedEquiv s B
  /-- `phase:A-cover`: every seed is covered by a coarse record. -/
  stageA_cover : ∀ s : Seed, s ∈ seeds → ∀ B : Family 4,
    SeedEquiv s B → ∃ r ∈ records, RecordEquiv r B
  /-- `refine:cover-preservation` and `refine:batch-cover`: every coarse record
  is covered by a final record. -/
  refine_cover : ∀ r : Record, r ∈ records → ∀ B : Family 4,
    RecordEquiv r B → ∃ f ∈ finals, FinalEquiv f B
  /-- Stage C negative output for every final record, converted to "no extension
  by two bases" by `exclude:local-certificate`. -/
  final_negative : ∀ f : Final, f ∈ finals →
    ¬ ∃ B : Family 4, IsFamily B ∧ FinalEquiv f B

/-- Theorem `execute:finite-theorem` (`execution.tex` lines 242--249): under the
seven source files, the arithmetic conditions of Appendix A, the terminal
conditions of Section 6.2 and the record-provenance/batch checks, four pairwise
mutually unbiased orthonormal bases in `ℂ^6` do not exist. -/
theorem finite_execution_certificate (C : FiniteExecutionContract) : NoFourMUBs := by
  intro hfour
  obtain ⟨B, hB⟩ := hfour
  obtain ⟨s, hs, hse⟩ := C.seed_cover B hB
  obtain ⟨r, hr, hre⟩ := C.stageA_cover s hs B hse
  obtain ⟨f, hf, hfe⟩ := C.refine_cover r hr B hre
  exact C.final_negative f hf ⟨B, hB, hfe⟩

end Qatlib.Papers.MUBSixOpenAI26.CartanBridge
