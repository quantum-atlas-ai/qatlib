/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.InstrumentCore.Measurement.Basic
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.CascadePrefixTransportVari

set_option backward.isDefEq.respectTransparency false

/-!
# Source Algorithms 1–2 — the cascade stages `B_i` / `A_i`

Fixed source: Ambainis, *Variable time amplitude amplification and a faster
quantum algorithm for solving systems of linear equations*, fixed preprint
**arXiv:1010.4458v2** (14 Nov 2010).  Algorithms 1 and 2 are printed on p.6
(§3.2).

Source construction:

* **Algorithm 1** (`B_i`): `B_i` is the stage algorithm obtained by running
  `Estimate(B_i, c, 1/κ, log m + 5)` (for `i < m`) and then the stage
  preparation; `B_i` outputs the stage-`i` step/outcome registers and, when its
  outcome register is `2` (not finished), passes control to stage `i+1`.
* **Algorithm 2** (`A_i`): if the estimated success probability
  `p > 1/(9m)`, set `A_i = B_i`; otherwise `A_i = Amplify(B_i, k)` for the
  smallest `k` with `1/(9m) ≤ (2k+1)²·p ≤ 1/m`.

The cascade is the word that, at stage `i`, runs `A_i` on the still-running
sector, paying `2·k_i + 1` oracle calls, and passes the surviving running
component to stage `i+1`.  The mathematical content used later:

* the cascade word is legal and its state stays normalized (stage words are
  unitary);
* the live (still-running) component is a scalar multiple of the original
  live ray — stages never create amplitude in a different running sector;
* stage time satisfies the exact recurrence
  `T_{i+1} = (2·k_i + 1)·(T_i + 2^i)` (the `2^i` is the stage-`i` preparation);
* the final good component is a scalar multiple of the original good ray.

The library proves these properties as
`Qatlib.Papers.VarTimeAmpAmp10.StopModel.cascadePrefixTransport_answer`
(the `CascadePrefixTransport` Prop).  The paper-layer theorem below states the
four clauses for explicit stages, history, initial running ket and schedule and
derives them from that result.
The success-probability bookkeeping `r_i` / `r_i'` of eq. (4) and the time
bounds of eq. (5)–(6) are the separate claims c003 (Lemma 2) and c004
(Lemma 3); this file covers the stage construction itself.
-/

open Qatlib.Foundations.InstrumentCore.Measurement
set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout
open Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Matrix
open scoped Classical

namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel

/-- Fixed arXiv:1010.4458v2, Algorithms 1–2 (printed p.6, §3.2).

For a legal stage list with a legal reached history, an initial running ket
`j₀`, and a round schedule `schedule`, the cascade word has, at every prefix
`i ≤ stages.length`:

1. a legal word with normalized state;
2. state equal to `a • (live projection of the plain stage-`i` state) + b`,
   where `b` is supported only on reached bad coordinates outside the live set;
3. the exact stage-time recurrence `T_{i+1} = (2·schedule_i + 1)·(T_i + 2^i)`;
4. a final good component parallel to the plain good ray.

This is the source's Algorithms 1–2 cascade construction. -/
theorem source_algorithms12
    (C : Type) [Fintype C] [DecidableEq C]
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (hl : GrowingVtLegal stages history)
    (j₀ : VtSpace C) (hj : j₀.1 = vtRunningFlag)
    (hs : GrowingVtSupported stages history j₀) (schedule : ℕ → ℕ) :
    (∀ i, i ≤ stages.length →
        DataVtWordLegal stages (cascadeWord schedule i) ∧
        Normalized (dataVtWordState stages history j₀ (cascadeWord schedule i)) ∧
        ∃ (a : ℂ) (b : QState (VtSpace C)),
          dataVtWordState stages history j₀ (cascadeWord schedule i) =
            a • Collapse (vtState stages i (Ket j₀)) (liveSet C) + b ∧
          (∀ p, b p ≠ 0 → p.1 = vtBadFlag ∧ p.2 ∈ history i) ∧
          Collapse b (liveSet C) = 0) ∧
    (∀ i, i < stages.length →
        dataVtWordTime (cascadeWord schedule (i + 1)) =
          (2 * schedule i + 1) * (dataVtWordTime (cascadeWord schedule i) + 2 ^ i)) ∧
    (∃ a : ℂ,
      Collapse (dataVtWordState stages history j₀ (cascadeWord schedule stages.length))
        (goodSet C) =
          a • Collapse (vtState stages stages.length (Ket j₀)) (goodSet C)) :=
  cascadePrefixTransport_answer C stages history hl j₀ hj hs schedule

end Qatlib.Papers.VarTimeAmpAmp10.StopModel
