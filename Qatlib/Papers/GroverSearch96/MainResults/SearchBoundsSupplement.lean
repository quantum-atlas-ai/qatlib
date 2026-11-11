/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3QueryBoundSubgoalAfas
import Qatlib.Concepts.SearchStopping.KnownCount.SummarySearchOptimalityAfas
import Qatlib.Concepts.SearchStopping.KnownCount.Section6LowerBoundSubgoalAfas
import Qatlib.Concepts.SearchStopping.KnownCount.PreparedSearch
import Mathlib.Analysis.Real.Pi.Bounds
import Qatlib.Papers.GroverSearch96.MainResults.SearchBounds

/-!
# Grover 1996, §3 algorithm, Summary headline and §6 lower bound

Source: `quant-ph/9605043v3`, §3 (p. 3), Summary (p. 1) and §6 (p. 7).

* §3 gives the algorithm: (i) prepare the uniform superposition, (ii) repeat
  `O(√N)` times a `π` phase rotation on the marked state followed by the
  diffusion `D = W R W`, (iii) sample, succeeding with probability at least
  `1/2`. All three steps have Lean counterparts in the phase-query model.
* The Summary claims `O(√N)` steps and that the algorithm is "within a small
  constant factor of the fastest possible quantum mechanical algorithm".
* §6 quotes [BennettEtAl1997] for an `Ω(√N)` query lower bound. The paper gives neither
  a proof nor an explicit constant.

The frozen layer proves a single-target query certificate with `(π/4)√N`
queries, a matching `⌊sin(π/8)√N⌋` fixed-space lower bound (BBHT's quantitative
route), and the prepared circuit from `|0…0⟩`. The modules below state these on
the paper's `N = 2^n` register and record the constant factor
`π/(4 sin(π/8)) ≈ 2.05`. The lower bound stays inside the fixed-space query
model: the BBBV `O(T²)` sensitivity argument, adaptive/measurement strategies and
elementary-gate time are not formalized here and are not claimed.
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.GroverSearch96.MainResults

open Qatlib.Papers.GroverSearch96.MainResults

open Matrix
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.QueryWordCore.QueryMachinery

/-- Concrete one-bit instance of the section-3 query certificate.  This is a
finite source-level witness for the asymptotic search interface, not an
elementary gate-count statement. -/
theorem section3_algorithm_n1 :
    ∃ k : ℕ, (k : ℝ) ≤ Real.pi / 4 * Real.sqrt (2 : ℝ) ∧
      FixedSpaceQueryUpperBound (MarkOracle (I := Reg 1)) (fun w => {w}) (1 / 2) k := by
  simpa using section3_algorithm 1 (by norm_num)

end Qatlib.Papers.GroverSearch96.MainResults
