/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Theorem2Afas
import Qatlib.Concepts.SearchStopping.KnownCount.Corollary21CorrectedAfas
import Qatlib.Concepts.SearchStopping.KnownCount.Corollary22Afas
import Qatlib.Concepts.SearchStopping.KnownCount.Corollary22RealRestrictedAfas
import Qatlib.Papers.GroverSearch96.MainResults.DiffusionAmplitudes

/-!
# Grover 1996, Theorem 2, Corollary 2.1 and Corollary 2.2 on the paper's register

Source: `quant-ph/9605043v3`, §5 (p. 6). The paper works on `N = 2^n` basis
states, one distinguished by `C(S) = 1` with amplitude `k` and the remaining
`N - 1` states with amplitude `l`. It states:

* Theorem 2: after diffusion the amplitudes are
  `k₂ = (2/N - 1) k + 2 (N - 1)/N l` and `l₂ = 2/N k + (N - 2)/N l`;
* Corollary 2.1: if `k < 0`, `l > 0` and `|k/l| < √N`, then both new amplitudes
  are positive;
* Corollary 2.2: `k₁² + (N - 1) l₁² = k² + (N - 1) l²`, i.e. the diffusion
  preserves the total squared mass of this two-amplitude family.

The frozen concept layer proves these statements for an arbitrary finite basis
and complex amplitudes. The paper's own register is `Reg n` with `N = 2^n`
(`card_reg`); this module states them there, in the paper's real amplitudes,
and records the physical probability-conservation reading of Corollary 2.2.

Corollary 2.1 carries the size restriction `n ≥ 3` (`N ≥ 8`): the printed proof
uses `N ≥ 9` for the second inequality, and the unqualified statement is refuted
at `N = 4` in the frozen layer. The paper's own statement omits this hypothesis,
so the bridge keeps the corrected range rather than silently strengthening it.
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.GroverSearch96.MainResults

open Qatlib.Papers.GroverSearch96.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SearchStopping.KnownCount

/-- **Corollary 2.2, normalized-state bridge.**  A real two-amplitude state on
the paper's register remains normalized after one diffusion step.  This is the
physical state-level form of the source quadratic identity, connecting the
printed `k² + (N−1)l²` conservation law to the executable `Normalized`
predicate used by the register model. -/
theorem diffusion_preserves_normalized_markedRegister (n : ℕ) (w : Reg n)
    (k l : ℝ)
    (hnorm : Normalized (MarkedVector ({w} : Finset (Reg n)) (k : ℂ) (l : ℂ))) :
    Normalized (MarkedVector ({w} : Finset (Reg n))
      (distinguishedAfter (2 ^ n) k l : ℂ)
      (ordinaryAfter (2 ^ n) k l : ℂ)) := by
  have hmass : twoAmplitudeMass (2 ^ n) k l = 1 := by
    rw [normalized_markedVector_iff] at hnorm
    rw [Finset.card_singleton, card_reg, Nat.cast_pow] at hnorm
    unfold twoAmplitudeMass
    simpa [Complex.normSq_ofReal, pow_two] using hnorm
  have hmass' := corollary2_2_markedRegister n k l
  have hafter : twoAmplitudeMass (2 ^ n)
      (distinguishedAfter (2 ^ n) k l)
      (ordinaryAfter (2 ^ n) k l) = 1 := by
    linarith
  rw [normalized_markedVector_iff]
  rw [Finset.card_singleton, card_reg, Nat.cast_pow]
  simpa [twoAmplitudeMass, Complex.normSq_ofReal, pow_two] using hafter

end Qatlib.Papers.GroverSearch96.MainResults
