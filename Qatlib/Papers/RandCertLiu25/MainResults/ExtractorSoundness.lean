/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 7: extractor soundness and output-length bounds

Formalises Corollary 7 of Liu--Shaydulin--Niroula et al., *Certified randomness
using a trapped-ion quantum processor*, fixed arXiv:2503.20498v1, Corollary 7
and Eqs. III.37--III.40, p. 22.

Statement.  Let `εsou ∈ (0,1]` and suppose a `(κ, εsou)`-quantum-proof strong
extractor is used in the extraction step with

  `κ = Q_min(n-1) - log(1/εsou) - 2`.     (III.38)

Then the protocol is `εsou`-sound.  If a two-universal (Toeplitz) extractor is
used, soundness holds whenever

  `ℓ ≤ Q_min(n-1) - 3 log(1/εsou) - 2`;     (III.39)

for a Trevisan extractor, whenever

  `ℓ ≤ Q_min(n-1) - 5 log(1/εsou) - 4 log ℓ - 8`.     (III.40)

We formalise:

* the soundness step: Theorem 3 with `εs = εsou/4` gives
  `Hmin ≥ κ`, and the extractor definition (III.37) then bounds the trace
  distance by `ε_ext/2 + 2εs = εsou`;
* the two output-length arithmetic chains (III.39) and (III.40), which are
  pure real arithmetic from `κ` in (III.38) and the extractor lemmas 5/6.

The trace distance and extractor are real-valued abstractions (`dist`,
`hExtractor`); the arithmetic is proved.  The `log(1/εs) = log(4/εsou)`
bookkeeping is the explicit hypothesis `hlog`, which holds because
`log 4 ≤ 2`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.RandCertLiu25.MainResults.ExtractorSoundness

/-- The extractor input-length parameter `κ` of Eq. (III.38). -/
def kappaOf (Qmin n epsSou : ℝ) : ℝ :=
  Qmin * (n - 1) - Real.log (1 / epsSou) - 2

/-- **Corollary 7, soundness** (Eqs. III.38, III.42--III.43).  Given the
Theorem 3 entropy bound with `εs = εsou/4` and the definition (III.37) of a
`(κ, εsou)`-quantum-proof strong extractor, the protocol is `εsou`-sound. -/
theorem corollary7_soundness (Qmin n epsSou epsS epsExt kappa dist Hmin : ℝ)
    (hepsSou : 0 < epsSou) (hn : 1 ≤ n)
    (hkappa : kappa = kappaOf Qmin n epsSou)
    (hepsS : epsS = epsSou / 4)
    (hlog : Real.log (1 / epsS) ≤ Real.log (1 / epsSou) + 2)
    (hHmin : Qmin * (n - 1) - Real.log (1 / epsS) ≤ Hmin)
    (hext : epsExt = epsSou)
    (hExtractor : kappa ≤ Hmin → dist ≤ epsExt / 2 + 2 * epsS) :
    dist ≤ epsSou := by
  have hHmin' : kappa ≤ Hmin := by
    rw [hkappa]
    unfold kappaOf
    linarith
  have hd := hExtractor hHmin'
  rw [hext, hepsS] at hd
  linarith

/-- **Corollary 7, Toeplitz output length** (Eq. III.39): Lemma 5 (a
two-universal extractor with `ℓ ≤ κ - 2 log(1/εsou)`) combined with `κ` from
(III.38) gives `ℓ ≤ Q_min(n-1) - 3 log(1/εsou) - 2`. -/
theorem corollary7_toeplitz_output_length (Qmin n epsSou kappa ell : ℝ)
    (hkappa : kappa = kappaOf Qmin n epsSou)
    (hEll : ell ≤ kappa - 2 * Real.log (1 / epsSou)) :
    ell ≤ Qmin * (n - 1) - 3 * Real.log (1 / epsSou) - 2 := by
  rw [hkappa] at hEll
  unfold kappaOf at hEll
  linarith

/-- **Corollary 7, Trevisan output length** (Eq. III.40): Lemma 6 (a Trevisan
extractor with `ℓ ≤ κ - 4 log(1/εsou) - 4 log ℓ - 6`) combined with `κ` from
(III.38) gives `ℓ ≤ Q_min(n-1) - 5 log(1/εsou) - 4 log ℓ - 8`. -/
theorem corollary7_trevisan_output_length (Qmin n epsSou kappa ell : ℝ)
    (hkappa : kappa = kappaOf Qmin n epsSou)
    (hEll : ell ≤ kappa - 4 * Real.log (1 / epsSou) - 4 * Real.log ell - 6) :
    ell ≤ Qmin * (n - 1) - 5 * Real.log (1 / epsSou) - 4 * Real.log ell - 8 := by
  rw [hkappa] at hEll
  unfold kappaOf at hEll
  linarith

end Qatlib.Papers.RandCertLiu25.MainResults.ExtractorSoundness
