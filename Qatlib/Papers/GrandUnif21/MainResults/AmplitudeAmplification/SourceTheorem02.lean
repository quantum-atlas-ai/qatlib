/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.QSVT
import Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

set_option backward.isDefEq.respectTransparency false

/-!
# GrandUnif21 Theorem 2 — Amplitude amplification

Source: arXiv:2105.02859v3, Sec. II B, Theorem 2 and Eq. (13) (metadata lines
197--207).  Given a unitary `U` together with phase operators
`A_φ = e^{iφ|A₀⟩⟨A₀|}`, `B_φ = e^{iφ|B₀⟩⟨B₀|}` on the two Bloch spheres of the
problem, the amplitude element

`⟨A₀| A_{φ₀} ∏_k U B_{φ_{2k-1}} U† A_{φ_{2k}} U |B₀⟩`

is a polynomial `Poly(a)` in `a = ⟨A₀|U|B₀⟩` of degree at most `d` (odd) which
obeys conditions (i)--(iii) of Theorem 1.

The Lean model below is the paper's own two-dimensional Bloch reduction (its
Eqs. (11)--(12) and the surrounding discussion): the workspace is `Fin 2`, the
states `|A₀⟩` and `|B₀⟩` are the same frame vector `e₀`, the phase operators
are `phaseRotation (e₀ e₀ᴴ)` (the library's convention for
`e^{iφ|A₀⟩⟨A₀|}`, see Appendix A of the paper on signal-basis conventions), and
the paper's observation that `U = U†` on these two-dimensional subspaces is the
hypothesis `Uᴴ = U`.  The encoded amplitude is `e₀ᴴ U e₀ = a`.

The proof identifies the paper's word `∏_k [e^{iφ_k|A₀⟩⟨A₀|} · U]` with the
library alternating product `phasedAlternating` (the final frame phase of that
product is the identity and drops out against `|B₀⟩`), then applies the forward
QSVT identity
`Qatlib.Concepts.CoherentSim.CoherentOAA.qsvt_odd` at the rank-one
encoding `!![a]`, and finally reads off the Theorem 1 conditions from
`Qatlib.Papers.QSingValue19.PhaseExistence.PhaseSynthesis.completedPair_response`.

Boundary: matrix-level amplitude identity for a supplied legal phase table and
the two-dimensional Bloch model; no state preparation, no approximation of the
sign function and no query-complexity claim.
-/

set_option autoImplicit false
noncomputable section

open Matrix Polynomial
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.Execution.WorkspaceCP

namespace Qatlib.Papers.GrandUnif21.MainResults.AmplitudeAmplification

/-- The alternating word of GrandUnif21 Eq. (13): one phase rotation
`e^{iφ|A₀⟩⟨A₀|}` on the chosen frame followed by one query `U`, repeated for
every entry of the phase list. -/
noncomputable def amplitudeWord (U P : Matrix (Fin 2) (Fin 2) ℂ) : List ℂ → Matrix (Fin 2) (Fin 2) ℂ
  | [] => 1
  | z :: zs => phaseRotation P z * U * amplitudeWord U P zs

/-- The paper's alternating word is the library alternating QSVT product with
unit final phase, because `U = U†` on the two Bloch spheres (GrandUnif21
Eq. (13) and the paragraph after it). -/
theorem amplitudeWord_eq_phasedAlternating
    {U : Matrix (Fin 2) (Fin 2) ℂ} (hherm : Uᴴ = U) (P : Matrix (Fin 2) (Fin 2) ℂ)
    (zs : List ℂ) :
    amplitudeWord U P zs = phasedAlternating U P P 1 zs := by
  induction zs with
  | nil => simp [amplitudeWord, phasedAlternating, phaseRotation]
  | cons z zs ih =>
    simp only [amplitudeWord, phasedAlternating]
    rw [hherm, ih]

/-- GrandUnif21 Theorem 2, Eq. (13): for the two-dimensional Bloch model of
Eqs. (11)--(12) with encoded amplitude `a = e₀ᴴ U e₀`, `Uᴴ = U`, and any legal
phase table of odd length `d`, the amplitude element of the alternating word is
`P(a)` where `(P,Q)` is a completed polynomial pair of degree `d` satisfying the
conditions of Theorem 1. -/
theorem source_theorem2_amplitude_amplification
    {a : ℝ} {U : Matrix (Fin 2) (Fin 2) ℂ} {e0 : Matrix (Fin 2) (Fin 1) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hherm : Uᴴ = U)
    (he0 : e0ᴴ * e0 = 1) (henc : e0ᴴ * U * e0 = !![(a : ℂ)])
    {d : ℕ} (hodd : d % 2 = 1) (zs : List ℂ) (hlen : zs.length = d)
    (hzs : ∀ z ∈ zs, IsPhase z) :
    ∃ P Q : Polynomial ℂ, CompletedPair d P Q ∧
      (compress e0 (amplitudeWord U (e0 * e0ᴴ) zs) e0) 0 0 = P.eval (a : ℂ) := by
  have hphase1 : IsPhase (1 : ℂ) := by simp [IsPhase]
  have hs : zs.length % 2 = 1 := by rw [hlen]; exact hodd
  have hPE : ProjectedUnitaryEncoding (!![(a : ℂ)]) U e0 e0 :=
    ⟨hU, he0, he0, henc⟩
  have hav : (!![(a : ℂ)] : Matrix (Fin 1) (Fin 1) ℂ) * 1 = (a : ℂ) • 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  have haw : (!![(a : ℂ)] : Matrix (Fin 1) (Fin 1) ℂ)ᴴ * 1 = (a : ℂ) • 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  refine ⟨responseP 1 zs, responseQ 1 zs, ?_, ?_⟩
  · rw [← hlen]
    exact completedPair_response hphase1 zs hzs
  · have hq := qsvt_odd hPE hav haw (1 : ℂ) zs hs
    have hq' : compress e0
        (phasedAlternating U (e0 * e0ᴴ) (e0 * e0ᴴ) (1 : ℂ) zs) e0 * 1
        = (responseP 1 zs).eval (a : ℂ) • 1 := by
      simpa [rangeProjector] using hq
    rw [amplitudeWord_eq_phasedAlternating hherm]
    rw [Matrix.mul_one] at hq'
    rw [hq']
    simp

end Qatlib.Papers.GrandUnif21.MainResults.AmplitudeAmplification
