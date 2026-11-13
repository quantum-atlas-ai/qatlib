/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.OddApproximation
import Qatlib.Concepts.WalkSearch.Spectral.Approximation
import Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

set_option backward.isDefEq.respectTransparency false

/-!
# GrandUnif21 Theorem 4 — Singular value transformation

Source: arXiv:2105.02859v3, Sec. IV D, Theorem 4, Eqs. (43)--(47).
For a rectangular block encoding `A = Π̃ U Π` with left and
right singular frames `Π̃ = Σ_k |w_k⟩⟨w_k|` and `Π = Σ_k |v_k⟩⟨v_k|`, and a
completed QSP response polynomial `P` of degree `d`:

* `d` odd (Eqs. 44--45): the word `Π̃_{φ₁} U ∏_k Π_{φ_{2k}} U† Π̃_{φ_{2k+1}} U`
  compresses to `Poly^{(SV)}(A) = Σ_k P(σ_k) |w_k⟩⟨v_k|` between the left and
  right frames;
* `d` even (Eqs. 46--47): the word `∏_k Π_{φ_{2k-1}} U† Π̃_{φ_{2k}} U`
  compresses to `Poly^{(SV)}(A) = Σ_k P(σ_k) |v_k⟩⟨v_k|` on the right frame.

The paper-layer statements below realize the words as the library's
alternating phase products `phasedAlternating` and identify the compressed
operators with `oddSingularTransform` and `rightSingularTransform`, which are
exactly the two spectral sums of Eqs. (45) and (47), reusing

* `Qatlib.Concepts.CoherentSim.CoherentOAA.qsvt_odd_eq_oddSingularTransform`,
* `Qatlib.Concepts.WalkSearch.Spectral.qsvt_even_right_eq_rightSingularTransform`,
  and the response-polynomial interface
  `Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.completedPair_iff_response`.

Boundary: matrix-level compressed identities; no gate compilation, no
singular-vector preparation and no numerical stability claim.  The paper's
approximate encoding `(α, a, ε)` and its rescaling by `α` are not modelled;
`ProjectedUnitaryEncoding` is the exact normalized encoding.
-/

set_option autoImplicit false
noncomputable section

open Matrix Polynomial
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.Execution.WorkspaceCP

namespace Qatlib.Papers.GrandUnif21.MainResults.SingularValueTransformation

/-- GrandUnif21 Theorem 4, odd-`d` case, Eqs. (44)--(45): for a rectangular
projected encoding `A = Π̃ U Π` and a completed response pair `(P,Q)` of odd
degree `d`, there is a legal phase table of length `d` whose odd alternating
word compresses between the left and right frames to the singular-value
transform `Σ_k P(σ_k)|w_k⟩⟨v_k|` of Eq. (45). -/
theorem source_theorem4_singular_odd
    {H I O : Type*} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O]
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R)
    {d : ℕ} {P Q : Polynomial ℂ} (hpair : CompletedPair d P Q)
    (hodd : d % 2 = 1) :
    ∃ (base : ℂ) (zs : List ℂ),
      IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧ zs.length = d ∧
        compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) R =
          oddSingularTransform A (fun x => P.eval (x : ℂ)) := by
  obtain ⟨base, zs, hb, hzs, hlen, hP, _hQ⟩ := completedPair_iff_response.mp hpair
  have hs : zs.length % 2 = 1 := by rw [hlen]; exact hodd
  refine ⟨base, zs, hb, hzs, hlen, ?_⟩
  rw [qsvt_odd_eq_oddSingularTransform h base zs hs, hP]

/-- GrandUnif21 Theorem 4, even-`d` case, Eqs. (46)--(47): for a rectangular
projected encoding `A = Π̃ U Π` and a completed response pair `(P,Q)` of even
degree `d`, there is a legal phase table of length `d` whose even alternating
word (with `U†` queried first) compresses on the right frame to the
singular-value transform `Σ_k P(σ_k)|v_k⟩⟨v_k|` of Eq. (47). -/
theorem source_theorem4_singular_even
    {H I O : Type*} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O]
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R)
    {d : ℕ} {P Q : Polynomial ℂ} (hpair : CompletedPair d P Q)
    (heven : d % 2 = 0) :
    ∃ (base : ℂ) (zs : List ℂ),
      IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧ zs.length = d ∧
        compress R (phasedAlternating Uᴴ (rangeProjector L) (rangeProjector R) base zs) R =
          rightSingularTransform A (fun x => P.eval (x : ℂ)) := by
  obtain ⟨base, zs, hb, hzs, hlen, hP, _hQ⟩ := completedPair_iff_response.mp hpair
  have hs : zs.length % 2 = 0 := by rw [hlen]; exact heven
  refine ⟨base, zs, hb, hzs, hlen, ?_⟩
  rw [qsvt_even_right_eq_rightSingularTransform h base zs hs, hP]

end Qatlib.Papers.GrandUnif21.MainResults.SingularValueTransformation
