/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MUBCompletion26.Completion.MUB6A119Endpoint

set_option backward.isDefEq.respectTransparency false

/-!
# MUBCompletion26 — Theorem 9.3 (uniform local nonextension) and Appendix D audit

Fixed source: arXiv:2610.12180v1, Theorem 9.3 (§9.2) and Appendix D.

Theorem 9.3: for every exact unit-modulus Hadamard `H` in the `10^{-6}` closed
neighbourhood `U` of the reference matrix, the pair `(I, H/√6)` has exactly `48`
common-unbiased projective unit rays; any three of those rays (repetitions
included) contain a pair with unit representatives whose overlap modulus is
`> 1/120`; and for every `K` with `|K_{ij}| = 1` and `|(H* K)_{ij}|² = 6` one has
Gram defects `> 3/100` and `> 1/1200`, so the pair cannot extend to a third
mutually unbiased orthonormal basis or to an edge of a quartet.

The quantitative core (`1/120` separation implies Gram defect `> 1/1200`, hence
no orthonormal family of six selected rays) is already proved in the Frozen
package.  The bridge theorems below cite that development (`MUB6GraphGramGap`,
`MUB6A119Endpoint`, `MUB6A119Certificate`) instead of reproving it.  The two
closure statements — exactly 48 common rays, and that the certified 48 enclosed
rays cover every common-unbiased ray — are the paper's interval/`Krawczyk`
verification; in the Frozen development they appear as the explicit cover
hypothesis of `no_orthonormal_candidates`.  They are not re-certified here.
-/

open Matrix
open scoped Matrix BigOperators

set_option autoImplicit false

namespace Qatlib.Papers.MUBCompletion26.Completion.UniformNonextension

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UnbiasedBases.ThreeBasis
open Qatlib.Papers.MUBCompletion26.Completion
open Qatlib.Papers.MUBCompletion26.Completion.MUB6A119Certificate

/-- Theorem 9.3, `1/120` separation, transported to the frozen `1/1200` Gram gap
(arXiv:2610.12180v1, §9.2, eq. (9.8)).  For the certified enclosure `V` of the
48 common rays and any choice of six of them (with independent phases), the
squared Frobenius Gram defect exceeds `1/1200`. -/
theorem theorem_9_3_gram_gap (V : Fin 48 → QState (Fin 6))
    (hn : ∀ a, Normalized (V a)) (hV : EnclosesOverlaps V)
    (label : Fin 6 → Fin 48) (phase : Fin 6 → ℂ)
    (hp : ∀ j, Complex.normSq (phase j) = 1) :
    (1 : ℝ) / 1200 < gramDefectSquared (chosenRays V label phase) :=
  Qatlib.Papers.MUBCompletion26.Completion.enclosed_rays_gram_gap V hn hV label phase hp

/-- Theorem 9.3, non-extension part (arXiv:2610.12180v1, §9.2, (9.8)).  Six
common-unbiased rays selected from the certified enclosure with arbitrary
repetitions and phases cannot be orthonormal, so the pair `(I, H/√6)` cannot
extend to a third mutually unbiased orthonormal basis. -/
theorem theorem_9_3_nonextension (V : Fin 48 → QState (Fin 6))
    (hn : ∀ a, Normalized (V a)) (hV : EnclosesOverlaps V)
    (label : Fin 6 → Fin 48) (phase : Fin 6 → ℂ)
    (hp : ∀ j, Complex.normSq (phase j) = 1) :
    ¬ OrthonormalColumns (chosenRays V label phase) :=
  Qatlib.Papers.MUBCompletion26.Completion.no_basis_from_enclosed_rays V hn hV label phase hp

/-- Theorem 9.3, no orthonormal candidate family (arXiv:2610.12180v1, §9.2).
If the certified enclosure covers every common-unbiased ray of the pair, no six
such rays are orthonormal.  This is the form in which the paper's exact
`48`-ray enumeration enters the argument. -/
theorem theorem_9_3_no_orthonormal_candidates
    (candidate : QState (Fin 6) → Prop) (V : Fin 48 → QState (Fin 6))
    (hn : ∀ a, Normalized (V a)) (hV : EnclosesOverlaps V)
    (cover : ∀ ψ, candidate ψ → ∃ a : Fin 48, ∃ c : ℂ,
      Complex.normSq c = 1 ∧ ψ = fun i => c * V a i)
    (B : Fin 6 → QState (Fin 6)) (hc : ∀ j, candidate (B j)) :
    ¬ OrthonormalColumns B :=
  Qatlib.Papers.MUBCompletion26.Completion.no_orthonormal_candidates
    candidate V hn hV cover B hc

/-- Theorem 9.3, overlap separation (arXiv:2610.12180v1, §9.2).  Distinct
non-adjacent certified rays have overlap modulus `> 1/120`; this is the input to
the frozen sign-graph argument. -/
theorem theorem_9_3_overlap_separation (V : Fin 48 → QState (Fin 6))
    (hV : EnclosesOverlaps V) (a b : Fin 48) (hne : a ≠ b) (hno : ¬ Edge a b) :
    (1 : ℝ) / 120 < ‖Inner (V a) (V b)‖ :=
  enclosed_pair_gap V hV a b hne hno

/-! ## Appendix D: the finite candidate cover audit -/

/-- The recorded outcome of the Appendix D machine audit: the certified pair
table has `1128` ordered pairs and the sign graph has `36` edges, for the frozen
source package.  The structure records the audit's totals; the interval/Krawczyk
program semantics are not re-verified here. -/
structure CandidateAudit where
  sourceSha256 : String
  pairs : ℕ
  edges : ℕ
  pairs_eq : pairs = 1128
  edges_eq : edges = 36

/-- Appendix D audit record (arXiv:2610.12180v1, Appendix D).  There is an audit
certificate with the frozen source SHA256, `1128` pairs and `36` edges.  This is
a statement of the audit's reported finite totals, not a re-certification of the
C++/interval arithmetic. -/
theorem appendix_d_audit :
    ∃ c : CandidateAudit,
      c.sourceSha256 = "407c9a89ab2b4ddd8d7000bdc1b895814a8a806ee56edadce6c29aba4b885f06" := by
  /- Source: Appendix D and §9.3 of arXiv:2610.12180v1 (fixed official source
     package, SHA256 recorded above).

     The paper's data: 1128 ordered pairs of candidate rays and a 36-edge sign
     graph; the certified finite properties support the replay and analytic chain
     but do not certify the continuous semantics of the interval program nor the
     complete cover for every `H ∈ U`.

     Lean gap: the concrete pair/edge tables live in the Frozen modules
     `MUB6A119Data`/`MUB6A119Certificate` and are checked there by `decide`.
     This theorem records the audit result as a certificate; it does not re-run
     the machine arithmetic.
     Suggested next tactic: `exact ⟨⟨"...", 1128, 36, rfl, rfl⟩, rfl⟩`. -/
  exact ⟨⟨"407c9a89ab2b4ddd8d7000bdc1b895814a8a806ee56edadce6c29aba4b885f06",
    1128, 36, rfl, rfl⟩, rfl⟩

end Qatlib.Papers.MUBCompletion26.Completion.UniformNonextension
