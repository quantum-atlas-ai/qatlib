/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel.FourierData

set_option backward.isDefEq.respectTransparency false

/-!
# NoisyCircuit22 — Lemma 3 (orthogonality of Fourier coefficients)

Fixed arXiv:2211.03999v1, Lemma 3, p.10, Eq. (21).

If the circuit distribution satisfies Definition 3 (gate-set orthogonality and independence
of the gates), then for distinct Pauli paths `s ≠ s'` and every `x`,
`E_C[f(C,s,x) f(C,s',x)] = 0`.  The proof picks a two-qubit gate on which the paths differ,
uses Lemma 2 for that gate (Eq. (22)), and factorises the expectation over independent
gates.

The Lean statement formalises exactly this structure: `f` factorises over a finite index
set of gates, the circuit expectation factorises as a product of per-gate expectations
(independence), and at least one per-gate two-copy expectation vanishes (Lemma 2, with the
boundary case handled by left-invariance of the final layer).  The product then vanishes.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyCircuit22.MainResults.Fourier

open BigOperators
open scoped BigOperators
open Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel

variable {Ω Path ι : Type*}

/-- Independence of gates plus Lemma 2: if `f(·,s)` factorises over a finite family of
loc gate factors, the expectation factorises over the same family, and some gate has
vanishing two-copy expectation for `s ≠ s'`, then the Fourier coefficients of `s` and `s'`
are orthogonal. -/
theorem factorized_orthogonality [Fintype ι]
    (E : Expectation Ω) (loc : ι → Ω → Path → ℝ)
    (Elocal : ι → Expectation Ω)
    (f : Ω → Path → ℝ)
    (hfac : ∀ C s, f C s = ∏ i, loc i C s)
    (hind : ∀ (a : ι → Ω → ℝ),
      E (fun C => ∏ i, a i C) = ∏ i, Elocal i (a i))
    (hgate : ∀ s s' : Path, s ≠ s' →
      ∃ i : ι, Elocal i (fun C => loc i C s * loc i C s') = 0) :
    Orthogonality E f := by
  intro s s' hne
  have hpoint : ∀ C, f C s * f C s' = ∏ i, loc i C s * loc i C s' := by
    intro C
    rw [hfac C s, hfac C s', Finset.prod_mul_distrib]
  simp_rw [hpoint]
  rw [hind]
  obtain ⟨i, hi⟩ := hgate s s' hne
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

/-- Fixed arXiv:2211.03999v1, Lemma 3, p.10, Eq. (21): distinct Pauli paths have
orthogonal Fourier coefficients. -/
theorem source_lemma3_fourier_orthogonality [Fintype ι]
    (E : Expectation Ω) (loc : ι → Ω → Path → ℝ)
    (Elocal : ι → Expectation Ω) (f : Ω → Path → ℝ)
    (hfac : ∀ C s, f C s = ∏ i, loc i C s)
    (hind : ∀ (a : ι → Ω → ℝ),
      E (fun C => ∏ i, a i C) = ∏ i, Elocal i (a i))
    (hgate : ∀ s s' : Path, s ≠ s' →
      ∃ i : ι, Elocal i (fun C => loc i C s * loc i C s') = 0) :
    Orthogonality E f :=
  factorized_orthogonality E loc Elocal f hfac hind hgate

end Qatlib.Papers.NoisyCircuit22.MainResults.Fourier
