/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# CycloSieve26 — Proposition 4: LWE and CyLWE sample equivalence

Source: Boucher–Fouque–Shen, *Cyclotomic Cosets* (arXiv:2609.34996v1),
**Proposition 4**, page 19–20, §5.1.

The proposition states that `p − 1` LWE samples with common secret `s ∈ ℤ_q^n`
combine into one CyLWE sample with the *same* secret, and conversely that one
CyLWE sample decomposes into `p − 1` LWE samples.  The paper realises the ring
`R_q = ℤ_q[ζ_p]` in the power basis `(1, ζ_p, …, ζ_p^{p−2})`, so a ring element
is exactly a `(p−1)`-tuple of `ℤ_q` coordinates (`ι : ℤ_q^{p−1} → R_q`).  Under
this identification the two directions are the coordinatewise statements that
`b' = ⟨a', s⟩ + e'` holds in every coefficient.

The final paragraph of the paper also records that the error distribution is
preserved because the discrete Gaussian weight on `R_q` factors over the power
basis.  `gaussianWeightVec_eq_prod` proves that factorisation for the real
Gaussian weight `ρ_r(x) = exp(−π‖x‖²/r²)`.

The development is coordinatewise and therefore elementary, but it is the
content the reduction relies on.
-/

set_option autoImplicit false

namespace Qatlib.Papers.CycloSieve26.MainResults

open Finset
open scoped BigOperators

variable {n p q : ℕ}

/-! ## LWE and CyLWE samples in coordinates -/

/-- The inner product `⟨a, s⟩ = ∑ i, aᵢ sᵢ` over `ℤ_q`. -/
def dot {q : ℕ} (a s : Fin n → ZMod q) : ZMod q := ∑ i, a i * s i

/-- A single search-LWE sample `(a, b)` is consistent with secret `s` and error
`e` when `b = ⟨a, s⟩ + e` (Definition 1). -/
def lweConsistent {q : ℕ} (s : Fin n → ZMod q) (e : ZMod q)
    (ab : (Fin n → ZMod q) × ZMod q) : Prop :=
  ab.2 = dot ab.1 s + e

/-- A CyLWE sample over `R_q`: the `R_q^n`-vector `a` and the `R_q`-scalar `b`,
both written in the power basis `(1, ζ_p, …, ζ_p^{p−2})`, i.e. with `p − 1`
`ℤ_q`-coordinates each (Definition 2). -/
abbrev CyLWESample (n p q : ℕ) : Type :=
  (Fin (p - 1) → Fin n → ZMod q) × (Fin (p - 1) → ZMod q)

/-- A CyLWE sample is consistent with secret `s` and error coordinates `e`
when every coefficient satisfies `bᵢ = ⟨aᵢ, s⟩ + eᵢ`. -/
def cylweConsistent {q : ℕ} (s : Fin n → ZMod q) (e : Fin (p - 1) → ZMod q)
    (ab : CyLWESample n p q) : Prop :=
  ∀ i, ab.2 i = dot (ab.1 i) s + e i

/-- The forward map of Proposition 4: `p − 1` LWE samples `(aᵢ, bᵢ)` are read
as the coefficient expansion `a' = ∑ aᵢ ζ_p^i`, `b' = ∑ bᵢ ζ_p^i`; in the power
basis the CyLWE sample is exactly the tuple of the given LWE samples. -/
def combineLWE (samples : Fin (p - 1) → (Fin n → ZMod q) × ZMod q) : CyLWESample n p q :=
  (fun i => (samples i).1, fun i => (samples i).2)

/-- The converse map of Proposition 4: a CyLWE sample decomposes into the
`p − 1` LWE samples given by its coefficient tuples. -/
def splitCyLWE (ab : CyLWESample n p q) : Fin (p - 1) → (Fin n → ZMod q) × ZMod q :=
  fun i => (ab.1 i, ab.2 i)

/-- **Proposition 4, forward direction** (paper p. 19–20):
given `p − 1` LWE samples with the common secret `s` and errors `eᵢ`, the
coefficient combination is a CyLWE sample with the same secret and the combined
error coordinates. -/
theorem prop4_forward {q : ℕ} (s : Fin n → ZMod q) (e : Fin (p - 1) → ZMod q)
    (samples : Fin (p - 1) → (Fin n → ZMod q) × ZMod q)
    (h : ∀ i, lweConsistent s (e i) (samples i)) :
    cylweConsistent s e (combineLWE samples) := by
  simpa [cylweConsistent, lweConsistent, combineLWE] using h

/-- **Proposition 4, converse direction** (paper p. 20):
the coefficient decomposition of a CyLWE sample with secret `s` and error
coordinates `e` yields `p − 1` LWE samples with the same secret and errors. -/
theorem prop4_converse {q : ℕ} (s : Fin n → ZMod q) (e : Fin (p - 1) → ZMod q)
    (ab : CyLWESample n p q) (h : cylweConsistent s e ab) :
    ∀ i, lweConsistent s (e i) (splitCyLWE ab i) := by
  intro i
  simpa [cylweConsistent, lweConsistent, splitCyLWE] using h i

/-- **Proposition 4** (paper p. 19, §5.1): the two sample families are
inter-convertible with the same secret and with the error carried
coefficientwise. -/
theorem proposition4 {q : ℕ} :
    (∀ (s : Fin n → ZMod q) (e : Fin (p - 1) → ZMod q)
        (samples : Fin (p - 1) → (Fin n → ZMod q) × ZMod q),
        (∀ i, lweConsistent s (e i) (samples i)) →
          cylweConsistent s e (combineLWE samples)) ∧
    (∀ (s : Fin n → ZMod q) (e : Fin (p - 1) → ZMod q) (ab : CyLWESample n p q),
        cylweConsistent s e ab →
          ∀ i, lweConsistent s (e i) (splitCyLWE ab i)) :=
  ⟨prop4_forward, prop4_converse⟩

/-! ## Factorisation of the Gaussian weight over the power basis -/

/-- The one-dimensional Gaussian weight `ρ_r(t) = exp(−π t²/r²)`. -/
noncomputable def gaussianWeight (r : ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(Real.pi * t ^ 2 / r ^ 2))

/-- The Gaussian weight on a coordinate vector `x ∈ ℝ^d`,
`ρ_r(x) = exp(−π ‖x‖²/r²)`. -/
noncomputable def gaussianWeightVec {d : ℕ} (r : ℝ) (x : Fin d → ℝ) : ℝ :=
  Real.exp (-(Real.pi * (∑ i, (x i) ^ 2) / r ^ 2))

/-- The Gaussian weight on `ℝ^d` **factors over coordinates**:
`ρ_r(x) = ∏ᵢ ρ_r(xᵢ)`.  This is the factorisation used in the proof of
Proposition 4 (`ραq(e') = ∏ᵢ ραq(eᵢ)`, paper p. 20). -/
theorem gaussianWeightVec_eq_prod {d : ℕ} (r : ℝ) (x : Fin d → ℝ) :
    gaussianWeightVec r x = ∏ i, gaussianWeight r (x i) := by
  unfold gaussianWeightVec gaussianWeight
  rw [← Real.exp_sum]
  congr 1
  simp only [div_eq_mul_inv, Finset.sum_neg_distrib, Finset.sum_mul, Finset.mul_sum]

end Qatlib.Papers.CycloSieve26.MainResults
