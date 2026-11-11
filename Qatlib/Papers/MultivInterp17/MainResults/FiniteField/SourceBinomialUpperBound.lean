/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Chen--Childs--Hung, "Quantum algorithm for multivariate polynomial
interpolation", arXiv:1701.03990v2 (19 Jan 2018).

Claim `MultivInterp17.c010`, Corollary 3.12 (p.11):

  `r_{n,d} ≤ C(n+d-1, d-1)`.

The paper proves this by induction on `n+d`, using Lemma 3.11
(`r_{n,d} ≤ r_{n-1,d} + r_{n,d-1}`, file
`SourceReorderRecurrence.lean`) and Pascal's rule
`C(n+d-2,d-1) + C(n+d-2,d-2) = C(n+d-1,d-1)`. The boundary values
`r_{1,d} = ⌈(d+1)/2⌉ ≤ d` and `r_{n,1} = 1` are Remark 3.15
([BV97; dBCW02; CvDHS16]).

Because the paper's `r_{n,d}` is defined through the finite-field counting
condition `|R''_k| = q^J - O(q^{J-1})` (Lemma 3.11), we state the corollary in
the same abstract form in which it is used: for any family `r` that satisfies
the Lemma 3.11 recurrence and the Remark 3.15 boundary bounds, the binomial
bound holds. This is exactly the induction carried out in the paper's proof;
no additional hypothesis is introduced beyond the two inputs the paper uses.
-/
import Qatlib.Papers.MultivInterp17.MainResults.Model.InterpolationModel

/-!
# SourceBinomialUpperBound

Paper-layer definitions and source results for MultivInterp17.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.MultivInterp17.MainResults.FiniteField

open Qatlib.Papers.MultivInterp17.MainResults.Model

/-- Corollary 3.12 (p.11). For a family `r : ℕ → ℕ → ℕ` of reorder thresholds
satisfying the Lemma 3.11 recurrence `r n d ≤ r (n-1) d + r n (d-1)` for
`n, d ≥ 2` and the Remark 3.15 boundary bounds `r 1 d ≤ d`, `r n 1 ≤ 1`, the
binomial upper bound `r n d ≤ C(n+d-1, d-1)` holds for all positive `n, d`.

This is the induction of the paper's proof: the recurrence feeds Pascal's rule
`C(n+d-2,d-1) + C(n+d-2,d-2) = C(n+d-1,d-1)`. -/
theorem corollary_3_12 (r : ℕ → ℕ → ℕ)
    (hleft : ∀ d, r 1 d ≤ d)
    (hbottom : ∀ n, r n 1 ≤ 1)
    (hrec : ∀ n d, 2 ≤ n → 2 ≤ d → r n d ≤ r (n - 1) d + r n (d - 1)) :
    ∀ n d, 1 ≤ n → 1 ≤ d → r n d ≤ (n + d - 1).choose (d - 1) := by
  intro n d hn hd
  suffices h : ∀ m, ∀ n d, n + d = m → 1 ≤ n → 1 ≤ d →
      r n d ≤ (n + d - 1).choose (d - 1) from h (n + d) n d rfl hn hd
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n d hsum hn hd
    rcases eq_or_lt_of_le hn with hn1 | hn2
    · -- `n = 1`: boundary value `r 1 d ≤ d = C(d, d-1)`.
      subst hn1
      have hchoose : (1 + d - 1).choose (d - 1) = d := by
        have h1 : 1 + d - 1 = d := by omega
        rw [h1]
        have hdpos : d = (d - 1) + 1 := by omega
        calc d.choose (d - 1) = ((d - 1) + 1).choose (d - 1) := by rw [← hdpos]
          _ = (d - 1) + 1 := Nat.choose_succ_self_right (d - 1)
          _ = d := by omega
      rw [hchoose]
      exact hleft d
    rcases eq_or_lt_of_le hd with hd1 | hd2
    · -- `d = 1`: boundary value `r n 1 ≤ 1 = C(n, 0)`.
      subst hd1
      have hchoose : (n + 1 - 1).choose (1 - 1) = 1 := by
        have : n + 1 - 1 = n := by omega
        rw [this, Nat.choose_zero_right]
      rw [hchoose]
      exact hbottom n
    -- `n, d ≥ 2`: Lemma 3.11 plus the induction hypothesis.
    have hrd : r n d ≤ r (n - 1) d + r n (d - 1) := hrec n d hn2 hd2
    have ih1 : r (n - 1) d ≤ ((n - 1) + d - 1).choose (d - 1) := by
      refine ih ((n - 1) + d) ?_ (n - 1) d rfl (by omega) (by omega)
      omega
    have ih2 : r n (d - 1) ≤ (n + (d - 1) - 1).choose ((d - 1) - 1) := by
      refine ih (n + (d - 1)) ?_ n (d - 1) rfl hn (by omega)
      omega
    calc r n d ≤ r (n - 1) d + r n (d - 1) := hrd
      _ ≤ ((n - 1) + d - 1).choose (d - 1)
            + (n + (d - 1) - 1).choose ((d - 1) - 1) := Nat.add_le_add ih1 ih2
      _ = (n + d - 1).choose (d - 1) := by
        have h1 : (n - 1) + d - 1 = n + d - 2 := by omega
        have h2 : n + (d - 1) - 1 = n + d - 2 := by omega
        have h3 : (d - 1) - 1 = d - 2 := by omega
        rw [h1, h2, h3]
        have hpas := Nat.choose_succ_succ' (n + d - 2) (d - 2)
        -- `hpas : C(n+d-1, d-1) = C(n+d-2,d-2) + C(n+d-2,d-1)`.
        have e1 : n + d - 2 + 1 = n + d - 1 := by omega
        have e2 : d - 2 + 1 = d - 1 := by omega
        rw [e1, e2] at hpas
        rw [hpas, Nat.add_comm]

end Qatlib.Papers.MultivInterp17.MainResults.FiniteField
