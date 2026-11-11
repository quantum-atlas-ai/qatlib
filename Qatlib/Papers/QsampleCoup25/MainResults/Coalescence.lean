/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QsampleCoup25.MainResults.EdgePreservation

set_option backward.isDefEq.respectTransparency false

/-!
# Coalescence probabilities as traces of edge Laplacians (source Lemma 15)

Temme--Wocjan, *Quantized Markov Chain Couplings that Prepare Qsamples*,
arXiv:2504.02651v2, Quantum 9, 1951 (2025). Fixed source PDF SHA-256
`616a3932dd7120d6c178df5869e910d5891e93396e55f7ccd07c11d3110cabf6`.

Source Lemma 15 (95): the probability `Pr_{x,y}{τ_coal > m}` that the two
components of the coupling have not coalesced after `m` transitions is

`tr([C*]^m(|−xy⟩⟨−xy|))`.

The proof iterates source Lemma 14 (proved in `EdgePreservation`): `C*` maps the
elementary Laplacian `|−xy⟩⟨−xy|` to the `C`-weighted sum of elementary
Laplacians, and each *edge* Laplacian (with `x' ≠ y'`) has trace one, whereas a
"Laplacian" with `x' = y'` vanishes. Iterating the identity and taking traces
therefore counts exactly the mass that remains on off-diagonal joint states,
which is `Pr_{x,y}{τ_coal > m}`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QsampleCoup25.MainResults

open Finset BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {P : Matrix Ω Ω ℝ} {π : Ω → ℝ} {C : Matrix (Ω × Ω) (Ω × Ω) ℝ}

/-! ## The off-diagonal mass -/

/-- The probability that the coupling started at `(x, y)` is in an off-diagonal
state after `m` steps. This is the sum of the `m`-step coupling probabilities
over all off-diagonal target states (source Remark 3, eq. (18)). -/
def notCoalesced (C : Matrix (Ω × Ω) (Ω × Ω) ℝ) (m : ℕ) (x y : Ω) : ℝ :=
  ∑ p : Ω × Ω, if p.1 ≠ p.2 then (C ^ m) p (x, y) else 0

/-- The `m`-fold iterated matricization `[C*]^m`. -/
def cStarIter (C : Matrix (Ω × Ω) (Ω × Ω) ℝ) (m : ℕ) :
    Matrix Ω Ω ℝ → Matrix Ω Ω ℝ :=
  Nat.rec (fun M => M) (fun _ f M => cStar C (f M)) m

omit [DecidableEq Ω] in
/-- The zeroth iterate of the matricization is the identity map. -/
@[simp]
theorem cStarIter_zero (C : Matrix (Ω × Ω) (Ω × Ω) ℝ) (M : Matrix Ω Ω ℝ) :
    cStarIter C 0 M = M := rfl

omit [DecidableEq Ω] in
/-- The `(m+1)`-st iterate is the matricization of the `m`-th iterate. -/
@[simp]
theorem cStarIter_succ (C : Matrix (Ω × Ω) (Ω × Ω) ℝ) (m : ℕ) (M : Matrix Ω Ω ℝ) :
    cStarIter C (m + 1) M = cStar C (cStarIter C m M) := rfl

/-! ## Linearity of the matricization -/

omit [DecidableEq Ω] in
/-- The matricization of the zero matrix is zero. -/
theorem cStar_zero (C : Matrix (Ω × Ω) (Ω × Ω) ℝ) :
    cStar C (0 : Matrix Ω Ω ℝ) = 0 := by
  funext x' y'
  simp [cStar]

omit [DecidableEq Ω] in
/-- The matricization is additive. -/
theorem cStar_add (C : Matrix (Ω × Ω) (Ω × Ω) ℝ) (A B : Matrix Ω Ω ℝ) :
    cStar C (A + B) = cStar C A + cStar C B := by
  funext x' y'
  simp only [cStar, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

omit [DecidableEq Ω] in
/-- The matricization is homogeneous over the reals. -/
theorem cStar_smul (C : Matrix (Ω × Ω) (Ω × Ω) ℝ) (a : ℝ) (A : Matrix Ω Ω ℝ) :
    cStar C (a • A) = a • cStar C A := by
  funext x' y'
  simp only [cStar, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

omit [DecidableEq Ω] in
/-- The matricization of a finite sum is the finite sum of the matricizations. -/
theorem cStar_sum {ι : Type*} (C : Matrix (Ω × Ω) (Ω × Ω) ℝ) (s : Finset ι)
    (g : ι → Matrix Ω Ω ℝ) :
    cStar C (∑ i ∈ s, g i) = ∑ i ∈ s, cStar C (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [cStar_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, cStar_add, ih]

/-! ## Elementary Laplacians with equal endpoints vanish; edge ones have trace one -/

omit [Fintype Ω] in
/-- The elementary Laplacian of the degenerate edge `(x, x)` vanishes. -/
theorem edgeProj_self (x : Ω) : edgeProj x x = 0 := by
  funext a b
  simp [edgeProj]

/-- The trace of the elementary Laplacian `|−xy⟩⟨−xy|` is `1` for `x ≠ y` and
`0` for `x = y` (source Lemma 15, "the trace of each edge Laplacian is one"). -/
theorem trace_edgeProj (x y : Ω) :
    (edgeProj x y).trace = if x = y then 0 else 1 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  by_cases h : x = y
  · subst h
    simp [edgeProj]
  · have hsq_x : (∑ a : Ω, eVec x a * eVec x a) = 1 := by
      rw [Finset.sum_eq_single x]
      · simp [eVec]
      · intro a _ ha
        simp [eVec, ha]
      · intro hx
        exact absurd (Finset.mem_univ x) hx
    have hcross : (∑ a : Ω, eVec x a * eVec y a) = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      by_cases hax : a = x
      · have hxa : eVec x a = 1 := by simp [eVec, hax]
        have hya : eVec y a = 0 := by
          have hay : a ≠ y := fun hh => h (hax.symm.trans hh)
          simp [eVec, hay]
        rw [hxa, hya, mul_zero]
      · have hxa : eVec x a = 0 := by simp [eVec, hax]
        rw [hxa, zero_mul]
    have hsq_y : (∑ a : Ω, eVec y a * eVec y a) = 1 := by
      rw [Finset.sum_eq_single y]
      · simp [eVec]
      · intro a _ ha
        simp [eVec, ha]
      · intro hy
        exact absurd (Finset.mem_univ y) hy
    have hexp : (∑ a : Ω, (eVec x a - eVec y a) * (eVec x a - eVec y a))
        = (∑ a : Ω, eVec x a * eVec x a) - 2 * (∑ a : Ω, eVec x a * eVec y a)
          + (∑ a : Ω, eVec y a * eVec y a) := by
      have hpt : ∀ a : Ω, (eVec x a - eVec y a) * (eVec x a - eVec y a)
          = (eVec x a * eVec x a) - (2 * (eVec x a * eVec y a))
            + (eVec y a * eVec y a) := by
        intro a
        ring
      rw [Finset.sum_congr rfl (fun a _ => hpt a)]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    calc (∑ a : Ω, edgeProj x y a a)
        = (1 / 2 : ℝ) * (∑ a : Ω, (eVec x a - eVec y a) * (eVec x a - eVec y a)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          simp only [edgeProj]
          ring
      _ = (1 / 2 : ℝ) * ((∑ a : Ω, eVec x a * eVec x a)
            - 2 * (∑ a : Ω, eVec x a * eVec y a)
            + (∑ a : Ω, eVec y a * eVec y a)) := by rw [hexp]
      _ = (1 / 2 : ℝ) * (1 - 2 * 0 + 1) := by rw [hsq_x, hcross, hsq_y]
      _ = if x = y then 0 else 1 := by rw [if_neg h]; norm_num

/-! ## Source Lemma 15: the iteration formula -/

/-- The iterated matricization applied to an elementary Laplacian is the
`C`-weighted sum of elementary Laplacians: the coefficient of `|−pq⟩⟨−pq|`
after `m` steps is the probability that the coupling started at `(x, y)` is at
`(p, q)`. This is the iterated form of source Lemma 14 (86). -/
theorem cStarIter_edgeProj (hc : Coupling P C) (m : ℕ) (x y : Ω) :
    cStarIter C m (edgeProj x y)
      = ∑ p : Ω × Ω,
          (if p.1 ≠ p.2 then (C ^ m) p (x, y) else 0) • edgeProj p.1 p.2 := by
  induction m with
  | zero =>
      simp only [cStarIter_zero, pow_zero]
      by_cases h : x = y
      · rw [show edgeProj x y = 0 from by rw [h, edgeProj_self]]
        refine (Finset.sum_eq_zero fun p _ => ?_).symm
        by_cases hp : p.1 ≠ p.2
        · have hpne : p ≠ (x, y) := by
            intro hh
            rw [hh] at hp
            exact hp (by rw [h])
          simp [hp, hpne]
        · simp [hp]
      · rw [Finset.sum_eq_single (x, y)]
        · simp [h]
        · intro p _ hp
          simp [hp]
        · intro hmem
          exact absurd (Finset.mem_univ (x, y)) hmem
  | succ m ih =>
      rw [cStarIter_succ, ih]
      rw [cStar_sum C Finset.univ
        (fun p : Ω × Ω => (if p.1 ≠ p.2 then (C ^ m) p (x, y) else 0) • edgeProj p.1 p.2)]
      simp only [cStar_smul, cStar_edgeProj hc]
      simp_rw [← Finset.sum_product', Finset.univ_product_univ]
      have hswap : (∑ p : Ω × Ω,
            (if p.1 ≠ p.2 then (C ^ m) p (x, y) else 0) •
              (∑ q : Ω × Ω, C q p • edgeProj q.1 q.2))
          = ∑ q : Ω × Ω, (∑ p : Ω × Ω,
              (if p.1 ≠ p.2 then (C ^ m) p (x, y) else 0) * C q p) •
              edgeProj q.1 q.2 := by
        simp_rw [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_smul]
      rw [hswap]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : q.1 ≠ q.2
      · have hzero : ∀ p : Ω × Ω, ¬ (p.1 ≠ p.2) → C q p * (C ^ m) p (x, y) = 0 := by
          intro p hp
          have hpq : p.1 = p.2 := by simpa using hp
          have hpeq : p = (p.1, p.1) := Prod.ext rfl hpq.symm
          have hc0 : C q p = 0 := by
            rw [hpeq]
            exact hc.meet_offdiag q.1 q.2 p.1 hq
          rw [hc0, zero_mul]
        have hsplit : (∑ p : Ω × Ω,
              (if p.1 ≠ p.2 then (C ^ m) p (x, y) else 0) * C q p)
            = ∑ p : Ω × Ω, C q p * (C ^ m) p (x, y) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          by_cases hp : p.1 ≠ p.2
          · simp [hp, mul_comm]
          · simp [hp, hzero p hp]
        rw [hsplit, pow_succ', Matrix.mul_apply]
        simp [hq]
      · have hqeq : q.1 = q.2 := by simpa using hq
        rw [hqeq]
        simp [edgeProj_self]

/-- Source Lemma 15 (95): the non-coalescence probability equals the trace of
the `m`-fold matricization applied to the elementary Laplacian. -/
theorem trace_cStarIter_edgeProj (hc : Coupling P C) (m : ℕ) (x y : Ω) :
    (cStarIter C m (edgeProj x y)).trace = notCoalesced C m x y := by
  rw [cStarIter_edgeProj hc, Matrix.trace_sum]
  rw [notCoalesced]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.trace_smul, trace_edgeProj]
  by_cases hp : p.1 ≠ p.2
  · simp [hp, smul_eq_mul]
  · simp [hp]

end Qatlib.Papers.QsampleCoup25.MainResults
