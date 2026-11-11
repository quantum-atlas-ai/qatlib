/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QsampleCoup25.MainResults.Coalescence

set_option backward.isDefEq.respectTransparency false

/-!
# Submultiplicativity of the maximal non-coalescence probability (source Lemma 17)

Temme--Wocjan, *Quantized Markov Chain Couplings that Prepare Qsamples*,
arXiv:2504.02651v2, Quantum 9, 1951 (2025). Fixed source PDF SHA-256
`616a3932dd7120d6c178df5869e910d5891e93396e55f7ccd07c11d3110cabf6`.

Source Lemma 17 (107): for any Markov chain coupling and any `ℓ ≥ 1`,

`Pr_max{τ_coal ≥ ℓ · m} ≤ Pr_max{τ_coal ≥ m}^ℓ`.

The classical proof observes that the coupling transition matrix has the block
structure `[[P, A], [0, B]]` with respect to the decomposition of `Ω × Ω` into
the diagonal and its complement (source eq. (108)): coalesced pairs never leave
the diagonal, so the `(diagonal, off-diagonal)` block of every power of `C` is
zero. The `1`-norm of the off-diagonal block `B^m` is exactly the maximal
non-coalescence probability, and the `1`-norm is submultiplicative because the
entries are nonnegative.

We formalise this without ever forming the block matrix: `PrMaxLe C m v` means
that every off-diagonal `m`-step probability is at most `v`. The theorem
`prMaxLe_pow` shows that this bound propagates to `v ^ ℓ` at time `ℓ * m`, which
is precisely the content of (107) once `v` is read as `Pr_max{τ_coal ≥ m}`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QsampleCoup25.MainResults

open Finset BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {P : Matrix Ω Ω ℝ} {π : Ω → ℝ} {C : Matrix (Ω × Ω) (Ω × Ω) ℝ}

/-- The off-diagonal mass, written as a filtered sum. -/
def offMass (C : Matrix (Ω × Ω) (Ω × Ω) ℝ) (m : ℕ) (x y : Ω) : ℝ :=
  ∑ p ∈ (Finset.univ.filter (fun p : Ω × Ω => p.1 ≠ p.2)), (C ^ m) p (x, y)

/-- The filtered and indicator forms of the off-diagonal mass agree. -/
theorem offMass_eq_notCoalesced (C : Matrix (Ω × Ω) (Ω × Ω) ℝ) (m : ℕ) (x y : Ω) :
    offMass C m x y = notCoalesced C m x y := by
  rw [offMass, notCoalesced, Finset.sum_filter]

/-- `PrMaxLe C m v` is the assertion that every off-diagonal `m`-step coupling
probability is at most `v`; it is the hypothesis `Pr_max{τ_coal ≥ m} ≤ v`. -/
def PrMaxLe (C : Matrix (Ω × Ω) (Ω × Ω) ℝ) (m : ℕ) (v : ℝ) : Prop :=
  ∀ x y : Ω, x ≠ y → notCoalesced C m x y ≤ v

/-! ## Nonnegativity of powers of a coupling matrix -/

/-- The entries of every power of a coupling matrix are nonnegative. -/
theorem coupling_pow_nonneg (hc : Coupling P C) (k : ℕ) :
    ∀ p q : Ω × Ω, 0 ≤ (C ^ k) p q := by
  induction k with
  | zero =>
      intro p q
      rw [pow_zero]
      by_cases h : p = q
      · rw [h]
        simp
      · have hz : (1 : Matrix (Ω × Ω) (Ω × Ω) ℝ) p q = 0 := by
          rw [Matrix.one_apply]
          simp [h]
        rw [hz]
  | succ k ih =>
      intro p q
      rw [pow_succ', Matrix.mul_apply]
      exact Finset.sum_nonneg fun s _ =>
        mul_nonneg (hc.nonneg p s) (ih s q)

/-! ## The diagonal is absorbing -/

/-- Once the two components have coalesced they never separate: the entry
`(C^k) p r` vanishes for `k ≥ 1`, off-diagonal `p` and diagonal `r`
(source eq. (108), the zero block of `C`). -/
theorem pow_offdiag_diag_zero (hc : Coupling P C) :
    ∀ {k : ℕ}, 0 < k → ∀ {p r : Ω × Ω},
      p.1 ≠ p.2 → r.1 = r.2 → (C ^ k) p r = 0 := by
  intro k
  induction k with
  | zero => intro hk; exact absurd hk (Nat.lt_irrefl 0)
  | succ k ih =>
      intro hk p r hp hr
      cases k with
      | zero =>
          rw [pow_one]
          have hr' : r = (r.1, r.1) := Prod.ext rfl hr.symm
          rw [hr']
          exact hc.meet_offdiag p.1 p.2 r.1 hp
      | succ j =>
          rw [pow_succ', Matrix.mul_apply]
          refine Finset.sum_eq_zero fun s _ => ?_
          by_cases hs : s.1 = s.2
          · have hs' : s = (s.1, s.1) := Prod.ext rfl hs.symm
            rw [hs', hc.meet_offdiag p.1 p.2 s.1 hp, zero_mul]
          · rw [ih (Nat.succ_pos j) hs hr, mul_zero]

/-! ## Submultiplicativity -/

/-- The key induction: an off-diagonal `m`-step bound `v ≥ 0` propagates to the
bound `v ^ ℓ` at time `ℓ * m`, for every `ℓ ≥ 1`. -/
theorem prMaxLe_pow (hc : Coupling P C) {m : ℕ} (hm : 0 < m) {v : ℝ} (hv : 0 ≤ v)
    (hP : PrMaxLe C m v) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    PrMaxLe C (ℓ * m) (v ^ ℓ) := by
  -- A local form of the induction, recorded for all positive exponents.
  have key : ∀ k : ℕ, 0 < k → ∀ x y : Ω, x ≠ y →
      notCoalesced C (k * m) x y ≤ v ^ k := by
    intro k
    induction k with
    | zero => intro hk; exact absurd hk (Nat.lt_irrefl 0)
    | succ k ih =>
        intro hk x y hxy
        cases k with
        | zero =>
            simpa [one_mul] using hP x y hxy
        | succ j =>
            -- exponent `(j + 2) * m = (j + 1) * m + m`
            have hexp : (j + 1 + 1) * m = (j + 1) * m + m := by ring
            have hpos : 0 < (j + 1) * m := Nat.mul_pos (Nat.succ_pos j) hm
            rw [hexp]
            -- expand the `m`-step factor and swap the two sums
            have hmain : notCoalesced C ((j + 1) * m + m) x y
                = ∑ r : Ω × Ω, (C ^ m) r (x, y) *
                    (∑ p ∈ (Finset.univ.filter (fun p : Ω × Ω => p.1 ≠ p.2)),
                      (C ^ ((j + 1) * m)) p r) := by
              rw [notCoalesced, ← Finset.sum_filter]
              rw [pow_add]
              simp only [Matrix.mul_apply]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun p _ => ?_
              ring
            rw [hmain]
            -- split the outer sum into diagonal and off-diagonal targets
            rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
              (fun r : Ω × Ω => r.1 ≠ r.2)]
            have hdiag : (∑ r ∈ Finset.univ.filter (fun r : Ω × Ω => ¬ r.1 ≠ r.2),
                (C ^ m) r (x, y) *
                  (∑ p ∈ (Finset.univ.filter (fun p : Ω × Ω => p.1 ≠ p.2)),
                    (C ^ ((j + 1) * m)) p r)) = 0 := by
              refine Finset.sum_eq_zero fun r hr => ?_
              have hr' : r.1 = r.2 := by
                simp only [Finset.mem_filter] at hr
                simpa using hr.2
              have hz : (∑ p ∈ (Finset.univ.filter (fun p : Ω × Ω => p.1 ≠ p.2)),
                    (C ^ ((j + 1) * m)) p r) = 0 := by
                refine Finset.sum_eq_zero fun p hp => ?_
                have hp' : p.1 ≠ p.2 := by
                  simp only [Finset.mem_filter] at hp
                  exact hp.2
                exact pow_offdiag_diag_zero hc hpos hp' hr'
              rw [hz, mul_zero]
            rw [hdiag, add_zero]
            -- off-diagonal targets: bound each inner sum by `v ^ (j + 1)`
            have hoff : (∑ r ∈ Finset.univ.filter (fun r : Ω × Ω => r.1 ≠ r.2),
                (C ^ m) r (x, y) *
                  (∑ p ∈ (Finset.univ.filter (fun p : Ω × Ω => p.1 ≠ p.2)),
                    (C ^ ((j + 1) * m)) p r))
                ≤ ∑ r ∈ Finset.univ.filter (fun r : Ω × Ω => r.1 ≠ r.2),
                    (C ^ m) r (x, y) * v ^ (j + 1) := by
              refine Finset.sum_le_sum fun r hr => ?_
              have hr' : r.1 ≠ r.2 := by
                simp only [Finset.mem_filter] at hr
                exact hr.2
              have hinner : (∑ p ∈ (Finset.univ.filter (fun p : Ω × Ω => p.1 ≠ p.2)),
                    (C ^ ((j + 1) * m)) p r) = notCoalesced C ((j + 1) * m) r.1 r.2 := by
                rw [notCoalesced, ← Finset.sum_filter]
              rw [hinner]
              exact mul_le_mul_of_nonneg_left (ih (Nat.succ_pos j) r.1 r.2 hr')
                (coupling_pow_nonneg hc m r (x, y))
            refine le_trans hoff ?_
            rw [← Finset.sum_mul]
            have hnot : (∑ p ∈ (Finset.univ.filter (fun p : Ω × Ω => p.1 ≠ p.2)),
                (C ^ m) p (x, y)) = notCoalesced C m x y :=
              offMass_eq_notCoalesced C m x y
            rw [hnot]
            calc notCoalesced C m x y * v ^ (j + 1)
                ≤ v * v ^ (j + 1) :=
                  mul_le_mul_of_nonneg_right (hP x y hxy) (pow_nonneg hv (j + 1))
              _ = v ^ (j + 2) := by rw [pow_succ]; ring
  exact key ℓ hℓ

end Qatlib.Papers.QsampleCoup25.MainResults
