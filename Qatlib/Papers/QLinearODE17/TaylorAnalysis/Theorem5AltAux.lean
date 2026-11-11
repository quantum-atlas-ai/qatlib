/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.TaylorAux
import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem6AltAux

/-!
# Explicit solution of the scalar Taylor system

The translated Taylor polynomial `taylorTransPoly` describes how forcing terms propagate between
blocks. The functions `scalarJumpTerm`, `scalarBlockVal`, and `scalarSolve` give an explicit
solution of the scalar history system.

Row identities for the initial, history, jump, and padding regions combine in
`scalarSolve_correct`. See [BerryEtAl2017ODE] for the paper's setting.

## Main statements

* `taylorTransPoly`: The translated Taylor polynomial `∑ j ∈ Icc b k, b! * z^(j-b) / j!`.
* `scalarSolve_correct`: For `m > 0`, the explicit function `scalarSolve` satisfies every row of
  the finite scalar Taylor system.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option backward.isDefEq.respectTransparency false


namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Matrix
set_option warningAsError false

/-- The translated Taylor polynomial `∑ j ∈ Icc b k, b! * z^(j-b) / j!`. -/
noncomputable def taylorTransPoly (k b : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.Icc b k, ((Nat.factorial b : ℕ) : ℂ) * z ^ (j - b) / ((Nat.factorial j : ℕ) : ℂ)

/-- The translated Taylor polynomial with `b = 0` equals `taylorPoly`. -/
theorem taylorTransPoly_zero (k : ℕ) (z : ℂ) :
    taylorTransPoly k 0 z = taylorPoly k z := by
  have hr : Finset.range (k + 1) = Finset.Icc 0 k := by
    ext i
    simp only [Finset.mem_range, Finset.mem_Icc]
    omega
  rw [taylorTransPoly, taylorPoly, hr]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

/-- The scalar Taylor-system kernel on natural-number row and column labels. -/
noncomputable def scalarKernelEntry (m k : ℕ) (lam : ℂ) : ℕ → ℕ → ℂ :=
  fun r c =>
    (if r = c then (1 : ℂ) else 0)
      - (if r < m * (k + 1) ∧ 1 ≤ r % (k + 1) ∧ c + 1 = r then
          lam / ((r % (k + 1) : ℕ) : ℂ) else 0)
      - (if r ≤ m * (k + 1) ∧ 0 < r ∧ (k + 1 : ℕ) ∣ r ∧ r - (k + 1) ≤ c ∧ c < r then
          (1 : ℂ) else 0)
      - (if m * (k + 1) < r ∧ c + 1 = r then (1 : ℂ) else 0)

/-- The effective source at a block boundary, combining its right-hand-side entry with
translated Taylor contributions from the preceding block. -/
noncomputable def scalarJumpTerm (k : ℕ) (lam : ℂ) (r : ℕ → ℂ) : ℕ → ℂ := fun s =>
  if s = 0 then r 0
  else r (s * (k + 1)) + ∑ i ∈ Finset.range k,
    taylorTransPoly k (i + 1) lam * r ((s - 1) * (k + 1) + i + 1)

/-- The scalar boundary value at block `a`, expressed as the sum of propagated jump sources. -/
noncomputable def scalarBlockVal (k : ℕ) (lam : ℂ) (r : ℕ → ℂ) (a : ℕ) : ℂ :=
  ∑ s ∈ Finset.range (a + 1), (taylorPoly k lam) ^ (a - s) * scalarJumpTerm k lam r s

/-- The explicit scalar solution on the history and padding regions, extended by zero beyond the
finite system. -/
noncomputable def scalarSolve (m k p : ℕ) (lam : ℂ) (r : ℕ → ℂ) : ℕ → ℂ := fun ℓ =>
  if ℓ < m * (k + 1) then
    (lam ^ (ℓ % (k + 1)) / ((Nat.factorial (ℓ % (k + 1)) : ℕ) : ℂ))
      * scalarBlockVal k lam r (ℓ / (k + 1))
    + ∑ t ∈ Finset.range (ℓ % (k + 1)),
        (lam ^ (ℓ % (k + 1) - t - 1) * ((Nat.factorial (t + 1) : ℕ) : ℂ)
          / ((Nat.factorial (ℓ % (k + 1)) : ℕ) : ℂ)) * r (ℓ / (k + 1) * (k + 1) + t + 1)
  else if ℓ = m * (k + 1) then scalarBlockVal k lam r m
  else if ℓ ≤ m * (k + 1) + p then
    scalarBlockVal k lam r m
      + ∑ q ∈ Finset.range (ℓ - m * (k + 1)), r (m * (k + 1) + q + 1)
  else 0

section Rows

variable (m k p : ℕ) (lam : ℂ) (x : ℕ → ℂ)

/-- The zeroth scalar row returns the zeroth coordinate of `x`. -/
theorem scalarRow_zero :
    ∑ c ∈ Finset.range (m * (k + 1) + p + 1), scalarKernelEntry m k lam 0 c * x c = x 0 := by
  have hentry : ∀ c : ℕ,
      scalarKernelEntry m k lam 0 c = if 0 = c then (1 : ℂ) else 0 := by
    intro c
    simp [scalarKernelEntry]
  have h0 : 0 ∈ Finset.range (m * (k + 1) + p + 1) := Finset.mem_range.mpr (by omega)
  rw [Finset.sum_eq_single_of_mem 0 h0]
  · rw [hentry 0]
    simp
  · intro c hc_mem hc
    rw [hentry c, if_neg (Ne.symm hc)]
    ring

/-- A positive-order history row subtracts `lam / j` times the preceding coordinate from the
current coordinate. -/
theorem scalarRow_step (a j : ℕ) (ha : a < m) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hlt : a * (k + 1) + j < m * (k + 1) + p + 1) :
    ∑ c ∈ Finset.range (m * (k + 1) + p + 1),
        scalarKernelEntry m k lam (a * (k + 1) + j) c * x c
      = x (a * (k + 1) + j) - (lam / ((j : ℕ) : ℂ)) * x (a * (k + 1) + j - 1) := by
  set ℓ := a * (k + 1) + j with hℓ
  have hmod : ℓ % (k + 1) = j := by rw [hℓ]; exact label_mod_of_le a j k hjk
  have hℓm : ℓ < m * (k + 1) := by
    have h1 : (a + 1) * (k + 1) = a * (k + 1) + (k + 1) := Nat.succ_mul a (k + 1)
    have h2 : (a + 1) * (k + 1) ≤ m * (k + 1) := by gcongr; omega
    omega
  have hentry : ∀ c : ℕ,
      scalarKernelEntry m k lam ℓ c
        = (if ℓ = c then (1 : ℂ) else 0)
          - (if c + 1 = ℓ then lam / ((j : ℕ) : ℂ) else 0) := by
    intro c
    have hs : (ℓ < m * (k + 1) ∧ 1 ≤ j ∧ c + 1 = ℓ) ↔ (c + 1 = ℓ) := by
      simp [hℓm, show 1 ≤ j by omega]
    have hj : ¬ (ℓ ≤ m * (k + 1) ∧ 0 < ℓ ∧ (k + 1 : ℕ) ∣ ℓ ∧ ℓ - (k + 1) ≤ c ∧ c < ℓ) := by
      rw [Nat.dvd_iff_mod_eq_zero, hmod]
      omega
    have hp : ¬ (m * (k + 1) < ℓ ∧ c + 1 = ℓ) := by omega
    simp only [scalarKernelEntry, hmod, hs, if_neg hj, if_neg hp, sub_zero]
  have hdiag : ∑ c ∈ Finset.range (m * (k + 1) + p + 1),
      (if ℓ = c then (1 : ℂ) else 0) * x c = x ℓ := by
    rw [Finset.sum_eq_single_of_mem ℓ (Finset.mem_range.mpr hlt)]
    · rw [if_pos rfl]
      ring
    · intro c _ hc
      rw [if_neg (Ne.symm hc)]
      ring
  have hstep : ∑ c ∈ Finset.range (m * (k + 1) + p + 1),
      (if c + 1 = ℓ then lam / ((j : ℕ) : ℂ) else 0) * x c
      = (lam / ((j : ℕ) : ℂ)) * x (ℓ - 1) := by
    rw [Finset.sum_eq_single_of_mem (ℓ - 1) (Finset.mem_range.mpr (by omega))]
    · rw [if_pos (by omega : (ℓ - 1) + 1 = ℓ)]
    · intro c _ hc
      rw [if_neg (by omega : ¬ (c + 1 = ℓ))]
      ring
  simp only [hentry, sub_mul, Finset.sum_sub_distrib]
  rw [hdiag, hstep]

/-- A block-boundary row subtracts the sum of the preceding history block from its boundary
coordinate. -/
theorem scalarRow_jump (a : ℕ) (ha1 : 1 ≤ a) (ham : a ≤ m)
    (hlt : a * (k + 1) < m * (k + 1) + p + 1) :
    ∑ c ∈ Finset.range (m * (k + 1) + p + 1),
        scalarKernelEntry m k lam (a * (k + 1)) c * x c
      = x (a * (k + 1))
        - ∑ i ∈ Finset.range (k + 1), x (a * (k + 1) - (k + 1) + i) := by
  set ℓ := a * (k + 1) with hℓ
  have hmod : ℓ % (k + 1) = 0 := by rw [hℓ]; exact Nat.mul_mod_left a (k + 1)
  have hXge : (k + 1) ≤ a * (k + 1) := Nat.le_mul_of_pos_left (k + 1) (by omega)
  have hℓm : ℓ ≤ m * (k + 1) := by rw [hℓ]; exact Nat.mul_le_mul_right (k + 1) ham
  have hentry : ∀ c : ℕ,
      scalarKernelEntry m k lam ℓ c
        = (if ℓ = c then (1 : ℂ) else 0)
          - (if ℓ - (k + 1) ≤ c ∧ c < ℓ then (1 : ℂ) else 0) := by
    intro c
    have hs : ¬ (ℓ < m * (k + 1) ∧ 1 ≤ ℓ % (k + 1) ∧ c + 1 = ℓ) := by omega
    have hj : (ℓ ≤ m * (k + 1) ∧ 0 < ℓ ∧ (k + 1 : ℕ) ∣ ℓ ∧ ℓ - (k + 1) ≤ c ∧ c < ℓ)
        ↔ (ℓ - (k + 1) ≤ c ∧ c < ℓ) := by
      simp [hℓm, show 0 < ℓ by omega, show (k + 1 : ℕ) ∣ ℓ by
        rw [hℓ, Nat.mul_comm]; exact Nat.dvd_mul_right (k + 1) a]
    have hp : ¬ (m * (k + 1) < ℓ ∧ c + 1 = ℓ) := by omega
    simp only [scalarKernelEntry]
    rw [if_neg hs, if_neg hp]
    simp only [hj, sub_zero]
  have hdiag : ∑ c ∈ Finset.range (m * (k + 1) + p + 1),
      (if ℓ = c then (1 : ℂ) else 0) * x c = x ℓ := by
    rw [Finset.sum_eq_single_of_mem ℓ (Finset.mem_range.mpr hlt)]
    · rw [if_pos rfl]
      ring
    · intro c _ hc
      rw [if_neg (Ne.symm hc)]
      ring
  have hjump : ∑ c ∈ Finset.range (m * (k + 1) + p + 1),
      (if ℓ - (k + 1) ≤ c ∧ c < ℓ then (1 : ℂ) else 0) * x c
      = ∑ i ∈ Finset.range (k + 1), x (ℓ - (k + 1) + i) := by
    have hgeo : ℓ - (k + 1) + (k + 1) = ℓ := by omega
    have hrew : ∀ c ∈ Finset.range (m * (k + 1) + p + 1),
        (if ℓ - (k + 1) ≤ c ∧ c < ℓ then (1 : ℂ) else 0) * x c
          = if ℓ - (k + 1) ≤ c ∧ c < ℓ then x c else 0 := by
      intro c _
      by_cases hwin : ℓ - (k + 1) ≤ c ∧ c < ℓ
      · rw [if_pos hwin, if_pos hwin]
        ring
      · rw [if_neg hwin, if_neg hwin]
        ring
    rw [Finset.sum_congr rfl (fun c hc => hrew c hc), ← Finset.sum_filter]
    refine Finset.sum_bij'
      (fun c _ => c - (ℓ - (k + 1)))
      (fun i _ => ℓ - (k + 1) + i)
      (fun c hc => Finset.mem_range.mpr (by
        show c - (ℓ - (k + 1)) < k + 1
        have hmem := Finset.mem_filter.mp hc
        omega))
      (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
        show ℓ - (k + 1) + i < m * (k + 1) + p + 1
        have hi1 := Finset.mem_range.mp hi
        have hd : ℓ ≤ m * (k + 1) + p := by omega
        omega),
        by show ℓ - (k + 1) ≤ ℓ - (k + 1) + i ∧ ℓ - (k + 1) + i < ℓ
           have hi1 := Finset.mem_range.mp hi
           omega⟩)
      (fun c hc => by
        show ℓ - (k + 1) + (c - (ℓ - (k + 1))) = c
        have hmem := Finset.mem_filter.mp hc
        omega)
      (fun i hi => by
        show ℓ - (k + 1) + i - (ℓ - (k + 1)) = i
        have hi1 := Finset.mem_range.mp hi
        omega)
      (fun c hc => by
        show x c = x (ℓ - (k + 1) + (c - (ℓ - (k + 1))))
        have hmem := Finset.mem_filter.mp hc
        congr 1
        omega)
  simp only [hentry, sub_mul, Finset.sum_sub_distrib]
  rw [hdiag, hjump]

/-- A positive padding row is the difference of consecutive padding coordinates. -/
theorem scalarRow_pad (q : ℕ) (hq1 : 1 ≤ q) (hqp : q ≤ p)
    (hlt : m * (k + 1) + q < m * (k + 1) + p + 1) :
    ∑ c ∈ Finset.range (m * (k + 1) + p + 1),
        scalarKernelEntry m k lam (m * (k + 1) + q) c * x c
      = x (m * (k + 1) + q) - x (m * (k + 1) + q - 1) := by
  set ℓ := m * (k + 1) + q with hℓ
  have hentry : ∀ c : ℕ,
      scalarKernelEntry m k lam ℓ c
        = (if ℓ = c then (1 : ℂ) else 0)
          - (if c + 1 = ℓ then (1 : ℂ) else 0) := by
    intro c
    have hs : ¬ (ℓ < m * (k + 1) ∧ 1 ≤ ℓ % (k + 1) ∧ c + 1 = ℓ) := by omega
    have hj : ¬ (ℓ ≤ m * (k + 1) ∧ 0 < ℓ ∧ (k + 1 : ℕ) ∣ ℓ ∧ ℓ - (k + 1) ≤ c ∧ c < ℓ) := by omega
    have hp : (m * (k + 1) < ℓ ∧ c + 1 = ℓ) ↔ (c + 1 = ℓ) := by
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨by omega, h⟩
    simp only [scalarKernelEntry]
    rw [if_neg hs, if_neg hj]
    simp only [hp, sub_zero]
  have hdiag : ∑ c ∈ Finset.range (m * (k + 1) + p + 1),
      (if ℓ = c then (1 : ℂ) else 0) * x c = x ℓ := by
    rw [Finset.sum_eq_single_of_mem ℓ (Finset.mem_range.mpr hlt)]
    · rw [if_pos rfl]
      ring
    · intro c _ hc
      rw [if_neg (Ne.symm hc)]
      ring
  have hstep : ∑ c ∈ Finset.range (m * (k + 1) + p + 1),
      (if c + 1 = ℓ then (1 : ℂ) else 0) * x c = x (ℓ - 1) := by
    rw [Finset.sum_eq_single_of_mem (ℓ - 1) (Finset.mem_range.mpr (by omega))]
    · rw [if_pos (by omega : (ℓ - 1) + 1 = ℓ)]
      ring
    · intro c _ hc
      rw [if_neg (by omega : ¬ (c + 1 = ℓ))]
      ring
  simp only [hentry, sub_mul, Finset.sum_sub_distrib]
  rw [hdiag, hstep]

end Rows

section Values

variable (m k p : ℕ) (lam : ℂ) (r : ℕ → ℂ)

/-- Successive scalar boundary values satisfy the Taylor propagation recurrence with source
`scalarJumpTerm`. -/
theorem scalarBlockVal_succ (a : ℕ) :
    scalarBlockVal k lam r (a + 1) = taylorPoly k lam * scalarBlockVal k lam r a
      + scalarJumpTerm k lam r (a + 1) := by
  rw [scalarBlockVal, Finset.sum_range_succ, scalarBlockVal]
  have hsplit : taylorPoly k lam * ∑ s ∈ Finset.range (a + 1),
      taylorPoly k lam ^ (a - s) * scalarJumpTerm k lam r s
      = ∑ s ∈ Finset.range (a + 1),
        taylorPoly k lam ^ (a + 1 - s) * scalarJumpTerm k lam r s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs1 : s ≤ a := by simpa using! hs
    have hexp : taylorPoly k lam * taylorPoly k lam ^ (a - s)
        = taylorPoly k lam ^ (a + 1 - s) := by
      rw [show a + 1 - s = (a - s) + 1 from by omega, pow_succ']
    rw [← mul_assoc, hexp]
  rw [hsplit]
  have hzero : taylorPoly k lam ^ (a + 1 - (a + 1)) = 1 := by
    rw [Nat.sub_self, pow_zero]
  rw [hzero, one_mul]

/-- For `m > 0`, the explicit scalar solution starts at `r 0`. -/
theorem scalarSolve_zero (hm : 0 < m) : scalarSolve m k p lam r 0 = r 0 := by
  have hlt : 0 < m * (k + 1) := Nat.mul_pos hm (by omega)
  have hmod : 0 % (k + 1) = 0 := Nat.zero_mod _
  have hdiv : 0 / (k + 1) = 0 := Nat.zero_div _
  simp only [scalarSolve, hlt, hmod, hdiv]
  rw [scalarBlockVal, Finset.sum_range_succ, scalarJumpTerm]
  simp

/-- Inside a history block, `scalarSolve` is the factorial-scaled propagated boundary value plus
the accumulated local source terms. -/
theorem scalarSolve_hist (a j : ℕ) (ha : a < m) (hjk : j ≤ k) :
    scalarSolve m k p lam r (a * (k + 1) + j) =
      (lam ^ j / ((Nat.factorial j : ℕ) : ℂ)) * scalarBlockVal k lam r a
      + ∑ t ∈ Finset.range j,
          (lam ^ (j - t - 1) * ((Nat.factorial (t + 1) : ℕ) : ℂ)
            / ((Nat.factorial j : ℕ) : ℂ)) * r (a * (k + 1) + t + 1) := by
  have hlt : a * (k + 1) + j < m * (k + 1) := by
    have h1 : (a + 1) * (k + 1) = a * (k + 1) + (k + 1) := Nat.succ_mul a (k + 1)
    have h2 : (a + 1) * (k + 1) ≤ m * (k + 1) := by gcongr; omega
    omega
  have hmod : (a * (k + 1) + j) % (k + 1) = j := label_mod_of_le a j k hjk
  have hdiv : (a * (k + 1) + j) / (k + 1) = a := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega : 0 < k + 1) _ _,
      Nat.div_eq_of_lt (by omega : j < k + 1), Nat.add_zero]
  simp only [scalarSolve, hlt, hmod, hdiv]
  rfl

/-- At each boundary `a ≤ m`, `scalarSolve` equals `scalarBlockVal`. -/
theorem scalarSolve_jump (a : ℕ) (ham : a ≤ m) :
    scalarSolve m k p lam r (a * (k + 1)) = scalarBlockVal k lam r a := by
  rcases Nat.lt_or_eq_of_le ham with hlt | heq
  · have h0 := scalarSolve_hist m k p lam r a 0 hlt (by omega)
    rw [show a * (k + 1) = a * (k + 1) + 0 from (Nat.add_zero _).symm, h0]
    simp
  · rw [heq]
    simp [scalarSolve]

/-- At padding offset `q`, `scalarSolve` is the final boundary value plus the sum of the first
`q` padding sources. -/
theorem scalarSolve_pad (q : ℕ) (hq1 : 1 ≤ q) (hqp : q ≤ p) :
    scalarSolve m k p lam r (m * (k + 1) + q) =
      scalarBlockVal k lam r m
      + ∑ i ∈ Finset.range q, r (m * (k + 1) + i + 1) := by
  have hnlt : ¬ (m * (k + 1) + q < m * (k + 1)) := by omega
  have hne : ¬ (m * (k + 1) + q = m * (k + 1)) := by omega
  have hle : m * (k + 1) + q ≤ m * (k + 1) + p := by omega
  simp only [scalarSolve, hnlt, hne, hle, if_false, Nat.add_sub_cancel_left]
  rfl

end Values

/-- Reorders a finite triangular double sum by summing over its lower index first. -/
theorem triangular_sum_swap (K : ℕ) : ∀ (f : ℕ → ℕ → ℂ),
    ∑ i ∈ Finset.range (K + 1), ∑ t ∈ Finset.range i, f t i
      = ∑ t ∈ Finset.range K, ∑ i ∈ Finset.Ico (t + 1) (K + 1), f t i := by
  induction K with
  | zero => intro f; simp
  | succ K ih =>
      intro f
      have hL : ∑ i ∈ Finset.range (K + 2), ∑ t ∈ Finset.range i, f t i
          = (∑ i ∈ Finset.range (K + 1), ∑ t ∈ Finset.range i, f t i)
            + ∑ t ∈ Finset.range (K + 1), f t (K + 1) := by
        rw [Finset.sum_range_succ]
      have hRinner : ∀ t ∈ Finset.range (K + 1),
          ∑ i ∈ Finset.Ico (t + 1) (K + 2), f t i
            = (∑ i ∈ Finset.Ico (t + 1) (K + 1), f t i) + f t (K + 1) := by
        intro t ht
        have hle : t + 1 ≤ K + 1 := by simpa using! ht
        have hins : Finset.Ico (t + 1) (K + 2)
            = insert (K + 1) (Finset.Ico (t + 1) (K + 1)) := by
          have h1 := Nat.Ico_succ_right_eq_insert_Ico hle
          rw [show K + 2 = (K + 1).succ from rfl]
          exact h1
        have hnmem : ¬ (K + 1 ∈ Finset.Ico (t + 1) (K + 1)) := by
          intro hcon
          have hmem := Finset.mem_Ico.mp hcon
          omega
        rw [hins, Finset.sum_insert hnmem]
        ring
      have hempty : ∑ i ∈ Finset.Ico (K + 1) (K + 1), f K i = 0 := by
        rw [Finset.Ico_self, Finset.sum_empty]
      have hR : ∑ t ∈ Finset.range (K + 1), ∑ i ∈ Finset.Ico (t + 1) (K + 2), f t i
          = (∑ t ∈ Finset.range K, ∑ i ∈ Finset.Ico (t + 1) (K + 1), f t i)
            + ∑ t ∈ Finset.range (K + 1), f t (K + 1) := by
        rw [Finset.sum_congr rfl hRinner, Finset.sum_add_distrib,
          Finset.sum_range_succ, hempty, add_zero]
      rw [hL, hR, ih f]

section Correct

/-- The sum of a history block equals the propagated preceding boundary value plus its
translated Taylor source contributions. -/
theorem scalarBlock_sum (m k p : ℕ) (lam : ℂ) (r : ℕ → ℂ) (a : ℕ) (ham1 : 1 ≤ a) (ham : a ≤ m) :
    ∑ i ∈ Finset.range (k + 1), scalarSolve m k p lam r ((a - 1) * (k + 1) + i)
      = taylorPoly k lam * scalarBlockVal k lam r (a - 1)
        + ∑ i ∈ Finset.range k, taylorTransPoly k (i + 1) lam * r ((a - 1) * (k + 1) + i + 1) := by
  have ham' : a - 1 < m := by omega
  have hval : ∀ i ∈ Finset.range (k + 1),
      scalarSolve m k p lam r ((a - 1) * (k + 1) + i)
        = (lam ^ i / ((Nat.factorial i : ℕ) : ℂ)) * scalarBlockVal k lam r (a - 1)
          + ∑ t ∈ Finset.range i,
              (lam ^ (i - t - 1) * ((Nat.factorial (t + 1) : ℕ) : ℂ)
                / ((Nat.factorial i : ℕ) : ℂ)) * r ((a - 1) * (k + 1) + t + 1) :=
    fun i hi => scalarSolve_hist m k p lam r (a - 1) i ham' (by
      have hi1 := Finset.mem_range.mp hi
      omega)
  rw [Finset.sum_congr rfl hval, Finset.sum_add_distrib,
    triangular_sum_swap k (fun t i =>
      (lam ^ (i - t - 1) * ((Nat.factorial (t + 1) : ℕ) : ℂ)
        / ((Nat.factorial i : ℕ) : ℂ)) * r ((a - 1) * (k + 1) + t + 1)),
    ← Finset.sum_mul]
  simp only [taylorPoly]
  congr 1
  · refine Finset.sum_congr rfl fun t ht => ?_
    have hIco : Finset.Ico (t + 1) (k + 1) = Finset.Icc (t + 1) k := by
      ext i
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hIco]
    simp only [taylorTransPoly, ← Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp only [Finset.mem_Icc] at hj
    field_simp
    rw [show j - t - 1 = j - (t + 1) from by omega]
    ring

/-- The boundary recurrence leaves exactly the right-hand-side entry at that boundary after
subtracting the preceding block sum. -/
theorem scalarJump_finish (k : ℕ) (lam : ℂ) (r : ℕ → ℂ) (a : ℕ) (ha1 : 1 ≤ a) :
    scalarBlockVal k lam r a - (taylorPoly k lam * scalarBlockVal k lam r (a - 1)
        + ∑ i ∈ Finset.range k, taylorTransPoly k (i + 1) lam * r ((a - 1) * (k + 1) + i + 1))
      = r (a * (k + 1)) := by
  have hsplit : scalarBlockVal k lam r a
      = taylorPoly k lam * scalarBlockVal k lam r (a - 1) + scalarJumpTerm k lam r ((a - 1) + 1) := by
    rw [show a = (a - 1) + 1 from by omega]
    exact scalarBlockVal_succ k lam r (a - 1)
  rw [hsplit]
  have hJa : scalarJumpTerm k lam r ((a - 1) + 1)
      = r (((a - 1) + 1) * (k + 1))
        + ∑ i ∈ Finset.range k,
          taylorTransPoly k (i + 1) lam * r ((a - 1) * (k + 1) + i + 1) := by
    rw [show (a - 1) + 1 = a from by omega]
    simp only [scalarJumpTerm]
    rw [if_neg (by omega : ¬ (a = 0))]
  rw [hJa, show ((a - 1) + 1) * (k + 1) = a * (k + 1) from by
    rw [show (a - 1) + 1 = a from by omega]]
  ring

/-- For `m > 0`, the explicit function `scalarSolve` satisfies every row of the finite scalar
Taylor system. -/
theorem scalarSolve_correct (m k p : ℕ) (lam : ℂ) (r : ℕ → ℂ) (hm : 0 < m) :
    ∀ ℓ, ℓ < m * (k + 1) + p + 1 →
      ∑ c ∈ Finset.range (m * (k + 1) + p + 1),
        scalarKernelEntry m k lam ℓ c * scalarSolve m k p lam r c = r ℓ := by
  intro ℓ hℓ
  by_cases h0 : ℓ = 0
  · subst h0
    rw [scalarRow_zero m k p lam (scalarSolve m k p lam r),
      scalarSolve_zero m k p lam r hm]
  by_cases hhist : ℓ < m * (k + 1)
  · have ha : ℓ / (k + 1) < m := (Nat.div_lt_iff_lt_mul (by omega)).mpr hhist
    have hjk : ℓ % (k + 1) ≤ k := Nat.lt_succ_iff.mp (Nat.mod_lt ℓ (by omega))
    by_cases hj0 : ℓ % (k + 1) = 0
    · have hdvd : (k + 1) ∣ ℓ := Nat.dvd_of_mod_eq_zero hj0
      have ha1 : 1 ≤ ℓ / (k + 1) :=
        (Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd (by omega : 0 < ℓ) hdvd)
      set a := ℓ / (k + 1) with hla
      have hla1 : ℓ = a * (k + 1) := by
        have h1 : ℓ / (k + 1) * (k + 1) + ℓ % (k + 1) = ℓ := by
          rw [Nat.mul_comm]
          exact Nat.div_add_mod ℓ (k + 1)
        rw [← hla] at h1
        omega
      rw [hla1,
        scalarRow_jump m k p lam (scalarSolve m k p lam r) a ha1 (le_of_lt ha)
          (by rw [← hla1]; exact hℓ),
        scalarSolve_jump m k p lam r a (le_of_lt ha),
        show a * (k + 1) - (k + 1) = (a - 1) * (k + 1) from by
          have h2 : (a - 1 + 1) * (k + 1) = (a - 1) * (k + 1) + (k + 1) := Nat.succ_mul _ _
          rw [show a - 1 + 1 = a from by omega] at h2
          omega,
        scalarBlock_sum m k p lam r a ha1 (le_of_lt ha),
        scalarJump_finish k lam r a ha1]
    · have hj1 : 1 ≤ ℓ % (k + 1) := by omega
      set a := ℓ / (k + 1) with hla
      set j := ℓ % (k + 1) with hlj
      have hla1 : ℓ = a * (k + 1) + j := by
        have h1 : ℓ / (k + 1) * (k + 1) + ℓ % (k + 1) = ℓ := by
          rw [Nat.mul_comm]
          exact Nat.div_add_mod ℓ (k + 1)
        rw [← hla, ← hlj] at h1
        exact h1.symm
      rw [hla1, scalarRow_step m k p lam (scalarSolve m k p lam r) a j ha hj1 hjk
        (by rw [← hla1]; exact hℓ),
        scalarSolve_hist m k p lam r a j ha hjk,
        show a * (k + 1) + j - 1 = a * (k + 1) + (j - 1) from by omega,
        scalarSolve_hist m k p lam r a (j - 1) ha (by omega)]
      have hfj : ((Nat.factorial j : ℕ) : ℂ)
          = ((Nat.factorial (j - 1) : ℕ) : ℂ) * ((j : ℕ) : ℂ) := by
        have h1 : ((Nat.factorial (j - 1 + 1) : ℕ) : ℂ)
            = ((Nat.factorial (j - 1) : ℕ) : ℂ) * (((j - 1 + 1 : ℕ) : ℂ)) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        rw [show j - 1 + 1 = j from by omega] at h1
        simpa using! h1
      have hfj0 : ((Nat.factorial j : ℕ) : ℂ) ≠ 0 := by
        exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
      have hfj10 : ((Nat.factorial (j - 1) : ℕ) : ℂ) ≠ 0 := by
        exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hlam : lam ^ j = lam * lam ^ (j - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hjc : ((j : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : (j : ℕ) ≠ 0)
      have hA : (lam / ((j : ℕ) : ℂ))
          * ((lam ^ (j - 1) / ((Nat.factorial (j - 1) : ℕ) : ℂ))
            * scalarBlockVal k lam r a)
          = (lam ^ j / ((Nat.factorial j : ℕ) : ℂ)) * scalarBlockVal k lam r a := by
        rw [hlam, hfj]
        field_simp
      have hS : (lam / ((j : ℕ) : ℂ))
          * ∑ t ∈ Finset.range (j - 1),
              (lam ^ (j - 1 - t - 1) * ((Nat.factorial (t + 1) : ℕ) : ℂ)
                / ((Nat.factorial (j - 1) : ℕ) : ℂ)) * r (a * (k + 1) + t + 1)
          = ∑ t ∈ Finset.range (j - 1),
              (lam ^ (j - t - 1) * ((Nat.factorial (t + 1) : ℕ) : ℂ)
                / ((Nat.factorial j : ℕ) : ℂ)) * r (a * (k + 1) + t + 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t ht => ?_
        have htj : t < j - 1 := Finset.mem_range.mp ht
        have hlamT : lam ^ (j - t - 1) = lam * lam ^ (j - 1 - t - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [hlamT, hfj]
        field_simp
      have hdistrib : (lam / ((j : ℕ) : ℂ))
          * ((lam ^ (j - 1) / ((Nat.factorial (j - 1) : ℕ) : ℂ)) * scalarBlockVal k lam r a
            + ∑ t ∈ Finset.range (j - 1),
                (lam ^ (j - 1 - t - 1) * ((Nat.factorial (t + 1) : ℕ) : ℂ)
                  / ((Nat.factorial (j - 1) : ℕ) : ℂ)) * r (a * (k + 1) + t + 1))
          = (lam / ((j : ℕ) : ℂ))
              * ((lam ^ (j - 1) / ((Nat.factorial (j - 1) : ℕ) : ℂ))
                * scalarBlockVal k lam r a)
            + (lam / ((j : ℕ) : ℂ)) * ∑ t ∈ Finset.range (j - 1),
                (lam ^ (j - 1 - t - 1) * ((Nat.factorial (t + 1) : ℕ) : ℂ)
                  / ((Nat.factorial (j - 1) : ℕ) : ℂ)) * r (a * (k + 1) + t + 1) := by
        exact mul_add (lam / ((j : ℕ) : ℂ)) _ _
      rw [hdistrib, hA, hS]
      have hsplit : ∑ t ∈ Finset.range j,
          (lam ^ (j - t - 1) * ((Nat.factorial (t + 1) : ℕ) : ℂ)
            / ((Nat.factorial j : ℕ) : ℂ)) * r (a * (k + 1) + t + 1)
          = ∑ t ∈ Finset.range (j - 1),
                (lam ^ (j - t - 1) * ((Nat.factorial (t + 1) : ℕ) : ℂ)
                  / ((Nat.factorial j : ℕ) : ℂ)) * r (a * (k + 1) + t + 1)
            + (lam ^ (j - (j - 1) - 1) * ((Nat.factorial j : ℕ) : ℂ)
              / ((Nat.factorial j : ℕ) : ℂ)) * r (a * (k + 1) + (j - 1) + 1) := by
        have hgen := Finset.sum_range_succ (n := j - 1)
          (f := fun t => (lam ^ (j - t - 1) * ((Nat.factorial (t + 1) : ℕ) : ℂ)
            / ((Nat.factorial j : ℕ) : ℂ)) * r (a * (k + 1) + t + 1))
        rw [show (j - 1) + 1 = j from by omega] at hgen
        exact hgen
      rw [hsplit]
      have hterm : (lam ^ (j - (j - 1) - 1) * ((Nat.factorial j : ℕ) : ℂ)
            / ((Nat.factorial j : ℕ) : ℂ)) * r (a * (k + 1) + (j - 1) + 1) = r ℓ := by
        have hzero : j - (j - 1) - 1 = 0 := by omega
        have hfj0 : ((Nat.factorial j : ℕ) : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.factorial_pos j).ne'
        rw [hzero, pow_zero, one_mul, div_self hfj0, one_mul,
          show a * (k + 1) + (j - 1) + 1 = ℓ from by omega]
      rw [hterm, hla1]
      ring
  · by_cases hlast : ℓ = m * (k + 1)
    · rw [hlast, scalarRow_jump m k p lam (scalarSolve m k p lam r) m
        (by omega) (le_refl m) (by omega), scalarSolve_jump m k p lam r m (le_refl m),
        show m * (k + 1) - (k + 1) = (m - 1) * (k + 1) from by
          have h1 : (m - 1) * (k + 1) + (k + 1) = m * (k + 1) := by
            rw [← Nat.succ_mul, show Nat.succ (m - 1) = m from by omega]
          omega,
        scalarBlock_sum m k p lam r m (by omega) (le_refl m),
        scalarJump_finish k lam r m (by omega)]
    · have hq : 1 ≤ ℓ - m * (k + 1) := by omega
      have hqp : ℓ - m * (k + 1) ≤ p := by omega
      set q := ℓ - m * (k + 1) with hlq
      have hlq1 : ℓ = m * (k + 1) + q := by omega
      rw [hlq1, scalarRow_pad m k p lam (scalarSolve m k p lam r) q hq hqp
        (by omega), scalarSolve_pad m k p lam r q hq hqp]
      by_cases hq1 : q = 1
      · rw [hq1]
        have hprev : m * (k + 1) + 1 - 1 = m * (k + 1) := by omega
        rw [hprev, scalarSolve_jump m k p lam r m (le_refl m)]
        have hsum1 : ∑ t ∈ Finset.range 1, r (m * (k + 1) + t + 1)
            = r (m * (k + 1) + 0 + 1) := by
          rw [Finset.sum_range_one]
        have hrw1 : r (m * (k + 1) + 0 + 1) = r ℓ := by
          congr 1
          omega
        rw [hsum1, hrw1]
        ring
      · have hprev : m * (k + 1) + q - 1 = m * (k + 1) + (q - 1) := by omega
        rw [hprev, scalarSolve_pad m k p lam r (q - 1) (by omega) (by omega)]
        have hgen := Finset.sum_range_succ (n := q - 1)
          (f := fun t => r (m * (k + 1) + t + 1))
        rw [show (q - 1) + 1 = q from by omega] at hgen
        have hlast : r (m * (k + 1) + (q - 1) + 1) = r ℓ := by
          congr 1
          omega
        rw [hgen]
        have key : m * (k + 1) + (q - 1) + 1 = ℓ := by omega
        have key2 : m * (k + 1) + q = ℓ := by omega
        simp only [key, key2]
        ring

end Correct

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
