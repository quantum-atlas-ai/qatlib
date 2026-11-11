/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

/-!
# Max-E3LIN2 instance model (source §I–§II)

Farhi–Goldstone–Gutmann, *A Quantum Approximate Optimization Algorithm Applied
to a Bounded Occurrence Constraint Problem*, fixed arXiv:1412.6062v2 (25 Jun 2015),
PDF at `prove/assets/1412.6062.pdf`.

This file fixes the paper's combinatorial object: an instance of Max-E3LIN2 on
`n` bits with `m` equations, at most one equation per ordered triple `a < b < c`,
each equation a sign `d_abc ∈ {−1,+1}` (paper (5)–(6)); the objective value of a
string is `(1/2) Σ_abc d_abc z_a z_b z_c` (paper (6)), and the number of satisfied
equations is `#sat`.

Boundary: this models the *instance* and the objective function only; the QAOA
state and the spectral computation are in `QaoaObjective`.
-/

namespace Qatlib.Papers.QAOABddOcc14.MainResults

open Matrix

/-- An ordered triple `a < b < c` of distinct bits, indexing one Max-E3LIN2 clause. -/
def Triple (n : ℕ) := {p : Fin n × Fin n × Fin n // p.1 < p.2.1 ∧ p.2.1 < p.2.2}

instance (n : ℕ) : Fintype (Triple n) := by
  unfold Triple; infer_instance

instance (n : ℕ) : DecidableEq (Triple n) := by
  unfold Triple; infer_instance

/-- First bit of an ordered triple. -/
def Triple.first {n : ℕ} (p : Triple n) : Fin n := p.1.1
/-- Second bit of an ordered triple. -/
def Triple.second {n : ℕ} (p : Triple n) : Fin n := p.1.2.1
/-- Third bit of an ordered triple. -/
def Triple.third {n : ℕ} (p : Triple n) : Fin n := p.1.2.2

/-- The `Z`-eigenvalue `±1` of a single bit.  `false ↦ +1`, `true ↦ −1`. -/
def bitSign {n : ℕ} (z : Fin n → Bool) (a : Fin n) : ℤ := if z a then -1 else 1

/-- Bit Sign eq one or neg one: the paper model identity or bound. -/
theorem bitSign_eq_one_or_neg_one {n : ℕ} (z : Fin n → Bool) (a : Fin n) :
    bitSign z a = 1 ∨ bitSign z a = -1 := by
  unfold bitSign; split <;> simp

/-- A Max-E3LIN2 instance: a sign coefficient on each ordered triple, with
`d_abc = 0` meaning "no equation" and `d_abc = ±1` meaning the equation is
`x_a + x_b + x_c ≡ 0` resp. `≡ 1` (mod 2).  Paper (5)–(6). -/
structure E3Instance (n : ℕ) where
  /-- The coefficient `d_abc`, taking values in `{−1,0,+1}`. -/
  d : Triple n → ℤ
  /-- Every coefficient is `−1`, `0` or `+1`. -/
  dval : ∀ p, d p = -1 ∨ d p = 0 ∨ d p = 1

namespace E3Instance

variable {n : ℕ} (I : E3Instance n)

/-- The number of equations `m` of the instance (paper §I: "an instance of
E3LIN2 with `m` equations"). -/
def numEquations : ℕ := (Finset.univ.filter (fun p => I.d p ≠ 0)).card

/-- The `Z`-product `z_a z_b z_c` of a clause, as an integer in `{±1}`. -/
def clauseSign (z : Fin n → Bool) (p : Triple n) : ℤ :=
  bitSign z p.first * bitSign z p.second * bitSign z p.third

/-- Clause `p` is satisfied by `z` when its equation holds, i.e. when
`d_abc · z_a z_b z_c = +1`; this is the indicator of the `(1/2)(1 + d ZZZ)`
objective term of paper (5). -/
def ClauseSat (z : Fin n → Bool) (p : Triple n) : Prop :=
  I.d p ≠ 0 ∧ clauseSign z p * I.d p = 1

instance (z : Fin n → Bool) (p : Triple n) : Decidable (I.ClauseSat z p) := by
  unfold ClauseSat; infer_instance

/-- Number of equations satisfied by the string `z`. -/
def satisfiedCount (z : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun p => I.ClauseSat z p)).card

/-- The objective *value* `C(z)` of paper (6): `(1/2) Σ_abc d_abc z_a z_b z_c`,
with the `1/2` additive offset of (5) dropped. -/
def objectiveValue (z : Fin n → Bool) : ℝ :=
  (1 / 2) * ∑ p : Triple n,
    (I.d p : ℝ) * (bitSign z p.first : ℝ) * (bitSign z p.second : ℝ) *
      (bitSign z p.third : ℝ)

/-- The bounded-occurrence hypothesis of §II: every bit is in no more than
`D + 1` equations (the `D+1` of paper §I). -/
def BoundedOccurrence (D : ℕ) : Prop :=
  ∀ a : Fin n,
    (Finset.univ.filter
        (fun p : Triple n =>
          I.d p ≠ 0 ∧ (a = p.first ∨ a = p.second ∨ a = p.third))).card ≤ D + 1

/-- Coarse bounded-occurrence: every bit occurs in at most `D + 1` equations,
expressed through the total number of incident clauses. -/
theorem boundedOccurrence_incident_le {D : ℕ} (h : I.BoundedOccurrence D) (a : Fin n) :
    (Finset.univ.filter
        (fun p : Triple n =>
          I.d p ≠ 0 ∧ (a = p.first ∨ a = p.second ∨ a = p.third))).card ≤ D + 1 :=
  h a

/-- The `Z`-product `z_a z_b z_c` is `±1`. -/
theorem clauseSign_eq_one_or_neg_one (z : Fin n → Bool) (p : Triple n) :
    clauseSign z p = 1 ∨ clauseSign z p = -1 := by
  unfold clauseSign
  have h1 := bitSign_eq_one_or_neg_one z p.first
  have h2 := bitSign_eq_one_or_neg_one z p.second
  have h3 := bitSign_eq_one_or_neg_one z p.third
  rcases h1 with a | a <;> rcases h2 with b | b <;> rcases h3 with c | c <;>
    simp [a, b, c]

/-- Per-clause arithmetic behind the identity `C(z) = #sat − m/2`:
`d · z_a z_b z_c = 2·[sat] − [d ≠ 0]`. -/
theorem clause_term_eq (z : Fin n → Bool) (p : Triple n) :
    (I.d p : ℝ) * (bitSign z p.first : ℝ) * (bitSign z p.second : ℝ) *
        (bitSign z p.third : ℝ) =
      2 * (if I.ClauseSat z p then (1 : ℝ) else 0) - (if I.d p ≠ 0 then (1 : ℝ) else 0) := by
  have hprod : (bitSign z p.first : ℝ) * (bitSign z p.second : ℝ) * (bitSign z p.third : ℝ)
      = (clauseSign z p : ℝ) := by unfold clauseSign; push_cast; ring
  have hcs := clauseSign_eq_one_or_neg_one z p
  have hcalc : (I.d p : ℝ) * (bitSign z p.first : ℝ) * (bitSign z p.second : ℝ) *
      (bitSign z p.third : ℝ) = (I.d p : ℝ) * (clauseSign z p : ℝ) := by
    rw [← hprod]; ring
  rw [hcalc]
  rcases I.dval p with hd | hd | hd
  · -- d = -1
    rcases hcs with hc | hc
    · have hsat : ¬ I.ClauseSat z p := by
        intro h; rcases h with ⟨-, h2⟩; rw [hc, hd] at h2; omega
      simp [hsat, hd, hc]
    · have hsat : I.ClauseSat z p := by
        refine ⟨?_, ?_⟩
        · rw [hd]; norm_num
        · rw [hc, hd]; norm_num
      simp [hsat, hd, hc]; norm_num
  · -- d = 0
    have hsat : ¬ I.ClauseSat z p := by intro h; exact h.1 hd
    simp [hsat, hd]
  · -- d = 1
    rcases hcs with hc | hc
    · have hsat : I.ClauseSat z p := by
        refine ⟨?_, ?_⟩
        · rw [hd]; norm_num
        · rw [hc, hd]; norm_num
      simp [hsat, hd, hc]; norm_num
    · have hsat : ¬ I.ClauseSat z p := by
        intro h; rcases h with ⟨-, h2⟩; rw [hc, hd] at h2; omega
      simp [hsat, hd, hc]

/-- **The objective value is `#sat − m/2`.**  This is the elementary identity used
throughout §II: the expected number of satisfied equations is `m/2` plus the
expectation (7) of the objective operator. -/
theorem objectiveValue_eq (z : Fin n → Bool) :
    I.objectiveValue z = (I.satisfiedCount z : ℝ) - (I.numEquations : ℝ) / 2 := by
  unfold objectiveValue satisfiedCount numEquations
  rw [Finset.mul_sum]
  have hstep : ∀ p : Triple n,
      (1 / 2 : ℝ) * ((I.d p : ℝ) * (bitSign z p.first : ℝ) * (bitSign z p.second : ℝ) *
        (bitSign z p.third : ℝ))
      = (if I.ClauseSat z p then (1 : ℝ) else 0) - (1 / 2) * (if I.d p ≠ 0 then (1 : ℝ) else 0) := by
    intro p
    have h := I.clause_term_eq z p
    calc
      (1 / 2 : ℝ) * ((I.d p : ℝ) * (bitSign z p.first : ℝ) * (bitSign z p.second : ℝ) *
          (bitSign z p.third : ℝ))
          = (1 / 2) * (2 * (if I.ClauseSat z p then (1 : ℝ) else 0) -
              (if I.d p ≠ 0 then (1 : ℝ) else 0)) := by rw [h]
      _ = (if I.ClauseSat z p then (1 : ℝ) else 0) -
              (1 / 2) * (if I.d p ≠ 0 then (1 : ℝ) else 0) := by ring
  have hcardSat : (I.satisfiedCount z : ℝ) =
      ∑ p : Triple n, if I.ClauseSat z p then (1 : ℝ) else 0 := by
    rw [satisfiedCount, Finset.card_filter]
    push_cast
    rfl
  have hcardEq : (I.numEquations : ℝ) =
      ∑ p : Triple n, if I.d p ≠ 0 then (1 : ℝ) else 0 := by
    rw [numEquations, Finset.card_filter]
    push_cast
    rfl
  calc
    ∑ p : Triple n,
        (1 / 2 : ℝ) * ((I.d p : ℝ) * (bitSign z p.first : ℝ) * (bitSign z p.second : ℝ) *
          (bitSign z p.third : ℝ))
        = ∑ p : Triple n,
            ((if I.ClauseSat z p then (1 : ℝ) else 0) -
              (1 / 2) * (if I.d p ≠ 0 then (1 : ℝ) else 0)) :=
          Finset.sum_congr rfl (fun p _ => hstep p)
    _ = (∑ p : Triple n, if I.ClauseSat z p then (1 : ℝ) else 0) -
          (1 / 2) * (∑ p : Triple n, if I.d p ≠ 0 then (1 : ℝ) else 0) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (I.satisfiedCount z : ℝ) - (I.numEquations : ℝ) / 2 := by
          rw [hcardSat, hcardEq]; ring

end E3Instance

end Qatlib.Papers.QAOABddOcc14.MainResults
