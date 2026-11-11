/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# QuadraticAmplitude — the two-copy quadratic amplitude map

Leyton--Osborne, *A quantum algorithm to solve nonlinear differential equations*,
fixed arXiv:0812.4423v1.

Source location: §3, equations (2), (3), (6), (7), (8), (12) and (16).

The paper encodes `n` complex amplitudes into the `(n+1)`-level state

  `|φ⟩ = (1/√2)|0⟩ + (1/√2) ∑_{j=1}^{n} z_j |j⟩`

with the convention `z_0 = 1`, so that `|φ⟩ = (1/√2) ∑_{j=0}^{n} z_j |j⟩`, and
requires `∑_{j=1}^{n} |z_j|² = 1`, i.e. `∑_{j=0}^{n} |z_j|² = 2` in the extended
index set.  Two copies give `|φ⟩|φ⟩` with amplitudes `z_k z_l / 2`.

The quadratic map is encoded by the linear operator `A` of equation (12)
whose matrix entries are the coefficient table `a^α_{kl}` of equation (6).
This module formalises the exact amplitude identity (16)

  `A |φ⟩|φ⟩ = (1/√2) |φ′⟩ |0⟩`,   `|φ′⟩ = (1/√2) ∑_α f_α(z) |α⟩`,

and the normalisation consequences behind the success probability `ε²/2`:
`‖|φ⟩|φ⟩‖ = 1` and `‖A |φ⟩|φ⟩‖² = 1/2` under the measure-preservation
assumption `∑_α |f_α(z)|² = 2` of equation (8).

Everything is finite-dimensional linear algebra over `ℂ`; no analysis or
approximation is involved in this module.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.NonlinODE08.TensorBranch

/-- The coefficient table `a α k l` of equation (6), indexed over the `n+1`
extended amplitude labels (with label `0` carrying the constant term). -/
abbrev Coeff (n : ℕ) := Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℂ

/-- The state space of the encoded amplitude vector `z`, equation (2). -/
abbrev AmpVec (n : ℕ) := Fin (n + 1) → ℂ

/-- The paper's quadratic form, equation (6): `f_α(z) = ∑_{k,l} a^α_{kl} z_k z_l`. -/
def quadForm {n : ℕ} (a : Coeff n) (z : AmpVec n) (α : Fin (n + 1)) : ℂ :=
  ∑ k : Fin (n + 1), ∑ l : Fin (n + 1), a α k l * z k * z l

/-- Two copies of the encoded state, equation (3): the tensor amplitude at
`(k,l)` is `z_k z_l / 2` because each factor carries its own `1/√2`. -/
def tensorAmp {n : ℕ} (z : AmpVec n) : Fin (n + 1) × Fin (n + 1) → ℂ :=
  fun kl => (1 / 2 : ℂ) * z kl.1 * z kl.2

/-- The linear operator `A` of equation (12), acting on the two-copy input
register: `A out inp = a^{out.1}_{inp.1,inp.2}` when the output pointer slot
`out.2` is `0`, and `0` otherwise. -/
def actA {n : ℕ} (a : Coeff n) (w : Fin (n + 1) × Fin (n + 1) → ℂ) :
    Fin (n + 1) × Fin (n + 1) → ℂ :=
  fun out =>
    if out.2 = 0 then ∑ inp : Fin (n + 1) × Fin (n + 1), a out.1 inp.1 inp.2 * w inp
    else 0

/-- The right-hand side of equation (16): the branch amplitude
`(1/2) f_α(z)` on `|α⟩|0⟩` and zero elsewhere. -/
def branchAmp {n : ℕ} (a : Coeff n) (z : AmpVec n) :
    Fin (n + 1) × Fin (n + 1) → ℂ :=
  fun out =>
    if out.2 = 0 then (1 / 2 : ℂ) * ∑ inp : Fin (n + 1) × Fin (n + 1),
      a out.1 inp.1 inp.2 * (z inp.1 * z inp.2)
    else 0

/-- Equation (16): the operator `A` applied to two copies of `|φ⟩` produces the
branch `(1/2) f_α(z) |α⟩|0⟩`, which is `(1/√2)|φ′⟩|0⟩` with
`|φ′⟩ = (1/√2) ∑_α f_α(z) |α⟩`. -/
theorem actA_tensorAmp {n : ℕ} (a : Coeff n) (z : AmpVec n) (out : Fin (n + 1) × Fin (n + 1)) :
    actA a (tensorAmp z) out = branchAmp a z out := by
  unfold actA branchAmp
  by_cases h : out.2 = 0
  · simp only [h, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro inp _
    simp only [tensorAmp]
    ring
  · simp only [h, if_false]

/-- Equation (3), normalisation: if `∑_j |z_j|² = 1` then `∑_{j≥1}`, encoded as
`∑_j |z_j|² = 2` over the extended index set, the two-copy state has norm one. -/
theorem tensorAmp_normSq_sum {n : ℕ} (z : AmpVec n)
    (hz : ∑ j : Fin (n + 1), Complex.normSq (z j) = 2) :
    ∑ kl : Fin (n + 1) × Fin (n + 1), Complex.normSq (tensorAmp z kl) = 1 := by
  have hhalf : Complex.normSq (1 / 2 : ℂ) = 1 / 4 := by
    norm_num [Complex.normSq_apply]
  have hfac : ∀ kl : Fin (n + 1) × Fin (n + 1),
      Complex.normSq (tensorAmp z kl) =
        (1 / 4) * (Complex.normSq (z kl.1) * Complex.normSq (z kl.2)) := by
    intro kl
    simp only [tensorAmp, Complex.normSq_mul, hhalf]
    ring
  calc
    ∑ kl : Fin (n + 1) × Fin (n + 1), Complex.normSq (tensorAmp z kl)
        = ∑ kl : Fin (n + 1) × Fin (n + 1),
            (1 / 4) * (Complex.normSq (z kl.1) * Complex.normSq (z kl.2)) :=
          Finset.sum_congr rfl (fun kl _ => hfac kl)
    _ = (1 / 4) * ((∑ k : Fin (n + 1), Complex.normSq (z k)) *
            (∑ l : Fin (n + 1), Complex.normSq (z l))) := by
          rw [Fintype.sum_prod_type]
          rw [Finset.sum_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum, Finset.mul_sum]
    _ = 1 := by rw [hz]; norm_num

/-- Equation (8) implies the success amplitude has squared norm `1/2`.  This is
`‖A|φ⟩|φ⟩‖² = (1/4) ∑_α |f_α(z)|² = 1/2` under measure preservation
`∑_α |f_α(z)|² = 2`. -/
theorem actA_normSq_sum {n : ℕ} (a : Coeff n) (z : AmpVec n)
    (hf : ∑ α : Fin (n + 1), Complex.normSq (quadForm a z α) = 2) :
    ∑ out : Fin (n + 1) × Fin (n + 1),
        Complex.normSq (actA a (tensorAmp z) out) = 1 / 2 := by
  have hhalf : Complex.normSq (1 / 2 : ℂ) = 1 / 4 := by
    norm_num [Complex.normSq_apply]
  -- collapse the output pointer slot: only `out.2 = 0` contributes
  have hcollapse : ∀ α : Fin (n + 1),
      (∑ β : Fin (n + 1), Complex.normSq
          (if β = 0 then (1 / 2 : ℂ) * quadForm a z α else 0))
        = Complex.normSq ((1 / 2 : ℂ) * quadForm a z α) := by
    intro α
    rw [Finset.sum_eq_single (0 : Fin (n + 1))]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h0
      exact absurd (Finset.mem_univ (0 : Fin (n + 1))) h0
  calc
    ∑ out : Fin (n + 1) × Fin (n + 1),
        Complex.normSq (actA a (tensorAmp z) out)
        = ∑ out : Fin (n + 1) × Fin (n + 1), Complex.normSq (branchAmp a z out) := by
          refine Finset.sum_congr rfl (fun out _ => ?_)
          rw [actA_tensorAmp]
    _ = ∑ α : Fin (n + 1), ∑ β : Fin (n + 1), Complex.normSq
          (if β = 0 then (1 / 2 : ℂ) * quadForm a z α else 0) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl (fun α _ => ?_)
          refine Finset.sum_congr rfl (fun β _ => ?_)
          simp only [branchAmp]
          have hsum : (∑ x : Fin (n + 1) × Fin (n + 1),
              a α x.1 x.2 * (z x.1 * z x.2)) = quadForm a z α := by
            simp only [quadForm]
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro l _
            show a α k l * (z k * z l) = a α k l * z k * z l
            ring
          rw [hsum]
    _ = ∑ α : Fin (n + 1), Complex.normSq ((1 / 2 : ℂ) * quadForm a z α) :=
          Finset.sum_congr rfl (fun α _ => hcollapse α)
    _ = ∑ α : Fin (n + 1), (1 / 4) * Complex.normSq (quadForm a z α) := by
          refine Finset.sum_congr rfl (fun α _ => ?_)
          simp only [Complex.normSq_mul, hhalf]
    _ = (1 / 4) * ∑ α : Fin (n + 1), Complex.normSq (quadForm a z α) := by
          rw [Finset.mul_sum]
    _ = 1 / 2 := by rw [hf]; norm_num

/-- The pointer-`1` branch after a time `ε`, i.e. `ε • A|φ⟩|φ⟩`, has squared norm
`ε²/2`.  This is the paper's postselection success probability at leading order. -/
theorem eps_branch_normSq_sum {n : ℕ} (a : Coeff n) (z : AmpVec n) (ε : ℝ)
    (hf : ∑ α : Fin (n + 1), Complex.normSq (quadForm a z α) = 2) :
    ∑ out : Fin (n + 1) × Fin (n + 1),
        Complex.normSq (((ε : ℝ) : ℂ) * actA a (tensorAmp z) out) = ε ^ 2 / 2 := by
  have hbase := actA_normSq_sum a z hf
  have hfac : ∀ out : Fin (n + 1) × Fin (n + 1),
      Complex.normSq (((ε : ℝ) : ℂ) * actA a (tensorAmp z) out)
        = ε ^ 2 * Complex.normSq (actA a (tensorAmp z) out) := by
    intro out
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  calc
    ∑ out : Fin (n + 1) × Fin (n + 1),
        Complex.normSq (((ε : ℝ) : ℂ) * actA a (tensorAmp z) out)
        = ∑ out : Fin (n + 1) × Fin (n + 1),
            ε ^ 2 * Complex.normSq (actA a (tensorAmp z) out) :=
          Finset.sum_congr rfl (fun out _ => hfac out)
    _ = ε ^ 2 * ∑ out : Fin (n + 1) × Fin (n + 1),
            Complex.normSq (actA a (tensorAmp z) out) := by rw [Finset.mul_sum]
    _ = ε ^ 2 / 2 := by rw [hbase]; ring

end Qatlib.Papers.NonlinODE08.TensorBranch
