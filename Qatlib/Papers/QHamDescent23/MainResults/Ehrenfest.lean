/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QHamDescent23.MainResults.SourceModel
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Add

set_option backward.isDefEq.respectTransparency false

/-!
# Ehrenfest — Lemma 1 (arXiv:2303.01471v1, Appendix B.1)

Source: *Quantum Hamiltonian Descent*, Leng–Hickman–Li–Wu, arXiv:2303.01471v1,
PDF page 21, equation (B.9):

`d/dt ⟨Ô(t)⟩_t = ⟨dÔ/dt⟩_t + ⟨i[H(t), Ô(t)]⟩_t`.

The statement is formalised for a finite orthonormal basis (the paper's
`L²` inner product is the `ι = ℕ` limit; on the finite model every operator is
a matrix, which is the exact bounded-operator content of the derivation in
(B.10)–(B.13)). The only structural hypothesis is that the Hamiltonian is
Hermitian — that is what turns `⟨Ψ_t|H` into `⟨HΨ_t|`.
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix
open Matrix

namespace Qatlib.Papers.QHamDescent23.MainResults.Ehrenfest

open Qatlib.Papers.QHamDescent23.MainResults

variable {n : ℕ}

/-- Differentiating a constant matrix-vector product entrywise. -/
theorem hasDerivAt_mulVec_const (A : Matrix (Fin n) (Fin n) ℂ)
    {ψ : ℝ → Ket (Fin n)} {ψ' : Ket (Fin n)} {t : ℝ}
    (h : HasDerivAt ψ ψ' t) :
    HasDerivAt (fun s => A *ᵥ ψ s) (A *ᵥ ψ') t := by
  rw [hasDerivAt_pi]
  intro i
  have hsum : HasDerivAt (fun s => ∑ j, A i j * ψ s j) (∑ j, A i j * ψ' j) t :=
    HasDerivAt.fun_sum (fun j _ => (hasDerivAt_pi.mp h j).const_mul (A i j))
  simpa [mulVec, dotProduct] using hsum

/-- Product rule for a time-dependent matrix against a time-dependent vector. -/
theorem hasDerivAt_mulVec_mul (O O' : ℝ → Matrix (Fin n) (Fin n) ℂ)
    {ψ : ℝ → Ket (Fin n)} {ψ' : Ket (Fin n)} {t : ℝ}
    (hO : HasDerivAt O (O' t) t) (hψ : HasDerivAt ψ ψ' t) :
    HasDerivAt (fun s => O s *ᵥ ψ s) (O' t *ᵥ ψ t + O t *ᵥ ψ') t := by
  rw [hasDerivAt_pi]
  intro i
  have hsum : HasDerivAt (fun s => ∑ j, O s i j * ψ s j)
      (∑ j, (O' t i j * ψ t j + O t i j * ψ' j)) t :=
    HasDerivAt.fun_sum (fun j _ =>
      ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hO i) j)).mul (hasDerivAt_pi.mp hψ j))
  have htarget : (O' t *ᵥ ψ t + O t *ᵥ ψ') i
      = ∑ j, (O' t i j * ψ t j + O t i j * ψ' j) := by
    simp [mulVec, dotProduct, Finset.sum_add_distrib]
  rw [htarget]
  simpa [mulVec, dotProduct] using hsum

/-- Source Lemma 1 (Ehrenfest theorem), arXiv:2303.01471v1, PDF page 21,
equation (B.9).

For a time-dependent observable `O(t)` and a solution `Ψ` of the Schrödinger
equation `i d/dt |Ψ_t⟩ = H(t)|Ψ_t⟩` with Hermitian `H(t)`,

`d/dt ⟨Ψ_t|O(t)|Ψ_t⟩ = ⟨Ψ_t|dO/dt|Ψ_t⟩ + ⟨Ψ_t| i[H(t),O(t)] |Ψ_t⟩`.

This is exactly (B.10)–(B.13): the three product-rule terms yield
`⟨Ψ̇|OΨ⟩ + ⟨Ψ|dO/dt Ψ⟩ + ⟨Ψ|OΨ̇⟩`, and `i|Ψ̇⟩ = H|Ψ⟩` with `H = H†`
collapses the first and third into the commutator term. -/
theorem source_ehrenfest (H O O' : ℝ → Matrix (Fin n) (Fin n) ℂ) (ψ : ℝ → Ket (Fin n))
    (hH : ∀ t, (H t).IsHermitian)
    (hψ : ∀ t, HasDerivAt ψ ((-Complex.I) • (H t *ᵥ ψ t)) t)
    (hO : ∀ t, HasDerivAt O (O' t) t) :
    ∀ t, HasDerivAt (fun s => bracket (ψ s) ((O s) *ᵥ ψ s))
      (bracket (ψ t) ((O' t) *ᵥ ψ t)
        + bracket (ψ t) ((Complex.I : ℂ) • (((H t * O t - O t * H t)) *ᵥ ψ t))) t := by
  intro t
  set v : Ket (Fin n) := ψ t with hv
  set v' : Ket (Fin n) := (-Complex.I) • (H t *ᵥ v) with hv'
  have hψt : HasDerivAt ψ v' t := hψ t
  have hw : HasDerivAt (fun s => O s *ᵥ ψ s) (O' t *ᵥ v + O t *ᵥ v') t :=
    hasDerivAt_mulVec_mul O O' (hO t) hψt
  -- derivative of the bracket, entrywise
  have hb : HasDerivAt (fun s => bracket (ψ s) (O s *ᵥ ψ s))
      (bracket v' (O t *ᵥ v) + bracket v (O' t *ᵥ v + O t *ᵥ v')) t := by
    have hsum : HasDerivAt
        (fun s => ∑ i, star (ψ s i) * ((O s *ᵥ ψ s) i))
        (∑ i, (star (v' i) * (O t *ᵥ v) i + star (v i) * ((O' t *ᵥ v + O t *ᵥ v') i))) t :=
      HasDerivAt.fun_sum (fun i _ =>
        ((hasDerivAt_pi.mp hψt i).star).mul (hasDerivAt_pi.mp hw i))
    have hgoal :
        (∑ i, (star (v' i) * (O t *ᵥ v) i + star (v i) * ((O' t *ᵥ v + O t *ᵥ v') i)))
          = bracket v' (O t *ᵥ v) + bracket v (O' t *ᵥ v + O t *ᵥ v') := by
      simp only [Finset.sum_add_distrib, bracket]
    rw [hgoal] at hsum
    simpa [bracket] using hsum
  -- rewrite the derivative to the (B.13) form
  have hD :
      bracket v' (O t *ᵥ v) + bracket v (O' t *ᵥ v + O t *ᵥ v')
        = bracket v (O' t *ᵥ v)
            + bracket v ((Complex.I : ℂ) • (((H t * O t - O t * H t)) *ᵥ v)) := by
    -- first term: ⟨v'|O v⟩ = i ⟨v|(H O)v⟩
    have h1 : bracket v' (O t *ᵥ v) = Complex.I * bracket v ((H t * O t) *ᵥ v) := by
      rw [hv', bracket_smul_left, bracket_mulVec_left_of_isHermitian (hH t) v (O t *ᵥ v),
        mulVec_mulVec]
      simp
    -- second term splits into ⟨v|O'v⟩ and -i ⟨v|(O H)v⟩
    have h2 : bracket v (O' t *ᵥ v + O t *ᵥ v')
        = bracket v (O' t *ᵥ v) + (-Complex.I) * bracket v ((O t * H t) *ᵥ v) := by
      rw [bracket_add_right]
      congr 1
      rw [hv', mulVec_smul, bracket_smul_right, mulVec_mulVec]
    rw [h1, h2, bracket_smul_right, Matrix.sub_mulVec, bracket_sub_right]
    ring
  rw [hD] at hb
  exact hb

end Qatlib.Papers.QHamDescent23.MainResults.Ehrenfest
