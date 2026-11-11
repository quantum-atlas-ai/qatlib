/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BoundedForm17.MainResults.CbTensorAux

set_option backward.isDefEq.respectTransparency false

/-!
# Symmetrization — the tensor step in the proof of Theorem 1.3

Arunachalam–Briët–Palazuelos, *Quantum Query Algorithms are Completely Bounded Forms*,
fixed arXiv:1711.07285v3 (printed p15, proof of Theorem 1.3, direction (1) ⇒ (2)).

The paper's reduction from a form of completely bounded norm at most one to a tensor of
completely bounded norm at most one: if `T_p = ∑_σ T^σ ∘ σ` is the defining decomposition
of Eq. (5), then `T = ∑_σ T^σ` satisfies

* `‖T‖_cb ≤ ∑_σ ‖T^σ‖_cb` (triangle inequality in the cb-norm supremum), and
* `T(y, …, y) = T_p(y, …, y) = p(y)` for every `y` (each `T^σ ∘ σ` agrees with `T^σ` on
  the diagonal).

Composing with the paper's `‖p‖_cb ≤ 1` gives `‖T‖_cb ≤ 1` and equal diagonal values, i.e.
exactly the hypothesis of Lemma 3.3 (1).  The subsequent Lemma 3.3 (1) ⇒ (2) step needs the
Christensen–Sinclair factorization `HasCbFactorization` and is not part of this file.

## Boundary

Real tensors, contraction-family `tensorCbNorm`, and the form norm `formCbNorm` of the
library.  Attainment of the infimum in Definition 1.2 is *not* asserted: the results below
hold for an arbitrary decomposition, and the `≤ 1` corollary assumes a decomposition whose
cost is at most one (the paper obtains one from compactness/attainment).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

open Qatlib.Concepts.QueryComplexity.CbDegreeBridge
open Qatlib.Papers.BoundedForm17.MainResults.CbTensorAux

namespace Qatlib.Papers.BoundedForm17.MainResults.Symmetrization

variable {κ : Type} [Fintype κ] {s : ℕ}

/-- The symmetrized tensor `T = ∑_σ T^σ` built from a decomposition `T_p = ∑_σ T^σ ∘ σ`
(paper proof of Theorem 1.3, (1) ⇒ (2)). -/
def symmetrize (D : Equiv.Perm (Fin s) → RealTensor κ s) : RealTensor κ s :=
  fun i => ∑ σ : Equiv.Perm (Fin s), D σ i

/-- Triangle inequality for the symmetrized tensor: its cb-norm is at most the cost of the
decomposition (paper: `‖T‖_cb ≤ ∑_σ ‖T^σ‖_cb`). -/
theorem tensorCbNorm_symmetrize_le (D : Equiv.Perm (Fin s) → RealTensor κ s) :
    tensorCbNorm (symmetrize D) ≤ ∑ σ : Equiv.Perm (Fin s), tensorCbNorm (D σ) := by
  refine csSup_le ?hne ?h
  · exact ⟨_, 1, fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ),
      fun _ _ => by simp, rfl⟩
  · rintro r ⟨d, A, hA, rfl⟩
    have hsplit : ∑ i : Fin s → κ, (symmetrize D i : ℂ) • matProdFin s (fun j => A j (i j))
        = ∑ σ : Equiv.Perm (Fin s),
            ∑ i : Fin s → κ, ((D σ i : ℝ) : ℂ) • matProdFin s (fun j => A j (i j)) := by
      show (∑ i : Fin s → κ, ((∑ σ : Equiv.Perm (Fin s), D σ i : ℝ) : ℂ)
          • matProdFin s (fun j => A j (i j))) = _
      push_cast
      simp only [Finset.sum_smul]
      exact Finset.sum_comm
    rw [hsplit]
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun σ _ => ?_
    exact norm_le_tensorCbNorm (D σ) A hA

/-- Diagonal values are unchanged by symmetrization: the symmetrized tensor and the form
agree at every point (paper: `T(y, …, y) = T_p(y, …, y) = p(y)`). -/
theorem formValue_symmetrize_eq {T : RealTensor κ s}
    {D : Equiv.Perm (Fin s) → RealTensor κ s}
    (hD : ∀ i : Fin s → κ, T i = ∑ σ : Equiv.Perm (Fin s), D σ (i ∘ σ))
    (y : κ → ℝ) : formValue (symmetrize D) y = formValue T y := by
  have hL : formValue (symmetrize D) y
      = ∑ σ : Equiv.Perm (Fin s), formValue (D σ) y := by
    show (∑ i : Fin s → κ, (∑ σ : Equiv.Perm (Fin s), D σ i) * ∏ j, y (i j))
        = ∑ σ : Equiv.Perm (Fin s), ∑ i : Fin s → κ, D σ i * ∏ j, y (i j)
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  have hR : formValue T y = ∑ σ : Equiv.Perm (Fin s), formValue (D σ) y := by
    have hT : formValue T y = ∑ i : Fin s → κ,
        (∑ σ : Equiv.Perm (Fin s), D σ (i ∘ σ)) * ∏ j, y (i j) := by
      rw [formValue]
      exact Finset.sum_congr rfl fun i _ => by rw [hD i]
    rw [hT]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [formValue]
    refine Fintype.sum_equiv (compEquiv (κ := κ) σ) _ _ fun j => ?_
    have hprod : (∏ k : Fin s, y ((j ∘ σ) k)) = ∏ k : Fin s, y (j k) := by
      rw [show (fun k : Fin s => y ((j ∘ σ) k)) = fun k => y (j (σ k)) from rfl,
        Equiv.Perm.prod_comp σ Finset.univ (fun k => y (j k)) (by simp)]
    simp only [compEquiv, Equiv.coe_fn_mk]
    rw [hprod]
  rw [hL, hR]

/-- The symmetric tensor of a form has cb-norm at least the form's cb-norm: the constant
decomposition `T^σ = (s!)⁻¹ • T` is admissible with cost at most `‖T‖_cb`, so the infimum
in Definition 1.2 is at most `‖T‖_cb` (paper §1.2: the cb-norm of a form can be much
smaller than that of its symmetric tensor). -/
theorem formCbNorm_le_tensorCbNorm (T : RealTensor κ s) (hT : IsSymmTensor T) :
    formCbNorm T ≤ tensorCbNorm T := by
  have hfac : (Nat.factorial s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos s).ne'
  have hmem : (∑ _σ : Equiv.Perm (Fin s),
      tensorCbNorm (fun i => (Nat.factorial s : ℝ)⁻¹ * T i))
      ∈ {c : ℝ | ∃ D : Equiv.Perm (Fin s) → RealTensor κ s,
        (∀ i : Fin s → κ, T i = ∑ σ : Equiv.Perm (Fin s), D σ (i ∘ σ)) ∧
          c = ∑ σ : Equiv.Perm (Fin s), tensorCbNorm (D σ)} := by
    refine ⟨fun _ => fun i => (Nat.factorial s : ℝ)⁻¹ * T i, ?_, rfl⟩
    intro i
    have hsum : ∑ _σ : Equiv.Perm (Fin s), ((Nat.factorial s : ℝ)⁻¹ * T i) = T i := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    calc T i = ∑ _σ : Equiv.Perm (Fin s), ((Nat.factorial s : ℝ)⁻¹ * T i) := hsum.symm
      _ = ∑ σ : Equiv.Perm (Fin s), (Nat.factorial s : ℝ)⁻¹ * T (i ∘ σ) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [isSymmTensor_apply T hT i σ]
  refine (csInf_le (formCbNorm_set_bddBelow T) hmem).trans ?_
  calc (∑ _σ : Equiv.Perm (Fin s), tensorCbNorm (fun i => (Nat.factorial s : ℝ)⁻¹ * T i))
      ≤ ∑ _σ : Equiv.Perm (Fin s), ((Nat.factorial s : ℝ)⁻¹ * tensorCbNorm T) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        calc tensorCbNorm (fun i => (Nat.factorial s : ℝ)⁻¹ * T i)
            ≤ |(Nat.factorial s : ℝ)⁻¹| * tensorCbNorm T := tensorCbNorm_constMul_le _ T
          _ = (Nat.factorial s : ℝ)⁻¹ * tensorCbNorm T := by
              rw [abs_of_nonneg (by positivity)]
    _ = tensorCbNorm T := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul]
        field_simp

/-- **Theorem 1.3, (1) ⇒ (2), tensor step** (arXiv:1711.07285v3, printed p15).  A
decomposition of `T_p` of cost at most one produces a tensor of completely bounded norm at
most one with the same diagonal values. -/
theorem exists_tensorCbNorm_le_one {T : RealTensor κ s}
    {D : Equiv.Perm (Fin s) → RealTensor κ s}
    (hD : ∀ i : Fin s → κ, T i = ∑ σ : Equiv.Perm (Fin s), D σ (i ∘ σ))
    (hcost : ∑ σ : Equiv.Perm (Fin s), tensorCbNorm (D σ) ≤ 1) :
    tensorCbNorm (symmetrize D) ≤ 1 ∧ ∀ y : κ → ℝ, formValue (symmetrize D) y = formValue T y :=
  ⟨(tensorCbNorm_symmetrize_le D).trans hcost, formValue_symmetrize_eq hD⟩

/-- **Completely bounded norm at most one reduces to a tensor bound**, under the paper's
attainment of the infimum in Definition 1.2: a cost-one decomposition yields a tensor of
cb-norm at most one with equal diagonal values. -/
theorem exists_tensor_of_cbFormNorm_le_one {T : RealTensor κ s}
    {D : Equiv.Perm (Fin s) → RealTensor κ s}
    (hD : ∀ i : Fin s → κ, T i = ∑ σ : Equiv.Perm (Fin s), D σ (i ∘ σ))
    (hattain : ∑ σ : Equiv.Perm (Fin s), tensorCbNorm (D σ) = formCbNorm T)
    (hle : formCbNorm T ≤ 1) :
    tensorCbNorm (symmetrize D) ≤ 1 ∧ ∀ y : κ → ℝ, formValue (symmetrize D) y = formValue T y :=
  exists_tensorCbNorm_le_one hD (hattain.trans_le hle)

end Qatlib.Papers.BoundedForm17.MainResults.Symmetrization
