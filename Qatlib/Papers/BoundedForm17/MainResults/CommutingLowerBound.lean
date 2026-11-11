/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BoundedForm17.MainResults.CbTensorAux

set_option backward.isDefEq.respectTransparency false

/-!
# CommutingLowerBound — Proposition 4.4 of arXiv:1711.07285v3

Arunachalam–Briët–Palazuelos, *Quantum Query Algorithms are Completely Bounded Forms*,
fixed arXiv:1711.07285v3 (printed p17, Proposition 4.4).  The proposition is the
commuting-contraction lower bound that drives Section 4's random-cubic separation:

`‖p‖_cb ≥ ‖∑_{i₁,…,i_t} (T_p)_{i₁…i_t} A_{i₁} ⋯ A_{i_t}‖`

for a `t`-linear form with symmetric tensor `T_p` and pairwise commuting contractions
`A₁,…,Aₙ` (the paper's `Aᵢ ∈ L(ℝᵐ)`; the library's tensor cb-norm is the contraction
supremum of `tensorCbNorm`, so contractions enter directly).

The proof is the paper's: expand the defining decomposition `T_p = ∑_σ T^σ ∘ σ`, bound
each term of the triangle inequality by `‖T^σ‖_cb`, and use commutativity to reorder the
matrix word produced by the permuted index.  No Christensen–Sinclair input is used.

## Boundary

Real tensors; the contraction supremum of `tensorCbNorm`; commutativity is an explicit
hypothesis (the paper's `Aᵢ` are pairwise commuting by assumption).  The statement is the
tensor-level inequality through `formCbNorm`; the paper's subsequent probabilistic choice
of `Aᵢ` (Theorem 4.1) is not part of this file.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

open Qatlib.Concepts.QueryComplexity.CbDegreeBridge
open Qatlib.Papers.BoundedForm17.MainResults.CbTensorAux

namespace Qatlib.Papers.BoundedForm17.MainResults.CommutingLowerBound

variable {κ : Type} [Fintype κ] {s : ℕ}

/-! ## Proposition 4.4 -/

/-- **Proposition 4.4** (arXiv:1711.07285v3, printed p17).  For a symmetric `t`-tensor
`T` and pairwise commuting contractions `A : κ → L(ℂ^d)`, the completely bounded norm of
the associated form dominates the operator norm of the commuting matrix word
`∑_{i₁,…,i_t} T_{i₁…i_t} A_{i₁}⋯A_{i_t}`. -/
theorem prop_4_4 (T : RealTensor κ s) (hT : IsSymmTensor T) {d : ℕ}
    (A : κ → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, ‖A i‖ ≤ 1)
    (hcomm : ∀ i j, A i * A j = A j * A i) :
    ‖∑ i : Fin s → κ, (T i : ℂ) • matProdFin s (fun j => A (i j))‖ ≤ formCbNorm T := by
  refine le_csInf (formCbNorm_set_nonempty T hT) ?_
  rintro c ⟨D, hD, rfl⟩
  -- The word sum, expanded through the decomposition and reindexed by each permutation.
  have hexp : ∑ i : Fin s → κ, (T i : ℂ) • matProdFin s (fun j => A (i j))
      = ∑ σ : Equiv.Perm (Fin s),
          ∑ i : Fin s → κ, ((D σ i : ℝ) : ℂ) • matProdFin s (fun j => A (i j)) := by
    have hTsum : ∀ i : Fin s → κ, (T i : ℂ)
        = ∑ σ : Equiv.Perm (Fin s), ((D σ (i ∘ σ) : ℝ) : ℂ) := by
      intro i
      rw [hD i]
      push_cast
      rfl
    calc ∑ i : Fin s → κ, (T i : ℂ) • matProdFin s (fun j => A (i j))
        = ∑ i : Fin s → κ, (∑ σ : Equiv.Perm (Fin s), ((D σ (i ∘ σ) : ℝ) : ℂ))
            • matProdFin s (fun j => A (i j)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hTsum i]
      _ = ∑ i : Fin s → κ, ∑ σ : Equiv.Perm (Fin s),
            ((D σ (i ∘ σ) : ℝ) : ℂ) • matProdFin s (fun j => A (i j)) := by
          simp only [Finset.sum_smul]
      _ = ∑ σ : Equiv.Perm (Fin s), ∑ i : Fin s → κ,
            ((D σ (i ∘ σ) : ℝ) : ℂ) • matProdFin s (fun j => A (i j)) :=
          Finset.sum_comm
      _ = ∑ σ : Equiv.Perm (Fin s), ∑ i : Fin s → κ,
            ((D σ i : ℝ) : ℂ) • matProdFin s (fun j => A (i j)) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          refine Fintype.sum_equiv (compEquiv (κ := κ) σ) _ _ ?_
          intro i
          have hP : matProdFin s (fun j => A ((i ∘ σ) j))
              = matProdFin s (fun j => A (i j)) :=
            matProdFin_comp_perm (M := fun j => A (i j))
              (fun a b => hcomm (i a) (i b)) σ
          simp only [compEquiv, Equiv.coe_fn_mk]
          rw [hP]
  rw [hexp]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun σ _ => ?_
  exact norm_le_tensorCbNorm (D σ) (fun _ i => A i) (fun _ i => hA i)

end Qatlib.Papers.BoundedForm17.MainResults.CommutingLowerBound
