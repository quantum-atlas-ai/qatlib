/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Armillary26.Instances.Rate
public import Qatlib.Papers.Armillary26.RoutingModel.Routing
public import Qatlib.Concepts.CodeCert.PermBlocks.Algebra
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum.Basic

@[expose] public section

/-!
# Closing the generic parameter chain from pairing conditions

The K/chi pairing condition on relative permutations derives full CSS
compatibility of the assembled permutation blocks; the resulting code then
carries the universal parameter chain without compatibility as a standing
hypothesis: rank at most `3P - 2`, encoded qubits at least `6P + 4`, and
rate strictly above one half. Instance equalities stay out of scope.
-/

namespace Qatlib.Papers.Armillary26.Instances

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodeCert.PermBlocks
open Qatlib.Concepts.ErrorCorrection.CssBuild
open scoped Matrix

/-- Split a sum over a doubled index into complementary half pairs. -/
theorem sum_pairs {M : Type*} [AddCommMonoid M] (m : ℕ) (T : Fin (m + m) → M) :
    ∑ b : Fin (m + m), T b
      = ∑ i : Fin m, (T ⟨(i : ℕ), by omega⟩ + T ⟨m + (i : ℕ), by omega⟩) := by
  have hsplit : ∑ b : Fin (m + m), T b
      = ∑ x : Fin m ⊕ Fin m, T (finSumFinEquiv x) :=
    Fintype.sum_equiv finSumFinEquiv.symm T (fun x => T (finSumFinEquiv x))
      (fun _ => by simp)
  rw [hsplit, Fintype.sum_sum_type (fun x => T (finSumFinEquiv x))]
  have hleft : ∑ x : Fin m, T (finSumFinEquiv (Sum.inl x))
      = ∑ i : Fin m, T ⟨(i : ℕ), by omega⟩ :=
    Fintype.sum_congr (fun x => T (finSumFinEquiv (Sum.inl x)))
      (fun i => T ⟨(i : ℕ), by omega⟩) (fun _ => rfl)
  have hright : ∑ x : Fin m, T (finSumFinEquiv (Sum.inr x))
      = ∑ i : Fin m, T ⟨m + (i : ℕ), by omega⟩ :=
    Fintype.sum_congr (fun x => T (finSumFinEquiv (Sum.inr x)))
      (fun i => T ⟨m + (i : ℕ), by omega⟩) (fun _ => rfl)
  rw [hleft, hright, ← Finset.sum_add_distrib]

/-- The paired K/chi condition: relative permutations agree on complementary
column pairs. -/
def pairCond {P : Type*} {m r : ℕ}
    (σX σZ : Fin r → Fin (m + m) → Equiv.Perm P) : Prop :=
  ∀ (a a' : Fin r) (i : Fin m),
    (σZ a' ⟨(i : ℕ), by omega⟩)⁻¹ * (σX a ⟨(i : ℕ), by omega⟩)
      = (σZ a' ⟨m + (i : ℕ), by omega⟩)⁻¹ * (σX a ⟨m + (i : ℕ), by omega⟩)

/-- The block product entry splits into per-column block terms. -/
theorem blockProd_entry {P : Type*} [Fintype P] [DecidableEq P] {m r : ℕ}
    (σX σZ : Fin r → Fin (m + m) → Equiv.Perm P) (a a' : Fin r) (p q : P) :
    (((permBlocks σX : Matrix (Fin r × P) (Fin (m + m) × P) (ZMod 2))
        * (permBlocks σZ)ᵀ : Matrix (Fin r × P) (Fin r × P) (ZMod 2))) (a, p) (a', q)
      = ∑ b : Fin (m + m),
        ((permMat (σX a b) * (permMat (σZ a' b))ᵀ : Matrix P P (ZMod 2))) p q := by
  have huniv : (Finset.univ : Finset (Fin (m + m) × P))
      = (Finset.univ : Finset (Fin (m + m))) ×ˢ (Finset.univ : Finset P) := by
    ext x
    simp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, permBlocks]
  rw [huniv, Finset.sum_product]
  exact Finset.sum_congr rfl fun b _ => rfl

/-- The pairing condition derives full compatibility of the assembled blocks. -/
theorem pairCompat {P : Type*} [Fintype P] [DecidableEq P] {m r : ℕ}
    (σX σZ : Fin r → Fin (m + m) → Equiv.Perm P) (hp : pairCond σX σZ) :
    (((permBlocks σX : Matrix (Fin r × P) (Fin (m + m) × P) (ZMod 2))
      * (permBlocks σZ : Matrix (Fin r × P) (Fin (m + m) × P) (ZMod 2))ᵀ :
      Matrix (Fin r × P) (Fin r × P) (ZMod 2))) = 0 := by
  ext x y
  obtain ⟨a, p⟩ := x
  obtain ⟨a', q⟩ := y
  rw [blockProd_entry σX σZ a a' p q]
  rw [sum_pairs m (fun b =>
    ((permMat (σX a b) * (permMat (σZ a' b))ᵀ : Matrix P P (ZMod 2))) p q)]
  refine Finset.sum_eq_zero fun i _ => ?_
  have heq : ((permMat (σX a ⟨(i : ℕ), by omega⟩)
        * (permMat (σZ a' ⟨(i : ℕ), by omega⟩))ᵀ : Matrix P P (ZMod 2))) p q
      = ((permMat (σX a ⟨m + (i : ℕ), by omega⟩)
        * (permMat (σZ a' ⟨m + (i : ℕ), by omega⟩))ᵀ : Matrix P P (ZMod 2))) p q := by
    have hmat : (permMat (σX a ⟨(i : ℕ), by omega⟩)
        * (permMat (σZ a' ⟨(i : ℕ), by omega⟩))ᵀ : Matrix P P (ZMod 2))
        = permMat (σX a ⟨m + (i : ℕ), by omega⟩)
          * (permMat (σZ a' ⟨m + (i : ℕ), by omega⟩))ᵀ :=
      (pairCancel _ _ _ _).mpr (hp a a' i)
    exact congrFun₂ hmat p q
  rw [heq, ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]

/-- The universal rank bound on three block rows of permutation blocks. -/
theorem rankBound {P : Type*} [Fintype P] [DecidableEq P] (p₀ : P)
    (σ : Fin 3 → Fin 12 → Equiv.Perm P) :
    Matrix.rank (permBlocks σ : Matrix (Fin 3 × P) (Fin 12 × P) (ZMod 2))
      ≤ 3 * Fintype.card P - 2 := by
  have h : Matrix.rank (permBlocks σ : Matrix (Fin 3 × P) (Fin 12 × P) (ZMod 2)) + 2
      ≤ 3 * Fintype.card P := perm_rank_add (K := ZMod 2) 2 p₀ σ
  omega

/-- The full generic chain from pairing conditions to code parameters. -/
theorem retained_pair {P : Type*} [Fintype P] [DecidableEq P] (p₀ : P)
    (σX σZ : Fin 3 → Fin 12 → Equiv.Perm P) (hp : pairCond (m := 6) σX σZ) :
    6 * Fintype.card P + 4
      ≤ (retainedCode σX σZ (pairCompat (m := 6) σX σZ hp)).encodedQubits
      ∧ (1 / 2 : ℚ)
        < ((retainedCode σX σZ (pairCompat (m := 6) σX σZ hp)).encodedQubits : ℚ) /
          (12 * Fintype.card P : ℕ) :=
  ⟨encoded_lower p₀ σX σZ (pairCompat (m := 6) σX σZ hp),
    rate_gt_half p₀ σX σZ (pairCompat (m := 6) σX σZ hp)⟩

end Qatlib.Papers.Armillary26.Instances
