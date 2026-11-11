/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Complex.Basic
import Mathlib.Data.List.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4 and Lemma 8 of arXiv:1311.6474v1: the commuting-projector invariant

Source: Martin Schwarz, Toby S. Cubitt, Frank Verstraete,
*An Information-Theoretic Proof of the Constructive Commutative Quantum Lovász Local Lemma*,
arXiv:1311.6474v1, Lemma 4 (Section 3, pp. 5–6) and Lemma 8 (Appendix A.1, p. 13).

Both lemmas state the same invariant, once for the information-theoretic analysis (Lemma 4) and
once for the coherent algorithm of Algorithm 2 (Lemma 8).  Fix a history in which the failed
projector is `Π_l` and let `Γ⁺` be its inclusive neighbourhood, listed in the order in which the
algorithm measures it (the paper's `Γ` returns an *ordered* tuple of projectors).  The algorithm
then applies the *fix operator* of that recursion level

  `fixOp = (∏_{i ∈ Γ⁺} Π⁰_i) · R · Π_l`

(Eq. (57)), where `Π⁰_i = 1 - Π_i` is the projector onto the satisfied subspace of `Π_i` and `R`
is the swap-and-rotate operation, which acts on registers other than those of the projectors.
Two properties are needed:

* (i)/(1) every projector that was satisfied before stays satisfied,
* (ii)/(2) the originally unsatisfied projector `Π_l` (and in fact every projector of `Γ⁺`) is
  satisfied afterwards.

The commuting-projector step is Eq. (57)–(58): a projector `Π_q` that commutes with all factors of
the operator can be moved to the right across them, so applying the operator to a state annihilated
by `Π_q` still yields a state annihilated by `Π_q`.  This is the only place in the paper where
commutativity of the `{Π_i}` is used, and `satisfied_preserved` formalises exactly it.

The file also provides the multi-level form `satisfied_of_commute_list_prod`: a state satisfied at
some recursion level stays satisfied through any further stack of level operators that commute with
the projector.  The full recursive control flow of Algorithm 2 (which decides which levels are
entered) is *not* modelled here.
-/

namespace Qatlib.Papers.LovaszLemma13.MainResults

open Matrix

open scoped BigOperators

set_option autoImplicit false

section Projections

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- A projector `A` satisfies a state `v` when it annihilates it, `A v = 0`.  This is the paper's
"`Π_i |φ⟩ = 0`", i.e. the state carries zero energy for the term `Π_i`. -/
def Satisfied (A : Matrix ν ν ℂ) (v : ν → ℂ) : Prop := A *ᵥ v = 0

/-- The complement `Π⁰ = 1 - Π` of a projector is orthogonal to it: `Π · Π⁰ = 0`. -/
lemma projector_mul_compl (A : Matrix ν ν ℂ) (hA : A * A = A) : A * (1 - A) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, hA, sub_self]

/-- Commutation is inherited by the complement of a projector. -/
lemma commute_compl {A B : Matrix ν ν ℂ} (h : A * B = B * A) : A * (1 - B) = (1 - B) * A := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, h]

/-- If `A` commutes with every factor of a list product then it commutes with the product. -/
lemma commute_list_prod (A : Matrix ν ν ℂ) (L : List (Matrix ν ν ℂ))
    (h : ∀ B ∈ L, A * B = B * A) : A * L.prod = L.prod * A := by
  induction L with
  | nil => simp
  | cons B t ih =>
      have hB : A * B = B * A := h B (List.mem_cons_self ..)
      have ht : A * t.prod = t.prod * A := ih (fun C hC => h C (List.mem_cons_of_mem B hC))
      rw [List.prod_cons]
      calc A * (B * t.prod) = (A * B) * t.prod := (Matrix.mul_assoc A B t.prod).symm
        _ = (B * A) * t.prod := by rw [hB]
        _ = B * (A * t.prod) := Matrix.mul_assoc B A t.prod
        _ = B * (t.prod * A) := by rw [ht]
        _ = (B * t.prod) * A := (Matrix.mul_assoc B t.prod A).symm

/-- The fix operator of one recursion level: apply the complement projector of every projector of
the neighbourhood `L` (in the algorithm's order), then the swap-and-rotate `R`, then the failed
projector itself (Eq. (57)). -/
noncomputable def fixOp (L : List (Matrix ν ν ℂ)) (R : Matrix ν ν ℂ) (P : Matrix ν ν ℂ) :
    Matrix ν ν ℂ := (L.map (fun A => 1 - A)).prod * R * P

/-- If `Π_q` is one of the measured projectors of the neighbourhood, then the fix operator contains
the complementary factor `1 - Π_q`; commuting it to the left of that factor makes the product
vanish.  This is the reason every projector of `Γ⁺` is satisfied after the fix step. -/
lemma compl_factor_zero (Pq : Matrix ν ν ℂ) (L : List (Matrix ν ν ℂ))
    (hproj : Pq * Pq = Pq) (hPq : Pq ∈ L)
    (hcomm : ∀ A ∈ L, Pq * (1 - A) = (1 - A) * Pq) :
    Pq * (L.map (fun A => 1 - A)).prod = 0 := by
  induction L with
  | nil => simp at hPq
  | cons A t ih =>
      rw [List.map_cons, List.prod_cons]
      by_cases hPA : Pq = A
      · subst hPA
        rw [← Matrix.mul_assoc, projector_mul_compl Pq hproj, Matrix.zero_mul]
      · have hPq' : Pq ∈ t := by
          rcases List.mem_cons.mp hPq with h | h
          · exact absurd h hPA
          · exact h
        have hc : Pq * (1 - A) = (1 - A) * Pq := hcomm A (List.mem_cons_self ..)
        rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc,
          ih hPq' (fun B hB => hcomm B (List.mem_cons_of_mem A hB)), Matrix.mul_zero]

/-- **Lemma 4 (ii) / Lemma 8 (2), algebraic core.**  The failed projector `l` belongs to its own
inclusive neighbourhood, so the complement factor `1 - Π_l` occurs in the fix operator; the failed
projector is therefore satisfied after the fix step, for every input state. -/
theorem fixOp_target_zero (L : List (Matrix ν ν ℂ)) (R Pq : Matrix ν ν ℂ)
    (hproj : Pq * Pq = Pq) (hPq : Pq ∈ L)
    (hcomm : ∀ A ∈ L, Pq * (1 - A) = (1 - A) * Pq) :
    Pq * fixOp L R Pq = 0 := by
  unfold fixOp
  set Lp : Matrix ν ν ℂ := (L.map (fun A => 1 - A)).prod with hLp
  have hzero : Pq * Lp = 0 := compl_factor_zero Pq L hproj hPq hcomm
  calc Pq * (Lp * R * Pq)
      = Pq * (Lp * R) * Pq := (Matrix.mul_assoc Pq (Lp * R) Pq).symm
    _ = (Pq * Lp) * R * Pq := by rw [(Matrix.mul_assoc Pq Lp R).symm]
    _ = ((0 : Matrix ν ν ℂ) * R) * Pq := by rw [hzero]
    _ = 0 := by rw [Matrix.zero_mul, Matrix.zero_mul]

/-- **Lemma 4 (i) / Lemma 8 (1), algebraic core (Eq. (57)–(58)).**  If the state `v` is satisfied
by the projector `Π_q`, and `Π_q` commutes with every projector of the neighbourhood and with the
swap-and-rotate `R`, then the state after the fix step is still satisfied by `Π_q`. -/
theorem satisfied_preserved (L : List (Matrix ν ν ℂ)) (R Pq P : Matrix ν ν ℂ)
    (hcommP : ∀ A ∈ L, Pq * A = A * Pq) (hcommR : Pq * R = R * Pq)
    (hcommP' : Pq * P = P * Pq)
    (v : ν → ℂ) (hv : Satisfied Pq v) :
    Satisfied Pq (fixOp L R P *ᵥ v) := by
  have hcommL : ∀ A ∈ L, Pq * (1 - A) = (1 - A) * Pq :=
    fun A hA => commute_compl (hcommP A hA)
  have hcommProd : Pq * (L.map (fun A => 1 - A)).prod
      = (L.map (fun A => 1 - A)).prod * Pq :=
    commute_list_prod Pq _ (fun A hA => by
      obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hA
      exact hcommL B hB)
  have hcommFix : Pq * fixOp L R P = fixOp L R P * Pq := by
    unfold fixOp
    calc Pq * ((L.map (fun A => 1 - A)).prod * R * P)
        = (Pq * (L.map (fun A => 1 - A)).prod) * R * P := by simp only [Matrix.mul_assoc]
      _ = ((L.map (fun A => 1 - A)).prod * Pq) * R * P := by rw [hcommProd]
      _ = (L.map (fun A => 1 - A)).prod * (Pq * R) * P := by simp only [Matrix.mul_assoc]
      _ = (L.map (fun A => 1 - A)).prod * (R * Pq) * P := by rw [hcommR]
      _ = (L.map (fun A => 1 - A)).prod * R * (Pq * P) := by simp only [Matrix.mul_assoc]
      _ = (L.map (fun A => 1 - A)).prod * R * (P * Pq) := by rw [hcommP']
      _ = ((L.map (fun A => 1 - A)).prod * R * P) * Pq := by simp only [Matrix.mul_assoc]
  unfold Satisfied at hv ⊢
  rw [Matrix.mulVec_mulVec, hcommFix, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

/-- **Lemma 4 (i)+(ii) / Lemma 8 (1)+(2) at one recursion level.**  After the fix step of the
level whose failed projector is `l`, (i) every projector `q` that was satisfied before and commutes
with the level stays satisfied, and (ii) the failed projector is satisfied. -/
theorem fix_step_invariant (L : List (Matrix ν ν ℂ)) (R Pq Pl : Matrix ν ν ℂ)
    (hproj : Pl * Pl = Pl) (hl : Pl ∈ L)
    (hcommP : ∀ A ∈ L, Pq * A = A * Pq) (hcommPl : ∀ A ∈ L, Pl * A = A * Pl)
    (hcommR : Pq * R = R * Pq)
    (v : ν → ℂ) (hv : Satisfied Pq v) :
    Satisfied Pq (fixOp L R Pl *ᵥ v) ∧ Satisfied Pl (fixOp L R Pl *ᵥ v) := by
  refine ⟨satisfied_preserved L R Pq Pl hcommP hcommR (hcommP Pl hl) v hv, ?_⟩
  unfold Satisfied
  rw [Matrix.mulVec_mulVec, fixOp_target_zero L R Pl hproj hl
    (fun A hA => commute_compl (hcommPl A hA)), Matrix.zero_mulVec]

/-- **Preservation along a stack of recursion levels.**  If a state is satisfied by `Π_q` and every
level operator of the stack commutes with `Π_q`, then the state obtained by applying the whole stack
is still satisfied by `Π_q`.  This is the induction over recursion levels of Lemma 4/8, separated
from the control flow that determines the stack. -/
theorem satisfied_of_commute_list_prod (Pq : Matrix ν ν ℂ) (F : List (Matrix ν ν ℂ))
    (hcomm : ∀ A ∈ F, Pq * A = A * Pq) (v : ν → ℂ) (hv : Satisfied Pq v) :
    Satisfied Pq (F.prod *ᵥ v) := by
  unfold Satisfied at hv ⊢
  rw [Matrix.mulVec_mulVec, commute_list_prod Pq F hcomm, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_zero]

end Projections

end Qatlib.Papers.LovaszLemma13.MainResults
