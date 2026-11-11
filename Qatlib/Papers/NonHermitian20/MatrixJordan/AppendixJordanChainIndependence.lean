/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Appendix A.2 — independence of Jordan chains (Non-Hermitian Physics)

Fixed arXiv:2006.01837v3 (Adv. Phys. review, 2020). Theorem A.2, p.150–151.

Suppose `λ` is an eigenvalue of `M` and `u_j` (`j = 1, …, m`) are generalized eigenvectors
of ranks `p_j + 1` with `0 ≤ p₁ ≤ ⋯ ≤ p_m`. Defining `u_j^{(k_j)} = (M - λI)^{k_j} u_j`
for `0 ≤ k_j ≤ p_j`, the `m + ∑_j p_j` vectors `{u_j^{(k_j)}}` are linearly independent
**iff** the `m` "top" vectors `u_j^{(p_j)}` are linearly independent.

We state this over an arbitrary field `K` and vector space `V` (the paper uses `K = ℂ`,
`V = ℂⁿ`). "Generalized eigenvector of rank `p_j + 1`" is encoded as
`((T - λ·1)^{p_j+1})(u_j) = 0`.

The `⇐` direction is the content; `⇒` follows because the top vectors are the sub-family of
the full family at position `k_j = p_j`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NonHermitian20.MatrixJordan

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Fixed arXiv:2006.01837v3, Theorem A.2, p.150–151.

For an endomorphism `T`, eigenvalue parameter `lam`, generalized-eigenvector ranks `p j + 1`
(`(T - lam·1)^{p j + 1} u_j = 0`) and the Jordan-chain vectors
`x ↦ (T - lam·1)^{k_x} u_j` (`0 ≤ k_x ≤ p_j`), the full chain family is linearly
independent iff the top family `j ↦ (T - lam·1)^{p_j} u_j` is linearly independent.

The order condition `0 ≤ p₁ ≤ ⋯ ≤ p_m` of the paper is not needed for the biconditional and
is dropped (the proof peels off the maximal rank, so no ordering is required). -/
theorem theorem_A2_jordan_chain_independence {m : ℕ} (T : V →ₗ[K] V) (lam : K)
    (p : Fin m → ℕ) (u : Fin m → V)
    (hrank : ∀ j, ((T - lam • (1 : V →ₗ[K] V)) ^ (p j + 1)) (u j) = 0) :
    LinearIndependent K (fun x : (Σ j : Fin m, Fin (p j + 1)) =>
        ((T - lam • (1 : V →ₗ[K] V)) ^ (x.2 : ℕ)) (u x.1)) ↔
      LinearIndependent K (fun j : Fin m =>
        ((T - lam • (1 : V →ₗ[K] V)) ^ (p j)) (u j)) := by
  classical
  set N : V →ₗ[K] V := T - lam • 1 with hN
  have hrankN : ∀ j, (N ^ (p j + 1)) (u j) = 0 := fun j => hrank j
  constructor
  · -- ⇒ : the top vectors are the sub-family of all chain vectors at `k_j = p_j`.
    intro hchain
    have hf : Function.Injective
        (fun j : Fin m => (⟨j, ⟨p j, Nat.lt_succ_self (p j)⟩⟩ : Sigma fun j => Fin (p j + 1))) := by
      intro a b hab
      exact congrArg Sigma.fst hab
    have h := hchain.comp _ hf
    simpa only [Function.comp_def] using h
  · -- ⇐ : the substantive direction.
    -- Fixed source: arXiv:2006.01837v3, Theorem A.2, pp.150–151; proof Eqs. (A16)–(A18).
    -- Formalised as the paper's induction on `r`: multiply a relation by `N^{P-r-1}`,
    -- collapse each chain to its unique surviving top-layer term, and use independence
    -- of the top vectors. Here `P` is the sum of the ranks, which bounds every `p j`.
    intro htop
    rw [Fintype.linearIndependent_iff]
    intro c hrel
    let top : Fin m → V := fun j => (N ^ (p j)) (u j)
    have htop' : LinearIndependent K top := htop
    -- Nilpotence: once the exponent reaches `p j + 1`, the chain vector vanishes.
    have hNpow_zero : ∀ (j : Fin m) (a : ℕ), p j + 1 ≤ a → (N ^ a) (u j) = 0 := by
      intro j a ha
      have hsplit : a = (p j + 1) + (a - (p j + 1)) := (Nat.add_sub_of_le ha).symm
      have h1 : (N ^ (p j + 1)) ((N ^ (a - (p j + 1))) (u j))
          = (N ^ (a - (p j + 1))) ((N ^ (p j + 1)) (u j)) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, pow_mul_comm]
      rw [hsplit, pow_add, Module.End.mul_apply, h1, hrankN j, map_zero]
    -- Expand a relation after applying `N^e`.
    have expand : ∀ (e : ℕ), (∑ x, c x • (N ^ (x.2 : ℕ)) (u x.1)) = 0 →
        (∑ j, ∑ k : Fin (p j + 1), c ⟨j, k⟩ • (N ^ (e + (k : ℕ))) (u j)) = 0 := by
      intro e hrel'
      have h := congrArg (fun w => (N ^ e) w) hrel'
      simp only [map_sum, map_smul, Fintype.sum_sigma, map_zero] at h
      simpa only [← Module.End.mul_apply, ← pow_add] using h
    -- Collapse one layer: under the induction hypothesis, only the term at
    -- `e + k = p j` survives, and the sum becomes a top-vector relation.
    have collapse : ∀ (e : ℕ),
        (∀ (j : Fin m) (k : Fin (p j + 1)), e + (k : ℕ) < p j → c ⟨j, k⟩ = 0) →
        (∑ j, ∑ k : Fin (p j + 1), c ⟨j, k⟩ • (N ^ (e + (k : ℕ))) (u j)) = 0 →
        (∑ j, (if h : e ≤ p j then
            c ⟨j, ⟨p j - e, Nat.lt_succ_of_le (Nat.sub_le (p j) e)⟩⟩ else 0) • top j) = 0 := by
      intro e hzero hsum
      have hinner : ∀ j : Fin m,
          (∑ k : Fin (p j + 1), c ⟨j, k⟩ • (N ^ (e + (k : ℕ))) (u j))
            = (if h : e ≤ p j then
                c ⟨j, ⟨p j - e, Nat.lt_succ_of_le (Nat.sub_le (p j) e)⟩⟩ else 0) • top j := by
        intro j
        by_cases h : e ≤ p j
        · rw [dif_pos h]
          let k0 : Fin (p j + 1) :=
            ⟨p j - e, Nat.lt_succ_of_le (Nat.sub_le (p j) e)⟩
          trans (c ⟨j, k0⟩ • (N ^ (e + (k0 : ℕ))) (u j))
          · exact Finset.sum_eq_single k0
              (fun k _ hk => by
                have hne : e + (k : ℕ) ≠ p j := by
                  intro heq
                  apply hk
                  apply Fin.ext
                  dsimp [k0]
                  omega
                rcases lt_or_gt_of_ne hne with hlt | hgt
                · rw [hzero j k hlt, zero_smul]
                · have hnil : p j + 1 ≤ e + (k : ℕ) := by omega
                  rw [hNpow_zero j (e + (k : ℕ)) hnil, smul_zero])
              (fun hk => absurd (Finset.mem_univ k0) hk)
          · have hk0 : e + (k0 : ℕ) = p j := by
              dsimp [k0]
              omega
            simp only [hk0, top]
            rfl
        · rw [dif_neg h, zero_smul]
          apply Finset.sum_eq_zero
          intro k _
          have hnil : p j + 1 ≤ e + (k : ℕ) := by omega
          rw [hNpow_zero j (e + (k : ℕ)) hnil, smul_zero]
      simpa only [hinner] using hsum
    -- Maximum rank, chosen as the sum so that no `Finset.sup` API is needed.
    let P : ℕ := ∑ j, p j
    have hp_le : ∀ j : Fin m, p j ≤ P := by
      intro j
      exact Finset.single_le_sum (fun i _ => Nat.zero_le (p i)) (Finset.mem_univ j)
    -- Base case: `k + P ≤ p_j` forces `k = 0` and `p_j = P`.
    have hbase : ∀ (j : Fin m) (k : Fin (p j + 1)),
        (k : ℕ) + P ≤ p j + 0 → c ⟨j, k⟩ = 0 := by
      intro j k hk
      have hzeroP : ∀ (j' : Fin m) (k' : Fin (p j' + 1)),
          P + (k' : ℕ) < p j' → c ⟨j', k'⟩ = 0 := by
        intro j' k' hlt
        have hle := hp_le j'
        omega
      have hcoll := collapse P hzeroP (expand P hrel)
      have hd := (Fintype.linearIndependent_iff.mp htop')
          (fun j' => if h : P ≤ p j' then
            c ⟨j', ⟨p j' - P, Nat.lt_succ_of_le (Nat.sub_le (p j') P)⟩⟩ else 0) hcoll
      have hd0 := hd j
      have hle := hp_le j
      have hpj : p j = P := by omega
      have hk0 : (k : ℕ) = 0 := by omega
      rw [dif_pos (le_of_eq hpj.symm)] at hd0
      have hd0' : c ⟨j, ⟨0, Nat.zero_lt_succ (p j)⟩⟩ = 0 := by
        simpa [hpj] using hd0
      have hkfin : k = ⟨0, Nat.zero_lt_succ (p j)⟩ := Fin.ext hk0
      simpa [hkfin] using hd0'
    -- Induction step.
    have hstep : ∀ r, r < P →
        (∀ (j : Fin m) (k : Fin (p j + 1)), (k : ℕ) + P ≤ p j + r → c ⟨j, k⟩ = 0) →
        (∀ (j : Fin m) (k : Fin (p j + 1)), (k : ℕ) + P ≤ p j + (r + 1) → c ⟨j, k⟩ = 0) := by
      intro r hr ih j k hk
      by_cases hle : (k : ℕ) + P ≤ p j + r
      · exact ih j k hle
      · have hEq : (k : ℕ) + P = p j + r + 1 := by omega
        let e : ℕ := P - r - 1
        have he : P = e + r + 1 := by
          dsimp [e]
          omega
        have hzero : ∀ (j' : Fin m) (k' : Fin (p j' + 1)),
            e + (k' : ℕ) < p j' → c ⟨j', k'⟩ = 0 := by
          intro j' k' hlt
          apply ih j' k'
          omega
        have hcoll := collapse e hzero (expand e hrel)
        have hd := (Fintype.linearIndependent_iff.mp htop')
            (fun j' => if h : e ≤ p j' then
              c ⟨j', ⟨p j' - e, Nat.lt_succ_of_le (Nat.sub_le (p j') e)⟩⟩ else 0) hcoll
        have hd0 := hd j
        have hep : e ≤ p j := by omega
        rw [dif_pos hep] at hd0
        have hkval : (k : ℕ) = p j - e := by omega
        have hkfin : k = ⟨p j - e, Nat.lt_succ_of_le (Nat.sub_le (p j) e)⟩ := Fin.ext hkval
        simpa [hkfin] using hd0
    -- Assemble the induction up to `P`.
    have hZ : ∀ r, r ≤ P →
        (∀ (j : Fin m) (k : Fin (p j + 1)), (k : ℕ) + P ≤ p j + r → c ⟨j, k⟩ = 0) := by
      intro r
      induction r with
      | zero => intro _; exact hbase
      | succ r ih =>
          intro hr
          exact hstep r (by omega) (ih (by omega))
    intro x
    rcases x with ⟨j, k⟩
    exact hZ P le_rfl j k (by omega)

end Qatlib.Papers.NonHermitian20.MatrixJordan
