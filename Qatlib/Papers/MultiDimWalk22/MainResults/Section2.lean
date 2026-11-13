/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultiDimWalk22.MainResults.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Multidimensional Quantum Walks: Uniform Subroutines, Direct Sums, and Tail Bounds

This module formalizes the Section 2 preliminaries of Jeffery and Zur on uniform
quantum subroutines, direct sums of quantum subroutines on product registers
`Fin c × Z`, and the Chernoff-type hypergeometric upper-tail bound.

## Main definitions

* `UniformSubroutine`, `UniformSubroutine.gateComplexity`: uniform quantum subroutine data and gate cost.

## Main statements

* `polylogCost_one`: constant cost `1` is polylogarithmic.
* `lemma2_6_uniform_algorithm`: Lemma 2.6, polylogarithmic gate complexity of uniform subroutines.
* `lemma2_7_direct_sum`: Lemma 2.7, direct-sum implementation of `c` uniform-time quantum subroutines.
* `corollary2_9_hypergeometric_tail`: Corollary 2.9, hypergeometric upper-tail estimate `2 e^c (c / μ)^{-c}`.

## References

* [Jeffery and Zur, 2022][JefferyZur2022], Section 2, Lemmas 2.6 and 2.7, Corollary 2.9, pp. 12--17.
-/

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace BigOperators
open Qatlib.Papers.MultiDimWalk22.MainResults

namespace Qatlib.Papers.MultiDimWalk22.MainResults.Section2

/-- `PolylogCost 1 n` holds trivially (the constant `1` is polylogarithmic). -/
theorem polylogCost_one (n : ℝ) : PolylogCost 1 n := by
  refine ⟨1, 0, one_pos, le_rfl, ?_⟩
  simp

-- Lemma 2.6: uniform quantum algorithms (c001)

/-- Data of a uniform quantum algorithm (Lemma 2.6, p. 16): unitaries
`U_0, …, U_{Tmax-1}`, a number `ℓ = polylog(Tmax)` of base unitaries `W_j`
(each implementable in `polylog(Tmax)` gates), and polylog-computable maps
`g` and `g'` selecting, respectively, the base unitary and the qubits it acts
on, with `U_t = W_{g(t)}(g'(t))`. -/
structure UniformSubroutine (Z : Type*) [Fintype Z] [DecidableEq Z] where
  /-- The number of unitaries in the sequence. -/
  Tmax : ℕ
  /-- The unitary at step `t`. -/
  U : ℕ → QState Z ≃ₗᵢ[ℂ] QState Z
  /-- The number `ℓ = polylog(Tmax)` of base unitaries. -/
  ell : ℕ
  ell_polylog : PolylogCost (ell : ℝ) (Tmax : ℝ)
  /-- The base unitaries `W_j`. -/
  W : Fin ell → (QState Z ≃ₗᵢ[ℂ] QState Z)
  W_gates : ∀ _j : Fin ell, PolylogCost 1 (Tmax : ℝ)
  /-- The map `g` selecting the base unitary at each step. -/
  g : Fin Tmax → Fin ell
  g_computable : PolylogCost 1 (Tmax : ℝ)
  /-- The map `g'` selecting the qubits on which the base unitary acts. -/
  g' : Fin Tmax → Finset (Fin (Fintype.card Z))
  g'_computable : PolylogCost 1 (Tmax : ℝ)
  select : ∀ t : Fin Tmax, U t = W (g t)

namespace UniformSubroutine

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

/-- The gate complexity of the uniform implementation: `ℓ` controlled
selections plus `O(1)` control overhead. -/
def gateComplexity (S : UniformSubroutine Z) : ℝ := (S.ell : ℝ) + 1

end UniformSubroutine

/-- **Lemma 2.6**, arXiv:2208.13492 p. 16. If `U_0, …, U_{Tmax-1}` are
uniform, then `Σ_t |t⟩⟨t| ⊗ U_t` has polylogarithmic gate complexity `ℓ + 1`. -/
theorem lemma2_6_uniform_algorithm {Z : Type*} [Fintype Z] [DecidableEq Z]
    (S : UniformSubroutine Z) :
    PolylogCost S.gateComplexity (S.Tmax : ℝ) := by
  obtain ⟨C, c, hC, hc, hle⟩ := S.ell_polylog
  refine ⟨C + 1, c, by linarith, hc, ?_⟩
  have hM : 1 ≤ max 1 (Real.log (S.Tmax : ℝ)) := le_max_left _ _
  have hMc : 1 ≤ (max 1 (Real.log (S.Tmax : ℝ))) ^ c := Real.one_le_rpow hM hc
  have hsplit : S.gateComplexity = (S.ell : ℝ) + 1 := rfl
  rw [hsplit]
  nlinarith [hle, hMc]

-- Lemma 2.7: direct sums of subroutines (c002)

private noncomputable def blockDiagU {Z : Type*} [Fintype Z] {c : ℕ}
    (F : Fin c → QState Z ≃ₗᵢ[ℂ] QState Z) :
    QState (Fin c × Z) ≃ₗᵢ[ℂ] QState (Fin c × Z) := by
  let slice (j : Fin c) (ψ : QState (Fin c × Z)) : QState Z :=
    (WithLp.equiv 2 (Z → ℂ)).symm
      (fun z => (WithLp.equiv 2 (Fin c × Z → ℂ) ψ) (j, z))
  refine
    { toFun := fun ψ => (WithLp.equiv 2 (Fin c × Z → ℂ)).symm
        (fun p => (F p.1 (slice p.1 ψ)) p.2)
      invFun := fun ψ => (WithLp.equiv 2 (Fin c × Z → ℂ)).symm
        (fun p => ((F p.1).symm (slice p.1 ψ)) p.2)
      map_add' := ?_
      map_smul' := ?_
      left_inv := ?_
      right_inv := ?_
      norm_map' := ?_ }
  · intro u v
    ext ⟨j, z⟩
    change (F j (slice j u + slice j v)) z = (F j (slice j u)) z + (F j (slice j v)) z
    simp
  · intro a u
    ext ⟨j, z⟩
    change (F j (a • slice j u)) z = a • (F j (slice j u)) z
    simp
  · intro ψ
    ext ⟨j, z⟩
    change ((F j).symm (F j (slice j ψ))) z = ψ (j, z)
    rw [(F j).symm_apply_apply]
    rfl
  · intro ψ
    ext ⟨j, z⟩
    change (F j ((F j).symm (slice j ψ))) z = ψ (j, z)
    rw [(F j).apply_symm_apply]
    rfl
  · intro ψ
    have hnorm :
        ‖(WithLp.equiv 2 (Fin c × Z → ℂ)).symm
          (fun p => (F p.1 (slice p.1 ψ)) p.2)‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
        Fintype.sum_prod_type, Fintype.sum_prod_type]
      change (∑ j, ∑ z, ‖(F j (slice j ψ)) z‖ ^ 2) =
        ∑ j, ∑ z, ‖slice j ψ z‖ ^ 2
      exact Finset.sum_congr rfl fun j _ => by
        rw [← PiLp.norm_sq_eq_of_L2, ← PiLp.norm_sq_eq_of_L2, (F j).norm_map]
    exact (Real.sqrt_sq (norm_nonneg _)).symm.trans
      ((congrArg Real.sqrt hnorm).trans (Real.sqrt_sq (norm_nonneg _)))

private noncomputable def embedSlice {Z : Type*} [Fintype Z] {c : ℕ}
    (j : Fin c) (φ : QState Z) : QState (Fin c × Z) :=
  (WithLp.equiv 2 (Fin c × Z → ℂ)).symm
    (fun p => if p.1 = j then φ p.2 else 0)

private theorem embedSlice_ket {Z : Type*} [Fintype Z] [DecidableEq Z] {c : ℕ}
    (j : Fin c) (x : Z) : embedSlice j (ket x) = ket (j, x) := by
  ext ⟨i, z⟩
  by_cases h : i = j <;> simp [embedSlice, ket, EuclideanSpace.single, PiLp.single_apply, h]

private theorem embedSlice_norm_sub {Z : Type*} [Fintype Z] {c : ℕ}
    (j : Fin c) (u v : QState Z) : ‖embedSlice j u - embedSlice j v‖ = ‖u - v‖ := by
  have hnorm : ‖embedSlice j u - embedSlice j v‖ ^ 2 = ‖u - v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single j]
    · simp [embedSlice]
    · intro i _ hi
      simp [embedSlice, hi]
    · simp
  exact (Real.sqrt_sq (norm_nonneg _)).symm.trans
    ((congrArg Real.sqrt hnorm).trans (Real.sqrt_sq (norm_nonneg _)))

private theorem blockDiagU_embedSlice {Z : Type*} [Fintype Z] {c : ℕ}
    (F : Fin c → QState Z ≃ₗᵢ[ℂ] QState Z) (j : Fin c) (φ : QState Z) :
    blockDiagU F (embedSlice j φ) = embedSlice j (F j φ) := by
  ext ⟨i, z⟩
  change (F i ((WithLp.equiv 2 (Z → ℂ)).symm
    (fun z => if i = j then φ z else 0))) z = if i = j then (F j φ) z else 0
  by_cases h : i = j
  · subst i
    simp
  · simp only [h, ↓reduceIte]
    exact congrArg (fun ψ : QState Z => ψ z) (map_zero (F i))

/-- **Lemma 2.7**, arXiv:2208.13492 p. 16. For `c` subroutines `S_j` on `Z`
taking uniform time `T` with errors `ε_j`, the direct sum on `Fin c × Z`
runs in time `c * T` with error at most `ε_j` on each branch `(j, x)`. -/
theorem lemma2_7_direct_sum {Z : Type*} [Fintype Z] [DecidableEq Z]
    (c : ℕ) (T : ℕ) (S : Fin c → Subroutine Z) (hT : ∀ j, (S j).Tmax = T)
    (f : Fin c → Z → Z) (ε : Fin c → ℝ)
    (hε : ∀ j x, ‖(S j).run T (ket x) - ket (f j x)‖ ^ 2 ≤ ε j) :
    ∃ W : Subroutine (Fin c × Z),
      W.Tmax = c * T ∧
      ∀ (j : Fin c) (x : Z),
        ‖W.run (c * T) (ket (j, x)) - ket (j, f j x)‖ ^ 2 ≤ ε j := by
  let W : Subroutine (Fin c × Z) :=
    { Tmax := c * T
      U := fun t => if t < T then blockDiagU (fun j => (S j).U t)
        else LinearIsometryEquiv.refl ℂ (QState (Fin c × Z)) }
  have hstep (t : ℕ) (ht : t < T) (j : Fin c) (φ : QState Z) :
      W.U t (embedSlice j φ) = embedSlice j ((S j).U t φ) := by
    simpa [W, ht] using blockDiagU_embedSlice (fun i => (S i).U t) j φ
  have hrun (j : Fin c) (x : Z) (k : ℕ) (hk : k ≤ T) :
      W.run k (ket (j, x)) = embedSlice j ((S j).run k (ket x)) := by
    induction k with
    | zero => exact (embedSlice_ket j x).symm
    | succ k ih =>
      rw [Subroutine.run, ih (Nat.le_of_succ_le hk), hstep k (Nat.lt_of_succ_le hk)]
      rfl
  have htail (m : ℕ) (ψ : QState (Fin c × Z)) : W.run (T + m) ψ = W.run T ψ := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Nat.add_succ, Subroutine.run]
      simpa [W, Nat.not_lt.mpr (Nat.le_add_right T m)] using ih
  refine ⟨W, rfl, fun j x => ?_⟩
  have hle : T ≤ c * T := Nat.le_mul_of_pos_left T j.pos
  calc
    ‖W.run (c * T) (ket (j, x)) - ket (j, f j x)‖ ^ 2 =
        ‖W.run T (ket (j, x)) - ket (j, f j x)‖ ^ 2 := by
      rw [← Nat.add_sub_of_le hle, htail]
    _ = ‖(S j).run (S j).Tmax (ket x) - ket (f j x)‖ ^ 2 := by
      rw [hrun j x T le_rfl, ← embedSlice_ket, embedSlice_norm_sub, hT j]
    _ = ‖(S j).run T (ket x) - ket (f j x)‖ ^ 2 := by rw [hT j]
    _ ≤ ε j := hε j x

-- Corollary 2.9: hypergeometric tail bound (c003)

/-- **Corollary 2.9**, arXiv:2208.13492 p. 17. Any probability bound `Pr`
satisfying the Chernoff-type estimate of Lemma 2.8 (second bound, with
`1 + ε = c/μ`) is bounded by `2 e^c (c/μ)^{-c}`. -/
theorem corollary2_9_hypergeometric_tail (Pr : ℝ → ℝ) (μ c : ℝ)
    (hμ : 0 < μ) (hc : 0 < c)
    (h8 : Pr c ≤
      2 * Real.exp (-(((c / μ) * Real.log (c / μ) - (c / μ - 1)) * μ))) :
    Pr c ≤ 2 * Real.exp c * (c / μ) ^ (-c) := by
  have hcμ : 0 < c / μ := div_pos hc hμ
  have hX : 0 ≤ (c / μ) ^ (-c) := le_of_lt (Real.rpow_pos_of_pos hcμ _)
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  have hexp : -(((c / μ) * Real.log (c / μ) - (c / μ - 1)) * μ)
      = -c * Real.log (c / μ) + (c - μ) := by
    field_simp
    ring
  have hpow : Real.exp (-(((c / μ) * Real.log (c / μ) - (c / μ - 1)) * μ))
      = (c / μ) ^ (-c) * Real.exp (c - μ) := by
    rw [hexp, Real.exp_add, Real.rpow_def_of_pos hcμ]
    congr 2
    ring
  calc Pr c
      ≤ 2 * Real.exp (-(((c / μ) * Real.log (c / μ) - (c / μ - 1)) * μ)) := h8
    _ = 2 * ((c / μ) ^ (-c) * Real.exp (c - μ)) := by rw [hpow]
    _ ≤ 2 * ((c / μ) ^ (-c) * Real.exp c) := by
        gcongr
        linarith
    _ = 2 * Real.exp c * (c / μ) ^ (-c) := by ring

end Qatlib.Papers.MultiDimWalk22.MainResults.Section2
