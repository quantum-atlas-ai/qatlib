/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GWSpeedupYuan25.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# Goemans–Williamson with Pauli sparsity — diagonal constraints (Lemma 10)

Fixed arXiv:2510.08292v1 (9 Oct 2025).

Paper statement (Lemma 10, §III A, p.~11, PDF line 757):
For a density matrix `ρ` on `n` qubits, the following are equivalent:
* every diagonal entry satisfies `⟨i|ρ|i⟩ = 2^{-n}`;
* `tr[Z_A ρ] = 0` for every non-empty subset `A ⊆ [n]`.

This file states both directions as one `↔` theorem over the register model of
`Definitions.lean` (`Reg n = Fin n → Bool`, `ZMat n A = Z_A`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GWSpeedupYuan25.MainResults.Relaxation

open Matrix Qatlib.Papers.GWSpeedupYuan25.MainResults
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- The Walsh character `χ_s(x) = ∏_i (-1)^{s_i ∧ x_i}` of the Boolean cube
`(Z/2)^n`, indexed by a bit string `s`; `χ_s` is the character of the subset
`{i | s i = true}`, whose diagonal Pauli sign `zSign` it reproduces. -/
private def chi (n : ℕ) (s x : Reg n) : ℂ :=
  ∏ i, if s i = true ∧ x i = true then (-1 : ℂ) else 1

/-- `χ_s` computes the diagonal sign `zSign` of the subset it indexes
(the "indicator" string of `A` has character `z_A`). -/
private theorem chi_eq_zSign (n : ℕ) (A : Finset (Fin n)) (x : Reg n) :
    chi n (fun i => decide (i ∈ A)) x = zSign n A x := by
  classical
  unfold chi zSign
  calc (∏ i, if (fun i => decide (i ∈ A)) i = true ∧ x i = true then (-1 : ℂ) else 1)
      = ∏ i ∈ (Finset.univ : Finset (Fin n)),
          (if i ∈ A then (if x i = true then (-1 : ℂ) else 1) else 1) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases h1 : i ∈ A <;> by_cases h2 : x i = true <;> simp [h1, h2]
    _ = ∏ i ∈ A, (if x i = true then (-1 : ℂ) else 1) := by
        refine (Finset.prod_subset (Finset.subset_univ A)
          (fun i _ hi => by simp [hi])).symm.trans ?_
        exact Finset.prod_congr rfl fun i hi => by simp [hi]
    _ = ∏ i ∈ A, (if x i then (-1 : ℂ) else 1) := by
        exact Finset.prod_congr rfl fun i _ => by cases x i <;> rfl

/-- Row orthogonality of the characters: summing `χ_s` over the cube gives `2^n`
for the trivial character `s = 0` and `0` otherwise (a factor `1 + (-1)` dies
whenever `s i = true`). -/
private theorem chi_sum (n : ℕ) (s : Reg n) :
    ∑ x : Reg n, chi n s x
      = if s = (fun _ => false) then (2 : ℂ) ^ n else 0 := by
  classical
  calc ∑ x : Reg n, chi n s x
      = ∑ x ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset Bool)),
          ∏ i, (if s i = true ∧ x i = true then (-1 : ℂ) else 1) := by
        rw [Fintype.piFinset_univ]
        exact Finset.sum_congr rfl fun x _ => rfl
    _ = ∏ i, ∑ b ∈ (Finset.univ : Finset Bool),
          (if s i = true ∧ b = true then (-1 : ℂ) else 1) :=
          Finset.sum_prod_piFinset (Finset.univ : Finset Bool)
            (fun (i : Fin n) (b : Bool) => if s i = true ∧ b = true then (-1 : ℂ) else 1)
    _ = if s = (fun _ => false) then (2 : ℂ) ^ n else 0 := by
        by_cases hs : s = (fun _ => false)
        · subst hs
          have hfac : ∀ i : Fin n, ∑ b ∈ (Finset.univ : Finset Bool),
              (if (fun _ => false) i = true ∧ b = true then (-1 : ℂ) else 1) = 2 := by
            intro i
            show (∑ b ∈ (Finset.univ : Finset Bool),
                (if false = true ∧ b = true then (-1 : ℂ) else 1)) = 2
            rw [Fintype.univ_bool]
            simp
            try ring
          rw [if_pos rfl, Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]
        · obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin n, s i₀ = true := by
            by_contra hcon; push_neg at hcon
            exact hs (funext fun i => Bool.eq_false_iff.mpr (hcon i))
          rw [Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀]; try ring)]
          simp [hs]

/-- Dual orthogonality of the characters: summing the pointwise product
`χ_s x * χ_s y` over all characters `s` gives `2^n` when `x = y` and `0`
otherwise. This is the Fourier-inversion engine of Lemma 10. -/
private theorem chi_dual (n : ℕ) (x y : Reg n) :
    ∑ s : Reg n, chi n s x * chi n s y
      = if x = y then (2 : ℂ) ^ n else 0 := by
  classical
  have key : ∀ s : Reg n, chi n s x * chi n s y
      = ∏ i, (if s i = true ∧ x i = true then (-1 : ℂ) else 1) *
          (if s i = true ∧ y i = true then (-1 : ℂ) else 1) := by
    intro s
    unfold chi
    rw [Finset.prod_mul_distrib]
  calc ∑ s : Reg n, chi n s x * chi n s y
      = ∑ s ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset Bool)),
          ∏ i, ((if s i = true ∧ x i = true then (-1 : ℂ) else 1) *
            (if s i = true ∧ y i = true then (-1 : ℂ) else 1)) := by
        rw [Fintype.piFinset_univ]
        exact Finset.sum_congr rfl fun s _ => key s
    _ = ∏ i, ∑ b ∈ (Finset.univ : Finset Bool),
          ((if b = true ∧ x i = true then (-1 : ℂ) else 1) *
            (if b = true ∧ y i = true then (-1 : ℂ) else 1)) :=
          Finset.sum_prod_piFinset (Finset.univ : Finset Bool)
            (fun (i : Fin n) (b : Bool) => (if b = true ∧ x i = true then (-1 : ℂ) else 1) *
              (if b = true ∧ y i = true then (-1 : ℂ) else 1))
    _ = if x = y then (2 : ℂ) ^ n else 0 := by
        by_cases hxy : x = y
        · subst hxy
          have hfac : ∀ i : Fin n, ∑ b ∈ (Finset.univ : Finset Bool),
              ((if b = true ∧ x i = true then (-1 : ℂ) else 1) *
                (if b = true ∧ x i = true then (-1 : ℂ) else 1)) = 2 := by
            intro i
            rw [Fintype.univ_bool]
            cases hx : x i <;> simp [hx] <;> try ring
          rw [if_pos rfl, Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]
        · obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin n, x i₀ ≠ y i₀ := by
            by_contra hcon; push_neg at hcon; exact hxy (funext hcon)
          rw [Finset.prod_eq_zero (Finset.mem_univ i₀) ?_]
          · simp [hxy]
          · revert hi₀
            cases hx : x i₀ <;> cases hy : y i₀ <;> simp <;> try ring

/-- The diagonal trace identity `tr[Z_A ρ] = ∑_x z_A(x) ρ_xx`. -/
private theorem zMat_trace (n : ℕ) (A : Finset (Fin n))
    (ρ : Matrix (Reg n) (Reg n) ℂ) :
    (ZMat n A * ρ).trace = ∑ x : Reg n, zSign n A x * ρ x x := by
  simp only [Matrix.trace, ZMat]
  exact Finset.sum_congr rfl fun x _ => Matrix.diagonal_mul _ _ x x

/-- Forward direction of Lemma 10, isolated for reuse:
constant diagonal `2^{-n}` forces all traceless constraints `tr[Z_A ρ] = 0`
(`A ≠ ∅`). -/
theorem lemma10_diagonal_implies_traces (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hρ : IsDensity ρ)
    (hdiag : ∀ x : Reg n, ρ x x = ((2 : ℂ) ^ n)⁻¹) :
    ∀ A : Finset (Fin n), A ≠ ∅ → (ZMat n A * ρ).trace = 0 := by
  intro A hA
  have hsum : ∑ x : Reg n, zSign n A x = 0 := by
    have h2 : ∑ x : Reg n, zSign n A x
        = ∑ x : Reg n, chi n (fun i => decide (i ∈ A)) x :=
      Finset.sum_congr rfl fun x _ => (chi_eq_zSign n A x).symm
    rw [h2, chi_sum n (fun i => decide (i ∈ A)), if_neg ?_]
    intro hc
    refine hA (Finset.ext fun i => ?_)
    have := congrFun hc i
    simpa using this
  have hterm : ∀ x : Reg n, zSign n A x * ρ x x
      = ((2 : ℂ) ^ n)⁻¹ * zSign n A x := fun x => by rw [hdiag x]; ring
  rw [zMat_trace, Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum,
    hsum, mul_zero]

/-- Backward direction of Lemma 10, isolated for reuse:
vanishing traceless constraints `tr[Z_A ρ] = 0` (`A ≠ ∅`) force the flat
diagonal `2^{-n}`. -/
theorem lemma10_traces_implies_diagonal (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hρ : IsDensity ρ)
    (htr : ∀ A : Finset (Fin n), A ≠ ∅ → (ZMat n A * ρ).trace = 0) :
    ∀ x : Reg n, ρ x x = ((2 : ℂ) ^ n)⁻¹ := by
  classical
  intro x
  -- Every character sum of the diagonal of `ρ` is `1` at `s = 0` and `0` else.
  have hF : ∀ s : Reg n, ∑ y : Reg n, chi n s y * ρ y y
      = if s = (fun _ => false) then 1 else 0 := by
    intro s
    by_cases hs : s = (fun _ => false)
    · subst hs
      have hchi0 : ∀ y : Reg n, chi n (fun _ => false) y = 1 := by
        intro y; simp [chi]
      rw [Finset.sum_congr rfl (fun y _ => by rw [hchi0 y, one_mul])]
      simpa [Matrix.trace, Matrix.diag] using hρ.2
    · obtain ⟨i, hi⟩ : ∃ i : Fin n, s i = true := by
        by_contra hcon; push_neg at hcon
        exact hs (funext fun i => Bool.eq_false_iff.mpr (hcon i))
      have hAmem : i ∈ Finset.univ.filter (fun i => s i = true) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      have hAne : (Finset.univ.filter (fun i => s i = true)) ≠ ∅ :=
        Finset.nonempty_iff_ne_empty.mp ⟨i, hAmem⟩
      have h1 : (ZMat n (Finset.univ.filter (fun i => s i = true)) * ρ).trace = 0 :=
        htr _ hAne
      rw [zMat_trace] at h1
      have hsA : s = fun i => decide (i ∈ Finset.univ.filter (fun i => s i = true)) := by
        funext i
        by_cases hsi : s i = true
        · simp [hsi, Finset.mem_filter]
        · simp [hsi, Finset.mem_filter]
      rw [if_neg hs, ← h1]
      refine Finset.sum_congr rfl fun y _ => ?_
      have h2 := chi_eq_zSign n (Finset.univ.filter (fun i => s i = true)) y
      conv_lhs => rw [hsA]
      rw [h2]
  -- Fourier inversion of the diagonal at `x`.
  have hmain : ∑ s : Reg n, chi n s x * (∑ y : Reg n, chi n s y * ρ y y)
      = (2 : ℂ) ^ n * ρ x x := by
    have hswap : ∑ s : Reg n, chi n s x * (∑ y : Reg n, chi n s y * ρ y y)
        = ∑ y : Reg n, ρ y y * (∑ s : Reg n, chi n s x * chi n s y) := by
      have e1 : ∀ s : Reg n, chi n s x * (∑ y : Reg n, chi n s y * ρ y y)
          = ∑ y : Reg n, chi n s x * (chi n s y * ρ y y) :=
        fun s => Finset.mul_sum _ _ _
      have e2 : ∀ y : Reg n, ρ y y * (∑ s : Reg n, chi n s x * chi n s y)
          = ∑ s : Reg n, ρ y y * (chi n s x * chi n s y) :=
        fun y => Finset.mul_sum _ _ _
      simp only [e1, e2]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun s _ => by ring
    rw [hswap, Finset.sum_congr rfl (fun y _ => by rw [chi_dual])]
    simp [mul_comm]
  rw [Finset.sum_congr rfl (fun s _ => by rw [hF s])] at hmain
  have hsingle : ∑ s : Reg n, chi n s x *
      (if s = (fun _ => false) then (1 : ℂ) else 0) = chi n (fun _ => false) x := by
    rw [Finset.sum_eq_single (fun _ => false)]
    · simp [chi]
    · intro b _ hb; simp [hb]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  rw [hsingle] at hmain
  have hchi0 : chi n (fun _ => false) x = 1 := by simp [chi]
  rw [hchi0] at hmain
  have hfin2 : ((2 : ℂ) ^ n)⁻¹ = ((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n * ρ x x) := by
    rw [← hmain, mul_one]
  rw [inv_mul_cancel_left₀ (pow_ne_zero n two_ne_zero)] at hfin2
  exact hfin2.symm

/-- Lemma 10 (arXiv:2510.08292v1, §III A, p.~11, Eq. (25)–(26)):
a density matrix `ρ` has all diagonal entries equal to `2^{-n}` iff all
traceless-diagonal-RDM constraints `tr[Z_A ρ] = 0` (`A ≠ ∅`) vanish. -/
theorem lemma10_diagonal_iff_traces (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hρ : IsDensity ρ) :
    (∀ x : Reg n, ρ x x = ((2 : ℂ) ^ n)⁻¹) ↔
      (∀ A : Finset (Fin n), A ≠ ∅ → (ZMat n A * ρ).trace = 0) :=
  ⟨lemma10_diagonal_implies_traces n ρ hρ,
    lemma10_traces_implies_diagonal n ρ hρ⟩

end Qatlib.Papers.GWSpeedupYuan25.MainResults.Relaxation
