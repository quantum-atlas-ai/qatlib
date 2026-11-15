/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra.BlockFormPerturbation
open scoped BigOperators

noncomputable def qForm {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (v : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, star (v i) * A i j * v j

def BlockDiagonal {N d : ℕ}
    (A : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ) : Prop :=
  ∀ P P' : Fin N, P ≠ P' → ∀ a b : Fin d, A (P, a) (P', b) = 0

def EntrywiseBound {N d : ℕ}
    (L : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ) (ε : ℝ) : Prop :=
  ∀ i j : Fin N × Fin d, ‖L i j‖ ≤ ε

def SectorBound {N d : ℕ}
    (G M : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ) (Λ m : ℝ) : Prop :=
  ∀ w : Fin N × Fin d → ℂ,
    (qForm G w).re ≤ (Λ - m) * (qForm M w).re

def Coercive {N d : ℕ}
    (M : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ) (μ : ℝ) : Prop :=
  ∀ v : Fin N × Fin d → ℂ,
    μ * (∑ i, ‖v i‖ ^ 2) ≤ (qForm M v).re

def RealForm {N d : ℕ}
    (A : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ) : Prop :=
  ∀ w : Fin N × Fin d → ℂ, (qForm A w).im = 0

def PositiveForm {N d : ℕ}
    (A : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ) : Prop :=
  ∀ w : Fin N × Fin d → ℂ, 0 ≤ (qForm A w).re

/-- The quadratic form `qForm` is additive in its matrix argument. -/
theorem qForm_add {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) (v : ι → ℂ) :
    qForm (A + B) v = qForm A v + qForm B v := by
  simp [qForm, Matrix.add_apply, Finset.sum_add_distrib, mul_add,
    add_mul]

/-- An entrywise bound on `L` bounds its quadratic-form norm by the total dimension times that
bound times the vector squared norm. -/
theorem qForm_le_bound {N d : ℕ}
    (L : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ) (ε : ℝ)
    (hε : 0 ≤ ε) (hL : EntrywiseBound L ε)
    (v : Fin N × Fin d → ℂ) :
    ‖qForm L v‖ ≤ (N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2) := by
  have h1 : ‖qForm L v‖ ≤ ∑ i, ∑ j, ‖v i‖ * ‖L i j‖ * ‖v j‖ := by
    rw [qForm]
    calc ‖∑ i, ∑ j, star (v i) * L i j * v j‖
        ≤ ∑ i, ‖∑ j, star (v i) * L i j * v j‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖v i‖ * ‖L i j‖ * ‖v j‖ := by
          apply Finset.sum_le_sum
          intro i _
          calc ‖∑ j, star (v i) * L i j * v j‖
              ≤ ∑ j, ‖star (v i) * L i j * v j‖ := norm_sum_le _ _
            _ ≤ ∑ j, ‖v i‖ * ‖L i j‖ * ‖v j‖ := by
                apply Finset.sum_le_sum
                intro j _
                rw [norm_mul, norm_mul, norm_star]
  have h2 : ∑ i, ∑ j, ‖v i‖ * ‖L i j‖ * ‖v j‖
      ≤ ε * (∑ i, ‖v i‖) * (∑ i, ‖v i‖) := by
    have hexp : ε * (∑ i, ‖v i‖) * (∑ i, ‖v i‖)
        = ∑ i, ∑ j, ‖v i‖ * ε * ‖v j‖ := by
      rw [show ε * (∑ i, ‖v i‖) * (∑ i, ‖v i‖)
          = ε * ((∑ i, ‖v i‖) * (∑ i, ‖v i‖)) from by ring,
        Finset.sum_mul_sum]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hexp]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hL i j) (norm_nonneg _))
      (norm_nonneg _)
  have h3 : (∑ i, ‖v i‖) * (∑ i, ‖v i‖)
      ≤ ((Finset.univ : Finset (Fin N × Fin d)).card : ℝ)
        * (∑ i, ‖v i‖ ^ 2) := by
    have hpair : ∀ i j : Fin N × Fin d,
        2 * ((‖v i‖ : ℝ) * ‖v j‖) ≤ ‖v i‖ ^ 2 + ‖v j‖ ^ 2 := by
      intro i j
      nlinarith [sq_nonneg ((‖v i‖ : ℝ) - ‖v j‖)]
    have c1 : ∑ i : Fin N × Fin d, ∑ j : Fin N × Fin d, (‖v i‖ ^ 2)
        = ((Finset.univ : Finset (Fin N × Fin d)).card : ℝ)
          * ∑ i, ‖v i‖ ^ 2 := by
      simp [Finset.sum_const]
      rw [← Finset.mul_sum]
    have c2 : ∑ i : Fin N × Fin d, ∑ j : Fin N × Fin d, (‖v j‖ ^ 2)
        = ((Finset.univ : Finset (Fin N × Fin d)).card : ℝ)
          * ∑ i, ‖v i‖ ^ 2 := by
      rw [Finset.sum_comm]
      simp [Finset.sum_const]
      rw [← Finset.mul_sum]
    have hexp : (∑ i, ‖v i‖) * (∑ i, ‖v i‖)
        = ∑ i : Fin N × Fin d, ∑ j : Fin N × Fin d, ‖v i‖ * ‖v j‖ := by
      rw [Finset.sum_mul_sum]
    have hsum : ∑ i : Fin N × Fin d, ∑ j : Fin N × Fin d,
          (‖v i‖ ^ 2 + ‖v j‖ ^ 2)
        = 2 * ((Finset.univ : Finset (Fin N × Fin d)).card : ℝ)
          * (∑ i, ‖v i‖ ^ 2) := by
      simp only [Finset.sum_add_distrib]
      rw [c1, c2]
      ring
    have hscale : 2 * (∑ i : Fin N × Fin d, ∑ j : Fin N × Fin d,
          ‖v i‖ * ‖v j‖)
        = ∑ i : Fin N × Fin d, ∑ j : Fin N × Fin d,
            (2 * (‖v i‖ * ‖v j‖)) := by
      have hsplit2 : (∑ i : Fin N × Fin d, ∑ j : Fin N × Fin d,
            ‖v i‖ * ‖v j‖)
          + (∑ i : Fin N × Fin d, ∑ j : Fin N × Fin d, ‖v i‖ * ‖v j‖)
          = ∑ i : Fin N × Fin d, ∑ j : Fin N × Fin d,
              (‖v i‖ * ‖v j‖ + ‖v i‖ * ‖v j‖) := by
        simp only [Finset.sum_add_distrib]
      rw [two_mul, hsplit2]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hmain : 2 * ((∑ i, ‖v i‖) * (∑ i, ‖v i‖))
        ≤ 2 * (((Finset.univ : Finset (Fin N × Fin d)).card : ℝ)
          * (∑ i, ‖v i‖ ^ 2)) := by
      rw [hexp, hscale]
      calc ∑ i : Fin N × Fin d, ∑ j : Fin N × Fin d,
            (2 * (‖v i‖ * ‖v j‖))
          ≤ ∑ i : Fin N × Fin d, ∑ j : Fin N × Fin d,
              (‖v i‖ ^ 2 + ‖v j‖ ^ 2) :=
              Finset.sum_le_sum (fun i _ =>
                Finset.sum_le_sum (fun j _ => hpair i j))
        _ = 2 * (((Finset.univ : Finset (Fin N × Fin d)).card : ℝ)
            * (∑ i, ‖v i‖ ^ 2)) := by
            rw [hsum]
            ring
    linarith [hmain]
  have hcard : ((Finset.univ : Finset (Fin N × Fin d)).card : ℝ)
      = (N : ℝ) * (d : ℝ) := by
    simp [Fintype.card_prod, Fintype.card_fin]
  calc ‖qForm L v‖ ≤ ε * (∑ i, ‖v i‖) * (∑ i, ‖v i‖) :=
      le_trans h1 h2
    _ ≤ ε * ((N : ℝ) * (d : ℝ) * (∑ i, ‖v i‖ ^ 2)) := by
        have hle : (∑ i, ‖v i‖) * (∑ i, ‖v i‖)
            ≤ (N : ℝ) * (d : ℝ) * (∑ i, ‖v i‖ ^ 2) := by
          rw [← hcard]
          exact h3
        have hassoc : (ε * ∑ i, ‖v i‖) * ∑ i, ‖v i‖
            = ε * ((∑ i, ‖v i‖) * ∑ i, ‖v i‖) := by ring
        rw [hassoc]
        exact mul_le_mul_of_nonneg_left hle hε
    _ = (N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2) := by ring

/-- Under the block coercivity, sector, and perturbation-budget assumptions, bounds the real
form quotient by the sector bound minus half its margin. -/
theorem quotient_bound {N d : ℕ} {Λ m μ ε : ℝ}
    {G L_G M L_M G_blk M_blk : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ}
    (hG : G = G_blk + L_G) (hM : M = M_blk + L_M)
    (_hBD_G : BlockDiagonal G_blk) (_hBD_M : BlockDiagonal M_blk)
    (hRF_G : RealForm G_blk) (_hRF_M : RealForm M_blk)
    (hPSD : PositiveForm G_blk)
    (hLB_G : EntrywiseBound L_G ε) (hLB_M : EntrywiseBound L_M ε)
    (hCoe : Coercive M_blk μ)
    (hSB : SectorBound G_blk M_blk Λ m)
    (hμ : 0 < μ) (hm : 0 < m) (hε : 0 ≤ ε) (hΛ : 1 ≤ Λ) (hmΛ : m ≤ Λ)
    (hReg : (N : ℝ) * (d : ℝ) * ε ≤ μ * m / (2 * (1 + Λ))) :
    ∀ v : Fin N × Fin d → ℂ, qForm M v ≠ 0 →
      (qForm G v / qForm M v).re ≤ Λ - m / 2 := by
  have hbre : ∀ z : ℂ, -‖z‖ ≤ z.re := by
    intro z
    have h1 : (-z).re ≤ ‖-z‖ := Complex.re_le_norm (-z)
    rw [norm_neg, Complex.neg_re] at h1
    linarith
  intro v hvM
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hvM (by simp [qForm])
  have hu : 0 < ∑ i, ‖v i‖ ^ 2 := by
    by_contra hcon
    push Not at hcon
    have hsum0 : ∑ i, ‖v i‖ ^ 2 = 0 :=
      le_antisymm hcon (Finset.sum_nonneg (fun i _ => sq_nonneg (‖v i‖)))
    have hz : ∀ i, ‖v i‖ = 0 := by
      intro i
      have hmem := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (‖v j‖))).mp hsum0 i
      have h2 : (‖v i‖ : ℝ) = 0 :=
        sq_eq_zero_iff.mp (hmem (Finset.mem_univ i))
      exact h2
    exact hv0 (funext fun i => (@norm_eq_zero ℂ _ (v i)).mp (hz i))
  have hAμ : μ * (∑ i, ‖v i‖ ^ 2) ≤ (qForm M_blk v).re :=
    hCoe v
  have hLG : ‖qForm L_G v‖
      ≤ (N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2) :=
    qForm_le_bound L_G ε hε hLB_G v
  have hLM : ‖qForm L_M v‖
      ≤ (N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2) :=
    qForm_le_bound L_M ε hε hLB_M v

  have hRegU : (N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2)
      ≤ (μ * m / (2 * (1 + Λ))) * (∑ i, ‖v i‖ ^ 2) :=
    mul_le_mul_of_nonneg_right hReg (Finset.sum_nonneg
      (fun i _ => sq_nonneg (‖v i‖)))
  have hAδpos : 0 < (qForm M_blk v).re
      - (N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2) := by
    have hhalf : (μ * m / (2 * (1 + Λ))) * (∑ i, ‖v i‖ ^ 2)
        ≤ μ * (∑ i, ‖v i‖ ^ 2) / 2 := by
      have h2 : m / (2 * (1 + Λ)) ≤ 1 / 2 := by
        have hd : (0 : ℝ) < 2 * (1 + Λ) := by nlinarith [hΛ]
        field_simp [hd]
        nlinarith [hmΛ]
      calc (μ * m / (2 * (1 + Λ))) * (∑ i, ‖v i‖ ^ 2)
          = μ * (∑ i, ‖v i‖ ^ 2) * (m / (2 * (1 + Λ))) := by ring
        _ ≤ μ * (∑ i, ‖v i‖ ^ 2) * (1 / 2) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = μ * (∑ i, ‖v i‖ ^ 2) / 2 := by ring
    have h1 := le_trans hRegU hhalf
    have h2 : μ * (∑ i, ‖v i‖ ^ 2) - μ * (∑ i, ‖v i‖ ^ 2) / 2
        = μ * (∑ i, ‖v i‖ ^ 2) / 2 := by ring
    nlinarith [hAμ, h1, h2, hμ, hu]

  have hReMlb : (qForm M_blk v).re
      - (N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2) ≤ (qForm M v).re := by
    have h1 : (qForm M v).re
        = (qForm M_blk v).re + (qForm L_M v).re := by
      rw [hM, qForm_add, Complex.add_re]
    have h2 : -((N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2))
        ≤ (qForm L_M v).re :=
      le_trans (neg_le_neg hLM) (hbre _)
    linarith
  have habsMlb : (qForm M_blk v).re
      - (N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2)
      ≤ ‖qForm M v‖ :=
    le_trans (le_trans hReMlb (le_abs_self _)) (Complex.abs_re_le_norm _)

  have hGblk_eq : ‖qForm G_blk v‖ = (qForm G_blk v).re := by
    have him0 : (qForm G_blk v).im = 0 := hRF_G v
    have habs : ‖qForm G_blk v‖ = |(qForm G_blk v).re| :=
      (Complex.abs_re_eq_norm.mpr him0).symm
    rw [habs]
    exact abs_of_nonneg (hPSD v)
  have hReG_blk : (qForm G_blk v).re
      ≤ (Λ - m) * (qForm M_blk v).re := hSB v
  have habsG : ‖qForm G v‖
      ≤ (Λ - m) * (qForm M_blk v).re
        + (N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2) := by
    have h1 : ‖qForm G v‖
        ≤ ‖qForm G_blk v‖ + ‖qForm L_G v‖ := by
      rw [hG, qForm_add]
      exact norm_add_le _ _
    calc ‖qForm G v‖
        ≤ ‖qForm G_blk v‖ + ‖qForm L_G v‖ := h1
      _ = (qForm G_blk v).re + ‖qForm L_G v‖ := by rw [hGblk_eq]
      _ ≤ (Λ - m) * (qForm M_blk v).re
          + (N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2) :=
          add_le_add hReG_blk hLG

  have hquot : (qForm G v / qForm M v).re
      ≤ ‖qForm G v‖ / ‖qForm M v‖ := by
    have h1 := Complex.re_le_norm (qForm G v / qForm M v)
    rw [norm_div] at h1
    exact h1

  have hkey : (N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2) * (1 + Λ - m / 2)
      ≤ (m / 2) * (qForm M_blk v).re := by
    have hnonneg : 0 ≤ (N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2) := by
      positivity
    have hstep1 : 1 + Λ - m / 2 ≤ 1 + Λ := by nlinarith [le_of_lt hm]
    calc (N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2) * (1 + Λ - m / 2)
        ≤ (N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2) * (1 + Λ) :=
            mul_le_mul_of_nonneg_left hstep1 hnonneg
      _ ≤ (μ * m / (2 * (1 + Λ))) * (∑ i, ‖v i‖ ^ 2) * (1 + Λ) := by
            have hpos : (0 : ℝ) ≤ 1 + Λ := by linarith
            exact mul_le_mul_of_nonneg_right hRegU hpos
      _ = (m / 2) * (μ * (∑ i, ‖v i‖ ^ 2)) := by
            have hd : (0 : ℝ) < 2 * (1 + Λ) := by nlinarith [hΛ]
            field_simp [hd]
      _ ≤ (m / 2) * (qForm M_blk v).re :=
            mul_le_mul_of_nonneg_left hAμ (by positivity)
  have hMpos : 0 < ‖qForm M v‖ :=
    lt_of_lt_of_le hAδpos habsMlb
  have hfin : ‖qForm G v‖ / ‖qForm M v‖ ≤ Λ - m / 2 := by
    rw [div_le_iff₀ hMpos]
    calc ‖qForm G v‖
        ≤ (Λ - m / 2) * ((qForm M_blk v).re
            - (N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2)) := by
          have hexpand : (Λ - m / 2) * ((qForm M_blk v).re
              - (N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2))
              = ((Λ - m) * (qForm M_blk v).re
                + (N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2))
                + ((m / 2) * (qForm M_blk v).re
                  - (N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2)
                    * (1 + Λ - m / 2)) := by ring
          rw [hexpand]
          have h2le : (0 : ℝ) ≤ (m / 2) * (qForm M_blk v).re
              - (N : ℝ) * (d : ℝ) * ε * (∑ i, ‖v i‖ ^ 2)
                * (1 + Λ - m / 2) := by linarith [hkey]
          linarith [habsG, h2le]
      _ ≤ (Λ - m / 2) * ‖qForm M v‖ :=
            mul_le_mul_of_nonneg_left habsMlb (by linarith)
  exact le_trans hquot hfin

/-- Taking real parts commutes with a finite complex sum. -/
theorem sum_re {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    (∑ i, f i).re = ∑ i, (f i).re := by
  have := Classical.decEq ι
  have hind : ∀ s : Finset ι, ∀ g : ι → ℂ,
      (∑ i ∈ s, g i).re = ∑ i ∈ s, (g i).re := by
    intro s
    induction s using Finset.induction with
    | empty => intro g; simp
    | insert x s hx ih =>
      intro g
      rw [Finset.sum_insert hx, Finset.sum_insert hx, Complex.add_re,
        ih g]
  exact hind Finset.univ f

noncomputable def blockComponent {N d : ℕ} (v : Fin N × Fin d → ℂ)
    (P : Fin N) : Fin N × Fin d → ℂ :=
  fun x => if x.1 = P then v x else 0

/-- The block component of `v` at `P` vanishes on every other block. -/
theorem blockComponent_supported {N d : ℕ} (v : Fin N × Fin d → ℂ)
    (P : Fin N) : ∀ Q a, Q ≠ P → blockComponent v P (Q, a) = 0 := by
  intro Q a hne
  unfold blockComponent
  change (if Q = P then v (Q, a) else 0) = 0
  rw [ite_eq_right hne]

/-- The block component of `v` at `P` agrees with `v` on that block. -/
theorem blockComponent_self {N d : ℕ} (v : Fin N × Fin d → ℂ)
    (P : Fin N) (a : Fin d) :
    blockComponent v P (P, a) = v (P, a) := by
  unfold blockComponent
  simp only [ite_true]

/-- The quadratic form of a block-diagonal matrix splits into the sum of its within-block entry
contributions. -/
theorem qForm_blockdiag_split {N d : ℕ}
    (A : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ)
    (hA : BlockDiagonal A) (v : Fin N × Fin d → ℂ) :
    qForm A v
      = ∑ P, ∑ a, ∑ b, star (v (P, a)) * A (P, a) (P, b) * v (P, b) := by
  simp only [qForm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro P _
  apply Finset.sum_congr rfl
  intro a _
  refine (Finset.sum_eq_single P ?_ ?_).trans ?_
  · intro P' _ hne
    apply Finset.sum_eq_zero
    intro b _
    rw [hA P P' (Ne.symm hne) a b, mul_zero, zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ P) hcon
  · rfl

/-- The quadratic form on one block component is the entry sum for that block. -/
theorem qForm_blockcomp_eq {N d : ℕ}
    (A : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ)
    (hA : BlockDiagonal A) (v : Fin N × Fin d → ℂ) (P : Fin N) :
    qForm A (blockComponent v P)
      = ∑ a, ∑ b, star (v (P, a)) * A (P, a) (P, b) * v (P, b) := by
  rw [qForm_blockdiag_split A hA (blockComponent v P)]
  refine (Finset.sum_eq_single P ?_ ?_).trans ?_
  · intro Q _ hne
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    show star (blockComponent v P (Q, a)) * A (Q, a) (Q, b)
      * blockComponent v P (Q, b) = 0
    rw [blockComponent_supported v P Q a hne, star_zero]
    simp
  · intro hcon
    exact absurd (Finset.mem_univ P) hcon
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [blockComponent_self v P a, blockComponent_self v P b]

/-- The quadratic form of a block-diagonal matrix is the sum of its values on the vector block
components. -/
theorem qForm_blockdiag_split' {N d : ℕ}
    (A : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ)
    (hA : BlockDiagonal A) (v : Fin N × Fin d → ℂ) :
    qForm A v = ∑ P, qForm A (blockComponent v P) := by
  rw [qForm_blockdiag_split A hA v]
  exact Finset.sum_congr rfl
    (fun P _ => (qForm_blockcomp_eq A hA v P).symm)

/-- For block-diagonal matrices, the same form bound on every individually supported block
implies the global sector bound. -/
theorem SectorBound_of_blocks {N d : ℕ} (Λ m : ℝ)
    (G M : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ)
    (hG : BlockDiagonal G) (hM : BlockDiagonal M)
    (hper : ∀ P : Fin N, ∀ w : Fin N × Fin d → ℂ,
      (∀ Q a, Q ≠ P → w (Q, a) = 0) →
        (qForm G w).re ≤ (Λ - m) * (qForm M w).re) :
    SectorBound G M Λ m := by
  intro v
  rw [qForm_blockdiag_split' G hG v,
    qForm_blockdiag_split' M hM v, sum_re, sum_re]
  calc (∑ P, (qForm G (blockComponent v P)).re)
      ≤ ∑ P, (Λ - m) * (qForm M (blockComponent v P)).re :=
          Finset.sum_le_sum
            (fun P _ => hper P _ (blockComponent_supported v P))
    _ = (Λ - m) * (∑ P, (qForm M (blockComponent v P)).re) :=
          (Finset.mul_sum _ _ _).symm

end Qatlib.Concepts.QuantumGibbs.FormAlgebra.BlockFormPerturbation
