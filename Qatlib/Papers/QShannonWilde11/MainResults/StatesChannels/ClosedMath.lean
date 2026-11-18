/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.Model.SourceModel

@[expose] public section


/-!
# Reviewed closed fragment of Wilde, arXiv:1106.1445v8

Only closed definitions and proofs are present. Capacity records have unconstrained
fields; conditional limits and averaging steps do not establish operational coding
or source algorithm costs. See the per-declaration source review receipt.
-/

namespace Qatlib.Papers.QShannonWilde11.MainResults.StatesChannels

open Matrix
open Qatlib.Papers.QShannonWilde11.MainResults.Model
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open scoped BigOperators ComplexOrder ENNReal

noncomputable section

/-- **Isometric extension from Kraus operators** — arXiv:1106.1445v8,
Eqs. (5.35)–(5.36), fixed PDF p. 192. For a Kraus family `{N_j}` with `Σ_j N_j† N_j = I`,
`U = Σ_j N_j ⊗ |j⟩_E` is an isometry and `Tr_E (U ρ U†) = Σ_j N_j ρ N_j†`.
Proved by expanding the matrix products and collapsing the register sum
(`Matrix.mul_apply`, `Fintype.sum_prod_type`, `Finset.sum_comm`); both the
isometry identity and the partial-trace identity are `ext`-plus-`simp` on
matrix entries. -/
theorem isometric_extension_isometry_and_partial_trace {a b : ℕ} {ι : Type} [Fintype ι]
    (K : ι → Matrix (Fin b) (Fin a) ℂ)
    (hK : (∑ j, (K j)ᴴ * (K j)) = (1 : Matrix (Fin a) (Fin a) ℂ)) :
    (isometricExtension K)ᴴ * isometricExtension K = 1 ∧
      (∀ ρ : Matrix (Fin a) (Fin a) ℂ,
        ptraceSecond (isometricExtension K * ρ * (isometricExtension K)ᴴ) =
          ∑ j, K j * ρ * (K j)ᴴ) := by
  constructor
  · ext ai ai'
    simp only [isometricExtension, Matrix.conjTranspose_apply, Matrix.mul_apply]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have step : (∑ j : ι, ∑ bo : Fin b, star (K j bo ai) * K j bo ai')
        = (∑ j, (K j)ᴴ * (K j)) ai ai' := by
      rw [Matrix.sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro bo _
      rw [Matrix.conjTranspose_apply]
    rw [step, hK, Matrix.one_apply]
  · intro ρ
    ext i k
    simp only [ptraceSecond, isometricExtension, Matrix.conjTranspose_apply,
      Matrix.mul_apply]
    rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- **Coherent quantum instrument** — arXiv:1106.1445v8, Eqs. (5.81)–(5.85),
fixed PDF p. 199. Superposing the pure extensions `U^{E_j}` of the CPTNI branches against
registers `|j⟩_J`, `|j⟩_{E_J}` gives Eq. (5.85),
`Σ_{j,k,j',k'} M_{j,k} ρ M_{j',k'}† ⊗ |k⟩⟨k'|_E ⊗ |j⟩⟨j'|_J ⊗ |j⟩⟨j'|_{E_J}`;
tracing over the environments `E`, `E_J` and the outcome register `J` recovers
the instrument sum `Σ_j Σ_l K^j_l ρ K^j_l†`.  When every branch is trace
preserving (each `U^{E_j}` an isometry) the assembled operator is an isometry
only up to the number of branches, `U†U = |ι|·1`; this is why the paper uses
CPTNI branches.  Both identities are proved by expanding the matrix products
and collapsing the register indicators with `Finset.sum_ite_eq'`. -/
theorem coherent_instrument_card_smul_and_partial_trace
    {a b : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (K : ι → κ → Matrix (Fin b) (Fin a) ℂ)
    (hK : ∀ j, (∑ l, (K j l)ᴴ * (K j l)) = (1 : Matrix (Fin a) (Fin a) ℂ)) :
    (coherentInstrument K)ᴴ * coherentInstrument K =
        (Fintype.card ι : ℂ) • (1 : Matrix (Fin a) (Fin a) ℂ) ∧
      (∀ ρ : Matrix (Fin a) (Fin a) ℂ,
        ptraceSecond (coherentInstrument K * ρ * (coherentInstrument K)ᴴ) =
          ∑ j, ∑ l, K j l * ρ * (K j l)ᴴ) := by
  have hmul : ∀ (c : Prop) [Decidable c] (v w : ℂ),
      star (if c then v else 0) * (if c then w else 0) = if c then star v * w else 0 := by
    intro c _ v w
    by_cases h : c <;> simp [h]
  have hcollapse : ∀ (g : ι → ℂ),
      (∑ j1 : ι, ∑ j2 : ι, (if j1 = j2 then g j1 else 0)) = ∑ j : ι, g j := by
    intro g
    have hinner : ∀ j1 : ι, (∑ j2 : ι, (if j1 = j2 then g j1 else 0)) = g j1 := by
      intro j1
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [hinner]
  have hperm : ∀ (f : Fin b → κ → ι → ℂ),
      (∑ bo : Fin b, ∑ l : κ, ∑ j : ι, f bo l j)
        = ∑ j : ι, ∑ l : κ, ∑ bo : Fin b, f bo l j := by
    intro f
    calc (∑ bo : Fin b, ∑ l : κ, ∑ j : ι, f bo l j)
        = ∑ bo : Fin b, ∑ j : ι, ∑ l : κ, f bo l j := by
          apply Finset.sum_congr rfl; intro bo _; rw [Finset.sum_comm]
      _ = ∑ j : ι, ∑ bo : Fin b, ∑ l : κ, f bo l j := by rw [Finset.sum_comm]
      _ = ∑ j : ι, ∑ l : κ, ∑ bo : Fin b, f bo l j := by
          apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_comm]
  constructor
  · ext ai ai'
    have hblock : ∀ j : ι, (∑ l : κ, ∑ bo : Fin b, star (K j l bo ai) * K j l bo ai')
        = (if ai = ai' then (1 : ℂ) else 0) := by
      intro j
      have h := congrArg (fun M : Matrix (Fin a) (Fin a) ℂ => M ai ai') (hK j)
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply] at h
      exact h
    simp only [coherentInstrument, Matrix.conjTranspose_apply, Matrix.mul_apply, hmul]
    conv_lhs =>
      rw [Fintype.sum_prod_type]
      enter [2, bo]
      rw [Fintype.sum_prod_type]
      enter [2, l]
      rw [Fintype.sum_prod_type]
    simp only [hcollapse, hperm, hblock]
    simp [Finset.sum_const, nsmul_eq_mul, Matrix.smul_apply, Matrix.one_apply]
  · intro ρ
    ext i k
    simp only [ptraceSecond, coherentInstrument, Matrix.conjTranspose_apply, Matrix.mul_apply]
    have hterm : ∀ x : κ × (ι × ι),
        (∑ x_1 : Fin a,
          (∑ x_2 : Fin a, (if x.2.1 = x.2.2 then K x.2.1 x.1 i x_2 else 0) * ρ x_2 x_1) *
            star (if x.2.1 = x.2.2 then K x.2.1 x.1 k x_1 else 0))
          = if x.2.1 = x.2.2 then (K x.2.1 x.1 * ρ * (K x.2.1 x.1)ᴴ) i k else 0 := by
      intro x
      by_cases h : x.2.1 = x.2.2
      · simp only [ite_eq_left h]
        simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.conjTranspose_apply]
      · simp [h]
    simp only [hterm]
    conv_lhs =>
      rw [Fintype.sum_prod_type]
      enter [2, l]
      rw [Fintype.sum_prod_type]
    simp only [hcollapse]
    rw [Finset.sum_comm]
    simp only [Matrix.sum_apply]

/-- **Coherent measurement** — arXiv:1106.1445v8, Eqs. (5.88)–(5.91), fixed PDF p. 200.
For a POVM `{M_j}` with `Σ_j M_j† M_j = I`, the isometry
`U = Σ_j M_j ⊗ |j⟩_{S'}` yields, after projecting the register on outcome `j`,
the unnormalised post-measurement operator `M_j ρ M_j†`.
Proved: the isometry identity uses the entry computation of
`isometric_extension_isometry_and_partial_trace`, and the
projected post-measurement formula follows by isolating the unique surviving
register term in `regProj` (`Finset.sum_eq_single`). -/
theorem coherent_measurement_isometry_and_projection {d : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ι → Matrix (Fin d) (Fin d) ℂ)
    (hM : (∑ j, (M j)ᴴ * (M j)) = (1 : Matrix (Fin d) (Fin d) ℂ)) :
    (coherentMeasurement M)ᴴ * coherentMeasurement M = 1 ∧
      (∀ (j : ι) (ρ : Matrix (Fin d) (Fin d) ℂ) (x y : Fin d) (a b : ι),
        (regProj (X := Fin d) (ι := ι) j * (coherentMeasurement M * ρ *
          (coherentMeasurement M)ᴴ) * regProj (X := Fin d) (ι := ι) j) (x, a) (y, b)
          = if a = j ∧ b = j then (M j * ρ * (M j)ᴴ) x y else 0) := by
  have hmeas : (coherentMeasurement M)ᴴ * coherentMeasurement M
      = (1 : Matrix (Fin d) (Fin d) ℂ) := by
    ext ai ai'
    simp only [coherentMeasurement, Matrix.conjTranspose_apply, Matrix.mul_apply]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have step : (∑ j : ι, ∑ bo : Fin d, star (M j bo ai) * M j bo ai')
        = (∑ j, (M j)ᴴ * (M j)) ai ai' := by
      rw [Matrix.sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro bo _
      rw [Matrix.conjTranspose_apply]
    rw [step, hM, Matrix.one_apply]
  refine ⟨hmeas, ?_⟩
  intro j ρ x y a b
  have hentry : ∀ (u v : Fin d) (c e : ι),
      (coherentMeasurement M * ρ * (coherentMeasurement M)ᴴ) (u, c) (v, e)
        = (M c * ρ * (M e)ᴴ) u v := by
    intro u v c e
    simp only [coherentMeasurement, Matrix.conjTranspose_apply, Matrix.mul_apply]
  have hproj : ∀ (A : Matrix (Fin d × ι) (Fin d × ι) ℂ),
      (regProj (X := Fin d) (ι := ι) j * A * regProj (X := Fin d) (ι := ι) j)
          (x, a) (y, b) = if a = j ∧ b = j then A (x, j) (y, j) else 0 := by
    intro A
    simp only [regProj, Matrix.mul_apply]
    by_cases ha : a = j <;> by_cases hb : b = j
    · simp only [ha, hb]
      rw [Finset.sum_eq_single (y, j)]
      · simp only []
        rw [Finset.sum_eq_single (x, j)]
        · simp
        · intro p _ hp
          by_cases h : p.2 = j ∧ x = p.1
          · exfalso; exact absurd (Prod.ext h.2.symm h.1) hp
          · simp [h]
        · intro hnot; simp at hnot
      · intro p _ hp
        by_cases h : p.2 = j ∧ p.1 = y
        · exfalso; exact absurd (Prod.ext h.2 h.1) hp
        · simp [h]
      · intro hnot; simp at hnot
    · simp [ha, hb]
    · simp [ha, hb]
    · simp [ha, hb]
  rw [hproj]
  by_cases h : a = j ∧ b = j
  · rw [ite_eq_left h, ite_eq_left h]; exact hentry x y j j
  · rw [ite_eq_right h, ite_eq_right h]

/-- **Proposition 5.2.1** — arXiv:1106.1445v8, fixed PDF p. 197. If `U : H_A → H_B ⊗ H_E`
is the isometric extension of a channel `N`, then its adjoint is
`N†(Y_B) = U† (Y_B ⊗ I_E) U`.
Proved by expanding both sides entrywise: the tensor factor `Y ⊗ 1` contributes
the Kronecker delta `δ_{jj'}`, which collapses the register sum
(`Finset.sum_ite_eq'`), and the remaining sums match after reindexing. -/
theorem isometric_extension_adjoint_eq_kraus_sum {a b _e : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : ι → Matrix (Fin b) (Fin a) ℂ)
    (Y : Matrix (Fin b) (Fin b) ℂ) :
    (isometricExtension K)ᴴ * (Matrix.kroneckerMap (· * ·) Y (1 : Matrix ι ι ℂ)) *
        (isometricExtension K) =
      ∑ j, (K j)ᴴ * Y * (K j) := by
  ext ai ai'
  simp only [isometricExtension, Matrix.conjTranspose_apply, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Finset.sum_mul, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl; intro j _
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro bo' _
  rw [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro bo _
  rw [Matrix.conjTranspose_apply]

end

end Qatlib.Papers.QShannonWilde11.MainResults.StatesChannels
