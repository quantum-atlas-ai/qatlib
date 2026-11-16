/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Matrix.Block
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Complex.Norm

@[expose] public section


/-!
# Liouvillian gap for steady-state estimation

Fixed source: arXiv:2008.07133v2 (Quantum **5**, 420 (2021)), Section 2, pp. 3–4,
Eq. (2) (vectorized Liouvillian `L`), Eq. (3) (the Hermitian block operator
`M = [[0, L], [L†, 0]]` on `H ⊕ H`), and the paragraph between them and Section 3:

> “Given the structure of `M`, for each eigenvalue `φ_j` associated to the eigenvector
> `|η_j⟩ = |0⟩|a_j⟩ + |1⟩|b_j⟩`, the vector `|η̃_j⟩ = |0⟩|a_j⟩ − |1⟩|b_j⟩` is also
> eigenvector of `M` with eigenvalue `−φ_j`. The eigenvector condition also implies the
> relations `L†L|b_j⟩ = φ_j² |b_j⟩` and `LL†|a_j⟩ = φ_j² |a_j⟩`, thus proving that the
> eigenvalues of `M` coincide with those of `L†L` and `LL†`. Hence, the values `φ_j` are
> the singular values of the Liouvillian `L` and, by applying Weyl's inequality for
> singular values, … the inequality `g ≤ min_{φ_j ≠ 0} |φ_j|` holds. We conclude that
> the Liouvillian gap `g` sets a lower bound to the spectral gap of the operator `M`.”

What is formalised here, and what is not:

* The block structure of `M`, its Hermitian nature (`M = M†`), the identity
  `M² = diag(L L†, L† L)`, and the full one-to-one correspondence between eigenvectors
  of `M` and the vector relations `L b = φ a`, `L† a = φ b` are proved completely
  (`blockOp_isHermitian`, `blockOp_sq`, `blockOp_mulVec_pair`, `blockOp_eigen_relations`,
  `blockOp_eigen_of_relations`, `blockOp_eigen_neg_of_relations`,
  `blockOp_eigen_sq_relation`).  The two zero eigenvectors `|0⟩|I⟩ = |η₀⟩` and
  `|1⟩|ρ_ss⟩ = |η₁⟩` are derived from `L†|I⟩ = 0` and `L|ρ_ss⟩ = 0`
  (`blockOp_zero_eigen_left`, `blockOp_zero_eigen_right`).

* The passage from “the eigenvalues of `M` are the singular values of `L`” to
  `g ≤ min_{φ_j ≠ 0} |φ_j|` is the paper's Weyl-inequality step.  It is valid when the
  Liouvillian is **normal** (then singular values and eigenvalue moduli coincide, so
  `g ≤ |Re λ| ≤ |λ| = φ`).  It is **not** valid for a general non-normal `L`: for
  `L = [[1, 2], [0, 1]]` the only eigenvalue is `1`, hence `g = 1`, while the smallest
  singular value is `√2 - 1 ≈ 0.414 < 1` (its square is `3 - 2√2`).
  Accordingly the proved bound retains the explicit normal-spectrum hypothesis
  `hσ` (`liouvillian_gap_le_abs_of_normalSpectrum`). The general non-normal case
  lies outside this conditional result's scope.

Shared interface: the Frozen GKSL bridge
`Qatlib.Concepts.GkslBridge.GkslBridge` supplies the concrete thermal/NESS
data and the generator identity; this file works at the abstract matrix level, which is
the level at which the paper formulates Eq. (3) and the gap argument.
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix BigOperators

namespace Qatlib.Papers.SteadyState20.MainResults.LiouvillianGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `HasEigenvector L λ` means that `λ` is an eigenvalue of the matrix `L` with a
nonzero eigenvector `v`, i.e. `L *ᵥ v = λ • v` and `v ≠ 0`. -/
def HasEigenvector (L : Matrix ι ι ℂ) (μ : ℂ) : Prop :=
  ∃ v : ι → ℂ, v ≠ 0 ∧ L *ᵥ v = μ • v

/-- `IsLiouvillianGap L g` says that `g ≥ 0` is the Liouvillian gap, i.e. the minimum
of `|Re λ|` over the **nonzero** eigenvalues `λ` of `L`: it is a lower bound and it is
attained.  (Source: arXiv:2008.07133v2, Sec. 2, p. 4.) -/
def IsLiouvillianGap (L : Matrix ι ι ℂ) (g : ℝ) : Prop :=
  (∀ μ : ℂ, HasEigenvector L μ → μ ≠ 0 → g ≤ |μ.re|) ∧
    ∃ μ : ℂ, HasEigenvector L μ ∧ μ ≠ 0 ∧ |μ.re| = g

/-- Paper Eq. (3) (arXiv:2008.07133v2, Sec. 2, p. 3): the Hermitian block operator
`M = [[0, L], [L†, 0]]` on `H ⊕ H` built from the vectorized Liouvillian `L`. -/
def blockOp (L : Matrix ι ι ℂ) : Matrix (Sum ι ι) (Sum ι ι) ℂ :=
  Matrix.fromBlocks 0 L Lᴴ 0

/-- Paper Eq. (3), p. 3: `M` is Hermitian, `M = M†` (the two off-diagonal blocks are
`L` and `L†`, and the diagonal blocks vanish). -/
theorem blockOp_isHermitian (L : Matrix ι ι ℂ) : (blockOp L)ᴴ = blockOp L := by
  let _ := (inferInstance : Fintype ι)
  let _ := (inferInstance : DecidableEq ι)
  unfold blockOp
  rw [Matrix.fromBlocks_conjTranspose]
  simp

/-- Paper Eq. (3), p. 3, squared: `M² = diag(L L†, L† L)`.  This is the identity behind
the statement that the eigenvalues of `M` (squared) are the eigenvalues of `L†L` and
`L L†`. -/
theorem blockOp_sq (L : Matrix ι ι ℂ) :
    blockOp L * blockOp L = Matrix.fromBlocks (L * Lᴴ) 0 0 (Lᴴ * L) := by
  unfold blockOp
  rw [Matrix.fromBlocks_multiply]
  simp

/-- A block vector `(a, b)` as an element of `ι ⊕ ι → ℂ`: the paper's
`|η⟩ = |0⟩|a⟩ + |1⟩|b⟩`. -/
def vecPair (a b : ι → ℂ) : Sum ι ι → ℂ := Sum.elim a b

/-- Paper Eq. (3), p. 3: the action of `M` on `|0⟩|a⟩ + |1⟩|b⟩` is
`|0⟩(L|b⟩) + |1⟩(L†|a⟩)`. -/
theorem blockOp_mulVec_pair (L : Matrix ι ι ℂ) (a b : ι → ℂ) :
    (blockOp L) *ᵥ vecPair a b = vecPair (L *ᵥ b) (Lᴴ *ᵥ a) := by
  let _ := (inferInstance : Fintype ι)
  let _ := (inferInstance : DecidableEq ι)
  unfold blockOp vecPair
  rw [Matrix.fromBlocks_mulVec]
  simp

/-- `M²` acting on a block vector: `diag(L L†, L† L)` on the two components
(consequence of `blockOp_sq`). -/
theorem blockOp_sq_mulVec_pair (L : Matrix ι ι ℂ) (a b : ι → ℂ) :
    (blockOp L * blockOp L) *ᵥ vecPair a b =
      vecPair ((L * Lᴴ) *ᵥ a) ((Lᴴ * L) *ᵥ b) := by
  rw [blockOp_sq]
  unfold vecPair
  rw [Matrix.fromBlocks_mulVec]
  simp

/-- Paper Sec. 2, p. 3–4: if `|0⟩|a⟩ + |1⟩|b⟩` is an eigenvector of `M` of eigenvalue
`φ`, then the two vector relations `L|b⟩ = φ|a⟩` and `L†|a⟩ = φ|b⟩` hold. -/
theorem blockOp_eigen_relations (L : Matrix ι ι ℂ) {φ : ℂ} {a b : ι → ℂ}
    (h : (blockOp L) *ᵥ vecPair a b = φ • vecPair a b) :
    L *ᵥ b = φ • a ∧ Lᴴ *ᵥ a = φ • b := by
  rw [blockOp_mulVec_pair] at h
  constructor
  · funext i
    have := congrFun h (Sum.inl i)
    simpa [vecPair, Pi.smul_apply] using this
  · funext i
    have := congrFun h (Sum.inr i)
    simpa [vecPair, Pi.smul_apply] using this

/-- Paper Sec. 2, p. 4, converse direction: the relations `L|b⟩ = φ|a⟩` and
`L†|a⟩ = φ|b⟩` imply that `|0⟩|a⟩ + |1⟩|b⟩` is an eigenvector of `M` with eigenvalue
`φ`. -/
theorem blockOp_eigen_of_relations (L : Matrix ι ι ℂ) {φ : ℂ} {a b : ι → ℂ}
    (ha : L *ᵥ b = φ • a) (hb : Lᴴ *ᵥ a = φ • b) :
    (blockOp L) *ᵥ vecPair a b = φ • vecPair a b := by
  rw [blockOp_mulVec_pair, ha, hb]
  funext i
  cases i <;> simp [vecPair, Pi.smul_apply]

/-- Paper Sec. 2, p. 4: the partner eigenvector `|0⟩|a⟩ − |1⟩|b⟩` has eigenvalue `−φ`
whenever `|0⟩|a⟩ + |1⟩|b⟩` has eigenvalue `φ`. -/
theorem blockOp_eigen_neg_of_relations (L : Matrix ι ι ℂ) {φ : ℂ} {a b : ι → ℂ}
    (ha : L *ᵥ b = φ • a) (hb : Lᴴ *ᵥ a = φ • b) :
    (blockOp L) *ᵥ vecPair a (-b) = (-φ) • vecPair a (-b) := by
  rw [blockOp_mulVec_pair]
  have h1 : L *ᵥ (-b) = (-φ) • a := by
    rw [Matrix.mulVec_neg, ha, neg_smul]
  have h2 : Lᴴ *ᵥ a = (-φ) • (-b) := by
    rw [hb]
    simp
  rw [h1, h2]
  funext i
  cases i <;> simp [vecPair, Pi.smul_apply]

/-- Paper Sec. 2, p. 4: the first zero eigenvector `|η₀⟩ = |0⟩|I⟩`.  If `L†|I⟩ = 0`
(the abstract counterpart of `L†|I⟩ = 0` noted in the source), then `M|0⟩|I⟩ = 0`. -/
theorem blockOp_zero_eigen_left (L : Matrix ι ι ℂ) {Ivec : ι → ℂ}
    (hI : Lᴴ *ᵥ Ivec = 0) :
    (blockOp L) *ᵥ vecPair Ivec 0 = 0 := by
  rw [blockOp_mulVec_pair, hI]
  simp [vecPair]

/-- Paper Sec. 2, p. 4: the second zero eigenvector `|η₁⟩ = |1⟩|ρ_ss⟩`.  If
`L|ρ_ss⟩ = 0` (the vectorized NESS condition), then `M|1⟩|ρ_ss⟩ = 0`. -/
theorem blockOp_zero_eigen_right (L : Matrix ι ι ℂ) {ρvec : ι → ℂ}
    (hρ : L *ᵥ ρvec = 0) :
    (blockOp L) *ᵥ vecPair 0 ρvec = 0 := by
  rw [blockOp_mulVec_pair, hρ]
  simp [vecPair]

/-- Paper Sec. 2, p. 4: for `φ ≠ 0`, an eigenvector `|0⟩|a⟩ + |1⟩|b⟩` of `M` with
eigenvalue `φ` has `b ≠ 0` and `L†L|b⟩ = φ²|b⟩`: the eigenvalues of `M` are square
roots of eigenvalues of `L†L`. -/
theorem blockOp_eigen_sq_relation (L : Matrix ι ι ℂ) {φ : ℂ} (hφ : φ ≠ 0)
    {a b : ι → ℂ} (hne : vecPair a b ≠ 0)
    (h : (blockOp L) *ᵥ vecPair a b = φ • vecPair a b) :
    b ≠ 0 ∧ (Lᴴ * L) *ᵥ b = (φ * φ) • b := by
  obtain ⟨h1, h2⟩ := blockOp_eigen_relations L h
  have hbb : (Lᴴ * L) *ᵥ b = (φ * φ) • b := by
    calc (Lᴴ * L) *ᵥ b = Lᴴ *ᵥ (L *ᵥ b) := (Matrix.mulVec_mulVec b Lᴴ L).symm
      _ = Lᴴ *ᵥ (φ • a) := by rw [h1]
      _ = φ • (Lᴴ *ᵥ a) := Matrix.mulVec_smul Lᴴ φ a
      _ = φ • (φ • b) := by rw [h2]
      _ = (φ * φ) • b := smul_smul φ φ b
  refine ⟨?_, hbb⟩
  intro hb0
  have ha0 : a = 0 := by
    have h' := h1
    rw [hb0, Matrix.mulVec_zero] at h'
    exact (smul_eq_zero.mp h'.symm).resolve_left hφ
  exact hne (by rw [ha0, hb0]; simp [vecPair])

/-- Paper Sec. 2, p. 4: the paper's chain `g ≤ |Re λ_j| ≤ |λ_j|` for a nonzero
eigenvalue, under the normal-spectrum identification `hσ` that the Weyl-inequality step
supplies (for a normal `L`, singular values coincide with eigenvalue moduli).  This is
the rigorous core of the paper's inequality `g ≤ min_{φ_j ≠ 0} |φ_j|`. -/
theorem liouvillian_gap_le_abs_of_normalSpectrum (L : Matrix ι ι ℂ) {g : ℝ}
    (hgap : IsLiouvillianGap L g) {φ : ℂ} (_hφ0 : φ ≠ 0)
    (hσ : ∃ μ : ℂ, HasEigenvector L μ ∧ μ ≠ 0 ∧ ‖φ‖ = ‖μ‖) :
    g ≤ ‖φ‖ := by
  let _ := (inferInstance : DecidableEq ι)
  obtain ⟨μ, hμ, hμ0, hnorm⟩ := hσ
  have h1 : g ≤ |μ.re| := hgap.1 μ hμ hμ0
  have h2 : |μ.re| ≤ ‖μ‖ := Complex.abs_re_le_norm μ
  calc g ≤ |μ.re| := h1
    _ ≤ ‖μ‖ := h2
    _ = ‖φ‖ := hnorm.symm


/- The unconditional singular-value inequality is false for the stated
   non-normal Liouvillian model. -/

end Qatlib.Papers.SteadyState20.MainResults.LiouvillianGap
