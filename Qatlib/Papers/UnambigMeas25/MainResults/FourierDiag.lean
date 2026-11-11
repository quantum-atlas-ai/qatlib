/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Fourier diagonalization of the summed POVM elements for Buzet--Chailloux,
"Fine-Grained Unambiguous Measurements", arXiv:2510.07298v2 (2025),
§3.1.2–3.1.3.

This file establishes:

* `sumCoset`: the coset sum `F_H = ∑_y F_{H,y}` of Proposition 8, and
  `hatM M = H^{⊗n} M H^{⊗n}`;
* the Fourier-transformed coset sum is invariant under conjugation by
  every phase operator `Z_c`, hence off-diagonal entries vanish
  (`prop8_offdiag`, Proposition 8, off-diagonal half);
* for a full-rank parity matrix, every diagonal entry equals `2^k` times
  the (y-independent) entry of a single outcome (`prop8_diag`), giving
  the full statement `prop8_fourier_diag`;
* the Fourier expansion of an arbitrary vector (Theorem 1 ingredient);
* the coset regrouping identity used to state Theorem 1 at the level of
  the full outcome sum;
* Proposition 9: a symmetric set with full dual support is linearly
  independent, and the Fourier kets lie in its span.
-/
import Qatlib.Papers.UnambigMeas25.MainResults.Preliminaries
import Qatlib.Papers.UnambigMeas25.MainResults.Fourier
import Qatlib.Papers.UnambigMeas25.MainResults.Symmetrization

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open scoped BigOperators
open Matrix

namespace Qatlib.Papers.UnambigMeas25.MainResults

/-! ### Phase and counting preliminaries -/

/-- Phases square to one. -/
lemma phase_sq (z : ZMod 2) : phase z * phase z = 1 := by
  rcases zmod2_cases z with rfl | rfl <;> simp [phase]

/-- If `w ≠ 0` in `F₂ⁿ`, some `c` pairs nontrivially with `w`. -/
lemma exists_pair_one {n : ℕ} (w : F2Vec n) (hw : w ≠ 0) :
    ∃ c : F2Vec n, dotF2 w c = 1 := by
  have hwi : ∃ t, w t ≠ 0 := by
    by_contra h
    push Not at h
    apply hw
    funext s
    simpa using h s
  obtain ⟨t, ht⟩ := hwi
  refine ⟨fun s => if s = t then (1 : ZMod 2) else 0, ?_⟩
  simp only [dotF2]
  rw [Finset.sum_eq_single t]
  · rw [if_pos rfl]
    rcases zmod2_cases (w t) with h0 | h1
    · exact absurd h0 ht
    · rw [h1, one_mul]
  · intro s _ hst
    rw [if_neg hst, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A constant sum over parity values: `∑_y T = 2^k T`. -/
lemma sum_univ_const_coe {k : ℕ} (T : ℂ) :
    ∑ _y : Fin k → ZMod 2, T = ((2 ^ k : ℕ) : ℂ) * T := by
  have hone : ∑ y : Fin k → ZMod 2, (1 : ℂ) = ((2 ^ k : ℕ) : ℂ) := by simp
  calc ∑ y : Fin k → ZMod 2, T = ∑ y : Fin k → ZMod 2, (1 : ℂ) * T :=
        Finset.sum_congr rfl (fun _y _ => (one_mul T).symm)
    _ = (∑ y : Fin k → ZMod 2, (1 : ℂ)) * T := (Finset.sum_mul Finset.univ _ T).symm
    _ = ((2 ^ k : ℕ) : ℂ) * T := by rw [hone]

/-! ### The coset sum and its Fourier conjugate -/

/-- `F_H = ∑_y F_{H,y}`: the sum of a measurement family over all parity
values of a fixed parity matrix (Proposition 8). -/
noncomputable def sumCoset {n : ℕ} (F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ)
    (idx : Idx n) : Matrix (F2Vec n) (F2Vec n) ℂ :=
  ∑ y : Fin idx.k → ZMod 2, F ⟨idx.k, idx.H, y⟩

/-- The Fourier conjugate `H^{⊗n} M H^{⊗n}` of a matrix. -/
noncomputable def hatM {n : ℕ} (M : Matrix (F2Vec n) (F2Vec n) ℂ) :
    Matrix (F2Vec n) (F2Vec n) ℂ := qftMat n * M * qftMat n

/-- Entrywise shape of `Z_c M Z_c`: phases multiply on both sides. -/
lemma phaseZ_mul_entry {n : ℕ} (c : F2Vec n) (M : Matrix (F2Vec n) (F2Vec n) ℂ)
    (i j : F2Vec n) :
    (phaseZ c * M * phaseZ c) i j
      = phase (dotF2 i c) * M i j * phase (dotF2 j c) := by
  have h1 : ∀ x : F2Vec n,
      (∑ y : F2Vec n, phaseZ c i y * M y x) = phase (dotF2 i c) * M i x := by
    intro x
    simp only [phaseZ]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]
    · intro y _ hyi
      rw [if_neg (Ne.symm hyi), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have h2 : ∀ x : F2Vec n,
      phase (dotF2 i c) * M i x * phaseZ c x j
      = if x = j then phase (dotF2 i c) * M i j * phase (dotF2 j c) else 0 := by
    intro x
    by_cases hxj : x = j <;> simp [hxj, phaseZ]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_congr rfl (fun x _ => by rw [h1 x]),
    Finset.sum_congr rfl (fun x _ => h2 x), Finset.sum_eq_single j]
  · rw [if_pos rfl]
  · intro x _ hxj
    rw [if_neg hxj]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Fourier conjugation turns `X`-conjugation into `Z`-conjugation
(Proposition 5, matrix form). -/
lemma hatM_conj_shiftX {n : ℕ} (c : F2Vec n) (M : Matrix (F2Vec n) (F2Vec n) ℂ) :
    hatM (shiftX c * M * shiftX c) = phaseZ c * hatM M * phaseZ c := by
  calc hatM (shiftX c * M * shiftX c)
      = qftMat n * (shiftX c * M * shiftX c) * qftMat n := rfl
    _ = (qftMat n * shiftX c) * M * (shiftX c * qftMat n) := by
        simp only [Matrix.mul_assoc]
    _ = (phaseZ c * qftMat n) * M * (qftMat n * phaseZ c) := by
        rw [prop5_qft_shift c, prop5_shift_qft c]
    _ = phaseZ c * (qftMat n * M * qftMat n) * phaseZ c := by
        simp only [Matrix.mul_assoc]

/-- Adding `H c` is an involution, hence a bijection, on parity values. -/
def cosetEquiv {n : ℕ} (idx : Idx n) (c : F2Vec n) :
    (Fin idx.k → ZMod 2) ≃ (Fin idx.k → ZMod 2) where
  toFun y := fun r => y r + ∑ s, idx.H r s * c s
  invFun y := fun r => y r + ∑ s, idx.H r s * c s
  left_inv y := by
    funext r
    show (y r + ∑ s, idx.H r s * c s) + ∑ s, idx.H r s * c s = y r
    rw [add_assoc, zmod_add_self, add_zero]
  right_inv y := by
    funext r
    show (y r + ∑ s, idx.H r s * c s) + ∑ s, idx.H r s * c s = y r
    rw [add_assoc, zmod_add_self, add_zero]

/-- Full row rank of the parity matrix: every parity value is attained. -/
def Idx.IsFullRank {n : ℕ} (idx : Idx n) : Prop :=
  ∀ y : Fin idx.k → ZMod 2, ∃ c : F2Vec n, ∀ r, ∑ s, idx.H r s * c s = y r

/-- Fourier-conjugating the coset sum distributes over the sum over
parity values. -/
theorem hatM_sumCoset_eq_sum {n : ℕ} {F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ}
    (idx : Idx n) :
    hatM (sumCoset F idx)
      = ∑ y : Fin idx.k → ZMod 2, hatM (F ⟨idx.k, idx.H, y⟩) := by
  rw [hatM, sumCoset, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl (fun y _ => rfl)

/-- The Fourier transform of a coset sum is invariant under conjugation
by every phase operator (Proposition 8, key step). -/
theorem hatM_sumCoset_conj {n : ℕ} {F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ}
    (hsymm : IsSymmetrized F) (idx : Idx n) (c : F2Vec n) :
    phaseZ c * hatM (sumCoset F idx) * phaseZ c = hatM (sumCoset F idx) := by
  have hsum : hatM (sumCoset F idx)
      = ∑ y : Fin idx.k → ZMod 2, hatM (F ⟨idx.k, idx.H, y⟩) :=
    hatM_sumCoset_eq_sum idx
  rw [hsum]
  calc phaseZ c * (∑ y : Fin idx.k → ZMod 2, hatM (F ⟨idx.k, idx.H, y⟩))
        * phaseZ c
      = ∑ y : Fin idx.k → ZMod 2,
          phaseZ c * hatM (F ⟨idx.k, idx.H, y⟩) * phaseZ c := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
    _ = ∑ y : Fin idx.k → ZMod 2,
          hatM (F ⟨idx.k, idx.H, fun r => y r + ∑ s, idx.H r s * c s⟩) := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        have h1 : shiftX c * F ⟨idx.k, idx.H, y⟩ * shiftX c
            = F ⟨idx.k, idx.H, fun r => y r + ∑ s, idx.H r s * c s⟩ :=
          Matrix.ext fun p q => hsymm ⟨idx.k, idx.H, y⟩ c p q
        rw [← hatM_conj_shiftX c, h1]
    _ = ∑ y : Fin idx.k → ZMod 2, hatM (F ⟨idx.k, idx.H, y⟩) :=
        Equiv.sum_comp (cosetEquiv idx c)
          (fun y => hatM (F ⟨idx.k, idx.H, y⟩))

/-- Entrywise consequence of phase-invariance: every entry is
`phase((i+j)·c)`-invariant. -/
lemma hatM_sumCoset_entry {n : ℕ} {F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ}
    (hsymm : IsSymmetrized F) (idx : Idx n) (c i j : F2Vec n) :
    hatM (sumCoset F idx) i j
      = phase (dotF2 (i + j) c) * hatM (sumCoset F idx) i j := by
  have h : (phaseZ c * hatM (sumCoset F idx) * phaseZ c) i j
      = hatM (sumCoset F idx) i j :=
    congrArg (fun M : Matrix (F2Vec n) (F2Vec n) ℂ => M i j) (hatM_sumCoset_conj hsymm idx c)
  rw [phaseZ_mul_entry c _ i j] at h
  have h2 : phase (dotF2 i c) * hatM (sumCoset F idx) i j * phase (dotF2 j c)
      = phase (dotF2 (i + j) c) * hatM (sumCoset F idx) i j := by
    rw [dotF2_add_left, phase_mul]
    ring
  rw [← h2, h]

/-- **Proposition 8, off-diagonal part** (arXiv:2510.07298v2, §3.1.2):
the Fourier transform of the coset sum is diagonal, for any parity
matrix (no full-rank assumption needed). -/
theorem prop8_offdiag {n : ℕ} {F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ}
    (hsymm : IsSymmetrized F) (idx : Idx n) {i j : F2Vec n} (hij : i ≠ j) :
    hatM (sumCoset F idx) i j = 0 := by
  have hw : i + j ≠ 0 := fun h0 => hij (add_eq_zero_iff_eq i j |>.mp h0)
  obtain ⟨c, hc⟩ := exists_pair_one (i + j) hw
  have h := hatM_sumCoset_entry hsymm idx c i j
  rw [hc, phase_one, neg_one_mul] at h
  exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp h)

/-- **Proposition 8, diagonal part** (arXiv:2510.07298v2, §3.1.2): for a
full-rank parity matrix, every diagonal entry of the Fourier-transformed
coset sum equals `2^k` times the (y-independent) entry of any single
outcome. -/
theorem prop8_diag {n : ℕ} {F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ}
    (hsymm : IsSymmetrized F) {idx : Idx n} (hfull : idx.IsFullRank)
    (i : F2Vec n) :
    hatM (sumCoset F idx) i i
      = ((2 ^ (idx.k : ℕ) : ℕ) : ℂ) * hatM (F idx) i i := by
  have hterm : ∀ y : Fin idx.k → ZMod 2,
      hatM (F ⟨idx.k, idx.H, y⟩) i i = hatM (F idx) i i := by
    intro y
    obtain ⟨c, hc⟩ := hfull (fun r => y r + idx.y r)
    have hfun : (fun r => idx.y r + ∑ s, idx.H r s * c s) = y := by
      funext r
      rw [hc r, ← add_assoc, add_comm (idx.y r) (y r), add_assoc,
        zmod_add_self (idx.y r), add_zero]
    have h1 : shiftX c * F idx * shiftX c = F ⟨idx.k, idx.H, y⟩ := by
      refine Matrix.ext fun p q => ?_
      rw [hsymm idx c p q, hfun]
    rw [← h1, hatM_conj_shiftX c, phaseZ_mul_entry c _ i i,
      mul_comm (phase (dotF2 i c)) (hatM (F idx) i i), mul_assoc, phase_sq,
      mul_one]
  rw [hatM_sumCoset_eq_sum, Matrix.sum_apply,
    Finset.sum_congr rfl (fun y _ => hterm y), sum_univ_const_coe]

/-- **Proposition 8** (arXiv:2510.07298v2, §3.1.2), corrected scope: for
a symmetrized measurement and a full-rank parity matrix, the Fourier
transform of the coset sum `F_H = ∑_y F_{H,y}` is diagonal, and every
diagonal entry equals `2^k` times the Fourier diagonal of a single
outcome (independent of the parity value). -/
theorem prop8_fourier_diag {n : ℕ} {F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ}
    (hsymm : IsSymmetrized F) {idx : Idx n} (hfull : idx.IsFullRank)
    (i j : F2Vec n) :
    hatM (sumCoset F idx) i j
      = if i = j then ((2 ^ (idx.k : ℕ) : ℕ) : ℂ) * hatM (F idx) i i else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    exact prop8_diag hsymm hfull i
  · rw [if_neg hij]
    exact prop8_offdiag hsymm idx hij

/-! ### Linear-algebra helpers for the Fourier expansion -/

/-- Shifts act on vectors by translation: `(X_a |v⟩)_j = v_{j+a}`. -/
lemma shiftX_mulVec_apply {n : ℕ} (a : F2Vec n) (v : F2Vec n → ℂ) (j : F2Vec n) :
    (shiftX a *ᵥ v) j = v (j + a) := by
  simp only [Matrix.mulVec, dotProduct, shiftX]
  rw [Finset.sum_eq_single (j + a)]
  · rw [if_pos (by rw [add_assoc, addSelf_zero, add_zero]), one_mul]
  · intro z _ hz
    have h' : ¬(j = z + a) := by
      intro h
      apply hz
      rw [h, add_assoc, addSelf_zero, add_zero]
    rw [if_neg h', zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Shift eigenvectors, pointwise: `x̂_{j+a} = (−1)^{x·a} x̂_j`
(Proposition 5, pointwise form). -/
lemma hatKet_shift {n : ℕ} (a x j : F2Vec n) :
    hatKet x (j + a) = phase (dotF2 x a) * hatKet x j := by
  rw [← shiftX_mulVec_apply a (hatKet x) j, prop5_eigenvector a x]
  simp

/-- Scaling the first argument conjugates the scalar out. -/
lemma innerVec_smul_left {n : ℕ} (c : ℂ) (u v : F2Vec n → ℂ) :
    innerVec (c • u) v = starRingEnd ℂ c * innerVec u v := by
  simp only [innerVec, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [Finset.sum_congr rfl (fun x _ =>
    mul_assoc (starRingEnd ℂ c) (starRingEnd ℂ (u x)) (v x)), ← Finset.mul_sum]

/-- Inner products distribute over sums in the second argument. -/
lemma innerVec_sum_right {n : ℕ} {ι : Type*} [Fintype ι]
    (u : F2Vec n → ℂ) (vs : ι → F2Vec n → ℂ) :
    innerVec u (∑ i, vs i) = ∑ i, innerVec u (vs i) := by
  simp only [innerVec, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Inner products distribute over sums in the first argument. -/
lemma innerVec_sum_left {n : ℕ} {ι : Type*} [Fintype ι]
    (us : ι → F2Vec n → ℂ) (v : F2Vec n → ℂ) :
    innerVec (∑ i, us i) v = ∑ i, innerVec (us i) v := by
  simp only [innerVec, Finset.sum_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Matrix-vector products distribute over sums of vectors. -/
lemma mulVec_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (M : Matrix (F2Vec n) (F2Vec n) ℂ) (vs : ι → F2Vec n → ℂ) :
    M *ᵥ (∑ i, vs i) = ∑ i, (M *ᵥ vs i) := by
  funext k
  have h1 : (∑ i, (M *ᵥ vs i)) k = ∑ i, ∑ l, M k l * vs i l := by
    simp only [Finset.sum_apply, Matrix.mulVec, dotProduct]
  rw [h1]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun x _ =>
    Finset.mul_sum Finset.univ (fun c => vs c x) (M k x)), Finset.sum_comm]

/-- Sums of matrices acting on a vector distribute over the sum. -/
lemma sum_mulVec_any {n : ℕ} {ι : Type*} [Fintype ι]
    (Ms : ι → Matrix (F2Vec n) (F2Vec n) ℂ) (u : F2Vec n → ℂ) :
    (∑ a, Ms a) *ᵥ u = ∑ a, (Ms a *ᵥ u) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Multiplying a standard basis vector selects a column. -/
lemma mulVec_single {n : ℕ} (M : Matrix (F2Vec n) (F2Vec n) ℂ) (j k : F2Vec n) :
    (M *ᵥ Pi.single j (1 : ℂ)) k = M k j := by
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, mul_one]
  · intro l _ hlj
    rw [if_neg hlj, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A matrix entry as an inner product of standard basis vectors. -/
lemma innerVec_single_single {n : ℕ} (M : Matrix (F2Vec n) (F2Vec n) ℂ)
    (i j : F2Vec n) :
    innerVec (Pi.single i (1 : ℂ)) (M *ᵥ Pi.single j (1 : ℂ)) = M i j := by
  simp only [innerVec, mulVec_single M j, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, map_one, one_mul]
  · intro k _ hki
    rw [if_neg hki, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Matrix entries against Fourier kets equal entries of the
Fourier-conjugated matrix: `⟨î|M|ĵ⟩ = (H^{⊗n} M H^{⊗n})_{ij}`. -/
lemma hat_inner_eq_entry {n : ℕ} (M : Matrix (F2Vec n) (F2Vec n) ℂ)
    (i i' : F2Vec n) :
    innerVec (hatKet i) (M *ᵥ hatKet i') = hatM M i i' := by
  have hH : qftMat n * (Mᴴ * qftMat n) = (hatM M)ᴴ := by
    rw [hatM, conjTranspose_mul, conjTranspose_mul, qft_conjTranspose]
  have hket : ∀ x : F2Vec n, hatKet x = qftMat n *ᵥ Pi.single x (1 : ℂ) :=
    fun x => rfl
  rw [hket i, hket i', innerVec_mulVec' M,
    Matrix.mulVec_mulVec (Pi.single i (1 : ℂ)) (Mᴴ) (qftMat n),
    innerVec_mulVec' (qftMat n),
    Matrix.mulVec_mulVec (Pi.single i (1 : ℂ)) ((qftMat n)ᴴ) (Mᴴ * qftMat n),
    qft_conjTranspose, hH, innerVec_mulVec, conjTranspose_conjTranspose,
    innerVec_single_single]

/-- **Fourier expansion** (Theorem 1 ingredient): every vector equals
the sum of its Fourier coefficients against the Fourier kets, pointwise:
`ψ_{0,j} = ∑_i ⟨î|ψ₀⟩ î_j`. -/
theorem fourier_expansion {n : ℕ} (ψ0 : F2Vec n → ℂ) (j : F2Vec n) :
    ∑ i : F2Vec n, fourierCoeff ψ0 i * hatKet i j = ψ0 j := by
  have hcoef : ∀ i : F2Vec n, fourierCoeff ψ0 i
      = ∑ k, (((Real.sqrt 2)⁻¹ ^ n : ℝ)) * phase (dotF2 i k) * ψ0 k := by
    intro i
    simp only [fourierCoeff, innerVec]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_mul, Complex.conj_ofReal, star_phase]
  have hterm : ∀ i k : F2Vec n,
      ((((Real.sqrt 2)⁻¹ ^ n : ℝ)) * phase (dotF2 i k) * ψ0 k)
        * ((((Real.sqrt 2)⁻¹ ^ n : ℝ)) * phase (dotF2 j i))
      = ψ0 k * (((((Real.sqrt 2)⁻¹ ^ n : ℝ)) * (((Real.sqrt 2)⁻¹ ^ n : ℝ)))
        * phase (dotF2 (k + j) i)) := by
    intro i k
    have h2 : phase (dotF2 k i) * phase (dotF2 j i)
        = phase (dotF2 (k + j) i) := by
      rw [← phase_mul, dotF2_add_left]
    calc ((((Real.sqrt 2)⁻¹ ^ n : ℝ)) * phase (dotF2 i k) * ψ0 k)
        * ((((Real.sqrt 2)⁻¹ ^ n : ℝ)) * phase (dotF2 j i))
        = ψ0 k * (((((Real.sqrt 2)⁻¹ ^ n : ℝ)) * phase (dotF2 k i))
          * ((((Real.sqrt 2)⁻¹ ^ n : ℝ)) * phase (dotF2 j i))) := by
            rw [dotF2_comm i k]
            ring
      _ = ψ0 k * (((((Real.sqrt 2)⁻¹ ^ n : ℝ)) * (((Real.sqrt 2)⁻¹ ^ n : ℝ)))
        * (phase (dotF2 k i) * phase (dotF2 j i))) := by ring
      _ = ψ0 k * (((((Real.sqrt 2)⁻¹ ^ n : ℝ)) * (((Real.sqrt 2)⁻¹ ^ n : ℝ)))
        * phase (dotF2 (k + j) i)) := by rw [h2]
  calc ∑ i, fourierCoeff ψ0 i * hatKet i j
      = ∑ i, (∑ k, (((Real.sqrt 2)⁻¹ ^ n : ℝ)) * phase (dotF2 i k) * ψ0 k)
          * ((((Real.sqrt 2)⁻¹ ^ n : ℝ)) * phase (dotF2 j i)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hcoef i, hatKet_apply i j]
    _ = ∑ k, ∑ i, ψ0 k * (((((Real.sqrt 2)⁻¹ ^ n : ℝ)) * (((Real.sqrt 2)⁻¹ ^ n : ℝ)))
        * phase (dotF2 (k + j) i)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun k _ => hterm i k)
    _ = ∑ k, (ψ0 k * (((((Real.sqrt 2)⁻¹ ^ n : ℝ)) * (((Real.sqrt 2)⁻¹ ^ n : ℝ)))))
        * (if k + j = 0 then ((2 ^ n : ℕ) : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        have hpull : ∀ i : F2Vec n,
            ψ0 k * (((((Real.sqrt 2)⁻¹ ^ n : ℝ)) * (((Real.sqrt 2)⁻¹ ^ n : ℝ)))
              * phase (dotF2 (k + j) i))
            = (ψ0 k * (((((Real.sqrt 2)⁻¹ ^ n : ℝ)) * (((Real.sqrt 2)⁻¹ ^ n : ℝ)))))
              * phase (dotF2 (k + j) i) := fun i => by ring
        rw [Finset.sum_congr rfl (fun i _ => hpull i), ← Finset.mul_sum,
          char_sum_full (k + j)]
    _ = ψ0 j := by
        rw [Finset.sum_eq_single j]
        · rw [addSelf_zero j, if_pos rfl, qft_coeff_sq_coe, mul_assoc,
          inv_two_pow_mul_two_pow, mul_one]
        · intro k _ hkj
          have hne : k + j ≠ 0 := fun h0 => hkj (add_eq_zero_iff_eq k j |>.mp h0)
          rw [if_neg hne, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h

/-- A state decomposes in the Fourier basis with its Fourier
coefficients (function form of `fourier_expansion`). -/
theorem fourier_decomposition {n : ℕ} (ψ0 : F2Vec n → ℂ) :
    ψ0 = ∑ i : F2Vec n, fourierCoeff ψ0 i • hatKet i := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact (fourier_expansion ψ0 j).symm

/-- The Fourier coefficient as an inner product against the Fourier
ket: `α̂_i = ⟨î|ψ₀⟩`. -/
lemma hat_inner_coeff {n : ℕ} (ψ0 : F2Vec n → ℂ) (i : F2Vec n) :
    innerVec (hatKet i) ψ0 = fourierCoeff ψ0 i := by
  have hfun : hatKet i
      = fun j => (((Real.sqrt 2)⁻¹ ^ n : ℝ)) * phase (dotF2 i j) := by
    refine funext (fun j => ?_)
    rw [hatKet_apply i j, dotF2_comm j i]
  exact congrArg (fun v : F2Vec n → ℂ => innerVec v ψ0) hfun

/-! ### Theorem 1: Fourier-diagonal quality formula -/

/-- Constant sums over parity values, real version. -/
lemma sum_univ_const_real_pi {k : ℕ} (T : ℝ) :
    ∑ _y : Fin k → ZMod 2, T = ((2 ^ k : ℕ) : ℝ) * T := by
  have hone : ∑ y : Fin k → ZMod 2, (1 : ℝ) = ((2 ^ k : ℕ) : ℝ) := by simp
  calc ∑ _y : Fin k → ZMod 2, T = ∑ _y : Fin k → ZMod 2, (1 : ℝ) * T :=
        Finset.sum_congr rfl (fun _y _ => (one_mul T).symm)
    _ = (∑ y : Fin k → ZMod 2, (1 : ℝ)) * T := (Finset.sum_mul Finset.univ _ T).symm
    _ = ((2 ^ k : ℕ) : ℝ) * T := by rw [hone]

/-- `2^k · 2^{-k} = 1` in `ℝ` with the natural casts. -/
lemma two_pow_mul_inv_two_pow (k : ℕ) :
    ((2 ^ k : ℕ) : ℝ) * (((2 ^ k : ℕ) : ℝ)⁻¹) = 1 := by
  have h0 : ((2 ^ k : ℕ) : ℝ) ≠ 0 := by positivity
  exact mul_inv_cancel₀ h0

/-- Real part of a real scaling. -/
lemma re_mul_real (x : ℝ) (z : ℂ) : (x * z).re = x * z.re := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The swap involution on outcome/parity-value pairs, used for coset
regrouping. -/
def idxSwap {n : ℕ} :
    (Σ idx : Idx n, Fin idx.k → ZMod 2) ≃ (Σ idx : Idx n, Fin idx.k → ZMod 2) where
  toFun p := ⟨⟨p.1.k, p.1.H, p.2⟩, p.1.y⟩
  invFun p := ⟨⟨p.1.k, p.1.H, p.2⟩, p.1.y⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Involution identity: summing `C(k)·T` over outcome/value pairs is
invariant under swapping the outcome with its parity value. -/
lemma sum_sigma_swap {n : ℕ} (C : Fin (n + 1) → ℝ) (T : Idx n → ℝ) :
    ∑ p : (Σ idx : Idx n, Fin idx.k → ZMod 2), C p.1.k * T p.1
      = ∑ p : (Σ idx : Idx n, Fin idx.k → ZMod 2),
          C p.1.k * T ⟨p.1.k, p.1.H, p.2⟩ :=
  (Equiv.sum_comp idxSwap (fun p => C p.1.k * T p.1)).symm

/-- **Coset regrouping** (Theorem 1, bookkeeping step): a cost-weighted
sum over outcomes equals the same weighted sum over the coset sums,
each scaled by `2^{-k}`. -/
lemma sum_idx_cost_weight {n : ℕ} (C : Fin (n + 1) → ℝ) (T : Idx n → ℝ) :
    ∑ idx : Idx n, C idx.k * T idx
      = ∑ idx : Idx n, (C idx.k * (((2 ^ (idx.k : ℕ) : ℕ) : ℝ)⁻¹))
          * ∑ y : Fin idx.k → ZMod 2, T ⟨idx.k, idx.H, y⟩ := by
  have hfix : ∀ idx : Idx n,
      ((2 ^ (idx.k : ℕ) : ℕ) : ℝ)
        * (C idx.k * (((2 ^ (idx.k : ℕ) : ℕ) : ℝ)⁻¹ * T idx))
      = C idx.k * T idx := by
    intro idx
    calc ((2 ^ (idx.k : ℕ) : ℕ) : ℝ)
        * (C idx.k * (((2 ^ (idx.k : ℕ) : ℕ) : ℝ)⁻¹ * T idx))
        = (((2 ^ (idx.k : ℕ) : ℕ) : ℝ) * (((2 ^ (idx.k : ℕ) : ℕ) : ℝ)⁻¹))
          * (C idx.k * T idx) := by ring
      _ = 1 * (C idx.k * T idx) := by rw [two_pow_mul_inv_two_pow (idx.k : ℕ)]
      _ = C idx.k * T idx := one_mul _
  have key := sum_sigma_swap C
    (fun idx => (((2 ^ (idx.k : ℕ) : ℕ) : ℝ)⁻¹ * T idx))
  rw [Fintype.sum_sigma, Fintype.sum_sigma] at key
  calc ∑ idx : Idx n, C idx.k * T idx
      = ∑ idx : Idx n, ∑ y : Fin idx.k → ZMod 2,
          C idx.k * (((2 ^ (idx.k : ℕ) : ℕ) : ℝ)⁻¹ * T idx) := by
        refine Finset.sum_congr rfl (fun idx _ => ?_)
        rw [← hfix idx, sum_univ_const_real_pi]
    _ = ∑ idx : Idx n, ∑ y : Fin idx.k → ZMod 2,
          C idx.k * (((2 ^ (idx.k : ℕ) : ℕ) : ℝ)⁻¹
            * T ⟨idx.k, idx.H, y⟩) := key
    _ = ∑ idx : Idx n, (C idx.k * (((2 ^ (idx.k : ℕ) : ℕ) : ℝ)⁻¹))
          * ∑ y : Fin idx.k → ZMod 2, T ⟨idx.k, idx.H, y⟩ := by
        refine Finset.sum_congr rfl (fun idx _ => ?_)
        rw [Finset.mul_sum Finset.univ (fun y => T ⟨idx.k, idx.H, y⟩)
          (C idx.k * (((2 ^ (idx.k : ℕ) : ℕ) : ℝ)⁻¹))]
        exact Finset.sum_congr rfl (fun y _ => by ring)

/-- Matrix-vector products against scaled vectors. -/
lemma mulVec_smul {n : ℕ} (M : Matrix (F2Vec n) (F2Vec n) ℂ) (c : ℂ)
    (v : F2Vec n → ℂ) :
    M *ᵥ (c • v) = c • (M *ᵥ v) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun l _ => by ring)

/-- **Fourier-basis expansion of a quadratic form** (Theorem 1, key
computation): `⟨ψ₀|M|ψ₀⟩ = ∑_{i,i'} α̂_ī α̂_{i'} (M̂)_{i,i'}`. -/
theorem hat_expansion {n : ℕ} (ψ0 : F2Vec n → ℂ)
    (M : Matrix (F2Vec n) (F2Vec n) ℂ) :
    innerVec ψ0 (M *ᵥ ψ0)
      = ∑ i : F2Vec n, ∑ i' : F2Vec n,
          starRingEnd ℂ (fourierCoeff ψ0 i) * fourierCoeff ψ0 i' * hatM M i i' := by
  have h1 : ∀ i i' : F2Vec n,
      innerVec (fourierCoeff ψ0 i • hatKet i)
          (M *ᵥ (fourierCoeff ψ0 i' • hatKet i'))
      = starRingEnd ℂ (fourierCoeff ψ0 i) * fourierCoeff ψ0 i' * hatM M i i' := by
    intro i i'
    rw [mulVec_smul, innerVec_smul_left, innerVec_smul, hat_inner_eq_entry]
    ring
  have h2 : innerVec ψ0 (M *ᵥ ψ0)
      = innerVec (∑ i : F2Vec n, fourierCoeff ψ0 i • hatKet i)
          (M *ᵥ ∑ i' : F2Vec n, fourierCoeff ψ0 i' • hatKet i') := by
    conv_lhs => rw [fourier_decomposition ψ0]
  rw [h2, mulVec_sum, innerVec_sum_left]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [innerVec_sum_right]
  exact Finset.sum_congr rfl (fun i' _ => h1 i i')

/-- **Theorem 1** (arXiv:2510.07298v2, §3.1.3), witness form: the
quality of any symmetrized fine-grained unambiguous measurement on a
symmetric state set is determined by the Fourier coefficients of `ψ₀`
and the diagonal Fourier entries of the coset sums `F_H`. Together with
Proposition 7 (`rhoOf_symmetrize`), this is the paper's characterization
of `ρ(S)` as a maximum over Fourier-diagonal data. -/
theorem thm1_witness {n : ℕ} {C : Fin (n + 1) → ℝ}
    {F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ} {ψ : F2Vec n → F2Vec n → ℂ}
    (hsym : IsSymmetricSet ψ) (hsymm : IsSymmetrized F) :
    rhoOf C F ψ
      = ∑ idx : Idx n, (C idx.k * (((2 ^ (idx.k : ℕ) : ℕ) : ℝ)⁻¹))
          * ∑ i : F2Vec n,
            Complex.normSq (fourierCoeff (ψ 0) i) * (hatM (sumCoset F idx) i i).re := by
  rw [lemma1_rho_eq_rho2 hsym hsymm, rho2Of,
    sum_idx_cost_weight C (fun idx => (innerVec (ψ 0) (F idx *ᵥ ψ 0)).re)]
  refine Finset.sum_congr rfl (fun idx _ => ?_)
  refine congrArg ((C idx.k * (((2 ^ (idx.k : ℕ) : ℕ) : ℝ)⁻¹)) * ·) ?_
  have hkey : ∑ y : Fin idx.k → ZMod 2,
      (innerVec (ψ 0) (F ⟨idx.k, idx.H, y⟩ *ᵥ ψ 0)).re
      = (innerVec (ψ 0) (sumCoset F idx *ᵥ ψ 0)).re := by
    rw [sumCoset, sum_mulVec_any, innerVec_sum_right]
    exact (Complex.re_sum Finset.univ
      (fun y => innerVec (ψ 0) (F ⟨idx.k, idx.H, y⟩ *ᵥ ψ 0))).symm
  rw [hkey, hat_expansion (ψ 0) (sumCoset F idx), Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.re_sum, Finset.sum_eq_single i]
  · rw [← Complex.normSq_eq_conj_mul_self, re_mul_real]
  · intro i' _ hii'
    rw [prop8_offdiag hsymm idx (Ne.symm hii'), mul_zero, Complex.zero_re]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `2^{-n} · 2ⁿ = 1` scaling, boxed form. -/
lemma inv_two_pow_coe_cancel (n : ℕ) (z : ℂ) :
    (((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) * (((2 ^ n : ℕ) : ℂ) * z) = z := by
  rw [← mul_assoc, inv_two_pow_mul_two_pow, one_mul]

/-- **Theorem 1**, per-outcome form: when every parity matrix has full
rank, the coset sums may be replaced by `2^k` times single outcomes,
giving exactly the sum appearing in the paper's Theorem 1. -/
theorem thm1_witness_fullrank {n : ℕ} {C : Fin (n + 1) → ℝ}
    {F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ} {ψ : F2Vec n → F2Vec n → ℂ}
    (hsym : IsSymmetricSet ψ) (hsymm : IsSymmetrized F)
    (hfull : ∀ idx : Idx n, idx.IsFullRank) :
    rhoOf C F ψ = ∑ idx : Idx n, C idx.k * ∑ i : F2Vec n,
      Complex.normSq (fourierCoeff (ψ 0) i) * (hatM (F idx) i i).re := by
  rw [thm1_witness hsym hsymm]
  refine Finset.sum_congr rfl (fun idx _ => ?_)
  have hdiag : ∀ i : F2Vec n, (hatM (sumCoset F idx) i i).re
      = ((2 ^ (idx.k : ℕ) : ℕ) : ℝ) * (hatM (F idx) i i).re := by
    intro i
    have hd := prop8_diag hsymm (hfull idx) i
    have hre := congrArg Complex.re hd
    have hcast : (((2 ^ (idx.k : ℕ) : ℕ) : ℂ) * hatM (F idx) i i).re
        = ((2 ^ (idx.k : ℕ) : ℕ) : ℝ) * (hatM (F idx) i i).re := by
      rw [show (((2 ^ (idx.k : ℕ) : ℕ) : ℂ))
            = ((((2 ^ (idx.k : ℕ) : ℕ) : ℝ)) : ℂ)
          from (Complex.ofReal_natCast _).symm, re_mul_real]
    exact hre.trans hcast
  have hsum : ∑ i : F2Vec n,
        Complex.normSq (fourierCoeff (ψ 0) i) * (hatM (sumCoset F idx) i i).re
      = ((2 ^ (idx.k : ℕ) : ℕ) : ℝ)
          * ∑ i : F2Vec n, Complex.normSq (fourierCoeff (ψ 0) i)
            * (hatM (F idx) i i).re := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [hdiag i]),
      Finset.sum_congr rfl (fun i _ =>
        mul_left_comm (Complex.normSq (fourierCoeff (ψ 0) i))
          ((2 ^ (idx.k : ℕ) : ℕ) : ℝ) ((hatM (F idx) i i).re))]
    exact (Finset.mul_sum Finset.univ
      (fun i => Complex.normSq (fourierCoeff (ψ 0) i) * (hatM (F idx) i i).re)
      ((2 ^ (idx.k : ℕ) : ℕ) : ℝ)).symm
  have hcancel : ∀ S : ℝ,
      (C idx.k * (((2 ^ (idx.k : ℕ) : ℕ) : ℝ)⁻¹))
        * (((2 ^ (idx.k : ℕ) : ℕ) : ℝ) * S) = C idx.k * S := by
    intro S
    calc (C idx.k * (((2 ^ (idx.k : ℕ) : ℕ) : ℝ)⁻¹))
        * (((2 ^ (idx.k : ℕ) : ℕ) : ℝ) * S)
        = (((2 ^ (idx.k : ℕ) : ℕ) : ℝ) * (((2 ^ (idx.k : ℕ) : ℕ) : ℝ)⁻¹))
          * (C idx.k * S) := by ring
      _ = 1 * (C idx.k * S) := by rw [two_pow_mul_inv_two_pow (idx.k : ℕ)]
      _ = C idx.k * S := one_mul _
  rw [hsum, hcancel]

/-! ### Proposition 9: full dual support -/

/-- Full dual support (Definition 18): every Fourier coefficient of
`ψ₀` is nonzero. -/
def HasFullDualSupport {n : ℕ} (ψ : F2Vec n → F2Vec n → ℂ) : Prop :=
  ∀ y : F2Vec n, fourierCoeff (ψ 0) y ≠ 0

/-- Fourier inversion: coefficients are recovered from their character
sums (Proposition 9, proof ingredient). -/
lemma fourier_invert {n : ℕ} (c : F2Vec n → ℂ) (x₀ : F2Vec n) :
    c x₀ = (((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ)
      * ∑ y : F2Vec n, (∑ x, c x * phase (dotF2 x y)) * phase (dotF2 x₀ y) := by
  have hterm : ∀ x y : F2Vec n,
      (c x * phase (dotF2 x y)) * phase (dotF2 x₀ y)
      = c x * phase (dotF2 (x + x₀) y) := by
    intro x y
    have hp : phase (dotF2 (x + x₀) y)
        = phase (dotF2 x y) * phase (dotF2 x₀ y) := by
      rw [← phase_mul, ← dotF2_add_left]
    rw [hp]
    ring
  have hR : ((2 ^ n : ℕ) : ℂ) * c x₀
      = ∑ y : F2Vec n, (∑ x, c x * phase (dotF2 x y)) * phase (dotF2 x₀ y) := by
    have step1 : ∀ y : F2Vec n,
        (∑ x, c x * phase (dotF2 x y)) * phase (dotF2 x₀ y)
        = ∑ x, (c x * phase (dotF2 x y)) * phase (dotF2 x₀ y) :=
      fun y => Finset.sum_mul Finset.univ (fun x => c x * phase (dotF2 x y))
        (phase (dotF2 x₀ y))
    have step2 : ∀ x : F2Vec n,
        ∑ y, (c x * phase (dotF2 x y)) * phase (dotF2 x₀ y)
        = c x * (if x + x₀ = 0 then ((2 ^ n : ℕ) : ℂ) else 0) := by
      intro x
      rw [Finset.sum_congr rfl (fun y _ => hterm x y), ← Finset.mul_sum,
        char_sum_full (x + x₀)]
    have step3 : ∑ x : F2Vec n,
        c x * (if x + x₀ = 0 then ((2 ^ n : ℕ) : ℂ) else 0)
        = ((2 ^ n : ℕ) : ℂ) * c x₀ := by
      rw [Finset.sum_eq_single x₀]
      · rw [addSelf_zero x₀, if_pos rfl, mul_comm]
      · intro x _ hxx₀
        rw [if_neg (fun h0 => hxx₀ (add_eq_zero_iff_eq x x₀ |>.mp h0)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [Finset.sum_congr rfl (fun y _ => step1 y), Finset.sum_comm,
      Finset.sum_congr rfl (fun x _ => step2 x), step3]
  calc c x₀ = (((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) * (((2 ^ n : ℕ) : ℂ) * c x₀) :=
        (inv_two_pow_coe_cancel n (c x₀)).symm
    _ = (((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ)
          * ∑ y : F2Vec n, (∑ x, c x * phase (dotF2 x y)) * phase (dotF2 x₀ y) := by
        rw [hR]

/-- **Proposition 9** (arXiv:2510.07298v2, §3.2.1), independence half:
the states of a symmetric set with full dual support are linearly
independent. -/
theorem prop9_linear_indep {n : ℕ} {ψ : F2Vec n → F2Vec n → ℂ}
    (hsym : IsSymmetricSet ψ) (hfull : HasFullDualSupport ψ)
    (c : F2Vec n → ℂ) (hzero : ∑ x, c x • ψ x = 0) (x₀ : F2Vec n) :
    c x₀ = 0 := by
  have hin : ∀ y₀ : F2Vec n,
      innerVec (hatKet y₀) (∑ x, c x • ψ x)
      = fourierCoeff (ψ 0) y₀ * ∑ x, c x * phase (dotF2 x y₀) := by
    intro y₀
    have hpx : ∀ x : F2Vec n,
        innerVec (hatKet y₀) (c x • ψ x)
        = fourierCoeff (ψ 0) y₀ * (c x * phase (dotF2 x y₀)) := by
      intro x
      rw [innerVec_smul, hsym x, innerVec_mulVec', shiftX_conjTranspose,
        prop5_eigenvector x y₀, innerVec_smul_left, star_phase, hat_inner_coeff,
        dotF2_comm y₀ x]
      ring
    rw [innerVec_sum_right, Finset.sum_congr rfl (fun x _ => hpx x),
      Finset.mul_sum]
  have hg : ∀ y₀ : F2Vec n, ∑ x, c x * phase (dotF2 x y₀) = 0 := by
    intro y₀
    have h := hin y₀
    rw [hzero] at h
    have hmul : fourierCoeff (ψ 0) y₀ * ∑ x, c x * phase (dotF2 x y₀) = 0 := by
      rw [← h]
      simp [innerVec]
    exact (mul_eq_zero.mp hmul).resolve_left (hfull y₀)
  rw [fourier_invert c x₀,
    Finset.sum_eq_zero (fun y _ => by rw [hg y, zero_mul]), mul_zero]

/-- **Proposition 9**, spanning half: every Fourier ket lies in the span
of the states, with an explicit witness (the inverse-Fourier
combination weighted by `α̂_{y₀}^{-1}`). -/
theorem prop9_span_witness {n : ℕ} {ψ : F2Vec n → F2Vec n → ℂ}
    (hsym : IsSymmetricSet ψ) (hfull : HasFullDualSupport ψ) (y₀ : F2Vec n) :
    ∑ x : F2Vec n,
        ((((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) * phase (dotF2 x y₀)
          * (fourierCoeff (ψ 0) y₀)⁻¹) • ψ x
      = hatKet y₀ := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hpsi : ∀ x : F2Vec n, ψ x j
      = ∑ i, fourierCoeff (ψ 0) i * (phase (dotF2 i x) * hatKet i j) := by
    intro x
    have h1 : ψ x j = ∑ i : F2Vec n, fourierCoeff (ψ 0) i * hatKet i (j + x) := by
      rw [hsym x, shiftX_mulVec_apply x (ψ 0) j, ← fourier_expansion (ψ 0) (j + x)]
    rw [h1]
    exact Finset.sum_congr rfl (fun i _ => by
      simp only [hatKet_shift x i j])
  have hpp : ∀ i x : F2Vec n, phase (dotF2 x y₀) * phase (dotF2 i x)
      = phase (dotF2 (i + y₀) x) := by
    intro i x
    rw [← phase_mul, dotF2_comm x y₀, ← dotF2_add_left, add_comm y₀ i]
  have hmain : ∀ i : F2Vec n,
      ∑ x : F2Vec n, ((((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) * phase (dotF2 x y₀)
          * (fourierCoeff (ψ 0) y₀)⁻¹)
        * (fourierCoeff (ψ 0) i * (phase (dotF2 i x) * hatKet i j))
      = (if i + y₀ = 0 then (1 : ℂ) else 0) * hatKet i j := by
    intro i
    have hpull : ∀ x : F2Vec n,
        ((((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) * phase (dotF2 x y₀)
            * (fourierCoeff (ψ 0) y₀)⁻¹)
          * (fourierCoeff (ψ 0) i * (phase (dotF2 i x) * hatKet i j))
        = ((((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) * (fourierCoeff (ψ 0) y₀)⁻¹
            * (fourierCoeff (ψ 0) i * hatKet i j))
          * phase (dotF2 (i + y₀) x) := by
      intro x
      have hre : ((((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) * phase (dotF2 x y₀)
            * (fourierCoeff (ψ 0) y₀)⁻¹)
          * (fourierCoeff (ψ 0) i * (phase (dotF2 i x) * hatKet i j))
        = ((((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) * (fourierCoeff (ψ 0) y₀)⁻¹)
          * (phase (dotF2 x y₀) * phase (dotF2 i x))
          * (fourierCoeff (ψ 0) i * hatKet i j) := by ring
      rw [hre, hpp i x]
      ring
    rw [Finset.sum_congr rfl (fun x _ => hpull x), ← Finset.mul_sum Finset.univ
      (fun x => phase (dotF2 (i + y₀) x))
      ((((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) * (fourierCoeff (ψ 0) y₀)⁻¹
        * (fourierCoeff (ψ 0) i * hatKet i j)), char_sum_full (i + y₀)]
    by_cases hiy : i + y₀ = 0
    · have hiy₀ : i = y₀ := (add_eq_zero_iff_eq i y₀).mp hiy
      rw [if_pos hiy, hiy₀, addSelf_zero y₀, if_pos rfl]
      calc ((((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) * (fourierCoeff (ψ 0) y₀)⁻¹
            * (fourierCoeff (ψ 0) y₀ * hatKet y₀ j)) * ((2 ^ n : ℕ) : ℂ)
          = ((((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) * ((2 ^ n : ℕ) : ℂ))
            * (((fourierCoeff (ψ 0) y₀)⁻¹ * fourierCoeff (ψ 0) y₀)
              * hatKet y₀ j) := by ring
        _ = 1 * (((fourierCoeff (ψ 0) y₀)⁻¹ * fourierCoeff (ψ 0) y₀)
              * hatKet y₀ j) := by rw [inv_two_pow_mul_two_pow]
        _ = 1 * (1 * hatKet y₀ j) := by rw [inv_mul_cancel₀ (hfull y₀)]
        _ = 1 * hatKet y₀ j := by ring
    · rw [if_neg hiy, if_neg hiy, mul_zero, zero_mul]
  have hstep : ∀ x : F2Vec n,
      ((((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) * phase (dotF2 x y₀)
          * (fourierCoeff (ψ 0) y₀)⁻¹) * ψ x j
      = ∑ i : F2Vec n, ((((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) * phase (dotF2 x y₀)
          * (fourierCoeff (ψ 0) y₀)⁻¹)
        * (fourierCoeff (ψ 0) i * (phase (dotF2 i x) * hatKet i j)) := by
    intro x
    rw [hpsi x, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x _ => hstep x), Finset.sum_comm,
    Finset.sum_congr rfl (fun i _ => hmain i), Finset.sum_eq_single y₀]
  · rw [addSelf_zero y₀, if_pos rfl, one_mul]
  · intro i _ hiy
    rw [if_neg (fun h0 => hiy ((add_eq_zero_iff_eq i y₀).mp h0)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Qatlib.Papers.UnambigMeas25.MainResults
