/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Qatlib.Papers.HamEvoPrec13.MainResults.SparseMatching
import Qatlib.Papers.HamEvoPrec13.MainResults.MatchedBlocks
import Qatlib.Papers.HamEvoPrec13.MainResults.SparseRounding

/-!
# Lemma 1: a one-sparse Hamiltonian is a sum of commuting self-inverse Hamiltonians

Berry--Cleve--Somma, "Exponential improvement in precision for Hamiltonian-evolution
simulation", fixed arXiv:1308.5424v3, Lemma 1 (statement page 2, proof page 3).

The paper proves that a real one-sparse Hamiltonian `G` can be approximated within
max-norm distance `γ` by an equally weighted sum of `O(‖G‖max / γ)` commuting
self-inverse Hamiltonians. The construction has three layers, mirrored here:

* split `G` into its diagonal and off-diagonal components, which commute because a
  one-sparse row cannot contain both;
* round every value to a multiple `(h/ℓ) g` of the granularity `g/ℓ`, with error at most
  `g/(2ℓ)` (Eq. (3));
* fill the zero `2 × 2` blocks with `±1` so that every summand squares to the identity
  (Eq. (4)), keeping the summands in the same block algebra so that they commute.

The result is `4 ℓ` summands of equal weight `g/(2 ℓ)`, which is `O(g/γ)` of them.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.HamEvoPrec13.MainResults

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rounded off-diagonal value of row `a`.

Rows without an off-diagonal nonzero entry round to `0`, so fixed points of the matching
never contribute an off-diagonal block. -/
def offRound (G : Matrix n n ℝ) (g : ℝ) (ℓ : ℕ) (a : n) : ℤ :=
  if mateZero G a = a then 0 else round ((ℓ : ℝ) * G a (mateZero G a) / g)

/-- The rounded diagonal value of row `a`.

Rows with an off-diagonal nonzero entry round to `0`: a one-sparse row has a single
nonzero entry, so it cannot also carry a diagonal one. -/
def diagRound (G : Matrix n n ℝ) (g : ℝ) (ℓ : ℕ) (a : n) : ℤ :=
  if mateZero G a = a then round ((ℓ : ℝ) * G a a / g) else 0

/-- The `i`-th unit coefficient of the rounded off-diagonal value of row `a`. -/
def offCoeff (G : Matrix n n ℝ) (g : ℝ) (ℓ : ℕ) (i : Fin ℓ) (a : n) : ℝ :=
  unitCoeff (offRound G g ℓ a) (i : ℕ)

/-- The `i`-th unit coefficient of the rounded diagonal value of row `a`. -/
def diagCoeff (G : Matrix n n ℝ) (g : ℝ) (ℓ : ℕ) (i : Fin ℓ) (a : n) : ℝ :=
  unitCoeff (diagRound G g ℓ a) (i : ℕ)

/-- Off-diagonal summand of weight `g/(2ℓ)`: the coefficient `offCoeff` sits in the
matched off-diagonal slot, and the complementary `±1` fills the block where the
coefficient vanishes (Eq. (4)). -/
def offPiece (G : Matrix n n ℝ) (g : ℝ) (ℓ : ℕ) (i : Fin ℓ) (pos : Bool) : Matrix n n ℝ :=
  matchedBlock (mateZero G)
    (fun a => if offCoeff G g ℓ i a = 0 then (if pos then 1 else -1) else 0)
    (fun a => offCoeff G g ℓ i a)

/-- Diagonal summand of weight `g/(2ℓ)`: the complementary pair of `±1` diagonal blocks
whose average is the rounded diagonal value. -/
def diagPiece (G : Matrix n n ℝ) (g : ℝ) (ℓ : ℕ) (i : Fin ℓ) (pos : Bool) : Matrix n n ℝ :=
  matchedBlock (mateZero G)
    (fun a => if pos then (if 0 ≤ diagCoeff G g ℓ i a then 1 else -1)
      else (if 0 < diagCoeff G g ℓ i a then 1 else -1))
    (fun _ => 0)

/-- The full family of `4ℓ` summands: `2ℓ` off-diagonal ones followed by `2ℓ` diagonal
ones. -/
def paperPiece (G : Matrix n n ℝ) (g : ℝ) (ℓ : ℕ) :
    (Fin ℓ × Bool) ⊕ (Fin ℓ × Bool) → Matrix n n ℝ
  | Sum.inl p => offPiece G g ℓ p.1 p.2
  | Sum.inr p => diagPiece G g ℓ p.1 p.2

/-- The matching of a one-sparse symmetric matrix is involutive everywhere: fixed points
are fixed by definition and genuine partners are paired by `mateZero_mateZero`. -/
theorem mateZero_involutive {G : Matrix n n ℝ} (hG : G.IsSymm) (h1 : IsOneSparse G) (a : n) :
    mateZero G (mateZero G a) = a := by
  by_cases h : mateZero G a = a
  · rw [h, h]
  · exact mateZero_mateZero hG h1 h

/-- Evaluation of the rounded off-diagonal value at a genuine matched pair. -/
theorem offRound_eq_round {G : Matrix n n ℝ} {g : ℝ} {ℓ : ℕ} {a : n}
    (ha : mateZero G a ≠ a) :
    offRound G g ℓ a = round ((ℓ : ℝ) * G a (mateZero G a) / g) := by
  unfold offRound
  rw [if_neg ha]

/-- Evaluation of the rounded off-diagonal value at a fixed point. -/
theorem offRound_eq_zero {G : Matrix n n ℝ} {g : ℝ} {ℓ : ℕ} {a : n}
    (ha : mateZero G a = a) : offRound G g ℓ a = 0 := by
  unfold offRound
  rw [if_pos ha]

/-- Evaluation of the rounded diagonal value at a fixed point. -/
theorem diagRound_eq_round {G : Matrix n n ℝ} {g : ℝ} {ℓ : ℕ} {a : n}
    (ha : mateZero G a = a) :
    diagRound G g ℓ a = round ((ℓ : ℝ) * G a a / g) := by
  unfold diagRound
  rw [if_pos ha]

/-- Evaluation of the rounded diagonal value at a genuine matched pair. -/
theorem diagRound_eq_zero {G : Matrix n n ℝ} {g : ℝ} {ℓ : ℕ} {a : n}
    (ha : mateZero G a ≠ a) : diagRound G g ℓ a = 0 := by
  unfold diagRound
  rw [if_neg ha]

/-- The rounded off-diagonal value is constant on matched pairs, because the two entries
of a symmetric one-sparse matrix at a pair agree. -/
theorem offRound_pair {G : Matrix n n ℝ} (hG : G.IsSymm) (h1 : IsOneSparse G) (g : ℝ) (ℓ : ℕ)
    (a : n) : offRound G g ℓ (mateZero G a) = offRound G g ℓ a := by
  by_cases ha : mateZero G a = a
  · have hfix : mateZero G (mateZero G a) = mateZero G a := by rw [ha]; exact ha
    unfold offRound
    rw [if_pos hfix]
    rw [if_pos ha]
  · have hinv := mateZero_mateZero hG h1 ha
    have hne : mateZero G (mateZero G a) ≠ mateZero G a := by
      rw [hinv]; exact Ne.symm ha
    unfold offRound
    rw [if_neg hne]
    rw [if_neg ha]
    rw [hinv]
    exact congrArg round (by rw [hG.apply a (mateZero G a)])

/-- The rounded diagonal value is constant on matched pairs: both endpoints of a pair
round to `0`, and fixed points are their own partner. -/
theorem diagRound_pair {G : Matrix n n ℝ} (hG : G.IsSymm) (h1 : IsOneSparse G) (g : ℝ) (ℓ : ℕ)
    (a : n) : diagRound G g ℓ (mateZero G a) = diagRound G g ℓ a := by
  by_cases ha : mateZero G a = a
  · have hfix : mateZero G (mateZero G a) = mateZero G a := by rw [ha]; exact ha
    unfold diagRound
    rw [if_pos hfix]
    rw [if_pos ha]
    rw [ha]
  · have hinv := mateZero_mateZero hG h1 ha
    have hne : mateZero G (mateZero G a) ≠ mateZero G a := by
      rw [hinv]; exact Ne.symm ha
    unfold diagRound
    rw [if_neg hne]
    rw [if_neg ha]

/-- The off-diagonal coefficients are constant on matched pairs. -/
theorem offCoeff_pair {G : Matrix n n ℝ} (hG : G.IsSymm) (h1 : IsOneSparse G) (g : ℝ) (ℓ : ℕ)
    (i : Fin ℓ) (a : n) : offCoeff G g ℓ i (mateZero G a) = offCoeff G g ℓ i a := by
  unfold offCoeff
  rw [offRound_pair hG h1 g ℓ a]

/-- The diagonal coefficients are constant on matched pairs. -/
theorem diagCoeff_pair {G : Matrix n n ℝ} (hG : G.IsSymm) (h1 : IsOneSparse G) (g : ℝ) (ℓ : ℕ)
    (i : Fin ℓ) (a : n) : diagCoeff G g ℓ i (mateZero G a) = diagCoeff G g ℓ i a := by
  unfold diagCoeff
  rw [diagRound_pair hG h1 g ℓ a]

/-- Every off-diagonal summand satisfies the matched-block coefficient conditions, hence is
a symmetric one-sparse self-inverse Hamiltonian. -/
theorem offPiece_matchedUnit {G : Matrix n n ℝ} (hG : G.IsSymm) (h1 : IsOneSparse G)
    (g : ℝ) (ℓ : ℕ) (i : Fin ℓ) (pos : Bool) :
    MatchedUnit (mateZero G)
      (fun a => if offCoeff G g ℓ i a = 0 then (if pos then 1 else -1) else 0)
      (fun a => offCoeff G g ℓ i a) := by
  refine ⟨mateZero_involutive hG h1, ?_, offCoeff_pair hG h1 g ℓ i, ?_, ?_, ?_⟩
  · intro a
    rw [offCoeff_pair hG h1 g ℓ i a]
  · intro a ha
    rw [offCoeff, show offRound G g ℓ a = 0 from by unfold offRound; rw [if_pos ha]]
    exact unitCoeff_zero i
  · intro a
    exact indicator_mul_zero _ _
  · intro a
    exact indicator_unit _ _ (signed_one_unit pos)
      (unitCoeff_eq_one_or_zero_or_neg (offRound G g ℓ a) (i : ℕ))

/-- Every diagonal summand satisfies the matched-block coefficient conditions: its
off-diagonal coefficient vanishes and its diagonal coefficient is a signed one. -/
theorem diagPiece_matchedUnit {G : Matrix n n ℝ} (hG : G.IsSymm) (h1 : IsOneSparse G)
    (g : ℝ) (ℓ : ℕ) (i : Fin ℓ) (pos : Bool) :
    MatchedUnit (mateZero G)
      (fun a => if pos then (if 0 ≤ diagCoeff G g ℓ i a then 1 else -1)
        else (if 0 < diagCoeff G g ℓ i a then 1 else -1))
      (fun _ => 0) := by
  refine ⟨mateZero_involutive hG h1, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [diagCoeff_pair hG h1 g ℓ i a]
  · intro a; rfl
  · intro a _
    rfl
  · intro a
    rw [mul_zero]
  · intro a
    have hd : (if pos then (if 0 ≤ diagCoeff G g ℓ i a then (1 : ℝ) else -1)
        else (if 0 < diagCoeff G g ℓ i a then (1 : ℝ) else -1)) = 1 ∨
        (if pos then (if 0 ≤ diagCoeff G g ℓ i a then (1 : ℝ) else -1)
          else (if 0 < diagCoeff G g ℓ i a then (1 : ℝ) else -1)) = -1 := by
      cases pos with
      | true =>
          by_cases h : 0 ≤ diagCoeff G g ℓ i a
          · exact Or.inl (by simp [h])
          · exact Or.inr (by simp [h])
      | false =>
          by_cases h : 0 < diagCoeff G g ℓ i a
          · exact Or.inl (by simp [h])
          · exact Or.inr (by simp [h])
    rcases hd with hd | hd <;> rw [hd] <;> norm_num

/-- The two off-diagonal variants average to the rounded off-diagonal value at the matched
slot and cancel everywhere else. -/
theorem offPiece_sum_apply (G : Matrix n n ℝ) (g : ℝ) (ℓ : ℕ)
    (i : Fin ℓ) (a b : n) :
    offPiece G g ℓ i true a b + offPiece G g ℓ i false a b
      = if b = mateZero G a then 2 * offCoeff G g ℓ i a else 0 := by
  by_cases hba : b = a
  · subst b
    by_cases hma : mateZero G a = a
    · have hy : offCoeff G g ℓ i a = 0 := by
        rw [offCoeff, offRound_eq_zero hma]
        exact unitCoeff_zero i
      simp [offPiece, matchedBlock, hma, hy]
    · simp only [offPiece, matchedBlock, if_pos rfl, if_neg (Ne.symm hma)]
      by_cases hy : offCoeff G g ℓ i a = 0 <;> simp [hy]
  · by_cases hbm : b = mateZero G a
    · subst b
      have hma : mateZero G a ≠ a := hba
      simp [offPiece, matchedBlock, hma]
      ring
    · simp [offPiece, matchedBlock, hba, hbm]

/-- The two diagonal variants average to the rounded diagonal value on the diagonal and
cancel everywhere else. -/
theorem diagPiece_sum_apply (G : Matrix n n ℝ) (g : ℝ) (ℓ : ℕ) (i : Fin ℓ) (a b : n) :
    diagPiece G g ℓ i true a b + diagPiece G g ℓ i false a b
      = if b = a then 2 * diagCoeff G g ℓ i a else 0 := by
  by_cases hba : b = a
  · subst b
    have ht : diagCoeff G g ℓ i a = 1 ∨ diagCoeff G g ℓ i a = 0 ∨ diagCoeff G g ℓ i a = -1 :=
      unitCoeff_eq_one_or_zero_or_neg (diagRound G g ℓ a) (i : ℕ)
    rcases ht with h | h | h <;> (simp [diagPiece, matchedBlock, h]; try norm_num)
  · by_cases hbm : b = mateZero G a
    · subst b
      simp [diagPiece, matchedBlock, hba]
    · simp [diagPiece, matchedBlock, hba, hbm]

/-- The entrywise sum over the `4ℓ` summands splits into the `2ℓ` off-diagonal and `2ℓ`
diagonal variants. -/
theorem sum_paperPiece_apply (G : Matrix n n ℝ) (g : ℝ) (ℓ : ℕ) (a b : n) :
    ∑ t, paperPiece G g ℓ t a b
      = (∑ i : Fin ℓ, (offPiece G g ℓ i true a b + offPiece G g ℓ i false a b))
        + ∑ i : Fin ℓ, (diagPiece G g ℓ i true a b + diagPiece G g ℓ i false a b) := by
  rw [Fintype.sum_sum_type]
  congr 1
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool]
    rfl
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool]
    rfl

/-- The rounded off-diagonal value lies within the granularity count `ℓ`. -/
theorem abs_offRound_le {G : Matrix n n ℝ} {g : ℝ} (hg : 0 < g) (ℓ : ℕ)
    (hbound : ∀ a b, |G a b| ≤ g) (a : n) : |offRound G g ℓ a| ≤ (ℓ : ℤ) := by
  unfold offRound
  by_cases ha : mateZero G a = a
  · rw [if_pos ha]; simp
  · rw [if_neg ha]
    exact abs_round_le_of_abs_le hg (hbound a (mateZero G a))

/-- The rounded diagonal value lies within the granularity count `ℓ`. -/
theorem abs_diagRound_le {G : Matrix n n ℝ} {g : ℝ} (hg : 0 < g) (ℓ : ℕ)
    (hbound : ∀ a b, |G a b| ≤ g) (a : n) : |diagRound G g ℓ a| ≤ (ℓ : ℤ) := by
  unfold diagRound
  by_cases ha : mateZero G a = a
  · rw [if_pos ha]
    exact abs_round_le_of_abs_le hg (hbound a a)
  · rw [if_neg ha]; simp

/-- The entrywise sum over the `4ℓ` summands is the rounded value: `2 · offRound` at the
matched slot and `2 · diagRound` on the diagonal. -/
theorem sum_paperPiece_eq {G : Matrix n n ℝ} {g : ℝ}
    (hg : 0 < g) (ℓ : ℕ) (hbound : ∀ a b, |G a b| ≤ g) (a b : n) :
    ∑ t, paperPiece G g ℓ t a b
      = (if b = mateZero G a then 2 * (offRound G g ℓ a : ℝ) else 0)
        + (if b = a then 2 * (diagRound G g ℓ a : ℝ) else 0) := by
  rw [sum_paperPiece_apply]
  congr 1
  · rw [Finset.sum_congr rfl fun i _ => offPiece_sum_apply G g ℓ i a b]
    by_cases hb : b = mateZero G a
    · rw [if_pos hb, Finset.sum_congr rfl fun i _ => if_pos hb, ← Finset.mul_sum]
      congr 1
      exact sum_unitCoeff ℓ (offRound G g ℓ a) (abs_offRound_le hg ℓ hbound a)
    · rw [if_neg hb, Finset.sum_congr rfl fun i _ => if_neg hb]
      simp
  · rw [Finset.sum_congr rfl fun i _ => diagPiece_sum_apply G g ℓ i a b]
    by_cases hb : b = a
    · rw [if_pos hb, Finset.sum_congr rfl fun i _ => if_pos hb, ← Finset.mul_sum]
      congr 1
      exact sum_unitCoeff ℓ (diagRound G g ℓ a) (abs_diagRound_le hg ℓ hbound a)
    · rw [if_neg hb, Finset.sum_congr rfl fun i _ => if_neg hb]
      simp

/-- **Lemma 1 of the paper.** A real one-sparse Hamiltonian `G` with entries bounded by `g`
is approximated within max-norm distance `γ` by an equally weighted sum of
`4 ⌈g/(2γ)⌉` commuting self-inverse one-sparse symmetric Hamiltonians of weight
`g/(2 ⌈g/(2γ)⌉)`, and `4 ⌈g/(2γ)⌉ ≤ 2 g / γ + 4` is the paper's `O(‖G‖max/γ)` count. -/
theorem lemma_one_decomposition (G : Matrix n n ℝ) (hG : G.IsSymm) (h1 : IsOneSparse G)
    (g γ : ℝ) (hg : 0 < g) (hγ : 0 < γ) (hbound : ∀ a b, |G a b| ≤ g) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ g / (2 * (ℓ : ℝ)) ≤ γ ∧ (4 * (ℓ : ℝ)) * γ ≤ 2 * g + 4 * γ ∧
      ∃ U : (Fin ℓ × Bool) ⊕ (Fin ℓ × Bool) → Matrix n n ℝ,
        (∀ t, (U t).IsSymm) ∧ (∀ t, IsOneSparse (U t)) ∧
        (∀ t, U t * U t = 1) ∧ (∀ t t', Commute (U t) (U t')) ∧
        (∀ a b, |G a b - (g / (2 * (ℓ : ℝ))) * ∑ t, U t a b| ≤ γ) := by
  set L : ℕ := ⌈g / (2 * γ)⌉₊ with hL
  have hgγ : 0 < g / (2 * γ) := by positivity
  have hLpos : 0 < L := by
    rw [hL]; exact Nat.ceil_pos.mpr hgγ
  have hLge : g / (2 * γ) ≤ (L : ℝ) := by
    rw [hL]; exact Nat.le_ceil _
  have hLlt : (L : ℝ) < g / (2 * γ) + 1 := by
    rw [hL]
    exact_mod_cast Nat.ceil_lt_add_one (le_of_lt hgγ)
  have hgran : g / (2 * (L : ℝ)) ≤ γ := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (L : ℝ))]
    have h2 : g ≤ (2 * γ) * (L : ℝ) := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * γ)).mp hLge
      linarith
    linarith
  have hcount : (4 * (L : ℝ)) * γ ≤ 2 * g + 4 * γ := by
    have hLle : (L : ℝ) ≤ g / (2 * γ) + 1 := le_of_lt hLlt
    have hmul : (L : ℝ) * γ ≤ (g / (2 * γ) + 1) * γ :=
      mul_le_mul_of_nonneg_right hLle hγ.le
    have hsimp : (g / (2 * γ) + 1) * γ = g / 2 + γ := by
      field_simp
    nlinarith [hmul, hsimp]
  refine ⟨L, hLpos, hgran, hcount, paperPiece G g L, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (⟨i, pos⟩ | ⟨i, pos⟩)
    · exact matchedBlock_isSymm (offPiece_matchedUnit hG h1 g L i pos)
    · exact matchedBlock_isSymm (diagPiece_matchedUnit hG h1 g L i pos)
  · rintro (⟨i, pos⟩ | ⟨i, pos⟩)
    · exact matchedBlock_isOneSparse (offPiece_matchedUnit hG h1 g L i pos)
    · exact matchedBlock_isOneSparse (diagPiece_matchedUnit hG h1 g L i pos)
  · rintro (⟨i, pos⟩ | ⟨i, pos⟩)
    · exact matchedBlock_mul_self (offPiece_matchedUnit hG h1 g L i pos)
    · exact matchedBlock_mul_self (diagPiece_matchedUnit hG h1 g L i pos)
  · rintro (⟨i, pos⟩ | ⟨i, pos⟩) (⟨j, pos'⟩ | ⟨j, pos'⟩)
    · exact matchedBlock_mul_comm (offPiece_matchedUnit hG h1 g L i pos)
        (offPiece_matchedUnit hG h1 g L j pos')
    · exact matchedBlock_mul_comm (offPiece_matchedUnit hG h1 g L i pos)
        (diagPiece_matchedUnit hG h1 g L j pos')
    · exact matchedBlock_mul_comm (diagPiece_matchedUnit hG h1 g L i pos)
        (offPiece_matchedUnit hG h1 g L j pos')
    · exact matchedBlock_mul_comm (diagPiece_matchedUnit hG h1 g L i pos)
        (diagPiece_matchedUnit hG h1 g L j pos')
  · intro a b
    by_cases hbm : b = mateZero G a
    · by_cases hba : b = a
      · -- fixed point of the matching: only the diagonal value is nonzero
        have hfix : mateZero G a = a := by rw [← hbm, hba]
        have hoff0 : (offRound G g L a : ℝ) = 0 := by
          rw [show offRound G g L a = 0 from by unfold offRound; rw [if_pos hfix]]
          norm_num
        have hdiag : (diagRound G g L a : ℝ) = (round ((L : ℝ) * G a a / g) : ℝ) := by
          rw [show diagRound G g L a = round ((L : ℝ) * G a a / g) from by
            unfold diagRound; rw [if_pos hfix]]
        rw [sum_paperPiece_eq hg L hbound a b, if_pos hbm, if_pos hba, hoff0, hdiag,
          hba]
        have hsimp : (g / (2 * (L : ℝ))) * (2 * (0 : ℝ) + 2 * (round ((L : ℝ) * G a a / g) : ℝ))
            = (g / (L : ℝ)) * (round ((L : ℝ) * G a a / g) : ℝ) := by
          field_simp
          ring
        rw [hsimp]
        calc |G a a - (g / (L : ℝ)) * (round ((L : ℝ) * G a a / g) : ℝ)| ≤ g / (2 * L) :=
              abs_sub_round_granularity hg hLpos
          _ ≤ γ := hgran
      · -- matched off-diagonal entry
        have hoff : (offRound G g L a : ℝ)
            = (round ((L : ℝ) * G a (mateZero G a) / g) : ℝ) := by
          rw [show offRound G g L a = round ((L : ℝ) * G a (mateZero G a) / g) from by
            unfold offRound
            rw [if_neg (by intro hh; exact hba (by rw [hbm, hh]))]]
        rw [sum_paperPiece_eq hg L hbound a b, if_pos hbm, if_neg hba, hoff, hbm]
        have hsimp : (g / (2 * (L : ℝ)))
              * (2 * (round ((L : ℝ) * G a (mateZero G a) / g) : ℝ) + 0)
            = (g / (L : ℝ)) * (round ((L : ℝ) * G a (mateZero G a) / g) : ℝ) := by
          field_simp
          ring
        rw [hsimp]
        calc |G a (mateZero G a) - (g / (L : ℝ)) * (round ((L : ℝ) * G a (mateZero G a) / g) : ℝ)|
              ≤ g / (2 * L) := abs_sub_round_granularity hg hLpos
          _ ≤ γ := hgran
    · by_cases hba : b = a
      · -- pair row's diagonal entry vanishes and the diagonal coefficient rounds to zero
        have hne : mateZero G a ≠ a := by
          intro hh; exact hbm (by rw [hba, hh])
        have hdiag0 : (diagRound G g L a : ℝ) = 0 := by
          rw [show diagRound G g L a = 0 from by unfold diagRound; rw [if_neg hne]]
          norm_num
        have hGa : G a b = 0 := by rw [hba]; exact mateZero_diag_eq_zero h1 hne
        rw [sum_paperPiece_eq hg L hbound a b, if_neg hbm, if_pos hba, hdiag0, hGa]
        simp [hγ.le]
      · -- outside the diagonal and the matching everything vanishes
        have hGa : G a b = 0 := mateZero_zero_of_ne h1 hba hbm
        rw [sum_paperPiece_eq hg L hbound a b, if_neg hbm, if_neg hba, hGa]
        simp [hγ.le]

end Qatlib.Papers.HamEvoPrec13.MainResults
