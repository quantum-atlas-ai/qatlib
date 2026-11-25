/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CssCodeCS96.Correction.CharacterBasis
public import Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecodingDefs
public import Qatlib.Papers.CssCodeCS96.Construction.SourceCoords
public import Qatlib.Papers.CssCodeCS96.Construction.Steane
import Mathlib.LinearAlgebra.Dimension.Constructions
import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# The two source codewords of the seven-qubit example

The fixed source writes the two logical codewords of the nested-code construction as normalized
superpositions over a coset of the smaller code. For the seven-qubit example the smaller code is
the row space of the Steane check matrix, the `[7,3,4]` simplex code, and the two logical states
are its coset superposition and the superposition of the coset shifted by a weight-three word of
the `[7,4,3]` Hamming kernel.

The module defines the two amplitude vectors coordinate by coordinate, proves that both lie in the
CSS codespace of `steaneData`, and proves that they span it. The states are written without their
normalizing scalar `2^(-3/2)`; multiplication by a nonzero scalar does not change the span, and the
docstrings record the normalized form.

## Main statements

* `mem_cssCodespace_iff`: the codespace of a `CssData` is the joint fixed space of its check
  operators.
* `cssPauliX_cosetState` and `cssPauliZ_cosetState`: the check operators fix every coset
  superposition over a self-orthogonal row space whose shift is orthogonal to it.
* `steane_source_span`: the CSS codespace of the seven-qubit code is spanned by the two source
  codewords.

## References

* [Calderbank and Shor, 1996][CalderbankShor1996], §III Eq. (2) and Eq. (6)
-/

namespace Qatlib.Papers.CssCodeCS96.Construction

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Papers.CssCodeCS96.Construction
open Qatlib.Papers.CssCodeCS96.Correction
open scoped Matrix

variable {ι κX κZ : Type*} [Fintype ι] [Fintype κX] [Fintype κZ] [DecidableEq ι]

omit [Fintype κX] [Fintype κZ] in
/-- An amplitude vector lies in the CSS codespace exactly when every X-check and every Z-check
operator fixes it. -/
theorem mem_cssCodespace_iff (c : CssData ι κX κZ) (v : (ι → ZMod 2) → ℂ) :
    v ∈ cssCodespace c ↔
      (∀ i, cssPauliX (c.hX i) *ᵥ v = v) ∧ (∀ j, cssPauliZ (c.hZ j) *ᵥ v = v) := by
  rw [cssCodespace, Submodule.mem_inf, cssXStabilized, cssZStabilized, Submodule.mem_iInf,
    Submodule.mem_iInf]
  constructor
  · rintro ⟨hx, hz⟩
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have h := hx i
      rw [cssXCheckKernel, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
        Matrix.one_mulVec, sub_eq_zero] at h
      exact h
    · have h := hz j
      rw [cssZCheckKernel, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
        Matrix.one_mulVec, sub_eq_zero] at h
      exact h
  · rintro ⟨hx, hz⟩
    refine ⟨fun i => ?_, fun j => ?_⟩
    · rw [cssXCheckKernel, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
        Matrix.one_mulVec, sub_eq_zero]
      exact hx i
    · rw [cssZCheckKernel, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
        Matrix.one_mulVec, sub_eq_zero]
      exact hz j

variable {n : ℕ}

/-- The uniform superposition over a coset of a binary submodule, written coordinate by
coordinate: the amplitude is one on the coset `K + e` and zero elsewhere. The normalized state of
the source is `2 ^ (-finrank K / 2)` times this vector. -/
noncomputable def cosetState (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (e : Fin n → ZMod 2) :
    (Fin n → ZMod 2) → ℂ := by
  classical
  exact fun a => if a + e ∈ K then 1 else 0

/-- Every check vector of a submodule fixes the coset superposition by translation. -/
theorem cssPauliX_cosetState {K : Submodule (ZMod 2) (Fin n → ZMod 2)} {e : Fin n → ZMod 2}
    {x : Fin n → ZMod 2} (hx : x ∈ K) : cssPauliX x *ᵥ cosetState K e = cosetState K e := by
  classical
  funext a
  rw [cssPauliX_mulVec_apply]
  show (if (a + x) + e ∈ K then 1 else 0) = (if a + e ∈ K then 1 else 0)
  rw [add_right_comm]
  by_cases h : a + e ∈ K
  · rw [ite_eq_left h, ite_eq_left (K.add_mem h hx)]
  · rw [ite_eq_right h]
    rw [ite_eq_right]
    intro hc
    exact h (by have := K.add_mem hc hx; rwa [add_assoc, binary_add_self, add_zero] at this)

/-- Every check vector of a self-orthogonal submodule whose shift is orthogonal to the submodule
fixes the coset superposition diagonally. -/
theorem cssPauliZ_cosetState {K : Submodule (ZMod 2) (Fin n → ZMod 2)} {e : Fin n → ZMod 2}
    (hss : ∀ a ∈ K, ∀ b ∈ K, bitDot a b = 0) (he : ∀ a ∈ K, bitDot a e = 0)
    {z : Fin n → ZMod 2} (hz : z ∈ K) : cssPauliZ z *ᵥ cosetState K e = cosetState K e := by
  classical
  funext a
  rw [cssPauliZ_mulVec_apply]
  show phaseOfBit (bitDot z a) * (if a + e ∈ K then 1 else 0) = (if a + e ∈ K then 1 else 0)
  by_cases h : a + e ∈ K
  · rw [ite_eq_left h, mul_one]
    have hae : a = (a + e) + e := by rw [add_assoc, binary_add_self, add_zero]
    have hzero : bitDot z a = 0 := by
      rw [hae, bitDot_add_right, hss z hz (a + e) h, he z hz, add_zero]
    rw [hzero, phaseOfBit_zero]
  · rw [ite_eq_right h, mul_zero]

/-- The row space of the Steane check matrix: the `[7,3,4]` simplex code, which is the classical
dual of the seven-qubit Steane kernel. -/
def simplexSpace : Submodule (ZMod 2) (Fin 7 → ZMod 2) :=
  LinearMap.range (Matrix.mulVecLin steaneHᵀ)

/-- A word lies in the simplex space exactly when it is a check-label combination. -/
theorem mem_simplexSpace {z : Fin 7 → ZMod 2} :
    z ∈ simplexSpace ↔ ∃ u : Fin 3 → ZMod 2, steaneHᵀ *ᵥ u = z := Iff.rfl

/-- Each check label contributes its check row to the simplex space. -/
theorem steaneH_transpose_mulVec_single (k : Fin 3) :
    steaneHᵀ *ᵥ (Pi.single k (1 : ZMod 2)) = steaneRow k := by
  funext i
  rw [Matrix.mulVec, dotProduct]
  classical
  rw [Finset.sum_eq_single k]
  · rw [Matrix.transpose_apply]
    have hs : (Pi.single k (1 : ZMod 2) : Fin 3 → ZMod 2) k = 1 := by simp
    rw [hs, mul_one]
    rfl
  · intro j _ hj
    rw [Matrix.transpose_apply]
    have hz : (Pi.single k (1 : ZMod 2) : Fin 3 → ZMod 2) j = 0 := by
      simp [Ne.symm hj]
    rw [hz, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- Each check row belongs to the simplex space. -/
theorem steaneRow_mem_simplexSpace (k : Fin 3) : steaneRow k ∈ simplexSpace :=
  ⟨Pi.single k (1 : ZMod 2), steaneH_transpose_mulVec_single k⟩

/-- The simplex space is self-orthogonal: the check matrix is orthogonal to its own transpose. -/
theorem bitDot_simplex {u v : Fin 3 → ZMod 2} :
    bitDot (steaneHᵀ *ᵥ u) (steaneHᵀ *ᵥ v) = 0 := by
  have hstep : bitDot (steaneHᵀ *ᵥ u) (steaneHᵀ *ᵥ v) = u ⬝ᵥ (steaneH *ᵥ (steaneHᵀ *ᵥ v)) := by
    have h1 := Matrix.dotProduct_mulVec u steaneH (steaneHᵀ *ᵥ v)
    have h2 : u ᵥ* steaneH = steaneHᵀ *ᵥ u := by
      simpa using Matrix.vecMul_transpose (A := steaneHᵀ) u
    rw [bitDot, h1, h2]
  rw [hstep, Matrix.mulVec_mulVec, steaneH_mul_transpose, Matrix.zero_mulVec, dotProduct_zero]

/-- Every simplex word is orthogonal to the weight-three word used as the coset shift. -/
theorem bitDot_simplex_logicalWord (u : Fin 3 → ZMod 2) :
    bitDot (steaneHᵀ *ᵥ u) logicalWord = 0 := by
  have hstep : bitDot (steaneHᵀ *ᵥ u) logicalWord = u ⬝ᵥ (steaneH *ᵥ logicalWord) := by
    have h1 := Matrix.dotProduct_mulVec u steaneH logicalWord
    have h2 : u ᵥ* steaneH = steaneHᵀ *ᵥ u := by
      simpa using Matrix.vecMul_transpose (A := steaneHᵀ) u
    rw [bitDot, h1, h2]
  rw [hstep, word_syndrome, dotProduct_zero]

/-- The simplex space is self-orthogonal in the sense needed by the diagonal check action. -/
theorem simplex_self_orthogonal {a : Fin 7 → ZMod 2} (ha : a ∈ simplexSpace) :
    ∀ b ∈ simplexSpace, bitDot a b = 0 := by
  obtain ⟨u, rfl⟩ := ha
  rintro _ ⟨v, rfl⟩
  exact bitDot_simplex

/-- The simplex space is orthogonal to the coset shift. -/
theorem simplex_orthogonal_shift {a : Fin 7 → ZMod 2} (ha : a ∈ simplexSpace) :
    bitDot a logicalWord = 0 := by
  obtain ⟨u, rfl⟩ := ha
  exact bitDot_simplex_logicalWord u

/-- The shift is not a simplex word, so the two cosets are distinct. -/
theorem logicalWord_notMem_simplexSpace : logicalWord ∉ simplexSpace := by
  rintro ⟨u, hu⟩
  exact rows_exclude u hu

/-- The first source codeword: the superposition over the simplex coset at the origin. -/
noncomputable def sourceC0 : (Fin 7 → ZMod 2) → ℂ := cosetState simplexSpace 0

/-- The second source codeword: the superposition over the simplex coset shifted by the weight-three
logical word. -/
noncomputable def sourceC1 : (Fin 7 → ZMod 2) → ℂ := cosetState simplexSpace logicalWord

/-- The first source codeword lies in the seven-qubit CSS codespace. -/
theorem sourceC0_mem_codespace : sourceC0 ∈ cssCodespace steaneData := by
  rw [mem_cssCodespace_iff]
  exact ⟨fun k => cssPauliX_cosetState (steaneRow_mem_simplexSpace k),
    fun k => cssPauliZ_cosetState (fun a ha => simplex_self_orthogonal ha)
      (fun a _ => by simp) (steaneRow_mem_simplexSpace k)⟩

/-- The second source codeword lies in the seven-qubit CSS codespace. -/
theorem sourceC1_mem_codespace : sourceC1 ∈ cssCodespace steaneData := by
  rw [mem_cssCodespace_iff]
  exact ⟨fun k => cssPauliX_cosetState (steaneRow_mem_simplexSpace k),
    fun k => cssPauliZ_cosetState (fun a ha => simplex_self_orthogonal ha)
      (fun a ha => simplex_orthogonal_shift ha) (steaneRow_mem_simplexSpace k)⟩

/-- The value of the first source codeword at the origin. -/
theorem sourceC0_zero : sourceC0 (0 : Fin 7 → ZMod 2) = 1 := by
  have hz : (0 : Fin 7 → ZMod 2) + 0 ∈ simplexSpace := by
    simp
  simp only [sourceC0, cosetState]
  rw [ite_eq_left hz]

/-- The first source codeword vanishes at the coset shift. -/
theorem sourceC0_logicalWord : sourceC0 logicalWord = 0 := by
  have hz : logicalWord + 0 ∉ simplexSpace := by
    simpa using logicalWord_notMem_simplexSpace
  simp only [sourceC0, cosetState]
  rw [ite_eq_right hz]

/-- The second source codeword vanishes at the origin. -/
theorem sourceC1_zero : sourceC1 (0 : Fin 7 → ZMod 2) = 0 := by
  have hz : (0 : Fin 7 → ZMod 2) + logicalWord ∉ simplexSpace := by
    simpa using logicalWord_notMem_simplexSpace
  simp only [sourceC1, cosetState]
  rw [ite_eq_right hz]

/-- The second source codeword is one at the coset shift. -/
theorem sourceC1_logicalWord : sourceC1 logicalWord = 1 := by
  simp only [sourceC1, cosetState]
  rw [binary_add_self logicalWord]
  rw [ite_eq_left (Submodule.zero_mem simplexSpace)]

/-- The two source codewords are linearly independent: they are supported on distinct cosets. -/
theorem sourceC_linearIndependent : LinearIndependent ℂ ![sourceC0, sourceC1] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h0 : s = 0 := by
    have hval := congrFun h (0 : Fin 7 → ZMod 2)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sourceC0_zero, sourceC1_zero, mul_one,
      mul_zero, add_zero] at hval
    exact hval
  have h1 : t = 0 := by
    have hval := congrFun h logicalWord
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sourceC0_logicalWord,
      sourceC1_logicalWord, mul_one, mul_zero, zero_add] at hval
    exact hval
  exact ⟨h0, h1⟩

/-- The span of the two source codewords is contained in the CSS codespace. -/
theorem source_span_le : Submodule.span ℂ ({sourceC0, sourceC1} : Set ((Fin 7 → ZMod 2) → ℂ)) ≤
    cssCodespace steaneData := by
  refine Submodule.span_le.mpr ?_
  intro x hx
  rcases hx with rfl | rfl
  · exact sourceC0_mem_codespace
  · exact sourceC1_mem_codespace

/-- The two source codewords of the fixed source span the seven-qubit CSS codespace. The states
are the coset superpositions of source Eq. (6), written without their normalizing scalars. -/
theorem steane_source_span :
    cssCodespace steaneData =
      Submodule.span ℂ ({sourceC0, sourceC1} : Set ((Fin 7 → ZMod 2) → ℂ)) := by
  refine (Submodule.eq_of_le_of_finrank_eq source_span_le ?_).symm
  rw [cssCodespace_finrank, steaneData_encodedQubits]
  have hspan : Submodule.span ℂ (Set.range ![sourceC0, sourceC1]) =
      Submodule.span ℂ ({sourceC0, sourceC1} : Set ((Fin 7 → ZMod 2) → ℂ)) := by
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [← hspan, finrank_span_eq_card sourceC_linearIndependent, Fintype.card_fin]
  norm_num

end Qatlib.Papers.CssCodeCS96.Construction
