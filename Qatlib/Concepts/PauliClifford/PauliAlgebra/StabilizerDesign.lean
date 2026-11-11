/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesignDefs
import Mathlib.Algebra.Ring.BooleanRing

/-!
# Stabilizer generators, code spaces, and Clifford actions

This module relates masked Pauli products and binary symplectic vectors to stabilizer code
spaces. It proves generator counting, projector trace and dimension formulas, uniqueness up to a
nonzero scalar for a full independent tableau, and correctness properties of Pauli measurement
updates. These constructions follow the stabilizer framework of [Gottesman1997].

The binary action of legal Clifford circuits preserves commutation and is transitive on nonzero
Pauli directions. The module also develops stabilizer-function normalization and rank
identities, uniform weights on the Hermitian nontrivial Pauli sector, explicitly defined second
and third moments, and a tableau simulator driven by a finite fair-bit tape; see
[DehaeneDeMoor2003] and [AaronsonGottesman2004] for background.

## Main statements

* `finrank_codeSpace_eq_pow_sub_rank`: code-space dimension from the reduced generator rank.
* `unique_stabilizerState`: proportionality of normalized code states for a full independent
  tableau.
* `consistent_measuredTableau`: consistency of a measurement update with an anticommuting
  selected row.
* `pauliDirection_orbit_transitive_legal`: transitivity of legal binary Clifford actions on
  nonzero vectors.
* `pauliThirdMoment_eq`: the case formula for the defined third moment.
* `clause3Simulate_rowUpdates`: the simulator's recorded row-update count.

## References

* [Gottesman, 1997][Gottesman1997]
* [Dehaene and De Moor, 2003][DehaeneDeMoor2003]
* [Aaronson and Gottesman, 2004][AaronsonGottesman2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign

open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Concepts.PauliClifford.ExactRank.StabilizerRank
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Matrix

open Qatlib.Concepts.PauliClifford.ExactRank (BooleanVec booleanDot booleanDotHom)

open scoped Classical

/-- A finite Boolean list selecting positions in a generator list. -/
abbrev Mask := List Bool

/-- Computes componentwise exclusive-or of two masks, stopping when either list ends. -/
def maskXor : Mask → Mask → Mask
  | [], _ => []
  | _, [] => []
  | b1 :: m1, b2 :: m2 => xor b1 b2 :: maskXor m1 m2

/-- Multiplies the Pauli generators selected by the mask, in list order and stopping when either
list ends. -/
def maskProduct {n : ℕ} : List (PauliElem n) → Mask → PauliElem n
  | [], _ => 1
  | _ :: _, [] => 1
  | g :: gs, b :: m =>
      if b then PauliElem.mul g (maskProduct gs m) else maskProduct gs m

/-- Multiplies the phase-free words of the generators selected by a mask. -/
def maskWordProduct {n : ℕ} : List (PauliElem n) → Mask → PauliWord n
  | [], _ => 1
  | _ :: _, [] => 1
  | g :: gs, b :: m => if b then g.word * maskWordProduct gs m else maskWordProduct gs m

/-- Every nonempty selection of generators has a nontrivial phase-free word. -/
def IndependentGenerators {n : ℕ} (gs : List (PauliElem n)) : Prop :=
  ∀ m : Mask, m.length = gs.length → (∃ b ∈ m, b = true) →
    maskWordProduct gs m ≠ trivialWord

/-- The set of masked products with one Boolean selection bit per generator. -/
def generatedSubgroup {n : ℕ} (gs : List (PauliElem n)) : Set (PauliElem n) :=
  {p | ∃ m : Mask, m.length = gs.length ∧ maskProduct gs m = p}

/-- The Pauli element with identity word and phase exponent two, representing negative identity. -/
def minusI (n : ℕ) : PauliElem n := ⟨fun _ => .I, 2⟩

/-- The trace of the single-qubit identity Pauli matrix is two. -/
theorem trace_P1_I : Matrix.trace (P1 .I) = 2 := by
  simp [P1, Matrix.trace]

/-- Every nonidentity single-qubit Pauli matrix has trace zero. -/
theorem trace_P1_ne (a : Pauli1) (ha : a ≠ .I) : Matrix.trace (P1 a) = 0 := by
  cases a <;> simp_all [P1, Matrix.trace]

/-- A Pauli operator has trace zero if its word contains a nonidentity letter. -/
theorem trace_op_eq_zero_of_word_ne (n : ℕ) (p : PauliElem n) (h : ∃ i, p.word i ≠ .I) :
    Matrix.trace (op p) = 0 := by
  have hprod : ∏ i : Fin n, Matrix.trace (P1 (p.word i)) = 0 := by
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (trace_P1_ne _ hi)
  have hword : Matrix.trace (pauliWordOp n p.word) = 0 := by
    rw [pauliWordOp_eq, productMatrix_trace]
    exact hprod
  rw [op, Matrix.trace_smul]
  simp [hword]

/-- The trace of an identity-word Pauli element is its scalar phase times `2 ^ n`. -/
theorem trace_op_trivial (n : ℕ) (φ : Phase4) :
    Matrix.trace (op (⟨fun _ => Pauli1.I, φ⟩ : PauliElem n))
      = (Complex.I ^ φ.val : ℂ) * (2 : ℂ) ^ n := by
  have hone : Matrix.trace (1 : Matrix (Reg n) (Reg n) ℂ) = (2 : ℂ) ^ n := by
    rw [Matrix.trace]
    simp
  rw [op_trivial_word, Matrix.trace_smul]
  simp [hone, smul_eq_mul]

/-- The exclusive-or of equal-length masks has the same length. -/
theorem maskXor_length : ∀ (m m' : Mask), m.length = m'.length → (maskXor m m').length = m.length := by
  intro m
  induction m with
  | nil =>
      intro m' h
      cases m' with
      | nil => rfl
      | cons a l => simp at h
  | cons b m ih =>
      intro m' h
      cases m' with
      | nil => simp at h
      | cons b' m' =>
          simp only [maskXor, List.length_cons]
          rw [ih m' (by simpa using! h)]

/-- Equal-length masks are equal if every bit of their exclusive-or is false. -/
theorem maskXor_eq_of_no_true : ∀ (m m' : Mask), m.length = m'.length →
    (∀ b ∈ maskXor m m', b = false) → m = m' := by
  intro m
  induction m with
  | nil =>
      intro m' h hnone
      cases m' with
      | nil => rfl
      | cons a l => simp at h
  | cons b m ih =>
      intro m' h hnone
      cases m' with
      | nil => simp at h
      | cons b' m' =>
          have hhead : xor b b' = false := by
            have hx := hnone (xor b b') (by simp [maskXor])
            simpa only [maskXor] using! hx
          have hbb : b = b' := by
            cases b <;> cases b' <;> simp_all
          subst hbb
          have hnone' : ∀ c ∈ maskXor m m', c = false := by
            intro c hc
            exact hnone c (by simp [maskXor, hc])
          exact congrArg (List.cons b) (ih m' (by simpa using! h) hnone')

/-- For masks matching the generator-list length, exclusive-or corresponds to multiplication of
their selected phase-free words. -/
theorem maskWordProduct_xor {n : ℕ} :
    ∀ (gs : List (PauliElem n)) (m m' : Mask),
      m.length = gs.length → m'.length = gs.length →
      maskWordProduct gs (maskXor m m') = maskWordProduct gs m * maskWordProduct gs m' := by
  intro gs
  induction gs with
  | nil =>
      intro m m' hm hm'
      cases m with
      | nil =>
          cases m' with
          | nil => simp [maskWordProduct]
          | cons b m' => simp at hm'
      | cons b m =>
          cases m' with
          | nil => simp at hm
          | cons b' m' => simp at hm
  | cons g gs ih =>
      intro m m' hm hm'
      cases m with
      | nil => simp at hm
      | cons b m₀ =>
        cases m' with
        | nil => simp at hm'
        | cons b' m₀' =>
          have h0 : m₀.length = gs.length := by simpa using! hm
          have h0' : m₀'.length = gs.length := by simpa using! hm'
          have hih : maskWordProduct gs (maskXor m₀ m₀')
              = maskWordProduct gs m₀ * maskWordProduct gs m₀' :=
            ih m₀ m₀' h0 h0'
          have hsplit : maskXor (b :: m₀) (b' :: m₀') = xor b b' :: maskXor m₀ m₀' := rfl
          rw [hsplit]
          simp only [maskWordProduct]
          cases b with
          | false =>
              cases b' with
              | false =>
                  simp only [Bool.xor_false, Bool.false_eq_true, ↓reduceIte]
                  exact hih
              | true =>
                  simp only [Bool.xor_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
                  rw [hih]
                  ac_rfl
          | true =>
              cases b' with
              | false =>
                  simp only [Bool.xor_false, Bool.false_eq_true, ↓reduceIte]
                  rw [hih]
                  ac_rfl
              | true =>
                  simp only [Bool.xor_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                  rw [hih]
                  calc maskWordProduct gs m₀ * maskWordProduct gs m₀'
                      = (g.word * g.word) * (maskWordProduct gs m₀ * maskWordProduct gs m₀') := by
                        rw [pauliWord_mul_self, one_mul]
                    _ = ((g.word * maskWordProduct gs m₀)
                        * (g.word * maskWordProduct gs m₀')) := by ac_rfl

/-- The word of a masked Pauli product is the corresponding masked word product. -/
theorem maskProduct_word {n : ℕ} :
    ∀ (gs : List (PauliElem n)) (m : Mask),
      (maskProduct gs m).word = maskWordProduct gs m := by
  intro gs
  induction gs with
  | nil =>
      intro m
      funext i
      rfl
  | cons g gs ih =>
      intro m
      cases m with
      | nil =>
          funext i
          rfl
      | cons b m₀ =>
          cases b with
          | false =>
              simp only [maskProduct, maskWordProduct, Bool.false_eq_true, ↓reduceIte]
              rw [ih m₀]
          | true =>
              simp only [maskProduct, maskWordProduct, ↓reduceIte]
              rw [pauliElem_mul_word]
              funext i
              rw [ih m₀]

/-- An all-false mask of the generator-list length selects the identity element. -/
theorem maskProduct_eq_one {n : ℕ} :
    ∀ (gs : List (PauliElem n)) (m : Mask), m.length = gs.length →
      (∀ b ∈ m, b = false) → maskProduct gs m = 1 := by
  intro gs
  induction gs with
  | nil =>
      intro m hm h
      cases m with
      | nil => rfl
      | cons b m => simp at hm
  | cons g gs ih =>
      intro m hm h
      cases m with
      | nil => simp at hm
      | cons b m₀ =>
          have hb : b = false := h b (by simp)
          subst hb
          have h0 : m₀.length = gs.length := by simpa using! hm
          have hnone : ∀ c ∈ m₀, c = false := by
            intro c hc
            exact h c (by simp [hc])
          simp only [maskProduct, Bool.false_eq_true, ↓reduceIte]
          exact ih m₀ h0 hnone

/-- For independent generators, equal masked products with matching mask lengths have equal
masks. -/
theorem maskProduct_injective {n : ℕ} (gs : List (PauliElem n))
    (hind : IndependentGenerators gs) {m m' : Mask}
    (hm : m.length = gs.length) (hm' : m'.length = gs.length)
    (h : maskProduct gs m = maskProduct gs m') : m = m' := by
  have hword : maskWordProduct gs m = maskWordProduct gs m' := by
    rw [← maskProduct_word gs m, ← maskProduct_word gs m']
    exact congrArg PauliElem.word h
  have hxor : maskWordProduct gs (maskXor m m') = trivialWord := by
    rw [maskWordProduct_xor gs m m' hm hm', ← hword, pauliWord_mul_self]
    exact pauliWord_one_eq_trivial
  have hxorlen : (maskXor m m').length = gs.length :=
    (maskXor_length m m' (hm.trans hm'.symm)).trans hm
  have hnone : ∀ b ∈ maskXor m m', b = false := by
    intro b hb
    by_contra hne
    have htrue : b = true := by
      cases b with
      | false => exact absurd hne (by simp)
      | true => rfl
    have hex : ∃ b' ∈ maskXor m m', b' = true := ⟨b, hb, htrue⟩
    have hcontra := hind (maskXor m m') hxorlen hex
    rw [hxor] at hcontra
    exact hcontra rfl
  exact maskXor_eq_of_no_true m m' (hm.trans hm'.symm) hnone

/-- Equality of lists constructed by `List.ofFn` implies equality of their indexing functions. -/
theorem list_ofFn_injective {n : ℕ} {α : Type} {f g : Fin n → α}
    (h : List.ofFn f = List.ofFn g) : f = g := by
  funext i
  have h1 : (List.ofFn f)[i.val]? = (List.ofFn g)[i.val]? := by rw [h]
  rw [List.getElem?_ofFn, List.getElem?_ofFn] at h1
  simp only [dif_pos i.isLt] at h1
  simp only [Option.some.injEq] at h1
  have hi : (⟨i.val, i.isLt⟩ : Fin n) = i := Fin.ext rfl
  rw [hi] at h1
  exact h1

/-- The image of all Boolean masks for `k` independent generators has cardinality `2 ^ k`. -/
theorem card_generatedSubgroup {n k : ℕ} (gs : List (PauliElem n)) (hgs : gs.length = k)
    (hind : IndependentGenerators gs) :
    Finset.card (Finset.image (fun m => maskProduct gs (List.ofFn m))
      (Finset.univ : Finset (Fin k → Bool))) = 2 ^ k := by
  have hinj : Function.Injective (fun m : Fin k → Bool => maskProduct gs (List.ofFn m)) := by
    intro m m' h
    have hm : (List.ofFn m).length = gs.length := by rw [List.length_ofFn]; exact hgs.symm
    have hm' : (List.ofFn m').length = gs.length := by rw [List.length_ofFn]; exact hgs.symm
    exact list_ofFn_injective (maskProduct_injective gs hind hm hm' h)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

/-- The trace of `op p * projectorAux gs` vanishes if no selected generator word cancels the
word of `p`. -/
theorem trace_op_mul_projectorAux_eq_zero {n : ℕ} :
    ∀ (gs : List (PauliElem n)) (p : PauliElem n),
      (∀ m : Mask, m.length = gs.length →
        p.word * maskWordProduct gs m ≠ trivialWord) →
      Matrix.trace (op p * projectorAux gs) = 0 := by
  intro gs
  induction gs with
  | nil =>
      intro p hp
      have hne : p.word ≠ trivialWord := by
        intro hcon
        have h := hp [] (by rfl)
        rw [maskWordProduct, mul_one, hcon] at h
        exact h rfl
      have hex : ∃ i, p.word i ≠ .I := by
        by_contra hc
        refine hne (funext fun j => ?_)
        by_contra hj
        exact hc ⟨j, hj⟩
      have htr : Matrix.trace (op p) = 0 := trace_op_eq_zero_of_word_ne n p hex
      simp only [projectorAux, Matrix.mul_one]
      exact htr
  | cons g gs ih =>
      intro p hp
      have hpFalse : ∀ m : Mask, m.length = gs.length →
          p.word * maskWordProduct gs m ≠ trivialWord := by
        intro m hm
        have h := hp (false :: m) (by simp [hm])
        simpa [maskWordProduct] using! h
      have hpTrue : ∀ m : Mask, m.length = gs.length →
          (PauliElem.mul p g).word * maskWordProduct gs m ≠ trivialWord := by
        intro m hm
        have h := hp (true :: m) (by simp [hm])
        simp only [maskWordProduct, ↓reduceIte] at h
        have hkey : (PauliElem.mul p g).word * maskWordProduct gs m
            = p.word * (g.word * maskWordProduct gs m) := by
          rw [pauliElem_mul_word, mul_assoc]
        rw [← hkey] at h
        exact h
      have h1 : Matrix.trace (op p * projectorAux gs) = 0 := ih p hpFalse
      have h2 : Matrix.trace (op (PauliElem.mul p g) * projectorAux gs) = 0 :=
        ih (PauliElem.mul p g) hpTrue
      have hcalc : op p * projectorAux (g :: gs)
          = ((2 : ℂ)⁻¹) • (op p * projectorAux gs + op (PauliElem.mul p g) * projectorAux gs) := by
        simp only [projectorAux]
        rw [Matrix.mul_smul, Matrix.mul_add, ← Matrix.mul_assoc, ← op_mul]
      rw [hcalc, Matrix.trace_smul, Matrix.trace_add, h1, h2]
      simp

/-- For independent generators, the trace of `projectorAux gs` is `2 ^ n / 2 ^ gs.length`. -/
theorem trace_projectorAux {n : ℕ} :
    ∀ (gs : List (PauliElem n)), IndependentGenerators gs →
      Matrix.trace (projectorAux gs) = (2 : ℂ) ^ n * ((2 : ℂ) ^ gs.length)⁻¹ := by
  intro gs
  induction gs with
  | nil =>
      intro hind
      have htr : Matrix.trace (1 : Matrix (Reg n) (Reg n) ℂ) = (2 : ℂ) ^ n := by
        rw [Matrix.trace]
        simp
      simp only [projectorAux]
      rw [htr]
      simp
  | cons g gs ih =>
      intro hind
      have hind' : IndependentGenerators gs := by
        intro m hm hne
        obtain ⟨b, hb, htrue⟩ := hne
        have h := hind (false :: m) (by simp [hm]) ⟨b, by simp [hb], htrue⟩
        simpa [maskWordProduct] using! h
      have hB : Matrix.trace (op g * projectorAux gs) = 0 := by
        refine trace_op_mul_projectorAux_eq_zero gs g ?_
        intro m hm
        have h := hind (true :: m) (by simp [hm])
        simpa [maskWordProduct] using! h
      have hIH : Matrix.trace (projectorAux gs) = (2 : ℂ) ^ n * ((2 : ℂ) ^ gs.length)⁻¹ :=
        ih hind'
      simp only [projectorAux]
      rw [Matrix.trace_smul, Matrix.trace_add, hIH, hB]
      simp only [smul_eq_mul, add_zero]
      have hpow : (2 : ℂ) ^ (gs.length + 1) = (2 : ℂ) ^ gs.length * 2 := by
        rw [pow_succ]
      simp only [List.length_cons]
      rw [hpow]
      field_simp

/-- For `k ≤ n` independent generators, the trace of `projectorAux gs` is `2 ^ (n - k)`. -/
theorem trace_projectorAux_eq_pow {n k : ℕ} (gs : List (PauliElem n)) (hgs : gs.length = k)
    (hk : k ≤ n) (hind : IndependentGenerators gs) :
    Matrix.trace (projectorAux gs) = (2 : ℂ) ^ (n - k) := by
  have hmain := trace_projectorAux gs hind
  rw [hgs] at hmain
  have hexp : (2 : ℂ) ^ n * ((2 : ℂ) ^ k)⁻¹ = (2 : ℂ) ^ (n - k) :=
    (pow_sub₀ (2 : ℂ) (by norm_num) hk).symm
  rw [hmain, hexp]

/-- The generated set contains negative identity exactly when a mask of the required length
selects negative identity. -/
theorem contains_minusI_iff_exists_mask {n : ℕ} (gs : List (PauliElem n)) :
    ContainsMinusI (generatedSubgroup gs) ↔
      ∃ m : Mask, m.length = gs.length ∧ maskProduct gs m = minusI n := by
  constructor
  · rintro ⟨m, hm, hprod⟩
    exact ⟨m, hm, hprod⟩
  · rintro ⟨m, hm, hprod⟩
    exact ⟨m, hm, hprod⟩

/-- The set generated by independent generators does not contain negative identity. -/
theorem not_contains_minusI_of_independent {n : ℕ} (gs : List (PauliElem n))
    (hind : IndependentGenerators gs) : ¬ ContainsMinusI (generatedSubgroup gs) := by
  rintro ⟨m, hm, hprod⟩
  have hword : maskWordProduct gs m = trivialWord := by
    rw [← maskProduct_word gs m]
    exact congrArg PauliElem.word hprod
  have hnone : ∀ b ∈ m, b = false := by
    intro b hb
    by_contra hne
    have htrue : b = true := by
      cases b with
      | false => exact absurd hne (by simp)
      | true => rfl
    have hcontra := hind m hm ⟨b, hb, htrue⟩
    rw [hword] at hcontra
    exact hcontra rfl
  have hone : maskProduct gs m = 1 := maskProduct_eq_one gs m hm hnone
  rw [hone] at hprod
  have hphase : (1 : PauliElem n).phase = (minusI n).phase := congrArg PauliElem.phase hprod
  have hz : (0 : ZMod 4) = 2 := by simpa [pauliElemOne, minusI] using! hphase
  exact absurd hz (by decide)

/-- Encodes a Pauli word as its pair of binary X and Z coordinate vectors. -/
def symplecticVec {n : ℕ} (w : PauliWord n) : BooleanVec n × BooleanVec n :=
  (symplecticX w, symplecticZ w)

/-- The trivial Pauli word has zero binary symplectic vector. -/
theorem symplecticVec_trivialWord {n : ℕ} : symplecticVec (trivialWord : PauliWord n) = 0 := by
  apply Prod.ext
  · funext i
    simp [symplecticVec, symplecticX, trivialWord]
  · funext i
    simp [symplecticVec, symplecticZ, trivialWord]

/-- The identity Pauli word has zero binary symplectic vector. -/
theorem symplecticVec_one {n : ℕ} : symplecticVec (1 : PauliWord n) = 0 := by
  rw [show (1 : PauliWord n) = trivialWord from rfl]
  exact symplecticVec_trivialWord

/-- Pauli words with equal binary symplectic vectors are equal. -/
theorem symplecticVec_injective {n : ℕ} {w w' : PauliWord n}
    (h : symplecticVec w = symplecticVec w') : w = w' := by
  funext i
  have hx := congrArg (fun v : BooleanVec n × BooleanVec n => v.1 i) h
  have hz := congrArg (fun v : BooleanVec n × BooleanVec n => v.2 i) h
  simp only [symplecticVec] at hx hz
  cases hwi : w i <;> cases hw'i : w' i <;>
    simp [symplecticX, symplecticZ, hwi, hw'i] at hx hz
  all_goals rfl

/-- A Pauli word has zero binary symplectic vector exactly when it is trivial. -/
theorem symplecticVec_eq_zero_iff {n : ℕ} {w : PauliWord n} :
    symplecticVec w = 0 ↔ w = trivialWord := by
  constructor
  · intro h
    have h' : symplecticVec w = symplecticVec (trivialWord : PauliWord n) := by
      rw [symplecticVec_trivialWord]
      exact h
    have h'' := symplecticVec_injective h'
    simpa using! h''
  · intro h
    rw [h]
    exact symplecticVec_trivialWord

/-- The X coordinate of a phase-free single-site Pauli product is the sum of the X coordinates
over `ZMod 2`. -/
theorem symplecticX_letter_mul (a b : Pauli1) :
    (if pauliMul1 a b = .X ∨ pauliMul1 a b = .Y then (1 : ZMod 2) else 0)
      = (if a = .X ∨ a = .Y then (1 : ZMod 2) else 0)
        + (if b = .X ∨ b = .Y then (1 : ZMod 2) else 0) := by
  cases a <;> cases b <;> decide

/-- The Z coordinate of a phase-free single-site Pauli product is the sum of the Z coordinates
over `ZMod 2`. -/
theorem symplecticZ_letter_mul (a b : Pauli1) :
    (if pauliMul1 a b = .Y ∨ pauliMul1 a b = .Z then (1 : ZMod 2) else 0)
      = (if a = .Y ∨ a = .Z then (1 : ZMod 2) else 0)
        + (if b = .Y ∨ b = .Z then (1 : ZMod 2) else 0) := by
  cases a <;> cases b <;> decide

/-- Multiplication of phase-free Pauli words corresponds to addition of their binary symplectic
vectors. -/
theorem symplecticVec_mul {n : ℕ} (w w' : PauliWord n) :
    symplecticVec (w * w') = symplecticVec w + symplecticVec w' := by
  have hmul : (w * w' : PauliWord n) = fun j => pauliMul1 (w j) (w' j) := by
    funext j
    rfl
  rw [hmul]
  simp only [symplecticVec, Prod.mk_add_mk]
  apply Prod.ext
  · funext i
    exact symplecticX_letter_mul (w i) (w' i)
  · funext i
    exact symplecticZ_letter_mul (w i) (w' i)

/-- Sums the binary symplectic vectors of generators selected by a Boolean mask. -/
def maskVecSum {n : ℕ} : List (PauliElem n) → Mask → BooleanVec n × BooleanVec n
  | [], _ => 0
  | _ :: _, [] => 0
  | g :: gs, b :: m =>
      if b then symplecticVec g.word + maskVecSum gs m else maskVecSum gs m

/-- The symplectic vector of a masked word product is the masked sum of generator vectors. -/
theorem symplecticVec_maskWordProduct {n : ℕ} :
    ∀ (gs : List (PauliElem n)) (m : Mask),
      symplecticVec (maskWordProduct gs m) = maskVecSum gs m := by
  intro gs
  induction gs with
  | nil =>
      intro m
      simp only [maskWordProduct, maskVecSum]
      exact symplecticVec_one
  | cons g gs ih =>
      intro m
      cases m with
      | nil =>
          simp only [maskWordProduct, maskVecSum]
          exact symplecticVec_one
      | cons b m₀ =>
          cases b with
          | false =>
              simp only [maskVecSum, maskWordProduct, Bool.false_eq_true, ↓reduceIte]
              rw [ih m₀]
          | true =>
              simp only [maskVecSum, maskWordProduct, ↓reduceIte]
              rw [symplecticVec_mul, ih m₀]

/-- A nonempty mask of the required length has nonzero vector sum for independent generators. -/
theorem maskVecSum_ne_zero_of_independent {n : ℕ} (gs : List (PauliElem n))
    (hind : IndependentGenerators gs) {m : Mask} (hm : m.length = gs.length)
    (hne : ∃ b ∈ m, b = true) : maskVecSum gs m ≠ 0 := by
  intro hz
  have hsym : symplecticVec (maskWordProduct gs m) = 0 := by
    rw [symplecticVec_maskWordProduct]
    exact hz
  have hword := symplecticVec_eq_zero_iff.mp hsym
  exact (hind m hm hne) hword

/-- The binary symplectic vector of the generator at a finite list index. -/
def symplecticVecOfFn {n : ℕ} (gs : List (PauliElem n)) (i : Fin gs.length) :
    BooleanVec n × BooleanVec n :=
  symplecticVec (generatorAt gs i).word

/-- Every element of `ZMod 2` is zero or one. -/
theorem zmod2_eq_zero_or_one (e : ZMod 2) : e = 0 ∨ e = 1 := by
  have hlt : e.val < 2 := ZMod.val_lt e
  interval_cases h : e.val
  · left
    have hz : e = 0 := by
      have hh := ZMod.natCast_zmod_val e
      rw [h, Nat.cast_zero] at hh
      exact hh.symm
    exact hz
  · right
    have hz : e = 1 := by
      have hh := ZMod.natCast_zmod_val e
      rw [h] at hh
      rw [← hh]
      simp
    exact hz

/-- Scalar multiplication over `ZMod 2` returns the vector when the scalar is one and zero
otherwise. -/
theorem zmod2_smul_eq {n : ℕ} (c0 : ZMod 2) (v : BooleanVec n × BooleanVec n) :
    c0 • v = if c0 = 1 then v else 0 := by
  rcases zmod2_eq_zero_or_one c0 with h0 | h1
  · subst h0
    simp
  · subst h1
    simp

/-- Adding an element of `ZMod 2` to itself gives zero. -/
theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_eq_zero_or_one x with h0 | h1
  · subst h0
    simp
  · subst h1
    decide

/-- The binary dot product is additive in its left argument. -/
theorem booleanDot_add_left {n : ℕ} (a b x : BooleanVec n) :
    booleanDot (a + b) x = booleanDot a x + booleanDot b x := by
  simp only [booleanDot]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Pi.add_apply, add_mul]

/-- The binary dot product is symmetric. -/
theorem booleanDot_comm {n : ℕ} (a x : BooleanVec n) : booleanDot a x = booleanDot x a := by
  simp only [booleanDot]
  exact Finset.sum_congr rfl fun i _ => mul_comm (a i) (x i)

/-- The binary symplectic form is additive in its left argument. -/
theorem symplecticForm_add_left {n : ℕ} (v₁ v₂ w : BooleanVec n × BooleanVec n) :
    symplecticForm (v₁ + v₂) w = symplecticForm v₁ w + symplecticForm v₂ w := by
  simp only [symplecticForm, Prod.fst_add, Prod.snd_add]
  have h1 : booleanDot (v₁.1 + v₂.1) w.2 = booleanDot v₁.1 w.2 + booleanDot v₂.1 w.2 :=
    booleanDot_add_left v₁.1 v₂.1 w.2
  have h2 : booleanDot (v₁.2 + v₂.2) w.1 = booleanDot v₁.2 w.1 + booleanDot v₂.2 w.1 :=
    booleanDot_add_left v₁.2 v₂.2 w.1
  rw [h1, h2]
  abel

/-- The binary symplectic form is additive in its right argument. -/
theorem symplecticForm_add_right {n : ℕ} (v w₁ w₂ : BooleanVec n × BooleanVec n) :
    symplecticForm v (w₁ + w₂) = symplecticForm v w₁ + symplecticForm v w₂ := by
  simp only [symplecticForm, Prod.fst_add, Prod.snd_add]
  have h1 : booleanDot v.1 (w₁.2 + w₂.2) = booleanDot v.1 w₁.2 + booleanDot v.1 w₂.2 :=
    map_add (booleanDotHom v.1) w₁.2 w₂.2
  have h2 : booleanDot v.2 (w₁.1 + w₂.1) = booleanDot v.2 w₁.1 + booleanDot v.2 w₂.1 :=
    map_add (booleanDotHom v.2) w₁.1 w₂.1
  rw [h1, h2]
  abel

/-- The binary symplectic form vanishes on equal arguments. -/
theorem symplecticForm_self {n : ℕ} (v : BooleanVec n × BooleanVec n) :
    symplecticForm v v = 0 := by
  simp only [symplecticForm]
  rw [booleanDot_comm v.1 v.2]
  exact zmod2_add_self _

/-- Two Pauli operators commute exactly when their binary symplectic pairing is zero. -/
theorem op_commute_iff_symplecticVec_form_zero {n : ℕ} (p q : PauliElem n) :
    op p * op q = op q * op p
      ↔ symplecticForm (symplecticVec p.word) (symplecticVec q.word) = 0 := by
  rw [op_commute_iff]
  rfl

/-- For independent generators, equal masked word products with masks of the required length
have equal masks. -/
theorem maskWordProduct_injective {n : ℕ} (gs : List (PauliElem n))
    (hind : IndependentGenerators gs) {m m' : Mask}
    (hm : m.length = gs.length) (hm' : m'.length = gs.length)
    (h : maskWordProduct gs m = maskWordProduct gs m') : m = m' := by
  have hxor : maskWordProduct gs (maskXor m m') = trivialWord := by
    rw [maskWordProduct_xor gs m m' hm hm', h, pauliWord_mul_self]
    exact pauliWord_one_eq_trivial
  have hxorlen : (maskXor m m').length = gs.length :=
    (maskXor_length m m' (hm.trans hm'.symm)).trans hm
  have hnone : ∀ b ∈ maskXor m m', b = false := by
    intro b hb
    by_contra hne
    have htrue : b = true := by
      cases b with
      | false => exact absurd hne (by simp)
      | true => rfl
    have hex : ∃ b' ∈ maskXor m m', b' = true := ⟨b, hb, htrue⟩
    have hcontra := hind (maskXor m m') hxorlen hex
    rw [hxor] at hcontra
    exact hcontra rfl
  exact maskXor_eq_of_no_true m m' (hm.trans hm'.symm) hnone

/-- A masked generator-vector sum equals the linear combination whose binary coefficients
determine the mask. -/
theorem maskVecSum_eq_sum {n : ℕ} :
    ∀ (gs : List (PauliElem n)) (c : Fin gs.length → ZMod 2),
      maskVecSum gs (List.ofFn (fun i => decide (c i = 1)))
        = ∑ i : Fin gs.length, c i • symplecticVecOfFn gs i := by
  intro gs
  induction gs with
  | nil =>
      intro c
      simp [maskVecSum]
  | cons g gs ih =>
      intro c
      have hmask : List.ofFn (fun i => decide (c i = 1))
          = decide (c 0 = 1) :: List.ofFn (fun i : Fin gs.length => decide (c i.succ = 1)) := by
        exact List.ofFn_succ
      have h0 : symplecticVecOfFn (g :: gs) 0 = symplecticVec g.word := by
        simp [symplecticVecOfFn, generatorAt]
      have hsucc (i : Fin gs.length) :
          symplecticVecOfFn (g :: gs) i.succ = symplecticVecOfFn gs i := by
        simp [symplecticVecOfFn, generatorAt]
      have hIH : maskVecSum gs (List.ofFn (fun i : Fin gs.length => decide (c i.succ = 1)))
          = ∑ i : Fin gs.length, c i.succ • symplecticVecOfFn gs i :=
        ih (fun i => c i.succ)
      have hsum := Fin.sum_univ_succ (fun i => c i • symplecticVecOfFn (g :: gs) i)
      have hsmul : c 0 • symplecticVec g.word
          = (if decide (c 0 = 1) then symplecticVec g.word else 0) := by
        by_cases hb : decide (c 0 = 1) = true
        · have hz : c 0 = 1 := of_decide_eq_true hb
          simp [hz]
        · have hz : c 0 ≠ 1 := fun h => hb (decide_eq_true_eq.mpr h)
          have hz0 : c 0 = 0 := (zmod2_eq_zero_or_one (c 0)).resolve_right hz
          simp [hz0]
      calc
        maskVecSum (g :: gs) (List.ofFn (fun i => decide (c i = 1)))
            = (if decide (c 0 = 1) then symplecticVec g.word else 0)
                + maskVecSum gs (List.ofFn (fun i : Fin gs.length => decide (c i.succ = 1))) := by
              rw [hmask, maskVecSum]
              by_cases hb : decide (c 0 = 1) = true
              · have hz : c 0 = 1 := of_decide_eq_true hb
                simp [hz]
              · have hz : c 0 ≠ 1 := fun h => hb (decide_eq_true_eq.mpr h)
                have hz0 : c 0 = 0 := (zmod2_eq_zero_or_one (c 0)).resolve_right hz
                simp [hz0]
        _ = c 0 • symplecticVec g.word
                + ∑ i : Fin gs.length, c i.succ • symplecticVecOfFn gs i := by
              rw [hsmul, hIH]
        _ = c 0 • symplecticVecOfFn (g :: gs) 0
                + ∑ i : Fin gs.length, c i.succ • symplecticVecOfFn (g :: gs) i.succ := by
              have hS : (∑ i : Fin gs.length, c i.succ • symplecticVecOfFn gs i)
                  = ∑ i : Fin gs.length, c i.succ • symplecticVecOfFn (g :: gs) i.succ :=
                Finset.sum_congr rfl fun i _ => congrArg (fun v => c i.succ • v) (hsucc i)
              rw [hS, h0]
        _ = ∑ i : Fin (g :: gs).length, c i • symplecticVecOfFn (g :: gs) i := hsum.symm

/-- Independent Pauli generators have linearly independent binary symplectic vectors over `ZMod
2`. -/
theorem symplecticVecOfFn_linearIndependent {n : ℕ} (gs : List (PauliElem n))
    (hind : IndependentGenerators gs) :
    LinearIndependent (ZMod 2) (symplecticVecOfFn gs) := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  intro c c' h
  have hsum : maskVecSum gs (List.ofFn (fun i => decide (c i = 1)))
      = maskVecSum gs (List.ofFn (fun i => decide (c' i = 1))) := by
    rw [maskVecSum_eq_sum gs c, maskVecSum_eq_sum gs c']
    exact h
  have hsym : symplecticVec (maskWordProduct gs (List.ofFn (fun i => decide (c i = 1))))
      = symplecticVec (maskWordProduct gs (List.ofFn (fun i => decide (c' i = 1)))) := by
    rw [symplecticVec_maskWordProduct, symplecticVec_maskWordProduct]
    exact hsum
  have hword : maskWordProduct gs (List.ofFn (fun i => decide (c i = 1)))
      = maskWordProduct gs (List.ofFn (fun i => decide (c' i = 1))) :=
    symplecticVec_injective hsym
  have hmask : List.ofFn (fun i => decide (c i = 1))
      = List.ofFn (fun i => decide (c' i = 1)) :=
    maskWordProduct_injective gs hind (by simp) (by simp) hword
  have hfun : (fun i => decide (c i = 1)) = (fun i => decide (c' i = 1)) :=
    list_ofFn_injective hmask
  funext i
  have hdec : decide (c i = 1) = decide (c' i = 1) := congrFun hfun i
  by_cases hb : c i = 1
  · have hb' : c' i = 1 := of_decide_eq_true (by rw [← hdec]; simp [hb])
    exact hb.trans hb'.symm
  · have hb0 : c i = 0 := (zmod2_eq_zero_or_one (c i)).resolve_right hb
    have hb0' : c' i = 0 := by
      have hne : c' i ≠ 1 := by
        intro h1
        have h1' : decide (c' i = 1) = true := decide_eq_true_eq.mpr h1
        rw [← hdec] at h1'
        simp [hb] at h1'
      exact (zmod2_eq_zero_or_one (c' i)).resolve_right hne
    exact hb0.trans hb0'.symm

/-- The binary symplectic images of all masked products of independent generators have
cardinality `2 ^ gs.length`. -/
theorem card_symplecticImage {n : ℕ} (gs : List (PauliElem n))
    (hind : IndependentGenerators gs) :
    ((Finset.univ : Finset (Fin gs.length → Bool)).image
        (fun m : Fin gs.length → Bool => symplecticVec (maskProduct gs (List.ofFn m)).word)).card
      = 2 ^ gs.length := by
  have hinj : Function.Injective
      (fun m : Fin gs.length → Bool => symplecticVec (maskProduct gs (List.ofFn m)).word) := by
    intro m m' h
    have hword : (maskProduct gs (List.ofFn m)).word
        = (maskProduct gs (List.ofFn m')).word := symplecticVec_injective h
    have hwp : maskWordProduct gs (List.ofFn m) = maskWordProduct gs (List.ofFn m') := by
      rw [maskProduct_word gs _, maskProduct_word gs _] at hword
      exact hword
    have hmask : List.ofFn m = List.ofFn m' :=
      maskWordProduct_injective gs hind (by simp) (by simp) hwp
    exact list_ofFn_injective hmask
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

/-- The squared complex norm of a real scalar equals its real square. -/
theorem norm_sq_ofReal (r : ℝ) : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
  have h : Complex.normSq (r : ℂ) = r ^ 2 := by
    show Complex.normSq (Complex.mk r 0) = r ^ 2
    rw [Complex.normSq_mk]
    ring
  rw [← Complex.normSq_eq_norm_sq]
  exact h

/-- The complex number `Complex.I` has norm one. -/
theorem norm_I : ‖(Complex.I : ℂ)‖ = 1 := by
  have h := Complex.normSq_eq_norm_sq (Complex.I)
  rw [Complex.normSq_I] at h
  nlinarith [norm_nonneg (Complex.I)]

/-- The complex number negative one has norm one. -/
theorem norm_neg_one : ‖(-1 : ℂ)‖ = 1 := by
  have h := Complex.normSq_eq_norm_sq (-1 : ℂ)
  rw [Complex.normSq_neg, Complex.normSq_one] at h
  nlinarith [norm_nonneg (-1 : ℂ)]

/-- The displayed affine-support phase function vanishes at `x` exactly when `x` lies outside
its affine support. -/
theorem isStabilizerFun_zero_iff {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n) (c : ZMod 2)
    (A : AffineSubspace (ZMod 2) (BooleanVec n)) (x : BooleanVec n) :
    (Complex.I ^ (booleanDot a x).val * (-1 : ℂ) ^ (quadFun Q b c x).val *
      (if x ∈ A then (1 : ℂ) else 0)) = 0 ↔ x ∉ A := by
  constructor
  · intro h hx
    have h1 : Complex.I ^ (booleanDot a x).val ≠ 0 := pow_ne_zero _ (by simp)
    have h2 : (-1 : ℂ) ^ (quadFun Q b c x).val ≠ 0 := pow_ne_zero _ (by simp)
    rw [if_pos hx] at h
    exact (mul_ne_zero (mul_ne_zero h1 h2) one_ne_zero) h
  · intro h
    rw [if_neg h]
    simp

/-- The squared norm of the displayed affine-support phase function is the indicator of its
affine support. -/
theorem isStabilizerFun_norm_sq {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n) (c : ZMod 2)
    (A : AffineSubspace (ZMod 2) (BooleanVec n)) (x : BooleanVec n) :
    ‖Complex.I ^ (booleanDot a x).val * (-1 : ℂ) ^ (quadFun Q b c x).val *
      (if x ∈ A then (1 : ℂ) else 0)‖ ^ 2 = if x ∈ A then (1 : ℝ) else 0 := by
  by_cases hx : x ∈ A
  · rw [if_pos hx, if_pos hx]
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_one, norm_I, norm_neg_one]
    simp
  · rw [if_neg hx, if_neg hx]
    simp

/-- The mass of the displayed stabilizer function equals the cardinality of its affine support. -/
theorem isStabilizerFun_mass_eq_card {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n) (c : ZMod 2)
    (A : AffineSubspace (ZMod 2) (BooleanVec n))
    (φ : BooleanVec n → ℂ)
    (hφ : φ = fun x => Complex.I ^ (booleanDot a x).val * (-1 : ℂ) ^ (quadFun Q b c x).val *
      (if x ∈ A then (1 : ℂ) else 0)) :
    stabilizerFunMass φ = ((↑A : Set (BooleanVec n)).toFinset.card : ℝ) := by
  rw [hφ, stabilizerFunMass]
  have hpoint : ∀ x : BooleanVec n,
      ‖Complex.I ^ (booleanDot a x).val * (-1 : ℂ) ^ (quadFun Q b c x).val *
        (if x ∈ A then (1 : ℂ) else 0)‖ ^ 2 = (if x ∈ A then (1 : ℝ) else 0) :=
    fun x => isStabilizerFun_norm_sq a Q b c A x
  rw [Finset.sum_congr rfl fun x _ => hpoint x]
  have hsum : ∑ x : BooleanVec n, (if x ∈ A then (1 : ℕ) else 0)
      = ((Finset.univ : Finset (BooleanVec n)).filter (fun x => x ∈ A)).card := by
    have h := Finset.card_filter (fun x => x ∈ A) (Finset.univ : Finset (BooleanVec n))
    exact h.symm
  have hcard : ((Finset.univ : Finset (BooleanVec n)).filter
      (fun x => x ∈ A)).card = (↑A : Set (BooleanVec n)).toFinset.card := by
    congr 1
    ext x
    simp [Set.mem_toFinset]
  calc
    ∑ x : BooleanVec n, (if x ∈ A then (1 : ℝ) else 0)
        = (((Finset.univ : Finset (BooleanVec n)).filter (fun x => x ∈ A)).card : ℝ) := by
          exact_mod_cast hsum
    _ = ((↑A : Set (BooleanVec n)).toFinset.card : ℝ) := by
          exact_mod_cast hcard

/-- The register-state encoding `stateOfFn` preserves the sum of squared amplitude norms. -/
theorem sum_normSq_stateOfFn {n : ℕ} (f : BooleanVec n → ℂ) :
    ∑ r : Reg n, ‖stateOfFn f r‖ ^ 2 = ∑ x : BooleanVec n, ‖f x‖ ^ 2 := by
  have h := Fintype.sum_bijective (regVecEquiv : Reg n ≃ BooleanVec n)
    regVecEquiv.bijective (fun r : Reg n => ‖stateOfFn f r‖ ^ 2)
    (fun x : BooleanVec n => ‖f x‖ ^ 2) (fun r => rfl)
  exact h

/-- A function of positive mass yields a normalized state under `normalizedStabilizerState`. -/
theorem normalizedStabilizerState_normalized {n : ℕ} (φ : BooleanVec n → ℂ)
    (hmass : 0 < stabilizerFunMass φ) : Normalized (normalizedStabilizerState φ) := by
  unfold Normalized normalizedStabilizerState
  rw [sum_normSq_stateOfFn]
  have hsq : ‖(Real.sqrt (stabilizerFunMass φ) : ℂ)‖ ^ 2 = stabilizerFunMass φ := by
    rw [norm_sq_ofReal, Real.sq_sqrt (le_of_lt hmass)]
  have hinv : ‖(Real.sqrt (stabilizerFunMass φ) : ℂ)⁻¹‖ ^ 2 = (stabilizerFunMass φ)⁻¹ := by
    rw [norm_inv, inv_pow, hsq]
  calc
    ∑ x : BooleanVec n, ‖φ x * (Real.sqrt (stabilizerFunMass φ) : ℂ)⁻¹‖ ^ 2
        = ∑ x : BooleanVec n,
            (‖φ x‖ ^ 2 * ‖(Real.sqrt (stabilizerFunMass φ) : ℂ)⁻¹‖ ^ 2) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [norm_mul]
          ring
    _ = stabilizerFunMass φ * ‖(Real.sqrt (stabilizerFunMass φ) : ℂ)⁻¹‖ ^ 2 := by
          unfold stabilizerFunMass
          rw [Finset.sum_mul]
    _ = 1 := by
          rw [hinv, mul_inv_cancel₀ (ne_of_gt hmass)]

/-- For nonzero mass, a normalized stabilizer-state amplitude vanishes exactly when the original
function vanishes at the corresponding binary vector. -/
theorem normalizedStabilizerState_zero_iff {n : ℕ} (φ : BooleanVec n → ℂ)
    (hmass : stabilizerFunMass φ ≠ 0) (r : Reg n) :
    normalizedStabilizerState φ r = 0 ↔ φ (regToVec r) = 0 := by
  rw [normalizedStabilizerState, stateOfFn]
  have hc : (Real.sqrt (stabilizerFunMass φ) : ℂ)⁻¹ ≠ 0 := by
    intro h
    have hz : (Real.sqrt (stabilizerFunMass φ) : ℂ) = 0 := inv_eq_zero.mp h
    have hr : Real.sqrt (stabilizerFunMass φ) = 0 := by
      have hre := congrArg Complex.re hz
      simpa using! hre
    have hz' : stabilizerFunMass φ = 0 := by
      have hpos : 0 ≤ stabilizerFunMass φ := by
        unfold stabilizerFunMass
        positivity
      rw [← Real.sq_sqrt hpos, hr]
      norm_num
    exact hmass hz'
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_right hc
  · intro h
    simp [h]

/-- Multiplying a function of nonzero mass by a nonzero complex scalar multiplies its normalized
state by the scalar divided by its norm. -/
theorem normalizedStabilizerState_smul {n : ℕ} (φ : BooleanVec n → ℂ) (lam : ℂ) (hlam : lam ≠ 0)
    (hmass : stabilizerFunMass φ ≠ 0) (r : Reg n) :
    normalizedStabilizerState (fun x => lam * φ x) r
      = (lam * ((‖lam‖ : ℝ) : ℂ)⁻¹) * normalizedStabilizerState φ r := by
  have hmasspos : 0 ≤ stabilizerFunMass φ := by
    unfold stabilizerFunMass
    positivity
  have hsqrtne : Real.sqrt (stabilizerFunMass φ) ≠ 0 := by
    intro h
    exact hmass ((Real.sqrt_eq_zero hmasspos).mp h)
  have hmass2 : stabilizerFunMass (fun x => lam * φ x)
      = ‖lam‖ ^ 2 * stabilizerFunMass φ := by
    unfold stabilizerFunMass
    calc
      ∑ x : BooleanVec n, ‖lam * φ x‖ ^ 2
          = ∑ x : BooleanVec n, (‖φ x‖ ^ 2 * ‖lam‖ ^ 2) := by
            exact Finset.sum_congr rfl fun x _ => by
              rw [norm_mul]
              ring
      _ = ‖lam‖ ^ 2 * ∑ x : BooleanVec n, ‖φ x‖ ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => by ring
      _ = ‖lam‖ ^ 2 * stabilizerFunMass φ := rfl
  have hsqrt : Real.sqrt (stabilizerFunMass (fun x => lam * φ x))
      = ‖lam‖ * Real.sqrt (stabilizerFunMass φ) := by
    rw [hmass2, Real.sqrt_mul (by positivity) (stabilizerFunMass φ),
      Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg lam)]
  have hne : ‖lam‖ ≠ 0 := by
    intro h
    apply hlam
    exact norm_eq_zero.mp h
  have hneC : ((‖lam‖ : ℝ) : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    apply hlam
    simpa using! hre
  have hsqrtc : (Real.sqrt (stabilizerFunMass φ) : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have hz : Real.sqrt (stabilizerFunMass φ) = 0 := by
      simpa using! hre
    exact hmass ((Real.sqrt_eq_zero hmasspos).mp hz)
  unfold normalizedStabilizerState stateOfFn
  rw [hsqrt, Complex.ofReal_mul]
  field_simp [hneC, hsqrtc]

/-- Powers of `Complex.I` with natural exponents less than four are equal only when their
exponents are equal. -/
theorem complex_I_pow_inj {a b : ℕ} (ha : a < 4) (hb : b < 4)
    (h : (Complex.I ^ a : ℂ) = Complex.I ^ b) : a = b := by
  interval_cases a <;> interval_cases b <;>
    (try rfl) <;>
    (exfalso; norm_num [Complex.ext_iff] at h)

/-- The matrix representing a phase-free Pauli word is nonzero. -/
theorem pauliWordOp_ne_zero {n : ℕ} (w : PauliWord n) : pauliWordOp n w ≠ 0 := by
  intro h
  have hu := pauliWordOp_unitary n w
  have h1 := Matrix.mem_unitaryGroup_iff'.mp hu
  rw [h] at h1
  simp at h1

/-- Pauli elements with equal words and equal operator matrices have equal phase exponents. -/
theorem op_eq_of_same_word {n : ℕ} {x y : PauliElem n}
    (h : op x = op y) (hw : x.word = y.word) : x.phase = y.phase := by
  have hne : pauliWordOp n x.word ≠ 0 := pauliWordOp_ne_zero x.word
  have hmat : ∀ i j, (Complex.I ^ x.phase.val : ℂ) * pauliWordOp n x.word i j
      = (Complex.I ^ y.phase.val : ℂ) * pauliWordOp n x.word i j := by
    intro i j
    have hc := congrArg (fun M : Matrix (Reg n) (Reg n) ℂ => M i j) h
    simp only [op, Matrix.smul_apply] at hc
    rw [← hw] at hc
    exact hc
  obtain ⟨i, j, hij⟩ : ∃ i j, pauliWordOp n x.word i j ≠ 0 := by
    by_contra hc
    have hcon : ∀ i j, pauliWordOp n x.word i j = 0 := by
      intro i j
      by_contra h2
      exact hc ⟨i, j, h2⟩
    refine hne (Matrix.ext fun i j => ?_)
    exact hcon i j
  have hmul : (Complex.I ^ x.phase.val : ℂ) = Complex.I ^ y.phase.val := by
    calc (Complex.I ^ x.phase.val : ℂ)
        = (Complex.I ^ x.phase.val : ℂ) * pauliWordOp n x.word i j
            * (pauliWordOp n x.word i j)⁻¹ := by field_simp
      _ = ((Complex.I ^ y.phase.val : ℂ) * pauliWordOp n x.word i j)
            * (pauliWordOp n x.word i j)⁻¹ := by rw [hmat i j]
      _ = Complex.I ^ y.phase.val := by field_simp
  have hsame : x.phase.val = y.phase.val :=
    complex_I_pow_inj (ZMod.val_lt x.phase) (ZMod.val_lt y.phase) hmul
  calc x.phase = (x.phase.val : ZMod 4) := (ZMod.natCast_zmod_val x.phase).symm
    _ = (y.phase.val : ZMod 4) := by rw [hsame]
    _ = y.phase := ZMod.natCast_zmod_val y.phase

/-- Commuting Pauli operator matrices imply commutativity of their Pauli-element products. -/
theorem pauliElem_mul_comm_of_op_commute {n : ℕ} {p q : PauliElem n}
    (h : op p * op q = op q * op p) : PauliElem.mul p q = PauliElem.mul q p := by
  apply pauli_ext
  · funext i
    exact pauliMul1_comm _ _
  · have hw : (PauliElem.mul p q).word = (PauliElem.mul q p).word := by
      funext i
      exact pauliMul1_comm _ _
    have hop : op (PauliElem.mul p q) = op (PauliElem.mul q p) := by
      rw [op_mul, h, op_mul]
    exact op_eq_of_same_word hop hw

/-- A zero binary symplectic pairing implies commutativity of the Pauli-element products. -/
theorem pauliElem_mul_comm_of_form_zero {n : ℕ} {p q : PauliElem n}
    (h : symplecticForm (symplecticVec p.word) (symplecticVec q.word) = 0) :
    PauliElem.mul p q = PauliElem.mul q p := by
  refine pauliElem_mul_comm_of_op_commute ?_
  exact (op_commute_iff p q).mpr h

/-- Enumerates all Boolean masks of a prescribed length. -/
def masksOfLen : ℕ → List Mask
  | 0 => [[]]
  | k + 1 => (masksOfLen k).map (fun m => false :: m) ++ (masksOfLen k).map (fun m => true :: m)

/-- Every mask in `masksOfLen k` has length `k`. -/
theorem masksOfLen_length : ∀ k (m : Mask), m ∈ masksOfLen k → m.length = k := by
  intro k
  induction k with
  | zero =>
      intro m hm
      simp only [masksOfLen, List.mem_singleton] at hm
      cases hm
      rfl
  | succ k ih =>
      intro m hm
      simp only [masksOfLen, List.mem_append, List.mem_map] at hm
      rcases hm with ⟨m0, hm0, rfl⟩ | ⟨m0, hm0, rfl⟩
      · simp [ih m0 hm0]
      · simp [ih m0 hm0]

/-- Every Boolean mask of length `k` belongs to `masksOfLen k`. -/
theorem mem_masksOfLen : ∀ (k : ℕ) (m : Mask), m.length = k → m ∈ masksOfLen k := by
  intro k
  induction k with
  | zero =>
      intro m hm
      cases m with
      | nil => simp [masksOfLen]
      | cons b m => simp at hm
  | succ k ih =>
      intro m hm
      cases m with
      | nil => simp at hm
      | cons b m =>
        have hlen : m.length = k := by simpa using! hm
        have hmem : m ∈ masksOfLen k := ih m hlen
        cases b with
        | false =>
            simp only [masksOfLen, List.mem_append, List.mem_map]
            exact Or.inl ⟨m, hmem, rfl⟩
        | true =>
            simp only [masksOfLen, List.mem_append, List.mem_map]
            exact Or.inr ⟨m, hmem, rfl⟩

/-- Right multiplication by the identity leaves a Pauli element unchanged. -/
theorem pauliElem_mul_one {n : ℕ} (p : PauliElem n) : PauliElem.mul p 1 = p := by
  apply pauli_ext
  · exact mul_one p.word
  · show p.phase + 0 + ∑ i, pauliMulPhase (p.word i) Pauli1.I = p.phase
    rw [add_zero]
    have hz : (∑ i, pauliMulPhase (p.word i) Pauli1.I) = 0 := by
      simp [pauliMulPhase_right_I]
    rw [hz, add_zero]

/-- Left multiplication by the identity leaves a Pauli element unchanged. -/
theorem pauliElem_one_mul {n : ℕ} (p : PauliElem n) : PauliElem.mul 1 p = p := by
  apply pauli_ext
  · exact one_mul p.word
  · show 0 + p.phase + ∑ i, pauliMulPhase Pauli1.I (p.word i) = p.phase
    rw [zero_add]
    have hz : (∑ i, pauliMulPhase Pauli1.I (p.word i)) = 0 := by
      simp [pauliMulPhase_I]
    rw [hz, add_zero]

/-- A Pauli element commuting with each of two elements also commutes with their product. -/
theorem pauliElem_mul_comm_of_comm {n : ℕ} (g a b : PauliElem n)
    (hga : PauliElem.mul g a = PauliElem.mul a g)
    (hgb : PauliElem.mul g b = PauliElem.mul b g) :
    PauliElem.mul g (PauliElem.mul a b) = PauliElem.mul (PauliElem.mul a b) g := by
  have h1 : PauliElem.mul g (PauliElem.mul a b)
      = PauliElem.mul (PauliElem.mul g a) b := (pauliElem_mul_assoc' g a b).symm
  have h2 : PauliElem.mul (PauliElem.mul g a) b
      = PauliElem.mul (PauliElem.mul a g) b := by rw [hga]
  have h3 : PauliElem.mul (PauliElem.mul a g) b
      = PauliElem.mul a (PauliElem.mul g b) := pauliElem_mul_assoc' a g b
  have h4 : PauliElem.mul a (PauliElem.mul g b)
      = PauliElem.mul a (PauliElem.mul b g) := by rw [hgb]
  have h5 : PauliElem.mul a (PauliElem.mul b g)
      = PauliElem.mul (PauliElem.mul a b) g := (pauliElem_mul_assoc' a b g).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

/-- A Pauli element commuting with every generator commutes with every masked product. -/
theorem maskProduct_comm {n : ℕ} : ∀ (gs : List (PauliElem n)) (m : Mask) (g : PauliElem n),
    (∀ h ∈ gs, PauliElem.mul g h = PauliElem.mul h g) →
    PauliElem.mul g (maskProduct gs m) = PauliElem.mul (maskProduct gs m) g := by
  intro gs
  induction gs with
  | nil =>
      intro m g hg
      simp only [maskProduct]
      rw [pauliElem_mul_one, pauliElem_one_mul]
  | cons h gs ih =>
      intro m g hg
      cases m with
      | nil =>
          simp only [maskProduct]
          rw [pauliElem_mul_one, pauliElem_one_mul]
      | cons b m₀ =>
          cases b with
          | false =>
              simp only [maskProduct, Bool.false_eq_true, ↓reduceIte]
              exact ih m₀ g (fun x hx => hg x (List.mem_cons_of_mem h hx))
          | true =>
              simp only [maskProduct, ↓reduceIte]
              have hgh : PauliElem.mul g h = PauliElem.mul h g := hg h (List.mem_cons_self)
              have hcomm := ih m₀ g (fun x hx => hg x (List.mem_cons_of_mem h hx))
              calc PauliElem.mul g (PauliElem.mul h (maskProduct gs m₀))
                  = PauliElem.mul (PauliElem.mul g h) (maskProduct gs m₀) :=
                    (pauliElem_mul_assoc' _ _ _).symm
                _ = PauliElem.mul (PauliElem.mul h g) (maskProduct gs m₀) := by rw [hgh]
                _ = PauliElem.mul h (PauliElem.mul g (maskProduct gs m₀)) :=
                    (pauliElem_mul_assoc' _ _ _)
                _ = PauliElem.mul h (PauliElem.mul (maskProduct gs m₀) g) := by rw [hcomm]
                _ = PauliElem.mul (PauliElem.mul h (maskProduct gs m₀)) g :=
                    (pauliElem_mul_assoc' _ _ _).symm

/-- For commuting Hermitian generators and masks of the required length, exclusive-or
corresponds to multiplication of masked Pauli products. -/
theorem maskProduct_xor {n : ℕ} : ∀ (gs : List (PauliElem n)) (_hcomm : CommutingHermitianPaulis gs)
    (m m' : Mask), m.length = gs.length → m'.length = gs.length →
    maskProduct gs (maskXor m m') = maskProduct gs m * maskProduct gs m' := by
  intro gs
  induction gs with
  | nil =>
      intro hcomm m m' hm hm'
      cases hcomm
      cases m with
      | nil =>
          cases m' with
          | nil =>
              simp only [maskProduct]
              exact (pauliElem_mul_one 1).symm
          | cons b m' => simp at hm'
      | cons b m =>
          cases m' with
          | nil => simp at hm
          | cons b' m' => simp at hm
  | cons g gs ih =>
      intro hcomm m m' hm hm'
      have hgs' : CommutingHermitianPaulis gs := by
        refine ⟨fun h hh => hcomm.1 h (List.mem_cons_of_mem g hh), ?_⟩
        intro h hh k hk
        exact hcomm.2 h (List.mem_cons_of_mem g hh) k (List.mem_cons_of_mem g hk)
      cases m with
      | nil => simp at hm
      | cons b m₀ =>
        cases m' with
        | nil => simp at hm'
        | cons b' m₀' =>
          have h0 : m₀.length = gs.length := by simpa using! hm
          have h0' : m₀'.length = gs.length := by simpa using! hm'
          have hih : maskProduct gs (maskXor m₀ m₀')
              = maskProduct gs m₀ * maskProduct gs m₀' :=
            ih hgs' m₀ m₀' h0 h0'
          have hsplit : maskXor (b :: m₀) (b' :: m₀') = xor b b' :: maskXor m₀ m₀' := rfl
          have hcommA : PauliElem.mul g (maskProduct gs m₀)
              = PauliElem.mul (maskProduct gs m₀) g :=
            maskProduct_comm gs m₀ g (fun x hx =>
              pauliElem_mul_comm_of_op_commute
                (hcomm.2 g (List.mem_cons_self) x (List.mem_cons_of_mem g hx)))
          have hcommB : PauliElem.mul g (maskProduct gs m₀')
              = PauliElem.mul (maskProduct gs m₀') g :=
            maskProduct_comm gs m₀' g (fun x hx =>
              pauliElem_mul_comm_of_op_commute
                (hcomm.2 g (List.mem_cons_self) x (List.mem_cons_of_mem g hx)))
          have hcommAB : PauliElem.mul g
                (PauliElem.mul (maskProduct gs m₀) (maskProduct gs m₀'))
              = PauliElem.mul (PauliElem.mul (maskProduct gs m₀) (maskProduct gs m₀')) g :=
            pauliElem_mul_comm_of_comm g (maskProduct gs m₀) (maskProduct gs m₀') hcommA hcommB
          have hgh : PauliElem.mul g g = 1 :=
            pauliElem_herm_sq (hcomm.1 g (List.mem_cons_self))
          have hchain : PauliElem.mul (PauliElem.mul g (maskProduct gs m₀))
                (PauliElem.mul g (maskProduct gs m₀'))
              = PauliElem.mul (maskProduct gs m₀) (maskProduct gs m₀') := by
                calc (PauliElem.mul (PauliElem.mul g (maskProduct gs m₀))
                    (PauliElem.mul g (maskProduct gs m₀')))
                    = PauliElem.mul (PauliElem.mul (PauliElem.mul g (maskProduct gs m₀)) g)
                        (maskProduct gs m₀') :=
                      (pauliElem_mul_assoc' _ _ _).symm
                  _ = PauliElem.mul (PauliElem.mul (PauliElem.mul (maskProduct gs m₀) g) g)
                        (maskProduct gs m₀') := by rw [hcommA]
                  _ = PauliElem.mul (PauliElem.mul (maskProduct gs m₀) g)
                        (PauliElem.mul g (maskProduct gs m₀')) :=
                      (pauliElem_mul_assoc' _ _ _)
                  _ = PauliElem.mul (maskProduct gs m₀)
                        (PauliElem.mul g (PauliElem.mul g (maskProduct gs m₀'))) :=
                      (pauliElem_mul_assoc' _ _ _)
                  _ = PauliElem.mul (maskProduct gs m₀)
                        (PauliElem.mul (PauliElem.mul g g) (maskProduct gs m₀')) := by
                      rw [pauliElem_mul_assoc' g g (maskProduct gs m₀')]
                  _ = PauliElem.mul (maskProduct gs m₀)
                        (PauliElem.mul 1 (maskProduct gs m₀')) := by rw [hgh]
                  _ = PauliElem.mul (maskProduct gs m₀) (maskProduct gs m₀') := by
                      rw [pauliElem_one_mul]
          cases b with
          | false =>
              cases b' with
              | false =>
                  rw [hsplit]
                  simp only [maskProduct, Bool.xor_false, Bool.false_eq_true, ↓reduceIte]
                  exact hih
              | true =>
                  rw [hsplit]
                  simp only [maskProduct, Bool.xor_true, Bool.not_false, Bool.false_eq_true,
                    ↓reduceIte]
                  rw [hih]
                  calc (PauliElem.mul g (PauliElem.mul (maskProduct gs m₀)
                        (maskProduct gs m₀')))
                      = PauliElem.mul (PauliElem.mul g (maskProduct gs m₀))
                          (maskProduct gs m₀') :=
                        (pauliElem_mul_assoc' _ _ _).symm
                    _ = PauliElem.mul (PauliElem.mul (maskProduct gs m₀) g)
                          (maskProduct gs m₀') := by rw [hcommA]
                    _ = PauliElem.mul (maskProduct gs m₀)
                          (PauliElem.mul g (maskProduct gs m₀')) :=
                        (pauliElem_mul_assoc' _ _ _)
          | true =>
              cases b' with
              | false =>
                  rw [hsplit]
                  simp only [maskProduct, Bool.xor_false, Bool.false_eq_true, ↓reduceIte]
                  rw [hih]
                  calc (PauliElem.mul g (PauliElem.mul (maskProduct gs m₀)
                        (maskProduct gs m₀')))
                      = PauliElem.mul (PauliElem.mul g (maskProduct gs m₀))
                          (maskProduct gs m₀') :=
                        (pauliElem_mul_assoc' _ _ _).symm
              | true =>
                  rw [hsplit]
                  simp only [maskProduct, Bool.xor_true, Bool.not_true, Bool.false_eq_true,
                    ↓reduceIte]
                  rw [hih]
                  calc (PauliElem.mul (maskProduct gs m₀) (maskProduct gs m₀'))
                      = PauliElem.mul (PauliElem.mul g (maskProduct gs m₀))
                          (PauliElem.mul g (maskProduct gs m₀')) := hchain.symm

/-- The identity belongs to the set of masked generator products. -/
theorem generatedSubgroup_one_mem {n : ℕ} (gs : List (PauliElem n)) :
    (1 : PauliElem n) ∈ generatedSubgroup gs := by
  refine ⟨List.replicate gs.length false, ⟨by simp, ?_⟩⟩
  exact maskProduct_eq_one gs _ (by simp) (by simp)

/-- The set generated by commuting Hermitian Pauli elements is closed under Pauli
multiplication. -/
theorem generatedSubgroup_mul_mem {n : ℕ} (gs : List (PauliElem n))
    (hgs : CommutingHermitianPaulis gs) {p q : PauliElem n}
    (hp : p ∈ generatedSubgroup gs) (hq : q ∈ generatedSubgroup gs) :
    PauliElem.mul p q ∈ generatedSubgroup gs := by
  obtain ⟨m, hm, hpm⟩ := hp
  obtain ⟨m', hm', hqm⟩ := hq
  have hlen : (maskXor m m').length = gs.length := by
    rw [maskXor_length m m' (hm.trans hm'.symm), hm]
  refine ⟨maskXor m m', ⟨hlen, ?_⟩⟩
  calc maskProduct gs (maskXor m m')
      = maskProduct gs m * maskProduct gs m' := maskProduct_xor gs hgs m m' hm hm'
    _ = p * q := by rw [hpm, hqm]

/-- Pauli elements with equal binary symplectic vectors and equal phase exponents are equal. -/
theorem pauliElem_eq_of_symplecticVec_phase {n : ℕ} {p q : PauliElem n}
    (h1 : symplecticVec p.word = symplecticVec q.word) (h2 : p.phase = q.phase) :
    p = q := by
  apply pauli_ext
  · exact symplecticVec_injective h1
  · exact h2

/-- Every element of `ZMod 4` is zero, one, two, or three. -/
theorem zmod4_cases (e : ZMod 4) : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by
  have hlt : e.val < 4 := ZMod.val_lt e
  interval_cases h : e.val
  · left
    have hz : e = 0 := by
      have hh := ZMod.natCast_zmod_val e
      rw [h, Nat.cast_zero] at hh
      exact hh.symm
    exact hz
  · right; left
    have hz : e = 1 := by
      have hh := ZMod.natCast_zmod_val e
      rw [h] at hh
      rw [← hh]
      simp
    exact hz
  · right; right; left
    have hz : e = 2 := by
      have hh := ZMod.natCast_zmod_val e
      rw [h] at hh
      rw [← hh]
      simp
    exact hz
  · right; right; right
    have hz : e = 3 := by
      have hh := ZMod.natCast_zmod_val e
      rw [h] at hh
      rw [← hh]
      simp
    exact hz

/-- The product of two commuting Hermitian Pauli elements is Hermitian. -/
theorem mul_herm_comm_herm {n : ℕ} {p q : PauliElem n} (hp : IsHermitianPauli p)
    (hq : IsHermitianPauli q) (hc : op p * op q = op q * op p) :
    IsHermitianPauli (PauliElem.mul p q) := by
  have hsq : op (PauliElem.mul p q) * op (PauliElem.mul p q) = 1 := by
    rw [op_mul]
    calc (op p * op q) * (op p * op q) = op p * (op q * op p) * op q := by ac_rfl
      _ = op p * (op p * op q) * op q := by rw [hc]
      _ = (op p * op p) * (op q * op q) := by ac_rfl
      _ = 1 := by rw [op_mul_self hp, op_mul_self hq, Matrix.mul_one]
  have hcoeff : (Complex.I ^ ((PauliElem.mul p q).phase + (PauliElem.mul p q).phase).val : ℂ) = 1 := by
    have h := op_mul_self_eq_phase (PauliElem.mul p q)
    rw [← hsq] at h
    have h' := congrArg (fun M : Matrix (Reg n) (Reg n) ℂ => M 0 0) h
    rw [hsq] at h'
    simp only [Matrix.smul_apply, Matrix.one_apply, if_true, smul_eq_mul, mul_one] at h'
    exact h'.symm
  have hval : ((PauliElem.mul p q).phase + (PauliElem.mul p q).phase).val = 0 := by
    have hlt : ((PauliElem.mul p q).phase + (PauliElem.mul p q).phase).val < 4 :=
      ZMod.val_lt _
    have hinj : ((PauliElem.mul p q).phase + (PauliElem.mul p q).phase).val = 0 :=
      complex_I_pow_inj hlt (by decide) hcoeff
    exact hinj
  have hsum : (PauliElem.mul p q).phase + (PauliElem.mul p q).phase = 0 := by
    have hh := ZMod.natCast_zmod_val ((PauliElem.mul p q).phase + (PauliElem.mul p q).phase)
    rw [hval, Nat.cast_zero] at hh
    exact hh.symm
  rcases zmod4_cases (PauliElem.mul p q).phase with h0 | h1 | h2 | h3
  · exact Or.inl h0
  · exfalso
    rw [h1] at hsum
    exact absurd hsum (by decide)
  · exact Or.inr h2
  · exfalso
    rw [h3] at hsum
    exact absurd hsum (by decide)

/-- For commuting Hermitian generators, the linear map associated to `projectorAux` is
idempotent. -/
theorem projectorAux_toLin'_idem {n : ℕ} (gs : List (PauliElem n))
    (hgs : CommutingHermitianPaulis gs) :
    (projectorAux gs).toLin'.comp (projectorAux gs).toLin' = (projectorAux gs).toLin' := by
  have hmul : projectorAux gs * projectorAux gs = projectorAux gs :=
    projectorAux_mul_self gs hgs
  rw [← Matrix.toLin'_mul, hmul]

/-- For a consistent tableau, its code space is the range of the associated generator projector. -/
theorem codeSpace_eq_range {n m : ℕ} (t : Tableau n m) (ht : ConsistentTableau t) :
    codeSpace t = (projectorAux (tableauGenerators t)).toLin'.range := by
  have hgen : CommutingHermitianPaulis (tableauGenerators t) := by
    constructor
    · intro h hh
      obtain ⟨a, rfl⟩ := (mem_tableauGenerators t h).mp hh
      exact ht.1 a
    · intro u hu v hv
      obtain ⟨a, rfl⟩ := (mem_tableauGenerators t u).mp hu
      obtain ⟨b, rfl⟩ := (mem_tableauGenerators t v).mp hv
      exact ht.2 a b
  have hcomp := projectorAux_toLin'_idem (tableauGenerators t) hgen
  ext ψ
  constructor
  · intro hψ
    have h : projectorAux (tableauGenerators t) *ᵥ ψ = ψ :=
      (stabilizerProjector_mem_codeSpace t ht ψ).mp hψ
    refine ⟨ψ, ?_⟩
    rw [Matrix.toLin'_apply]
    exact h
  · rintro ⟨x, hx⟩
    have h1 : (projectorAux (tableauGenerators t)).toLin' ψ = ψ := by
      rw [← hx]
      rw [← LinearMap.comp_apply, hcomp]
    have hfix : projectorAux (tableauGenerators t) *ᵥ ψ = ψ := by
      rwa [Matrix.toLin'_apply] at h1
    exact (stabilizerProjector_mem_codeSpace t ht ψ).mpr hfix

/-- The range of the projector for `k ≤ n` independent commuting Hermitian generators has
complex dimension `2 ^ (n - k)`. -/
theorem finrank_range_projectorAux {n k : ℕ} (gs : List (PauliElem n)) (hgs : gs.length = k)
    (hk : k ≤ n) (hcomm : CommutingHermitianPaulis gs) (hind : IndependentGenerators gs) :
    Module.finrank ℂ ((projectorAux gs).toLin'.range) = 2 ^ (n - k) := by
  have hidem : (projectorAux gs).toLin' * (projectorAux gs).toLin' = (projectorAux gs).toLin' := by
    rw [Module.End.mul_eq_comp, projectorAux_toLin'_idem gs hcomm]
  have hproj : LinearMap.IsProj ((projectorAux gs).toLin').range (projectorAux gs).toLin' :=
    LinearMap.IsIdempotentElem.isProj_range _ hidem
  have htr : LinearMap.trace ℂ (Reg n → ℂ) (projectorAux gs).toLin'
      = (Module.finrank ℂ ((projectorAux gs).toLin').range : ℂ) := hproj.trace
  rw [Matrix.trace_toLin'_eq] at htr
  have hmain : Matrix.trace (projectorAux gs) = (2 : ℂ) ^ (n - k) :=
    trace_projectorAux_eq_pow gs hgs hk hind
  rw [hmain] at htr
  exact_mod_cast htr.symm

/-- A consistent tableau with `k ≤ n` independent generators has code-space dimension `2 ^ (n -
k)`. -/
theorem finrank_codeSpace {n m k : ℕ} (t : Tableau n m)
    (hgs : (tableauGenerators t).length = k) (hk : k ≤ n) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t)) :
    Module.finrank ℂ (codeSpace t) = 2 ^ (n - k) := by
  have hgen : CommutingHermitianPaulis (tableauGenerators t) := by
    constructor
    · intro h hh
      obtain ⟨a, rfl⟩ := (mem_tableauGenerators t h).mp hh
      exact ht.1 a
    · intro u hu v hv
      obtain ⟨a, rfl⟩ := (mem_tableauGenerators t u).mp hu
      obtain ⟨b, rfl⟩ := (mem_tableauGenerators t v).mp hv
      exact ht.2 a b
  rw [codeSpace_eq_range t ht]
  exact finrank_range_projectorAux (tableauGenerators t) hgs hk hgen hind

/-- A consistent tableau with `k ≤ n` independent generators possesses a normalized state in its
code space. -/
theorem exists_normalized_codeState {n m k : ℕ} (t : Tableau n m)
    (hgs : (tableauGenerators t).length = k) (hk : k ≤ n) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t)) :
    ∃ ψ : QState (Reg n), Normalized ψ ∧ ψ ∈ codeSpace t := by
  have hfr : Module.finrank ℂ (codeSpace t) = 2 ^ (n - k) :=
    finrank_codeSpace t hgs hk ht hind
  have hne : codeSpace t ≠ ⊥ := by
    intro hz
    have hz2 : Module.finrank ℂ (codeSpace t) = 0 := by
      rw [hz]
      exact finrank_bot ℂ (QState (Reg n))
    rw [hfr] at hz2
    norm_num at hz2
  obtain ⟨ψ, hψ, hψne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  set S : ℝ := ∑ i, ‖ψ i‖ ^ 2 with hSdef
  have hSpos : 0 < S := by
    have hsome : ∃ i, ψ i ≠ 0 := by
      by_contra h
      apply hψne
      funext i
      exact Classical.byContradiction fun h1 => h ⟨i, h1⟩
    obtain ⟨i, hi⟩ := hsome
    have hne0 : ‖ψ i‖ ≠ 0 := norm_ne_zero_iff.mpr hi
    have hpos' : 0 < ‖ψ i‖ ^ 2 := by positivity
    rw [hSdef]
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, hpos'⟩
  have hsq : ‖(Real.sqrt S : ℂ)‖ ^ 2 = S := by
    rw [norm_sq_ofReal, Real.sq_sqrt (le_of_lt hSpos)]
  have hinv : ‖((Real.sqrt S : ℂ)⁻¹ : ℂ)‖ ^ 2 = S⁻¹ := by
    rw [norm_inv, inv_pow, hsq]
  have hconv : ∀ i : Reg n, (((Real.sqrt S : ℂ)⁻¹ : ℂ) • ψ) i
      = (((Real.sqrt S : ℂ)⁻¹ : ℂ) : ℂ) * ψ i := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul]
  refine ⟨((Real.sqrt S : ℂ)⁻¹ : ℂ) • ψ, ?_, ?_⟩
  · simp only [Normalized]
    calc ∑ i, ‖(((Real.sqrt S : ℂ)⁻¹ : ℂ) • ψ) i‖ ^ 2
        = ∑ i, (‖ψ i‖ ^ 2 * ‖((Real.sqrt S : ℂ)⁻¹ : ℂ)‖ ^ 2) := by
          exact Finset.sum_congr rfl fun i _ => by rw [hconv i, norm_mul]; ring
      _ = (∑ i, ‖ψ i‖ ^ 2) * ‖((Real.sqrt S : ℂ)⁻¹ : ℂ)‖ ^ 2 := by rw [Finset.sum_mul]
      _ = 1 := by rw [hSdef, hinv, mul_inv_cancel₀ (ne_of_gt hSpos)]
  · intro a
    rw [Matrix.mulVec_smul]
    congr 1
    exact (mem_codeSpace_iff t ψ).mp hψ a

/-- For a consistent tableau with `n` independent generators, any two normalized code states
differ by a nonzero complex scalar. See [Aaronson and Gottesman, Theorem
1][AaronsonGottesman2004]. -/
theorem unique_stabilizerState {n m : ℕ} (t : Tableau n m) (ht : ConsistentTableau t)
    (hgs : (tableauGenerators t).length = n) (hind : IndependentGenerators (tableauGenerators t)) :
    ∀ ψ₁ ψ₂ : QState (Reg n), ψ₁ ∈ codeSpace t → ψ₂ ∈ codeSpace t →
      Normalized ψ₁ → Normalized ψ₂ → ∃ lam : ℂ, lam ≠ 0 ∧ ψ₂ = lam • ψ₁ := by
  have hfr : Module.finrank ℂ (codeSpace t) = 1 := by
    rw [finrank_codeSpace t hgs (le_refl n) ht hind]
    simp
  have hne : codeSpace t ≠ ⊥ := by
    intro hz
    have hz2 : Module.finrank ℂ (codeSpace t) = 0 := by
      rw [hz]
      exact finrank_bot ℂ (QState (Reg n))
    rw [hfr] at hz2
    norm_num at hz2
  obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hspan : codeSpace t = ℂ ∙ v := by
    have hle : (ℂ ∙ v : Submodule ℂ (QState (Reg n))) ≤ codeSpace t := by
      refine Submodule.span_le.2 ?_
      intro x hx
      have hxv : x = v := Set.mem_singleton_iff.mp hx
      subst hxv
      exact hv
    have hne2 : (ℂ ∙ v : Submodule ℂ (QState (Reg n))) ≠ ⊥ := by
      intro hz
      have hmemv : v ∈ (ℂ ∙ v : Submodule ℂ (QState (Reg n))) :=
        Submodule.mem_span_singleton_self v
      rw [hz] at hmemv
      exact hvne hmemv
    have hatom : IsAtom (codeSpace t) :=
      (Submodule.isAtom_iff_finrank_eq_one).mpr hfr
    have hle' : codeSpace t ≤ (ℂ ∙ v : Submodule ℂ (QState (Reg n))) :=
      (isAtom_iff_le_of_ge.mp hatom).2 (ℂ ∙ v) hne2 hle
    exact le_antisymm hle' hle
  intro ψ₁ ψ₂ h₁ h₂ hn₁ hn₂
  have hψ₁ne : ψ₁ ≠ 0 := by
    intro hz
    have hsum : ∑ i, ‖ψ₁ i‖ ^ 2 = 1 := by simpa [Normalized] using! hn₁
    rw [hz] at hsum
    simp at hsum
  have hψ₂ne : ψ₂ ≠ 0 := by
    intro hz
    have hsum : ∑ i, ‖ψ₂ i‖ ^ 2 = 1 := by simpa [Normalized] using! hn₂
    rw [hz] at hsum
    simp at hsum
  have hmem2 : ψ₂ ∈ (ℂ ∙ v : Submodule ℂ (QState (Reg n))) := by
    rw [← hspan]
    exact h₂
  have hmem1 : ψ₁ ∈ (ℂ ∙ v : Submodule ℂ (QState (Reg n))) := by
    rw [← hspan]
    exact h₁
  obtain ⟨c, hcv⟩ := Submodule.mem_span_singleton.mp hmem2
  obtain ⟨c', hcv'⟩ := Submodule.mem_span_singleton.mp hmem1
  have hc0 : c = 0 → ψ₂ = 0 := by
    intro hz
    rw [← hcv, hz, zero_smul]
  have hc'0 : c' = 0 → ψ₁ = 0 := by
    intro hz
    rw [← hcv', hz, zero_smul]
  have hcne : c ≠ 0 := fun hz => hψ₂ne (hc0 hz)
  have hc'ne : c' ≠ 0 := fun hz => hψ₁ne (hc'0 hz)
  refine ⟨c * c'⁻¹, ?_, ?_⟩
  · intro hz
    rcases mul_eq_zero.mp hz with h1 | h2
    · exact hcne h1
    · exact absurd h2 (inv_ne_zero hc'ne)
  · rw [← hcv, ← hcv']
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    field_simp [hc'ne]

/-- A state fixed by every generator is fixed by every masked product with the required mask
length. -/
theorem op_maskProduct_fixes_codeSpace' {n : ℕ} (gs : List (PauliElem n)) (ψ : QState (Reg n))
    (hfix : ∀ g ∈ gs, op g *ᵥ ψ = ψ) :
    ∀ (mask : Mask), mask.length = gs.length → op (maskProduct gs mask) *ᵥ ψ = ψ := by
  have hop1 : op (1 : PauliElem n) = 1 := op_one
  induction gs with
  | nil =>
      intro mask hmask
      have hlen0 : mask.length = 0 := by
        rw [List.length_nil] at hmask
        exact hmask
      have : mask = [] := List.length_eq_zero_iff.mp hlen0
      subst this
      simp only [maskProduct]
      rw [hop1]
      exact Matrix.one_mulVec ψ
  | cons g gs ih =>
      intro mask hmask
      have hfix' : ∀ g' ∈ gs, op g' *ᵥ ψ = ψ := by
        intro g' hg'
        exact hfix g' (List.mem_cons_of_mem g hg')
      cases mask with
      | nil =>
          exfalso
          simp at hmask
      | cons b mask =>
          have hlen : mask.length = gs.length := by
            simp only [List.length_cons] at hmask
            omega
          have hg : op g *ᵥ ψ = ψ := hfix g (List.mem_cons_self)
          cases b with
          | false =>
              rw [maskProduct, if_neg (by decide)]
              exact ih hfix' mask hlen
          | true =>
              rw [maskProduct, if_pos (by decide)]
              rw [op_mul, ← Matrix.mulVec_mulVec]
              rw [ih hfix' mask hlen]
              exact hg

/-- Every code state is fixed by every masked product of the tableau generators. -/
theorem op_maskProduct_fixes_codeSpace {n m : ℕ} (t : Tableau n m) (ψ : QState (Reg n))
    (hψ : ψ ∈ codeSpace t) (mask : Mask) (hmask : mask.length = (tableauGenerators t).length) :
    op (maskProduct (tableauGenerators t) mask) *ᵥ ψ = ψ := by
  have hfix : ∀ g ∈ tableauGenerators t, op g *ᵥ ψ = ψ := by
    intro g hg
    obtain ⟨a, rfl⟩ := (mem_tableauGenerators t g).mp hg
    exact hψ a
  exact op_maskProduct_fixes_codeSpace' (tableauGenerators t) ψ hfix mask hmask

/-- If a Hermitian Pauli fixes a state, its positive measurement branch has the full state mass
and its negative branch has zero mass. -/
theorem pauliBranch_deterministic_of_fixes {n : ℕ} (ψ : QState (Reg n))
    (p : PauliElem n) (hp : IsHermitianPauli p) (hfix : op p *ᵥ ψ = ψ) :
    ProjectiveBranchMass (pauliBranchProjector p true) true ψ = MeasureProb ψ Finset.univ ∧
      ProjectiveBranchMass (pauliBranchProjector p true) false ψ = 0 := by
  have hplus : pauliBranchProjector p true *ᵥ ψ = ψ := by
    have hstep : pauliBranchProjector p true *ᵥ ψ
        = ((2 : ℂ)⁻¹) • ((1 + op p) *ᵥ ψ) := by
      rw [pauliBranchProjector]
      exact Matrix.smul_mulVec _ _ _
    rw [hstep, Matrix.add_mulVec, Matrix.one_mulVec, hfix]
    funext x
    simp only [Pi.smul_apply, Pi.add_apply]
    calc ((2 : ℂ)⁻¹) * (ψ x + ψ x) = ((2 : ℂ)⁻¹) * (2 * ψ x) := by ring
      _ = ((2 : ℂ)⁻¹ * 2) * ψ x := by ring
      _ = ψ x := by rw [half_mul_two]; ring
  refine ⟨?_, ?_⟩
  · have hbranch : ProjectiveBranch (pauliBranchProjector p true) true ψ = ψ := by
      rw [ProjectiveBranch]
      exact hplus
    simp only [ProjectiveBranchMass]
    rw [hbranch]
  · have hsum := projectiveBranchMass_add
      (pauliBranchProjector_isOrthogonalProjector hp true) ψ
    have hplusmass : ProjectiveBranchMass (pauliBranchProjector p true) true ψ
        = MeasureProb ψ Finset.univ := by
      have hbranch : ProjectiveBranch (pauliBranchProjector p true) true ψ = ψ := by
        rw [ProjectiveBranch]
        exact hplus
      simp only [ProjectiveBranchMass]
      rw [hbranch]
    rw [hplusmass] at hsum
    linarith

/-- A Hermitian Pauli in the generated set has a deterministic positive measurement branch on
the tableau code space. -/
theorem pauliBranch_deterministic_of_generatedSubgroup {n m : ℕ} (t : Tableau n m)
    (ψ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) (p : PauliElem n) (hp : IsHermitianPauli p)
    (hgen : p ∈ generatedSubgroup (tableauGenerators t)) :
    ProjectiveBranchMass (pauliBranchProjector p true) true ψ = MeasureProb ψ Finset.univ ∧
      ProjectiveBranchMass (pauliBranchProjector p true) false ψ = 0 := by
  obtain ⟨mask, hmask, hprod⟩ := hgen
  refine pauliBranch_deterministic_of_fixes ψ p hp ?_
  rw [← hprod]
  exact op_maskProduct_fixes_codeSpace t ψ hψ mask hmask

/-- A Hermitian Pauli anticommuting with some tableau row has equal measurement branch masses on
every code state. -/
theorem pauliBranch_equiprobable_of_anticommute_some {n m : ℕ} (t : Tableau n m)
    (ψ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) (p : PauliElem n) (hp : IsHermitianPauli p)
    (hanti : ∃ a : Fin m, op (t a).decode * op p = - (op p * op (t a).decode)) :
    ProjectiveBranchMass (pauliBranchProjector p true) true ψ = MeasureProb ψ Finset.univ / 2 ∧
      ProjectiveBranchMass (pauliBranchProjector p true) false ψ = MeasureProb ψ Finset.univ / 2 := by
  obtain ⟨a, ha⟩ := hanti
  exact pauliBranch_equiprobable t ψ hψ a p hp ha

/-- For a normalized code state, measuring a Hermitian Pauli anticommuting with some tableau row
has the fair-bit branch probabilities. -/
theorem pauliBranchMass_fairBit_of_anticommute_some {n m : ℕ} (t : Tableau n m)
    (ψ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) (hn : Normalized ψ) (p : PauliElem n)
    (hp : IsHermitianPauli p)
    (hanti : ∃ a : Fin m, op (t a).decode * op p = - (op p * op (t a).decode)) :
    ProjectiveBranchMass (pauliBranchProjector p true) true ψ = fairBitLaw.prob true ∧
      ProjectiveBranchMass (pauliBranchProjector p true) false ψ = fairBitLaw.prob false := by
  obtain ⟨a, ha⟩ := hanti
  exact pauliBranchMass_fairBit t ψ hψ hn a p hp ha

/-- The binary dot product with the zero vector is zero. -/
theorem booleanDot_zero {n : ℕ} (a : BooleanVec n) : booleanDot a 0 = 0 := by
  simp [booleanDot]

/-- The value of `quadFun Q b c` at zero is its constant coefficient `c`. -/
theorem quadFun_zero {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n)
    (c : ZMod 2) : quadFun Q b c 0 = c := by
  simp [quadFun]

/-- The natural representative of one in `ZMod 2` is one. -/
theorem zmod2_val_one : (1 : ZMod 2).val = 1 := by decide

/-- A stabilizer function nonzero at the origin takes value one or negative one there. -/
theorem isStabilizerFun_value_zero {n : ℕ} (φ : BooleanVec n → ℂ) (hφ : IsStabilizerFun φ)
    (hzero : φ 0 ≠ 0) :
    φ 0 ∈ ({1, -1} : Set ℂ) := by
  obtain ⟨a, Q, b, c, A, hφ'⟩ := hφ
  have hmem : (0 : BooleanVec n) ∈ A := by
    by_contra hn
    rw [hφ'] at hzero
    simp [booleanDot_zero, quadFun_zero, hn] at hzero
  rw [hφ']
  change (Complex.I ^ (booleanDot a 0).val * (-1 : ℂ) ^ (quadFun Q b c 0).val
      * (if (0 : BooleanVec n) ∈ A then (1 : ℂ) else 0)) ∈ ({1, -1} : Set ℂ)
  rw [booleanDot_zero, quadFun_zero]
  simp only [hmem, if_pos]
  rcases zmod2_eq_zero_or_one c with rfl | rfl <;> simp [zmod2_val_one]

/-- A stabilizer function cannot take the value `Complex.I` at the origin. -/
theorem not_isStabilizerFun_imag_zero {n : ℕ} (φ : BooleanVec n → ℂ) (hφ : IsStabilizerFun φ)
    (himag : φ 0 = Complex.I) (hne : φ 0 ≠ 0) : False := by
  have h := isStabilizerFun_value_zero φ hφ hne
  rw [himag] at h
  rcases h with h | h
  · exact absurd h (by simp [Complex.ext_iff])
  · exact absurd h (by simp [Complex.ext_iff])

/-- The one-bit function equal to `Complex.I` at zero and one elsewhere is not a stabilizer
function. -/
theorem not_isStabilizerFun_one_imag :
    ¬ IsStabilizerFun (fun x : BooleanVec 1 => if x = 0 then Complex.I else 1) := by
  intro h
  have hne : (fun x : BooleanVec 1 => if x = 0 then Complex.I else 1) 0 ≠ 0 := by simp
  exact not_isStabilizerFun_imag_zero _ h (by simp) hne

/-- Single-site Hadamard conjugation preserves the site symplectic form. -/
theorem siteForm_conjH (a b : Pauli1) :
    siteForm (conjHWord a) (conjHWord b) = siteForm a b := by
  cases a <;> cases b <;> decide

/-- Single-site phase-gate conjugation preserves the site symplectic form. -/
theorem siteForm_conjS (a b : Pauli1) :
    siteForm (conjSWord a) (conjSWord b) = siteForm a b := by
  cases a <;> cases b <;> decide

/-- The two-site CNOT word update preserves the sum of the two site symplectic pairings. -/
theorem siteForm_cnot (a b c d : Pauli1) :
    siteForm (pauliMul1 a (cnotTargetCross b)) (pauliMul1 c (cnotTargetCross d))
      + siteForm (pauliMul1 (cnotControlCross a) b) (pauliMul1 (cnotControlCross c) d)
      = siteForm a c + siteForm b d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- For the displayed X and Y letters, the single-site expression obtained from the CNOT word
update fails to preserve the site pairing. -/
theorem siteForm_cnot_degenerate_not :
    siteForm (pauliMul1 .X (cnotTargetCross .X)) (pauliMul1 .Y (cnotTargetCross .Y))
      ≠ siteForm .X .Y := by
  decide

/-- A finite sum splits into its values at two distinct indices and the sum over the remaining
indices. -/
theorem sum_split_two {n : ℕ} (i j : Fin n) (hij : i ≠ j) (f : Fin n → ZMod 2) :
    (∑ k, f k) = f i + f j + ∑ k ∈ Finset.univ \ {i, j}, f k := by
  have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hj : j ∈ Finset.univ.erase i := by simp [hij.symm]
  rw [← Finset.sum_erase_add _ _ hi, ← Finset.sum_erase_add _ _ hj]
  have hset : ((Finset.univ : Finset (Fin n)).erase i).erase j
      = Finset.univ \ {i, j} := by
    ext k
    simp [and_comm]
  rw [hset]
  abel

/-- Hadamard conjugation sends the site X coordinate to the original Z coordinate. -/
theorem siteX_conjH (a : Pauli1) : siteX (conjHWord a) = siteZ a := by
  cases a <;> decide

/-- Hadamard conjugation sends the site Z coordinate to the original X coordinate. -/
theorem siteZ_conjH (a : Pauli1) : siteZ (conjHWord a) = siteX a := by
  cases a <;> decide

/-- Phase-gate conjugation preserves the site X coordinate. -/
theorem siteX_conjS (a : Pauli1) : siteX (conjSWord a) = siteX a := by
  cases a <;> decide

/-- Phase-gate conjugation adds the site X coordinate to the site Z coordinate. -/
theorem siteZ_conjS (a : Pauli1) : siteZ (conjSWord a) = siteZ a + siteX a := by
  cases a <;> decide

/-- The displayed `cnotTargetCross` word update preserves the X coordinate of its first letter. -/
theorem siteX_cnotTarget (a b : Pauli1) :
    siteX (pauliMul1 a (cnotTargetCross b)) = siteX a := by
  cases a <;> cases b <;> decide

/-- The displayed `cnotTargetCross` word update adds the Z coordinates of its two letters. -/
theorem siteZ_cnotTarget (a b : Pauli1) :
    siteZ (pauliMul1 a (cnotTargetCross b)) = siteZ a + siteZ b := by
  cases a <;> cases b <;> decide

/-- The displayed `cnotControlCross` word update adds the X coordinates of its two letters. -/
theorem siteX_cnotControl (a b : Pauli1) :
    siteX (pauliMul1 (cnotControlCross a) b) = siteX a + siteX b := by
  cases a <;> cases b <;> decide

/-- The displayed `cnotControlCross` word update preserves the Z coordinate of its second
letter. -/
theorem siteZ_cnotControl (a b : Pauli1) :
    siteZ (pauliMul1 (cnotControlCross a) b) = siteZ b := by
  cases a <;> cases b <;> decide

/-- The action of a legal Clifford gate preserves the binary symplectic pairing of Pauli words. -/
theorem symplecticForm_cliffordAction {n : ℕ} (g : CliffordGate n) (hg : legalGate g)
    (p q : PauliElem n) :
    symplecticForm (symplecticVec (cliffordAction g p).word)
        (symplecticVec (cliffordAction g q).word)
      = symplecticForm (symplecticVec p.word) (symplecticVec q.word) := by
  simp only [symplecticVec]
  rw [symplecticForm_eq_sum_site, symplecticForm_eq_sum_site]
  cases g with
  | H i =>
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hki : k = i
      · rw [hki]
        have h1 : (cliffordAction (.H i) p).word i = conjHWord (p.word i) := by
          simp [cliffordAction]
        have h2 : (cliffordAction (.H i) q).word i = conjHWord (q.word i) := by
          simp [cliffordAction]
        rw [h1, h2]
        exact siteForm_conjH _ _
      · have h1 : (cliffordAction (.H i) p).word k = p.word k := by
          simp [cliffordAction, hki]
        have h2 : (cliffordAction (.H i) q).word k = q.word k := by
          simp [cliffordAction, hki]
        rw [h1, h2]
  | S i =>
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hki : k = i
      · rw [hki]
        have h1 : (cliffordAction (.S i) p).word i = conjSWord (p.word i) := by
          simp [cliffordAction]
        have h2 : (cliffordAction (.S i) q).word i = conjSWord (q.word i) := by
          simp [cliffordAction]
        rw [h1, h2]
        exact siteForm_conjS _ _
      · have h1 : (cliffordAction (.S i) p).word k = p.word k := by
          simp [cliffordAction, hki]
        have h2 : (cliffordAction (.S i) q).word k = q.word k := by
          simp [cliffordAction, hki]
        rw [h1, h2]
  | CNOT i j =>
      have hij : i ≠ j := hg

      have hsite :
          siteForm ((cliffordAction (.CNOT i j) p).word i)
              ((cliffordAction (.CNOT i j) q).word i)
            + siteForm ((cliffordAction (.CNOT i j) p).word j)
              ((cliffordAction (.CNOT i j) q).word j)
            = siteForm (p.word i) (q.word i) + siteForm (p.word j) (q.word j) := by
        have h1 : (cliffordAction (.CNOT i j) p).word i
            = pauliMul1 (p.word i) (cnotTargetCross (p.word j)) := by
          simp [cliffordAction]
        have h2 : (cliffordAction (.CNOT i j) q).word i
            = pauliMul1 (q.word i) (cnotTargetCross (q.word j)) := by
          simp [cliffordAction]
        have h3 : (cliffordAction (.CNOT i j) p).word j
            = pauliMul1 (cnotControlCross (p.word i)) (p.word j) := by
          simp [cliffordAction, hij.symm]
        have h4 : (cliffordAction (.CNOT i j) q).word j
            = pauliMul1 (cnotControlCross (q.word i)) (q.word j) := by
          simp [cliffordAction, hij.symm]
        rw [h1, h2, h3, h4]
        exact siteForm_cnot _ _ _ _
      have hT : (∑ k, siteForm ((cliffordAction (.CNOT i j) p).word k)
          ((cliffordAction (.CNOT i j) q).word k))
        = siteForm ((cliffordAction (.CNOT i j) p).word i)
            ((cliffordAction (.CNOT i j) q).word i)
          + siteForm ((cliffordAction (.CNOT i j) p).word j)
            ((cliffordAction (.CNOT i j) q).word j)
          + ∑ k ∈ Finset.univ \ {i, j},
            siteForm ((cliffordAction (.CNOT i j) p).word k)
              ((cliffordAction (.CNOT i j) q).word k) :=
        sum_split_two i j hij _
      have hT0 : (∑ k, siteForm (p.word k) (q.word k))
        = siteForm (p.word i) (q.word i) + siteForm (p.word j) (q.word j)
          + ∑ k ∈ Finset.univ \ {i, j}, siteForm (p.word k) (q.word k) :=
        sum_split_two i j hij _
      rw [hT, hsite, hT0]
      have hsum : (∑ k ∈ (Finset.univ : Finset (Fin n)) \ {i, j},
            siteForm ((cliffordAction (.CNOT i j) p).word k)
              ((cliffordAction (.CNOT i j) q).word k))
          = ∑ k ∈ (Finset.univ : Finset (Fin n)) \ {i, j}, siteForm (p.word k) (q.word k) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hmem := Finset.mem_sdiff.mp hk
        have hki : k ≠ i := by
          intro hcon
          exact hmem.2 (by simp [hcon])
        have hkj : k ≠ j := by
          intro hcon
          exact hmem.2 (by simp [hcon])
        have h1 : (cliffordAction (.CNOT i j) p).word k = p.word k := by
          simp [cliffordAction, hki, hkj]
        have h2 : (cliffordAction (.CNOT i j) q).word k = q.word k := by
          simp [cliffordAction, hki, hkj]
        rw [h1, h2]
      rw [hsum]

/-- The action of a legal Clifford gate preserves and reflects commutativity of Pauli operator
matrices. -/
theorem cliffordAction_preserves_commute {n : ℕ} (g : CliffordGate n) (hg : legalGate g)
    (p q : PauliElem n) :
    op (cliffordAction g p) * op (cliffordAction g q)
        = op (cliffordAction g q) * op (cliffordAction g p)
      ↔ op p * op q = op q * op p := by
  rw [op_commute_iff, op_commute_iff]
  simp only [pauliCommute]
  constructor
  · intro h
    have hsym := symplecticForm_cliffordAction g hg p q
    simp only [symplecticVec] at hsym
    rw [hsym] at h
    exact h
  · intro h
    have hsym := symplecticForm_cliffordAction g hg p q
    simp only [symplecticVec] at hsym
    rw [← hsym] at h
    exact h

/-- For a legal Clifford gate, the binary symplectic vector of its Pauli action is given by
`cliffordSymplecticMap`. -/
theorem symplecticVec_cliffordAction {n : ℕ} (g : CliffordGate n) (hg : legalGate g)
    (p : PauliElem n) :
    symplecticVec (cliffordAction g p).word = cliffordSymplecticMap g (symplecticVec p.word) := by
  apply Prod.ext
  · simp only [symplecticVec]
    funext k
    cases g with
    | H i =>
        by_cases hki : k = i
        · rw [hki]
          simp only [symplecticX_apply]
          have h1 : (cliffordAction (.H i) p).word i = conjHWord (p.word i) := by
            simp [cliffordAction]
          have h2 : (cliffordSymplecticMap (.H i) (symplecticX p.word, symplecticZ p.word)).1 i
              = symplecticZ p.word i := by
            simp [cliffordSymplecticMap]
          rw [h1, h2, symplecticZ_apply]
          exact siteX_conjH _
        · simp only [symplecticX_apply]
          have h1 : (cliffordAction (.H i) p).word k = p.word k := by
            simp [cliffordAction, hki]
          have h2 : (cliffordSymplecticMap (.H i) (symplecticX p.word, symplecticZ p.word)).1 k
              = symplecticX p.word k := by
            simp [cliffordSymplecticMap, hki]
          rw [h1, h2, symplecticX_apply]
    | S i =>
        by_cases hki : k = i
        · rw [hki]
          simp only [symplecticX_apply]
          have h1 : (cliffordAction (.S i) p).word i = conjSWord (p.word i) := by
            simp [cliffordAction]
          have h2 : (cliffordSymplecticMap (.S i) (symplecticX p.word, symplecticZ p.word)).1 i
              = symplecticX p.word i := by
            simp [cliffordSymplecticMap]
          rw [h1, h2, symplecticX_apply]
          exact siteX_conjS _
        · simp only [symplecticX_apply]
          have h1 : (cliffordAction (.S i) p).word k = p.word k := by
            simp [cliffordAction, hki]
          have h2 : (cliffordSymplecticMap (.S i) (symplecticX p.word, symplecticZ p.word)).1 k
              = symplecticX p.word k := by
            simp [cliffordSymplecticMap]
          rw [h1, h2, symplecticX_apply]
    | CNOT i j =>
        have hij : i ≠ j := hg
        by_cases hki : k = i
        · rw [hki]
          simp only [symplecticX_apply]
          have h1 : (cliffordAction (.CNOT i j) p).word i
              = pauliMul1 (p.word i) (cnotTargetCross (p.word j)) := by
            simp [cliffordAction]
          have h2 : (cliffordSymplecticMap (.CNOT i j)
              (symplecticX p.word, symplecticZ p.word)).1 i = symplecticX p.word i := by
            simp [cliffordSymplecticMap]
          rw [h1, h2, symplecticX_apply]
          exact siteX_cnotTarget _ _
        · by_cases hkj : k = j
          · rw [hkj]
            simp only [symplecticX_apply]
            have h1 : (cliffordAction (.CNOT i j) p).word j
                = pauliMul1 (cnotControlCross (p.word i)) (p.word j) := by
              simp [cliffordAction, hij.symm]
            have h2 : (cliffordSymplecticMap (.CNOT i j)
                (symplecticX p.word, symplecticZ p.word)).1 j
                = symplecticX p.word i + symplecticX p.word j := by
              simp [cliffordSymplecticMap, hij.symm, add_comm]
            rw [h1, h2, symplecticX_apply, symplecticX_apply]
            exact siteX_cnotControl _ _
          · simp only [symplecticX_apply]
            have h1 : (cliffordAction (.CNOT i j) p).word k = p.word k := by
              simp [cliffordAction, hki, hkj]
            have h2 : (cliffordSymplecticMap (.CNOT i j)
                (symplecticX p.word, symplecticZ p.word)).1 k = symplecticX p.word k := by
              simp [cliffordSymplecticMap, hki, hkj]
            rw [h1, h2, symplecticX_apply]
  · simp only [symplecticVec]
    funext k
    cases g with
    | H i =>
        by_cases hki : k = i
        · rw [hki]
          simp only [symplecticZ_apply]
          have h1 : (cliffordAction (.H i) p).word i = conjHWord (p.word i) := by
            simp [cliffordAction]
          have h2 : (cliffordSymplecticMap (.H i) (symplecticX p.word, symplecticZ p.word)).2 i
              = symplecticX p.word i := by
            simp [cliffordSymplecticMap]
          rw [h1, h2, symplecticX_apply]
          exact siteZ_conjH _
        · simp only [symplecticZ_apply]
          have h1 : (cliffordAction (.H i) p).word k = p.word k := by
            simp [cliffordAction, hki]
          have h2 : (cliffordSymplecticMap (.H i) (symplecticX p.word, symplecticZ p.word)).2 k
              = symplecticZ p.word k := by
            simp [cliffordSymplecticMap, hki]
          rw [h1, h2, symplecticZ_apply]
    | S i =>
        by_cases hki : k = i
        · rw [hki]
          simp only [symplecticZ_apply]
          have h1 : (cliffordAction (.S i) p).word i = conjSWord (p.word i) := by
            simp [cliffordAction]
          have h2 : (cliffordSymplecticMap (.S i) (symplecticX p.word, symplecticZ p.word)).2 i
              = symplecticZ p.word i + symplecticX p.word i := by
            simp [cliffordSymplecticMap]
          rw [h1, h2, symplecticZ_apply, symplecticX_apply]
          exact siteZ_conjS _
        · simp only [symplecticZ_apply]
          have h1 : (cliffordAction (.S i) p).word k = p.word k := by
            simp [cliffordAction, hki]
          have h2 : (cliffordSymplecticMap (.S i) (symplecticX p.word, symplecticZ p.word)).2 k
              = symplecticZ p.word k := by
            simp [cliffordSymplecticMap, hki]
          rw [h1, h2, symplecticZ_apply]
    | CNOT i j =>
        have hij : i ≠ j := hg
        by_cases hki : k = i
        · rw [hki]
          simp only [symplecticZ_apply]
          have h1 : (cliffordAction (.CNOT i j) p).word i
              = pauliMul1 (p.word i) (cnotTargetCross (p.word j)) := by
            simp [cliffordAction]
          have h2 : (cliffordSymplecticMap (.CNOT i j)
              (symplecticX p.word, symplecticZ p.word)).2 i
              = symplecticZ p.word i + symplecticZ p.word j := by
            simp [cliffordSymplecticMap]
          rw [h1, h2, symplecticZ_apply, symplecticZ_apply]
          exact siteZ_cnotTarget _ _
        · by_cases hkj : k = j
          · rw [hkj]
            simp only [symplecticZ_apply]
            have h1 : (cliffordAction (.CNOT i j) p).word j
                = pauliMul1 (cnotControlCross (p.word i)) (p.word j) := by
              simp [cliffordAction, hij.symm]
            have h2 : (cliffordSymplecticMap (.CNOT i j)
                (symplecticX p.word, symplecticZ p.word)).2 j = symplecticZ p.word j := by
              simp [cliffordSymplecticMap, hij.symm]
            rw [h1, h2, symplecticZ_apply]
            exact siteZ_cnotControl _ _
          · simp only [symplecticZ_apply]
            have h1 : (cliffordAction (.CNOT i j) p).word k = p.word k := by
              simp [cliffordAction, hki, hkj]
            have h2 : (cliffordSymplecticMap (.CNOT i j)
                (symplecticX p.word, symplecticZ p.word)).2 k = symplecticZ p.word k := by
              simp [cliffordSymplecticMap, hki]
            rw [h1, h2, symplecticZ_apply]

/-- A circuit of legal Clifford gates preserves the binary symplectic pairing of Pauli words. -/
theorem symplecticForm_cliffordActionCircuit {n : ℕ} (gs : CliffordCircuit n)
    (hlegal : ∀ g ∈ gs, legalGate g) (p q : PauliElem n) :
    symplecticForm (symplecticVec (cliffordActionCircuit gs p).word)
        (symplecticVec (cliffordActionCircuit gs q).word)
      = symplecticForm (symplecticVec p.word) (symplecticVec q.word) := by
  induction gs generalizing p q with
  | nil => rfl
  | cons g gs ih =>
      simp only [cliffordActionCircuit]
      rw [ih (fun g' hg' => hlegal g' (by simp [hg'])) (cliffordAction g p) (cliffordAction g q)]
      exact symplecticForm_cliffordAction g (hlegal g (by simp)) p q

/-- A circuit of legal Clifford gates preserves and reflects commutativity of Pauli operator
matrices. -/
theorem cliffordActionCircuit_preserves_commute {n : ℕ} (gs : CliffordCircuit n)
    (hlegal : ∀ g ∈ gs, legalGate g) (p q : PauliElem n) :
    op (cliffordActionCircuit gs p) * op (cliffordActionCircuit gs q)
        = op (cliffordActionCircuit gs q) * op (cliffordActionCircuit gs p)
      ↔ op p * op q = op q * op p := by
  induction gs generalizing p q with
  | nil => rfl
  | cons g gs ih =>
      simp only [cliffordActionCircuit]
      rw [ih (fun g' hg' => hlegal g' (by simp [hg'])) (cliffordAction g p) (cliffordAction g q)]
      exact cliffordAction_preserves_commute g (hlegal g (by simp)) p q

/-- A legal Clifford circuit preserves all three pairwise commutativity relations among three
Pauli operator matrices. -/
theorem cliffordActionCircuit_preserves_commute_pattern {n : ℕ} (gs : CliffordCircuit n)
    (hlegal : ∀ g ∈ gs, legalGate g) (p q r : PauliElem n) :
    ((op (cliffordActionCircuit gs p) * op (cliffordActionCircuit gs q)
        = op (cliffordActionCircuit gs q) * op (cliffordActionCircuit gs p))
      ↔ (op p * op q = op q * op p))
      ∧ ((op (cliffordActionCircuit gs p) * op (cliffordActionCircuit gs r)
        = op (cliffordActionCircuit gs r) * op (cliffordActionCircuit gs p))
      ↔ (op p * op r = op r * op p))
      ∧ ((op (cliffordActionCircuit gs q) * op (cliffordActionCircuit gs r)
        = op (cliffordActionCircuit gs r) * op (cliffordActionCircuit gs q))
      ↔ (op q * op r = op r * op q)) :=
  ⟨cliffordActionCircuit_preserves_commute gs hlegal p q,
   cliffordActionCircuit_preserves_commute gs hlegal p r,
   cliffordActionCircuit_preserves_commute gs hlegal q r⟩

/-- The binary symplectic vector of a legal Clifford circuit action is given by
`cliffordSymplecticCircuit`. -/
theorem symplecticVec_cliffordActionCircuit {n : ℕ} (gs : CliffordCircuit n)
    (hlegal : ∀ g ∈ gs, legalGate g) (p : PauliElem n) :
    symplecticVec (cliffordActionCircuit gs p).word
      = cliffordSymplecticCircuit gs (symplecticVec p.word) := by
  induction gs generalizing p with
  | nil => rfl
  | cons g gs ih =>
      simp only [cliffordActionCircuit]
      rw [ih (fun g' hg' => hlegal g' (by simp [hg'])) (cliffordAction g p)]
      rw [symplecticVec_cliffordAction g (hlegal g (by simp)) p]
      rfl

/-- Concatenating Clifford circuits composes their binary symplectic actions in execution order. -/
theorem cliffordSymplecticCircuit_append {n : ℕ} (gs hs : CliffordCircuit n)
    (v : BooleanVec n × BooleanVec n) :
    cliffordSymplecticCircuit (gs ++ hs) v
      = cliffordSymplecticCircuit hs (cliffordSymplecticCircuit gs v) := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
      simp only [cliffordSymplecticCircuit, List.cons_append]
      rw [ih]

/-- The local canonicalization map sets the Z coordinate at the selected site to zero. -/
theorem siteCanonicalVector_z_zero {n : ℕ} (j : Fin n) (v : BooleanVec n × BooleanVec n) :
    (siteCanonicalVector j v).2 j = 0 := by
  by_cases hz : v.2 j = 0
  · by_cases hx : v.1 j = 0
    · have h1 : (cliffordSymplecticMap (.S j) v).2 j = v.2 j + v.1 j := by
        simp [cliffordSymplecticMap]
      rw [siteCanonicalVector, if_pos hz, if_pos hx, h1]
      simp [hz, hx]
    · have h1 : (cliffordSymplecticMap (.S j) (cliffordSymplecticMap (.S j) v)).2 j
          = (cliffordSymplecticMap (.S j) v).2 j + (cliffordSymplecticMap (.S j) v).1 j := by
        simp [cliffordSymplecticMap]
      have h2 : (cliffordSymplecticMap (.S j) v).2 j = v.2 j + v.1 j := by
        simp [cliffordSymplecticMap]
      have h3 : (cliffordSymplecticMap (.S j) v).1 j = v.1 j := by
        simp [cliffordSymplecticMap]
      rw [siteCanonicalVector, if_pos hz, if_neg hx, h1, h2, h3]
      rw [hz]
      simp only [zero_add]
      exact zmod2_add_self _
  · by_cases hx : v.1 j = 0
    · have h1 : (cliffordSymplecticMap (.H j) v).2 j = v.1 j := by
        simp [cliffordSymplecticMap]
      rw [siteCanonicalVector, if_neg hz, if_pos hx, h1]
      exact hx
    · have h1 : (cliffordSymplecticMap (.S j) (cliffordSymplecticMap (.H j) v)).2 j
          = (cliffordSymplecticMap (.H j) v).2 j + (cliffordSymplecticMap (.H j) v).1 j := by
        simp [cliffordSymplecticMap]
      have h2 : (cliffordSymplecticMap (.H j) v).2 j = v.1 j := by
        simp [cliffordSymplecticMap]
      have h3 : (cliffordSymplecticMap (.H j) v).1 j = v.2 j := by
        simp [cliffordSymplecticMap]
      have hx1 : v.1 j = 1 := by
        rcases zmod2_eq_zero_or_one (v.1 j) with h | h
        · exact absurd h hx
        · exact h
      have hz1 : v.2 j = 1 := by
        rcases zmod2_eq_zero_or_one (v.2 j) with h | h
        · exact absurd h hz
        · exact h
      rw [siteCanonicalVector, if_neg hz, if_neg hx, h1, h2, h3, hx1, hz1]
      exact zmod2_add_self _

/-- The local canonicalization map preserves both binary coordinates at every other site. -/
theorem siteCanonicalVector_local {n : ℕ} (j : Fin n) (v : BooleanVec n × BooleanVec n)
    (k : Fin n) (hk : k ≠ j) :
    (siteCanonicalVector j v).1 k = v.1 k ∧ (siteCanonicalVector j v).2 k = v.2 k := by
  by_cases hz : v.2 j = 0
  · by_cases hx : v.1 j = 0
    · simp [siteCanonicalVector, hz, hx, cliffordSymplecticMap, hk]
    · simp [siteCanonicalVector, hz, hx, cliffordSymplecticMap, hk]
  · by_cases hx : v.1 j = 0
    · simp [siteCanonicalVector, hz, hx, cliffordSymplecticMap, hk]
    · simp [siteCanonicalVector, hz, hx, cliffordSymplecticMap, hk]

/-- The binary action of `siteCanonicalGates` agrees with `siteCanonicalVector`. -/
theorem siteCanonicalGates_eq {n : ℕ} (j : Fin n) (v : BooleanVec n × BooleanVec n) :
    cliffordSymplecticCircuit (siteCanonicalGates j v) v = siteCanonicalVector j v := by
  by_cases hz : v.2 j = 0
  · by_cases hx : v.1 j = 0
    · simp [siteCanonicalGates, siteCanonicalVector, hz, hx, cliffordSymplecticCircuit]
    · simp [siteCanonicalGates, siteCanonicalVector, hz, hx, cliffordSymplecticCircuit]
  · by_cases hx : v.1 j = 0
    · simp [siteCanonicalGates, siteCanonicalVector, hz, hx, cliffordSymplecticCircuit]
    · simp [siteCanonicalGates, siteCanonicalVector, hz, hx, cliffordSymplecticCircuit]

/-- Canonicalization at distinct listed sites clears their Z coordinates and preserves both
coordinates outside the list. -/
theorem canonicalCircuit_effect {n : ℕ} (sites : List (Fin n))
    (v : BooleanVec n × BooleanVec n) (hnd : sites.Nodup) :
    (∀ j ∈ sites, (cliffordSymplecticCircuit (canonicalCircuit sites v) v).2 j = 0)
      ∧ (∀ j, j ∉ sites →
        (cliffordSymplecticCircuit (canonicalCircuit sites v) v).1 j = v.1 j
          ∧ (cliffordSymplecticCircuit (canonicalCircuit sites v) v).2 j = v.2 j) := by
  induction sites generalizing v with
  | nil =>
      simp only [canonicalCircuit, cliffordSymplecticCircuit]
      constructor
      · intro j hj
        simp at hj
      · intro j hj
        simp
  | cons j js ih =>
      have hnd' : js.Nodup := hnd.tail
      have hj : j ∉ js := (List.nodup_cons.mp hnd).1
      have hsite : cliffordSymplecticCircuit (siteCanonicalGates j v) v
          = siteCanonicalVector j v := siteCanonicalGates_eq j v
      have hloc : ∀ k, k ≠ j →
          (siteCanonicalVector j v).1 k = v.1 k ∧ (siteCanonicalVector j v).2 k = v.2 k :=
        fun k hk => siteCanonicalVector_local j v k hk
      rw [show canonicalCircuit (j :: js) v
          = siteCanonicalGates j v ++ canonicalCircuit js (siteCanonicalVector j v) by rfl]
      rw [cliffordSymplecticCircuit_append, hsite]
      have hih := ih (siteCanonicalVector j v) hnd'
      refine ⟨?_, ?_⟩
      · intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · have hpres := (hih.2 k hj).2
          rw [hpres]
          exact siteCanonicalVector_z_zero k v
        · exact (hih.1 k hk)
      · intro k hk
        have hkj : k ≠ j := by
          intro hcon
          exact hk (by simp [hcon])
        rcases hloc k hkj with ⟨h1, h2⟩
        have hk' : k ∉ js := by
          intro hcon
          exact hk (by simp [hcon])
        have hpres := hih.2 k hk'
        rw [hpres.1, hpres.2]
        exact ⟨h1, h2⟩

/-- The X-coordinate update for CNOT preserves the control coordinate and adds it to the target
coordinate. -/
theorem cliffordSymplecticMap_CNOT_x {n : ℕ} (c t : Fin n) (x z : BooleanVec n) (j : Fin n) :
    (cliffordSymplecticMap (.CNOT c t) (x, z)).1 j
      = if j = c then x j else if j = t then x j + x c else x j := by
  by_cases h1 : j = c
  · simp [cliffordSymplecticMap, h1]
  · by_cases h2 : j = t
    · simp [cliffordSymplecticMap, h2]
    · simp [cliffordSymplecticMap, h2]

/-- The Z-coordinate update for CNOT adds the target coordinate to the control coordinate and
preserves the target coordinate. -/
theorem cliffordSymplecticMap_CNOT_z {n : ℕ} (c t : Fin n) (x z : BooleanVec n) (j : Fin n) :
    (cliffordSymplecticMap (.CNOT c t) (x, z)).2 j
      = if j = c then z j + z t else if j = t then z j else z j := by
  by_cases h1 : j = c
  · simp [cliffordSymplecticMap, h1]
  · by_cases h2 : j = t
    · simp [cliffordSymplecticMap, h2]
    · simp [cliffordSymplecticMap, h2]

/-- For zero Z coordinates, CNOTs from a control outside a duplicate-free target list add its X
coordinate exactly at those targets. -/
theorem cnotCircuit_effect {n : ℕ} (c : Fin n) (ts : List (Fin n))
    (hnd : ts.Nodup) (hc : c ∉ ts) :
    ∀ (x z : BooleanVec n), (∀ j, z j = 0) →
      cliffordSymplecticCircuit (ts.map (fun t => CliffordGate.CNOT c t)) (x, z)
        = ((fun j => if j ∈ ts then x j + x c else x j), z) := by
  induction ts with
  | nil =>
      intro x z hz
      simp [cliffordSymplecticCircuit]
  | cons t ts ih =>
      intro x z hz
      have hnd' : ts.Nodup := hnd.tail
      have ht : t ∉ ts := (List.nodup_cons.mp hnd).1
      have htc : t ≠ c := by
        intro hcon
        exact hc (by simp [hcon])
      have hct : c ≠ t := Ne.symm htc
      have hc' : c ∉ ts := fun hcon => hc (List.mem_cons_of_mem _ hcon)
      have hzt : (cliffordSymplecticMap (.CNOT c t) (x, z)).2 = z := by
        funext j
        rw [cliffordSymplecticMap_CNOT_z]
        by_cases h1 : j = c
        · simp [h1, hz]
        · by_cases h2 : j = t
          · simp [h2, hz]
          · simp [hz]
      have hxt : (cliffordSymplecticMap (.CNOT c t) (x, z)).1
          = (fun j => if j = t then x j + x c else x j) := by
        funext j
        rw [cliffordSymplecticMap_CNOT_x]
        by_cases h2 : j = t
        · simp [h2, htc]
        · simp [h2]
      rw [show List.map (fun t' => CliffordGate.CNOT c t') (t :: ts)
          = CliffordGate.CNOT c t :: List.map (fun t' => CliffordGate.CNOT c t') ts by rfl]
      rw [cliffordSymplecticCircuit]
      change cliffordSymplecticCircuit (List.map (fun t' => CliffordGate.CNOT c t') ts)
        (cliffordSymplecticMap (CliffordGate.CNOT c t) (x, z)) = _
      have hmap : cliffordSymplecticMap (.CNOT c t) (x, z)
          = ((fun j => if j = t then x j + x c else x j), z) := by
        apply Prod.ext
        · exact hxt
        · exact hzt
      rw [hmap]
      rw [ih hnd' hc' _ _ hz]
      congr 1
      funext j
      by_cases hjt : j = t
      · subst hjt
        simp [ht]
      · by_cases hjin : j ∈ ts
        · simp [hjin, hjt, hct]
        · simp [hjin, hjt]

/-- The list underlying `supportTail` has no duplicates and excludes the distinguished index. -/
theorem supportTail_toList {n : ℕ} (zero : Fin n) (x : BooleanVec n) :
    (supportTail zero x).toList.Nodup ∧ zero ∉ (supportTail zero x).toList := by
  constructor
  · exact Finset.nodup_toList _
  · simp [supportTail]

/-- Membership in `supportTail zero x` means being distinct from `zero` and having a nonzero X
coordinate. -/
theorem mem_supportTail {n : ℕ} (zero : Fin n) (x : BooleanVec n) (j : Fin n) :
    j ∈ supportTail zero x ↔ j ≠ zero ∧ x j ≠ 0 := by
  simp [supportTail]

/-- On a vector with zero Z coordinates, `cnotFixCircuit` adds `x i` at the distinguished site
exactly when its X coordinate is zero. -/
theorem cnotFixCircuit_effect {n : ℕ} (zero i : Fin n) (x : BooleanVec n)
    (hzi : i ≠ zero) :
    cliffordSymplecticCircuit (cnotFixCircuit zero i x) (x, 0)
      = ((fun j => if x zero = 0 ∧ j = zero then x zero + x i else x j), 0) := by
  by_cases hz : x zero = 0
  · have hzi' : zero ≠ i := Ne.symm hzi
    simp only [cnotFixCircuit, if_pos hz, cliffordSymplecticCircuit]
    apply Prod.ext
    · funext j
      show (cliffordSymplecticMap (CliffordGate.CNOT i zero) (x, 0)).1 j = _
      rw [cliffordSymplecticMap_CNOT_x]
      by_cases h1 : j = i
      · simp [h1, hzi, hz]
      · by_cases h2 : j = zero
        · simp [h2, hz, hzi']
        · simp [h2]
    · funext j
      show (cliffordSymplecticMap (CliffordGate.CNOT i zero) (x, 0)).2 j = _
      rw [cliffordSymplecticMap_CNOT_z]
      by_cases h1 : j = i
      · simp [h1]
      · by_cases h2 : j = zero
        · simp [h2]
        · simp [h2]
  · simp [cnotFixCircuit, hz, cliffordSymplecticCircuit]

/-- Local canonicalization makes the selected X coordinate zero for a zero coordinate pair and
one otherwise. -/
theorem siteCanonicalVector_x {n : ℕ} (j : Fin n) (v : BooleanVec n × BooleanVec n) :
    (siteCanonicalVector j v).1 j = if v.1 j = 0 ∧ v.2 j = 0 then 0 else 1 := by
  by_cases hz : v.2 j = 0
  · by_cases hx : v.1 j = 0
    · have h1 : (cliffordSymplecticMap (.S j) v).1 j = v.1 j := by
        simp [cliffordSymplecticMap]
      rw [siteCanonicalVector, if_pos hz, if_pos hx, h1]
      simp [hz, hx]
    · have h1 : (cliffordSymplecticMap (.S j) (cliffordSymplecticMap (.S j) v)).1 j
          = (cliffordSymplecticMap (.S j) v).1 j := by
        simp [cliffordSymplecticMap]
      have h2 : (cliffordSymplecticMap (.S j) v).1 j = v.1 j := by
        simp [cliffordSymplecticMap]
      rw [siteCanonicalVector, if_pos hz, if_neg hx, h1, h2]
      have hx1 : v.1 j = 1 := by
        rcases zmod2_eq_zero_or_one (v.1 j) with h | h
        · exact absurd h hx
        · exact h
      rw [hx1]
      simp [hz, hx]
  · by_cases hx : v.1 j = 0
    · have h1 : (cliffordSymplecticMap (.H j) v).1 j = v.2 j := by
        simp [cliffordSymplecticMap]
      rw [siteCanonicalVector, if_neg hz, if_pos hx, h1]
      have hz1 : v.2 j = 1 := by
        rcases zmod2_eq_zero_or_one (v.2 j) with h | h
        · exact absurd h hz
        · exact h
      rw [hz1]
      simp [hz, hx]
    · have h1 : (cliffordSymplecticMap (.S j) (cliffordSymplecticMap (.H j) v)).1 j
          = (cliffordSymplecticMap (.H j) v).1 j := by
        simp [cliffordSymplecticMap]
      have h2 : (cliffordSymplecticMap (.H j) v).1 j = v.2 j := by
        simp [cliffordSymplecticMap]
      rw [siteCanonicalVector, if_neg hz, if_neg hx, h1, h2]
      have hz1 : v.2 j = 1 := by
        rcases zmod2_eq_zero_or_one (v.2 j) with h | h
        · exact absurd h hz
        · exact h
      rw [hz1]
      simp [hz, hx]

/-- After canonicalization at distinct listed sites, each processed X coordinate indicates
whether its original coordinate pair was nonzero. -/
theorem canonicalCircuit_x_processed {n : ℕ} (sites : List (Fin n))
    (v : BooleanVec n × BooleanVec n) (hnd : sites.Nodup) (j : Fin n) (hj : j ∈ sites) :
    (cliffordSymplecticCircuit (canonicalCircuit sites v) v).1 j
      = if v.1 j = 0 ∧ v.2 j = 0 then 0 else 1 := by
  induction sites generalizing v with
  | nil => simp at hj
  | cons a as ih =>
      have hnd' : as.Nodup := hnd.tail
      have ha : a ∉ as := (List.nodup_cons.mp hnd).1
      rw [show canonicalCircuit (a :: as) v
          = siteCanonicalGates a v ++ canonicalCircuit as (siteCanonicalVector a v) from rfl]
      rw [cliffordSymplecticCircuit_append, siteCanonicalGates_eq a v]
      rcases List.mem_cons.mp hj with hjeq | hj'
      · have h1 := canonicalCircuit_effect as (siteCanonicalVector a v) hnd'
        have h2 := h1.2 a ha
        rw [hjeq, h2.1]
        exact siteCanonicalVector_x a v
      · have hja : j ≠ a := by
          intro hcon
          exact ha (hcon ▸ hj')
        have h1 := ih (siteCanonicalVector a v) hnd' hj'
        have hloc := siteCanonicalVector_local a v j hja
        rw [h1, hloc.1, hloc.2]

/-- If `x i = 1`, the displayed update makes the distinguished X coordinate one. -/
theorem cnotFix_x_zero {n : ℕ} (zero i : Fin n) (x : BooleanVec n) (_hzi : i ≠ zero)
    (hxi : x i = 1) :
    (if x zero = 0 ∧ zero = zero then x zero + x i else x zero) = 1 := by
  by_cases hz : x zero = 0
  · simp only [eq_self, and_true, if_pos hz]
    rw [hz, hxi]
    simp
  · have h1 : x zero = 1 := by
      rcases zmod2_eq_zero_or_one (x zero) with h | h
      · exact absurd h hz
      · exact h
    simp only [eq_self, and_true, if_neg hz]
    exact h1

/-- If `x i = 1`, the displayed update sets the distinguished X coordinate to one and preserves
the others. -/
theorem cnotFix_x_apply {n : ℕ} (zero i : Fin n) (x : BooleanVec n) (_hzi : i ≠ zero)
    (hxi : x i = 1) (j : Fin n) :
    (if x zero = 0 ∧ j = zero then x zero + x i else x j) = if j = zero then 1 else x j := by
  by_cases hjz : j = zero
  · rw [hjz]
    have h2 := cnotFix_x_zero zero i x _hzi hxi
    rw [h2]
    simp
  · have hne : ¬ (x zero = 0 ∧ j = zero) := by
      rintro ⟨_, h2⟩
      exact hjz h2
    rw [if_neg hne, if_neg hjz]

/-- At a processed site, the canonicalized X coordinate vanishes exactly when both original
binary coordinates vanish. -/
theorem canonicalCircuit_x_zero_iff {n : ℕ} (sites : List (Fin n))
    (v : BooleanVec n × BooleanVec n) (hnd : sites.Nodup) (j : Fin n) (hj : j ∈ sites) :
    (cliffordSymplecticCircuit (canonicalCircuit sites v) v).1 j = 0
      ↔ (v.1 j = 0 ∧ v.2 j = 0) := by
  have h1 := canonicalCircuit_x_processed sites v hnd j hj
  constructor
  · intro h
    by_cases hc : v.1 j = 0 ∧ v.2 j = 0
    · exact hc
    · have h2 : (1 : ZMod 2) = 0 := by
        have h3 : (0 : ZMod 2)
            = (if v.1 j = 0 ∧ v.2 j = 0 then (0 : ZMod 2) else 1) := by
          rw [← h1]
          exact h.symm
        rw [h3]
        simp [hc]
      exact absurd h2 (by decide)
  · rintro ⟨h2, h3⟩
    rw [canonicalCircuit_x_processed sites v hnd j hj]
    simp [h2, h3]

/-- If `i` differs from the distinguished site and `x i = 1`, the reduction circuit maps `(x,
0)` to the X unit vector at the distinguished site. -/
theorem cnotReduceCircuit_effect {n : ℕ} (zero i : Fin n) (x : BooleanVec n)
    (hzi : i ≠ zero) (hxi : x i = 1) :
    cliffordSymplecticCircuit (cnotReduceCircuit zero i x) (x, 0)
      = ((fun j => if j = zero then 1 else 0), 0) := by
  obtain ⟨hnd, hnotzero⟩ := supportTail_toList zero x
  rw [cnotReduceCircuit, cliffordSymplecticCircuit_append]
  rw [cnotFixCircuit_effect zero i x hzi]
  have hclear := cnotCircuit_effect zero (supportTail zero x).toList hnd hnotzero
  rw [show cnotClearCircuit zero x
        = (supportTail zero x).toList.map (fun j => CliffordGate.CNOT zero j) from rfl]
  rw [hclear (fun j => if x zero = 0 ∧ j = zero then x zero + x i else x j) 0
    (fun j => rfl)]
  refine Prod.ext ?_ rfl
  show (fun j => if j ∈ (supportTail zero x).toList then
        (if x zero = 0 ∧ j = zero then x zero + x i else x j)
          + (if x zero = 0 ∧ zero = zero then x zero + x i else x zero)
      else (if x zero = 0 ∧ j = zero then x zero + x i else x j))
      = (fun j => if j = zero then 1 else 0)
  funext j
  by_cases hjz : j = zero
  · rw [hjz]
    rw [if_neg hnotzero]
    have h2 := cnotFix_x_zero zero i x hzi hxi
    rw [h2]
    simp
  · by_cases hmem : j ∈ (supportTail zero x).toList
    · rw [if_pos hmem]
      rw [cnotFix_x_apply zero i x hzi hxi j]
      rw [cnotFix_x_zero zero i x hzi hxi]
      have hne : x j ≠ 0 :=
        (mem_supportTail zero x j).mp (Finset.mem_toList.mp hmem) |>.2
      have hxj : x j = 1 := by
        rcases zmod2_eq_zero_or_one (x j) with h | h
        · exact absurd h hne
        · exact h
      rw [hxj]
      simp [hjz, zmod2_add_self]
    · rw [if_neg hmem]
      rw [cnotFix_x_apply zero i x hzi hxi j]
      have hne : x j = 0 := by
        have h1 : ¬ (j ∈ supportTail zero x) := by
          intro hcon
          exact hmem (Finset.mem_toList.mpr hcon)
        have h2 := (mem_supportTail zero x j).not.mp h1
        by_cases hj0 : j ≠ zero
        · by_contra hc
          exact h2 ⟨hj0, hc⟩
        · exact (hj0 hjz).elim
      rw [hne]

/-- Applying the binary Hadamard map twice is the identity. -/
theorem cliffordSymplecticMap_H_inv {n : ℕ} (i : Fin n)
    (v : BooleanVec n × BooleanVec n) :
    cliffordSymplecticMap (.H i) (cliffordSymplecticMap (.H i) v) = v := by
  rcases v with ⟨x, z⟩
  apply Prod.ext
  · funext j
    simp only [cliffordSymplecticMap]
    by_cases h1 : j = i
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]
  · funext j
    simp only [cliffordSymplecticMap]
    by_cases h1 : j = i
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]

/-- Applying the binary phase-gate map twice is the identity. -/
theorem cliffordSymplecticMap_S_inv {n : ℕ} (i : Fin n)
    (v : BooleanVec n × BooleanVec n) :
    cliffordSymplecticMap (.S i) (cliffordSymplecticMap (.S i) v) = v := by
  rcases v with ⟨x, z⟩
  apply Prod.ext
  · funext j
    simp only [cliffordSymplecticMap]
  · funext j
    simp only [cliffordSymplecticMap]
    by_cases h1 : j = i
    · rw [if_pos h1, if_pos h1]
      have hxi : x j + x j = 0 := zmod2_add_self _
      calc (z j + x j) + x j = z j + (x j + x j) := by abel
        _ = z j + 0 := by rw [hxi]
        _ = z j := by simp
    · rw [if_neg h1, if_neg h1]

/-- Applying a CNOT binary map with distinct control and target twice is the identity. -/
theorem cliffordSymplecticMap_CNOT_inv {n : ℕ} (c t : Fin n) (hct : c ≠ t)
    (x z : BooleanVec n) :
    cliffordSymplecticMap (.CNOT c t) (cliffordSymplecticMap (.CNOT c t) (x, z)) = (x, z) := by
  have hxc : x c + x c = 0 := zmod2_add_self _
  have hzt : z t + z t = 0 := zmod2_add_self _
  have hct' : t ≠ c := Ne.symm hct
  apply Prod.ext
  · funext k
    simp only [cliffordSymplecticMap]
    by_cases h1 : k = c
    · rw [if_pos h1, if_pos h1]
    · by_cases h2 : k = t
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, if_true]
        calc (x k + x c) + x c = x k + (x c + x c) := by abel
          _ = x k + 0 := by rw [hxc]
          _ = x k := by simp
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
  · funext k
    simp only [cliffordSymplecticMap]
    by_cases h1 : k = c
    · rw [if_pos h1, if_pos h1]
      rw [if_neg hct', if_true]
      calc (z k + z t) + z t = z k + (z t + z t) := by abel
        _ = z k + 0 := by rw [hzt]
        _ = z k := by simp
    · by_cases h2 : k = t
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]

/-- Every legal Clifford gate has an involutive binary symplectic map. -/
theorem cliffordSymplecticMap_inv {n : ℕ} (g : CliffordGate n) (hg : legalGate g)
    (v : BooleanVec n × BooleanVec n) :
    cliffordSymplecticMap g (cliffordSymplecticMap g v) = v := by
  cases g with
  | H i => exact cliffordSymplecticMap_H_inv i v
  | S i => exact cliffordSymplecticMap_S_inv i v
  | CNOT i j =>
      have h : i ≠ j := by simpa [legalGate] using! hg
      rcases v with ⟨x, z⟩
      exact cliffordSymplecticMap_CNOT_inv i j h x z

/-- Reversing a legal Clifford circuit gives the inverse of its binary symplectic action. -/
theorem cliffordSymplecticCircuit_inv {n : ℕ} (gs : CliffordCircuit n)
    (hg : ∀ g ∈ gs, legalGate g) (v : BooleanVec n × BooleanVec n) :
    cliffordSymplecticCircuit gs.reverse (cliffordSymplecticCircuit gs v) = v := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
      have hg1 : legalGate g := hg g (by simp)
      have hg2 : ∀ g' ∈ gs, legalGate g' := fun g' h => hg g' (by simp [h])
      rw [List.reverse_cons, cliffordSymplecticCircuit_append]
      simp only [cliffordSymplecticCircuit]
      rw [ih hg2 (cliffordSymplecticMap g v)]
      exact cliffordSymplecticMap_inv g hg1 v

/-- Every gate in `siteCanonicalGates` is legal. -/
theorem legal_siteCanonicalGates {n : ℕ} (j : Fin n) (v : BooleanVec n × BooleanVec n) :
    ∀ g ∈ siteCanonicalGates j v, legalGate g := by
  intro g hg
  have hg' : g = .H j ∨ g = .S j := by
    by_cases hz : v.2 j = 0
    · by_cases hx : v.1 j = 0
      · have h1 : siteCanonicalGates j v = [.S j] := by simp [siteCanonicalGates, hz, hx]
        rw [h1] at hg
        simp at hg
        exact Or.inr hg
      · have h1 : siteCanonicalGates j v = [.S j, .S j] := by
          simp [siteCanonicalGates, hz, hx]
        rw [h1] at hg
        simp at hg
        exact Or.inr hg
    · by_cases hx : v.1 j = 0
      · have h1 : siteCanonicalGates j v = [.H j] := by simp [siteCanonicalGates, hz, hx]
        rw [h1] at hg
        simp at hg
        exact Or.inl hg
      · have h1 : siteCanonicalGates j v = [.H j, .S j] := by
          simp [siteCanonicalGates, hz, hx]
        rw [h1] at hg
        simp at hg
        rcases hg with hg1 | hg2
        · exact Or.inl hg1
        · exact Or.inr hg2
  rcases hg' with hg1 | hg2
  · rw [hg1]
    trivial
  · rw [hg2]
    trivial

/-- Every gate in `canonicalCircuit` is legal. -/
theorem legal_canonicalCircuit {n : ℕ} (sites : List (Fin n))
    (v : BooleanVec n × BooleanVec n) :
    ∀ g ∈ canonicalCircuit sites v, legalGate g := by
  induction sites generalizing v with
  | nil =>
      intro g hg
      simp [canonicalCircuit] at hg
  | cons a as ih =>
      rw [show canonicalCircuit (a :: as) v
          = siteCanonicalGates a v ++ canonicalCircuit as (siteCanonicalVector a v) from rfl]
      intro g hg
      rw [List.mem_append] at hg
      rcases hg with hg | hg
      · exact legal_siteCanonicalGates a v g hg
      · exact ih (siteCanonicalVector a v) g hg

/-- The fixing circuit uses legal gates when its source and distinguished site are distinct. -/
theorem legal_cnotFixCircuit {n : ℕ} (zero i : Fin n) (x : BooleanVec n) (hzi : i ≠ zero) :
    ∀ g ∈ cnotFixCircuit zero i x, legalGate g := by
  by_cases hz : x zero = 0
  · simp only [cnotFixCircuit, if_pos hz]
    intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    simp [legalGate, hzi]
  · simp only [cnotFixCircuit, if_neg hz]
    intro g hg
    simp at hg

/-- Every gate in `cnotClearCircuit` is legal. -/
theorem legal_cnotClearCircuit {n : ℕ} (zero : Fin n) (x : BooleanVec n) :
    ∀ g ∈ cnotClearCircuit zero x, legalGate g := by
  intro g hg
  rw [show cnotClearCircuit zero x
        = (supportTail zero x).toList.map (fun j => CliffordGate.CNOT zero j) from rfl] at hg
  rw [List.mem_map] at hg
  obtain ⟨j, hj, heq⟩ := hg
  have hj0 : j ≠ zero := (mem_supportTail zero x j).mp (Finset.mem_toList.mp hj) |>.1
  rw [← heq]
  simp only [legalGate]
  exact fun h => hj0 h.symm

/-- The reduction circuit uses legal gates when its selected index differs from the
distinguished site. -/
theorem legal_cnotReduceCircuit {n : ℕ} (zero i : Fin n) (x : BooleanVec n) (hzi : i ≠ zero) :
    ∀ g ∈ cnotReduceCircuit zero i x, legalGate g := by
  rw [cnotReduceCircuit]
  intro g hg
  rw [List.mem_append] at hg
  rcases hg with hg | hg
  · exact legal_cnotFixCircuit zero i x hzi g hg
  · exact legal_cnotClearCircuit zero x g hg

/-- Every nonzero binary symplectic vector can be mapped to the X unit vector at a specified
site by a legal Clifford circuit. -/
theorem pauliDirection_to_unit {n : ℕ} (zero : Fin n)
    (v : BooleanVec n × BooleanVec n) (hv : v ≠ 0) :
    ∃ (gs : CliffordCircuit n),
      (∀ g ∈ gs, legalGate g) ∧
        cliffordSymplecticCircuit gs v = ((fun j => if j = zero then 1 else 0), 0) := by
  set sites : List (Fin n) := (Finset.univ : Finset (Fin n)).toList with hsites
  have hnd : sites.Nodup := Finset.nodup_toList _
  set res : BooleanVec n × BooleanVec n :=
    cliffordSymplecticCircuit (canonicalCircuit sites v) v with hres
  have hmem : ∀ j : Fin n, j ∈ sites := by
    intro j
    simp [hsites]
  have hz0 : ∀ j : Fin n, res.2 j = 0 := by
    intro j
    have h1 := (canonicalCircuit_effect sites v hnd).1 j (hmem j)
    rw [← hres] at h1
    exact h1
  have hxne : res.1 ≠ 0 := by
    intro h
    have hzero : ∀ j : Fin n, res.1 j = 0 := by
      intro j
      rw [h]
      rfl
    apply hv
    apply Prod.ext
    · funext j
      have h1 := canonicalCircuit_x_zero_iff sites v hnd j (hmem j)
      rw [← hres] at h1
      have h2 := h1.mp (by rw [hzero j])
      exact h2.1
    · funext j
      have h1 := canonicalCircuit_x_zero_iff sites v hnd j (hmem j)
      rw [← hres] at h1
      have h2 := h1.mp (by rw [hzero j])
      exact h2.2
  by_cases hunit : ∀ j : Fin n, res.1 j = if j = zero then 1 else 0
  · refine ⟨canonicalCircuit sites v, ?_⟩
    refine ⟨legal_canonicalCircuit sites v, ?_⟩
    rw [← hres]
    apply Prod.ext
    · funext j
      exact hunit j
    · funext j
      exact hz0 j
  · have hex : ∃ i : Fin n, i ≠ zero ∧ res.1 i = 1 := by
      by_cases hz0v : res.1 zero = 0
      · have hex0 : ∃ i : Fin n, res.1 i ≠ 0 := by
          by_contra hc
          apply hxne
          funext j
          have h1 : res.1 j = 0 := by
            by_contra hc2
            exact hc ⟨j, hc2⟩
          exact h1
        obtain ⟨i, hi⟩ := hex0
        have hi1 : res.1 i = 1 := by
          rcases zmod2_eq_zero_or_one (res.1 i) with h | h
          · exact absurd h hi
          · exact h
        refine ⟨i, ?_, hi1⟩
        intro hcon
        subst hcon
        exact absurd (hi1.symm.trans hz0v) (by decide)
      · have hex0 : ∃ j : Fin n, j ≠ zero ∧ res.1 j ≠ 0 := by
          by_contra hc
          apply hunit
          intro j
          by_cases hjz : j = zero
          · have hz1 : res.1 zero = 1 := by
              rcases zmod2_eq_zero_or_one (res.1 zero) with h | h
              · exact absurd h hz0v
              · exact h
            simp [hjz, hz1]
          · have h1 : res.1 j = 0 := by
              by_contra hc2
              exact hc ⟨j, hjz, hc2⟩
            simp [hjz, h1]
        obtain ⟨j, hj0, hjne⟩ := hex0
        have hj1 : res.1 j = 1 := by
          rcases zmod2_eq_zero_or_one (res.1 j) with h | h
          · exact absurd h hjne
          · exact h
        exact ⟨j, hj0, hj1⟩
    obtain ⟨i, hi0, hi1⟩ := hex
    refine ⟨canonicalCircuit sites v ++ cnotReduceCircuit zero i res.1, ?_⟩
    refine ⟨?_, ?_⟩
    · intro g hg
      rw [List.mem_append] at hg
      rcases hg with hg | hg
      · exact legal_canonicalCircuit sites v g hg
      · exact legal_cnotReduceCircuit zero i res.1 hi0 g hg
    · rw [cliffordSymplecticCircuit_append]
      rw [← hres]
      have hres' : res = (res.1, 0) := by
        apply Prod.ext
        · rfl
        · funext j
          exact hz0 j
      rw [hres']
      exact cnotReduceCircuit_effect zero i res.1 hi0 hi1

/-- Any two nonzero binary symplectic vectors are connected by a Clifford circuit when a
register site is specified. -/
theorem pauliDirection_orbit_transitive {n : ℕ} (zero : Fin n)
    (v w : BooleanVec n × BooleanVec n) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ (gs : CliffordCircuit n), cliffordSymplecticCircuit gs v = w := by
  obtain ⟨g1, h1⟩ := pauliDirection_to_unit zero v hv
  obtain ⟨g2, h2⟩ := pauliDirection_to_unit zero w hw
  refine ⟨g1 ++ g2.reverse, ?_⟩
  rw [cliffordSymplecticCircuit_append, h1.2]
  have hinv := cliffordSymplecticCircuit_inv g2 h2.1 w
  rw [h2.2] at hinv
  exact hinv

/-- The indicator of a singleton binary vector is a stabilizer function. -/
theorem isStabilizerFun_delta {n : ℕ} (p : BooleanVec n) :
    IsStabilizerFun (fun x => if x = p then (1 : ℂ) else 0) := by
  refine ⟨0, 0, 0, 0, affineSpan (ZMod 2) ({p} : Set (BooleanVec n)), ?_⟩
  ext x
  simp [booleanDot, quadFun, AffineSubspace.mem_affineSpan_singleton]

/-- The set of numbers of terms in finite complex linear decompositions of a function into
stabilizer functions. -/
def stabilizerRankSet {n : ℕ} (F : BooleanVec n → ℂ) : Set ℕ :=
  {r | ∃ (c : Fin r → ℂ) (ψ : Fin r → BooleanVec n → ℂ),
    (∀ j, IsStabilizerFun (ψ j)) ∧ F = fun x => ∑ j, c j * ψ j x}

/-- The stabilizer rank is the infimum of the set of stabilizer-decomposition lengths. -/
theorem stabilizerRank_eq_sInf_set {n : ℕ} (F : BooleanVec n → ℂ) :
    stabilizerRank F = sInf (stabilizerRankSet F) := by
  rfl

/-- Every function on the binary cube possesses a finite decomposition into stabilizer
functions. -/
theorem stabilizerRankSet_nonempty {n : ℕ} (F : BooleanVec n → ℂ) :
    (stabilizerRankSet F).Nonempty := by
  let e : Fin (Fintype.card (BooleanVec n)) ≃ BooleanVec n := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (BooleanVec n), ?_⟩
  refine ⟨fun j => F (e j), fun j x => if x = e j then (1 : ℂ) else 0, fun j => ?_, ?_⟩
  · exact isStabilizerFun_delta (e j)
  · ext x
    symm
    rw [Finset.sum_eq_single (e.symm x)]
    · simp
    · intro j _ hj
      have hn : x ≠ e j := by
        intro he
        apply hj
        apply e.injective
        simpa using! he.symm
      simp [hn]
    · simp

/-- Multiplication by a nonzero complex scalar preserves stabilizer rank. -/
theorem stabilizerRank_smul {n : ℕ} (φ : BooleanVec n → ℂ) (lam : ℂ) (hlam : lam ≠ 0) :
    stabilizerRank (fun x => lam * φ x) = stabilizerRank φ := by
  have hmemF : ∃ (c : Fin (stabilizerRank φ) → ℂ)
      (ψ : Fin (stabilizerRank φ) → BooleanVec n → ℂ),
      (∀ j, IsStabilizerFun (ψ j)) ∧ φ = fun x => ∑ j, c j * ψ j x := by
    have h2 : stabilizerRank φ ∈ stabilizerRankSet φ := by
      rw [stabilizerRank_eq_sInf_set]
      exact Nat.sInf_mem (stabilizerRankSet_nonempty φ)
    simpa only [stabilizerRankSet, Set.mem_setOf_eq] using! h2
  have hmemL : ∃ (c : Fin (stabilizerRank (fun x => lam * φ x)) → ℂ)
      (ψ : Fin (stabilizerRank (fun x => lam * φ x)) → BooleanVec n → ℂ),
      (∀ j, IsStabilizerFun (ψ j))
        ∧ (fun x => lam * φ x) = fun x => ∑ j, c j * ψ j x := by
    have h2 : stabilizerRank (fun x => lam * φ x)
        ∈ stabilizerRankSet (fun x => lam * φ x) := by
      rw [stabilizerRank_eq_sInf_set]
      exact Nat.sInf_mem (stabilizerRankSet_nonempty (fun x => lam * φ x))
    simpa only [stabilizerRankSet, Set.mem_setOf_eq] using! h2
  have hle : stabilizerRank (fun x => lam * φ x) ≤ stabilizerRank φ := by
    have hset : stabilizerRank φ ∈ stabilizerRankSet (fun x => lam * φ x) := by
      obtain ⟨coeff, ψ, hψ, hrep⟩ := hmemF
      refine ⟨fun j => lam * coeff j, ψ, hψ, ?_⟩
      ext x
      calc lam * φ x = lam * (∑ j, coeff j * ψ j x) := by rw [congrFun hrep x]
        _ = ∑ j, (lam * coeff j) * ψ j x := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
    rw [stabilizerRank_eq_sInf_set]
    exact Nat.sInf_le hset
  have hge : stabilizerRank φ ≤ stabilizerRank (fun x => lam * φ x) := by
    have hset : stabilizerRank (fun x => lam * φ x) ∈ stabilizerRankSet φ := by
      obtain ⟨coeff, ψ, hψ, hrep⟩ := hmemL
      refine ⟨fun j => coeff j * lam⁻¹, ψ, hψ, ?_⟩
      ext x
      calc φ x = (lam⁻¹) * (lam * φ x) := by rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
        _ = (lam⁻¹) * (∑ j, coeff j * ψ j x) := by rw [congrFun hrep x]
        _ = ∑ j, (coeff j * lam⁻¹) * ψ j x := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
    rw [stabilizerRank_eq_sInf_set]
    exact Nat.sInf_le hset
  exact Nat.le_antisymm hle hge

/-- Encoding and normalizing a function with `normalizedStabilizerState` preserves its
stabilizer rank. -/
theorem stabilizerRank_normalizedStabilizerState {n : ℕ} (φ : BooleanVec n → ℂ) :
    stabilizerRank (amplitudeFn (normalizedStabilizerState φ)) = stabilizerRank φ := by
  have hrt (x : BooleanVec n) : regToVec (vecToReg x) = x := regVecEquiv.apply_symm_apply x
  have hamp : amplitudeFn (normalizedStabilizerState φ)
      = fun x => φ x * (Real.sqrt (stabilizerFunMass φ) : ℂ)⁻¹ := by
    funext x
    rw [normalizedStabilizerState, amplitudeFn, stateOfFn]
    simp only [hrt]
  by_cases hφ : φ = 0
  · rw [hamp]
    have hzero : (fun x => φ x * (Real.sqrt (stabilizerFunMass φ) : ℂ)⁻¹) = 0 := by
      funext x
      simp [hφ]
    rw [hzero]
    exact ((stabilizerRank_eq_zero (0 : BooleanVec n → ℂ)).mpr rfl).trans
      ((stabilizerRank_eq_zero φ).mpr hφ).symm
  · have hex : ∃ x, φ x ≠ 0 := by
      by_contra hc
      apply hφ
      funext x
      by_contra hx
      exact hc ⟨x, hx⟩
    obtain ⟨x, hx⟩ := hex
    have hmass : 0 < stabilizerFunMass φ := by
      have h1 : 0 < ‖φ x‖ ^ 2 := by
        have hn : 0 < ‖φ x‖ := (norm_pos_iff).mpr hx
        nlinarith
      have h2 : 0 ≤ ∑ y, ‖φ y‖ ^ 2 := Finset.sum_nonneg fun y _ => by positivity
      have h3 : 0 < ∑ y, ‖φ y‖ ^ 2 :=
        Finset.sum_pos' (fun y _ => by positivity) ⟨x, Finset.mem_univ x, h1⟩
      simpa [stabilizerFunMass] using! h3
    have hsqrt : (Real.sqrt (stabilizerFunMass φ) : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos_of_pos hmass)
    have hsqrt' : (Real.sqrt (stabilizerFunMass φ) : ℂ) ≠ 0 := by
      exact_mod_cast hsqrt
    rw [hamp]
    have h1 : (fun x => φ x * (Real.sqrt (stabilizerFunMass φ) : ℂ)⁻¹)
        = fun x => (Real.sqrt (stabilizerFunMass φ) : ℂ)⁻¹ * φ x := by
      funext x
      exact mul_comm _ _
    rw [h1]
    exact stabilizerRank_smul φ (Real.sqrt (stabilizerFunMass φ) : ℂ)⁻¹ (inv_ne_zero hsqrt')

/-- If `1 ≤ n` and `100 * r ≤ n`, rank at most `r` for the normalized state's amplitude function
forces equal amplitudes at two binary vectors of different cube weights. -/
theorem exact_rank_collision_normalizedStabilizerState {n r : ℕ} (φ : BooleanVec n → ℂ)
    (hn : 1 ≤ n) (hrn : 100 * r ≤ n)
    (hF : stabilizerRank (amplitudeFn (normalizedStabilizerState φ)) ≤ r) :
    ∃ y z : BooleanVec n, cubeWeight y ≠ cubeWeight z ∧
      amplitudeFn (normalizedStabilizerState φ) y = amplitudeFn (normalizedStabilizerState φ) z :=
  exact_rank_collision (amplitudeFn (normalizedStabilizerState φ)) hn hrn hF

/-- Tests membership in the set of masked generator products by enumerating masks of the
generator-list length. -/
def memGenerated {n : ℕ} (gs : List (PauliElem n)) (p : PauliElem n) : Bool :=
  (masksOfLen gs.length).any fun m => maskProduct gs m == p

/-- The Boolean membership test returns true exactly for elements of `generatedSubgroup gs`. -/
theorem memGenerated_eq_true_iff {n : ℕ} (gs : List (PauliElem n)) (p : PauliElem n) :
    memGenerated gs p = true ↔ p ∈ generatedSubgroup gs := by
  constructor
  · intro h
    simp only [memGenerated, List.any_eq_true] at h
    obtain ⟨m, hm, heq⟩ := h
    refine ⟨m, masksOfLen_length gs.length m hm, of_decide_eq_true heq⟩
  · intro h
    obtain ⟨m, hm, hpm⟩ := h
    have hm' : m ∈ masksOfLen gs.length := mem_masksOfLen gs.length m hm
    simp only [memGenerated, List.any_eq_true]
    exact ⟨m, hm', of_decide_eq_true (by simp [hpm])⟩

/-- The tail of a commuting Hermitian generator list is commuting and Hermitian. -/
theorem commutingHermitian_tail {n : ℕ} {g : PauliElem n} {rest : List (PauliElem n)}
    (hgs : CommutingHermitianPaulis (g :: rest)) : CommutingHermitianPaulis rest := by
  rcases hgs with ⟨h1, h2⟩
  refine ⟨fun k hk => h1 k (by simp [hk]),
    fun a ha b hb => h2 a (by simp [ha]) b (by simp [hb])⟩

/-- Replacing the tail of a commuting Hermitian list by a list drawn from that tail preserves
the commuting Hermitian property. -/
theorem commutingHermitian_cons_of_subset {n : ℕ} {g : PauliElem n}
    {h gs : List (PauliElem n)} (hgs : CommutingHermitianPaulis (g :: gs))
    (hh : ∀ k, k ∈ h → k ∈ gs) : CommutingHermitianPaulis (g :: h) := by
  rcases hgs with ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · intro k hk
    rcases List.mem_cons.mp hk with hkg | hkh
    · exact h1 k (by rw [hkg]; exact List.mem_cons_self)
    · exact h1 k (List.mem_cons_of_mem _ (hh k hkh))
  · intro a ha b hb
    rcases List.mem_cons.mp ha with hag | hah
    · rcases List.mem_cons.mp hb with hbg | hbh
      · exact h2 a (by rw [hag]; exact List.mem_cons_self)
          b (by rw [hbg]; exact List.mem_cons_self)
      · exact h2 a (by rw [hag]; exact List.mem_cons_self)
          b (List.mem_cons_of_mem _ (hh b hbh))
    · rcases List.mem_cons.mp hb with hbg | hbh
      · exact h2 a (List.mem_cons_of_mem _ (hh a hah))
          b (by rw [hbg]; exact List.mem_cons_self)
      · exact h2 a (List.mem_cons_of_mem _ (hh a hah)) b
          (List.mem_cons_of_mem _ (hh b hbh))

/-- A Boolean mask of successor length can be written as a head bit followed by a tail. -/
theorem mask_exists_cons {k : ℕ} {m : Mask} (hm : m.length = k + 1) :
    ∃ b m0, m = b :: m0 := by
  cases m with
  | nil => simp at hm
  | cons b m0 => exact ⟨b, m0, rfl⟩

/-- A generator belongs to the set generated by the list having it as head. -/
theorem self_mem_cons {n : ℕ} (g : PauliElem n) (gs : List (PauliElem n)) :
    g ∈ generatedSubgroup (g :: gs) := by
  refine ⟨true :: List.replicate gs.length false, ?_, ?_⟩
  · simp
  · show maskProduct (g :: gs) (true :: List.replicate gs.length false) = g
    rw [show maskProduct (g :: gs) (true :: List.replicate gs.length false)
        = g.mul (maskProduct gs (List.replicate gs.length false)) from rfl]
    rw [maskProduct_eq_one gs (List.replicate gs.length false) (by simp) (by simp)]
    exact pauliElem_mul_one g

/-- For commuting Hermitian generators, adding a head already generated by the tail does not
change the generated set. -/
theorem generatedSubgroup_cons_of_mem {n : ℕ} {g : PauliElem n} {rest : List (PauliElem n)}
    (hgs : CommutingHermitianPaulis (g :: rest)) (hg : g ∈ generatedSubgroup rest) :
    generatedSubgroup (g :: rest) = generatedSubgroup rest := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨m, hm, hpm⟩ := hp
    obtain ⟨b, m0, rfl⟩ := mask_exists_cons hm
    have hm0 : m0.length = rest.length := by
      have h1 := hm
      simp only [List.length_cons] at h1
      omega
    by_cases hb : b = true
    · simp only [maskProduct, if_pos hb] at hpm
      have hq : maskProduct rest m0 ∈ generatedSubgroup rest := ⟨m0, hm0, rfl⟩
      exact hpm ▸ generatedSubgroup_mul_mem rest (commutingHermitian_tail hgs) hg hq
    · simp only [maskProduct, if_neg hb] at hpm
      exact ⟨m0, hm0, hpm⟩
  · intro p hp
    obtain ⟨m, hm, hpm⟩ := hp
    have hm' : m.length = rest.length := hm
    refine ⟨false :: m, ?_, ?_⟩
    · simp [hm']
    · show maskProduct (g :: rest) (false :: m) = p
      rw [show maskProduct (g :: rest) (false :: m) = maskProduct rest m from rfl]
      exact hpm

/-- For commuting Hermitian lists with the same head, equality of the tail-generated sets
implies equality of the full generated sets. -/
theorem generatedSubgroup_cons_congr {n : ℕ} {g : PauliElem n}
    {rest gs : List (PauliElem n)} (hgs : CommutingHermitianPaulis (g :: gs))
    (hgs' : CommutingHermitianPaulis (g :: rest))
    (hconj : ∀ p, p ∈ generatedSubgroup rest ↔ p ∈ generatedSubgroup gs) :
    generatedSubgroup (g :: rest) = generatedSubgroup (g :: gs) := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨m, hm, hpm⟩ := hp
    obtain ⟨b, m0, rfl⟩ := mask_exists_cons hm
    have hm0 : m0.length = rest.length := by
      have h1 := hm
      simp only [List.length_cons] at h1
      omega
    have hq : maskProduct rest m0 ∈ generatedSubgroup rest := ⟨m0, hm0, rfl⟩
    obtain ⟨m1, hm1, hq1⟩ := (hconj _).mp hq
    by_cases hb : b = true
    · simp only [maskProduct, if_pos hb] at hpm
      have hg' : g ∈ generatedSubgroup (g :: gs) := self_mem_cons g gs
      have hmul : g.mul (maskProduct gs m1) ∈ generatedSubgroup (g :: gs) :=
        generatedSubgroup_mul_mem (g :: gs) hgs hg' ⟨false :: m1, by simp [hm1], by
          show maskProduct (g :: gs) (false :: m1) = maskProduct gs m1
          rfl⟩
      have hkey : p = g.mul (maskProduct gs m1) := by
        calc p = g.mul (maskProduct rest m0) := hpm.symm
          _ = g.mul (maskProduct gs m1) := by rw [hq1]
      exact hkey ▸ hmul
    · simp only [maskProduct, if_neg hb] at hpm
      refine ⟨false :: m1, ?_, ?_⟩
      · simp [hm1]
      · show maskProduct (g :: gs) (false :: m1) = p
        rw [show maskProduct (g :: gs) (false :: m1) = maskProduct gs m1 from rfl]
        exact hq1.trans hpm
  · intro p hp
    obtain ⟨m, hm, hpm⟩ := hp
    obtain ⟨b, m0, rfl⟩ := mask_exists_cons hm
    have hm0 : m0.length = gs.length := by
      have h1 := hm
      simp only [List.length_cons] at h1
      omega
    have hq : maskProduct gs m0 ∈ generatedSubgroup gs := ⟨m0, hm0, rfl⟩
    obtain ⟨m1, hm1, hq1⟩ := (hconj _).mpr hq
    by_cases hb : b = true
    · simp only [maskProduct, if_pos hb] at hpm
      have hg' : g ∈ generatedSubgroup (g :: rest) := self_mem_cons g rest
      have hmul : g.mul (maskProduct rest m1) ∈ generatedSubgroup (g :: rest) :=
        generatedSubgroup_mul_mem (g :: rest) hgs' hg'
          ⟨false :: m1, by simp [hm1], by
            show maskProduct (g :: rest) (false :: m1) = maskProduct rest m1
            rfl⟩
      have hkey : p = g.mul (maskProduct rest m1) := by
        calc p = g.mul (maskProduct gs m0) := hpm.symm
          _ = g.mul (maskProduct rest m1) := by rw [hq1]
      exact hkey ▸ hmul
    · simp only [maskProduct, if_neg hb] at hpm
      refine ⟨false :: m1, ?_, ?_⟩
      · simp [hm1]
      · show maskProduct (g :: rest) (false :: m1) = p
        rw [show maskProduct (g :: rest) (false :: m1) = maskProduct rest m1 from rfl]
        exact hq1.trans hpm

/-- Recursively removes a generator when it belongs to the set generated by the already reduced
tail. -/
def eliminateGenerators {n : ℕ} : List (PauliElem n) → List (PauliElem n)
  | [] => []
  | g :: gs =>
      let rest := eliminateGenerators gs
      if memGenerated rest g then rest else g :: rest

/-- Every generator retained by `eliminateGenerators` belongs to the original list. -/
theorem mem_eliminateGenerators {n : ℕ} (gs : List (PauliElem n)) (g : PauliElem n) :
    g ∈ eliminateGenerators gs → g ∈ gs := by
  induction gs with
  | nil => simp [eliminateGenerators]
  | cons a as ih =>
      simp only [eliminateGenerators]
      split
      · intro h
        exact List.mem_cons_of_mem _ (ih h)
      · intro h
        simp only [List.mem_cons] at h
        rcases h with hga | h
        · rw [hga]
          simp
        · exact List.mem_cons_of_mem _ (ih h)

/-- Eliminating redundant generators preserves the generated set for a commuting Hermitian list. -/
theorem generatedSubgroup_eliminateGenerators {n : ℕ} (gs : List (PauliElem n))
    (hgs : CommutingHermitianPaulis gs) :
    generatedSubgroup (eliminateGenerators gs) = generatedSubgroup gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      have hgs' : CommutingHermitianPaulis gs := commutingHermitian_tail hgs
      have hrest : generatedSubgroup (eliminateGenerators gs) = generatedSubgroup gs := ih hgs'
      have hconj : ∀ p, p ∈ generatedSubgroup (eliminateGenerators gs)
          ↔ p ∈ generatedSubgroup gs := fun p => by rw [hrest]
      have hcomm : CommutingHermitianPaulis (g :: eliminateGenerators gs) :=
        commutingHermitian_cons_of_subset hgs (mem_eliminateGenerators gs)
      simp only [eliminateGenerators]
      split
      · next h =>
          have hgmem : g ∈ generatedSubgroup (eliminateGenerators gs) :=
            (memGenerated_eq_true_iff _ _).mp h
          rw [← generatedSubgroup_cons_of_mem hcomm hgmem]
          rw [generatedSubgroup_cons_congr hgs hcomm hconj]
      · next h =>
          have hgnot : g ∉ generatedSubgroup (eliminateGenerators gs) := by
            intro hcon
            exact h ((memGenerated_eq_true_iff _ _).mpr hcon)
          rw [generatedSubgroup_cons_congr hgs hcomm hconj]

/-- Scaling the sum of two equal complex matrices by one half returns that matrix. -/
theorem half_smul_add {n : ℕ} (P : Matrix (Reg n) (Reg n) ℂ) :
    ((2 : ℂ)⁻¹) • (P + P) = P := by
  ext i j
  simp [Matrix.smul_apply]
  ring

/-- A list drawn from a commuting Hermitian generator list is also commuting and Hermitian. -/
theorem commutingHermitian_of_subset {n : ℕ} {gs gs' : List (PauliElem n)}
    (hgs : CommutingHermitianPaulis gs) (h : ∀ k, k ∈ gs' → k ∈ gs) :
    CommutingHermitianPaulis gs' := by
  constructor
  · intro k hk
    exact hgs.1 k (h k hk)
  · intro u hu v hv
    exact hgs.2 u (h u hu) v (h v hv)

/-- The set generated by a list is contained in the set generated after adjoining a head. -/
theorem generatedSubgroup_tail_subset {n : ℕ} (g : PauliElem n)
    (rest : List (PauliElem n)) :
    generatedSubgroup rest ⊆ generatedSubgroup (g :: rest) := by
  intro p hp
  obtain ⟨m, hm, hpm⟩ := hp
  refine ⟨false :: m, ?_, ?_⟩
  · simp [hm]
  · show maskProduct (g :: rest) (false :: m) = p
    rw [show maskProduct (g :: rest) (false :: m) = maskProduct rest m from rfl]
    exact hpm

/-- An all-false mask of the generator-list length has identity word product. -/
theorem maskWordProduct_eq_one {n : ℕ} :
    ∀ (gs : List (PauliElem n)) (m : Mask), m.length = gs.length →
      (∀ b ∈ m, b = false) → maskWordProduct gs m = 1 := by
  intro gs
  induction gs with
  | nil =>
      intro m hm h
      cases m with
      | nil => rfl
      | cons b m0 => simp at hm
  | cons g gs ih =>
      intro m hm h
      cases m with
      | nil => simp at hm
      | cons b m0 =>
          have hb : b = false := h b (by simp)
          subst hb
          have h0 : m0.length = gs.length := by simpa using! hm
          have hnone : ∀ c ∈ m0, c = false := by
            intro c hc
            exact h c (by simp [hc])
          simp only [maskWordProduct, Bool.false_eq_true, ↓reduceIte]
          exact ih m0 h0 hnone

/-- Two Hermitian Pauli elements with the same word are equal or have product negative identity. -/
theorem hermitian_eq_or_mul_minusI {n : ℕ} {p q : PauliElem n}
    (hp : IsHermitianPauli p) (hq : IsHermitianPauli q) (hw : p.word = q.word) :
    p = q ∨ p * q = minusI n := by
  by_cases hph : p.phase = q.phase
  · left
    exact pauli_ext hw hph
  · right
    have hsum : p.phase + q.phase = 2 := by
      rcases hp with hp0 | hp2 <;> rcases hq with hq0 | hq2
      · exact absurd hph (by simp [hp0, hq0])
      · simp [hp0, hq2]
      · simp [hp2, hq0]
      · exact absurd hph (by simp [hp2, hq2])
    apply pauli_ext
    · funext i
      show pauliMul1 (p.word i) (q.word i) = Pauli1.I
      rw [hw]
      exact pauliMul1_self _
    · show p.phase + q.phase + ∑ i, pauliMulPhase (p.word i) (q.word i) = 2
      rw [hsum]
      simp [pauliMulPhase_self, hw]

/-- A Pauli operator commuting with every generator commutes with the operator of every masked
product of the required length. -/
theorem op_commute_maskProduct {n : ℕ} {g : PauliElem n} :
    ∀ (rest : List (PauliElem n)), (∀ h ∈ rest, op g * op h = op h * op g) →
      ∀ (m : Mask), m.length = rest.length →
        op g * op (maskProduct rest m) = op (maskProduct rest m) * op g := by
  intro rest
  induction rest with
  | nil =>
      intro hg m hm
      cases m with
      | nil =>
          simp only [maskProduct, op_one, Matrix.one_mul, Matrix.mul_one]
      | cons b m0 => simp at hm
  | cons h rest ih =>
      intro hg m hm
      obtain ⟨b, m0, rfl⟩ := mask_exists_cons hm
      have hm0 : m0.length = rest.length := by
        simp only [List.length_cons] at hm
        omega
      have hgrest : ∀ k ∈ rest, op g * op k = op k * op g :=
        fun k hk => hg k (by simp [hk])
      have hmp : maskProduct (h :: rest) (b :: m0)
          = if b then PauliElem.mul h (maskProduct rest m0) else maskProduct rest m0 := rfl
      by_cases hb : b = true
      · rw [hmp, if_pos hb, op_mul h (maskProduct rest m0)]
        have hih := ih hgrest m0 hm0
        calc op g * (op h * op (maskProduct rest m0))
            = (op g * op h) * op (maskProduct rest m0) := by rw [Matrix.mul_assoc]
          _ = (op h * op g) * op (maskProduct rest m0) := by
              rw [hg h (List.mem_cons_self)]
          _ = op h * (op g * op (maskProduct rest m0)) := by rw [Matrix.mul_assoc]
          _ = op h * (op (maskProduct rest m0) * op g) := by rw [hih]
          _ = (op h * op (maskProduct rest m0)) * op g := by rw [Matrix.mul_assoc]
      · rw [hmp, if_neg hb]
        exact ih hgrest m0 hm0

/-- Every masked product of a commuting Hermitian generator list, with mask of the required
length, is Hermitian. -/
theorem maskProduct_herm {n : ℕ} :
    ∀ (gs : List (PauliElem n)) (hgs : CommutingHermitianPaulis gs) (m : Mask),
      m.length = gs.length → IsHermitianPauli (maskProduct gs m) := by
  intro gs
  induction gs with
  | nil =>
      intro _hgs m hm
      cases m with
      | nil =>
          simp only [maskProduct]
          exact Or.inl rfl
      | cons b m0 => simp at hm
  | cons g rest ih =>
      intro hgs m hm
      have hrest : CommutingHermitianPaulis rest := commutingHermitian_tail hgs
      obtain ⟨b, m0, rfl⟩ := mask_exists_cons hm
      have hm0 : m0.length = rest.length := by
        simp only [List.length_cons] at hm
        omega
      have hgrest : ∀ h ∈ rest, op g * op h = op h * op g :=
        fun h hh => hgs.2 g (List.mem_cons_self) h (by simp [hh])
      cases b with
      | false =>
          rw [show maskProduct (g :: rest) (false :: m0) = maskProduct rest m0 from rfl]
          exact ih hrest m0 hm0
      | true =>
          rw [show maskProduct (g :: rest) (true :: m0)
                = PauliElem.mul g (maskProduct rest m0) from rfl]
          exact mul_herm_comm_herm (hgs.1 g (List.mem_cons_self)) (ih hrest m0 hm0)
            (op_commute_maskProduct (g := g) rest hgrest m0 hm0)

/-- Every masked product of commuting Hermitian generators acts as the identity on their
projector. -/
theorem projectorAux_mul_maskProduct {n : ℕ} :
    ∀ (gs : List (PauliElem n)) (hgs : CommutingHermitianPaulis gs) (m : Mask),
      m.length = gs.length → op (maskProduct gs m) * projectorAux gs = projectorAux gs := by
  intro gs
  induction gs with
  | nil =>
      intro _hgs m hm
      have : m = [] := by
        cases m with
        | nil => rfl
        | cons b m0 => simp at hm
      subst this
      simp only [maskProduct, op_one, projectorAux, Matrix.mul_one]
  | cons g rest ih =>
      intro hgs m hm
      have hrest : CommutingHermitianPaulis rest := commutingHermitian_tail hgs
      obtain ⟨b, m0, rfl⟩ := mask_exists_cons hm
      have hm0 : m0.length = rest.length := by
        simp only [List.length_cons] at hm
        omega
      have hgrest : ∀ h ∈ rest, op g * op h = op h * op g :=
        fun h hh => hgs.2 g (List.mem_cons_self) h (by simp [hh])
      have hIH := ih hrest m0 hm0
      have hform : projectorAux (g :: rest)
          = ((2 : ℂ)⁻¹) • (projectorAux rest + op g * projectorAux rest) := rfl
      have hcomm : op g * op (maskProduct rest m0) = op (maskProduct rest m0) * op g :=
        op_commute_maskProduct (g := g) rest hgrest m0 hm0
      have hkey : op (maskProduct rest m0) * projectorAux rest
            + op (maskProduct rest m0) * (op g * projectorAux rest)
          = projectorAux rest + op g * projectorAux rest := by
        calc op (maskProduct rest m0) * projectorAux rest
                + op (maskProduct rest m0) * (op g * projectorAux rest)
            = projectorAux rest + op (maskProduct rest m0) * (op g * projectorAux rest) := by
              rw [hIH]
          _ = projectorAux rest + (op (maskProduct rest m0) * op g)
                * projectorAux rest := by rw [Matrix.mul_assoc]
          _ = projectorAux rest + (op g * op (maskProduct rest m0))
                * projectorAux rest := by rw [hcomm]
          _ = projectorAux rest + op g * (op (maskProduct rest m0)
                * projectorAux rest) := by rw [Matrix.mul_assoc]
          _ = projectorAux rest + op g * projectorAux rest := by rw [hIH]
      have hinner : op (maskProduct rest m0) * projectorAux (g :: rest) = projectorAux (g :: rest) := by
        calc op (maskProduct rest m0) * projectorAux (g :: rest)
            = ((2 : ℂ)⁻¹) • (op (maskProduct rest m0) *
                (projectorAux rest + op g * projectorAux rest)) := by
              rw [hform, Matrix.mul_smul]
          _ = ((2 : ℂ)⁻¹) • (op (maskProduct rest m0) * projectorAux rest
                + op (maskProduct rest m0) * (op g * projectorAux rest)) := by
              rw [Matrix.mul_add]
          _ = ((2 : ℂ)⁻¹) • (projectorAux rest + op g * projectorAux rest) := by
              rw [hkey]
          _ = projectorAux (g :: rest) := hform.symm
      have hmp : maskProduct (g :: rest) (b :: m0)
          = if b then PauliElem.mul g (maskProduct rest m0) else maskProduct rest m0 := rfl
      by_cases hb : b = true
      · rw [hmp, if_pos hb, op_mul g (maskProduct rest m0)]
        calc (op g * op (maskProduct rest m0)) * projectorAux (g :: rest)
            = op g * (op (maskProduct rest m0) * projectorAux (g :: rest)) := by
              rw [Matrix.mul_assoc]
          _ = op g * projectorAux (g :: rest) := by rw [hinner]
          _ = projectorAux (g :: rest) :=
              projectorAux_mul_gen (g :: rest)
                (fun h hh => hgs.1 h (by simp [hh]))
                (fun u hu v hv => hgs.2 u (by simp [hu]) v (by simp [hv]))
                g (List.mem_cons_self)
      · rw [hmp, if_neg hb]
        exact hinner

/-- Eliminating redundant commuting Hermitian generators preserves `projectorAux`. -/
theorem projectorAux_eliminateGenerators {n : ℕ} (gs : List (PauliElem n))
    (hgs : CommutingHermitianPaulis gs) :
    projectorAux (eliminateGenerators gs) = projectorAux gs := by
  induction gs with
  | nil => rfl
  | cons g rest ih =>
      have hrest : CommutingHermitianPaulis rest := commutingHermitian_tail hgs
      have ih' : projectorAux (eliminateGenerators rest) = projectorAux rest := ih hrest
      have hcommErest : CommutingHermitianPaulis (eliminateGenerators rest) :=
        commutingHermitian_of_subset hrest (mem_eliminateGenerators rest)
      have hformE : projectorAux (g :: eliminateGenerators rest)
          = ((2 : ℂ)⁻¹) • (projectorAux (eliminateGenerators rest)
              + op g * projectorAux (eliminateGenerators rest)) := rfl
      have hformR : projectorAux (g :: rest)
          = ((2 : ℂ)⁻¹) • (projectorAux rest + op g * projectorAux rest) := rfl
      simp only [eliminateGenerators]
      split
      · next h =>
          have hgmem : g ∈ generatedSubgroup (eliminateGenerators rest) :=
            (memGenerated_eq_true_iff _ _).mp h
          obtain ⟨m, hm, hgm⟩ := hgmem
          have hstabE : op g * projectorAux (eliminateGenerators rest)
              = projectorAux (eliminateGenerators rest) := by
            rw [← hgm]
            exact projectorAux_mul_maskProduct _ hcommErest m hm
          have hstab : op g * projectorAux rest = projectorAux rest := by
            rw [← ih']
            exact hstabE
          rw [ih', hformR, hstab, half_smul_add]
      · next h =>
          rw [hformE, hformR, ih']

/-- Eliminating redundant commuting Hermitian generators gives independent generators if the
generated set excludes negative identity. -/
theorem independent_eliminateGenerators {n : ℕ} :
    ∀ (gs : List (PauliElem n)), CommutingHermitianPaulis gs →
      (minusI n ∉ generatedSubgroup gs) → IndependentGenerators (eliminateGenerators gs) := by
  intro gs
  induction gs with
  | nil =>
      intro hgs hminus
      simp only [eliminateGenerators]
      intro m hm hex
      have hm0 : m.length = 0 := by simpa using! hm
      have hml : m = [] := by
        cases m with
        | nil => rfl
        | cons b m0 => simp at hm0
      subst hml
      obtain ⟨b, hb, htrue⟩ := hex
      exact absurd hb (by simp)
  | cons g rest ih =>
      intro hgs hminus
      have hrest : CommutingHermitianPaulis rest := commutingHermitian_tail hgs
      have hminusRest : minusI n ∉ generatedSubgroup rest := by
        intro hcon
        exact hminus (generatedSubgroup_tail_subset g rest hcon)
      have ih' := ih hrest hminusRest
      have hconj : generatedSubgroup (eliminateGenerators rest) = generatedSubgroup rest :=
        generatedSubgroup_eliminateGenerators rest hrest
      have hcommErest : CommutingHermitianPaulis (eliminateGenerators rest) :=
        commutingHermitian_of_subset hrest (mem_eliminateGenerators rest)
      have hcommE : CommutingHermitianPaulis (g :: eliminateGenerators rest) :=
        commutingHermitian_cons_of_subset hgs (mem_eliminateGenerators rest)
      have hconsEq : generatedSubgroup (g :: eliminateGenerators rest)
          = generatedSubgroup (g :: rest) :=
        generatedSubgroup_cons_congr hgs hcommE (fun p => by rw [hconj])
      intro m hm hex
      have helim : eliminateGenerators (g :: rest) = eliminateGenerators rest ∨
          eliminateGenerators (g :: rest) = g :: eliminateGenerators rest := by
        simp only [eliminateGenerators]
        split
        · exact Or.inl rfl
        · exact Or.inr rfl
      by_cases hmem : memGenerated (eliminateGenerators rest) g = true
      · have helim : eliminateGenerators (g :: rest) = eliminateGenerators rest := by
          simp only [eliminateGenerators, hmem, if_true]
        rw [helim]
        have hmE : m.length = (eliminateGenerators rest).length := by
          rw [helim] at hm
          exact hm
        exact ih' m hmE hex
      · have helim : eliminateGenerators (g :: rest) = g :: eliminateGenerators rest := by
          simp only [eliminateGenerators, hmem, Bool.false_eq_true, ↓reduceIte]
        rw [helim]
        have hgnot : g ∉ generatedSubgroup (eliminateGenerators rest) := by
          intro hcon
          exact hmem ((memGenerated_eq_true_iff _ _).mpr hcon)
        have hmKE : m.length = (g :: eliminateGenerators rest).length := by
          rw [helim] at hm
          exact hm
        have hmKE' : m.length = (eliminateGenerators rest).length + 1 := by
          simp only [List.length_cons] at hmKE
          exact hmKE
        obtain ⟨b, m0, rfl⟩ := mask_exists_cons hmKE'
        have hm0 : m0.length = (eliminateGenerators rest).length := by
          simp only [List.length_cons] at hmKE'
          omega
        cases b with
        | false =>
            rw [show maskWordProduct (g :: eliminateGenerators rest) (false :: m0)
                  = maskWordProduct (eliminateGenerators rest) m0 from rfl]
            obtain ⟨c, hc, hct⟩ := hex
            have hc' : c ∈ m0 := by
              simp only [List.mem_cons] at hc
              rcases hc with hc | hc
              · exact absurd hct (by simp [hc])
              · exact hc
            exact ih' m0 hm0 ⟨c, hc', hct⟩
        | true =>
            rw [show maskWordProduct (g :: eliminateGenerators rest) (true :: m0)
                  = g.word * maskWordProduct (eliminateGenerators rest) m0 from rfl]
            by_cases htrue0 : ∃ c ∈ m0, c = true
            · have hIE := ih' m0 hm0 htrue0
              intro hcontra
              have hcomm1 : maskWordProduct (eliminateGenerators rest) m0 * g.word = trivialWord := by
                rw [mul_comm]
                exact hcontra
              have hw : g.word = maskWordProduct (eliminateGenerators rest) m0 := by
                calc g.word = 1 * g.word := (one_mul _).symm
                  _ = (maskWordProduct (eliminateGenerators rest) m0
                        * maskWordProduct (eliminateGenerators rest) m0) * g.word := by
                      rw [pauliWord_mul_self, one_mul]
                  _ = maskWordProduct (eliminateGenerators rest) m0
                        * (maskWordProduct (eliminateGenerators rest) m0 * g.word) := by
                      rw [mul_assoc]
                  _ = maskWordProduct (eliminateGenerators rest) m0 * trivialWord := by
                      rw [hcomm1]
                  _ = maskWordProduct (eliminateGenerators rest) m0 * 1 := by
                      rw [← pauliWord_one_eq_trivial]
                  _ = maskWordProduct (eliminateGenerators rest) m0 := by rw [mul_one]
              have hword : g.word = (maskProduct (eliminateGenerators rest) m0).word := by
                rw [maskProduct_word, hw]
              have hhermG : IsHermitianPauli g := hgs.1 g (List.mem_cons_self)
              have hhermH : IsHermitianPauli (maskProduct (eliminateGenerators rest) m0) :=
                maskProduct_herm _ hcommErest m0 hm0
              rcases hermitian_eq_or_mul_minusI hhermG hhermH hword with heq | hmul
              · have hgmem : g ∈ generatedSubgroup (eliminateGenerators rest) :=
                  ⟨m0, hm0, heq.symm⟩
                exact hmem ((memGenerated_eq_true_iff _ _).mpr hgmem)
              · have hhmem : maskProduct (eliminateGenerators rest) m0
                    ∈ generatedSubgroup (g :: eliminateGenerators rest) := by
                  refine ⟨false :: m0, ?_, ?_⟩
                  · simp [hm0]
                  · show maskProduct (g :: eliminateGenerators rest) (false :: m0)
                      = maskProduct (eliminateGenerators rest) m0
                    rfl
                have hmemE : g * maskProduct (eliminateGenerators rest) m0
                      ∈ generatedSubgroup (g :: eliminateGenerators rest) :=
                  generatedSubgroup_mul_mem _ hcommE
                    (self_mem_cons g (eliminateGenerators rest)) hhmem
                have hminusMem : minusI n ∈ generatedSubgroup (g :: eliminateGenerators rest) := by
                  rw [← hmul]
                  exact hmemE
                exact hminus (by rw [← hconsEq]; exact hminusMem)
            · have hone : maskWordProduct (eliminateGenerators rest) m0 = 1 := by
                apply maskWordProduct_eq_one
                · exact hm0
                · intro c hc
                  by_contra hne
                  have h1 : c = true := by cases c <;> simp_all
                  exact htrue0 ⟨c, hc, h1⟩
              rw [hone, mul_one]
              intro hcontra
              have hhermG : IsHermitianPauli g := hgs.1 g (List.mem_cons_self)
              rcases hhermG with hg0 | hg2
              · have hg1 : g = 1 := pauli_ext hcontra hg0
                have hgmem : g ∈ generatedSubgroup (eliminateGenerators rest) := by
                  rw [hg1]
                  exact generatedSubgroup_one_mem (eliminateGenerators rest)
                exact hmem ((memGenerated_eq_true_iff _ _).mpr hgmem)
              · have hgminus : g = minusI n := pauli_ext hcontra hg2
                exact hminus (by
                  rw [← hgminus]
                  exact self_mem_cons g rest)

/-- The length of the generator list obtained by `eliminateGenerators`. -/
def generatedGroupRank {n : ℕ} (gs : List (PauliElem n)) : ℕ := (eliminateGenerators gs).length

/-- Every list of length `n` can be represented by `List.ofFn` on `Fin n`. -/
theorem exists_ofFn_eq_of_length {α : Type} {n : ℕ} (m : List α) (hm : m.length = n) :
    ∃ f : Fin n → α, List.ofFn f = m := by
  subst hm
  exact ⟨fun i : Fin m.length => m[i.val], List.ofFn_getElem⟩

/-- The generated set is the finite image of all Boolean selection functions on the generator
indices. -/
theorem generatedSubgroup_eq_image {n : ℕ} (gs : List (PauliElem n)) :
    generatedSubgroup gs
      = ((Finset.univ : Finset (Fin gs.length → Bool)).image
          (fun m => maskProduct gs (List.ofFn m)) : Set (PauliElem n)) := by
  ext p
  constructor
  · intro hp
    obtain ⟨m, hm, hpm⟩ := hp
    obtain ⟨f, hf⟩ := exists_ofFn_eq_of_length m hm
    rw [Finset.mem_coe]
    refine Finset.mem_image.mpr ⟨f, Finset.mem_univ f, ?_⟩
    rw [hf]
    exact hpm
  · intro hp
    rw [Finset.mem_coe] at hp
    simp only [Finset.mem_image] at hp
    obtain ⟨m, hm, hpm⟩ := hp
    exact ⟨List.ofFn m, by simp, hpm⟩

/-- For commuting Hermitian generators excluding negative identity, the generated set has
cardinality `2 ^ generatedGroupRank gs`. -/
theorem card_generatedSubgroup_eq_pow_rank {n : ℕ} (gs : List (PauliElem n))
    (hgs : CommutingHermitianPaulis gs)
    (hminus : minusI n ∉ generatedSubgroup gs) :
    Finset.card ((Finset.univ : Finset (Fin gs.length → Bool)).image
        (fun m => maskProduct gs (List.ofFn m))) = 2 ^ generatedGroupRank gs := by
  have hIE : IndependentGenerators (eliminateGenerators gs) :=
    independent_eliminateGenerators gs hgs hminus
  have hconj : generatedSubgroup (eliminateGenerators gs) = generatedSubgroup gs :=
    generatedSubgroup_eliminateGenerators gs hgs
  have himg : (Finset.univ : Finset (Fin gs.length → Bool)).image
        (fun m => maskProduct gs (List.ofFn m))
      = (Finset.univ : Finset (Fin (eliminateGenerators gs).length → Bool)).image
        (fun m => maskProduct (eliminateGenerators gs) (List.ofFn m)) := by
    have hset : ((Finset.univ : Finset (Fin gs.length → Bool)).image
          (fun m => maskProduct gs (List.ofFn m)) : Set (PauliElem n))
        = ((Finset.univ : Finset (Fin (eliminateGenerators gs).length → Bool)).image
          (fun m => maskProduct (eliminateGenerators gs) (List.ofFn m)) : Set (PauliElem n)) := by
      rw [← generatedSubgroup_eq_image gs,
        ← generatedSubgroup_eq_image (eliminateGenerators gs), hconj]
    apply Finset.ext
    intro p
    rw [Finset.mem_coe.symm, Finset.mem_coe.symm, hset]
  rw [himg]
  exact card_generatedSubgroup (eliminateGenerators gs) rfl hIE

/-- For `k` independent commuting Hermitian generators, the projector-range dimension times `2 ^
k` equals `2 ^ n`. -/
theorem finrank_range_projectorAux_mul {n k : ℕ} (gs : List (PauliElem n))
    (hgs : gs.length = k) (hcomm : CommutingHermitianPaulis gs)
    (hind : IndependentGenerators gs) :
    Module.finrank ℂ ((projectorAux gs).toLin'.range) * 2 ^ k = 2 ^ n := by
  have hidem : (projectorAux gs).toLin' * (projectorAux gs).toLin' = (projectorAux gs).toLin' := by
    rw [Module.End.mul_eq_comp, projectorAux_toLin'_idem gs hcomm]
  have hproj : LinearMap.IsProj ((projectorAux gs).toLin').range (projectorAux gs).toLin' :=
    LinearMap.IsIdempotentElem.isProj_range _ hidem
  have htr : LinearMap.trace ℂ (Reg n → ℂ) (projectorAux gs).toLin'
      = (Module.finrank ℂ ((projectorAux gs).toLin').range : ℂ) := hproj.trace
  rw [Matrix.trace_toLin'_eq] at htr
  have hmain : Matrix.trace (projectorAux gs) = (2 : ℂ) ^ n * ((2 : ℂ) ^ gs.length)⁻¹ :=
    trace_projectorAux gs hind
  rw [hmain] at htr
  rw [hgs] at htr
  have hmul : ((Module.finrank ℂ ((projectorAux gs).toLin'.range) : ℂ)) * (2 : ℂ) ^ k
      = (2 : ℂ) ^ n := by
    rw [← htr]
    field_simp
  exact_mod_cast hmul

/-- For commuting Hermitian generators excluding negative identity, the reduced generator rank
is at most the number of qubits. -/
theorem generatedGroupRank_le_n {n : ℕ} (gs : List (PauliElem n))
    (hgs : CommutingHermitianPaulis gs)
    (hminus : minusI n ∉ generatedSubgroup gs) :
    generatedGroupRank gs ≤ n := by
  have hIE : IndependentGenerators (eliminateGenerators gs) :=
    independent_eliminateGenerators gs hgs hminus
  have hcommE : CommutingHermitianPaulis (eliminateGenerators gs) :=
    commutingHermitian_of_subset hgs (mem_eliminateGenerators gs)
  have hmul := finrank_range_projectorAux_mul (eliminateGenerators gs) rfl hcommE hIE
  have hfin : Module.finrank ℂ ((projectorAux (eliminateGenerators gs)).toLin'.range) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hmul
    have hz2 : (2 : ℕ) ^ n = 0 := by omega
    exact absurd hz2 (Nat.ne_of_gt (by positivity))
  have hpos : 0 < Module.finrank ℂ ((projectorAux (eliminateGenerators gs)).toLin'.range) :=
    Nat.pos_of_ne_zero hfin
  have hle : 2 ^ generatedGroupRank gs ≤ 2 ^ n := by
    calc 2 ^ generatedGroupRank gs
        ≤ Module.finrank ℂ ((projectorAux (eliminateGenerators gs)).toLin'.range)
            * 2 ^ generatedGroupRank gs := Nat.le_mul_of_pos_left (2 ^ generatedGroupRank gs) hpos
      _ = 2 ^ n := hmul
  exact Nat.pow_le_pow_iff_right (by decide) |>.mp hle

/-- A consistent tableau's code space is the range of the projector formed from its reduced
generators. -/
theorem codeSpace_eq_range_eliminateGenerators {n m : ℕ} (t : Tableau n m)
    (ht : ConsistentTableau t) :
    codeSpace t = (projectorAux (eliminateGenerators (tableauGenerators t))).toLin'.range := by
  have hgen : CommutingHermitianPaulis (tableauGenerators t) := by
    constructor
    · intro h hh
      obtain ⟨a, rfl⟩ := (mem_tableauGenerators t h).mp hh
      exact ht.1 a
    · intro u hu v hv
      obtain ⟨a, rfl⟩ := (mem_tableauGenerators t u).mp hu
      obtain ⟨b, rfl⟩ := (mem_tableauGenerators t v).mp hv
      exact ht.2 a b
  rw [codeSpace_eq_range t ht, projectorAux_eliminateGenerators _ hgen]

/-- For a consistent tableau whose generated set excludes negative identity, its code-space
dimension is `2 ^ (n - generatedGroupRank (tableauGenerators t))`. -/
theorem finrank_codeSpace_eq_pow_sub_rank {n m : ℕ} (t : Tableau n m)
    (ht : ConsistentTableau t)
    (hminus : minusI n ∉ generatedSubgroup (tableauGenerators t)) :
    Module.finrank ℂ (codeSpace t) = 2 ^ (n - generatedGroupRank (tableauGenerators t)) := by
  have hgen : CommutingHermitianPaulis (tableauGenerators t) := by
    constructor
    · intro h hh
      obtain ⟨a, rfl⟩ := (mem_tableauGenerators t h).mp hh
      exact ht.1 a
    · intro u hu v hv
      obtain ⟨a, rfl⟩ := (mem_tableauGenerators t u).mp hu
      obtain ⟨b, rfl⟩ := (mem_tableauGenerators t v).mp hv
      exact ht.2 a b
  have hind : IndependentGenerators (eliminateGenerators (tableauGenerators t)) :=
    independent_eliminateGenerators _ hgen hminus
  have hcomm : CommutingHermitianPaulis (eliminateGenerators (tableauGenerators t)) :=
    commutingHermitian_of_subset hgen (mem_eliminateGenerators _)
  have hr : generatedGroupRank (tableauGenerators t) ≤ n :=
    generatedGroupRank_le_n (tableauGenerators t) hgen hminus
  rw [codeSpace_eq_range_eliminateGenerators t ht]
  exact finrank_range_projectorAux (eliminateGenerators (tableauGenerators t)) rfl hr hcomm hind

/-- The binary symplectic pairing of the two Pauli words is nonzero. -/
def pauliAnticommutes {n : ℕ} (p q : PauliElem n) : Prop :=
  symplecticForm (symplecticVec p.word) (symplecticVec q.word) ≠ 0

/-- Two Pauli elements anticommute exactly when they do not commute. -/
theorem pauliAnticommutes_iff {n : ℕ} (p q : PauliElem n) :
    pauliAnticommutes p q ↔ ¬ pauliCommute p q := by
  unfold pauliAnticommutes pauliCommute symplecticVec
  rfl

/-- The binary symplectic form is symmetric. -/
theorem symplecticForm_comm {n : ℕ} (v w : BooleanVec n × BooleanVec n) :
    symplecticForm v w = symplecticForm w v := by
  simp only [symplecticForm]
  rw [booleanDot_comm v.2 w.1, booleanDot_comm v.1 w.2]
  abel

/-- Anticommuting Pauli words have binary symplectic pairing one. -/
theorem symplecticForm_eq_one_of_anticommutes {n : ℕ} {p q : PauliElem n}
    (h : pauliAnticommutes p q) :
    symplecticForm (symplecticVec p.word) (symplecticVec q.word) = 1 := by
  rcases zmod2_eq_zero_or_one
      (symplecticForm (symplecticVec p.word) (symplecticVec q.word)) with h' | h'
  · exact (h h').elim
  · exact h'

/-- The selected measurement row decodes to the outcome-signed measured Pauli element. -/
theorem decode_measuredRow_of_eq {n m : ℕ} (t : Tableau n m) (a₀ : Fin m) (p : PauliElem n)
    (b : Bool) {i : Fin m} (hi : i = a₀) :
    (measuredRow t a₀ p b i).decode = signedMeasuredPauli p b := by
  subst hi
  rw [measuredRow, if_pos rfl, decode_encode]

/-- An unselected row commuting with the measured Pauli decodes to its original element. -/
theorem decode_measuredRow_of_commute {n m : ℕ} (t : Tableau n m) (a₀ : Fin m) (p : PauliElem n)
    (b : Bool) {i : Fin m} (hi : i ≠ a₀) (hc : pauliCommute (t i).decode p) :
    (measuredRow t a₀ p b i).decode = (t i).decode := by
  rw [measuredRow, if_neg hi, if_pos hc]

/-- An unselected row not commuting with the measured Pauli decodes to its product with the
selected row. -/
theorem decode_measuredRow_of_anticommute {n m : ℕ} (t : Tableau n m) (a₀ : Fin m)
    (p : PauliElem n) (b : Bool) {i : Fin m} (hi : i ≠ a₀) (hc : ¬ pauliCommute (t i).decode p) :
    (measuredRow t a₀ p b i).decode = PauliElem.mul (t i).decode (t a₀).decode := by
  rw [measuredRow, if_neg hi, if_neg hc, decode_mul]

/-- Changing the measurement-outcome sign preserves the Pauli word. -/
theorem word_signedMeasuredPauli {n : ℕ} (p : PauliElem n) (b : Bool) :
    (signedMeasuredPauli p b).word = p.word := by
  cases b with
  | true => rfl
  | false =>
      show (PauliElem.mul p (⟨fun _ => Pauli1.I, 2⟩ : PauliElem n)).word = p.word
      rw [pauliElem_mul_word]
      have h : (fun _ : Fin n => Pauli1.I) = (1 : PauliWord n) := by funext i; rfl
      rw [h, mul_one]

/-- The row `minusIRow` decodes to the identity word with phase exponent two. -/
theorem decode_minusIRow {n : ℕ} :
    (minusIRow n).decode = (⟨fun _ : Fin n => Pauli1.I, 2⟩ : PauliElem n) := by
  apply pauli_ext
  · funext k
    rfl
  · rfl

/-- The signed measured Pauli element is the decoding of `feedbackRow p b`. -/
theorem signedMeasuredPauli_eq_feedbackRow {n : ℕ} (p : PauliElem n) (b : Bool) :
    signedMeasuredPauli p b = (feedbackRow p b).decode := by
  cases b with
  | true =>
      show p = (feedbackRow p true).decode
      simp [feedbackRow, decode_encode]
  | false =>
      show PauliElem.mul p (⟨fun _ => Pauli1.I, 2⟩ : PauliElem n) = (feedbackRow p false).decode
      simp [feedbackRow, decode_mul, decode_encode, decode_minusIRow]

/-- The operator of the signed measured Pauli is `op p` for true and its negative for false. -/
theorem op_signedMeasuredPauli {n : ℕ} (p : PauliElem n) (b : Bool) :
    op (signedMeasuredPauli p b) = if b then op p else -op p := by
  rw [signedMeasuredPauli_eq_feedbackRow]
  exact op_feedbackRow p b

/-- The outcome-signed version of a Hermitian Pauli element is Hermitian. -/
theorem hermitian_signedMeasuredPauli {n : ℕ} (p : PauliElem n) (hp : IsHermitianPauli p)
    (b : Bool) : IsHermitianPauli (signedMeasuredPauli p b) := by
  cases b with
  | true => exact hp
  | false =>
      have hsum : (∑ i : Fin n, pauliMulPhase (p.word i) Pauli1.I) = 0 := by
        simp [pauliMulPhase_right_I]
      show (p.phase + 2 + (∑ i : Fin n, pauliMulPhase (p.word i) Pauli1.I) = 0 ∨
            p.phase + 2 + (∑ i : Fin n, pauliMulPhase (p.word i) Pauli1.I) = 2)
      rw [hsum]
      rcases hp with hp0 | hp2
      · rw [hp0]
        show (0 : ZMod 4) + 2 + 0 = 0 ∨ (0 : ZMod 4) + 2 + 0 = 2
        decide
      · rw [hp2]
        show (2 : ZMod 4) + 2 + 0 = 0 ∨ (2 : ZMod 4) + 2 + 0 = 2
        decide

/-- The selected measurement row has the binary symplectic vector of the measured Pauli word. -/
theorem symplecticVec_measuredRow_of_eq {n m : ℕ} (t : Tableau n m) (a₀ : Fin m) (p : PauliElem n)
    (b : Bool) {i : Fin m} (hi : i = a₀) :
    symplecticVec (measuredRow t a₀ p b i).decode.word = symplecticVec p.word := by
  rw [decode_measuredRow_of_eq t a₀ p b hi, word_signedMeasuredPauli]

/-- An unselected commuting measurement row retains its binary symplectic vector. -/
theorem symplecticVec_measuredRow_of_commute {n m : ℕ} (t : Tableau n m) (a₀ : Fin m)
    (p : PauliElem n) (b : Bool) {i : Fin m} (hi : i ≠ a₀) (hc : pauliCommute (t i).decode p) :
    symplecticVec (measuredRow t a₀ p b i).decode.word = symplecticVec (t i).decode.word := by
  rw [decode_measuredRow_of_commute t a₀ p b hi hc]

/-- An unselected noncommuting measurement row has vector equal to its original vector plus the
selected row vector. -/
theorem symplecticVec_measuredRow_of_anticommute {n m : ℕ} (t : Tableau n m) (a₀ : Fin m)
    (p : PauliElem n) (b : Bool) {i : Fin m} (hi : i ≠ a₀) (hc : ¬ pauliCommute (t i).decode p) :
    symplecticVec (measuredRow t a₀ p b i).decode.word =
      symplecticVec (t i).decode.word + symplecticVec (t a₀).decode.word := by
  rw [decode_measuredRow_of_anticommute t a₀ p b hi hc, pauliElem_mul_word, symplecticVec_mul]

/-- A Pauli element anticommuting with each of two elements commutes with their product. -/
theorem pauliCommute_mul_of_anticommute {n : ℕ} (p q r : PauliElem n)
    (hq : pauliAnticommutes p q) (hr : pauliAnticommutes p r) :
    pauliCommute p (PauliElem.mul q r) := by
  show symplecticForm (symplecticVec p.word) (symplecticVec (PauliElem.mul q r).word) = 0
  rw [pauliElem_mul_word, symplecticVec_mul, symplecticForm_add_right]
  have h1 := symplecticForm_eq_one_of_anticommutes hq
  have h2 := symplecticForm_eq_one_of_anticommutes hr
  rw [h1, h2]
  decide

/-- Pauli commutativity is symmetric. -/
theorem pauliCommute_comm {n : ℕ} (p q : PauliElem n) :
    pauliCommute p q ↔ pauliCommute q p := by
  unfold pauliCommute
  rw [symplecticForm_comm]

/-- A binary symplectic pairing vanishes exactly when the Pauli elements commute. -/
theorem symplecticForm_eq_zero_iff_commute {n : ℕ} (p q : PauliElem n) :
    symplecticForm (symplecticVec p.word) (symplecticVec q.word) = 0 ↔ pauliCommute p q := by
  unfold pauliCommute symplecticVec
  rfl

/-- A binary symplectic pairing is nonzero exactly when the Pauli elements anticommute. -/
theorem symplecticForm_ne_zero_iff_anticommute {n : ℕ} (p q : PauliElem n) :
    symplecticForm (symplecticVec p.word) (symplecticVec q.word) ≠ 0 ↔ pauliAnticommutes p q := by
  unfold pauliAnticommutes
  rfl

/-- Commuting Pauli elements have zero binary symplectic pairing. -/
theorem form_zero_of_commute {n : ℕ} {p q : PauliElem n} (h : pauliCommute p q) :
    symplecticForm (symplecticVec p.word) (symplecticVec q.word) = 0 :=
  (symplecticForm_eq_zero_iff_commute p q).mpr h

/-- Commutativity in the reversed order also implies zero binary symplectic pairing. -/
theorem form_zero_of_commute_symm {n : ℕ} {p q : PauliElem n} (h : pauliCommute q p) :
    symplecticForm (symplecticVec p.word) (symplecticVec q.word) = 0 := by
  have h' := form_zero_of_commute h
  rw [symplecticForm_comm] at h'
  exact h'

/-- Anticommutativity in the reversed order rules out commutativity. -/
theorem not_commute_of_anticommutes {n : ℕ} {p q : PauliElem n} (h : pauliAnticommutes q p) :
    ¬ pauliCommute p q := by
  intro hc
  have hz : symplecticForm (symplecticVec p.word) (symplecticVec q.word) = 0 :=
    form_zero_of_commute hc
  have hz' : symplecticForm (symplecticVec q.word) (symplecticVec p.word) = 0 := by
    rw [symplecticForm_comm]
    exact hz
  exact h hz'

/-- Anticommutativity in the reversed order gives binary symplectic pairing one. -/
theorem form_one_of_anticommute_symm {n : ℕ} {p q : PauliElem n} (h : pauliAnticommutes q p) :
    symplecticForm (symplecticVec p.word) (symplecticVec q.word) = 1 := by
  have h' := symplecticForm_eq_one_of_anticommutes h
  rw [symplecticForm_comm] at h'
  exact h'

/-- If the selected row anticommutes with the measured Pauli, all updated row vectors of a
consistent tableau have pairwise zero symplectic pairing. -/
theorem symplecticForm_measuredRow_zero {n m : ℕ} (t : Tableau n m) (ht : ConsistentTableau t)
    (a₀ : Fin m) (p : PauliElem n)
    (hanti : pauliAnticommutes (t a₀).decode p) (b : Bool) (i j : Fin m) :
    symplecticForm (symplecticVec (measuredRow t a₀ p b i).decode.word)
      (symplecticVec (measuredRow t a₀ p b j).decode.word) = 0 := by
  have hrow : ∀ u v : Fin m,
      symplecticForm (symplecticVec (t u).decode.word) (symplecticVec (t v).decode.word) = 0 := by
    intro u v
    exact (op_commute_iff_symplecticVec_form_zero (t u).decode (t v).decode).mp (ht.2 u v)
  by_cases hi : i = a₀
  · by_cases hj : j = a₀
    · rw [symplecticVec_measuredRow_of_eq t a₀ p b hi,
        symplecticVec_measuredRow_of_eq t a₀ p b hj]
      exact symplecticForm_self _
    · by_cases hcj : pauliCommute (t j).decode p
      · rw [symplecticVec_measuredRow_of_eq t a₀ p b hi,
          symplecticVec_measuredRow_of_commute t a₀ p b hj hcj]
        exact form_zero_of_commute_symm hcj
      · rw [symplecticVec_measuredRow_of_eq t a₀ p b hi,
          symplecticVec_measuredRow_of_anticommute t a₀ p b hj hcj,
          symplecticForm_add_right]
        have h1 : symplecticForm (symplecticVec p.word) (symplecticVec (t j).decode.word) = 1 :=
          form_one_of_anticommute_symm ((pauliAnticommutes_iff (t j).decode p).mpr hcj)
        have h2 : symplecticForm (symplecticVec p.word) (symplecticVec (t a₀).decode.word) = 1 :=
          form_one_of_anticommute_symm hanti
        rw [h1, h2]
        decide
  · by_cases hj : j = a₀
    · by_cases hci : pauliCommute (t i).decode p
      · rw [symplecticVec_measuredRow_of_commute t a₀ p b hi hci,
          symplecticVec_measuredRow_of_eq t a₀ p b hj]
        exact form_zero_of_commute hci
      · rw [symplecticVec_measuredRow_of_anticommute t a₀ p b hi hci,
          symplecticVec_measuredRow_of_eq t a₀ p b hj,
          symplecticForm_add_left]
        have h1 : symplecticForm (symplecticVec (t i).decode.word) (symplecticVec p.word) = 1 :=
          symplecticForm_eq_one_of_anticommutes
            ((pauliAnticommutes_iff (t i).decode p).mpr hci)
        have h2 : symplecticForm (symplecticVec (t a₀).decode.word) (symplecticVec p.word) = 1 :=
          symplecticForm_eq_one_of_anticommutes hanti
        rw [h1, h2]
        decide
    · by_cases hci : pauliCommute (t i).decode p
      · by_cases hcj : pauliCommute (t j).decode p
        · rw [symplecticVec_measuredRow_of_commute t a₀ p b hi hci,
            symplecticVec_measuredRow_of_commute t a₀ p b hj hcj]
          exact hrow i j
        · rw [symplecticVec_measuredRow_of_commute t a₀ p b hi hci,
            symplecticVec_measuredRow_of_anticommute t a₀ p b hj hcj,
            symplecticForm_add_right]
          rw [hrow i j, hrow i a₀]
          decide
      · by_cases hcj : pauliCommute (t j).decode p
        · rw [symplecticVec_measuredRow_of_anticommute t a₀ p b hi hci,
            symplecticVec_measuredRow_of_commute t a₀ p b hj hcj,
            symplecticForm_add_left]
          rw [hrow i j, hrow a₀ j]
          decide
        · rw [symplecticVec_measuredRow_of_anticommute t a₀ p b hi hci,
            symplecticVec_measuredRow_of_anticommute t a₀ p b hj hcj,
            symplecticForm_add_left, symplecticForm_add_right, symplecticForm_add_right]
          rw [hrow i j, hrow i a₀, hrow a₀ j, hrow a₀ a₀]
          decide

/-- At the selected index, the measured tableau decodes to the outcome-signed measured Pauli. -/
theorem decode_measuredTableau_of_eq {n m : ℕ} (t : Tableau n m) (a₀ : Fin m) (p : PauliElem n)
    (b : Bool) {i : Fin m} (hi : i = a₀) :
    (measuredTableau t a₀ p b i).decode = signedMeasuredPauli p b := by
  show (measuredRow t a₀ p b i).decode = _
  exact decode_measuredRow_of_eq t a₀ p b hi

/-- An unselected row commuting with the measured Pauli is unchanged after decoding the measured
tableau. -/
theorem decode_measuredTableau_of_commute {n m : ℕ} (t : Tableau n m) (a₀ : Fin m) (p : PauliElem n)
    (b : Bool) {i : Fin m} (hi : i ≠ a₀) (hc : pauliCommute (t i).decode p) :
    (measuredTableau t a₀ p b i).decode = (t i).decode := by
  show (measuredRow t a₀ p b i).decode = _
  exact decode_measuredRow_of_commute t a₀ p b hi hc

/-- An unselected noncommuting row of the measured tableau decodes to its product with the
selected original row. -/
theorem decode_measuredTableau_of_anticommute {n m : ℕ} (t : Tableau n m) (a₀ : Fin m)
    (p : PauliElem n) (b : Bool) {i : Fin m} (hi : i ≠ a₀) (hc : ¬ pauliCommute (t i).decode p) :
    (measuredTableau t a₀ p b i).decode = PauliElem.mul (t i).decode (t a₀).decode := by
  show (measuredRow t a₀ p b i).decode = _
  exact decode_measuredRow_of_anticommute t a₀ p b hi hc

/-- Updating a consistent tableau by a Hermitian Pauli measurement with an anticommuting
selected row preserves tableau consistency. -/
theorem consistent_measuredTableau {n m : ℕ} (t : Tableau n m) (ht : ConsistentTableau t)
    (a₀ : Fin m) (p : PauliElem n) (hp : IsHermitianPauli p)
    (hanti : pauliAnticommutes (t a₀).decode p) (b : Bool) :
    ConsistentTableau (measuredTableau t a₀ p b) := by
  constructor
  · intro i
    by_cases hi : i = a₀
    · rw [decode_measuredTableau_of_eq t a₀ p b hi]
      exact hermitian_signedMeasuredPauli p hp b
    · by_cases hc : pauliCommute (t i).decode p
      · rw [decode_measuredTableau_of_commute t a₀ p b hi hc]
        exact ht.1 i
      · rw [decode_measuredTableau_of_anticommute t a₀ p b hi hc]
        exact mul_herm_comm_herm (ht.1 i) (ht.1 a₀) (ht.2 i a₀)
  · intro i j
    exact (op_commute_iff_symplecticVec_form_zero (measuredTableau t a₀ p b i).decode
      (measuredTableau t a₀ p b j).decode).mpr
      (symplecticForm_measuredRow_zero t ht a₀ p hanti b i j)

/-- Projecting a code state onto a measurement branch places it in the updated tableau's code
space, provided the selected row anticommutes with the Hermitian measured Pauli. -/
theorem mem_codeSpace_measuredTableau {n m : ℕ} (t : Tableau n m) (ht : ConsistentTableau t)
    (a₀ : Fin m) (p : PauliElem n) (hp : IsHermitianPauli p)
    (hanti : pauliAnticommutes (t a₀).decode p) (b : Bool) (ψ : QState (Reg n))
    (hψ : ψ ∈ codeSpace t) :
    pauliBranchProjector p b *ᵥ ψ ∈ codeSpace (measuredTableau t a₀ p b) := by
  rw [mem_codeSpace_iff]
  intro i
  by_cases hi : i = a₀
  · rw [decode_measuredTableau_of_eq t a₀ p b hi, signedMeasuredPauli_eq_feedbackRow]
    exact op_feedbackRow_branch p hp b ψ
  · by_cases hc : pauliCommute (t i).decode p
    · rw [decode_measuredTableau_of_commute t a₀ p b hi hc]
      have hswap : op (t i).decode * pauliBranchProjector p b
          = pauliBranchProjector p b * op (t i).decode :=
        op_row_comm_branch (t i).decode p b ((op_commute_iff (t i).decode p).mpr hc)
      rw [Matrix.mulVec_mulVec, hswap]
      have hfix : op (t i).decode *ᵥ ψ = ψ := (mem_codeSpace_iff t ψ).mp hψ i
      rw [← Matrix.mulVec_mulVec, hfix]
    · rw [decode_measuredTableau_of_anticommute t a₀ p b hi hc]
      have hform : symplecticForm
          (symplecticVec (PauliElem.mul (t i).decode (t a₀).decode).word)
          (symplecticVec p.word) = 0 := by
        have hz := symplecticForm_measuredRow_zero t ht a₀ p hanti b i a₀
        rw [decode_measuredRow_of_anticommute t a₀ p b hi hc] at hz
        rw [decode_measuredRow_of_eq t a₀ p b rfl, word_signedMeasuredPauli] at hz
        exact hz
      have hcomm : op (PauliElem.mul (t i).decode (t a₀).decode) * op p
          = op p * op (PauliElem.mul (t i).decode (t a₀).decode) :=
        (op_commute_iff_symplecticVec_form_zero _ _).mpr hform
      have hswap : op (PauliElem.mul (t i).decode (t a₀).decode) * pauliBranchProjector p b
          = pauliBranchProjector p b * op (PauliElem.mul (t i).decode (t a₀).decode) :=
        op_row_comm_branch _ p b hcomm
      have hfix₀ : op (t a₀).decode *ᵥ ψ = ψ := (mem_codeSpace_iff t ψ).mp hψ a₀
      have hfixᵢ : op (t i).decode *ᵥ ψ = ψ := (mem_codeSpace_iff t ψ).mp hψ i
      have hfix : op (PauliElem.mul (t i).decode (t a₀).decode) *ᵥ ψ = ψ := by
        calc op (PauliElem.mul (t i).decode (t a₀).decode) *ᵥ ψ
            = op (t i).decode *ᵥ (op (t a₀).decode *ᵥ ψ) := by
                rw [op_mul]
                exact (Matrix.mulVec_mulVec ψ (op (t i).decode) (op (t a₀).decode)).symm
          _ = op (t i).decode *ᵥ ψ := by rw [hfix₀]
          _ = ψ := hfixᵢ
      calc op (PauliElem.mul (t i).decode (t a₀).decode) *ᵥ (pauliBranchProjector p b *ᵥ ψ)
          = (op (PauliElem.mul (t i).decode (t a₀).decode) * pauliBranchProjector p b) *ᵥ ψ :=
            (Matrix.mulVec_mulVec ψ _ _)
        _ = (pauliBranchProjector p b * op (PauliElem.mul (t i).decode (t a₀).decode)) *ᵥ ψ := by
            rw [hswap]
        _ = pauliBranchProjector p b *ᵥ
            (op (PauliElem.mul (t i).decode (t a₀).decode) *ᵥ ψ) :=
            (Matrix.mulVec_mulVec ψ _ _).symm
        _ = pauliBranchProjector p b *ᵥ ψ := by rw [hfix]

/-- Every state in the updated code space is an eigenvector of the measured Pauli with sign
determined by the Boolean outcome. -/
theorem codeSpace_measuredTableau_subset_branch {n m : ℕ} (t : Tableau n m) (a₀ : Fin m)
    (p : PauliElem n) (b : Bool) (ψ : QState (Reg n))
    (hψ : ψ ∈ codeSpace (measuredTableau t a₀ p b)) :
    op p *ᵥ ψ = if b then ψ else -ψ := by
  have h := (mem_codeSpace_iff (measuredTableau t a₀ p b) ψ).mp hψ a₀
  rw [decode_measuredTableau_of_eq t a₀ p b rfl] at h
  cases b with
  | true =>
      rw [op_signedMeasuredPauli] at h
      simp at h
      exact h
  | false =>
      rw [op_signedMeasuredPauli] at h
      simp at h
      calc op p *ᵥ ψ = Neg.neg ((-op p) *ᵥ ψ) := by
            have hneg : (-op p) *ᵥ ψ = -(op p *ᵥ ψ) := Matrix.neg_mulVec ψ (op p)
            rw [hneg, neg_neg]
        _ = -ψ := by rw [h]

/-- The list of tableau generators has one entry per row. -/
theorem tableauGenerators_length {n m : ℕ} (t : Tableau n m) :
    (tableauGenerators t).length = m := by
  simp [tableauGenerators, List.length_map, List.length_finRange]

/-- Identifies tableau row indices with indices of the corresponding generator list. -/
def rowEquiv {n m : ℕ} (t : Tableau n m) : Fin m ≃ Fin (tableauGenerators t).length :=
  Equiv.ofBijective (Fin.cast (tableauGenerators_length t).symm)
    ⟨Fin.cast_injective _, fun y =>
        ⟨⟨y.val, by
            have hy := y.isLt
            have hL := tableauGenerators_length t
            omega⟩, by
          apply Fin.ext
          rfl⟩⟩

/-- Accessing the generator corresponding to a row index returns that row's decoded Pauli
element. -/
theorem generatorAt_rowEquiv {n m : ℕ} (t : Tableau n m) (i : Fin m) :
    generatorAt (tableauGenerators t) (rowEquiv t i) = (t i).decode := by
  show (tableauGenerators t).getD (rowEquiv t i).val 1 = (t i).decode
  have hval : (rowEquiv t i).val = i.val := rfl
  rw [hval, tableauGenerators, List.getD_eq_getElem _ _ (by
    simp only [List.length_map, List.length_finRange]
    omega)]
  rw [List.getElem_map]
  have hfin : (List.finRange m)[i.1] = i := by
    have hq : (List.finRange m)[i.1]? = some i := by
      simp only [List.finRange, List.getElem?_ofFn, dif_pos i.isLt]
    have hq' : (List.finRange m)[i.1]? = some ((List.finRange m)[i.1]) :=
      List.getElem?_eq_getElem (by simp [List.length_finRange])
    rw [hq'] at hq
    exact Option.some.inj hq
  rw [hfin]

/-- The binary symplectic vector of a decoded tableau row. -/
def rowSympVec {n m : ℕ} (t : Tableau n m) (i : Fin m) : BooleanVec n × BooleanVec n :=
  symplecticVec (t i).decode.word

/-- Reindexing the generator-vector family by `rowEquiv` gives the row-vector family. -/
theorem symplecticVecOfFn_rowEquiv {n m : ℕ} (t : Tableau n m) (i : Fin m) :
    symplecticVecOfFn (tableauGenerators t) (rowEquiv t i) = rowSympVec t i := by
  rw [symplecticVecOfFn, generatorAt_rowEquiv]
  rfl

/-- The binary symplectic form respects scalar multiplication in its left argument. -/
theorem symplecticForm_smul_left {n : ℕ} (c : ZMod 2) (v w : BooleanVec n × BooleanVec n) :
    symplecticForm (c • v) w = c • symplecticForm v w := by
  rcases zmod2_eq_zero_or_one c with h0 | h1
  · subst h0
    simp [symplecticForm, booleanDot]
  · subst h1
    simp [symplecticForm, booleanDot]

/-- The symplectic pairing of a finite binary linear combination equals the corresponding linear
combination of pairings. -/
theorem symplecticForm_sum_left {n m : ℕ} (c : Fin m → ZMod 2)
    (v : Fin m → BooleanVec n × BooleanVec n) (w : BooleanVec n × BooleanVec n) :
    symplecticForm (∑ i, c i • v i) w = ∑ i, c i • symplecticForm (v i) w := by
  classical
  induction m with
  | zero =>
      simp [symplecticForm, booleanDot]
  | succ m ih =>
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ, symplecticForm_add_left,
        symplecticForm_smul_left]
      rw [ih (fun i => c i.succ) (fun i => v i.succ)]

/-- The binary indicator that a tableau row anticommutes with a measured Pauli element. -/
def antiFlag {n m : ℕ} (t : Tableau n m) (p : PauliElem n) (i : Fin m) : ZMod 2 :=
  if pauliAnticommutes (t i).decode p then 1 else 0

/-- Replacing one vector of an independent isotropic family by a vector pairing to one with it,
and adding multiples of the replaced vector to the other rows, preserves linear
independence. -/
theorem linearIndependent_measured {n m : ℕ} (v v' : Fin m → BooleanVec n × BooleanVec n)
    (vp : BooleanVec n × BooleanVec n) (a₀ : Fin m) (anti : Fin m → ZMod 2)
    (hv : LinearIndependent (ZMod 2) v)
    (hpair : ∀ i j : Fin m, symplecticForm (v i) (v j) = 0)
    (hvpa : symplecticForm vp (v a₀) = 1)
    (hnew₀ : v' a₀ = vp)
    (hnew : ∀ i : Fin m, i ≠ a₀ → v' i = v i + anti i • v a₀) :
    LinearIndependent (ZMod 2) v' := by
  classical
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  intro c c' h
  have hz : (∑ i, (c i - c' i) • v' i) = 0 := by
    have hstep : (∑ i, (c i - c' i) • v' i)
        = (∑ i, c i • v' i) - ∑ i, c' i • v' i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [sub_smul]
    rw [hstep]
    exact sub_eq_zero.mpr h
  set d : Fin m → ZMod 2 := fun i => c i - c' i with hd
  have hzd : (∑ i, d i • v' i) = 0 := by
    rw [hd]
    exact hz

  have hpairzero : ∀ i ∈ (Finset.univ : Finset (Fin m)).erase a₀,
      symplecticForm (v' i) (v a₀) = 0 := by
    intro i hi
    have hi' : i ≠ a₀ := by
      intro hcon
      subst hcon
      simp at hi
    rw [hnew i hi', symplecticForm_add_left, hpair i a₀, symplecticForm_smul_left,
      symplecticForm_self]
    simp
  have hda0 : d a₀ = 0 := by
    have h1 : symplecticForm (∑ i, d i • v' i) (v a₀)
        = ∑ i, d i • symplecticForm (v' i) (v a₀) := symplecticForm_sum_left _ _ _
    have h2 : (∑ i, d i • symplecticForm (v' i) (v a₀)) = d a₀ := by
      have hsplit : (∑ i, d i • symplecticForm (v' i) (v a₀))
          = (∑ i ∈ (Finset.univ : Finset (Fin m)).erase a₀,
              d i • symplecticForm (v' i) (v a₀))
            + d a₀ • symplecticForm (v' a₀) (v a₀) := by
        symm
        exact Finset.sum_erase_add (Finset.univ : Finset (Fin m))
          (fun i => d i • symplecticForm (v' i) (v a₀)) (Finset.mem_univ a₀)
      have hzero : (∑ i ∈ (Finset.univ : Finset (Fin m)).erase a₀,
          d i • symplecticForm (v' i) (v a₀)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hpairzero i hi]
        simp
      rw [hsplit, hzero, hnew₀, hvpa]
      simp
    have h3 : symplecticForm (∑ i, d i • v' i) (v a₀) = 0 := by
      rw [hzd]
      simp [symplecticForm, booleanDot]
    rw [← h1, h3] at h2
    exact h2.symm

  set β : ZMod 2 := ∑ i ∈ (Finset.univ : Finset (Fin m)).erase a₀, d i * anti i with hβ
  have hexp : (∑ i, d i • v' i) = (∑ i, d i • v i) + β • v a₀ := by
    have hsplit : (∑ i, d i • v' i)
        = (∑ i ∈ (Finset.univ : Finset (Fin m)).erase a₀, d i • v' i) + d a₀ • v' a₀ := by
      symm
      exact Finset.sum_erase_add (Finset.univ : Finset (Fin m))
        (fun i => d i • v' i) (Finset.mem_univ a₀)
    have hsub : (∑ i ∈ (Finset.univ : Finset (Fin m)).erase a₀, d i • v' i)
        = (∑ i ∈ (Finset.univ : Finset (Fin m)).erase a₀, d i • v i) + β • v a₀ := by
      have hpoint : ∀ i ∈ (Finset.univ : Finset (Fin m)).erase a₀,
          d i • v' i = d i • v i + (d i * anti i) • v a₀ := by
        intro i hi
        have hi' : i ≠ a₀ := by
          intro hcon
          subst hcon
          simp at hi
        rw [hnew i hi', smul_add, smul_smul]
      rw [Finset.sum_congr rfl (fun i hi => hpoint i hi), Finset.sum_add_distrib]
      have hsl : (∑ i ∈ (Finset.univ : Finset (Fin m)).erase a₀, (d i * anti i) • v a₀)
          = β • v a₀ := by
        calc (∑ i ∈ (Finset.univ : Finset (Fin m)).erase a₀, (d i * anti i) • v a₀)
            = (∑ i ∈ (Finset.univ : Finset (Fin m)).erase a₀, d i * anti i) • v a₀ :=
              Finset.sum_smul.symm
          _ = β • v a₀ := by rw [← hβ]
      rw [hsl]
    have htail : (∑ i ∈ (Finset.univ : Finset (Fin m)).erase a₀, d i • v i)
        = (∑ i, d i • v i) := by
      have h2 : (∑ x ∈ (Finset.univ : Finset (Fin m)).erase a₀, d x • v x)
          + d a₀ • v a₀ = ∑ x, d x • v x := by
        exact Finset.sum_erase_add (Finset.univ : Finset (Fin m))
          (fun i => d i • v i) (Finset.mem_univ a₀)
      rw [hda0] at h2
      simpa using! h2
    rw [hsplit, hnew₀, hsub, htail]
    simp [hda0]
  have hz2 : (∑ i, d i • v i) + β • v a₀ = 0 := by
    rw [← hexp]
    exact hzd

  have hker : ∀ g : Fin m → ZMod 2, (∑ i, g i • v i) = 0 → ∀ i, g i = 0 := by
    intro g hg
    have h1 := ((linearIndependent_iff' (R := (ZMod 2)) (M := BooleanVec n × BooleanVec n)
      (ι := Fin m) (v := v)).mp hv) (Finset.univ) g
    intro i
    exact h1 hg i (Finset.mem_univ i)
  have hzero : ∀ i, d i = 0 := by
    intro i
    by_cases hi : i = a₀
    · subst hi
      exact hda0
    · have hgi : (∑ k, (if k = a₀ then β else d k) • v k) = 0 := by
        have hsplit : (∑ k, (if k = a₀ then β else d k) • v k)
            = (∑ k ∈ (Finset.univ : Finset (Fin m)).erase a₀, d k • v k)
              + β • v a₀ := by
          have h2 : (∑ x ∈ (Finset.univ : Finset (Fin m)).erase a₀,
                (if x = a₀ then β else d x) • v x)
              + (if a₀ = a₀ then β else d a₀) • v a₀
              = ∑ x, (if x = a₀ then β else d x) • v x := by
            exact Finset.sum_erase_add (Finset.univ : Finset (Fin m))
              (fun k => (if k = a₀ then β else d k) • v k) (Finset.mem_univ a₀)
          rw [← h2]
          have hf0 : (if a₀ = a₀ then β else d a₀) • v a₀ = β • v a₀ := by simp
          rw [hf0]
          have hinner : (∑ k ∈ (Finset.univ : Finset (Fin m)).erase a₀,
              (if k = a₀ then β else d k) • v k)
              = (∑ k ∈ (Finset.univ : Finset (Fin m)).erase a₀, d k • v k) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hk' : k ≠ a₀ := by
              intro hcon
              subst hcon
              simp at hk
            rw [if_neg hk']
          rw [hinner, add_comm]
        have htail : (∑ k ∈ (Finset.univ : Finset (Fin m)).erase a₀, d k • v k)
            = (∑ k, d k • v k) := by
          have h2 : (∑ x ∈ (Finset.univ : Finset (Fin m)).erase a₀, d x • v x)
              + d a₀ • v a₀ = ∑ x, d x • v x := by
            exact Finset.sum_erase_add (Finset.univ : Finset (Fin m))
              (fun k => d k • v k) (Finset.mem_univ a₀)
          rw [hda0] at h2
          simpa using! h2
        rw [hsplit, htail]
        exact hz2
      simpa [hi] using! hker _ hgi i
  funext i
  exact sub_eq_zero.mp (hzero i)

/-- Reindexing a linearly independent family by an equivalence preserves linear independence. -/
theorem linearIndependent_comp {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {v : ι' → M}
    (e : ι ≃ ι') (hv : LinearIndependent R v) :
    LinearIndependent R (fun i => v (e i)) := by
  classical
  rw [linearIndependent_iff_injective_fintypeLinearCombination] at hv ⊢
  intro c c' h
  have h1 : (∑ i, c i • v (e i)) = ∑ j, c (e.symm j) • v j := by
    refine Fintype.sum_equiv e (fun i => c i • v (e i)) (fun j => c (e.symm j) • v j) ?_
    intro x
    simp
  have h2 : (∑ i, c' i • v (e i)) = ∑ j, c' (e.symm j) • v j := by
    refine Fintype.sum_equiv e (fun i => c' i • v (e i)) (fun j => c' (e.symm j) • v j) ?_
    intro x
    simp
  have h3 : ∑ j, c (e.symm j) • v j = ∑ j, c' (e.symm j) • v j := by
    rw [← h1, ← h2]
    exact h
  have h3' : Fintype.linearCombination R v (c ∘ e.symm)
      = Fintype.linearCombination R v (c' ∘ e.symm) := by
    simpa only [Fintype.linearCombination, Function.comp_apply] using! h3
  have h4 := hv h3'
  funext i
  simpa using! congrFun h4 (e i)

/-- A measurement update with an anticommuting selected row preserves linear independence of
tableau row vectors for a consistent tableau with independent generators. -/
theorem linearIndependent_measuredTableau {n m : ℕ} (t : Tableau n m) (ht : ConsistentTableau t)
    (a₀ : Fin m) (p : PauliElem n) (hanti : pauliAnticommutes (t a₀).decode p) (b : Bool)
    (hind : IndependentGenerators (tableauGenerators t)) :
    LinearIndependent (ZMod 2) (rowSympVec (measuredTableau t a₀ p b)) := by
  have hold : LinearIndependent (ZMod 2) (rowSympVec t) := by
    have h2 := linearIndependent_comp (rowEquiv t)
      (symplecticVecOfFn_linearIndependent (tableauGenerators t) hind)
    have heq : (fun i : Fin m => symplecticVecOfFn (tableauGenerators t) (rowEquiv t i))
        = rowSympVec t := by
      funext i
      exact symplecticVecOfFn_rowEquiv t i
    rw [← heq]
    exact h2
  have hpair : ∀ i j : Fin m, symplecticForm (rowSympVec t i) (rowSympVec t j) = 0 := by
    intro i j
    exact (op_commute_iff_symplecticVec_form_zero (t i).decode (t j).decode).mp (ht.2 i j)
  have hvpa : symplecticForm (symplecticVec p.word) (rowSympVec t a₀) = 1 := by
    have h1 := symplecticForm_eq_one_of_anticommutes hanti
    rw [symplecticForm_comm] at h1
    exact h1
  have hnew₀ : rowSympVec (measuredTableau t a₀ p b) a₀ = symplecticVec p.word := by
    have h1 := symplecticVec_measuredRow_of_eq t a₀ p b rfl
    exact h1
  have hnew : ∀ i : Fin m, i ≠ a₀ →
      rowSympVec (measuredTableau t a₀ p b) i
        = rowSympVec t i + antiFlag t p i • rowSympVec t a₀ := by
    intro i hi
    by_cases hc : pauliCommute (t i).decode p
    · have h1 := symplecticVec_measuredRow_of_commute t a₀ p b hi hc
      have hanti' : ¬ pauliAnticommutes (t i).decode p :=
        ((pauliAnticommutes_iff (t i).decode p).not).mpr (not_not.mpr hc)
      show symplecticVec (measuredRow t a₀ p b i).decode.word
        = symplecticVec (t i).decode.word + antiFlag t p i • symplecticVec (t a₀).decode.word
      rw [h1]
      simp [antiFlag, hanti']
    · have h1 := symplecticVec_measuredRow_of_anticommute t a₀ p b hi hc
      have hanti' : pauliAnticommutes (t i).decode p := (pauliAnticommutes_iff _ _).mpr hc
      show symplecticVec (measuredRow t a₀ p b i).decode.word
        = symplecticVec (t i).decode.word + antiFlag t p i • symplecticVec (t a₀).decode.word
      rw [h1]
      simp [antiFlag, hanti']
  exact linearIndependent_measured (rowSympVec t) (rowSympVec (measuredTableau t a₀ p b))
    (symplecticVec p.word) a₀ (antiFlag t p) hold hpair hvpa hnew₀ hnew

/-- Every mask of length `k` is `List.ofFn` of a Boolean function on `Fin k`. -/
theorem mask_eq_ofFn {k : ℕ} (mk : Mask) (hmk : mk.length = k) :
    ∃ c : Fin k → Bool, mk = List.ofFn c := by
  refine ⟨fun i => mk.getD i.val false, ?_⟩
  apply List.ext_getElem
  · simp [List.length_ofFn, hmk]
  · intro j h1 h2
    rw [← List.getD_eq_getElem mk false h1, List.getElem_ofFn h2]

/-- Linear independence of the generator symplectic vectors implies `IndependentGenerators`. -/
theorem IndependentGenerators_of_linearIndependent {n : ℕ} (gs : List (PauliElem n))
    (h : LinearIndependent (ZMod 2) (symplecticVecOfFn gs)) : IndependentGenerators gs := by
  classical
  intro mk hmk hne
  obtain ⟨c, hmk'⟩ := mask_eq_ofFn mk hmk
  set c' : Fin gs.length → ZMod 2 := fun i => if c i then 1 else 0 with hc'
  have hmk'' : mk = List.ofFn (fun i => decide (c' i = 1)) := by
    rw [hmk']
    congr 1
    funext i
    by_cases hb : c i
    · simp [hc', hb]
    · simp [hc', hb]
  have hsum : maskVecSum gs mk = ∑ i : Fin gs.length, c' i • symplecticVecOfFn gs i := by
    rw [hmk'', maskVecSum_eq_sum]
  intro hword
  have hsym : symplecticVec (maskWordProduct gs mk) = 0 := by
    rw [hword]
    exact symplecticVec_trivialWord
  have hzero : (∑ i : Fin gs.length, c' i • symplecticVecOfFn gs i) = 0 := by
    rw [← hsum, ← symplecticVec_maskWordProduct, hsym]
  have h1 := ((linearIndependent_iff' (R := (ZMod 2))
    (M := BooleanVec n × BooleanVec n) (ι := Fin gs.length)
    (v := symplecticVecOfFn gs)).mp h) (Finset.univ) c'
  have hc'0 : ∀ i : Fin gs.length, c' i = 0 := fun i => h1 hzero i (Finset.mem_univ i)
  have hcfalse : ∀ i : Fin gs.length, c i = false := by
    intro i
    have hval : (if c i then 1 else 0 : ZMod 2) = 0 := by
      simpa only [hc'] using! hc'0 i
    by_cases hb : c i = true
    · exfalso
      simp only [if_pos hb] at hval
      exact absurd hval (by simp)
    · cases hcval : c i with
      | false => rfl
      | true => exact absurd hcval hb
  obtain ⟨b, hb, hbt⟩ := hne
  have hbfalse : b = false := by
    have hmem' : b ∈ List.ofFn c := by
      rw [← hmk']
      exact hb
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem'
    rw [hcfalse i] at hi
    exact hi.symm
  exact absurd hbt (by simp [hbfalse])

/-- For a consistent tableau with independent generators, a measurement update with an
anticommuting selected row has linearly independent generator vectors. -/
theorem measuredTableau_gens_linearIndependent {n m : ℕ} (t : Tableau n m)
    (ht : ConsistentTableau t) (a₀ : Fin m) (p : PauliElem n)
    (hanti : pauliAnticommutes (t a₀).decode p) (b : Bool)
    (hind : IndependentGenerators (tableauGenerators t)) :
    LinearIndependent (ZMod 2)
      (symplecticVecOfFn (tableauGenerators (measuredTableau t a₀ p b))) := by
  have hrow : LinearIndependent (ZMod 2) (rowSympVec (measuredTableau t a₀ p b)) :=
    linearIndependent_measuredTableau t ht a₀ p hanti b hind
  have h2 := linearIndependent_comp (rowEquiv (measuredTableau t a₀ p b)).symm hrow
  have heq : (fun j : Fin (tableauGenerators (measuredTableau t a₀ p b)).length =>
      rowSympVec (measuredTableau t a₀ p b)
        ((rowEquiv (measuredTableau t a₀ p b)).symm j))
      = symplecticVecOfFn (tableauGenerators (measuredTableau t a₀ p b)) := by
    funext j
    have h1 := symplecticVecOfFn_rowEquiv (measuredTableau t a₀ p b)
      ((rowEquiv (measuredTableau t a₀ p b)).symm j)
    rw [Equiv.apply_symm_apply] at h1
    exact h1.symm
  rw [← heq]
  exact h2

/-- A Hermitian measurement update with an anticommuting selected row preserves code-space
dimension `2 ^ (n - m)` for a consistent tableau with `m ≤ n` independent generators. -/
theorem finrank_codeSpace_measuredTableau {n m : ℕ} (t : Tableau n m) (ht : ConsistentTableau t)
    (a₀ : Fin m) (p : PauliElem n) (hp : IsHermitianPauli p)
    (hanti : pauliAnticommutes (t a₀).decode p) (b : Bool)
    (hind : IndependentGenerators (tableauGenerators t)) (hm : m ≤ n) :
    Module.finrank ℂ (codeSpace (measuredTableau t a₀ p b)) = 2 ^ (n - m) := by
  have hcons : ConsistentTableau (measuredTableau t a₀ p b) :=
    consistent_measuredTableau t ht a₀ p hp hanti b
  have hLI : LinearIndependent (ZMod 2)
      (symplecticVecOfFn (tableauGenerators (measuredTableau t a₀ p b))) :=
    measuredTableau_gens_linearIndependent t ht a₀ p hanti b hind
  have hind' : IndependentGenerators (tableauGenerators (measuredTableau t a₀ p b)) :=
    IndependentGenerators_of_linearIndependent _ hLI
  have hlen : (tableauGenerators (measuredTableau t a₀ p b)).length = m :=
    tableauGenerators_length (measuredTableau t a₀ p b)
  exact finrank_codeSpace (measuredTableau t a₀ p b) hlen hm hcons hind'

/-- The Boolean outcome opposite to the given outcome. -/
def otherOutcome (b : Bool) : Bool := if b then false else true

/-- Flipping the measurement outcome leaves every unselected decoded tableau row unchanged. -/
theorem measuredTableau_flip_off {n m : ℕ} (t : Tableau n m) (a₀ : Fin m) (p : PauliElem n)
    (b : Bool) {i : Fin m} (hi : i ≠ a₀) :
    (measuredTableau t a₀ p (otherOutcome b) i).decode = (measuredTableau t a₀ p b i).decode := by
  by_cases hc : pauliCommute (t i).decode p
  · rw [decode_measuredTableau_of_commute t a₀ p (otherOutcome b) hi hc,
      decode_measuredTableau_of_commute t a₀ p b hi hc]
  · rw [decode_measuredTableau_of_anticommute t a₀ p (otherOutcome b) hi hc,
      decode_measuredTableau_of_anticommute t a₀ p b hi hc]

/-- Flipping the measurement outcome negates the decoded Pauli element at the selected row. -/
theorem measuredTableau_flip_measured {n m : ℕ} (t : Tableau n m) (a₀ : Fin m)
    (p : PauliElem n) (b : Bool) :
    (measuredTableau t a₀ p (otherOutcome b) a₀).decode
      = negPauliElem (measuredTableau t a₀ p b a₀).decode := by
  cases b with
  | true =>
      simp only [otherOutcome, reduceIte]
      rw [decode_measuredTableau_of_eq t a₀ p false rfl,
        decode_measuredTableau_of_eq t a₀ p true rfl]
      show PauliElem.mul p (⟨fun _ => Pauli1.I, 2⟩ : PauliElem n) = negPauliElem p
      apply pauli_ext
      · rw [pauliElem_mul_word]
        show p.word * (fun _ : Fin n => Pauli1.I) = p.word
        rw [show (fun _ : Fin n => Pauli1.I) = (1 : PauliWord n) by funext i; rfl, mul_one]
      · show p.phase + 2 + (∑ i, pauliMulPhase (p.word i) Pauli1.I) = p.phase + 2
        simp [pauliMulPhase_right_I]
  | false =>
      simp only [otherOutcome, Bool.false_eq_true, ite_false]
      rw [decode_measuredTableau_of_eq t a₀ p true rfl,
        decode_measuredTableau_of_eq t a₀ p false rfl]
      show p = negPauliElem (PauliElem.mul p (⟨fun _ => Pauli1.I, 2⟩ : PauliElem n))
      apply pauli_ext
      · show p.word = (PauliElem.mul p (⟨fun _ : Fin n => Pauli1.I, 2⟩ : PauliElem n)).word
        rw [pauliElem_mul_word]
        show p.word = p.word * (fun _ : Fin n => Pauli1.I)
        rw [show (fun _ : Fin n => Pauli1.I) = (1 : PauliWord n) by funext i; rfl, mul_one]
      · show p.phase = (p.phase + 2 + (∑ i, pauliMulPhase (p.word i) Pauli1.I)) + 2
        simp [pauliMulPhase_right_I]
        abel

/-- At the acted-on site, the Hadamard Pauli action applies `conjHWord` to the word letter. -/
theorem cliffordAction_H_word {n : ℕ} (i k : Fin n) (p : PauliElem n) (hk : k = i) :
    (cliffordAction (.H i) p).word k = conjHWord (p.word k) := by
  simp [cliffordAction, hk]

/-- The Hadamard Pauli action preserves word letters outside its site. -/
theorem cliffordAction_H_word_ne {n : ℕ} (i k : Fin n) (p : PauliElem n) (hk : k ≠ i) :
    (cliffordAction (.H i) p).word k = p.word k := by
  simp [cliffordAction, hk]

/-- The Hadamard Pauli action adds the local `conjHPhase` correction to the phase exponent. -/
theorem cliffordAction_H_phase {n : ℕ} (i : Fin n) (p : PauliElem n) :
    (cliffordAction (.H i) p).phase = p.phase + conjHPhase (p.word i) := by
  simp only [cliffordAction]
  simp

/-- At the acted-on site, the phase-gate Pauli action applies `conjSWord` to the word letter. -/
theorem cliffordAction_S_word {n : ℕ} (i k : Fin n) (p : PauliElem n) (hk : k = i) :
    (cliffordAction (.S i) p).word k = conjSWord (p.word k) := by
  simp [cliffordAction, hk]

/-- The phase-gate Pauli action preserves word letters outside its site. -/
theorem cliffordAction_S_word_ne {n : ℕ} (i k : Fin n) (p : PauliElem n) (hk : k ≠ i) :
    (cliffordAction (.S i) p).word k = p.word k := by
  simp [cliffordAction, hk]

/-- The phase-gate Pauli action adds the local `conjSPhase` correction to the phase exponent. -/
theorem cliffordAction_S_phase {n : ℕ} (i : Fin n) (p : PauliElem n) :
    (cliffordAction (.S i) p).phase = p.phase + conjSPhase (p.word i) := by
  simp only [cliffordAction]
  simp

/-- The defined CNOT Pauli action preserves the phase field. -/
theorem cliffordAction_CNOT_phase {n : ℕ} (i j : Fin n) (p : PauliElem n) :
    (cliffordAction (.CNOT i j) p).phase = p.phase := by
  simp [cliffordAction]

/-- The local Hadamard phase correction is zero or two. -/
theorem conjHPhase_eq (a : Pauli1) : conjHPhase a = 0 ∨ conjHPhase a = 2 := by
  cases a <;> simp [conjHPhase]

/-- The local phase-gate phase correction is zero or two. -/
theorem conjSPhase_eq (a : Pauli1) : conjSPhase a = 0 ∨ conjSPhase a = 2 := by
  cases a <;> simp [conjSPhase]

/-- The defined action of any Clifford gate preserves the Hermitian Pauli predicate. -/
theorem cliffordAction_hermitian {n : ℕ} (g : CliffordGate n) (p : PauliElem n)
    (hp : IsHermitianPauli p) : IsHermitianPauli (cliffordAction g p) := by
  cases g with
  | H i =>
      show (cliffordAction (.H i) p).phase = 0 ∨ (cliffordAction (.H i) p).phase = 2
      rw [cliffordAction_H_phase]
      rcases hp with hp0 | hp2
      · rcases conjHPhase_eq (p.word i) with h0 | h2
        · rw [hp0, h0]; decide
        · rw [hp0, h2]; decide
      · rcases conjHPhase_eq (p.word i) with h0 | h2
        · rw [hp2, h0]; decide
        · rw [hp2, h2]; decide
  | S i =>
      show (cliffordAction (.S i) p).phase = 0 ∨ (cliffordAction (.S i) p).phase = 2
      rw [cliffordAction_S_phase]
      rcases hp with hp0 | hp2
      · rcases conjSPhase_eq (p.word i) with h0 | h2
        · rw [hp0, h0]; decide
        · rw [hp0, h2]; decide
      · rcases conjSPhase_eq (p.word i) with h0 | h2
        · rw [hp2, h0]; decide
        · rw [hp2, h2]; decide
  | CNOT i j =>
      show (cliffordAction (.CNOT i j) p).phase = 0 ∨ (cliffordAction (.CNOT i j) p).phase = 2
      rw [cliffordAction_CNOT_phase]
      exact hp

/-- A Hadamard or phase gate at one site preserves word letters at every other site. -/
theorem cliffordAction_site_word_ne {n : ℕ} (g : CliffordGate n) (i k : Fin n) (q : PauliElem n)
    (hk : k ≠ i) (hg : g = .H i ∨ g = .S i) :
    (cliffordAction g q).word k = q.word k := by
  rcases hg with hg | hg
  · subst hg
    exact cliffordAction_H_word_ne i k q hk
  · subst hg
    exact cliffordAction_S_word_ne i k q hk

/-- A circuit consisting of Hadamard and phase gates at a single site preserves every word
letter outside that site. -/
theorem cliffordActionCircuit_site_word_ne {n : ℕ} : ∀ (c : CliffordCircuit n) (i k : Fin n)
    (q : PauliElem n), k ≠ i → (∀ g ∈ c, g = .H i ∨ g = .S i) →
    (cliffordActionCircuit c q).word k = q.word k
  | [], _, _, _, _, _ => rfl
  | g :: gs, i, k, q, hk, h => by
      rw [cliffordActionCircuit]
      rw [cliffordActionCircuit_site_word_ne gs i k (cliffordAction g q) hk
        (fun g' hg' => h g' (List.mem_cons_of_mem g hg'))]
      exact cliffordAction_site_word_ne g i k q hk (h g (List.mem_cons_self))

/-- The sign-flip circuit preserves word letters outside its chosen site. -/
theorem signFlipCircuit_word_ne {n : ℕ} (i k : Fin n) (p : PauliElem n) (hk : k ≠ i) :
    (cliffordActionCircuit (signFlipCircuit i (p.word i)) p).word k = p.word k := by
  cases hp : p.word i with
  | I =>
      simp only [signFlipCircuit, cliffordActionCircuit]
  | X =>
      show (cliffordActionCircuit [.S i, .S i] p).word k = p.word k
      exact cliffordActionCircuit_site_word_ne [.S i, .S i] i k p hk
        (fun g hg => by
          have hg' : g = .S i ∨ g = .S i := by simpa using! hg
          rcases hg' with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inr rfl)
  | Y =>
      show (cliffordActionCircuit [.H i, .S i, .S i, .H i] p).word k = p.word k
      exact cliffordActionCircuit_site_word_ne [.H i, .S i, .S i, .H i] i k p hk
        (fun g hg => by
          have hg' : g = .H i ∨ g = .S i ∨ g = .S i ∨ g = .H i := by simpa using! hg
          rcases hg' with rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact Or.inr rfl
          · exact Or.inl rfl)
  | Z =>
      show (cliffordActionCircuit [.H i, .S i, .S i, .H i] p).word k = p.word k
      exact cliffordActionCircuit_site_word_ne [.H i, .S i, .S i, .H i] i k p hk
        (fun g hg => by
          have hg' : g = .H i ∨ g = .S i ∨ g = .S i ∨ g = .H i := by simpa using! hg
          rcases hg' with rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact Or.inr rfl
          · exact Or.inl rfl)

/-- The sign-flip circuit associated with a site's Pauli letter preserves that letter. -/
theorem signFlipCircuit_word_at {n : ℕ} (i : Fin n) (p : PauliElem n) (a : Pauli1)
    (ha : p.word i = a) : (cliffordActionCircuit (signFlipCircuit i a) p).word i = a := by
  cases a with
  | I =>
      simp [signFlipCircuit, cliffordActionCircuit, ha]
  | X =>
      simp only [signFlipCircuit, cliffordActionCircuit]
      simp only [cliffordAction_S_word]
      simp only [ha, conjSWord]
  | Y =>
      simp only [signFlipCircuit, cliffordActionCircuit]
      simp only [cliffordAction_H_word, cliffordAction_S_word]
      simp only [ha, conjHWord, conjSWord]
  | Z =>
      simp only [signFlipCircuit, cliffordActionCircuit]
      simp only [cliffordAction_H_word, cliffordAction_S_word]
      simp only [ha, conjHWord, conjSWord]

/-- At a nonidentity site letter, the sign-flip circuit adds two to the Pauli phase exponent. -/
theorem signFlipCircuit_phase_at {n : ℕ} (i : Fin n) (p : PauliElem n) (a : Pauli1)
    (ha : p.word i = a) (hne : a ≠ .I) :
    (cliffordActionCircuit (signFlipCircuit i a) p).phase = p.phase + 2 := by
  cases a with
  | I => exact (hne rfl).elim
  | X =>
      simp only [signFlipCircuit, cliffordActionCircuit]
      rw [cliffordAction_S_phase i _, cliffordAction_S_phase i p]
      simp only [cliffordAction_S_word]
      simp only [ha, conjSPhase, conjSWord]
      abel
  | Y =>
      simp only [signFlipCircuit, cliffordActionCircuit]
      rw [cliffordAction_H_phase i _, cliffordAction_S_phase i _, cliffordAction_S_phase i _,
        cliffordAction_H_phase i p]
      simp only [cliffordAction_H_word, cliffordAction_S_word]
      simp only [ha, conjHPhase, conjSPhase, conjHWord, conjSWord]
      abel
  | Z =>
      simp only [signFlipCircuit, cliffordActionCircuit]
      rw [cliffordAction_H_phase i _, cliffordAction_S_phase i _, cliffordAction_S_phase i _,
        cliffordAction_H_phase i p]
      simp only [cliffordAction_H_word, cliffordAction_S_word]
      simp only [ha, conjHPhase, conjSPhase, conjHWord, conjSWord]
      abel

/-- The sign-flip circuit preserves the entire Pauli word. -/
theorem signFlipCircuit_word {n : ℕ} (i : Fin n) (p : PauliElem n) :
    (cliffordActionCircuit (signFlipCircuit i (p.word i)) p).word = p.word := by
  have hat := signFlipCircuit_word_at i p (p.word i) rfl
  funext k
  by_cases hk : k = i
  · rw [hk]
    exact hat
  · exact signFlipCircuit_word_ne i k p hk

/-- Adding an even residue modulo four preserves and reflects membership in the set consisting
of zero and two. -/
theorem even_phase_add {a b : ZMod 4} (hb : b = 0 ∨ b = 2) :
    (a + b = 0 ∨ a + b = 2) ↔ (a = 0 ∨ a = 2) := by
  rcases hb with hb | hb
  · subst hb
    simp
  · subst hb
    rcases zmod4_cases a with h0 | h1 | h2 | h3
    · subst h0; decide
    · subst h1; decide
    · subst h2; decide
    · subst h3; decide

/-- The defined action of any Clifford gate preserves and reflects the Hermitian Pauli
predicate. -/
theorem cliffordAction_hermitian_iff {n : ℕ} (g : CliffordGate n) (p : PauliElem n) :
    IsHermitianPauli (cliffordAction g p) ↔ IsHermitianPauli p := by
  cases g with
  | H i =>
      show (cliffordAction (.H i) p).phase = 0 ∨ (cliffordAction (.H i) p).phase = 2 ↔
        p.phase = 0 ∨ p.phase = 2
      rw [cliffordAction_H_phase]
      exact even_phase_add (conjHPhase_eq (p.word i))
  | S i =>
      show (cliffordAction (.S i) p).phase = 0 ∨ (cliffordAction (.S i) p).phase = 2 ↔
        p.phase = 0 ∨ p.phase = 2
      rw [cliffordAction_S_phase]
      exact even_phase_add (conjSPhase_eq (p.word i))
  | CNOT i j =>
      show (cliffordAction (.CNOT i j) p).phase = 0 ∨ (cliffordAction (.CNOT i j) p).phase = 2 ↔
        p.phase = 0 ∨ p.phase = 2
      rw [cliffordAction_CNOT_phase]

/-- Concatenating Clifford circuits composes their Pauli actions in execution order. -/
theorem cliffordActionCircuit_append {n : ℕ} (c1 c2 : CliffordCircuit n) (p : PauliElem n) :
    cliffordActionCircuit (c1 ++ c2) p = cliffordActionCircuit c2 (cliffordActionCircuit c1 p) := by
  induction c1 generalizing p with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.cons_append, cliffordActionCircuit]
      rw [ih]

/-- The action of any Clifford circuit preserves the Hermitian Pauli predicate. -/
theorem cliffordActionCircuit_hermitian {n : ℕ} (c : CliffordCircuit n) (p : PauliElem n)
    (hp : IsHermitianPauli p) : IsHermitianPauli (cliffordActionCircuit c p) := by
  induction c generalizing p with
  | nil => exact hp
  | cons g gs ih =>
      simp only [cliffordActionCircuit]
      exact ih (cliffordAction g p) (cliffordAction_hermitian g p hp)

/-- Any two nonzero binary symplectic vectors are connected by a legal Clifford circuit when a
register site is specified. -/
theorem pauliDirection_orbit_transitive_legal {n : ℕ} (zero : Fin n)
    (v w : BooleanVec n × BooleanVec n) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ (gs : CliffordCircuit n), (∀ g ∈ gs, legalGate g) ∧
      cliffordSymplecticCircuit gs v = w := by
  obtain ⟨g1, h1⟩ := pauliDirection_to_unit zero v hv
  obtain ⟨g2, h2⟩ := pauliDirection_to_unit zero w hw
  refine ⟨g1 ++ g2.reverse, ?_, ?_⟩
  · intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact h1.1 g hg
    · rw [List.mem_reverse] at hg
      exact h2.1 g hg
  · rw [cliffordSymplecticCircuit_append, h1.2]
    have hinv := cliffordSymplecticCircuit_inv g2 h2.1 w
    rw [h2.2] at hinv
    exact hinv

/-- Every Pauli element with nontrivial word can be mapped to its negative by a Clifford
circuit. -/
theorem cliffordSignFlip {n : ℕ} (p : PauliElem n) (hw : p.word ≠ trivialWord) :
    ∃ (c : CliffordCircuit n), cliffordActionCircuit c p = negPauliElem p := by
  have hne : ∃ i : Fin n, p.word i ≠ .I := by
    by_contra h
    refine hw (funext fun i => ?_)
    by_contra hni
    exact h ⟨i, hni⟩
  obtain ⟨i, hi⟩ := hne
  refine ⟨signFlipCircuit i (p.word i), ?_⟩
  apply pauli_ext
  · exact signFlipCircuit_word i p
  · exact signFlipCircuit_phase_at i p (p.word i) rfl hi

/-- The phase exponents of two Hermitian Pauli elements are equal or differ by two. -/
theorem phase_eq_or_add_two {n : ℕ} {p q : PauliElem n}
    (hp : IsHermitianPauli p) (hq : IsHermitianPauli q) :
    p.phase = q.phase ∨ p.phase = q.phase + 2 := by
  rcases hp with hp0 | hp2
  · rcases hq with hq0 | hq2
    · exact Or.inl (hp0.trans hq0.symm)
    · exact Or.inr (by rw [hp0, hq2]; decide)
  · rcases hq with hq0 | hq2
    · exact Or.inr (by rw [hp2, hq0]; decide)
    · exact Or.inl (hp2.trans hq2.symm)

/-- Any two Hermitian Pauli elements with nontrivial words are connected by a Clifford circuit
under the defined Pauli action. -/
theorem cliffordOrbit_eq {n : ℕ} (σ : PauliElem n) (hσ : IsHermitianPauli σ)
    (hwσ : σ.word ≠ trivialWord) :
    ∀ (τ : PauliElem n), IsHermitianPauli τ → τ.word ≠ trivialWord →
      ∃ (c : CliffordCircuit n), cliffordActionCircuit c σ = τ := by
  intro τ hτ hwτ
  have hn : 0 < n := by
    by_contra h
    have hz : n = 0 := Nat.eq_zero_of_not_pos h
    subst hz
    exact hwτ (funext fun i => nomatch i)
  obtain ⟨zero, hzero⟩ : ∃ z : Fin n, True := ⟨⟨0, by omega⟩, trivial⟩
  have hv : symplecticVec σ.word ≠ 0 :=
    fun h => hwσ (symplecticVec_eq_zero_iff.mp h)
  have hw : symplecticVec τ.word ≠ 0 :=
    fun h => hwτ (symplecticVec_eq_zero_iff.mp h)
  obtain ⟨c1, hlegal, hc1⟩ := pauliDirection_orbit_transitive_legal zero
    (symplecticVec σ.word) (symplecticVec τ.word) hv hw
  have hsym : symplecticVec (cliffordActionCircuit c1 σ).word = symplecticVec τ.word := by
    rw [symplecticVec_cliffordActionCircuit c1 hlegal σ]
    exact hc1
  have hword : (cliffordActionCircuit c1 σ).word = τ.word := symplecticVec_injective hsym
  have hherm : IsHermitianPauli (cliffordActionCircuit c1 σ) :=
    cliffordActionCircuit_hermitian c1 σ hσ
  rcases phase_eq_or_add_two hherm hτ with heq | hdiff
  · refine ⟨c1, ?_⟩
    apply pauli_ext
    · exact hword
    · exact heq
  · have hne : ∃ i : Fin n, τ.word i ≠ .I := by
      by_contra h
      refine hwτ (funext fun i => ?_)
      by_contra hni
      exact h ⟨i, hni⟩
    obtain ⟨i, hi⟩ := hne
    refine ⟨c1 ++ signFlipCircuit i (τ.word i), ?_⟩
    rw [cliffordActionCircuit_append]
    have hcirc : signFlipCircuit i (τ.word i)
        = signFlipCircuit i ((cliffordActionCircuit c1 σ).word i) :=
      congrArg (fun a => signFlipCircuit i a) (congrArg (fun w => w i) hword.symm)
    rw [hcirc]
    apply pauli_ext
    · rw [signFlipCircuit_word i (cliffordActionCircuit c1 σ), hword]
    · have hph : (cliffordActionCircuit (signFlipCircuit i ((cliffordActionCircuit c1 σ).word i))
          (cliffordActionCircuit c1 σ)).phase = (cliffordActionCircuit c1 σ).phase + 2 := by
        apply signFlipCircuit_phase_at i (cliffordActionCircuit c1 σ) _ rfl
        exact hword ▸ hi
      rw [hph, hdiff]
      abel

/-- A real-valued function invariant under each Clifford gate is invariant under every Clifford
circuit. -/
theorem cliffordInvariant_const_on_circuit {n : ℕ} (w : PauliElem n → ℝ)
    (hinv : ∀ (g : CliffordGate n) (p : PauliElem n), w (cliffordAction g p) = w p) :
    ∀ (c : CliffordCircuit n) (p : PauliElem n), w (cliffordActionCircuit c p) = w p := by
  intro c
  induction c with
  | nil => intro p; rfl
  | cons g gs ih =>
      intro p
      simp only [cliffordActionCircuit]
      rw [ih, hinv]

/-- A real-valued function invariant under each Clifford gate takes equal values on elements
connected by a Clifford circuit. -/
theorem cliffordInvariant_const_on_orbit {n : ℕ} (w : PauliElem n → ℝ)
    (hinv : ∀ (g : CliffordGate n) (p : PauliElem n), w (cliffordAction g p) = w p)
    {σ τ : PauliElem n} (hτ : ∃ c : CliffordCircuit n, cliffordActionCircuit c σ = τ) :
    w σ = w τ := by
  obtain ⟨c, hc⟩ := hτ
  have h := cliffordInvariant_const_on_circuit w hinv c σ
  rw [hc] at h
  exact h.symm

/-- A real-valued function invariant under every Clifford gate is constant on Hermitian Pauli
elements with nontrivial words. -/
theorem pauliMixing_equal {n : ℕ} (w : PauliElem n → ℝ)
    (hinv : ∀ (g : CliffordGate n) (p : PauliElem n), w (cliffordAction g p) = w p)
    (σ τ : PauliElem n) (hσ : IsHermitianPauli σ) (hwσ : σ.word ≠ trivialWord)
    (hτ : IsHermitianPauli τ) (hwτ : τ.word ≠ trivialWord) : w σ = w τ := by
  obtain ⟨c, hc⟩ := cliffordOrbit_eq σ hσ hwσ τ hτ hwτ
  exact cliffordInvariant_const_on_orbit w hinv ⟨c, hc⟩

/-- Identifies a Pauli element with its word and phase exponent. -/
def pauliElemEquiv (n : ℕ) : PauliElem n ≃ (PauliWord n × ZMod 4) where
  toFun p := (p.word, p.phase)
  invFun := fun x => ⟨x.1, x.2⟩
  left_inv := by
    intro p
    cases p
    rfl
  right_inv := by
    intro x
    rcases x with ⟨w, φ⟩
    rfl

instance pauliElemFintype (n : ℕ) : Fintype (PauliElem n) :=
  Fintype.ofEquiv (PauliWord n × ZMod 4) (pauliElemEquiv n).symm

instance instDecidableIsHermitianPauli {n : ℕ} (p : PauliElem n) : Decidable (IsHermitianPauli p) :=
  inferInstanceAs (Decidable (p.phase = 0 ∨ p.phase = 2))

/-- Casting the natural number `4 ^ n - 1` to the reals agrees with real exponentiation followed
by subtraction. -/
theorem cast_pred_pow_four (n : ℕ) : ((4 : ℕ) ^ n - 1 : ℝ) = (4 : ℝ) ^ n - 1 := by
  have hle : (1 : ℕ) ≤ 4 ^ n := by
    cases n with
    | zero => simp
    | succ k =>
        rw [Nat.pow_succ]
        exact Nat.succ_le_of_lt (by positivity)
  simp

/-- There are two even phase exponents in `ZMod 4`. -/
theorem card_evenPhase : Fintype.card {φ : ZMod 4 // φ = 0 ∨ φ = 2} = 2 := by
  decide

/-- There are `4 ^ n - 1` nontrivial Pauli words on `n` sites. -/
theorem card_nontrivialWord (n : ℕ) :
    Fintype.card {w : PauliWord n // w ≠ trivialWord} = 4 ^ n - 1 := by
  have h1 : Fintype.card {w : PauliWord n // w ≠ trivialWord}
      = Fintype.card (PauliWord n) - Fintype.card {w : PauliWord n // w = trivialWord} :=
    Fintype.card_subtype_compl (fun w : PauliWord n => w = trivialWord)
  have h1b : Fintype.card {w : PauliWord n // w = trivialWord} = 1 :=
    Fintype.card_subtype_eq trivialWord
  have h2 : Fintype.card (PauliWord n) = 4 ^ n := by
    have h3 : Fintype.card Pauli1 = 4 := by decide
    show Fintype.card (Fin n → Pauli1) = 4 ^ n
    rw [Fintype.card_fun, Fintype.card_fin, h3]
  rw [h1, h1b, h2]

/-- Identifies Hermitian Pauli elements with nontrivial words with pairs of an even phase
exponent and a nontrivial word. -/
def nontrivHermEquiv (n : ℕ) :
    {p : PauliElem n // IsHermitianPauli p ∧ p.word ≠ trivialWord}
      ≃ ({φ : ZMod 4 // φ = 0 ∨ φ = 2} × {w : PauliWord n // w ≠ trivialWord}) where
  toFun p := (⟨p.1.phase, p.2.1⟩, ⟨p.1.word, p.2.2⟩)
  invFun x := ⟨⟨x.2.1, x.1.1⟩, ⟨x.1.2, x.2.2⟩⟩
  left_inv := by
    intro p
    apply Subtype.ext
    rcases p with ⟨p, hp⟩
    cases p
    rfl
  right_inv := by
    intro x
    rcases x with ⟨⟨φ, hφ⟩, ⟨w, hw⟩⟩
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl

/-- There are `2 * (4 ^ n - 1)` Hermitian Pauli elements with nontrivial words. -/
theorem card_nontrivialHermitianPauli (n : ℕ) :
    Fintype.card {p : PauliElem n // IsHermitianPauli p ∧ p.word ≠ trivialWord}
      = 2 * (4 ^ n - 1) := by
  have h := Fintype.card_congr (nontrivHermEquiv n)
  rw [h, Fintype.card_prod, card_evenPhase, card_nontrivialWord]

/-- Every Clifford binary symplectic map fixes zero. -/
theorem cliffordSymplecticMap_zero {n : ℕ} (g : CliffordGate n) :
    cliffordSymplecticMap g 0 = 0 := by
  rcases g with g | g | g
  · simp only [cliffordSymplecticMap]
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · funext j; simp
    · funext j; simp
  · simp only [cliffordSymplecticMap]
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · funext j; simp
    · funext j; simp
  · simp only [cliffordSymplecticMap]
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · funext j; simp
    · funext j; simp

/-- Every Clifford circuit's binary symplectic action fixes zero. -/
theorem cliffordSymplecticCircuit_zero {n : ℕ} (gs : CliffordCircuit n) :
    cliffordSymplecticCircuit gs 0 = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      simp only [cliffordSymplecticCircuit]
      rw [cliffordSymplecticMap_zero, ih]

/-- The subtype of Hermitian Pauli elements whose words are nontrivial. -/
abbrev PauliSector (n : ℕ) := {p : PauliElem n // IsHermitianPauli p ∧ p.word ≠ trivialWord}

/-- The constant weight on `PauliSector n` equal to the reciprocal of its cardinality. -/
noncomputable def pauliMixingMeasure (n : ℕ) : PauliSector n → ℝ :=
  fun _ => (Fintype.card (PauliSector n) : ℝ)⁻¹

/-- Every weight assigned by `pauliMixingMeasure` is nonnegative. -/
theorem pauliMixingMeasure_nonneg (n : ℕ) (q : PauliSector n) : 0 ≤ pauliMixingMeasure n q := by
  simp [pauliMixingMeasure]

/-- The mixing measure assigns the same weight to every pair of sector elements. -/
theorem pauliMixingMeasure_const (n : ℕ) (q q' : PauliSector n) :
    pauliMixingMeasure n q = pauliMixingMeasure n q' := rfl

/-- The Pauli sector has cardinality `2 * (4 ^ n - 1)`. -/
theorem card_pauliSector (n : ℕ) : Fintype.card (PauliSector n) = 2 * (4 ^ n - 1) := by
  exact card_nontrivialHermitianPauli n

/-- The Pauli-sector cardinality equals the number of all Pauli elements satisfying its defining
predicate. -/
theorem card_pauliSector_filter (n : ℕ) :
    Fintype.card (PauliSector n)
      = (Finset.univ.filter (fun p : PauliElem n => IsHermitianPauli p ∧ p.word ≠ trivialWord)).card :=
  Fintype.card_subtype _

/-- The Pauli sector has positive cardinality when the number of qubits is positive. -/
theorem card_pauliSector_pos (n : ℕ) (h : 0 < n) : 0 < Fintype.card (PauliSector n) := by
  rw [card_pauliSector]
  have h4 : 4 ≤ 4 ^ n := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ]
    have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by decide : (0 : ℕ) < 4)
    omega
  have hlt : 1 < 4 ^ n := by omega
  have hpos : 0 < 4 ^ n - 1 := (Nat.sub_pos_iff_lt).mpr hlt
  exact Nat.mul_pos (by decide : (0 : ℕ) < 2) hpos

/-- For a positive number of qubits, the sector mixing weights sum to one. -/
theorem pauliMixingMeasure_sum_one (n : ℕ) (h : 0 < n) :
    (∑ q : PauliSector n, pauliMixingMeasure n q) = 1 := by
  have hpos : (0 : ℝ) < Fintype.card (PauliSector n) := by
    exact_mod_cast card_pauliSector_pos n h
  have hne : (Fintype.card (PauliSector n) : ℝ) ≠ 0 := ne_of_gt hpos
  calc (∑ q : PauliSector n, pauliMixingMeasure n q)
      = (Fintype.card (PauliSector n) : ℝ) * (Fintype.card (PauliSector n) : ℝ)⁻¹ := by
        simp [pauliMixingMeasure, Finset.sum_const]
    _ = 1 := mul_inv_cancel₀ hne

/-- Extends the constant sector weight to all Pauli elements by assigning zero outside the
Hermitian nontrivial sector. -/
noncomputable def pauliMixingProb (n : ℕ) (p : PauliElem n) : ℝ :=
  if IsHermitianPauli p ∧ p.word ≠ trivialWord then
    (Fintype.card (PauliSector n) : ℝ)⁻¹
  else 0

/-- The extended mixing weight is nonnegative for every Pauli element. -/
theorem pauliMixingProb_nonneg (n : ℕ) (p : PauliElem n) : 0 ≤ pauliMixingProb n p := by
  by_cases h : IsHermitianPauli p ∧ p.word ≠ trivialWord
  · simp [pauliMixingProb, h]
  · simp [pauliMixingProb, h]

/-- On the Pauli sector, the extended mixing weight agrees with `pauliMixingMeasure`. -/
theorem pauliMixingProb_of_sector (n : ℕ) (q : PauliSector n) :
    pauliMixingProb n q.1 = pauliMixingMeasure n q := by
  simp [pauliMixingProb, q.2.1, q.2.2, pauliMixingMeasure]

/-- For a positive number of qubits, the extended mixing weights over all Pauli elements sum to
one. -/
theorem pauliMixingProb_sum_one (n : ℕ) (h : 0 < n) :
    (∑ p : PauliElem n, pauliMixingProb n p) = 1 := by
  have hpos : (0 : ℝ) < Fintype.card (PauliSector n) := by
    exact_mod_cast card_pauliSector_pos n h
  have hne : (Fintype.card (PauliSector n) : ℝ) ≠ 0 := ne_of_gt hpos
  have h1 : (∑ p : PauliElem n, pauliMixingProb n p)
      = Finset.sum ((Finset.univ : Finset (PauliElem n)).filter
          (fun p => IsHermitianPauli p ∧ p.word ≠ trivialWord))
          (fun _ => (Fintype.card (PauliSector n) : ℝ)⁻¹) := by
    simp only [pauliMixingProb]
    rw [Finset.sum_filter]
  calc (∑ p : PauliElem n, pauliMixingProb n p)
      = Finset.sum ((Finset.univ : Finset (PauliElem n)).filter
          (fun p => IsHermitianPauli p ∧ p.word ≠ trivialWord))
          (fun _ => (Fintype.card (PauliSector n) : ℝ)⁻¹) := h1
    _ = ((Finset.univ : Finset (PauliElem n)).filter
          (fun p => IsHermitianPauli p ∧ p.word ≠ trivialWord)).card
          * (Fintype.card (PauliSector n) : ℝ)⁻¹ := by
        simp [Finset.sum_const]
    _ = (Fintype.card (PauliSector n) : ℝ) * (Fintype.card (PauliSector n) : ℝ)⁻¹ := by
        rw [card_pauliSector_filter]
    _ = 1 := mul_inv_cancel₀ hne

/-- The defined action of any Clifford circuit preserves and reflects the Hermitian Pauli
predicate. -/
theorem cliffordActionCircuit_hermitian_iff {n : ℕ} (c : CliffordCircuit n) (p : PauliElem n) :
    IsHermitianPauli (cliffordActionCircuit c p) ↔ IsHermitianPauli p := by
  induction c generalizing p with
  | nil => simp [cliffordActionCircuit]
  | cons g gs ih =>
      rw [cliffordActionCircuit]
      exact Iff.trans (ih (cliffordAction g p)) (cliffordAction_hermitian_iff g p)

/-- A legal Clifford circuit sends a Pauli word to the trivial word exactly when the original
word is trivial. -/
theorem cliffordActionCircuit_word_trivial_iff {n : ℕ} (c : CliffordCircuit n)
    (hc : ∀ g ∈ c, legalGate g) (p : PauliElem n) :
    (cliffordActionCircuit c p).word = trivialWord ↔ p.word = trivialWord := by
  have hsym : symplecticVec (cliffordActionCircuit c p).word
      = cliffordSymplecticCircuit c (symplecticVec p.word) :=
    symplecticVec_cliffordActionCircuit c hc p
  constructor
  · intro h
    have hz : symplecticVec (cliffordActionCircuit c p).word = 0 :=
      (symplecticVec_eq_zero_iff).mpr h
    rw [hsym] at hz
    have hinj := cliffordSymplecticCircuit_inv c hc (symplecticVec p.word)
    rw [hz] at hinj
    rw [cliffordSymplecticCircuit_zero] at hinj
    exact (symplecticVec_eq_zero_iff).mp hinj.symm
  · intro h
    have hz : symplecticVec p.word = 0 := (symplecticVec_eq_zero_iff).mpr h
    have hz' : symplecticVec (cliffordActionCircuit c p).word = 0 := by
      rw [hsym, hz, cliffordSymplecticCircuit_zero]
    exact (symplecticVec_eq_zero_iff).mp hz'

/-- The action of a legal Clifford circuit preserves membership in the Hermitian nontrivial
Pauli sector. -/
theorem cliffordActionCircuit_mem_sector {n : ℕ} (c : CliffordCircuit n)
    (hc : ∀ g ∈ c, legalGate g) (q : PauliSector n) :
    IsHermitianPauli (cliffordActionCircuit c q.1) ∧
      (cliffordActionCircuit c q.1).word ≠ trivialWord := by
  refine ⟨(cliffordActionCircuit_hermitian_iff c q.1).mpr q.2.1, ?_⟩
  intro h
  exact q.2.2 ((cliffordActionCircuit_word_trivial_iff c hc q.1).mp h)

/-- The extended mixing weight is invariant under every legal Clifford circuit. -/
theorem pauliMixingProb_clifford_invariant {n : ℕ} (c : CliffordCircuit n)
    (hc : ∀ g ∈ c, legalGate g) (p : PauliElem n) :
    pauliMixingProb n (cliffordActionCircuit c p) = pauliMixingProb n p := by
  by_cases h : IsHermitianPauli p ∧ p.word ≠ trivialWord
  · have h2 := cliffordActionCircuit_mem_sector c hc ⟨p, h⟩
    simp [pauliMixingProb, h, h2.1, h2.2]
  · have h3 : ¬ (IsHermitianPauli (cliffordActionCircuit c p) ∧
        (cliffordActionCircuit c p).word ≠ trivialWord) := by
      rintro ⟨hh1, hh2⟩
      exact h ⟨(cliffordActionCircuit_hermitian_iff c p).mp hh1,
        (cliffordActionCircuit_word_trivial_iff c hc p).not.mp hh2⟩
    simp [pauliMixingProb, h, h3]

/-- Negating a Hermitian Pauli element preserves the Hermitian predicate. -/
theorem negPauliElem_hermitian {n : ℕ} (p : PauliElem n) (hp : IsHermitianPauli p) :
    IsHermitianPauli (negPauliElem p) := by
  rcases hp with hp | hp
  · right
    show (negPauliElem p).phase = 2
    simp only [negPauliElem]
    show p.phase + 2 = 2
    rw [hp]
    decide
  · left
    show (negPauliElem p).phase = 0
    simp only [negPauliElem]
    show p.phase + 2 = 0
    rw [hp]
    decide

/-- Negating a Pauli element twice returns the original element. -/
theorem negPauliElem_involutive {n : ℕ} (p : PauliElem n) :
    negPauliElem (negPauliElem p) = p := by
  apply pauli_ext
  · rfl
  · show p.phase + 2 + 2 = p.phase
    abel

/-- The operator represented by `negPauliElem p` is the negative of `op p`. -/
theorem op_negPauliElem {n : ℕ} (p : PauliElem n) : op (negPauliElem p) = -op p := by
  have hq : PauliElem.mul p (⟨fun _ : Fin n => Pauli1.I, 2⟩ : PauliElem n) = negPauliElem p := by
    apply pauli_ext
    · rw [pauliElem_mul_word]
      show p.word * (fun _ : Fin n => Pauli1.I) = p.word
      rw [show (fun _ : Fin n => Pauli1.I) = (1 : PauliWord n) by funext i; rfl, mul_one]
    · show p.phase + 2 + (∑ i, pauliMulPhase (p.word i) Pauli1.I) = p.phase + 2
      simp [pauliMulPhase_right_I]
  rw [← hq, op_mul]
  have hone : op (⟨fun _ : Fin n => Pauli1.I, 2⟩ : PauliElem n)
      = -(1 : Matrix (Reg n) (Reg n) ℂ) := by
    rw [op_trivial_word, zmod4_val_two, I_pow_two, neg_one_eq_smul_one, neg_smul, one_smul]
  rw [hone]
  simp

/-- The involutive equivalence of the Pauli sector induced by Pauli negation. -/
def sectorNegEquiv (n : ℕ) : PauliSector n ≃ PauliSector n where
  toFun q := ⟨negPauliElem q.1, ⟨negPauliElem_hermitian q.1 q.2.1, q.2.2⟩⟩
  invFun q := ⟨negPauliElem q.1, ⟨negPauliElem_hermitian q.1 q.2.1, q.2.2⟩⟩
  left_inv q := by
    apply Subtype.ext
    exact negPauliElem_involutive q.1
  right_inv q := by
    apply Subtype.ext
    exact negPauliElem_involutive q.1

/-- The sum of the operators over the Hermitian nontrivial Pauli sector is zero. -/
theorem sum_op_sector_eq_zero (n : ℕ) : (∑ q : PauliSector n, op q.1) = 0 := by
  have hpoint : ∀ q : PauliSector n, op ((sectorNegEquiv n) q).1 = -(op q.1) := by
    intro q
    show op (negPauliElem q.1) = -(op q.1)
    rw [op_negPauliElem]
  have hS : (∑ q : PauliSector n, op q.1) = -(∑ q : PauliSector n, op q.1) := by
    calc (∑ q : PauliSector n, op q.1)
        = ∑ q : PauliSector n, op ((sectorNegEquiv n) q).1 :=
          (Equiv.sum_comp (sectorNegEquiv n) (fun q : PauliSector n => op q.1)).symm
      _ = ∑ q : PauliSector n, -(op q.1) := by simp_rw [hpoint]
      _ = -(∑ q : PauliSector n, op q.1) := by rw [Finset.sum_neg_distrib]
  have hSS : (∑ q : PauliSector n, op q.1) + (∑ q : PauliSector n, op q.1) = 0 := by
    calc (∑ q : PauliSector n, op q.1) + (∑ q : PauliSector n, op q.1)
        = -(∑ q : PauliSector n, op q.1) + (∑ q : PauliSector n, op q.1) :=
          congrArg (fun s => s + (∑ q : PauliSector n, op q.1)) hS
      _ = 0 := by simp
  apply Matrix.ext
  intro i j
  have hij : (∑ q : PauliSector n, op q.1) i j + (∑ q : PauliSector n, op q.1) i j = 0 := by
    have h := congrFun (congrFun hSS i) j
    simpa [Matrix.add_apply, Matrix.zero_apply] using! h
  have hz : (2 : ℂ) * (∑ q : PauliSector n, op q.1) i j = 0 := by
    rw [← smul_eq_mul, two_smul]
    exact hij
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

/-- The uniform average of the operator matrices over the Hermitian nontrivial Pauli sector. -/
noncomputable def pauliSectorUniformAverage (n : ℕ) : Matrix (Reg n) (Reg n) ℂ :=
  ∑ q : PauliSector n, (Fintype.card (PauliSector n) : ℂ)⁻¹ • op q.1

/-- The uniform average of Pauli-sector operator matrices is zero. -/
theorem pauliSectorUniformAverage_eq_zero (n : ℕ) : pauliSectorUniformAverage n = 0 := by
  rw [pauliSectorUniformAverage, ← Finset.smul_sum, sum_op_sector_eq_zero, smul_zero]

/-- Returns the operator of the triple product when its word is trivial, and the uniform sector
average otherwise. -/
noncomputable def pauliThirdMoment {n : ℕ} (P1 P2 P3 : PauliElem n) : Matrix (Reg n) (Reg n) ℂ :=
  if (P1 * P2 * P3).word = trivialWord then
    op (P1 * P2 * P3)
  else
    pauliSectorUniformAverage n

/-- For a triple product with trivial word, `pauliThirdMoment` equals its operator matrix. -/
theorem pauliThirdMoment_of_closed {n : ℕ} {P1 P2 P3 : PauliElem n}
    (h : (P1 * P2 * P3).word = trivialWord) :
    pauliThirdMoment P1 P2 P3 = op (P1 * P2 * P3) := by
  rw [pauliThirdMoment, if_pos h]

/-- For a triple product with nontrivial word, `pauliThirdMoment` is zero. -/
theorem pauliThirdMoment_of_open {n : ℕ} {P1 P2 P3 : PauliElem n}
    (h : (P1 * P2 * P3).word ≠ trivialWord) :
    pauliThirdMoment P1 P2 P3 = 0 := by
  rw [pauliThirdMoment, if_neg h]
  exact pauliSectorUniformAverage_eq_zero n

/-- The defined third moment is the triple-product operator for trivial product word and zero
otherwise. -/
theorem pauliThirdMoment_eq {n : ℕ} (P1 P2 P3 : PauliElem n) :
    pauliThirdMoment P1 P2 P3
      = if (P1 * P2 * P3).word = trivialWord then op (P1 * P2 * P3) else 0 := by
  by_cases h : (P1 * P2 * P3).word = trivialWord
  · rw [pauliThirdMoment_of_closed h, if_pos h]
  · rw [pauliThirdMoment_of_open h, if_neg h]

/-- The operator matrix of every Pauli element is nonzero. -/
theorem op_ne_zero {n : ℕ} (p : PauliElem n) : op p ≠ 0 := by
  intro h
  have hh := op_mul_ne_zero p p
  rw [h, zero_mul] at hh
  exact absurd rfl hh

/-- The defined third moment is nonzero exactly when the triple product has trivial word. -/
theorem pauliThirdMoment_ne_zero_iff {n : ℕ} (P1 P2 P3 : PauliElem n) :
    pauliThirdMoment P1 P2 P3 ≠ 0 ↔ (P1 * P2 * P3).word = trivialWord := by
  by_cases h : (P1 * P2 * P3).word = trivialWord
  · refine ⟨fun _ => h, fun _ => ?_⟩
    rw [pauliThirdMoment_of_closed h]
    exact op_ne_zero _
  · refine ⟨fun hne => ?_, fun hh => ?_⟩
    · rw [pauliThirdMoment_of_open h] at hne
      exact (hne rfl).elim
    · exact (h hh).elim

/-- Returns the operator of the pair product when its word is trivial, and the uniform sector
average otherwise. -/
noncomputable def pauliSecondMoment {n : ℕ} (P1 P2 : PauliElem n) : Matrix (Reg n) (Reg n) ℂ :=
  if (P1 * P2).word = trivialWord then
    op (P1 * P2)
  else
    pauliSectorUniformAverage n

/-- For a pair product with trivial word, `pauliSecondMoment` equals its operator matrix. -/
theorem pauliSecondMoment_of_closed {n : ℕ} {P1 P2 : PauliElem n}
    (h : (P1 * P2).word = trivialWord) :
    pauliSecondMoment P1 P2 = op (P1 * P2) := by
  rw [pauliSecondMoment, if_pos h]

/-- For a pair product with nontrivial word, `pauliSecondMoment` is zero. -/
theorem pauliSecondMoment_of_open {n : ℕ} {P1 P2 : PauliElem n}
    (h : (P1 * P2).word ≠ trivialWord) :
    pauliSecondMoment P1 P2 = 0 := by
  rw [pauliSecondMoment, if_neg h]
  exact pauliSectorUniformAverage_eq_zero n

/-- A Boolean random tape indexed by `Fin m`. -/
abbrev FairTape (m : ℕ) := Fin m → Bool

/-- The uniform finite distribution on Boolean tapes of length `m`, assigning each tape
probability `(1 / 2) ^ m`. -/
noncomputable def fairTapeLaw (m : ℕ) : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (FairTape m) where
  prob := fun _ => (1 / 2 : ℝ) ^ m
  nonneg := fun _ => by positivity
  sum_one := by
    have hcard : Fintype.card (FairTape m) = 2 ^ m := by
      rw [Fintype.card_fun]
      simp [Fintype.card_bool]
    calc (∑ ω : FairTape m, (1 / 2 : ℝ) ^ m) = (Fintype.card (FairTape m) : ℝ) * ((1 / 2 : ℝ) ^ m) := by
          simp [Finset.sum_const]
      _ = ((2 : ℝ) ^ m) * ((1 / 2 : ℝ) ^ m) := by rw [hcard]; norm_num
      _ = 1 := by
        rw [← mul_pow]
        norm_num

/-- There are `2 ^ m` Boolean tapes of length `m`. -/
theorem card_fairTape (m : ℕ) : Fintype.card (FairTape m) = 2 ^ m := by
  rw [Fintype.card_fun]
  simp [Fintype.card_bool]

/-- Each Boolean tape of length `m` has probability `(1 / 2) ^ m` under `fairTapeLaw`. -/
theorem fairTapeLaw_prob (m : ℕ) (ω : FairTape m) :
    (fairTapeLaw m).prob ω = (1 / 2 : ℝ) ^ m := rfl

/-- The probability of a Boolean tape equals the product of its individual fair-bit
probabilities. -/
theorem fairTapeLaw_prob_eq_product (m : ℕ) (ω : FairTape m) :
    (fairTapeLaw m).prob ω = ∏ i, fairBitLaw.prob (ω i) := by
  simp [fairTapeLaw, fairBitLaw, Finset.prod_const]

/-- A tape of length one gives the same probability to its bit as `fairBitLaw`. -/
theorem clause3TapeBit_is_fairBit (b : Bool) :
    (fairTapeLaw 1).prob (fun _ => b) = fairBitLaw.prob b := by
  simp [fairTapeLaw, fairBitLaw]

/-- Classifies a simulation step as random or deterministic. -/
inductive Clause3StepKind

  | random

  | deterministic
  deriving DecidableEq, Repr

/-- A simulation step specifying a measured Pauli element, a selected tableau row, and a random
or deterministic kind. -/
structure Clause3Step (n m : ℕ) where

  measured : PauliElem n

  row : Fin m

  kind : Clause3StepKind

/-- A simulation result containing the outcome list, final tableau, random-bit count, and
row-update count. -/
structure Clause3SimResult (n m : ℕ) where

  outcomes : List Bool

  finalTableau : Tableau n m

  randomBits : ℕ

  rowUpdates : ℕ

/-- Counts the steps marked random in a simulation-step list. -/
def clause3RandomCount {n m : ℕ} : List (Clause3Step n m) → ℕ
  | [] => 0
  | s :: ss => (if s.kind == .random then 1 else 0) + clause3RandomCount ss

/-- Processes measurement steps using the corresponding tape bit for random steps and true for
deterministic steps, while updating the tableau and operation counts. -/
noncomputable def clause3Simulate {n m : ℕ} (t : Tableau n m) :
    (steps : List (Clause3Step n m)) → (ω : FairTape steps.length) → Clause3SimResult n m
  | [], _ => ⟨[], t, 0, 0⟩
  | s :: ss, ω =>
      let b := if s.kind == .random then ω 0 else true
      let t' := measuredTableau t s.row s.measured b
      let r := clause3Simulate t' ss (fun i => ω i.succ)
      ⟨b :: r.outcomes, r.finalTableau, r.randomBits + (if s.kind == .random then 1 else 0),
        r.rowUpdates + m⟩

/-- The simulator produces exactly one Boolean outcome per step. -/
theorem clause3Simulate_outcomes_length {n m : ℕ} (steps : List (Clause3Step n m)) :
    ∀ (t : Tableau n m) (ω : FairTape steps.length),
      (clause3Simulate t steps ω).outcomes.length = steps.length := by
  induction steps with
  | nil => intro t ω; rfl
  | cons s ss ih =>
      intro t ω
      cases hk : s.kind with
      | random =>
          have h := ih (measuredTableau t s.row s.measured (ω 0)) (fun i => ω i.succ)
          simp [clause3Simulate, hk, h]
      | deterministic =>
          have h := ih (measuredTableau t s.row s.measured true) (fun i => ω i.succ)
          simp [clause3Simulate, hk, h]

/-- The simulator's random-bit count equals the number of steps marked random. -/
theorem clause3Simulate_randomBits_eq {n m : ℕ} (steps : List (Clause3Step n m)) :
    ∀ (t : Tableau n m) (ω : FairTape steps.length),
      (clause3Simulate t steps ω).randomBits = clause3RandomCount steps := by
  induction steps with
  | nil => intro t ω; rfl
  | cons s ss ih =>
      intro t ω
      cases hk : s.kind with
      | random =>
          have h := ih (measuredTableau t s.row s.measured (ω 0)) (fun i => ω i.succ)
          simp [clause3Simulate, hk, h, clause3RandomCount]
          omega
      | deterministic =>
          have h := ih (measuredTableau t s.row s.measured true) (fun i => ω i.succ)
          simp [clause3Simulate, hk, h, clause3RandomCount]

/-- The number of random steps is at most the total number of steps. -/
theorem clause3RandomCount_le {n m : ℕ} : ∀ (steps : List (Clause3Step n m)), clause3RandomCount steps ≤ steps.length := by
  intro steps
  induction steps with
  | nil => simp [clause3RandomCount]
  | cons s ss ih =>
      cases hk : s.kind with
      | random =>
          simp [clause3RandomCount, hk]
          omega
      | deterministic =>
          simp [clause3RandomCount, hk]
          omega

/-- The simulator's random-bit count is at most the number of steps. -/
theorem clause3Simulate_randomBits_le {n m : ℕ} (steps : List (Clause3Step n m)) :
    ∀ (t : Tableau n m) (ω : FairTape steps.length),
      (clause3Simulate t steps ω).randomBits ≤ steps.length := by
  intro t ω
  rw [clause3Simulate_randomBits_eq]
  exact clause3RandomCount_le steps

/-- The simulator records exactly `steps.length * m` row updates. -/
theorem clause3Simulate_rowUpdates {n m : ℕ} (steps : List (Clause3Step n m)) :
    ∀ (t : Tableau n m) (ω : FairTape steps.length),
      (clause3Simulate t steps ω).rowUpdates = steps.length * m := by
  induction steps with
  | nil => intro t ω; simp [clause3Simulate]
  | cons s ss ih =>
      intro t ω
      cases hk : s.kind with
      | random =>
          have h := ih (measuredTableau t s.row s.measured (ω 0)) (fun i => ω i.succ)
          simp [clause3Simulate, hk, h]
          ring
      | deterministic =>
          have h := ih (measuredTableau t s.row s.measured true) (fun i => ω i.succ)
          simp [clause3Simulate, hk, h]
          ring

/-- When the first simulation step is random, its first recorded outcome is the first tape bit. -/
theorem clause3Simulate_first_outcome_random {n m : ℕ} (s : Clause3Step n m) (ss : List (Clause3Step n m))
    (t : Tableau n m) (ω : FairTape (s :: ss).length) (hk : s.kind = .random) :
    (clause3Simulate t (s :: ss) ω).outcomes.head? = some (ω 0) := by
  simp [clause3Simulate, hk]

/-- For a normalized code state, a Hermitian Pauli measurement anticommuting with some tableau
row has the two fair-bit branch probabilities. -/
theorem clause3RandomStep_branch_prob {n m : ℕ} (t : Tableau n m) (ψ : QState (Reg n))
    (hψ : ψ ∈ codeSpace t) (hn : Normalized ψ) (p : PauliElem n) (hp : IsHermitianPauli p)
    (hanti : ∃ a : Fin m, op (t a).decode * op p = - (op p * op (t a).decode)) :
    ProjectiveBranchMass (pauliBranchProjector p true) true ψ = fairBitLaw.prob true ∧
      ProjectiveBranchMass (pauliBranchProjector p true) false ψ = fairBitLaw.prob false :=
  pauliBranchMass_fairBit_of_anticommute_some t ψ hψ hn p hp hanti

/-- The natural representative of zero in `ZMod 2` is zero. -/
theorem zmod2_val_zero : (0 : ZMod 2).val = 0 := rfl

/-- The natural representative of one plus one in `ZMod 2` is zero. -/
theorem zmod2_val_one_add_one : ((1 : ZMod 2) + 1).val = 0 := rfl

/-- The product of the three powers of `Complex.I` with exponents given by two binary residues
and their sum is one or negative one. -/
theorem iPowZ2_triple (z1 z2 : ZMod 2) :
    (Complex.I ^ z1.val : ℂ) * (Complex.I ^ z2.val) * (Complex.I ^ (z1 + z2).val)
      ∈ ({1, -1} : Set ℂ) := by
  rcases zmod2_eq_zero_or_one z1 with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one z2 with rfl | rfl <;>
    simp [zmod2_val_zero, zmod2_val_one, zmod2_val_one_add_one]

/-- Every natural power of complex negative one is one or negative one. -/
theorem negOnePow_mem (k : ℕ) : ((-1 : ℂ)^k) ∈ ({1, -1} : Set ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      rcases ih with ih | ih
      · rw [ih, one_mul]; simp
      · rw [ih, neg_mul]; simp

/-- The product of two complex numbers each equal to one or negative one is again one or
negative one. -/
theorem mul_mem_pm_one {u v : ℂ} (hu : u ∈ ({1, -1} : Set ℂ)) (hv : v ∈ ({1, -1} : Set ℂ)) :
    u * v ∈ ({1, -1} : Set ℂ) := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp

/-- The binary dot product is additive in its right argument. -/
theorem booleanDot_add {n : ℕ} (a x y : BooleanVec n) :
    booleanDot a (x + y) = booleanDot a x + booleanDot a y := by
  simp [booleanDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- For a stabilizer function nonzero at `0`, `x`, `y`, and `x + y`, the product of its values
at these four points is one or negative one. -/
theorem isStabilizerFun_second_difference {n : ℕ} (φ : BooleanVec n → ℂ) (hφ : IsStabilizerFun φ)
    {x y : BooleanVec n} (hx : φ x ≠ 0) (hy : φ y ≠ 0) (hxy : φ (x + y) ≠ 0)
    (h0 : φ 0 ≠ 0) :
    φ x * φ y * φ (x + y) * φ 0 ∈ ({1, -1} : Set ℂ) := by
  obtain ⟨a, Q, b, c, A, hφ'⟩ := hφ
  have hmem (z : BooleanVec n) (hz : φ z ≠ 0) : z ∈ A := by
    by_contra hn
    rw [hφ'] at hz
    simp [hn] at hz
  have hxm : x ∈ A := hmem x hx
  have hym : y ∈ A := hmem y hy
  have hxym : x + y ∈ A := hmem (x + y) hxy
  have h0m : (0 : BooleanVec n) ∈ A := hmem 0 h0
  have hi' : (Complex.I ^ (booleanDot a x).val : ℂ) * Complex.I ^ (booleanDot a y).val
      * Complex.I ^ (booleanDot a (x + y)).val * Complex.I ^ (booleanDot a 0).val
      ∈ ({1, -1} : Set ℂ) := by
    have h0i : Complex.I ^ (booleanDot a 0).val = 1 := by
      rw [booleanDot_zero, zmod2_val_zero, pow_zero]
    have h := iPowZ2_triple (booleanDot a x) (booleanDot a y)
    rw [h0i, booleanDot_add a x y, mul_one]
    exact h
  have hn' : ((-1 : ℂ) ^ (quadFun Q b c x).val) * (-1 : ℂ) ^ (quadFun Q b c y).val
      * (-1 : ℂ) ^ (quadFun Q b c (x + y)).val * (-1 : ℂ) ^ (quadFun Q b c 0).val
      ∈ ({1, -1} : Set ℂ) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    exact negOnePow_mem _
  rw [hφ']
  simp only [hxm, hym, hxym, h0m, if_true, mul_one]
  have heq :
      (Complex.I ^ (booleanDot a x).val * (-1 : ℂ) ^ (quadFun Q b c x).val)
      * (Complex.I ^ (booleanDot a y).val * (-1 : ℂ) ^ (quadFun Q b c y).val)
      * (Complex.I ^ (booleanDot a (x + y)).val * (-1 : ℂ) ^ (quadFun Q b c (x + y)).val)
      * (Complex.I ^ (booleanDot a 0).val * (-1 : ℂ) ^ (quadFun Q b c 0).val)
      = (Complex.I ^ (booleanDot a x).val * Complex.I ^ (booleanDot a y).val
          * Complex.I ^ (booleanDot a (x + y)).val * Complex.I ^ (booleanDot a 0).val)
      * ((-1 : ℂ) ^ (quadFun Q b c x).val * (-1 : ℂ) ^ (quadFun Q b c y).val
          * (-1 : ℂ) ^ (quadFun Q b c (x + y)).val * (-1 : ℂ) ^ (quadFun Q b c 0).val) := by
    ring
  rw [heq]
  exact mul_mem_pm_one hi' hn'

/-- For a stabilizer function nonzero at the origin, the fourth power of its value there is one
or negative one. -/
theorem isStabilizerFun_second_difference_zero {n : ℕ} (φ : BooleanVec n → ℂ)
    (hφ : IsStabilizerFun φ) (h0 : φ 0 ≠ 0) :
    φ 0 * φ 0 * φ 0 * φ 0 ∈ ({1, -1} : Set ℂ) :=
  isStabilizerFun_second_difference φ hφ h0 h0 h0 h0

end Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
