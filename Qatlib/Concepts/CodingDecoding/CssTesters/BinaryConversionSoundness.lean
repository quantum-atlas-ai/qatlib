/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.CssTesters.CssTester
public import Qatlib.Concepts.CodingDecoding.CssTesters.FieldBinaryMatrix
public import Qatlib.Concepts.CodingDecoding.CssTesters.CssCode

@[expose] public section
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode Qatlib.Concepts.CodingDecoding.CssTesters Qatlib.Concepts.CodingDecoding.CssTesters.CssTester
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters.CssTester

open Qatlib.Concepts.CodingDecoding.CssTesters Qatlib.Concepts.CodingDecoding.CssTesters

namespace Qatlib.Concepts.CodingDecoding.CssTesters.BinaryConversionSoundness

open Matrix

open scoped Classical BigOperators ENNReal

section Transfer

variable {F : Type} [Field F] [Algebra (ZMod 2) F] {s : ℕ}
  (e : F ≃ₗ[ZMod 2] (Fin s → ZMod 2))
variable {κ κ' κ'' α : Type} [Fintype κ] [Fintype κ'] [Fintype κ'']
  [DecidableEq κ] [DecidableEq κ'] [DecidableEq κ''] [Fintype α] [DecidableEq α]

def toBinary (x : κ → F) : κ × Fin s → ZMod 2 := fun p => e (x p.1) p.2

def ofBinary (v : κ × Fin s → ZMod 2) : κ → F := fun q => e.symm fun k => v (q, k)

omit [Fintype κ] [DecidableEq κ] in
/-- Converting binary coordinates to field coordinates and back recovers the binary vector. -/
@[simp] theorem toBinary_ofBinary [Fintype κ] [DecidableEq κ] (v : κ × Fin s → ZMod 2) :
    toBinary e (ofBinary e v) = v := by
  funext p
  exact congrFun (e.apply_symm_apply _) p.2

omit [Fintype κ] [DecidableEq κ] in
/-- Converting a field vector to binary coordinates and back recovers the field vector. -/
@[simp] theorem ofBinary_toBinary [Fintype κ] [DecidableEq κ] (x : κ → F) :
    ofBinary e (toBinary e x) = x := by
  funext q
  show e.symm (e (x q)) = x q
  exact e.symm_apply_apply (x q)

omit [Fintype κ] [DecidableEq κ] in
/-- Binary coordinate conversion sends the zero field vector to zero. -/
@[simp] theorem toBinary_zero [Fintype κ] [DecidableEq κ] : toBinary e (0 : κ → F) = 0 := by
  funext p
  simp [toBinary, map_zero]

def binaryEquiv : (κ → F) ≃ₗ[ZMod 2] (κ × Fin s → ZMod 2) where
  toFun x p := e (x p.1) p.2
  map_add' x y := by
    funext p
    show e ((x + y) p.1) p.2 = e (x p.1) p.2 + e (y p.1) p.2
    rw [Pi.add_apply, map_add, Pi.add_apply]
  map_smul' c x := by
    funext p
    show e ((c • x) p.1) p.2 = (c • e (x p.1)) p.2
    rw [Pi.smul_apply, map_smul, Pi.smul_apply]
  invFun v q := e.symm fun k => v (q, k)
  left_inv x := by
    funext q
    show e.symm (e (x q)) = x q
    exact e.symm_apply_apply (x q)
  right_inv v := by
    funext p
    show e (e.symm (fun k => v (p.1, k))) p.2 = v (p.1, p.2)
    rw [e.apply_symm_apply]

omit [Fintype κ] [DecidableEq κ] in
/-- The binary linear equivalence acts by `toBinary`. -/
theorem binaryEquiv_apply [Fintype κ] [DecidableEq κ] (x : κ → F) : binaryEquiv e x = toBinary e x := rfl

omit [Fintype κ] [DecidableEq κ] in
/-- Converting binary coordinates to field vectors preserves addition. -/
theorem ofBinary_add [Fintype κ] [DecidableEq κ] (v1 v2 : κ × Fin s → ZMod 2) :
    ofBinary e (v1 + v2) = ofBinary e v1 + ofBinary e v2 := by
  funext q
  show e.symm (fun k => (v1 + v2) (q, k)) = e.symm (fun k => v1 (q, k)) + e.symm
      (fun k => v2 (q, k))
  rw [← map_add]
  congr 1

omit [Fintype κ] [DecidableEq κ] in
/-- Converting binary coordinates to field vectors preserves scalar multiplication over `ZMod
2`. -/
theorem ofBinary_smul [Fintype κ] [DecidableEq κ] (c : ZMod 2) (v : κ × Fin s → ZMod 2) :
    ofBinary e (c • v) = c • ofBinary e v := by
  funext q
  show e.symm (fun k => (c • v) (q, k)) = c • e.symm (fun k => v (q, k))
  rw [← map_smul]
  congr 1

/-- A field vector has zero binary representation exactly when it is zero. -/
theorem toBinary_eq_zero_iff (y : κ → F) : toBinary e y = 0 ↔ y = 0 := by
  constructor
  · intro h
    have h0 : binaryEquiv e y = binaryEquiv e (0 : κ → F) := by
      rw [binaryEquiv_apply, binaryEquiv_apply, h, toBinary_zero]
    exact (binaryEquiv e).injective h0
  · intro h
    rw [h, toBinary_zero]

/-- The inverse coordinate equivalence reconstructs a field element from its coordinates and the
standard basis images. -/
private theorem symm_single_repr (w : Fin s → ZMod 2) :
    e.symm w = ∑ k, w k • e.symm (Pi.single k 1) := by
  conv_lhs => rw [pi_eq_sum_univ' w]
  simp only [map_sum, map_smul]

/-- Multiplying a field element by a coordinate expansion gives the stated sum of scaled basis
products. -/
private theorem coord_repr (a x : F) :
    a * x = ∑ k : Fin s, e x k • (a * e.symm (Pi.single k 1)) := by
  conv_lhs => rw [← e.symm_apply_apply x, symm_single_repr e (e x)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, mul_left_comm]

omit [DecidableEq κ] [DecidableEq κ'] in
/-- The binary matrix acts on converted vectors exactly as converting the original matrix-vector
product. -/
theorem binaryMatrix_mulVec [DecidableEq κ] [DecidableEq κ'] (M : Matrix κ' κ F) (x : κ → F) :
    binaryMatrix s e M *ᵥ toBinary e x = toBinary e (M *ᵥ x) := by
  funext r
  simp only [Matrix.mulVec, dotProduct, toBinary, binaryMatrix]
  have hR : e (∑ q : κ, M r.1 q * x q) r.2 = ∑ q : κ, e (M r.1 q * x q) r.2 := by
    rw [map_sum e fun q : κ => M r.1 q * x q, Finset.sum_apply]
  rw [Fintype.sum_prod_type, hR]
  dsimp only
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [coord_repr e (M r.1 q) (x q),
    map_sum e fun k : Fin s => e (x q) k • (M r.1 q * e.symm (Pi.single k 1)),
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul e, Pi.smul_apply,
    smul_eq_mul (M r.1 q) (e.symm (Pi.single k 1)), mul_comm, smul_eq_mul]

/-- A binary vector lies in the binary matrix kernel exactly when its field reconstruction lies
in the original matrix kernel. -/
theorem binaryMatrix_mulVec_eq_zero_iff (M : Matrix κ' κ F) (v : κ × Fin s → ZMod 2) :
    binaryMatrix s e M *ᵥ v = 0 ↔ M *ᵥ ofBinary e v = 0 := by
  have h : binaryMatrix s e M *ᵥ v = toBinary e (M *ᵥ ofBinary e v) := by
    rw [← binaryMatrix_mulVec e M (ofBinary e v), toBinary_ofBinary]
  rw [h, toBinary_eq_zero_iff]

/-- Membership in the binary matrix range is equivalent to membership of the reconstructed
vector in the original matrix range. -/
theorem mem_range_binaryMatrix_iff (M : Matrix κ' κ F) (v : κ' × Fin s → ZMod 2) :
    v ∈ LinearMap.range (Matrix.mulVecLin (binaryMatrix s e M)) ↔
      ofBinary e v ∈ LinearMap.range (Matrix.mulVecLin M) := by
  constructor
  · rintro ⟨w, hw⟩
    rw [Matrix.mulVecLin_apply] at hw
    have hkey : binaryMatrix s e M *ᵥ w = toBinary e (M *ᵥ ofBinary e w) := by
      rw [← binaryMatrix_mulVec e M (ofBinary e w), toBinary_ofBinary]
    refine ⟨ofBinary e w, ?_⟩
    rw [Matrix.mulVecLin_apply, ← hw, hkey, ofBinary_toBinary]
  · rintro ⟨y, hy⟩
    rw [Matrix.mulVecLin_apply] at hy
    refine ⟨toBinary e y, ?_⟩
    rw [Matrix.mulVecLin_apply, binaryMatrix_mulVec, hy, toBinary_ofBinary]

/-- Multiplication by a standard basis vector selects the corresponding matrix column entry. -/
private theorem mulVec_single_entry {R : Type} [CommRing R] {m n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix m n R) (a : m) (b : n) :
    (M *ᵥ Pi.single b 1) a = M a b := by
  simp only [Matrix.mulVec, dotProduct]
  refine (Finset.sum_eq_single b ?_ ?_).trans ?_
  · intro c _ hcb
    simp [hcb]
  · intro hb
    exact absurd (Finset.mem_univ b) hb
  · simp

/-- Binary conversion preserves a zero product of compatible matrices. -/
theorem binaryMatrix_mul_eq_zero (A : Matrix κ' κ F) (B : Matrix κ κ'' F)
    (hAB : A * B = 0) :
    binaryMatrix s e A * binaryMatrix s e B = 0 := by
  have h : ∀ w : κ'' × Fin s → ZMod 2, (binaryMatrix s e A * binaryMatrix s e B) *ᵥ w = 0 := by
    intro w
    have hB : binaryMatrix s e B *ᵥ w = toBinary e (B *ᵥ ofBinary e w) := by
      rw [← binaryMatrix_mulVec e B (ofBinary e w), toBinary_ofBinary]
    rw [← Matrix.mulVec_mulVec, hB, binaryMatrix_mulVec, Matrix.mulVec_mulVec, hAB,
      Matrix.zero_mulVec, toBinary_zero]
  ext p q
  have hentry := mulVec_single_entry (binaryMatrix s e A * binaryMatrix s e B) p q
  rw [h (Pi.single q 1)] at hentry
  simpa using hentry.symm

end Transfer

section Dual

variable {F : Type} [Field F] [Algebra (ZMod 2) F] [Module.Finite (ZMod 2) F] {s : ℕ}
  [NeZero s] (e : F ≃ₗ[ZMod 2] (Fin s → ZMod 2))
variable {κ κ' : Type} [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ']

private def multMat (a : F) : Matrix (Fin s) (Fin s) (ZMod 2) :=
  Matrix.of fun i k => e (a * e.symm (Pi.single k 1)) i

omit [Module.Finite (ZMod 2) F] [NeZero s] in
/-- The multiplication matrix of a field product is the product of the multiplication matrices. -/
private theorem multMat_mul [Module.Finite (ZMod 2) F] [NeZero s] (a b : F) : multMat e (a * b) = multMat e a * multMat e b := by
  ext i k
  simp only [Matrix.mul_apply, multMat, Matrix.of_apply]
  have hR : e (a * (b * e.symm (Pi.single k 1))) i =
      ∑ j : Fin s, e (e (b * e.symm (Pi.single k 1)) j • (a * e.symm (Pi.single j 1))) i := by
    rw [coord_repr e a (b * e.symm (Pi.single k 1)),
      map_sum e fun j : Fin s => e (b * e.symm (Pi.single k 1)) j • (a * e.symm (Pi.single j 1)),
      Finset.sum_apply]
  rw [mul_assoc, hR]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

omit [Module.Finite (ZMod 2) F] [NeZero s] in
/-- The multiplication matrix of the field identity is the identity matrix. -/
private theorem multMat_one [Module.Finite (ZMod 2) F] [NeZero s] : multMat e 1 = 1 := by
  ext i k
  simp [multMat, one_mul, Matrix.one_apply, Pi.single_apply]

/-- The transpose multiplication matrix of a nonzero field element sends every nonzero binary
vector to a nonzero vector. -/
private theorem multMat_mulVec_cancel (a : F) (ha : a ≠ 0)
    (w : Fin s → ZMod 2) (hw : w ≠ 0) :
    (multMat e a)ᵀ *ᵥ w ≠ 0 := by
  intro h0
  apply hw
  have h1 : (multMat e a⁻¹)ᵀ *ᵥ ((multMat e a)ᵀ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← multMat_mul,
      mul_inv_cancel₀ ha, multMat_one]
    simp
  rw [h0, Matrix.mulVec_zero] at h1
  exact h1.symm

private def toDualLin : F →ₗ[ZMod 2] (Fin s → ZMod 2) where
  toFun u := (multMat e u)ᵀ *ᵥ Pi.single 0 1
  map_add' u v := by
    show (multMat e (u + v))ᵀ *ᵥ Pi.single 0 1 = (multMat e u)ᵀ *ᵥ Pi.single 0 1 +
      (multMat e v)ᵀ *ᵥ Pi.single 0 1
    have h : multMat e (u + v) = multMat e u + multMat e v := by
      ext i k
      simp only [multMat, Matrix.of_apply, Matrix.add_apply, add_mul, map_add,
        Pi.add_apply]
    rw [h, Matrix.transpose_add, Matrix.add_mulVec]
  map_smul' c u := by
    show (multMat e (c • u))ᵀ *ᵥ Pi.single 0 1 = c • (multMat e u)ᵀ *ᵥ Pi.single 0 1
    have h : multMat e (c • u) = c • multMat e u := by
      ext i k
      simp only [multMat, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply,
        smul_mul_assoc, map_smul]
    rw [h, Matrix.transpose_smul, Matrix.smul_mulVec]

/-- The field-to-dual linear map `toDualLin` is injective. -/
private theorem toDual_injective : Function.Injective ⇑(toDualLin e) := by
  intro u1 u2 h
  by_contra hne
  have hkey : (multMat e (u1 - u2))ᵀ *ᵥ (Pi.single 0 1 : Fin s → ZMod 2) = 0 := by
    have hm : toDualLin e (u1 - u2) = 0 := by
      rw [map_sub, h, sub_self]
    exact hm
  exact absurd hkey
    (multMat_mulVec_cancel e (u1 - u2) (sub_ne_zero_of_ne hne) _ (by simp))

/-- The field-to-dual linear map `toDualLin` is surjective. -/
private theorem toDual_surjective : Function.Surjective ⇑(toDualLin e) := by
  have hfr : Module.finrank (ZMod 2) F = Module.finrank (ZMod 2) (Fin s → ZMod 2) :=
    e.finrank_eq
  have hinj : LinearMap.ker (toDualLin e) = ⊥ := LinearMap.ker_eq_bot.mpr (toDual_injective e)
  have hrange : LinearMap.range (toDualLin e) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have hsum := LinearMap.finrank_range_add_finrank_ker (toDualLin e)
    rw [hinj] at hsum
    simp only [finrank_bot, add_zero] at hsum
    exact hsum.trans hfr
  exact LinearMap.range_eq_top.mp hrange

@[no_expose] noncomputable def dualEquiv : F ≃ₗ[ZMod 2] (Fin s → ZMod 2) :=
  LinearEquiv.ofBijective (toDualLin e) ⟨toDual_injective e, toDual_surjective e⟩

/-- Under `dualEquiv`, field multiplication corresponds to the transpose multiplication matrix
action. -/
theorem dualEquiv_mul (a u : F) :
    dualEquiv e (a * u) =
      (Matrix.of fun (i k : Fin s) => e (a * e.symm (Pi.single k 1)) i)ᵀ *ᵥ dualEquiv e u := by
  show (multMat e (a * u))ᵀ *ᵥ Pi.single 0 1 =
    (multMat e a)ᵀ *ᵥ ((multMat e u)ᵀ *ᵥ Pi.single 0 1)
  rw [mul_comm a u, multMat_mul, Matrix.transpose_mul, ← Matrix.mulVec_mulVec]

/-- The dual coordinate image of a multiplied dual basis vector gives the stated transposed
multiplication matrix entry. -/
theorem dualEquiv_mul_single (a : F) (k i : Fin s) :
    dualEquiv e (a * (dualEquiv e).symm (Pi.single k 1)) i =
      e (a * e.symm (Pi.single i 1)) k := by
  rw [dualEquiv_mul, Matrix.mulVec, dotProduct]
  simp [Pi.single_apply, Matrix.of_apply]

omit [DecidableEq κ] [DecidableEq κ'] in
/-- Transposing the binary matrix is equivalent to converting the original transpose using the
dual coordinate equivalence. -/
theorem binaryMatrix_transpose_eq [DecidableEq κ] [DecidableEq κ'] (M : Matrix κ' κ F) :
    (binaryMatrix s e M)ᵀ = binaryMatrix s (dualEquiv e) Mᵀ := by
  funext p q
  have h := dualEquiv_mul_single e (Mᵀ p.1 q.1) q.2 p.2
  simp only [Matrix.transpose_apply, binaryMatrix] at h ⊢
  simpa [multMat, Matrix.of_apply] using h.symm

/-- The transposed binary matrix intertwines dual binary conversion with the original transposed
matrix action. -/
theorem binaryMatrix_transpose_mulVec (M : Matrix κ' κ F) (y : κ' → F) :
    (binaryMatrix s e M)ᵀ *ᵥ toBinary (dualEquiv e) y = toBinary (dualEquiv e) (Mᵀ *ᵥ y) := by
  rw [binaryMatrix_transpose_eq e M, binaryMatrix_mulVec]

/-- The transposed binary kernel corresponds to the original transposed kernel under dual
reconstruction. -/
theorem binaryMatrix_transpose_mulVec_eq_zero_iff (M : Matrix κ' κ F)
    (v : κ' × Fin s → ZMod 2) :
    (binaryMatrix s e M)ᵀ *ᵥ v = 0 ↔ Mᵀ *ᵥ ofBinary (dualEquiv e) v = 0 := by
  rw [binaryMatrix_transpose_eq e M, binaryMatrix_mulVec_eq_zero_iff]

/-- Membership in the transposed binary matrix range corresponds to membership in the original
transposed range under dual reconstruction. -/
theorem mem_range_binaryMatrix_transpose_iff (M : Matrix κ' κ F) (v : κ × Fin s → ZMod 2) :
    v ∈ LinearMap.range (Matrix.mulVecLin ((binaryMatrix s e M)ᵀ)) ↔
      ofBinary (dualEquiv e) v ∈ LinearMap.range (Matrix.mulVecLin Mᵀ) := by
  rw [binaryMatrix_transpose_eq e M, mem_range_binaryMatrix_iff]

end Dual

section Counting

variable {F : Type} [Field F] [Algebra (ZMod 2) F] {s : ℕ}
  (e : F ≃ₗ[ZMod 2] (Fin s → ZMod 2))
variable {κ α : Type} [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α]

omit [Algebra (ZMod 2) F] κ α [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α] in
/-- Block weight is at most the number of nonzero field coordinates. -/
theorem blockWeight_le_card_support [Algebra (ZMod 2) F] {κ α : Type}
    [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α] (part : κ → α) (x : κ → F) :
    blockWeight part x ≤ (Finset.univ.filter fun q => x q ≠ 0).card := by
  have himg : (Finset.univ.filter fun q => x q ≠ 0).image part =
      Finset.univ.filter fun a => ∃ q, part q = a ∧ x q ≠ 0 := by
    ext a
    simp [Finset.mem_image, Finset.mem_filter, and_comm]
  calc blockWeight part x
      = ((Finset.univ.filter fun q => x q ≠ 0).image part).card := by rw [himg]; rfl
    _ ≤ (Finset.univ.filter fun q => x q ≠ 0).card := Finset.card_image_le

/-- The number of nonzero field coordinates is at most the bit weight of their binary
representation. -/
theorem card_support_le_bitWeight (x : κ → F) :
    (Finset.univ.filter fun q => x q ≠ 0).card ≤ bitWeight (toBinary e x) := by
  classical
  have hex : ∀ q ∈ (Finset.univ.filter fun q => x q ≠ 0),
      ∃ k, toBinary e x (q, k) ≠ 0 := by
    intro q hq
    have hx : x q ≠ 0 := (Finset.mem_filter.mp hq).2
    have hne : e (x q) ≠ 0 := by
      intro h0
      exact hx (by rw [← e.symm_apply_apply (x q), h0, map_zero])
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
    exact ⟨k, by simpa [toBinary, Pi.zero_apply] using hk⟩
  choose g hg using hex
  have hsub : (Finset.univ.filter fun q => x q ≠ 0) ⊆
      (Finset.univ.filter fun p => toBinary e x p ≠ 0).image Prod.fst := by
    intro q hq
    refine Finset.mem_image.mpr ⟨(q, g q hq), by simpa using hg q hq, rfl⟩
  calc (Finset.univ.filter fun q => x q ≠ 0).card
      ≤ ((Finset.univ.filter fun p => toBinary e x p ≠ 0).image Prod.fst).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter fun p => toBinary e x p ≠ 0).card := Finset.card_image_le
    _ = bitWeight (toBinary e x) := rfl

omit [DecidableEq κ] in
/-- The bit weight of a converted vector is at most the extension degree times its field support
size. -/
theorem bitWeight_toBinary_le [DecidableEq κ] (x : κ → F) :
    bitWeight (toBinary e x) ≤ s * (Finset.univ.filter fun q => x q ≠ 0).card := by
  have hsub : (Finset.univ.filter fun p => toBinary e x p ≠ 0) ⊆
      (Finset.univ.filter fun q => x q ≠ 0) ×ˢ (Finset.univ : Finset (Fin s)) := by
    intro p hp
    refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ p.2⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro h0
    have hp' : toBinary e x p ≠ 0 := (Finset.mem_filter.mp hp).2
    apply hp'
    obtain ⟨q, k⟩ := p
    show toBinary e x (q, k) = 0
    simp [toBinary, h0, map_zero]
  calc bitWeight (toBinary e x)
      ≤ ((Finset.univ.filter fun q => x q ≠ 0) ×ˢ (Finset.univ : Finset (Fin s))).card :=
        Finset.card_le_card hsub
    _ = (Finset.univ.filter fun q => x q ≠ 0).card * Fintype.card (Fin s) :=
        Finset.card_product _ _
    _ = s * (Finset.univ.filter fun q => x q ≠ 0).card := by rw [Fintype.card_fin, mul_comm]

omit [Algebra (ZMod 2) F] κ α [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α] in
/-- When every partition fiber has size at most `M2`, support size is at most `M2` times block
weight. -/
theorem card_support_le_mul [Algebra (ZMod 2) F] {κ α : Type}
    [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α] (part : κ → α) (x : κ → F) (M2 : ℕ)
    (hM2 : ∀ a : α, (Finset.univ.filter fun q => part q = a).card ≤ M2) :
    (Finset.univ.filter fun q => x q ≠ 0).card ≤ M2 * blockWeight part x := by
  classical
  set T : Finset κ := Finset.univ.filter fun q => x q ≠ 0 with hT
  have hsum : T.card = ∑ a ∈ T.image part, (T.filter fun q => part q = a).card := by
    have hmaps : ∀ q ∈ T, part q ∈ T.image part := fun q hq => Finset.mem_image_of_mem _ hq
    calc T.card = ∑ q ∈ T, 1 := by rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_one]
      _ = ∑ a ∈ T.image part, ∑ q ∈ T.filter fun q => part q = a, 1 :=
            (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ = ∑ a ∈ T.image part, (T.filter fun q => part q = a).card := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_one]
  have hfiber : ∀ a ∈ T.image part, (T.filter fun q => part q = a).card ≤ M2 := by
    intro a _
    have h1 : T.filter (fun q => part q = a) ⊆ Finset.univ.filter fun q => part q = a :=
      Finset.filter_subset_filter _ (Finset.subset_univ _)
    exact (Finset.card_le_card h1).trans (hM2 a)
  have himg : (T.image part).card = blockWeight part x := by
    have hset : T.image part =
        Finset.univ.filter fun a => ∃ q, part q = a ∧ x q ≠ 0 := by
      ext a
      simp [Finset.mem_image, Finset.mem_filter, hT, and_comm]
    rw [hset]
    rfl
  calc T.card = ∑ a ∈ T.image part, (T.filter fun q => part q = a).card := hsum
    _ ≤ ∑ a ∈ T.image part, M2 := Finset.sum_le_sum hfiber
    _ = M2 * (T.image part).card := by
        rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_comm]
    _ = M2 * blockWeight part x := by rw [himg]

end Counting

section Rank

variable {F : Type} [Field F] [Algebra (ZMod 2) F] [Module.Free (ZMod 2) F] {s : ℕ}
  (e : F ≃ₗ[ZMod 2] (Fin s → ZMod 2))
variable {κ κ' : Type} [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ']

private def rangeMap (M : Matrix κ' κ F)
    (hmem : ∀ v : κ' × Fin s → ZMod 2,
      v ∈ LinearMap.range (Matrix.mulVecLin (binaryMatrix s e M)) ↔
        ofBinary e v ∈ LinearMap.range (Matrix.mulVecLin M)) :
    LinearMap.range (Matrix.mulVecLin (binaryMatrix s e M)) →ₗ[ZMod 2]
      LinearMap.range (Matrix.mulVecLin M) where
  toFun v := ⟨ofBinary e ↑v, (hmem ↑v).mp v.property⟩
  map_add' v1 v2 := by
    apply Subtype.ext
    show ofBinary e (↑(v1 + v2) : κ' × Fin s → ZMod 2) = ofBinary e ↑v1 + ofBinary e ↑v2
    rw [Submodule.coe_add]
    exact ofBinary_add e _ _
  map_smul' c v := by
    apply Subtype.ext
    show ofBinary e (↑(c • v) : κ' × Fin s → ZMod 2) = c • ofBinary e ↑v
    rw [Submodule.coe_smul]
    exact ofBinary_smul e _ _

omit [Module.Free (ZMod 2) F] [DecidableEq κ] in
/-- The induced range map acts by field reconstruction `ofBinary`. -/
private theorem rangeMap_apply [Module.Free (ZMod 2) F] [DecidableEq κ] (M : Matrix κ' κ F)
    (hmem : ∀ v : κ' × Fin s → ZMod 2,
      v ∈ LinearMap.range (Matrix.mulVecLin (binaryMatrix s e M)) ↔
        ofBinary e v ∈ LinearMap.range (Matrix.mulVecLin M))
    (v : LinearMap.range (Matrix.mulVecLin (binaryMatrix s e M))) :
    (rangeMap e M hmem v : κ' → F) = ofBinary e v := rfl

/-- Binary matrix conversion multiplies rank by the field extension degree. -/
theorem rank_binaryMatrix (M : Matrix κ' κ F)
    (hrank : Module.finrank (ZMod 2) F = s) :
    Matrix.rank (binaryMatrix s e M) = s * Matrix.rank M := by
  classical
  have hmem : ∀ v : κ' × Fin s → ZMod 2,
      v ∈ LinearMap.range (Matrix.mulVecLin (binaryMatrix s e M)) ↔
        ofBinary e v ∈ LinearMap.range (Matrix.mulVecLin M) :=
    fun v => mem_range_binaryMatrix_iff e M v
  have hmem' : ∀ w : κ' → F,
      toBinary e w ∈ LinearMap.range (Matrix.mulVecLin (binaryMatrix s e M)) ↔
        w ∈ LinearMap.range (Matrix.mulVecLin M) := by
    intro w
    rw [hmem, ofBinary_toBinary]
  have hφ : LinearMap.range (Matrix.mulVecLin (binaryMatrix s e M)) ≃ₗ[ZMod 2]
      LinearMap.range (Matrix.mulVecLin M) :=
    LinearEquiv.ofBijective (rangeMap e M hmem)
      ⟨fun a b hv => by
          apply Subtype.ext
          have hh : (rangeMap e M hmem a : κ' → F) = rangeMap e M hmem b :=
            congrArg Subtype.val hv
          rw [rangeMap_apply e M hmem a, rangeMap_apply e M hmem b] at hh
          rw [← toBinary_ofBinary e (a : κ' × Fin s → ZMod 2),
            ← toBinary_ofBinary e (b : κ' × Fin s → ZMod 2), hh],
        fun aw => ⟨⟨toBinary e (aw : κ' → F), hmem' (aw : κ' → F) |>.mpr aw.property⟩, by
          apply Subtype.ext
          exact ofBinary_toBinary e (aw : κ' → F)⟩⟩
  calc Matrix.rank (binaryMatrix s e M)
      = Module.finrank (ZMod 2) ↥(LinearMap.range (Matrix.mulVecLin (binaryMatrix s e M))) := rfl
    _ = Module.finrank (ZMod 2) ↥(LinearMap.range (Matrix.mulVecLin M)) := hφ.finrank_eq
    _ = Module.finrank (ZMod 2) F * Module.finrank F ↥(LinearMap.range (Matrix.mulVecLin M)) := by
        rw [← Module.finrank_mul_finrank (F := ZMod 2) (K := F)
          (A := LinearMap.range (Matrix.mulVecLin M))]
    _ = s * Matrix.rank M := by rw [hrank]; rfl

end Rank

section Support

variable {F : Type} [Field F] [Algebra (ZMod 2) F] {s : ℕ}
  (e : F ≃ₗ[ZMod 2] (Fin s → ZMod 2))
variable {κ κ' α : Type} [Fintype κ] [Fintype κ'] [Fintype α]
  [DecidableEq κ] [DecidableEq κ'] [DecidableEq α]

omit [DecidableEq κ] [DecidableEq κ'] in
/-- A zero field matrix entry gives zero in every corresponding binary block entry. -/
theorem binaryMatrix_apply_eq_zero [DecidableEq κ] [DecidableEq κ'] (M : Matrix κ' κ F) {p : κ' × Fin s} {q : κ × Fin s}
    (h : M p.1 q.1 = 0) : binaryMatrix s e M p q = 0 := by
  simp only [binaryMatrix, h, zero_smul, map_zero, Pi.zero_apply]

omit [DecidableEq κ] [DecidableEq κ'] in
/-- A zero field matrix entry gives zero in the corresponding transposed binary block entry. -/
theorem binaryMatrix_transpose_apply_eq_zero [DecidableEq κ] [DecidableEq κ'] (M : Matrix κ' κ F)
    {j : κ × Fin s} {p : κ' × Fin s} (h : M p.1 j.1 = 0) :
    (binaryMatrix s e M)ᵀ j p = 0 := by
  simp only [Matrix.transpose_apply, binaryMatrix, h, zero_smul, map_zero, Pi.zero_apply]

/-- A support restricted to selected first coordinates has size at most their count times the
second-coordinate cardinality. -/
private theorem card_filter_prod_le {β γ : Type} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (P : β × γ → ZMod 2) (Q : β → Prop) [DecidablePred Q]
    (h : ∀ p : β × γ, P p ≠ 0 → Q p.1) :
    (Finset.univ.filter fun p => P p ≠ 0).card ≤
      (Finset.univ.filter Q).card * Fintype.card γ := by
  classical
  have hsub : (Finset.univ.filter fun p => P p ≠ 0) ⊆
      (Finset.univ.filter Q) ×ˢ (Finset.univ : Finset γ) := by
    intro p hp
    refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ p.2⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h p ((Finset.mem_filter.mp hp).2)⟩
  calc (Finset.univ.filter fun p => P p ≠ 0).card
      ≤ ((Finset.univ.filter Q) ×ˢ (Finset.univ : Finset γ)).card :=
        Finset.card_le_card hsub
    _ = (Finset.univ.filter Q).card * Fintype.card γ := Finset.card_product _ _

/-- Pauli weight is at most the sum of the X and Z bit weights. -/
theorem pauliWeight_le_bitWeight_add {ι : Type} [Fintype ι] (x z : ι → ZMod 2) :
    pauliWeight x z ≤ bitWeight x + bitWeight z := by
  have hsub : (Finset.univ.filter fun i => x i ≠ 0 ∨ z i ≠ 0) ⊆
      (Finset.univ.filter fun i => x i ≠ 0) ∪ (Finset.univ.filter fun i => z i ≠ 0) := by
    intro i hi
    refine Finset.mem_union.mpr ?_
    rcases (Finset.mem_filter.mp hi).2 with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  calc pauliWeight x z = (Finset.univ.filter fun i => x i ≠ 0 ∨ z i ≠ 0).card := rfl
    _ ≤ ((Finset.univ.filter fun i => x i ≠ 0) ∪
        (Finset.univ.filter fun i => z i ≠ 0)).card := Finset.card_le_card hsub
    _ ≤ bitWeight x + bitWeight z := Finset.card_union_le _ _

/-- For a finite nonempty set, block distance is attained by some element of that set. -/
private theorem exists_blockDist_eq {F α κ : Type} [Zero F] [Sub F] [Fintype κ] [Fintype α]
    [DecidableEq α] (part : κ → α) (x : κ → F) (S : Set (κ → F))
    (hSfin : S.Finite) (hSne : S.Nonempty) :
    ∃ y ∈ S, (blockWeight part (fun i => x i - y i) : ℕ∞) = blockDist part x S := by
  classical
  unfold blockDist
  have : Fintype ↥S := Set.Finite.fintype hSfin
  obtain ⟨y₀, hy₀⟩ := hSne
  obtain ⟨y, _, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset ↥S) (fun y : ↥S => blockWeight part (fun i => x i - (y : κ → F) i))
    ⟨⟨y₀, hy₀⟩, Finset.mem_univ _⟩
  refine ⟨(y : κ → F), y.2, ?_⟩
  apply le_antisymm
  · apply le_sInf
    rintro w ⟨y', hy', rfl⟩
    show (blockWeight part (fun i => x i - (y : κ → F) i) : ℕ∞) ≤
        (blockWeight part (fun i => x i - y' i) : ℕ∞)
    exact_mod_cast hmin ⟨y', hy'⟩ (Finset.mem_univ _)
  · have hmem : ((blockWeight part (fun i => x i - (y : κ → F) i) : ℕ∞)) ∈
        {w : ℕ∞ | ∃ y ∈ S, (blockWeight part (fun i => x i - y i) : ℕ∞) = w} :=
      ⟨(y : κ → F), y.2, rfl⟩
    exact sInf_le hmem

end Support

/-- Binary conversion of a chain complex satisfying the stated distance, soundness, and sparsity
bounds yields a CSS code with the stated dimension and parameter guarantees. -/
theorem binaryConversionSoundness :
    ∀ (s : ℕ) (F : Type) [Field F] [Algebra (ZMod 2) F] [Module.Free (ZMod 2) F]
      [Fintype F] [Module.Finite (ZMod 2) F],
      0 < s → Module.finrank (ZMod 2) F = s → Fintype.card F = 2 ^ s →
      ∀ (κ1 κ2 κ3 α : Type) [Fintype κ1] [Fintype κ2] [Fintype κ3] [Fintype α]
        [DecidableEq κ1] [DecidableEq κ2] [DecidableEq κ3] [DecidableEq α]
        (A : Matrix κ3 κ2 F) (B : Matrix κ2 κ1 F),
        A * B = 0 →
      ∀ (part : κ2 → α) (partA : κ3 → α) (partB : κ1 → α)
        (μc μh εc εh : ℝ) (wF M2 : ℕ),
        0 < μc → 0 < μh → 0 < εc → 0 < εh →
        (∀ a : α, (Finset.univ.filter fun i : κ2 => part i = a).card ≤ M2) →
        0 < Fintype.card κ2 → 0 < Fintype.card κ1 + Fintype.card κ3 →
        (∀ x : κ2 → F, A *ᵥ x = 0 →
          x ∉ LinearMap.range (Matrix.mulVecLin B) →
          (μc : ℝ) ≤ (blockWeight part x : ℝ)) →
        (∀ y : κ2 → F, (Bᵀ : Matrix κ1 κ2 F) *ᵥ y = (0 : κ1 → F) →
          y ∉ LinearMap.range (Matrix.mulVecLin (Aᵀ : Matrix κ2 κ3 F)) →
          (μh : ℝ) ≤ (blockWeight part y : ℝ)) →
        (∀ x : κ2 → F,
          (εc : ℝ) *
            ((blockDist part x (LinearMap.ker (Matrix.mulVecLin A))).toNat : ℝ) ≤
            (blockWeight partA (A *ᵥ x) : ℝ)) →
        (∀ y : κ2 → F,
          (εh : ℝ) *
            ((blockDist part y
              (LinearMap.ker (Matrix.mulVecLin (Bᵀ : Matrix κ1 κ2 F)))).toNat : ℝ) ≤
            (blockWeight partB ((Bᵀ : Matrix κ1 κ2 F) *ᵥ y) : ℝ)) →
        ((∀ i : κ2, (Finset.univ.filter fun c : κ3 => A c i ≠ 0).card ≤ wF) ∧
          (∀ c : κ3, (Finset.univ.filter fun i : κ2 => A c i ≠ 0).card ≤ wF) ∧
          (∀ j : κ1, (Finset.univ.filter fun i : κ2 => B i j ≠ 0).card ≤ wF) ∧
          (∀ i : κ2, (Finset.univ.filter fun j : κ1 => B i j ≠ 0).card ≤ wF)) →
        ∀ (e : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)),
          let HX : Matrix (κ3 × Fin s) (κ2 × Fin s) (ZMod 2) := binaryMatrix s e A
          let HZ : Matrix (κ1 × Fin s) (κ2 × Fin s) (ZMod 2) :=
            (binaryMatrix s e B)ᵀ
          ∃ (hcompat : HX * HZᵀ = 0),
            let c : CssData (κ2 × Fin s) (κ3 × Fin s) (κ1 × Fin s) :=
              { hX := HX, hZ := HZ, hcompat := hcompat }
            c.numQubits = s * Fintype.card κ2 ∧
            c.encodedQubits = s * (Fintype.card κ2 - Matrix.rank A - Matrix.rank B) ∧
            ((Nat.ceil (min μc μh) : ℕ) : ℕ∞) ≤ cssDistance c ∧
            cssHasSoundnessAtLeast c
              ((Fintype.card κ2 : ℝ) * min εc εh /
                ((s : ℝ) * M2 * (Fintype.card κ1 + Fintype.card κ3))) ∧
            c.checkWeight ≤ s * wF ∧
            c.qubitIncidence ≤ 2 * s * wF := by
  intro s F _ _ _ _ _ hs hdim hcard κ1 κ2 κ3 α _ _ _ _ _ _ _ _ A B hAB
    part partA partB μc μh εc εh wF M2 hμc hμh hεc hεh hM2 hκ2 hκ13
    hμc' hμh' hεc' hεh' hwF e
  classical
  have : NeZero s := ⟨hs.ne'⟩
  have hminpos : 0 < min μc μh := lt_min hμc hμh
  have hminεpos : 0 < min εc εh := lt_min hεc hεh
  refine ⟨binaryMatrix_mul_eq_zero e A B hAB, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Fintype.card (κ2 × Fin s) = s * Fintype.card κ2
    rw [Fintype.card_prod, Fintype.card_fin, mul_comm]
  · show Fintype.card (κ2 × Fin s) - Matrix.rank (binaryMatrix s e A)
        - Matrix.rank ((binaryMatrix s e B)ᵀ) =
      s * (Fintype.card κ2 - Matrix.rank A - Matrix.rank B)
    rw [Fintype.card_prod, Fintype.card_fin, mul_comm (Fintype.card κ2) s,
      Matrix.rank_transpose, rank_binaryMatrix e A hdim, rank_binaryMatrix e B hdim]
    conv_lhs => rw [Nat.sub_sub, ← mul_add, ← Nat.mul_sub]
    conv_rhs => rw [Nat.sub_sub]
  · simp only [cssDistance]
    apply le_min
    · apply le_sInf
      rintro w ⟨z, hz1, hz2, hz3⟩
      have hzF0 : A *ᵥ ofBinary e z = 0 := (binaryMatrix_mulVec_eq_zero_iff e A z).mp hz1
      have hzFr : ofBinary e z ∉ LinearMap.range (Matrix.mulVecLin B) := fun hin =>
        hz2 ((mem_range_binaryMatrix_iff e B z).mpr hin)
      have hμ := hμc' (ofBinary e z) hzF0 hzFr
      have hbw : (blockWeight part (ofBinary e z) : ℕ) ≤ bitWeight z := by
        have h1 := blockWeight_le_card_support part (ofBinary e z)
        have h2 := card_support_le_bitWeight e (ofBinary e z)
        rw [toBinary_ofBinary e z] at h2
        exact h1.trans h2
      rw [← hz3]
      have hceil : Nat.ceil (min μc μh) ≤ bitWeight z := by
        apply Nat.ceil_le.mpr
        refine le_trans (min_le_left _ _) ?_
        exact le_trans hμ (by exact_mod_cast hbw)
      exact_mod_cast hceil
    · apply le_sInf
      rintro w ⟨x, hx1, hx2, hx3⟩
      have hxF0 : (Bᵀ : Matrix κ1 κ2 F) *ᵥ ofBinary (dualEquiv e) x = 0 :=
        (binaryMatrix_transpose_mulVec_eq_zero_iff e B x).mp hx1
      have hxFr : ofBinary (dualEquiv e) x ∉
          LinearMap.range (Matrix.mulVecLin (Aᵀ : Matrix κ2 κ3 F)) := fun hin =>
        hx2 ((mem_range_binaryMatrix_transpose_iff e A x).mpr hin)
      have hμ := hμh' (ofBinary (dualEquiv e) x) hxF0 hxFr
      have hbw : (blockWeight part (ofBinary (dualEquiv e) x) : ℕ) ≤ bitWeight x := by
        have h1 := blockWeight_le_card_support part (ofBinary (dualEquiv e) x)
        have h2 := card_support_le_bitWeight (dualEquiv e) (ofBinary (dualEquiv e) x)
        rw [toBinary_ofBinary (dualEquiv e) x] at h2
        exact h1.trans h2
      rw [← hx3]
      have hceil : Nat.ceil (min μc μh) ≤ bitWeight x := by
        apply Nat.ceil_le.mpr
        refine le_trans (min_le_right _ _) ?_
        exact le_trans hμ (by exact_mod_cast hbw)
      exact_mod_cast hceil
  · rw [cssHasSoundnessAtLeast_iff]
    rintro ⟨ηX, ηZ⟩
    have hN : ((Fintype.card (κ2 × Fin s) : ℕ) : ℝ) = (s : ℝ) * (Fintype.card κ2 : ℝ) := by
      rw [Fintype.card_prod, Fintype.card_fin]; push_cast; ring
    have hD : ((Fintype.card ((κ3 × Fin s) ⊕ (κ1 × Fin s)) : ℕ) : ℝ) =
        (s : ℝ) * ((Fintype.card κ1 : ℝ) + (Fintype.card κ3 : ℝ)) := by
      rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
      push_cast; ring
    rw [hN, hD]
    simp only [Nat.cast_add]
    set W := (cssSyndromeWeight
        (⟨binaryMatrix s e A, (binaryMatrix s e B)ᵀ,
          binaryMatrix_mul_eq_zero e A B hAB⟩ :
          CssData (κ2 × Fin s) (κ3 × Fin s) (κ1 × Fin s)) ηX ηZ).toNat with hW
    by_cases hW0 : W = 0
    · rw [hW0]; simp only [Nat.cast_zero, mul_zero]; positivity
    · have hne : ∃ (x z : κ2 × Fin s → ZMod 2), binaryMatrix s e A *ᵥ z = ηX ∧
          (binaryMatrix s e B)ᵀ *ᵥ x = ηZ := by
        by_contra hcon
        have htop : (cssSyndromeWeight (⟨binaryMatrix s e A, (binaryMatrix s e B)ᵀ,
          binaryMatrix_mul_eq_zero e A B hAB⟩ :
          CssData (κ2 × Fin s) (κ3 × Fin s) (κ1 × Fin s)) ηX ηZ) = ⊤ := by
          show sInf {w : ℕ∞ | ∃ (x z : κ2 × Fin s → ZMod 2),
            binaryMatrix s e A *ᵥ z = ηX ∧ (binaryMatrix s e B)ᵀ *ᵥ x = ηZ ∧
            ((pauliWeight x z : ℕ) : ℕ∞) = w} = ⊤
          rw [sInf_eq_top]
          rintro w ⟨x, z, hxz, hxX, -⟩
          exact (hcon ⟨x, z, hxz, hxX⟩).elim
        rw [hW, htop] at hW0
        simp at hW0
      obtain ⟨x₀, z₀, hz₀, hx₀⟩ := hne
      have hAz : A *ᵥ ofBinary e z₀ = ofBinary e ηX := by
        have h1 := binaryMatrix_mulVec e A (ofBinary e z₀)
        rw [toBinary_ofBinary e z₀, hz₀] at h1
        calc A *ᵥ ofBinary e z₀
            = ofBinary e (toBinary e (A *ᵥ ofBinary e z₀)) := (ofBinary_toBinary e _).symm
          _ = ofBinary e ηX := by rw [h1]
      have hBx : (Bᵀ : Matrix κ1 κ2 F) *ᵥ ofBinary (dualEquiv e) x₀
          = ofBinary (dualEquiv e) ηZ := by
        have h1 := binaryMatrix_transpose_mulVec e B (ofBinary (dualEquiv e) x₀)
        rw [toBinary_ofBinary (dualEquiv e) x₀, hx₀] at h1
        calc (Bᵀ : Matrix κ1 κ2 F) *ᵥ ofBinary (dualEquiv e) x₀
            = ofBinary (dualEquiv e)
                (toBinary (dualEquiv e)
                  ((Bᵀ : Matrix κ1 κ2 F) *ᵥ ofBinary (dualEquiv e) x₀)) :=
              (ofBinary_toBinary (dualEquiv e) _).symm
          _ = ofBinary (dualEquiv e) ηZ := by rw [h1]
      have hedc := hεc' (ofBinary e z₀)
      have hedh := hεh' (ofBinary (dualEquiv e) x₀)
      have hSfinA : ((↑(LinearMap.ker (Matrix.mulVecLin A)) : Set (κ2 → F))).Finite :=
        Set.Finite.subset Set.finite_univ (Set.subset_univ _)
      have hSneA : ((↑(LinearMap.ker (Matrix.mulVecLin A)) : Set (κ2 → F))).Nonempty :=
        ⟨0, SetLike.mem_coe.mpr (Submodule.zero_mem _)⟩
      obtain ⟨y_c, hy_c, hyc_eq⟩ := exists_blockDist_eq part (ofBinary e z₀)
        (↑(LinearMap.ker (Matrix.mulVecLin A)) : Set (κ2 → F)) hSfinA hSneA
      have hSfinH : ((↑(LinearMap.ker (Matrix.mulVecLin (Bᵀ : Matrix κ1 κ2 F))) :
        Set (κ2 → F))).Finite := Set.Finite.subset Set.finite_univ (Set.subset_univ _)
      have hSneH : ((↑(LinearMap.ker (Matrix.mulVecLin (Bᵀ : Matrix κ1 κ2 F))) :
        Set (κ2 → F))).Nonempty := ⟨0, SetLike.mem_coe.mpr (Submodule.zero_mem _)⟩
      obtain ⟨y_h, hy_h, hyh_eq⟩ := exists_blockDist_eq part (ofBinary (dualEquiv e) x₀)
        (↑(LinearMap.ker (Matrix.mulVecLin (Bᵀ : Matrix κ1 κ2 F))) : Set (κ2 → F))
        hSfinH hSneH
      have hy_cA : A *ᵥ y_c = 0 := by
        have h := LinearMap.mem_ker.mp (SetLike.mem_coe.mp hy_c)
        rwa [Matrix.mulVecLin_apply] at h
      have hy_hB : (Bᵀ : Matrix κ1 κ2 F) *ᵥ y_h = 0 := by
        have h := LinearMap.mem_ker.mp (SetLike.mem_coe.mp hy_h)
        rwa [Matrix.mulVecLin_apply] at h
      have hdc : ((blockDist part (ofBinary e z₀)
            ↑(LinearMap.ker (Matrix.mulVecLin A))).toNat : ℝ) =
          (blockWeight part (ofBinary e z₀ - y_c) : ℝ) := by
        rw [← hyc_eq]
        exact_mod_cast ENat.natCast_toNat (ENat.natCast_ne_top _)
      have hdh : ((blockDist part (ofBinary (dualEquiv e) x₀)
            ↑(LinearMap.ker (Matrix.mulVecLin (Bᵀ : Matrix κ1 κ2 F)))).toNat : ℝ) =
          (blockWeight part (ofBinary (dualEquiv e) x₀ - y_h) : ℝ) := by
        rw [← hyh_eq]
        exact_mod_cast ENat.natCast_toNat (ENat.natCast_ne_top _)
      have hsyndz : binaryMatrix s e A *ᵥ
          toBinary e (ofBinary e z₀ - y_c) = ηX := by
        rw [binaryMatrix_mulVec e A (ofBinary e z₀ - y_c),
          Matrix.mulVec_sub, hy_cA, sub_zero, hAz]
        exact toBinary_ofBinary e ηX
      have hsyndx : (binaryMatrix s e B)ᵀ *ᵥ
          toBinary (dualEquiv e) (ofBinary (dualEquiv e) x₀ - y_h) = ηZ := by
        rw [binaryMatrix_transpose_mulVec e B (ofBinary (dualEquiv e) x₀ - y_h),
          Matrix.mulVec_sub, hy_hB, sub_zero, hBx]
        exact toBinary_ofBinary (dualEquiv e) ηZ
      have hWle : W ≤ pauliWeight
          (toBinary (dualEquiv e) (ofBinary (dualEquiv e) x₀ - y_h))
          (toBinary e (ofBinary e z₀ - y_c)) := by
        rw [hW]
        exact ENat.toNat_le_of_le_natCast (sInf_le ⟨_, _, hsyndz, hsyndx, rfl⟩)
      have hbwz : bitWeight (toBinary e (ofBinary e z₀ - y_c)) ≤
          s * (M2 * blockWeight part (ofBinary e z₀ - y_c)) := by
        have h1 := bitWeight_toBinary_le e (ofBinary e z₀ - y_c)
        have h2 := card_support_le_mul part (ofBinary e z₀ - y_c) M2 hM2
        calc bitWeight (toBinary e (ofBinary e z₀ - y_c))
            ≤ s * (Finset.univ.filter fun q => (ofBinary e z₀ - y_c) q ≠ 0).card := h1
          _ ≤ s * (M2 * blockWeight part (ofBinary e z₀ - y_c)) :=
              Nat.mul_le_mul_left s h2
      have hbwx : bitWeight (toBinary (dualEquiv e) (ofBinary (dualEquiv e) x₀ - y_h)) ≤
          s * (M2 * blockWeight part (ofBinary (dualEquiv e) x₀ - y_h)) := by
        have h1 := bitWeight_toBinary_le (dualEquiv e) (ofBinary (dualEquiv e) x₀ - y_h)
        have h2 := card_support_le_mul part (ofBinary (dualEquiv e) x₀ - y_h) M2 hM2
        calc bitWeight (toBinary (dualEquiv e) (ofBinary (dualEquiv e) x₀ - y_h))
            ≤ s * (Finset.univ.filter
                fun q => (ofBinary (dualEquiv e) x₀ - y_h) q ≠ 0).card := h1
          _ ≤ s * (M2 * blockWeight part (ofBinary (dualEquiv e) x₀ - y_h)) :=
              Nat.mul_le_mul_left s h2
      have hbX : (blockWeight partA (ofBinary e ηX) : ℝ) ≤ (bitWeight ηX : ℝ) := by
        have h1 := blockWeight_le_card_support partA (ofBinary e ηX)
        have h2 := card_support_le_bitWeight e (ofBinary e ηX)
        rw [toBinary_ofBinary e ηX] at h2
        exact_mod_cast h1.trans h2
      have hbZ : (blockWeight partB (ofBinary (dualEquiv e) ηZ) : ℝ) ≤
          (bitWeight ηZ : ℝ) := by
        have h1 := blockWeight_le_card_support partB (ofBinary (dualEquiv e) ηZ)
        have h2 := card_support_le_bitWeight (dualEquiv e) (ofBinary (dualEquiv e) ηZ)
        rw [toBinary_ofBinary (dualEquiv e) ηZ] at h2
        exact_mod_cast h1.trans h2
      rw [hAz] at hedc
      rw [hBx] at hedh
      rw [hdc] at hedc
      rw [hdh] at hedh
      have hM2pos : 0 < M2 := by
        obtain ⟨i⟩ := Fintype.card_pos_iff.mp hκ2
        have h1 : i ∈ Finset.univ.filter fun q => part q = part i :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩
        have h2 : 0 < (Finset.univ.filter fun q => part q = part i).card :=
          Finset.card_pos.mpr ⟨i, h1⟩
        exact lt_of_lt_of_le h2 (hM2 (part i))
      have hkey : min εc εh * (W : ℝ) ≤
          (s : ℝ) * ((M2 : ℝ) * ((bitWeight ηX : ℝ) + (bitWeight ηZ : ℝ))) := by
        have hA : (W : ℝ) ≤ (s : ℝ) * ((M2 : ℝ) *
              (blockWeight part (ofBinary (dualEquiv e) x₀ - y_h) : ℝ)) +
            (s : ℝ) * ((M2 : ℝ) * (blockWeight part (ofBinary e z₀ - y_c) : ℝ)) := by
          have hP' : (pauliWeight
              (toBinary (dualEquiv e) (ofBinary (dualEquiv e) x₀ - y_h))
              (toBinary e (ofBinary e z₀ - y_c)) : ℕ) ≤
              s * (M2 * blockWeight part (ofBinary (dualEquiv e) x₀ - y_h)) +
              s * (M2 * blockWeight part (ofBinary e z₀ - y_c)) :=
            le_trans (pauliWeight_le_bitWeight_add _ _) (add_le_add hbwx hbwz)
          exact_mod_cast le_trans hWle hP'
        have hz1 : (min εc εh : ℝ) * (blockWeight part (ofBinary e z₀ - y_c) : ℝ) ≤
            εc * (blockWeight part (ofBinary e z₀ - y_c) : ℝ) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        have hz2 : (min εc εh : ℝ) *
            (blockWeight part (ofBinary (dualEquiv e) x₀ - y_h) : ℝ) ≤
            εh * (blockWeight part (ofBinary (dualEquiv e) x₀ - y_h) : ℝ) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        have hedc2 := hedc.trans hbX
        have hedh2 := hedh.trans hbZ
        have hleft : (s : ℝ) * ((M2 : ℝ) * ((min εc εh : ℝ) *
                (blockWeight part (ofBinary (dualEquiv e) x₀ - y_h) : ℝ))) ≤
            (s : ℝ) * ((M2 : ℝ) * (εh *
                (blockWeight part (ofBinary (dualEquiv e) x₀ - y_h) : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hz2 (by positivity)) (by positivity)
        have hright : (s : ℝ) * ((M2 : ℝ) * ((min εc εh : ℝ) *
                (blockWeight part (ofBinary e z₀ - y_c) : ℝ))) ≤
            (s : ℝ) * ((M2 : ℝ) * (εc *
                (blockWeight part (ofBinary e z₀ - y_c) : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hz1 (by positivity)) (by positivity)
        have hleft2 : (s : ℝ) * ((M2 : ℝ) * (εh *
                (blockWeight part (ofBinary (dualEquiv e) x₀ - y_h) : ℝ))) ≤
            (s : ℝ) * ((M2 : ℝ) * (bitWeight ηZ : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hedh2 (by positivity)) (by positivity)
        have hright2 : (s : ℝ) * ((M2 : ℝ) * (εc *
                (blockWeight part (ofBinary e z₀ - y_c) : ℝ))) ≤
            (s : ℝ) * ((M2 : ℝ) * (bitWeight ηX : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hedc2 (by positivity)) (by positivity)
        calc (min εc εh : ℝ) * (W : ℝ)
            ≤ (min εc εh : ℝ) * ((s : ℝ) * ((M2 : ℝ) *
                (blockWeight part (ofBinary (dualEquiv e) x₀ - y_h) : ℝ)) +
              (s : ℝ) * ((M2 : ℝ) * (blockWeight part (ofBinary e z₀ - y_c) : ℝ))) :=
                mul_le_mul_of_nonneg_left hA (le_of_lt hminεpos)
          _ = (s : ℝ) * ((M2 : ℝ) * ((min εc εh : ℝ) *
                (blockWeight part (ofBinary (dualEquiv e) x₀ - y_h) : ℝ))) +
              (s : ℝ) * ((M2 : ℝ) * ((min εc εh : ℝ) *
                (blockWeight part (ofBinary e z₀ - y_c) : ℝ))) := by ring
          _ ≤ (s : ℝ) * ((M2 : ℝ) * (εh *
                (blockWeight part (ofBinary (dualEquiv e) x₀ - y_h) : ℝ))) +
              (s : ℝ) * ((M2 : ℝ) * (εc *
                (blockWeight part (ofBinary e z₀ - y_c) : ℝ))) :=
                add_le_add hleft hright
          _ ≤ (s : ℝ) * ((M2 : ℝ) * (bitWeight ηZ : ℝ)) +
              (s : ℝ) * ((M2 : ℝ) * (bitWeight ηX : ℝ)) :=
                add_le_add hleft2 hright2
          _ = (s : ℝ) * ((M2 : ℝ) * ((bitWeight ηX : ℝ) + (bitWeight ηZ : ℝ))) := by ring
      have hsℝ : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
      have hκ2ℝ : (0 : ℝ) < (Fintype.card κ2 : ℝ) := by exact_mod_cast hκ2
      have hκ13ℝ : (0 : ℝ) < ((Fintype.card κ1 : ℝ) + (Fintype.card κ3 : ℝ)) := by
        exact_mod_cast hκ13
      have hEpos : (0 : ℝ) < (s : ℝ) * (M2 : ℝ) *
          ((Fintype.card κ1 : ℝ) + (Fintype.card κ3 : ℝ)) :=
        mul_pos (mul_pos hsℝ (by exact_mod_cast hM2pos)) hκ13ℝ
      have hNpos : (0 : ℝ) < (s : ℝ) * (Fintype.card κ2 : ℝ) := mul_pos hsℝ hκ2ℝ
      have hDpos : (0 : ℝ) < (s : ℝ) *
          ((Fintype.card κ1 : ℝ) + (Fintype.card κ3 : ℝ)) := mul_pos hsℝ hκ13ℝ
      rw [div_div, div_mul_eq_mul_div, mul_assoc,
        div_le_div_iff₀ (mul_pos hEpos hNpos) hDpos]
      calc ((Fintype.card κ2 : ℝ) * (min εc εh * (W : ℝ))) *
          ((s : ℝ) * ((Fintype.card κ1 : ℝ) + (Fintype.card κ3 : ℝ)))
          = (((Fintype.card κ1 : ℝ) + (Fintype.card κ3 : ℝ)) *
              ((Fintype.card κ2 : ℝ) * (s : ℝ))) * (min εc εh * (W : ℝ)) := by ring
        _ ≤ (((Fintype.card κ1 : ℝ) + (Fintype.card κ3 : ℝ)) *
              ((Fintype.card κ2 : ℝ) * (s : ℝ))) *
            ((s : ℝ) * ((M2 : ℝ) * ((bitWeight ηX : ℝ) + (bitWeight ηZ : ℝ)))) :=
              mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = ((bitWeight ηX : ℝ) + (bitWeight ηZ : ℝ)) *
            (((s : ℝ) * (M2 : ℝ) * ((Fintype.card κ1 : ℝ) + (Fintype.card κ3 : ℝ))) *
              ((s : ℝ) * (Fintype.card κ2 : ℝ))) := by ring
  · show max (Finset.univ.sup fun i : κ3 × Fin s => bitWeight (binaryMatrix s e A i))
        (Finset.univ.sup fun j : κ1 × Fin s => bitWeight ((binaryMatrix s e B)ᵀ j)) ≤
        s * wF
    apply max_le
    · apply Finset.sup_le
      intro i _
      have h1 : bitWeight (binaryMatrix s e A i) ≤
          (Finset.univ.filter fun q : κ2 => A i.1 q ≠ 0).card * Fintype.card (Fin s) :=
        card_filter_prod_le (β := κ2) (γ := Fin s)
          (fun p => binaryMatrix s e A i p) (fun q => A i.1 q ≠ 0)
          (fun p hp h0 => hp (binaryMatrix_apply_eq_zero e A h0))
      rw [Fintype.card_fin] at h1
      calc bitWeight (binaryMatrix s e A i)
          ≤ (Finset.univ.filter fun q : κ2 => A i.1 q ≠ 0).card * s := h1
        _ ≤ wF * s := Nat.mul_le_mul_right s (hwF.2.1 i.1)
        _ = s * wF := mul_comm wF s
    · apply Finset.sup_le
      intro j _
      have h1 : bitWeight ((binaryMatrix s e B)ᵀ j) ≤
          (Finset.univ.filter fun i : κ2 => B i j.1 ≠ 0).card * Fintype.card (Fin s) :=
        card_filter_prod_le (β := κ2) (γ := Fin s)
          (fun p => (binaryMatrix s e B)ᵀ j p) (fun i => B i j.1 ≠ 0)
          (fun p hp h0 => hp (binaryMatrix_transpose_apply_eq_zero e B h0))
      rw [Fintype.card_fin] at h1
      calc bitWeight ((binaryMatrix s e B)ᵀ j)
          ≤ (Finset.univ.filter fun i : κ2 => B i j.1 ≠ 0).card * s := h1
        _ ≤ wF * s := Nat.mul_le_mul_right s (hwF.2.2.1 j.1)
        _ = s * wF := mul_comm wF s
  · apply Finset.sup_le
    intro p _
    have h1 : (Finset.univ.filter fun i : κ3 × Fin s =>
          binaryMatrix s e A i p ≠ 0).card ≤
        (Finset.univ.filter fun c : κ3 => A c p.1 ≠ 0).card * Fintype.card (Fin s) :=
      card_filter_prod_le (β := κ3) (γ := Fin s)
        (fun i => binaryMatrix s e A i p) (fun c => A c p.1 ≠ 0)
        (fun i hi h0 => hi (binaryMatrix_apply_eq_zero e A h0))
    rw [Fintype.card_fin] at h1
    have h2 : (Finset.univ.filter fun j : κ1 × Fin s =>
          (binaryMatrix s e B)ᵀ j p ≠ 0).card ≤
        (Finset.univ.filter fun i : κ1 => B p.1 i ≠ 0).card * Fintype.card (Fin s) :=
      card_filter_prod_le (β := κ1) (γ := Fin s)
        (fun j => (binaryMatrix s e B)ᵀ j p) (fun i => B p.1 i ≠ 0)
        (fun j hj h0 => hj (binaryMatrix_transpose_apply_eq_zero e B h0))
    rw [Fintype.card_fin] at h2
    calc (Finset.univ.filter fun i : κ3 × Fin s => binaryMatrix s e A i p ≠ 0).card +
        (Finset.univ.filter fun j : κ1 × Fin s => (binaryMatrix s e B)ᵀ j p ≠ 0).card
        ≤ wF * s + wF * s := add_le_add
          (h1.trans (Nat.mul_le_mul_right s (hwF.1 p.1)))
          (h2.trans (Nat.mul_le_mul_right s (hwF.2.2.2 p.1)))
      _ = 2 * s * wF := by ring

end Qatlib.Concepts.CodingDecoding.CssTesters.BinaryConversionSoundness
