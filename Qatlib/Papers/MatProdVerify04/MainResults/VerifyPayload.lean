/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Persistent data in Figure 1 of quantum matrix product verification

The four vectors live over the coefficient alphabet. The two walk subsets
are represented by membership masks. The compressed scalar and the
interference control bit are also persistent. This counts the data carried
by a branch of the walk and excludes the temporary storage of its operators.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MatProdVerify04.MainResults

/-- A basis label for the persistent data of Verify Once, including the
classically chosen vectors and the quantum walk registers. -/
structure VerifyOnceData (n : ℕ) (K : Type*) where
  p : Fin n → K
  q : Fin n → K
  rowSketch : Fin n → K
  colSketch : Fin n → K
  scalar : K
  rows : Fin n → Bool
  cols : Fin n → Bool
  control : Bool

/-- Lay out the basis label as four coefficient vectors, one coefficient
scalar, two subset masks, and one binary control. -/
def verifyDataLayout (n : ℕ) (K : Type*) :
    VerifyOnceData n K ≃
      ((Fin n → K) × (Fin n → K) × (Fin n → K) × (Fin n → K) × K) ×
      ((Fin n → Bool) × (Fin n → Bool) × Bool) where
  toFun x := (⟨x.p, x.q, x.rowSketch, x.colSketch, x.scalar⟩, ⟨x.rows, x.cols, x.control⟩)
  invFun x := ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2.1, x.1.2.2.2.2,
    x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv x := by
    cases x
    rfl
  right_inv _ := rfl

instance (n : ℕ) (K : Type*) [Fintype K] : Fintype (VerifyOnceData n K) :=
  Fintype.ofEquiv _ (verifyDataLayout n K).symm

/-- The encoded walk data has four coefficient vectors of length n, one
coefficient scalar, two masks of length n, and one control bit. -/
theorem verify_data_card (n : ℕ) (K : Type*) [Fintype K] :
    Fintype.card (VerifyOnceData n K) = Fintype.card K ^ (4 * n + 1) * 2 ^ (2 * n + 1) := by
  rw [Fintype.card_congr (verifyDataLayout n K)]
  simp [Fintype.card_prod, pow_add]
  ring

/-- With w bits available per coefficient, the persistent data fits in
w times the coefficient count plus the bits for both masks and the control. -/
theorem verify_data_bit_capacity (n w : ℕ) (K : Type*) [Fintype K]
    (hword : Fintype.card K ≤ 2 ^ w) :
    Fintype.card (VerifyOnceData n K) ≤ 2 ^ (w * (4 * n + 1) + (2 * n + 1)) := by
  rw [verify_data_card]
  calc
    _ ≤ (2 ^ w) ^ (4 * n + 1) * 2 ^ (2 * n + 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hword _)
    _ = _ := by rw [← pow_mul, ← pow_add]

/-- The persistent layout has a linear bit budget in the matrix dimension
for a fixed coefficient width. -/
theorem verify_data_bits_linear (n w : ℕ) (hn : 1 ≤ n) :
    w * (4 * n + 1) + (2 * n + 1) ≤ (5 * w + 3) * n := by
  have hword : w * 1 ≤ w * n := Nat.mul_le_mul_left w hn
  nlinarith only [hn, hword]

/-- Encode the persistent data injectively in a fixed-width bit register
whose length is linear in the matrix dimension. -/
noncomputable def verifyDataEncoding (n w : ℕ) (K : Type*) [Fintype K]
    (hn : 1 ≤ n) (hword : Fintype.card K ≤ 2 ^ w) :
    VerifyOnceData n K ↪ (Fin ((5 * w + 3) * n) → Bool) := by
  have hcap : Fintype.card (VerifyOnceData n K) ≤
      Fintype.card (Fin ((5 * w + 3) * n) → Bool) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    exact (verify_data_bit_capacity n w K hword).trans
      (Nat.pow_le_pow_right (by decide) (verify_data_bits_linear n w hn))
  exact ((Fintype.equivFin (VerifyOnceData n K)).toEmbedding.trans
    (Fin.castLEEmb hcap)).trans (Fintype.equivFin _).symm.toEmbedding

end Qatlib.Papers.MatProdVerify04.MainResults
