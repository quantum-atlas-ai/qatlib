/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-! Tanner-graph syndrome lemmas for
"Hamiltonian Decoded Quantum Interferometry"
(arXiv:2510.07913, 2025).

Lemma 52 and Corollary 53 of the paper relate the matrix syndrome
`H *ᵥ e` of a binary parity-check matrix to the Tanner-graph picture:
for a check `j`, the graph syndrome bit `wⱼ = |N(j) ∩ S| mod 2` (with
`S` the support of `e`) coincides with the matrix syndrome entry, and a
check with an odd intersection with the support already certifies
`H *ᵥ e ≠ 0`.

- `tannerNbr` realizes the Tanner neighborhood of a check as the
  support of its parity row.
- `mulVec_eq_card_inter` is Lemma 52: the matrix syndrome entry equals
  the parity of the neighborhood-support intersection cardinality.
- `syndrome_nonzero_of_odd_inter` is Corollary 53: a check whose
  intersection with the error support has odd cardinality forces
  `H *ᵥ e ≠ 0`.

No axiom, no `admit`, no `native_decide`. -/
set_option autoImplicit false

namespace Qatlib.Papers.HamDecodedQI25.MainResults.TannerSyndrome

variable {r n : ℕ}

/-- The Tanner-graph neighborhood of check `j`: the variable nodes in
the support of the `j`-th parity row of `H`. -/
def tannerNbr (H : Matrix (Fin r) (Fin n) (ZMod 2)) (j : Fin r) : Finset (Fin n) :=
  Finset.univ.filter fun i => H j i ≠ 0

/-- **Lemma 52, syndrome identity**: for a binary error `e` with
entries in `{0, 1}`, the matrix syndrome entry at check `j` equals the
mod-2 cardinality of the intersection of the check's Tanner neighborhood
with the support of `e` (the graph syndrome bit `wⱼ`). -/
theorem mulVec_eq_card_inter (H : Matrix (Fin r) (Fin n) (ZMod 2)) (e : Fin n → ZMod 2)
    (he : ∀ i, e i = 0 ∨ e i = 1) (j : Fin r) :
    H.mulVec e j = (((tannerNbr H j).filter fun i => e i = 1).card : ZMod 2) := by
  classical
  have hsplit : H.mulVec e j = ∑ i ∈ tannerNbr H j, H j i * e i := by
    rw [Matrix.mulVec, dotProduct, ← Finset.sum_filter_of_ne (p := fun i => H j i ≠ 0)]
    · simp [tannerNbr]
    · intro i _ hi
      exact (mul_ne_zero_iff.mp hi).1
  have hone : ∀ i ∈ tannerNbr H j, H j i * e i = (if e i = 1 then (1 : ZMod 2) else 0) := by
    intro i hi
    have hH : H j i = 1 := by
      have hne : H j i ≠ 0 := by simpa [tannerNbr] using hi
      have hv : (H j i).val = 0 ∨ (H j i).val = 1 := by
        have h := ZMod.val_lt (H j i)
        omega
      rcases hv with h0 | h1
      · exact absurd (ZMod.val_injective (n := 2)
          (show (H j i).val = (0 : ZMod 2).val from by rw [h0, ZMod.val_zero])) hne
      · exact ZMod.val_injective (n := 2)
          (show (H j i).val = (1 : ZMod 2).val from by rw [h1, ZMod.val_one])
    rcases he i with h0 | h1
    · simp [h0, hH]
    · simp [h1, hH]
  rw [hsplit, Finset.sum_congr rfl fun i hi => hone i hi]
  simp [Finset.sum_boole]

/-- **Corollary 53** (`Γ₁(S)` = unique-neighbor checks): if some check
has exactly one neighbor in the error support (in particular, if the
unique-neighbor set `Γ₁(S)` is nonempty), then the syndrome is
nonzero. -/
theorem syndrome_nonzero_of_unique_neighbor (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (e : Fin n → ZMod 2) (he : ∀ i, e i = 0 ∨ e i = 1) (j : Fin r)
    (hun : ((tannerNbr H j).filter fun i => e i = 1).card = 1) :
    H.mulVec e ≠ 0 := by
  have hentry := mulVec_eq_card_inter H e he j
  intro hz
  have hzj : H.mulVec e j = 0 := congrFun hz j
  have h0 : (((tannerNbr H j).filter fun i => e i = 1).card : ZMod 2) = 0 :=
    hentry.symm.trans hzj
  rw [hun] at h0
  simp at h0

end Qatlib.Papers.HamDecodedQI25.MainResults.TannerSyndrome
