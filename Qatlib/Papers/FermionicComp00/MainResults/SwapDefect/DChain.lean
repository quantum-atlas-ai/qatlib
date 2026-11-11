/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FermionicComp00.MainResults.SwapDefect.TwoLfm

/-!
# Defect-chain conversion of two-mode operators

The module computes Jordan-Wigner signs and the action of creation and annihilation products on
basis vectors. These calculations identify parity-preserving fermionic two-mode operators with
qubit operators conjugated by `swapDefectChain`, and establish the inverse conversion.

These constructions belong to the formalization of [BravyiKitaev2002].

## Main statements

* `lfmUnit2_eq_chain`: converts a parity-compatible fermionic matrix unit.
* `lfmApply2_eq_qubitApply2_chain`: converts a parity-preserving two-mode matrix.
* `qubitApply2_eq_chain_lfm`: gives the reverse conversion.

## References

* [Bravyi and Kitaev, 2002][BravyiKitaev2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner

namespace Qatlib.Papers.FermionicComp00.MainResults.SwapDefect

/-- The Jordan-Wigner sign is the product of occupation signs over positions preceding `i`. -/
theorem jwSign_eq_prod {m : ℕ} (i : Fin m) (x : Reg m) :
    jwSign i x = ∏ s : Fin m, (if s.val < i.val then (if x s then (-1 : ℂ) else 1) else 1) := by
  rw [jwSign_eq, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  by_cases hs : s.val < i.val
  · rw [if_pos hs]
    by_cases hx : x s <;> simp [hs, hx]
  · rw [if_neg hs]; simp [hs]

/-- Updating the bit at `i` does not change its own Jordan-Wigner sign. -/
theorem jwSign_update_self {m : ℕ} (i : Fin m) (x : Reg m) (b : Bool) :
    jwSign i (Function.update x i b) = jwSign i x := by
  rw [jwSign_eq_prod, jwSign_eq_prod]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  by_cases hs : s.val < i.val
  · rw [if_pos hs, if_pos hs]
    have hsi : s ≠ i := by
      intro h; rw [h] at hs; exact absurd hs (lt_irrefl _)
    rw [Function.update_apply, if_neg hsi]
  · rw [if_neg hs, if_neg hs]

/-- Updating a bit preceding `i` makes the product of the new and old Jordan-Wigner signs equal
to the product of the new and old occupation signs at that bit. -/
theorem jwSign_update_lt_mul {m : ℕ} {i t : Fin m} (h : t.val < i.val) (x : Reg m) (b : Bool) :
    jwSign i (Function.update x t b) * jwSign i x =
      (if b then (-1 : ℂ) else 1) * (if x t then (-1 : ℂ) else 1) := by
  rw [jwSign_eq_prod, jwSign_eq_prod, ← Finset.prod_mul_distrib]
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ t)]
  have hrest : (∏ s ∈ (Finset.univ : Finset (Fin m)) \ {t},
      ((if s.val < i.val then
          (if (Function.update x t b) s then (-1 : ℂ) else 1) else 1) *
        (if s.val < i.val then (if x s then (-1 : ℂ) else 1) else 1))) = 1 := by
    refine Finset.prod_eq_one (fun s hs => ?_)
    have hst : s ≠ t := by
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hs
      exact hs.2
    have hupd : (Function.update x t b) s = x s := by
      rw [Function.update_apply, if_neg hst]
    rw [hupd]
    by_cases hs2 : s.val < i.val
    · rw [if_pos hs2]
      by_cases hx : x s <;> simp [hx]
    · rw [if_neg hs2]; simp
  rw [hrest, mul_one]
  simp [h, Function.update_self]

/-- Updating a bit preceding `i` multiplies its Jordan-Wigner sign by the product of the old and
new occupation signs at that bit. -/
theorem jwSign_update_lt {m : ℕ} {i t : Fin m} (h : t.val < i.val) (x : Reg m) (b : Bool) :
    jwSign i (Function.update x t b) =
      jwSign i x * ((if b then (-1 : ℂ) else 1) * (if x t then (-1 : ℂ) else 1)) := by
  have hsq : jwSign i x * jwSign i x = 1 := jwSign_sq i x
  calc jwSign i (Function.update x t b)
      = jwSign i (Function.update x t b) * (jwSign i x * jwSign i x) := by
          rw [hsq, mul_one]
    _ = (jwSign i (Function.update x t b) * jwSign i x) * jwSign i x := by ring
    _ = ((if b then (-1 : ℂ) else 1) * (if x t then (-1 : ℂ) else 1)) * jwSign i x := by
          rw [jwSign_update_lt_mul h]
    _ = jwSign i x * ((if b then (-1 : ℂ) else 1) * (if x t then (-1 : ℂ) else 1)) := by ring

/-- Every even natural power of a Jordan-Wigner sign is one. -/
theorem jwSign_pow_even {m : ℕ} (i : Fin m) (x : Reg m) (k : ℕ) :
    jwSign i x ^ (2 * k) = 1 := by
  rw [pow_mul, pow_two, jwSign_sq, one_pow]

/-- The register obtained by clearing position `i` when `b` is true and leaving the register
unchanged otherwise. -/
def clearBit {m : ℕ} (i : Fin m) (b : Bool) (x : Reg m) : Reg m :=
  if b then Function.update x i false else x

/-- The register obtained by setting position `i` when `b` is true and leaving the register
unchanged otherwise. -/
def setBit {m : ℕ} (i : Fin m) (b : Bool) (x : Reg m) : Reg m :=
  if b then Function.update x i true else x

/-- Clearing a bit with control `true` updates that position to `false`. -/
theorem clearBit_true_eq {m : ℕ} (i : Fin m) (x : Reg m) :
    clearBit i true x = Function.update x i false := by simp [clearBit]

/-- Clearing a bit with control `false` leaves the register unchanged. -/
theorem clearBit_false_eq {m : ℕ} (i : Fin m) (x : Reg m) : clearBit i false x = x := by
  simp [clearBit]

/-- The Boolean-controlled power of annihilation acts on a basis vector by conditional clearing
with its Jordan-Wigner sign, or gives zero when the required occupation is absent. -/
theorem annihilation_pow_mulVec_ket {m : ℕ} (i : Fin m) (b : Bool) (x : Reg m) :
    annihilation i ^ bitNat b *ᵥ ket x =
      (if (if b then x i else true) then
        (jwSign i x ^ bitNat b) • ket (clearBit i b x) else 0) := by
  cases b <;> simp [bitNat, clearBit, annihilation_mulVec_ket]

/-- The Boolean-controlled power of creation acts on a basis vector by conditional setting with
its Jordan-Wigner sign, or gives zero when the required vacancy is absent. -/
theorem creation_pow_mulVec_ket {m : ℕ} (i : Fin m) (b : Bool) (x : Reg m) :
    creation i ^ bitNat b *ᵥ ket x =
      (if (if b then !x i else true) then
        (jwSign i (setBit i b x) ^ bitNat b) • ket (setBit i b x) else 0) := by
  cases b
  · simp [bitNat, setBit]
  · simp only [bitNat, if_true, pow_one]
    rw [creation_mulVec_ket]
    cases x i <;> simp [setBit]

/-- Conditional clearing leaves every position different from the selected one unchanged. -/
theorem clearBit_apply_ne {m : ℕ} {i k : Fin m} (h : k ≠ i) (b : Bool) (x : Reg m) :
    clearBit i b x k = x k := by
  unfold clearBit
  by_cases hb : b
  · rw [if_pos hb, Function.update_apply, if_neg h]
  · rw [if_neg hb]

/-- Conditional setting leaves every position different from the selected one unchanged. -/
theorem setBit_apply_ne {m : ℕ} {i k : Fin m} (h : k ≠ i) (b : Bool) (x : Reg m) :
    setBit i b x k = x k := by
  unfold setBit
  by_cases hb : b
  · rw [if_pos hb, Function.update_apply, if_neg h]
  · rw [if_neg hb]

/-- Clearing an occupied earlier bit, when requested, multiplies the later Jordan-Wigner sign by
the corresponding power of negative one. -/
theorem jwSign_clearBit {m : ℕ} {j k : Fin m} (hjk : j.val < k.val) (q0 : Bool)
    (x : Reg m) (hj : (if q0 then x j else true) = true) :
    jwSign k (clearBit j q0 x) = jwSign k x * (-1 : ℂ) ^ (bitNat q0) := by
  unfold clearBit
  by_cases hb : q0
  · rw [if_pos hb, jwSign_update_lt hjk]
    have hxj : x j = true := by rw [if_pos hb] at hj; exact hj
    simp [bitNat, hb, hxj]
  · rw [if_neg hb]
    simp [bitNat, hb]

/-- Two Boolean-controlled annihilations at ordered positions clear the selected occupations
with the product of Jordan-Wigner signs and the crossing sign, and otherwise give zero. -/
theorem down_mulVec_ket {m : ℕ} {j k : Fin m} (hjk : j.val < k.val) (q0 q1 : Bool)
    (x : Reg m) :
    (annihilation k ^ bitNat q1 * annihilation j ^ bitNat q0) *ᵥ ket x =
      (if (if q0 then x j else true) ∧ (if q1 then x k else true) then
        ((jwSign j x ^ bitNat q0) * (jwSign k x ^ bitNat q1) *
          (-1 : ℂ) ^ (bitNat q0 * bitNat q1)) •
        ket (clearBit k q1 (clearBit j q0 x)) else 0) := by
  have hne : k ≠ j := by
    intro h; rw [h] at hjk; exact absurd hjk (lt_irrefl _)
  rw [← Matrix.mulVec_mulVec, annihilation_pow_mulVec_ket]
  by_cases hj : (if q0 then x j else true)
  · rw [if_pos hj, Matrix.mulVec_smul, annihilation_pow_mulVec_ket]
    have hk_eq : (if q1 then (clearBit j q0 x) k else true) = (if q1 then x k else true) := by
      rw [clearBit_apply_ne hne]
    by_cases hk : (if q1 then x k else true)
    · rw [hk_eq, if_pos hk, if_pos ⟨hj, hk⟩, smul_smul]
      congr 1
      rw [jwSign_clearBit hjk q0 x hj, mul_pow, ← pow_mul]
      ring
    · rw [hk_eq, if_neg hk, if_neg (fun hc => hk hc.2), smul_zero]
  · rw [if_neg hj, Matrix.mulVec_zero, if_neg (fun hc => hj hc.1)]

/-- When the selected occupations equal `q0` and `q1`, the two controlled annihilations give the
cleared basis vector with the specified Jordan-Wigner and crossing signs. -/
theorem down_mulVec_ket_of {m : ℕ} {j k : Fin m} (hjk : j.val < k.val) (q0 q1 : Bool)
    (x : Reg m) (hx0 : x j = q0) (hx1 : x k = q1) :
    (annihilation k ^ bitNat q1 * annihilation j ^ bitNat q0) *ᵥ ket x =
      ((jwSign j x ^ bitNat q0) * (jwSign k x ^ bitNat q1) *
        (-1 : ℂ) ^ (bitNat q0 * bitNat q1)) •
        ket (clearBit k q1 (clearBit j q0 x)) := by
  rw [down_mulVec_ket hjk q0 q1 x]
  have hcond : ((if q0 then x j else true) ∧ (if q1 then x k else true)) := by
    constructor
    · rw [hx0]; cases q0 <;> simp
    · rw [hx1]; cases q1 <;> simp
  rw [if_pos hcond]

/-- Conditional setting at `i` leaves the Jordan-Wigner sign at `i` unchanged. -/
theorem jwSign_setBit_self {m : ℕ} (i : Fin m) (b : Bool) (x : Reg m) :
    jwSign i (setBit i b x) = jwSign i x := by
  unfold setBit
  by_cases hb : b
  · rw [if_pos hb]; exact jwSign_update_self i x true
  · rw [if_neg hb]

/-- Conditional setting at a later position leaves an earlier Jordan-Wigner sign unchanged. -/
theorem jwSign_setBit_gt {m : ℕ} {i k : Fin m} (h : i.val < k.val) (b : Bool) (x : Reg m) :
    jwSign i (setBit k b x) = jwSign i x := by
  rw [jwSign_eq_prod, jwSign_eq_prod]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  by_cases hs : s.val < i.val
  · rw [if_pos hs, if_pos hs]
    have hsk : s ≠ k := by intro h'; rw [h'] at hs; omega
    rw [setBit_apply_ne hsk]
  · rw [if_neg hs, if_neg hs]

/-- On a register vacant at two ordered positions, controlled creation produces the set register
with the product of the two Jordan-Wigner sign powers. -/
theorem up_mulVec_ket {m : ℕ} {j k : Fin m} (hjk : j.val < k.val) (p0 p1 : Bool)
    (x : Reg m) (hx : x j = false ∧ x k = false) :
    (creation j ^ bitNat p0 * creation k ^ bitNat p1) *ᵥ ket x =
      ((jwSign j x ^ bitNat p0) * (jwSign k x ^ bitNat p1)) •
        ket (setBit j p0 (setBit k p1 x)) := by
  have hkj : j ≠ k := by intro h; rw [h] at hjk; exact absurd hjk (lt_irrefl _)
  rw [← Matrix.mulVec_mulVec, creation_pow_mulVec_ket]
  have hkcond : (if p1 then !x k else true) = true := by
    cases p1 <;> simp [hx.2]
  rw [if_pos hkcond, Matrix.mulVec_smul, creation_pow_mulVec_ket]
  have hjbit : (setBit k p1 x) j = false := by
    rw [setBit_apply_ne hkj]; exact hx.1
  have hjcond : (if p0 then !(setBit k p1 x) j else true) = true := by
    cases p0 <;> simp [hjbit]
  rw [if_pos hjcond, smul_smul]
  have hcj : jwSign j (setBit j p0 (setBit k p1 x)) = jwSign j x := by
    rw [jwSign_setBit_self, jwSign_setBit_gt hjk]
  have hck : jwSign k (setBit k p1 x) = jwSign k x := jwSign_setBit_self k p1 x
  rw [hcj, hck, mul_comm]

/-- The scalar product of intermediate-mode occupation signs forming the diagonal of
`swapDefectChain`. -/
def chainDiag {m : ℕ} (j k : Fin m) (x : Reg m) : ℂ :=
  ∏ s ∈ (Finset.univ.filter (fun s : Fin m => j < s ∧ s < k)),
    ((-1 : ℂ) ^ (if x s ∧ x k then 1 else 0))

/-- A basis vector is an eigenvector of the swap-defect chain with eigenvalue `chainDiag j k x`. -/
theorem swapDefectChain_mulVec_ket {m : ℕ} (j k : Fin m) (x : Reg m) :
    swapDefectChain j k *ᵥ ket x = chainDiag j k x • ket x := by
  rw [swapDefectChain]
  funext y
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, ket_apply]
  by_cases hy : y = x <;> simp [hy, chainDiag]

/-- Converting a Boolean conjunction to a natural number gives the product of the two
Boolean-to-natural values. -/
theorem bitNat_and (a b : Bool) : bitNat (a && b) = bitNat a * bitNat b := by
  cases a <;> cases b <;> simp [bitNat]

/-- At ordered endpoints, the later Jordan-Wigner sign splits into the earlier sign, the
occupation sign at the earlier endpoint, and the intermediate sign product. -/
theorem jwSign_split {m : ℕ} {j k : Fin m} (hjk : j.val < k.val) (x : Reg m) :
    jwSign k x = jwSign j x * ((-1 : ℂ) ^ (bitNat (x j))) * jwSignProd j k x := by
  set g : Fin m → ℂ := fun s => if x s then (-1 : ℂ) else 1 with hg
  have hconv : ∀ i : Fin m,
      (∏ s : Fin m, (if s.val < i.val then (if x s then (-1 : ℂ) else 1) else 1))
        = ∏ s ∈ Finset.univ.filter (fun s : Fin m => s.val < i.val), g s := by
    intro i
    rw [Finset.prod_filter]
  have hmem : j ∈ Finset.univ.filter (fun s : Fin m => ¬ s.val < j.val ∧ s.val < k.val) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hsplit :
      (∏ s ∈ Finset.univ.filter (fun s : Fin m => s.val < k.val), g s)
        = (∏ s ∈ Finset.univ.filter (fun s : Fin m => s.val < j.val), g s) * g j *
          (∏ s ∈ Finset.univ.filter (fun s : Fin m => j < s ∧ s < k), g s) := by
    rw [← Finset.prod_filter_mul_prod_filter_not
      (s := Finset.univ.filter (fun s : Fin m => s.val < k.val))
      (p := fun s : Fin m => s.val < j.val) (f := g)]
    have h1 : (Finset.univ.filter (fun s : Fin m => s.val < k.val)).filter
          (fun s : Fin m => s.val < j.val)
        = Finset.univ.filter (fun s : Fin m => s.val < j.val) := by
      ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have h2 : (Finset.univ.filter (fun s : Fin m => s.val < k.val)).filter
          (fun s : Fin m => ¬ s.val < j.val)
        = Finset.univ.filter (fun s : Fin m => ¬ s.val < j.val ∧ s.val < k.val) := by
      ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
    rw [h1, h2, Finset.prod_eq_mul_prod_diff_singleton_of_mem hmem]
    have h3 : (Finset.univ.filter (fun s : Fin m => ¬ s.val < j.val ∧ s.val < k.val)) \ {j}
        = Finset.univ.filter (fun s : Fin m => j < s ∧ s < k) := by
      ext s
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton,
        true_and]
      omega
    rw [h3, mul_assoc]
  have hgj : g j = (-1 : ℂ) ^ (bitNat (x j)) := by
    by_cases hx : x j <;> simp [hg, bitNat, hx]
  have hgprod :
      (∏ s ∈ Finset.univ.filter (fun s : Fin m => j < s ∧ s < k), g s)
        = ∏ s ∈ Finset.univ.filter (fun s : Fin m => j < s ∧ s < k), (-1 : ℂ) ^ (bitNat (x s)) := by
    refine Finset.prod_congr rfl (fun s _ => ?_)
    simp [hg, bitNat]
  rw [jwSign_eq_prod, jwSign_eq_prod, jwSignProd, hconv k, hconv j, hsplit, hgj, hgprod]

/-- The chain diagonal is the intermediate Jordan-Wigner sign product raised to the occupation
bit at `k`. -/
theorem chainDiag_eq {m : ℕ} (j k : Fin m) (x : Reg m) :
    chainDiag j k x = jwSignProd j k x ^ (bitNat (x k)) := by
  rw [chainDiag, jwSignProd, ← Finset.prod_pow]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  show (-1 : ℂ) ^ (if x s ∧ x k then 1 else 0) = ((-1 : ℂ) ^ (bitNat (x s))) ^ (bitNat (x k))
  rw [← pow_mul, ← bitNat_and]
  simp [bitNat, Bool.and_eq_true]

/-- Updating either endpoint leaves the intermediate Jordan-Wigner sign product unchanged. -/
theorem jwSignProd_update {m : ℕ} {j k : Fin m} (a b : Bool) (x : Reg m) :
    jwSignProd j k (Function.update (Function.update x j a) k b) = jwSignProd j k x := by
  rw [jwSignProd, jwSignProd]
  refine Finset.prod_congr rfl (fun s hs => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
  have hsj : s ≠ j := by intro h; rw [h] at hs; exact absurd hs.1 (lt_irrefl _)
  have hsk : s ≠ k := by intro h; rw [h] at hs; exact absurd hs.2 (lt_irrefl _)
  rw [Function.update_apply, if_neg hsk, Function.update_apply, if_neg hsj]

/-- The sign coefficient combining endpoint Jordan-Wigner powers and crossing signs for a
two-mode fermionic matrix unit. -/
def twoCoef {m : ℕ} (p q : Reg 2) (j k : Fin m) (x : Reg m) : ℂ :=
  jwSign j x ^ (bitNat (p 0) + bitNat (q 0)) *
    jwSign k x ^ (bitNat (p 1) + bitNat (q 1)) *
    (-1 : ℂ) ^ (bitNat (q 0) * (bitNat (q 1) + bitNat (p 1)))

/-- The intermediate Jordan-Wigner sign product raised to the sum of the input and output
occupation bits at the second selected mode. -/
def pairCoef {m : ℕ} (p q : Reg 2) (j k : Fin m) (x : Reg m) : ℂ :=
  jwSignProd j k x ^ (bitNat (p 1) + bitNat (q 1))

/-- For ordered modes and even total input-output occupation parity, the fermionic coefficient
equals the intermediate pair coefficient when the first input occupation matches. -/
theorem twoCoef_eq_pairCoef {m : ℕ} {j k : Fin m} (hjk : j.val < k.val) (p q : Reg 2)
    (x : Reg m) (hpar : (bitNat (p 0) + bitNat (p 1) + bitNat (q 0) + bitNat (q 1)) % 2 = 0)
    (hx0 : x j = q 0) :
    twoCoef p q j k x = pairCoef p q j k x := by
  have hsplit := jwSign_split hjk x
  have hsq : jwSign j x ^ 2 = 1 := by rw [pow_two, jwSign_sq]
  cases hp0 : p 0 <;> cases hp1 : p 1 <;> cases hq0 : q 0 <;> cases hq1 : q 1
  all_goals
    simp only [twoCoef, pairCoef]
    rw [hsplit]
    simp [bitNat, hp0, hp1, hq0, hq1, hx0, pow_two, jwSign_sq] at hpar ⊢
    try ring_nf
    try simp [hsq]

/-- The product of chain diagonals before and after replacing the endpoint occupations equals
`pairCoef`, when the second input occupation matches. -/
theorem chainDiag_update {m : ℕ} {j k : Fin m} (hjk : j.val < k.val) (p q : Reg 2)
    (x : Reg m) (hx1 : x k = q 1) :
    chainDiag j k x * chainDiag j k (Function.update (Function.update x j (p 0)) k (p 1))
      = pairCoef p q j k x := by
  rw [chainDiag_eq, chainDiag_eq, jwSignProd_update, hx1, Function.update_self, pairCoef,
    ← pow_add, Nat.add_comm (bitNat (q 1)) (bitNat (p 1))]

/-- Conditional clearing at `i` leaves its own Jordan-Wigner sign unchanged. -/
theorem jwSign_clearBit_self {m : ℕ} (i : Fin m) (b : Bool) (x : Reg m) :
    jwSign i (clearBit i b x) = jwSign i x := by
  unfold clearBit
  by_cases hb : b
  · rw [if_pos hb]; exact jwSign_update_self i x false
  · rw [if_neg hb]

/-- Updating a later position leaves an earlier Jordan-Wigner sign unchanged. -/
theorem jwSign_update_gt {m : ℕ} {i k : Fin m} (h : i.val < k.val) (b : Bool) (x : Reg m) :
    jwSign i (Function.update x k b) = jwSign i x := by
  rw [jwSign_eq_prod, jwSign_eq_prod]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  by_cases hs : s.val < i.val
  · rw [if_pos hs, if_pos hs]
    have hsk : s ≠ k := by intro h'; rw [h'] at hs; omega
    rw [Function.update_apply, if_neg hsk]
  · rw [if_neg hs, if_neg hs]

/-- Conditional clearing at a later position leaves an earlier Jordan-Wigner sign unchanged. -/
theorem jwSign_clearBit_gt {m : ℕ} {i k : Fin m} (h : i.val < k.val) (b : Bool) (x : Reg m) :
    jwSign i (clearBit k b x) = jwSign i x := by
  unfold clearBit
  by_cases hb : b
  · rw [if_pos hb]; exact jwSign_update_gt h false x
  · rw [if_neg hb]

/-- Replacing a true Boolean by false and leaving a false Boolean unchanged always gives false. -/
theorem ite_false_self (b : Bool) : (if b then false else b) = false := by
  cases b <;> rfl

/-- Replacing both selected occupations agrees with clearing the matching input occupations and
then setting the output occupations. -/
theorem update_update_eq_setBit {m : ℕ} {j k : Fin m} (hjk : j.val < k.val) (p q : Reg 2)
    (x : Reg m) (hx0 : x j = q 0) (hx1 : x k = q 1) :
    Function.update (Function.update x j (p 0)) k (p 1) =
      setBit j (p 0) (setBit k (p 1) (clearBit k (q 1) (clearBit j (q 0) x))) := by
  have hkj : j ≠ k := by intro h; rw [h] at hjk; exact absurd hjk (lt_irrefl _)
  have hne : k ≠ j := hkj.symm
  funext t
  cases hp0 : p 0 <;> cases hp1 : p 1 <;> cases hq0 : q 0 <;> cases hq1 : q 1
  all_goals
    by_cases htj : t = j
    · simp [setBit, clearBit, Function.update_apply, htj, hkj, hne, hx0, hp0, hp1, hq0, hq1]
    · by_cases htk : t = k
      · simp [setBit, clearBit, Function.update_apply, htj, htk, hkj, hne, hx0, hx1, hp0, hp1, hq0,
          hq1]
      · simp [setBit, clearBit, Function.update_apply, htj, htk]

/-- Clearing the matching input occupations leaves both selected modes vacant. -/
theorem clearBit_pair_vac {m : ℕ} {j k : Fin m} (hjk : j.val < k.val) (q : Reg 2)
    (x : Reg m) (hx0 : x j = q 0) (hx1 : x k = q 1) :
    (clearBit k (q 1) (clearBit j (q 0) x)) j = false ∧
      (clearBit k (q 1) (clearBit j (q 0) x)) k = false := by
  have hkj : j ≠ k := by intro h; rw [h] at hjk; exact absurd hjk (lt_irrefl _)
  have hne : k ≠ j := hkj.symm
  constructor
  · rw [clearBit_apply_ne hkj]
    cases hq0 : q 0
    · rw [clearBit_false_eq, hx0]
      exact hq0
    · rw [clearBit_true_eq, Function.update_self]
  · cases hq1 : q 1
    · rw [clearBit_false_eq, clearBit_apply_ne hne, hx1]
      exact hq1
    · rw [clearBit_true_eq, Function.update_self]

/-- Clearing both selected modes leaves the Jordan-Wigner sign at the earlier mode unchanged. -/
theorem jwSign_j_clearBit_pair {m : ℕ} {j k : Fin m} (hjk : j.val < k.val) (q : Reg 2)
    (x : Reg m) :
    jwSign j (clearBit k (q 1) (clearBit j (q 0) x)) = jwSign j x := by
  rw [jwSign_clearBit_gt hjk, jwSign_clearBit_self]

/-- Clearing both selected modes changes the later Jordan-Wigner sign by the sign of the
requested earlier annihilation, under its occupation condition. -/
theorem jwSign_k_clearBit_pair {m : ℕ} {j k : Fin m} (hjk : j.val < k.val) (q : Reg 2)
    (x : Reg m) (hj : (if q 0 then x j else true) = true) :
    jwSign k (clearBit k (q 1) (clearBit j (q 0) x)) =
      jwSign k x * (-1 : ℂ) ^ (bitNat (q 0)) := by
  rw [jwSign_clearBit_self, jwSign_clearBit hjk (q 0) x hj]

/-- The fermionic matrix unit factors into its creation operators and two-mode vacuum
projection, followed by its annihilation operators. -/
theorem lfmUnit2_assoc {m : ℕ} (p q : Reg 2) (j k : Fin m) :
    lfmUnit2 p q j k =
      (creation j ^ bitNat (p 0) * creation k ^ bitNat (p 1) *
        ((1 - numberOp j) * (1 - numberOp k))) *
      (annihilation k ^ bitNat (q 1) * annihilation j ^ bitNat (q 0)) := by
  rw [lfmUnit2]
  exact mul_assoc _ _ _

/-- The product of the annihilation and creation sign factors is the coefficient `twoCoef`. -/
theorem coef_mul_eq_twoCoef {m : ℕ} (p q : Reg 2) (j k : Fin m) (x : Reg m) :
    (jwSign j x ^ bitNat (q 0) * jwSign k x ^ bitNat (q 1) *
        (-1 : ℂ) ^ (bitNat (q 0) * bitNat (q 1))) *
      (jwSign j x ^ bitNat (p 0) *
        (jwSign k x * (-1 : ℂ) ^ (bitNat (q 0))) ^ bitNat (p 1))
      = twoCoef p q j k x := by
  cases hp0 : p 0 <;> cases hp1 : p 1 <;> cases hq0 : q 0 <;> cases hq1 : q 1
  all_goals
    simp [twoCoef, bitNat, hp0, hp1, hq0, hq1]
    try ring_nf

/-- On a matching input basis configuration, the fermionic matrix unit replaces the two
occupations and multiplies by `twoCoef`. -/
theorem lfmUnit2_mulVec_ket_pos {m : ℕ} {j k : Fin m} (hjk : j.val < k.val) (p q : Reg 2)
    (x : Reg m) (hx0 : x j = q 0) (hx1 : x k = q 1) :
    lfmUnit2 p q j k *ᵥ ket x =
      twoCoef p q j k x •
        ket (Function.update (Function.update x j (p 0)) k (p 1)) := by
  obtain ⟨hz0, hz1⟩ := clearBit_pair_vac hjk q x hx0 hx1
  have hvac : ((1 - numberOp j) * (1 - numberOp k) : Matrix (Reg m) (Reg m) ℂ) *ᵥ
      ket (clearBit k (q 1) (clearBit j (q 0) x)) =
      ket (clearBit k (q 1) (clearBit j (q 0) x)) := by
    rw [vacuumProj_mulVec_ket]
    simp [hz0, hz1]
  have hup := up_mulVec_ket hjk (p 0) (p 1) (clearBit k (q 1) (clearBit j (q 0) x)) ⟨hz0, hz1⟩
  have hjcond : (if q 0 then x j else true) = true := by rw [hx0]; cases q 0 <;> simp
  have hpj := jwSign_j_clearBit_pair hjk q x
  have hpk := jwSign_k_clearBit_pair hjk q x hjcond
  rw [lfmUnit2_assoc, ← Matrix.mulVec_mulVec,
    down_mulVec_ket_of hjk (q 0) (q 1) x hx0 hx1, Matrix.mulVec_smul,
    ← Matrix.mulVec_mulVec, hvac, hup, smul_smul,
    update_update_eq_setBit hjk p q x hx0 hx1]
  congr 1
  rw [hpj, hpk, coef_mul_eq_twoCoef]

/-- A fermionic two-mode matrix unit annihilates basis configurations whose selected occupations
do not match its input label. -/
theorem lfmUnit2_mulVec_ket_neg {m : ℕ} {j k : Fin m} (hjk : j.val < k.val) (p q : Reg 2)
    (x : Reg m) (hnc : ¬ (x j = q 0 ∧ x k = q 1)) :
    lfmUnit2 p q j k *ᵥ ket x = 0 := by
  have hkj : j ≠ k := by intro h; rw [h] at hjk; exact absurd hjk (lt_irrefl _)
  have hne : k ≠ j := hkj.symm
  rw [lfmUnit2_assoc, ← Matrix.mulVec_mulVec, down_mulVec_ket hjk (q 0) (q 1) x]
  by_cases hc : ((if q 0 then x j else true) ∧ (if q 1 then x k else true))
  · have hyj : (clearBit k (q 1) (clearBit j (q 0) x)) j = false → x j = q 0 := by
      intro e
      rw [clearBit_apply_ne hkj] at e
      cases hq0 : q 0
      · rw [hq0] at e
        rw [clearBit_false_eq] at e
        rw [e]
      · have hx : x j = true := by simpa [hq0] using! hc.1
        rw [hx]
    have hyk : (clearBit k (q 1) (clearBit j (q 0) x)) k = false → x k = q 1 := by
      intro e
      cases hq1 : q 1
      · rw [hq1] at e
        rw [clearBit_false_eq, clearBit_apply_ne hne] at e
        rw [e]
      · have hx : x k = true := by simpa [hq1] using! hc.2
        rw [hx]
    rw [if_pos hc, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec]
    have hvac0 : ((1 - numberOp j) * (1 - numberOp k) : Matrix (Reg m) (Reg m) ℂ) *ᵥ
        ket (clearBit k (q 1) (clearBit j (q 0) x)) = 0 := by
      rw [vacuumProj_mulVec_ket]
      by_cases e0 : (clearBit k (q 1) (clearBit j (q 0) x)) j = false
      · by_cases e1 : (clearBit k (q 1) (clearBit j (q 0) x)) k = false
        · exact absurd ⟨hyj e0, hyk e1⟩ hnc
        · have h1 : (clearBit k (q 1) (clearBit j (q 0) x)) k = true := by
            cases hv : (clearBit k (q 1) (clearBit j (q 0) x)) k <;> simp_all
          rw [e0, h1]; simp
      · have h0 : (clearBit k (q 1) (clearBit j (q 0) x)) j = true := by
          cases hv : (clearBit k (q 1) (clearBit j (q 0) x)) j <;> simp_all
        rw [h0]; simp
    rw [hvac0, Matrix.mulVec_zero, smul_zero]
  · rw [if_neg hc, Matrix.mulVec_zero]

/-- A fermionic two-mode matrix unit conditionally replaces the selected occupations with
coefficient `twoCoef`, and is zero on nonmatching inputs. -/
theorem lfmUnit2_mulVec_ket {m : ℕ} {j k : Fin m} (hjk : j.val < k.val) (p q : Reg 2)
    (x : Reg m) :
    lfmUnit2 p q j k *ᵥ ket x =
      (if x j = q 0 ∧ x k = q 1 then
        twoCoef p q j k x •
          ket (Function.update (Function.update x j (p 0)) k (p 1)) else 0) := by
  by_cases hc : x j = q 0 ∧ x k = q 1
  · rw [if_pos hc]; exact lfmUnit2_mulVec_ket_pos hjk p q x hc.1 hc.2
  · rw [if_neg hc]; exact lfmUnit2_mulVec_ket_neg hjk p q x hc

/-- Conjugating a qubit matrix unit by the defect chain conditionally replaces the selected
occupations with coefficient `pairCoef`. See [BravyiKitaev2002]. -/
theorem swapDefectChain_conj_mulVec_ket {m : ℕ} {j k : Fin m} (hjk : j.val < k.val)
    (p q : Reg 2) (x : Reg m) :
    (swapDefectChain j k * qubitUnit2 p q j k * swapDefectChain j k) *ᵥ ket x =
      (if x j = q 0 ∧ x k = q 1 then
        pairCoef p q j k x • ket (Function.update (Function.update x j (p 0)) k (p 1)) else 0) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, swapDefectChain_mulVec_ket,
    Matrix.mulVec_smul, qubitUnit2_mulVec_ket]
  by_cases hc : x j = q 0 ∧ x k = q 1
  · rw [if_pos hc, Matrix.mulVec_smul, swapDefectChain_mulVec_ket, smul_smul, if_pos hc,
      chainDiag_update hjk p q x hc.2]
  · rw [if_neg hc, smul_zero, Matrix.mulVec_zero, if_neg hc]

/-- For ordered modes and even total input-output occupation parity, the fermionic matrix unit
is the qubit matrix unit conjugated by the defect chain. [BravyiKitaev2002] -/
theorem lfmUnit2_eq_chain {m : ℕ} {j k : Fin m} (hjk : j.val < k.val) (p q : Reg 2)
    (hpar : (bitNat (p 0) + bitNat (p 1) + bitNat (q 0) + bitNat (q 1)) % 2 = 0) :
    lfmUnit2 p q j k = swapDefectChain j k * qubitUnit2 p q j k * swapDefectChain j k := by
  ext y x
  rw [← mulVec_ket_apply (M := lfmUnit2 p q j k),
    ← mulVec_ket_apply (M := swapDefectChain j k * qubitUnit2 p q j k * swapDefectChain j k),
    lfmUnit2_mulVec_ket hjk p q x, swapDefectChain_conj_mulVec_ket hjk p q x]
  by_cases hc : x j = q 0 ∧ x k = q 1
  · rw [if_pos hc, if_pos hc, twoCoef_eq_pairCoef hjk p q x hpar hc.1]
  · rw [if_neg hc, if_neg hc]

/-- For ordered modes and even total input-output occupation parity, the qubit matrix unit is
the fermionic matrix unit conjugated by the defect chain. See [BravyiKitaev2002]. -/
theorem qubitUnit2_eq_chain {m : ℕ} {j k : Fin m} (hjk : j.val < k.val) (p q : Reg 2)
    (hpar : (bitNat (p 0) + bitNat (p 1) + bitNat (q 0) + bitNat (q 1)) % 2 = 0) :
    qubitUnit2 p q j k = swapDefectChain j k * lfmUnit2 p q j k * swapDefectChain j k := by
  rw [lfmUnit2_eq_chain hjk p q hpar]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, swapDefectChain_mul_self, Matrix.one_mul,
    Matrix.mul_assoc, swapDefectChain_mul_self, Matrix.mul_one]

/-- A parity-preserving two-mode matrix has fermionic placement equal to its qubit matrix-unit
expansion conjugated by the defect chain. -/
theorem lfmApply2_eq_chain {m : ℕ} {j k : Fin m} (hjk : j.val < k.val)
    (X : Matrix (Reg 2) (Reg 2) ℂ)
    (hpar : ∀ p q : Reg 2, X p q ≠ 0 →
      (bitNat (p 0) + bitNat (p 1) + bitNat (q 0) + bitNat (q 1)) % 2 = 0) :
    lfmApply2 X j k =
      swapDefectChain j k *
        (∑ p : Reg 2, ∑ q : Reg 2, X p q • qubitUnit2 p q j k) *
        swapDefectChain j k := by
  rw [lfmApply2]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  by_cases hX : X p q = 0
  · rw [hX, zero_smul, zero_smul]
  · rw [lfmUnit2_eq_chain hjk p q (hpar p q hX)]

/-- The qubit matrix-unit expansion of a parity-preserving matrix equals its fermionic placement
conjugated by the defect chain. -/
theorem qubitSum_eq_chain_lfm {m : ℕ} {j k : Fin m} (hjk : j.val < k.val)
    (X : Matrix (Reg 2) (Reg 2) ℂ)
    (hpar : ∀ p q : Reg 2, X p q ≠ 0 →
      (bitNat (p 0) + bitNat (p 1) + bitNat (q 0) + bitNat (q 1)) % 2 = 0) :
    (∑ p : Reg 2, ∑ q : Reg 2, X p q • qubitUnit2 p q j k) =
      swapDefectChain j k * lfmApply2 X j k * swapDefectChain j k := by
  rw [lfmApply2]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  by_cases hX : X p q = 0
  · rw [hX, zero_smul, zero_smul]
  · rw [qubitUnit2_eq_chain hjk p q (hpar p q hX)]

/-- At distinct positions, qubit placement is the sum of placed matrix units weighted by the
matrix entries. See [BravyiKitaev2002]. -/
theorem qubitApply2_eq_sum {m : ℕ} (X : Matrix (Reg 2) (Reg 2) ℂ) {j k : Fin m}
    (hjk : j ≠ k) :
    qubitApply2 X j k = ∑ p : Reg 2, ∑ q : Reg 2, X p q • qubitUnit2 p q j k := by
  ext y x
  simp only [qubitApply2, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  let xp : Reg 2 := fun t => x (if t = 0 then j else k)
  let yp : Reg 2 := fun t => y (if t = 0 then j else k)
  have hxp0 : xp 0 = x j := rfl
  have hxp1 : xp 1 = x k := rfl
  have hyp0 : yp 0 = y j := rfl
  have hyp1 : yp 1 = y k := rfl
  change X yp xp * (∏ s ∈ Finset.univ.filter (fun s : Fin m => s ≠ j ∧ s ≠ k),
      (if y s = x s then (1 : ℂ) else 0)) =
    ∑ p : Reg 2, ∑ q : Reg 2, X p q * qubitUnit2 p q j k y x
  have hinner : ∀ p : Reg 2,
      (∑ q : Reg 2, X p q * qubitUnit2 p q j k y x) =
        X p xp * qubitUnit2 p xp j k y x := by
    intro p
    rw [Finset.sum_eq_single xp]
    · intro q _ hq
      have hq' : ¬ (x j = q 0 ∧ x k = q 1) := by
        rintro ⟨e0, e1⟩
        apply hq
        funext t
        fin_cases t
        · simp [xp, e0]
        · simp [xp, e1]
      simp only [qubitUnit2, Matrix.of_apply]
      rw [if_neg (by rintro ⟨h1, h2, -⟩; exact hq' ⟨h1, h2⟩)]
      simp
    · intro h
      simp at h
  simp_rw [hinner]
  have hsum : (∑ p : Reg 2, X p xp * qubitUnit2 p xp j k y x) =
      X yp xp * qubitUnit2 yp xp j k y x := by
    rw [Finset.sum_eq_single yp]
    · intro p _ hp
      by_cases hupd : y = Function.update (Function.update x j (p 0)) k (p 1)
      · exfalso
        apply hp
        have hp0 : p 0 = yp 0 := by
          have h1 := congrFun hupd j
          have h2 : Function.update (Function.update x j (p 0)) k (p 1) j = p 0 := by
            rw [Function.update_apply, if_neg hjk, Function.update_apply, if_pos rfl]
          rw [h2] at h1
          rw [← h1]
          exact hyp0.symm
        have hp1 : p 1 = yp 1 := by
          have h1 := congrFun hupd k
          have h2 : Function.update (Function.update x j (p 0)) k (p 1) k = p 1 := by
            rw [Function.update_apply, if_pos rfl]
          rw [h2] at h1
          rw [← h1]
          exact hyp1.symm
        funext t
        fin_cases t
        · exact hp0
        · exact hp1
      · simp only [qubitUnit2, Matrix.of_apply]
        rw [if_neg (by rintro ⟨-, -, h⟩; exact hupd h)]
        simp
    · intro h
      simp at h
  rw [hsum]
  by_cases hagree : y = Function.update (Function.update x j (yp 0)) k (yp 1)
  · have hterm : qubitUnit2 yp xp j k y x = (1 : ℂ) := by
      simp only [qubitUnit2, Matrix.of_apply]
      rw [if_pos ⟨hxp0.symm, hxp1.symm, hagree⟩]
    rw [hterm, mul_one]
    have hprod : (∏ s ∈ Finset.univ.filter (fun s : Fin m => s ≠ j ∧ s ≠ k),
        (if y s = x s then (1 : ℂ) else 0)) = 1 := by
      refine Finset.prod_eq_one (fun s hs => ?_)
      rw [Finset.mem_filter] at hs
      obtain ⟨-, hsj, hsk⟩ := hs
      have hyx : y s = x s := by
        have h1 := congrFun hagree s
        rw [h1]
        rw [Function.update_apply, if_neg hsk, Function.update_apply, if_neg hsj]
      rw [if_pos hyx]
    rw [hprod, mul_one]
  · have hterm : qubitUnit2 yp xp j k y x = 0 := by
      simp only [qubitUnit2, Matrix.of_apply]
      rw [if_neg (by rintro ⟨-, -, h⟩; exact hagree h)]
    rw [hterm, mul_zero]
    have hex : ∃ s, s ≠ j ∧ s ≠ k ∧ y s ≠ x s := by
      by_contra h
      apply hagree
      funext t
      by_cases htj : t = j
      · rw [htj]
        simp [Function.update_apply, hjk, hyp0]
      · by_cases htk : t = k
        · rw [htk]
          simp [Function.update_apply, hyp1]
        · have hyt : y t = x t := by
            by_contra hne
            exact h ⟨t, htj, htk, hne⟩
          simp [Function.update_apply, htk, htj, hyt]
    obtain ⟨s, hsj, hsk, hne⟩ := hex
    have hprod0 : (∏ s' ∈ Finset.univ.filter (fun s' : Fin m => s' ≠ j ∧ s' ≠ k),
        (if y s' = x s' then (1 : ℂ) else 0)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hsj, hsk⟩) ?_
      rw [if_neg hne]
    rw [hprod0, mul_zero]

/-- For ordered modes, fermionic placement of a parity-preserving two-mode matrix equals its
qubit placement conjugated by the defect chain. [BravyiKitaev2002] -/
theorem lfmApply2_eq_qubitApply2_chain {m : ℕ} {j k : Fin m} (hjk : j.val < k.val)
    (X : Matrix (Reg 2) (Reg 2) ℂ)
    (hpar : ∀ p q : Reg 2, X p q ≠ 0 →
      (bitNat (p 0) + bitNat (p 1) + bitNat (q 0) + bitNat (q 1)) % 2 = 0) :
    lfmApply2 X j k = swapDefectChain j k * qubitApply2 X j k * swapDefectChain j k := by
  rw [lfmApply2_eq_chain hjk X hpar, ← qubitApply2_eq_sum X (ne_of_lt hjk)]

/-- For ordered modes, qubit placement of a parity-preserving two-mode matrix equals its
fermionic placement conjugated by the defect chain. [BravyiKitaev2002] -/
theorem qubitApply2_eq_chain_lfm {m : ℕ} {j k : Fin m} (hjk : j.val < k.val)
    (X : Matrix (Reg 2) (Reg 2) ℂ)
    (hpar : ∀ p q : Reg 2, X p q ≠ 0 →
      (bitNat (p 0) + bitNat (p 1) + bitNat (q 0) + bitNat (q 1)) % 2 = 0) :
    qubitApply2 X j k = swapDefectChain j k * lfmApply2 X j k * swapDefectChain j k := by
  rw [qubitApply2_eq_sum X (ne_of_lt hjk), qubitSum_eq_chain_lfm hjk X hpar]

end Qatlib.Papers.FermionicComp00.MainResults.SwapDefect
