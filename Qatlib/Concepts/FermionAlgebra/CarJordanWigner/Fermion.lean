/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.TrotterFormula.LieStrang.CommutatorProductFormula
import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.FermionDefs
import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.FermionHubbard

/-!
# Canonical anticommutation and Jordan–Wigner identities

The theorem `g1` collects the canonical anticommutation relations for the occupation-basis
operators `annihilation` and `creation`, their adjoint relation, and the action and idempotence
of `numberOp`. It also establishes parity involution and anticommutation, the Jordan–Wigner
Pauli representation, and annihilation of the vacuum.

The canonical relations are those of [BravyiKitaev2002], with the fermionic simulation
interpretation developed in [OrtizEtAl2001]. The proofs track the occupation-prefix sign
explicitly through basis-coordinate updates.

## Main statements

* `g1`: the canonical relations, occupation and parity identities, Jordan–Wigner formulas, and
  vacuum rule hold for every finite number of modes.

## References

* [Bravyi and Kitaev, 2002][BravyiKitaev2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 512000

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.TrotterFormula.LieStrang

namespace Qatlib.Concepts.FermionAlgebra.CarJordanWigner

open Matrix
open scoped Matrix.Norms.L2Operator

/-- Finite indices with unequal natural-number values are unequal. -/
private theorem fin_ne_of_val_ne {n : ℕ} {a b : Fin n} (h : ¬(a : ℕ) = (b : ℕ)) : a ≠ b :=
  fun hab => h (congrArg Fin.val hab)

/-- Updating one register coordinate leaves every distinct coordinate unchanged. -/
private theorem upd_ne {n : ℕ} (x : Reg n) {i j : Fin n} (h : j ≠ i) (b : Bool) :
    Function.update x i b j = x j := by
  rw [Function.update_apply, if_neg h]

/-- Updates at two distinct register coordinates commute. -/
private theorem upd_upd_ne {n : ℕ} (x : Reg n) {i j : Fin n} (h : i ≠ j) (a b : Bool) :
    Function.update (Function.update x i a) j b = Function.update (Function.update x j b) i a :=
  Function.update_comm h a b x

/-- Registers agreeing at every position before mode `i` have equal Jordan–Wigner signs at `i`. -/
private theorem jwSign_congr {n : ℕ} {i : Fin n} {w v : Reg n}
    (h : ∀ k : Fin n, (k : ℕ) < (i : ℕ) → w k = v k) : jwSign i w = jwSign i v := by
  rw [jwSign_eq, jwSign_eq]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by
    by_cases hk : (k : ℕ) < (i : ℕ)
    · simp [h k hk]
    · simp [hk]

/-- Updating mode `i` leaves its own occupation-prefix sign unchanged. -/
private theorem jwSign_upd_self {n : ℕ} (i : Fin n) (x : Reg n) (b : Bool) :
    jwSign i (Function.update x i b) = jwSign i x := by
  refine jwSign_congr fun k hk => ?_
  have hki : (k : ℕ) ≠ (i : ℕ) := by omega
  rw [upd_ne x (fin_ne_of_val_ne hki) b]

/-- Changing a Boolean occupation strictly before mode `i` reverses the Jordan–Wigner sign at
`i`. -/
private theorem jwSign_upd_flip {n : ℕ} {i j : Fin n} (x : Reg n) (b : Bool)
    (hji : (j : ℕ) < (i : ℕ)) (hne : x j ≠ b) :
    jwSign i (Function.update x j b) = -(jwSign i x) := by
  have key : jwSign i (Function.update x j b) * jwSign i x = -1 := by
    rw [jwSign_eq, jwSign_eq i x, ← pow_add]
    have hf : ∀ k : Fin n, k ≠ j → (if (k : ℕ) < (i : ℕ) then (if Function.update x j b k then 1 else 0) else 0)
        = (if (k : ℕ) < (i : ℕ) then (if x k then 1 else 0) else 0) := by
      intro k hk
      by_cases hkl : (k : ℕ) < (i : ℕ)
      · rw [upd_ne x hk b]
      · simp [hkl]
    have _hocc : (if b then 1 else 0) + (if x j then 1 else 0) = 1 := by
      cases b <;> simp_all
    have hE1 : (∑ k : Fin n, if (k : ℕ) < (i : ℕ) then (if Function.update x j b k then 1 else 0) else 0)
        = (if b then 1 else 0) + ∑ k ∈ Finset.univ.erase j,
            (if (k : ℕ) < (i : ℕ) then (if x k then 1 else 0) else 0) := by
      have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin n))
        (fun k : Fin n => if (k : ℕ) < (i : ℕ) then (if Function.update x j b k then 1 else 0) else 0)
        (Finset.mem_univ j)
      rw [← hsplit]
      have hfj : (if (j : ℕ) < (i : ℕ) then (if Function.update x j b j then 1 else 0) else 0)
          = (if b then 1 else 0) := by
        rw [if_pos hji, upd_self]
      simp only [hfj]
      congr 1
      exact Finset.sum_congr rfl fun k hk => hf k (fun h => (Finset.mem_erase.mp hk).1 h)
    have hE0 : (∑ k : Fin n, if (k : ℕ) < (i : ℕ) then (if x k then 1 else 0) else 0)
        = (if x j then 1 else 0) + ∑ k ∈ Finset.univ.erase j,
            (if (k : ℕ) < (i : ℕ) then (if x k then 1 else 0) else 0) := by
      have h2 := Finset.add_sum_erase (Finset.univ : Finset (Fin n))
        (fun k : Fin n => if (k : ℕ) < (i : ℕ) then (if x k then 1 else 0) else 0)
        (Finset.mem_univ j)
      (try dsimp only at h2)
      rw [if_pos hji] at h2
      exact h2.symm
    rw [hE1, hE0]
    have hcomb : ((if b then 1 else 0)
          + ∑ k ∈ Finset.univ.erase j, (if (k : ℕ) < (i : ℕ) then (if x k then 1 else 0) else 0))
        + ((if x j then 1 else 0)
          + ∑ k ∈ Finset.univ.erase j, (if (k : ℕ) < (i : ℕ) then (if x k then 1 else 0) else 0))
        = 2 * (∑ k ∈ Finset.univ.erase j, (if (k : ℕ) < (i : ℕ) then (if x k then 1 else 0) else 0)) + 1 := by
      omega
    rw [hcomb, pow_add, pow_mul]
    norm_num
  calc jwSign i (Function.update x j b)
      = jwSign i (Function.update x j b) * 1 := (mul_one _).symm
    _ = jwSign i (Function.update x j b) * (jwSign i x * jwSign i x) := by rw [jwSign_sq]
    _ = jwSign i (Function.update x j b) * jwSign i x * jwSign i x := by rw [mul_assoc]
    _ = (-1) * jwSign i x := by rw [key]
    _ = -(jwSign i x) := neg_one_mul _

/-- The Jordan–Wigner sign equals the product of the occupation parity factors at modes
preceding `i`. -/
private theorem jwSign_prod {n : ℕ} (i : Fin n) (x : Reg n) :
    jwSign i x = ∏ k : Fin n, (if (k : ℕ) < (i : ℕ) then (if x k then -1 else 1 : ℂ) else 1) := by
  rw [jwSign_eq, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : (k : ℕ) < (i : ℕ)
  · rw [if_pos hk, if_pos hk]
    by_cases hxk : x k
    · rw [if_pos hxk, if_pos hxk, pow_one]
    · rw [if_neg hxk, if_neg hxk, pow_zero]
  · rw [if_neg hk, if_neg hk, pow_zero]

/-- The parity operator is diagonal, with entry minus one raised to the total occupation count. -/
private theorem par_apply {n : ℕ} (y x : Reg n) :
    parityOp (n := n) y x = if x = y then (-1 : ℂ) ^ (∑ k, if x k then 1 else 0) else 0 := rfl

/-- The Jordan–Wigner word has entries given by preceding parity factors, the local lowering
matrix, and following identity factors. -/
private theorem jw_apply {n : ℕ} (i : Fin n) (y x : Reg n) :
    jwPauliWord i y x = ∏ j : Fin n,
      (if j < i then (if y j = x j then (if x j then -1 else 1 : ℂ) else 0)
      else if i < j then (if y j = x j then 1 else 0)
      else sigmaMinus (boolEquivFin2 (y j)) (boolEquivFin2 (x j))) := rfl

/-- The Pauli lowering combination equals the matrix with its sole nonzero entry in the
upper-right position. -/
private theorem sigmaMinus_eq : sigmaMinus = !![0, 1; 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [sigmaMinus, pauliX, pauliY, Matrix.smul_apply, Matrix.add_apply,
      smul_eq_mul] <;>
    norm_num

/-- On Boolean basis indices, the lowering matrix has value one only from occupied input to
unoccupied output. -/
private theorem sigmaMinus_apply (a b : Bool) :
    sigmaMinus (boolEquivFin2 a) (boolEquivFin2 b) = if a then 0 else if b then 1 else 0 := by
  rw [sigmaMinus_eq]
  rcases a with _ | _ <;> rcases b with _ | _ <;>
    simp [boolEquivFin2]

/-- The anticommutator of annihilation at `i` and creation at `j` is the identity for equal
modes and zero otherwise. -/
private theorem car_delta {n : ℕ} (i j : Fin n) :
    annihilation i * creation j + creation j * annihilation i
      = (if i = j then (1 : Matrix (Reg n) (Reg n) ℂ) else 0) := by
  by_cases hij : i = j
  · subst hij
    ext y x
    by_cases hxi : x i = true
    · have h1 : (annihilation i * creation i) y x = 0 := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun z _ => ?_
        rw [cre_apply i z x, if_neg (fun h => absurd h.1 (by simp [hxi])), mul_zero]
      have h2 : (creation i * annihilation i) y x = (if y = x then (1 : ℂ) else 0) := by
        rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update x i false)]
        · rw [ann_apply i (Function.update x i false) x, if_pos ⟨hxi, rfl⟩, cre_apply i y _]
          have hzi : ¬ (Function.update x i false) i = true := by rw [upd_self]; simp
          by_cases hy : y = Function.update (Function.update x i false) i true
          · rw [if_pos ⟨hzi, hy⟩]
            have hyx : y = x := by rw [hy, upd_upd_self, upd_eq_self hxi]
            rw [if_pos hyx, hyx, jwSign_sq]
          · rw [if_neg (fun h => hy h.2), zero_mul, if_neg]
            intro h
            exact hy (by rw [h, upd_upd_self, upd_eq_self hxi])
        · intro z _ hz
          rw [ann_apply i z x, if_neg (fun h => hz h.2), mul_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
      rw [Matrix.add_apply, h1, h2, zero_add, if_pos (rfl : i = i), Matrix.one_apply]
    · have hxi' : x i = false := by simpa using! hxi
      have h1 : (annihilation i * creation i) y x = (if y = x then (1 : ℂ) else 0) := by
        rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update x i true)]
        · rw [cre_apply i (Function.update x i true) x, if_pos ⟨hxi, rfl⟩,
            ann_apply i y _]
          have hzi : (Function.update x i true) i = true := upd_self x i true
          by_cases hy : y = Function.update (Function.update x i true) i false
          · rw [if_pos ⟨hzi, hy⟩]
            have hyx : y = x := by rw [hy, upd_upd_self, upd_eq_self hxi']
            rw [if_pos hyx, jwSign_sq]
          · rw [if_neg (fun h => hy h.2), zero_mul, if_neg]
            intro h
            exact hy (by rw [h, upd_upd_self, upd_eq_self hxi'])
        · intro z _ hz
          rw [cre_apply i z x, if_neg (fun h => hz h.2), mul_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
      have h2 : (creation i * annihilation i) y x = 0 := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun z _ => ?_
        rw [ann_apply i z x, if_neg (fun h => absurd h.1 (by simp [hxi])), mul_zero]
      rw [Matrix.add_apply, h1, h2, add_zero, if_pos (rfl : i = i), Matrix.one_apply]
  · ext y x
    have hne : i ≠ j := hij
    by_cases hxi : x i = true
    · by_cases hxj : x j = true
      · have h1 : (annihilation i * creation j) y x = 0 := by
          rw [Matrix.mul_apply]
          refine Finset.sum_eq_zero fun z _ => ?_
          rw [cre_apply j z x, if_neg (fun h => absurd h.1 (by simp [hxj])), mul_zero]
        have h2 : (creation j * annihilation i) y x = 0 := by
          rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update x i false)]
          · rw [ann_apply i (Function.update x i false) x, if_pos ⟨hxi, rfl⟩,
              cre_apply j y _]
            have hzj : (Function.update x i false) j = true := by
              rw [upd_ne x (Ne.symm hne) false]
              exact hxj
            rw [if_neg (fun h => h.1 hzj), zero_mul]
          · intro z _ hz
            rw [ann_apply i z x, if_neg (fun h => hz h.2), mul_zero]
          · intro h
            exact absurd (Finset.mem_univ _) h
        rw [Matrix.add_apply, h1, h2, add_zero, if_neg hij, Matrix.zero_apply]
      · have h1 : (annihilation i * creation j) y x
            = (if y = Function.update (Function.update x j true) i false
               then jwSign i (Function.update x j true) * jwSign j (Function.update x j true)
               else 0) := by
          rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update x j true)]
          · rw [cre_apply j (Function.update x j true) x, if_pos ⟨by simp [hxj], rfl⟩,
              ann_apply i y _]
            have hzix : (Function.update x j true) i = x i := upd_ne x hne true
            by_cases hy : y = Function.update (Function.update x j true) i false
            · rw [if_pos ⟨by rw [hzix]; exact hxi, hy⟩, if_pos hy]
            · rw [if_neg (fun h => hy h.2), zero_mul, if_neg hy]
          · intro z _ hz
            rw [cre_apply j z x, if_neg (fun h => hz h.2), mul_zero]
          · intro h
            exact absurd (Finset.mem_univ _) h
        have h2 : (creation j * annihilation i) y x
            = (if y = Function.update (Function.update x i false) j true
               then jwSign j (Function.update (Function.update x i false) j true) * jwSign i x
               else 0) := by
          rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update x i false)]
          · rw [ann_apply i (Function.update x i false) x, if_pos ⟨hxi, rfl⟩,
              cre_apply j y _]
            have hzj : ¬ (Function.update x i false) j = true := by
              rw [upd_ne x (Ne.symm hne) false]
              simp [hxj]
            by_cases hy : y = Function.update (Function.update x i false) j true
            · rw [if_pos ⟨hzj, hy⟩, if_pos hy, hy]
            · rw [if_neg (fun h => hy h.2), zero_mul, if_neg hy]
          · intro z _ hz
            rw [ann_apply i z x, if_neg (fun h => hz h.2), mul_zero]
          · intro h
            exact absurd (Finset.mem_univ _) h
        have hrow : Function.update (Function.update x j true) i false
            = Function.update (Function.update x i false) j true :=
          upd_upd_ne x (Ne.symm hne) true false
        rw [Matrix.add_apply, h1, h2, hrow, if_neg hij, Matrix.zero_apply]
        by_cases hy : y = Function.update (Function.update x i false) j true
        · rw [if_pos hy, if_pos hy]
          rcases Nat.lt_trichotomy (i : ℕ) (j : ℕ) with hlt | heq | hgt
          · have s1 : jwSign i (Function.update x j true) = jwSign i x := by
              refine jwSign_congr fun k hk => ?_
              have hkj : (k : ℕ) ≠ (j : ℕ) := by omega
              rw [upd_ne x (fin_ne_of_val_ne hkj) true]
            have s2 : jwSign j (Function.update (Function.update x i false) j true)
                = -(jwSign j x) := by
              rw [jwSign_upd_self j (Function.update x i false) true,
                jwSign_upd_flip x false hlt (by simp [hxi])]
            rw [s1, s2, jwSign_upd_self j x true]
            ring
          · exact absurd (Fin.ext heq) hij
          · have s1 : jwSign i (Function.update x j true) = -(jwSign i x) :=
              jwSign_upd_flip x true hgt (by simp [hxj])
            have s2 : jwSign j (Function.update (Function.update x i false) j true)
                = jwSign j x := by
              rw [jwSign_upd_self j (Function.update x i false) true]
              refine jwSign_congr fun k hk => ?_
              have hki : (k : ℕ) ≠ (i : ℕ) := by omega
              rw [upd_ne x (fin_ne_of_val_ne hki) false]
            rw [s1, s2, jwSign_upd_self j x true]
            ring
        · rw [if_neg hy, if_neg hy, add_zero]
    · by_cases hxj : x j = true
      · have h1 : (annihilation i * creation j) y x = 0 := by
          rw [Matrix.mul_apply]
          refine Finset.sum_eq_zero fun z _ => ?_
          rw [cre_apply j z x, if_neg (fun h => absurd h.1 (by simp [hxj])), mul_zero]
        have h2 : (creation j * annihilation i) y x = 0 := by
          rw [Matrix.mul_apply]
          refine Finset.sum_eq_zero fun z _ => ?_
          rw [ann_apply i z x, if_neg (fun h => absurd h.1 (by simp [hxi])), mul_zero]
        rw [Matrix.add_apply, h1, h2, add_zero, if_neg hij, Matrix.zero_apply]
      · have h1 : (annihilation i * creation j) y x = 0 := by
          rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update x j true)]
          · rw [cre_apply j (Function.update x j true) x, if_pos ⟨by simp [hxj], rfl⟩,
              ann_apply i y _]
            have hzix : ¬ (Function.update x j true) i = true := by
              rw [upd_ne x hne true]
              simp [hxi]
            rw [if_neg (fun h => hzix h.1), zero_mul]
          · intro z _ hz
            rw [cre_apply j z x, if_neg (fun h => hz h.2), mul_zero]
          · intro h
            exact absurd (Finset.mem_univ _) h
        have h2 : (creation j * annihilation i) y x = 0 := by
          rw [Matrix.mul_apply]
          refine Finset.sum_eq_zero fun z _ => ?_
          rw [ann_apply i z x, if_neg (fun h => absurd h.1 (by simp [hxi])), mul_zero]
        rw [Matrix.add_apply, h1, h2, add_zero, if_neg hij, Matrix.zero_apply]

/-- Any two annihilation operators have zero anticommutator. -/
private theorem ann_anticommute {n : ℕ} (i j : Fin n) :
    annihilation i * annihilation j + annihilation j * annihilation i = 0 := by
  by_cases hij : i = j
  · subst hij
    ext y x
    have hz : (annihilation i * annihilation i) y x = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [ann_apply i y z, ann_apply i z x]
      by_cases h1 : z i ∧ y = Function.update z i false
      · rw [if_pos h1, if_neg (fun h2 => by
          obtain ⟨_, hz2⟩ := h2
          rw [hz2, upd_self] at h1
          exact absurd h1.1 (by simp)), mul_zero]
      · rw [if_neg h1, zero_mul]
    rw [Matrix.add_apply, hz, add_zero, Matrix.zero_apply]
  · ext y x
    have hne : i ≠ j := hij
    by_cases hxi : x i = true
    · by_cases hxj : x j = true
      · have h1 : (annihilation i * annihilation j) y x
            = (if y = Function.update (Function.update x j false) i false
               then jwSign i (Function.update x j false) * jwSign j x else 0) := by
          rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update x j false)]
          · rw [ann_apply j (Function.update x j false) x, if_pos ⟨hxj, rfl⟩,
              ann_apply i y _]
            by_cases hy : y = Function.update (Function.update x j false) i false
            · rw [if_pos ⟨by rw [upd_ne x hne false]; exact hxi, hy⟩, if_pos hy]
            · rw [if_neg (fun h => hy h.2), zero_mul, if_neg hy]
          · intro z _ hz
            rw [ann_apply j z x, if_neg (fun h => hz h.2), mul_zero]
          · intro h
            exact absurd (Finset.mem_univ _) h
        have h2 : (annihilation j * annihilation i) y x
            = (if y = Function.update (Function.update x i false) j false
               then jwSign j (Function.update x i false) * jwSign i x else 0) := by
          rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update x i false)]
          · rw [ann_apply i (Function.update x i false) x, if_pos ⟨hxi, rfl⟩,
              ann_apply j y _]
            by_cases hy : y = Function.update (Function.update x i false) j false
            · rw [if_pos ⟨by rw [upd_ne x (Ne.symm hne) false]; exact hxj, hy⟩, if_pos hy]
            · rw [if_neg (fun h => hy h.2), zero_mul, if_neg hy]
          · intro z _ hz
            rw [ann_apply i z x, if_neg (fun h => hz h.2), mul_zero]
          · intro h
            exact absurd (Finset.mem_univ _) h
        have hrow : Function.update (Function.update x j false) i false
            = Function.update (Function.update x i false) j false :=
          upd_upd_ne x (Ne.symm hne) false false
        rw [Matrix.add_apply, h1, h2, hrow, Matrix.zero_apply]
        by_cases hy : y = Function.update (Function.update x i false) j false
        · rw [if_pos hy, if_pos hy]
          rcases Nat.lt_trichotomy (i : ℕ) (j : ℕ) with hlt | heq | hgt
          · have s1 : jwSign i (Function.update x j false) = jwSign i x := by
              refine jwSign_congr fun k hk => ?_
              have hkj : (k : ℕ) ≠ (j : ℕ) := by omega
              rw [upd_ne x (fin_ne_of_val_ne hkj) false]
            have s2 : jwSign j (Function.update x i false) = -(jwSign j x) :=
              jwSign_upd_flip x false hlt (by simp [hxi])
            rw [s1, s2]
            ring
          · exact absurd (Fin.ext heq) hij
          · have s1 : jwSign i (Function.update x j false) = -(jwSign i x) :=
              jwSign_upd_flip x false hgt (by simp [hxj])
            have s2 : jwSign j (Function.update x i false) = jwSign j x := by
              refine jwSign_congr fun k hk => ?_
              have hki : (k : ℕ) ≠ (i : ℕ) := by omega
              rw [upd_ne x (fin_ne_of_val_ne hki) false]
            rw [s1, s2]
            ring
        · rw [if_neg hy, if_neg hy, add_zero]
      · have h1 : (annihilation i * annihilation j) y x = 0 := by
          rw [Matrix.mul_apply]
          refine Finset.sum_eq_zero fun z _ => ?_
          rw [ann_apply j z x, if_neg (fun h => absurd h.1 (by simp [hxj])), mul_zero]
        have h2 : (annihilation j * annihilation i) y x = 0 := by
          rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update x i false)]
          · rw [ann_apply i (Function.update x i false) x, if_pos ⟨hxi, rfl⟩,
              ann_apply j y _]
            have hzj : ¬ (Function.update x i false) j = true := by
              rw [upd_ne x (Ne.symm hne) false]
              simp [hxj]
            rw [if_neg (fun h => hzj h.1), zero_mul]
          · intro z _ hz
            rw [ann_apply i z x, if_neg (fun h => hz h.2), mul_zero]
          · intro h
            exact absurd (Finset.mem_univ _) h
        rw [Matrix.add_apply, h1, h2, add_zero, Matrix.zero_apply]
    · by_cases hxj : x j = true
      · have h1 : (annihilation i * annihilation j) y x = 0 := by
          rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update x j false)]
          · rw [ann_apply j (Function.update x j false) x, if_pos ⟨hxj, rfl⟩,
              ann_apply i y _]
            have hzix : ¬ (Function.update x j false) i = true := by
              rw [upd_ne x hne false]
              simp [hxi]
            rw [if_neg (fun h => hzix h.1), zero_mul]
          · intro z _ hz
            rw [ann_apply j z x, if_neg (fun h => hz h.2), mul_zero]
          · intro h
            exact absurd (Finset.mem_univ _) h
        have h2 : (annihilation j * annihilation i) y x = 0 := by
          rw [Matrix.mul_apply]
          refine Finset.sum_eq_zero fun z _ => ?_
          rw [ann_apply i z x, if_neg (fun h => absurd h.1 (by simp [hxi])), mul_zero]
        rw [Matrix.add_apply, h1, h2, add_zero, Matrix.zero_apply]
      · have h1 : (annihilation i * annihilation j) y x = 0 := by
          rw [Matrix.mul_apply]
          refine Finset.sum_eq_zero fun z _ => ?_
          rw [ann_apply j z x, if_neg (fun h => absurd h.1 (by simp [hxj])), mul_zero]
        have h2 : (annihilation j * annihilation i) y x = 0 := by
          rw [Matrix.mul_apply]
          refine Finset.sum_eq_zero fun z _ => ?_
          rw [ann_apply i z x, if_neg (fun h => absurd h.1 (by simp [hxi])), mul_zero]
        rw [Matrix.add_apply, h1, h2, add_zero, Matrix.zero_apply]

/-- Any two creation operators have zero anticommutator. -/
private theorem cre_anticommute {n : ℕ} (i j : Fin n) :
    creation i * creation j + creation j * creation i = 0 := by
  calc creation i * creation j + creation j * creation i
      = (annihilation i)ᴴ * (annihilation j)ᴴ
          + (annihilation j)ᴴ * (annihilation i)ᴴ := by
        rw [creation_eq_conjTranspose i, creation_eq_conjTranspose j]
    _ = (annihilation j * annihilation i + annihilation i * annihilation j)ᴴ := by
        rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    _ = (0 : Matrix (Reg n) (Reg n) ℂ)ᴴ := by rw [ann_anticommute j i]
    _ = 0 := Matrix.conjTranspose_zero

/-- A basis ket is an eigenvector of `numberOp i` with eigenvalue its Boolean occupation at mode
`i`. -/
private theorem numberOp_mulVec {n : ℕ} (i : Fin n) (x : Reg n) :
    numberOp i *ᵥ Ket x = (if x i then (1 : ℂ) else 0) • Ket x := by
  funext y
  have hsum : ∑ z : Reg n, numberOp i y z * Ket x z
      = numberOp i y x * Ket x x :=
    Finset.sum_eq_single x
      (fun b _ hb => by rw [ket_ne hb, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h)
  simp only [Matrix.mulVec, dotProduct]
  rw [hsum, ket_self, mul_one]
  simp only [num_apply, Pi.smul_apply, smul_eq_mul, ket_apply]
  by_cases hxi : x i = true
  · by_cases hxy : y = x
    · subst hxy
      simp
    · rw [if_neg hxy, mul_zero, if_neg (fun h => hxy h.1.symm)]
  · by_cases hxy : y = x
    · subst hxy
      simp [hxi]
    · rw [if_neg hxy, mul_zero, if_neg (fun h => hxy h.1.symm)]

/-- The square of the total parity operator is the identity. -/
private theorem parity_sq {n : ℕ} :
    parityOp (n := n) * parityOp (n := n) = 1 := by
  ext y x
  rw [Matrix.mul_apply, Finset.sum_eq_single x]
  · rw [par_apply y x, par_apply x x, Matrix.one_apply]
    by_cases hxy : x = y
    · rw [if_pos hxy, if_pos rfl, neg_one_pow_mul_self, if_pos hxy.symm]
    · rw [if_neg hxy, zero_mul, if_neg (fun h => hxy h.symm)]
  · intro z _ hz
    rw [par_apply z x, if_neg (fun h => hz h.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Replacing one Boolean coordinate changes the total occupation count by the difference
between its new and old occupations. -/
private theorem par_count_add {n : ℕ} (x : Reg n) (i : Fin n) (b : Bool) :
    (∑ k : Fin n, if Function.update x i b k then 1 else 0) + (if x i then 1 else 0)
      = (∑ k : Fin n, if x k then 1 else 0) + (if b then 1 else 0) := by
  have hE1 : (∑ k : Fin n, if Function.update x i b k then 1 else 0)
      = (if b then 1 else 0)
        + ∑ k ∈ Finset.univ.erase i, (if x k then 1 else 0) := by
    have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin n))
      (fun k : Fin n => if Function.update x i b k then 1 else 0) (Finset.mem_univ i)
    rw [← hsplit]
    have hfj : (if Function.update x i b i then 1 else 0) = (if b then 1 else 0) := by
      rw [upd_self]
    simp only [hfj]
    congr 1
    exact Finset.sum_congr rfl fun k hk => by
      rw [upd_ne x (fun h => (Finset.mem_erase.mp hk).1 h) b]
  have hE0 := Finset.add_sum_erase (Finset.univ : Finset (Fin n))
    (fun k : Fin n => if x k then 1 else 0) (Finset.mem_univ i)
  (try dsimp only at hE0)
  simp only [hE1, ← hE0]
  ring

/-- The total parity operator anticommutes with every annihilation operator. -/
private theorem parity_ann {n : ℕ} (i : Fin n) :
    parityOp (n := n) * annihilation i = -(annihilation i * parityOp (n := n)) := by
  ext y x
  rw [Matrix.mul_apply, Finset.sum_eq_single y, Matrix.neg_apply, Matrix.mul_apply,
    Finset.sum_eq_single x]
  · rw [par_apply y y, if_pos rfl, par_apply x x, if_pos rfl]
    by_cases hxi : x i = true
    · by_cases hy : y = Function.update x i false
      · rw [ann_apply i y x, if_pos ⟨hxi, hy⟩]
        have e : (-1 : ℂ) ^ (∑ k : Fin n, if y k then 1 else 0)
            = -(-1 : ℂ) ^ (∑ k : Fin n, if x k then 1 else 0) := by
          rw [hy]
          have h2 : (∑ k : Fin n, if Function.update x i false k then 1 else 0) + 1
              = ∑ k : Fin n, if x k then 1 else 0 := by
            have h := par_count_add x i false
            rw [if_pos hxi, if_neg (by decide)] at h
            omega
          rw [← h2, pow_succ]
          ring
        rw [e]
        ring
      · rw [ann_apply i y x, if_neg (fun h => hy h.2), mul_zero, zero_mul, neg_zero]
    · rw [ann_apply i y x, if_neg (fun h => absurd h.1 (by simp [hxi])), mul_zero,
        zero_mul, neg_zero]
  · intro z _ hz
    rw [par_apply z x, if_neg (fun h => hz h.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro z _ hz
    rw [par_apply y z, if_neg hz, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The total parity operator anticommutes with every creation operator. -/
private theorem parity_cre {n : ℕ} (i : Fin n) :
    parityOp (n := n) * creation i = -(creation i * parityOp (n := n)) := by
  ext y x
  rw [Matrix.mul_apply, Finset.sum_eq_single y, Matrix.neg_apply, Matrix.mul_apply,
    Finset.sum_eq_single x]
  · rw [par_apply y y, if_pos rfl, par_apply x x, if_pos rfl]
    by_cases hxi : x i = true
    · rw [cre_apply i y x, if_neg (fun h => absurd h.1 (by simp [hxi])), mul_zero,
        zero_mul, neg_zero]
    · by_cases hy : y = Function.update x i true
      · rw [cre_apply i y x, if_pos ⟨hxi, hy⟩]
        have e : (-1 : ℂ) ^ (∑ k : Fin n, if y k then 1 else 0)
            = -(-1 : ℂ) ^ (∑ k : Fin n, if x k then 1 else 0) := by
          rw [hy]
          have h2 : (∑ k : Fin n, if Function.update x i true k then 1 else 0)
              = (∑ k : Fin n, if x k then 1 else 0) + 1 := by
            have h := par_count_add x i true
            rw [if_neg hxi, if_pos (rfl : true = true)] at h
            omega
          rw [h2, pow_succ]
          ring
        rw [e]
        ring
      · rw [cre_apply i y x, if_neg (fun h => hy h.2), mul_zero, zero_mul, neg_zero]
  · intro z _ hz
    rw [par_apply z x, if_neg (fun h => hz h.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro z _ hz
    rw [par_apply y z, if_neg hz, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Each annihilation operator equals its Jordan–Wigner Pauli word. -/
private theorem jw_eq_ann {n : ℕ} (i : Fin n) : annihilation i = jwPauliWord i := by
  ext y x
  rw [ann_apply i y x, jw_apply i y x]
  by_cases hxi : x i = true
  · by_cases hy : y = Function.update x i false
    · rw [if_pos ⟨hxi, hy⟩, jwSign_prod i x]
      have hyk : ∀ k : Fin n, (k : ℕ) ≠ (i : ℕ) → y k = x k := by
        intro k hk
        rw [hy, upd_ne x (fin_ne_of_val_ne hk) false]
      refine Finset.prod_congr rfl fun k _ => ?_
      rcases Nat.lt_trichotomy (k : ℕ) (i : ℕ) with hlt | heq | hgt
      · have hflt : k < i := hlt
        rw [if_pos hlt, if_pos (hyk k (by omega)), if_pos hflt]
      · have hki : k = i := Fin.ext heq
        subst hki
        rw [if_neg (Nat.lt_irrefl _), if_neg (lt_irrefl _), if_neg (lt_irrefl _), hy,
          upd_self, hxi, sigmaMinus_apply]
        simp
      · have hnk : ¬ (k : ℕ) < (i : ℕ) := by omega
        have hfnk : ¬ (k < i) := fun h => hnk h
        have hfgt : i < k := hgt
        rw [if_neg hnk, if_neg hfnk, if_pos hfgt, if_pos (hyk k (by omega))]
    · rw [if_neg (fun h => hy h.2)]
      rw [funext_iff, not_forall] at hy
      obtain ⟨k, hk⟩ := hy
      refine (Finset.prod_eq_zero (Finset.mem_univ k) ?_).symm
      rcases Nat.lt_trichotomy (k : ℕ) (i : ℕ) with hlt | heq | hgt
      · have hflt : k < i := hlt
        rw [if_pos hflt]
        refine if_neg ?_
        intro h
        apply hk
        rw [h, upd_ne x (fin_ne_of_val_ne (by omega)) false]
      · have hki : k = i := Fin.ext heq
        subst hki
        rw [upd_self] at hk
        have hyk2 : y k = true := by
          rcases hyv : y k with _ | _
          · exact absurd hyv hk
          · rfl
        rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _), hyk2, hxi, sigmaMinus_apply]
        simp
      · have hnk : ¬ (k : ℕ) < (i : ℕ) := by omega
        have hfnk : ¬ (k < i) := fun h => hnk h
        have hfgt : i < k := hgt
        rw [if_neg hfnk, if_pos hfgt]
        refine if_neg ?_
        intro h
        apply hk
        rw [h, upd_ne x (fin_ne_of_val_ne (by omega)) false]
  · rw [if_neg (fun h => absurd h.1 (by simp [hxi]))]
    have hxi' : x i = false := by simpa using! hxi
    refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
    rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _), hxi', sigmaMinus_apply]
    simp

/-- Each creation operator equals the adjoint of its Jordan–Wigner Pauli word. -/
private theorem jw_eq_cre {n : ℕ} (i : Fin n) : creation i = (jwPauliWord i)ᴴ := by
  rw [creation_eq_conjTranspose i, jw_eq_ann i]

/-- Every annihilation operator sends the all-zero occupation ket to zero. -/
private theorem vacuum {n : ℕ} (i : Fin n) :
    annihilation i *ᵥ Ket (ZeroStr n) = 0 := by
  funext y
  have hsum : ∑ z : Reg n, annihilation i y z * Ket (ZeroStr n) z
      = annihilation i y (ZeroStr n) * Ket (ZeroStr n) (ZeroStr n) :=
    Finset.sum_eq_single (ZeroStr n)
      (fun b _ hb => by rw [ket_ne hb, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h)
  rw [show (annihilation i *ᵥ Ket (ZeroStr n)) y
      = ∑ z : Reg n, annihilation i y z * Ket (ZeroStr n) z from rfl, hsum, ket_self,
    mul_one, ann_apply, if_neg (by simp [ZeroStr]), Pi.zero_apply]

/-- The finite-mode operators satisfy the canonical anticommutation relations of [Bravyi and
Kitaev, Eq. (2)][BravyiKitaev2002]. They also satisfy the adjoint, number-operator, parity,
Jordan–Wigner, and vacuum identities stated here. -/
theorem g1 : ∀ (n : ℕ),

  (∀ i j : Fin n,
    annihilation i * creation j + creation j * annihilation i
      = (if i = j then (1 : Matrix (Reg n) (Reg n) ℂ) else 0)
      ∧ annihilation i * annihilation j + annihilation j * annihilation i = 0
      ∧ creation i * creation j + creation j * creation i = 0) ∧

  (∀ i : Fin n, creation i = (annihilation i)ᴴ) ∧

  (∀ i : Fin n,
    numberOp i = creation i * annihilation i
      ∧ ∀ x : Reg n, numberOp i *ᵥ Ket x = (if x i then (1 : ℂ) else 0) • Ket x
      ∧ numberOp i * numberOp i = numberOp i) ∧

  (parityOp (n := n) * parityOp (n := n) = 1
    ∧ ∀ i : Fin n, parityOp (n := n) * annihilation i = -(annihilation i * parityOp (n := n))
    ∧ ∀ i : Fin n, parityOp (n := n) * creation i = -(creation i * parityOp (n := n))) ∧

  (∀ i : Fin n, annihilation i = jwPauliWord i ∧ creation i = (jwPauliWord i)ᴴ) ∧

  (∀ i : Fin n, annihilation i *ᵥ Ket (ZeroStr n) = 0) := by
  intro n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i j => ⟨car_delta i j, ann_anticommute i j, cre_anticommute i j⟩
  · exact fun i => creation_eq_conjTranspose i
  · exact fun i => ⟨numberOp_eq i, fun x => ⟨numberOp_mulVec i x, numberOp_idem i⟩⟩
  · exact And.intro parity_sq
      (fun i => And.intro (parity_ann i) (fun i' => parity_cre i'))
  · exact fun i => ⟨jw_eq_ann i, jw_eq_cre i⟩
  · exact fun i => vacuum i

end Qatlib.Concepts.FermionAlgebra.CarJordanWigner
