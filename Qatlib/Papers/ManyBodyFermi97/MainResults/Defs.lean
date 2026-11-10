/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorRegistersDefs
import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorRegisters
import Qatlib.Foundations.CircuitReversal.ReversalAlgebra.CircuitReversalAlgebra
import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.FermionDefs
import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.FermionHubbard
import Qatlib.Concepts.TrotterFormula.GeneralOrder.GeneralTrotterOrder
import Mathlib.Data.Nat.Log
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open scoped Matrix.Norms.L2Operator
open Matrix

namespace Qatlib.Papers.ManyBodyFermi97.MainResults

open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath

def quWordBits (m : ℕ) : ℕ := Nat.clog 2 m

def firstQuantizedBits (n m : ℕ) : ℕ := n * quWordBits m

def secondQuantizedBits (m : ℕ) : ℕ := m

theorem le_two_pow_quWordBits (m : ℕ) : m ≤ 2 ^ quWordBits m :=
  Nat.le_pow_clog (by norm_num) m

theorem le_two_pow : ∀ n : ℕ, n ≤ 2 ^ n
  | 0 => by simp
  | n + 1 => by
    have ih : n ≤ 2 ^ n := le_two_pow n
    have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
    calc n + 1 ≤ 2 ^ n + 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by ring

theorem quWordBits_le (m : ℕ) : quWordBits m ≤ m := by
  rw [quWordBits, Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
  exact le_two_pow m

theorem secondQuantized_card (m : ℕ) : Fintype.card (Reg m) = 2 ^ m :=
  card_reg m

theorem firstQuantized_bits_suffice (n m : ℕ) :
    m ^ n ≤ 2 ^ firstQuantizedBits n m := by
  rw [firstQuantizedBits, pow_mul']
  exact Nat.pow_le_pow_left (le_two_pow_quWordBits m) n

theorem firstQuantized_injective (n m : ℕ) :
    Function.Injective
      (toReg (fun _ : Fin n => m) (firstQuantizedBits n m) (by
        rw [Finset.prod_const]
        simpa [Fintype.card_fin] using! firstQuantized_bits_suffice n m)) := by
  apply toReg_injective

def secondQuantPotentialCost (m : ℕ) : ℕ := m

def secondQuantPairCost (m : ℕ) : ℕ := m + 8

def secondQuantHubbardCost (m : ℕ) (pairs : Finset (Fin m × Fin m)) : ℕ :=
  secondQuantPotentialCost m + pairs.sum (fun _ => secondQuantPairCost m)

theorem sq_ge_self {m : ℕ} (hm : 1 ≤ m) : m ≤ m ^ 2 := by
  have h : m * 1 ≤ m * m := Nat.mul_le_mul_left m hm
  simpa [pow_two] using! h

theorem sum_le_card_mul {ι : Type*} (s : Finset ι) (f : ι → ℕ) (C : ℕ)
    (hf : ∀ x ∈ s, f x ≤ C) : s.sum f ≤ s.card * C := by
  calc s.sum f ≤ s.sum (fun _ => C) := Finset.sum_le_sum hf
    _ = s.card * C := by simp [Finset.sum_const]

theorem secondQuantHubbardCost_bound {m c : ℕ} (hm : 1 ≤ m)
    (pairs : Finset (Fin m × Fin m)) (hcard : pairs.card ≤ c * m) :
    secondQuantHubbardCost m pairs ≤ (1 + 9 * c) * m ^ 2 := by
  unfold secondQuantHubbardCost secondQuantPotentialCost secondQuantPairCost
  have hsum : pairs.sum (fun _ => m + 8) ≤ pairs.card * (m + 8) :=
    sum_le_card_mul pairs (fun _ => m + 8) (m + 8) (fun _ _ => le_rfl)
  have h1 : pairs.sum (fun _ => m + 8) ≤ (c * m) * (m + 8) :=
    hsum.trans (Nat.mul_le_mul_right _ hcard)
  have hm2 : m ≤ m ^ 2 := sq_ge_self hm
  have hmul8 : m * 8 ≤ m ^ 2 * 8 := Nat.mul_le_mul_right 8 hm2
  have hinner : m * (m + 8) ≤ 9 * m ^ 2 := by
    calc m * (m + 8) = m * m + m * 8 := by ring
      _ ≤ m ^ 2 + m ^ 2 * 8 := by
          rw [show m * m = m ^ 2 by ring]
          exact Nat.add_le_add_left hmul8 _
      _ = 9 * m ^ 2 := by ring
  have hmid : (c * m) * (m + 8) ≤ c * (9 * m ^ 2) := by
    calc (c * m) * (m + 8) = c * (m * (m + 8)) := by ring
      _ ≤ c * (9 * m ^ 2) := Nat.mul_le_mul_left c hinner
  calc m + pairs.sum (fun _ => m + 8)
      ≤ m + c * (9 * m ^ 2) := Nat.add_le_add_left (h1.trans hmid) m
    _ ≤ m ^ 2 + c * (9 * m ^ 2) := Nat.add_le_add_right hm2 _
    _ = (1 + 9 * c) * m ^ 2 := by ring

def chainPairs (m : ℕ) : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun p : Fin m × Fin m => p.1.val + 1 = p.2.val)

theorem chainPairs_card (m : ℕ) : (chainPairs m).card ≤ m := by
  have hmaps : Set.MapsTo (fun p : Fin m × Fin m => p.1)
      ↑(chainPairs m) ↑(Finset.univ : Finset (Fin m)) := by
    intro p _; simp
  have hinj : (↑(chainPairs m) : Set (Fin m × Fin m)).InjOn (fun p => p.1) := by
    intro p hp q hq hpq
    simp only [chainPairs, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp hq
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    simp only at hpq hp hq
    subst hpq
    have h2 : q2 = p2 := by
      apply Fin.ext
      omega
    subst h2
    rfl
  have := Finset.card_le_card_of_injOn (fun p : Fin m × Fin m => p.1) hmaps hinj
  simpa [Fintype.card_fin] using! this

theorem chain_hubbard_cost_bound (m : ℕ) (hm : 1 ≤ m) :
    secondQuantHubbardCost m (chainPairs m) ≤ 10 * m ^ 2 := by
  have h := secondQuantHubbardCost_bound (c := 1) hm (chainPairs m)
    (by simpa using! chainPairs_card m)
  simpa using! h

def antisymStepTwoCost (n q : ℕ) : ℕ := n * q ^ 2

def antisymStepThreeCost (n q : ℕ) : ℕ := n ^ 2 * q

def antisymStepFourCost (n : ℕ) : ℕ := 2 * n * Nat.clog 2 n

def antisymTotalCost (n q : ℕ) : ℕ :=
  antisymStepTwoCost n q + antisymStepThreeCost n q + antisymStepFourCost n

theorem antisymTotalCost_bound {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) :
    antisymTotalCost n q ≤ 4 * n ^ 2 * q ^ 2 := by
  unfold antisymTotalCost antisymStepTwoCost antisymStepThreeCost antisymStepFourCost
  have hn2 : n ≤ n ^ 2 := sq_ge_self hn
  have hq2 : q ≤ q ^ 2 := sq_ge_self hq
  have hq2pos : 1 ≤ q ^ 2 := by
    calc 1 = 1 * 1 := by ring
      _ ≤ q * q := Nat.mul_le_mul hq hq
      _ = q ^ 2 := by ring
  have hclog : Nat.clog 2 n ≤ n := quWordBits_le n
  have h1 : n * q ^ 2 ≤ n ^ 2 * q ^ 2 := Nat.mul_le_mul_right _ hn2
  have h2 : n ^ 2 * q ≤ n ^ 2 * q ^ 2 := Nat.mul_le_mul_left _ hq2
  have h3 : 2 * n * Nat.clog 2 n ≤ 2 * n ^ 2 * q ^ 2 := by
    have ha : n * Nat.clog 2 n ≤ n * n := Nat.mul_le_mul_left n hclog
    calc 2 * n * Nat.clog 2 n = 2 * (n * Nat.clog 2 n) := by ring
      _ ≤ 2 * (n * n) := Nat.mul_le_mul_left 2 ha
      _ = 2 * n ^ 2 := by ring
      _ ≤ 2 * n ^ 2 * q ^ 2 := by
          calc 2 * n ^ 2 = 2 * n ^ 2 * 1 := by ring
            _ ≤ 2 * n ^ 2 * q ^ 2 := Nat.mul_le_mul_left _ hq2pos
  calc n * q ^ 2 + n ^ 2 * q + 2 * n * Nat.clog 2 n
      ≤ n ^ 2 * q ^ 2 + n ^ 2 * q ^ 2 + 2 * n ^ 2 * q ^ 2 :=
        Nat.add_le_add (Nat.add_le_add h1 h2) h3
    _ = 4 * n ^ 2 * q ^ 2 := by ring

def oneParticleStepCost (m : ℕ) : ℕ := m ^ 2

def twoParticleStepCost (m : ℕ) : ℕ := m ^ 4

theorem oneParticleStepCost_le {m : ℕ} (hm : 1 ≤ m) :
    oneParticleStepCost m ≤ m ^ 4 := by
  unfold oneParticleStepCost
  exact Nat.pow_le_pow_right hm (by norm_num)

theorem firstQuantized_simulation_bound {m : ℕ} (hm : 1 ≤ m) :
    oneParticleStepCost m + twoParticleStepCost m ≤ 2 * m ^ 4 := by
  unfold twoParticleStepCost
  calc oneParticleStepCost m + m ^ 4
      ≤ m ^ 4 + m ^ 4 := Nat.add_le_add_right (oneParticleStepCost_le hm) _
    _ = 2 * m ^ 4 := by ring

def firstQuantHubbardStepCost (q : ℕ) : ℕ := 2 * (q ^ 2 + 2 * q + 4)

theorem firstQuantHubbardStepCost_bound {q : ℕ} (hq : 1 ≤ q) :
    firstQuantHubbardStepCost q ≤ 14 * q ^ 2 := by
  unfold firstQuantHubbardStepCost
  have h1 : q ≤ q ^ 2 := sq_ge_self hq
  have hq2pos : 1 ≤ q ^ 2 := by
    calc 1 = 1 * 1 := by ring
      _ ≤ q * q := Nat.mul_le_mul hq hq
      _ = q ^ 2 := by ring
  have h4 : 4 ≤ 4 * q ^ 2 := by
    calc 4 = 4 * 1 := by ring
      _ ≤ 4 * q ^ 2 := Nat.mul_le_mul_left 4 hq2pos
  have h2 : q ^ 2 + 2 * q + 4 ≤ q ^ 2 + 2 * q ^ 2 + 4 * q ^ 2 := by
    apply Nat.add_le_add
    · exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 h1) _
    · exact h4
  calc 2 * (q ^ 2 + 2 * q + 4) ≤ 2 * (q ^ 2 + 2 * q ^ 2 + 4 * q ^ 2) :=
        Nat.mul_le_mul_left 2 h2
    _ = 14 * q ^ 2 := by ring

noncomputable def chainHopping (m : ℕ) (t : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => if (i.val : ℤ) + 1 = j.val ∨ (j.val : ℤ) + 1 = i.val then t else 0

noncomputable def evenBlocks (m : ℕ) (t : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => if i.val / 2 = j.val / 2 then chainHopping m t i j else 0

noncomputable def oddBlocks (m : ℕ) (t : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => if i.val / 2 ≠ j.val / 2 then chainHopping m t i j else 0

theorem chainHopping_eq_blocks (m : ℕ) (t : ℂ) :
    chainHopping m t = evenBlocks m t + oddBlocks m t := by
  ext i j
  simp only [evenBlocks, oddBlocks, Matrix.add_apply]
  by_cases h : i.val / 2 = j.val / 2
  · simp [h]
  · simp [h]

theorem evenBlocks_block_diagonal (m : ℕ) (t : ℂ) (i j : Fin m)
    (h : evenBlocks m t i j ≠ 0) : i.val / 2 = j.val / 2 := by
  by_contra hne
  apply h
  simp [evenBlocks, hne]

theorem evenBlocks_two_by_two (m : ℕ) (t : ℂ) {i j : Fin m}
    (hblk : i.val / 2 = j.val / 2)
    (hadj : (i.val : ℤ) + 1 = j.val ∨ (j.val : ℤ) + 1 = i.val) :
    evenBlocks m t i j = t := by
  simp [evenBlocks, chainHopping, hblk, hadj]

theorem evenBlocks_diagonal_zero (m : ℕ) (t : ℂ) (i : Fin m) :
    evenBlocks m t i i = 0 := by
  simp [evenBlocks, chainHopping]

theorem local_evolution_jets {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => NormedSpace.exp (t • H)) 0 = H ^ k :=
  Qatlib.Concepts.TrotterFormula.GeneralOrder.trotter_exp_jets H k

end Qatlib.Papers.ManyBodyFermi97.MainResults
