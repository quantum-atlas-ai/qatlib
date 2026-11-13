/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.RandomResource

/-!
# Existence of collision-free linear response codes

This module uses collision bounds to construct a generator matrix whose responses separate an
entire finite candidate family. It proves birthday-style row cutoffs, exact one-query recovery
with a fixed separating matrix, and code lengths capped by the database dimension, formalizing
the code-existence argument of [TerhalSmolin1998].

## Main statements

* `exists_prime_cutoff`: Over a prime alphabet, every injective candidate family possesses a
  separating response matrix with `2*Nat.clog A k + 1` rows, giving the birthday-code existence
  bound of [TerhalSmolin1998].
* `whole_family_recovery`: A fixed matrix separating all candidates yields a point-mass decoded
  output at the true label with exactly one oracle query, as in the collision-free construction
  of [TerhalSmolin1998].

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.ZeroCodeExist

open LinearCodeProgram RandomHashLaw RandomRecovery

variable {A m n k : ℕ} [NeZero A] [NeZero k]

omit [NeZero k] in

/-- If each candidate's collision probability is bounded by `(k - 1)*q` and `k*(k - 1)*q < 1`,
some generator matrix separates all candidates. -/
theorem exists_injective_code_of_bound (candidates : Fin k → Fin n → ZMod A) (q : ENNReal)
    (hcollision : ∀ t : Fin k, (matrixLaw A m n).toOuterMeasure
      {g | ∃ j : {j : Fin k // j≠t}, response g (candidates j) = response g (candidates t)} ≤
      ((k-1:ℕ):ENNReal)*q)
    (hbudget : (k:ENNReal)*((k-1:ℕ):ENNReal)*q < 1) :
    ∃ g : Fin m → Fin n → ZMod A, Function.Injective (fun t => response g (candidates t)) := by
  classical
  by_contra hn
  have hall (g : Fin m → Fin n → ZMod A) :
      ∃ t : Fin k, ∃ j : {j : Fin k // j≠t}, response g (candidates j) = response g (candidates t) := by
    have hg : ¬Function.Injective (fun t => response g (candidates t)) := fun h => hn ⟨g,h⟩
    simp only [Function.Injective] at hg
    push Not at hg
    obtain ⟨t,j,he,hne⟩ := hg
    exact ⟨t,⟨j,Ne.symm hne⟩,he.symm⟩
  have he : (⋃ t : Fin k, {g : Fin m → Fin n → ZMod A |
      ∃ j : {j : Fin k // j≠t}, response g (candidates j) = response g (candidates t)}) = Set.univ := by
    ext g
    simp only [Set.mem_iUnion,Set.mem_setOf_eq,Set.mem_univ,iff_true]
    exact hall g
  have hu := MeasureTheory.measure_iUnion_le (μ:=(matrixLaw A m n).toOuterMeasure)
    (fun t : Fin k => {g | ∃ j : {j : Fin k // j≠t}, response g (candidates j) = response g (candidates t)})
  rw [he] at hu
  have hone : (matrixLaw A m n).toOuterMeasure Set.univ = 1 := by
    rw [PMF.toOuterMeasure_apply]
    simpa only [Set.indicator_univ] using (matrixLaw A m n).tsum_coe
  rw [hone] at hu
  have hb : (1:ENNReal) ≤ (k:ENNReal)*((k-1:ℕ):ENNReal)*q := by
    calc
      1 ≤ _ := hu
      _ ≤ ∑' _ : Fin k, ((k-1:ℕ):ENNReal)*q := ENNReal.tsum_le_tsum hcollision
      _ = _ := by simp [mul_assoc]
  exact (not_le_of_gt hbudget) hb

omit [NeZero A] in

/-- For a fixed generator matrix with injective candidate responses, the response decoder
returns the true label exactly. -/
theorem decoder_exact (candidates : Fin k → Fin n → ZMod A)
    (g : Fin m → Fin n → ZMod A)
    (hcode : Function.Injective (fun t => response g (candidates t))) (t : Fin k) :
    decoder candidates g (response g (candidates t)) = t := by
  by_contra h
  obtain ⟨j,hj⟩ := error_implies_collision candidates g t h
  exact j.property (hcode hj)

/-- For `b ≥ 2`, the birthday collision budget at row count `2*Nat.clog b k + 1` is strictly
less than one. -/
theorem birthday_budget (k b : ℕ) (hb : 2≤b) :
    (k:ENNReal)*((k-1:ℕ):ENNReal)*((1:ENNReal)/(b:ENNReal)^(2*Nat.clog b k+1)) < 1 := by
  have hbpos : 0<b := by omega
  have hc : k*(k-1) < b^(2*Nat.clog b k+1) := by
    have hk := Nat.le_pow_clog (by omega : 1<b) k
    have hp : 0<b^(Nat.clog b k) := Nat.pow_pos hbpos
    have he : b^(2*Nat.clog b k+1) = (b^(Nat.clog b k)*b^(Nat.clog b k))*b := by
      rw [show 2*Nat.clog b k+1 = (Nat.clog b k+Nat.clog b k)+1 by omega,pow_succ,pow_add]
    rw [he]
    calc
      k*(k-1) ≤ k*k := Nat.mul_le_mul_left k (Nat.sub_le k 1)
      _ ≤ b^(Nat.clog b k)*b^(Nat.clog b k) := Nat.mul_le_mul hk hk
      _ < _ := by nlinarith
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_natCast,
    ENNReal.toReal_one,ENNReal.toReal_pow]
  rw [mul_one_div]
  apply (div_lt_one (by positivity : (0:ℝ)<(b:ℝ)^(2*Nat.clog b k+1))).2
  exact_mod_cast hc

omit [NeZero k] in

/-- Every injective candidate family possesses a separating response matrix with `2*Nat.clog 2 k
+ 1` rows. -/
theorem exists_binary_cutoff (candidates : Fin k → Fin n → ZMod A)
    (hinj : Function.Injective candidates) :
    ∃ g : Fin (2*Nat.clog 2 k+1) → Fin n → ZMod A,
      Function.Injective (fun t => response g (candidates t)) :=
  exists_injective_code_of_bound candidates ((1:ENNReal)/2^(2*Nat.clog 2 k+1))
    (general_collision_union_bound candidates hinj) (birthday_budget k 2 (by decide))

omit [NeZero k] in

/-- Over a prime alphabet, every injective candidate family possesses a separating response
matrix with `2*Nat.clog A k + 1` rows, giving the birthday-code existence bound of
[TerhalSmolin1998]. -/
theorem exists_prime_cutoff [Fact (Nat.Prime A)] (candidates : Fin k → Fin n → ZMod A)
    (hinj : Function.Injective candidates) :
    ∃ g : Fin (2*Nat.clog A k+1) → Fin n → ZMod A,
      Function.Injective (fun t => response g (candidates t)) :=
  exists_injective_code_of_bound candidates ((1:ENNReal)/A^(2*Nat.clog A k+1))
    (collision_union_bound candidates hinj) (birthday_budget k A (Nat.Prime.two_le Fact.out))

/-- A fixed matrix separating all candidates yields a point-mass decoded output at the true
label with exactly one oracle query, as in the collision-free construction of
[TerhalSmolin1998]. -/
theorem whole_family_recovery (candidates : Fin k → Fin n → ZMod A)
    (g : Fin m → Fin n → ZMod A)
    (hcode : Function.Injective (fun t => response g (candidates t))) (t : Fin k) :
    (ResourceProgram.measured g (candidates t)).map (fun p => decoder candidates g p.1.1) = PMF.pure t ∧
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (ResourceProgram.program g) = 1 := by
  constructor
  · rw [ResourceProgram.measured_eq,outputLaw_decoded,decoder_exact candidates g hcode t]
  · exact (ResourceProgram.program_resources g).1

omit [NeZero k] [NeZero A] in

/-- If a separating code of length `M` exists for an injective candidate family, one also exists
with length at most `min n M`. -/
theorem cap_code_length (candidates : Fin k → Fin n → ZMod A)
    (hinj : Function.Injective candidates) (M : ℕ)
    (hex : ∃ g : Fin M → Fin n → ZMod A, Function.Injective (fun t => response g (candidates t))) :
    ∃ m, m ≤ min n M ∧ ∃ g : Fin m → Fin n → ZMod A,
      Function.Injective (fun t => response g (candidates t)) := by
  by_cases h : n≤M
  · refine ⟨n,Nat.le_min.mpr ⟨le_rfl,h⟩,FullDatabase.identityQueries A n,?_⟩
    intro t j he
    apply hinj
    simpa only [FullDatabase.response_identity] using he
  · obtain ⟨g,hg⟩ := hex
    exact ⟨M,Nat.le_min.mpr ⟨by omega,le_rfl⟩,g,hg⟩

omit [NeZero k] in

/-- Every injective candidate family possesses a separating code of length at most `min n
(2*Nat.clog 2 k + 1)`, providing a dimension-capped code-existence bound for
[TerhalSmolin1998]. -/
theorem capped_binary_code (candidates : Fin k → Fin n → ZMod A)
    (hinj : Function.Injective candidates) :
    ∃ m, m ≤ min n (2*Nat.clog 2 k+1) ∧ ∃ g : Fin m → Fin n → ZMod A,
      Function.Injective (fun t => response g (candidates t)) :=
  cap_code_length candidates hinj _ (exists_binary_cutoff candidates hinj)

end Qatlib.Papers.SingleQuery97.MainResults.ZeroCodeExist
