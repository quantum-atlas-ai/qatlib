/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonAbelianHSP01.MainResults.Defs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults

open scoped IsMulCommutative

section AbelianClosure

variable {M : Type*} [Group M] {ι : Type*}

theorem isMulCommutative_closure_range (h : ι → M)
    (hcomm : ∀ i j : ι, Commute (h i) (h j)) :
    IsMulCommutative (Subgroup.closure (Set.range h)) :=
  Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hcomm i j)

end AbelianClosure

section CommutingFamily

variable {M : Type*} [Group M] {ι : Type*} [Fintype ι] [DecidableEq ι]

def closureGen (h : ι → M) (i : ι) : Subgroup.closure (Set.range h) :=
  ⟨h i, Subgroup.subset_closure ⟨i, rfl⟩⟩

noncomputable def zpowProd (h : ι → M) (hcomm : ∀ i j : ι, Commute (h i) (h j))
    (m : ι → ℤ) : Subgroup.closure (Set.range h) :=
  letI : IsMulCommutative (Subgroup.closure (Set.range h)) :=
    isMulCommutative_closure_range h hcomm
  ∏ i, closureGen h i ^ m i

@[simp] theorem zpowProd_zero (h : ι → M) (hcomm : ∀ i j : ι, Commute (h i) (h j)) :
    zpowProd h hcomm 0 = 1 := by
  letI : IsMulCommutative (Subgroup.closure (Set.range h)) :=
    isMulCommutative_closure_range h hcomm
  simp [zpowProd]

theorem zpowProd_add (h : ι → M) (hcomm : ∀ i j : ι, Commute (h i) (h j))
    (m n : ι → ℤ) :
    zpowProd h hcomm (m + n) = zpowProd h hcomm m * zpowProd h hcomm n := by
  letI : IsMulCommutative (Subgroup.closure (Set.range h)) :=
    isMulCommutative_closure_range h hcomm
  simp only [zpowProd]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Pi.add_apply, zpow_add]

theorem zpowProd_neg (h : ι → M) (hcomm : ∀ i j : ι, Commute (h i) (h j))
    (m : ι → ℤ) :
    zpowProd h hcomm (-m) = (zpowProd h hcomm m)⁻¹ := by
  letI : IsMulCommutative (Subgroup.closure (Set.range h)) :=
    isMulCommutative_closure_range h hcomm
  have key : (∏ i, closureGen h i ^ (-m) i) = ∏ i, (closureGen h i ^ m i)⁻¹ := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Pi.neg_apply, zpow_neg]
  simp only [zpowProd]
  rw [key]
  simpa using
    (Finset.prod_inv_distrib (s := (Finset.univ : Finset ι))
      (f := fun i => closureGen h i ^ m i))

theorem zpowProd_single (h : ι → M) (hcomm : ∀ i j : ι, Commute (h i) (h j))
    (i : ι) :
    zpowProd h hcomm (Pi.single i (1 : ℤ)) = closureGen h i := by
  letI : IsMulCommutative (Subgroup.closure (Set.range h)) :=
    isMulCommutative_closure_range h hcomm
  simp [zpowProd, Pi.single_apply]

theorem mem_closure_iff_exists_zpow_vector (h : ι → M)
    (hcomm : ∀ i j : ι, Commute (h i) (h j)) (g : M) :
    g ∈ Subgroup.closure (Set.range h) ↔
      ∃ m : ι → ℤ, (zpowProd h hcomm m : M) = g := by
  constructor
  · intro hg
    refine Subgroup.closure_induction (k := Set.range h)
      (p := fun x _ => ∃ m : ι → ℤ, (zpowProd h hcomm m : M) = x) ?_ ?_ ?_ ?_ hg
    · rintro x ⟨i, rfl⟩
      exact ⟨Pi.single i 1, by simp [zpowProd_single, closureGen]⟩
    · exact ⟨0, by simp [zpowProd_zero]⟩
    · rintro x y _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
      refine ⟨m + n, ?_⟩
      rw [zpowProd_add]
      rfl
    · rintro x _ ⟨m, rfl⟩
      refine ⟨-m, ?_⟩
      rw [zpowProd_neg]
      rfl
  · rintro ⟨m, rfl⟩
    exact (zpowProd h hcomm m).2

theorem exists_coprime_kernel_iff (h : ι → M)
    (hcomm : ∀ i j : ι, Commute (h i) (h j)) (g : M) :
    g ∈ Subgroup.closure (Set.range h) ↔
      ∃ (m : ι → ℤ) (n : ℤ),
        Nat.Coprime n.natAbs (orderOf g) ∧
          (zpowProd h hcomm m : M) * g ^ (-n) = 1 := by
  constructor
  · intro hg
    obtain ⟨m, hm⟩ := (mem_closure_iff_exists_zpow_vector h hcomm g).1 hg
    refine ⟨m, 1, by simp, ?_⟩
    rw [hm]
    simp
  · rintro ⟨m, n, hcop, hker⟩

    set x : M := (zpowProd h hcomm m : M) with hx
    have hxmem : x ∈ Subgroup.closure (Set.range h) := (zpowProd h hcomm m).2

    have hgn : g ^ n = x := by
      have h1 : g ^ (-n) = x⁻¹ := eq_inv_of_mul_eq_one_right hker
      calc
        g ^ n = (g ^ (-n))⁻¹ := by rw [zpow_neg, inv_inv]
        _ = (x⁻¹)⁻¹ := by rw [h1]
        _ = x := inv_inv x

    have hgcd : Int.gcd n (orderOf g) = 1 := by
      rw [Int.gcd_def]
      simpa using hcop
    have hdvd : Int.gcd n (orderOf g : ℕ) ∣ (1 : ℕ) := by
      simpa [hgcd] using (dvd_refl (1 : ℕ))
    obtain ⟨u, v, huv⟩ :=
      (Int.gcd_dvd_iff (a := n) (b := ((orderOf g : ℕ) : ℤ))).1 hdvd

    have hgu : g = x ^ u := by
      have h1 : g = g ^ (n * u + (orderOf g : ℤ) * v) := by
        rw [← huv]
        simp
      rw [h1, zpow_add, zpow_mul, zpow_mul, zpow_natCast, pow_orderOf_eq_one, hgn]
      simp
    rw [hgu]
    exact Subgroup.zpow_mem (K := Subgroup.closure (Set.range h)) hxmem u

end CommutingFamily

section QuotientMembership

variable {G : Type*} [Group G] {X : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem f_eq_one_iff_quotient_eq_one {N : Subgroup G} [N.Normal] (f : G → X)
    (hf : ∀ a b : G, f a = f b ↔ a⁻¹ * b ∈ N) (y : G) :
    f y = f 1 ↔ (y : G ⧸ N) = 1 := by
  rw [show f y = f 1 ↔ y⁻¹ * 1 ∈ N from hf y 1, mul_one, Subgroup.inv_mem_iff,
    QuotientGroup.eq_one_iff]

theorem quotient_membership_iff {N : Subgroup G} [N.Normal] (h : ι → G) (g : G)
    (hcomm : ∀ i j : ι, Commute ((h i : G ⧸ N)) ((h j : G ⧸ N))) :
    (g : G ⧸ N) ∈ Subgroup.closure (Set.range (fun i => (h i : G ⧸ N))) ↔
      ∃ (m : ι → ℤ) (n : ℤ),
        Nat.Coprime n.natAbs (orderOf ((g : G ⧸ N))) ∧
          (zpowProd (fun i => (h i : G ⧸ N)) hcomm m : G ⧸ N) *
            (g : G ⧸ N) ^ (-n) = 1 :=
  exists_coprime_kernel_iff (fun i => (h i : G ⧸ N)) hcomm (g : G ⧸ N)

theorem order_in_quotient_eq_period {N : Subgroup G} [N.Normal] (g : G) (k : ℕ) :
    (g : G ⧸ N) ^ k = 1 ↔ g ^ k ∈ N := by
  rw [← QuotientGroup.eq_one_iff (g ^ k), ← QuotientGroup.mk_pow]

theorem order_in_quotient_dvd_iff {N : Subgroup G} [N.Normal] (g : G) (k : ℕ) :
    (g : G ⧸ N) ^ k = 1 ↔ orderOf ((g : G ⧸ N)) ∣ k :=
  orderOf_dvd_iff_pow_eq_one.symm

end QuotientMembership

end Qatlib.Papers.NonAbelianHSP01.MainResults
