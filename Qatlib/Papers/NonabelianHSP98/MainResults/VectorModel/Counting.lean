/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Orthogonal
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Counting

open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup.Wreath
open Qatlib.Papers.NonabelianHSP98.MainResults.Pairing
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Orthogonal
open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

@[simp] lemma phi_a (g : Wreath n) : (phi g).2.2 = g.a := by
  rcases zmod2_eq_zero_or_one g.a with h | h
  · simp [phi, h]
  · simp [phi, h]

lemma add_self_eq_zero (v : Vec n) : v + v = 0 := by
  rcases v with ⟨x, y, a⟩
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i
    exact CharTwo.add_self_eq_zero (x i)
  · funext i
    exact CharTwo.add_self_eq_zero (y i)
  · exact CharTwo.add_self_eq_zero a

def wreathEquiv (n : ℕ) :
    Wreath n ≃ ((Fin n → ZMod 2) × (Fin n → ZMod 2) × ZMod 2) where
  toFun g := (g.x, g.y, g.a)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv g := by cases g; rfl
  right_inv p := by rcases p with ⟨x, y, a⟩; rfl

theorem card_wreath (n : ℕ) : Fintype.card (Wreath n) = 2 ^ (2 * n + 1) := by
  rw [Fintype.card_congr (wreathEquiv n)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  rw [show (2 : ℕ) ^ n * (2 ^ n * 2) = 2 ^ (2 * n + 1) by
    rw [show 2 * n + 1 = n + (n + 1) by omega, pow_add, pow_add]
    norm_num]

theorem four_dvd_card_subgroup (U : Subgroup (Wreath n)) (hcard : 4 ≤ Fintype.card U) :
    4 ∣ Fintype.card U := by
  classical
  have hdvd : Fintype.card U ∣ 2 ^ (2 * n + 1) := by
    simpa [card_wreath] using Subgroup.card_subgroup_dvd_card U
  obtain ⟨j, -, hj⟩ :=
    (Nat.dvd_prime_pow (show Nat.Prime 2 by norm_num) (m := 2 * n + 1)
      (i := Fintype.card U)).mp hdvd
  have h2 : 2 ≤ j := by
    have h4 : 4 ≤ 2 ^ j := by rwa [hj] at hcard
    have h22 : 2 ^ 2 ≤ 2 ^ j := by simpa using h4
    exact (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp h22
  rw [hj]
  simpa using! (pow_dvd_pow 2 h2)

def phiSubEquiv (U : Subgroup (Wreath n)) : U ≃ phiSub U where
  toFun x := ⟨phi x, mem_phiSub.mpr x.2⟩
  invFun w := ⟨phiInv w, mem_phiSub.mp (by rw [phiInv_phi]; exact w.2)⟩
  left_inv x := by apply Subtype.ext; simp [phi_phiInv]
  right_inv w := by apply Subtype.ext; simp [phiInv_phi]

theorem card_phiSub (U : Subgroup (Wreath n)) :
    Fintype.card (phiSub U) = Fintype.card U := by
  classical
  exact (Fintype.card_congr (phiSubEquiv U)).symm

theorem sum_mu_eq_sum_dot (U : Subgroup (Wreath n)) (y : Wreath n) :
    (∑ u : U, mu (u : Wreath n) y) = ∑ w : phiSub U, dot (phi y) (w : Vec n) := by
  classical
  rw [Fintype.sum_equiv (phiSubEquiv U)
    (fun u : U => mu (u : Wreath n) y) (fun w : phiSub U => dot (phi y) (w : Vec n))]
  intro u
  rw [phi_mu]
  exact dot_comm _ _

theorem exists_dot_one (W : Submodule (ZMod 2) (Vec n)) (y : Vec n)
    (hne : ∃ w ∈ W, dot y w ≠ 0) : ∃ w₀ ∈ W, dot y w₀ = 1 := by
  obtain ⟨w, hw, hne⟩ := hne
  refine ⟨w, hw, ?_⟩
  rcases zmod2_eq_zero_or_one (dot y w) with h | h
  · exact absurd h hne
  · exact h

theorem card_dot_zero_eq_one (W : Submodule (ZMod 2) (Vec n)) (y : Vec n)
    (w₀ : Vec n) (hw₀ : w₀ ∈ W) (hd₀ : dot y w₀ = 1) :
    (univ.filter (fun w : W => dot y (w : Vec n) = 0)).card
      = (univ.filter (fun w : W => dot y (w : Vec n) = 1)).card := by
  classical
  apply Finset.card_bij
    (fun (w : W) (_ : w ∈ univ.filter (fun w : W => dot y (w : Vec n) = 0)) =>
      (⟨(w : Vec n) + w₀, W.add_mem w.2 hw₀⟩ : W))
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    rw [dot_add_right, hw, hd₀, zero_add]
  · intro a _ b _ h
    apply Subtype.ext
    have h' := congrArg (fun z : W => (z : Vec n)) h
    simp only [Subtype.coe_mk] at h'
    exact add_right_cancel h'
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz
    refine ⟨⟨(z : Vec n) + w₀, W.add_mem z.2 hw₀⟩, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      rw [dot_add_right, hz, hd₀]
      decide
    · apply Subtype.ext
      simp only [Subtype.coe_mk]
      rw [add_assoc, add_self_eq_zero, add_zero]

theorem sum_dot_eq_zero (W : Submodule (ZMod 2) (Vec n)) (y : Vec n)
    (hne : ∃ w ∈ W, dot y w ≠ 0) (h4 : 4 ∣ Fintype.card W) :
    (∑ w : W, dot y (w : Vec n)) = 0 := by
  classical
  obtain ⟨w₀, hw₀, hd₀⟩ := exists_dot_one W y hne
  have hcount := card_dot_zero_eq_one W y w₀ hw₀ hd₀
  let A : Finset W := univ.filter (fun w : W => dot y (w : Vec n) = 0)
  let B : Finset W := univ.filter (fun w : W => dot y (w : Vec n) = 1)
  have hAB : A.card = B.card := by simpa only [A, B] using hcount
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro w hwA hwB
    simp only [A, B, mem_filter, mem_univ, true_and] at hwA hwB
    rw [hwA] at hwB
    exact zero_ne_one hwB
  have hunion : A ∪ B = univ := by
    ext w
    simp only [A, B, mem_union, mem_filter, mem_univ, true_and, iff_true]
    rcases zmod2_eq_zero_or_one (dot y (w : Vec n)) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hcardW : 2 * B.card = Fintype.card W := by
    have hc := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ] at hc
    omega
  have hB : 2 ∣ B.card := by
    obtain ⟨k, hk⟩ := h4
    refine ⟨k, ?_⟩
    omega
  have hsum : (∑ w : W, dot y (w : Vec n))
      = ((univ.filter (fun w : W => dot y (w : Vec n) = 1)).card : ZMod 2) := by
    calc (∑ w : W, dot y (w : Vec n))
        = ∑ w : W, (if dot y (w : Vec n) = 1 then (1 : ZMod 2) else 0) := by
          apply Finset.sum_congr rfl
          intro w _
          rcases zmod2_eq_zero_or_one (dot y (w : Vec n)) with h | h
          · simp [h]
          · simp [h]
      _ = ((univ.filter (fun w : W => dot y (w : Vec n) = 1)).card : ZMod 2) := by
          simpa using (Finset.sum_boole (univ : Finset W)
            (fun w : W => dot y (w : Vec n) = 1))
  rw [hsum]
  obtain ⟨m, hm⟩ := hB
  rw [hm, Nat.cast_mul]
  have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [h2, zero_mul]

noncomputable def chi : ZMod 2 → ℂ := fun a => if a = 0 then 1 else -1

theorem sum_chi_eq_zero (W : Submodule (ZMod 2) (Vec n)) (y : Vec n)
    (hne : ∃ w ∈ W, dot y w ≠ 0) :
    (∑ w : W, chi (dot y (w : Vec n))) = 0 := by
  classical
  obtain ⟨w₀, hw₀, hd₀⟩ := exists_dot_one W y hne
  have hcount := card_dot_zero_eq_one W y w₀ hw₀ hd₀
  let A : Finset W := univ.filter (fun w : W => dot y (w : Vec n) = 0)
  let B : Finset W := univ.filter (fun w : W => dot y (w : Vec n) = 1)
  have hAB : A.card = B.card := by simpa only [A, B] using hcount
  have hsplit : (∑ w : W, chi (dot y (w : Vec n)))
      = A.sum (fun w => chi (dot y (w : Vec n)))
        + B.sum (fun w => chi (dot y (w : Vec n))) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := (univ : Finset W))
      (p := fun w : W => dot y (w : Vec n) = 0)]
    have hAeq : (univ.filter (fun w : W => dot y (w : Vec n) = 0)) = A := rfl
    have hBeq : (univ.filter (fun w : W => ¬ dot y (w : Vec n) = 0)) = B := by
      ext w
      simp only [B, mem_filter, mem_univ, true_and]
      constructor
      · intro h
        rcases zmod2_eq_zero_or_one (dot y (w : Vec n)) with h0 | h1
        · exact absurd h0 h
        · exact h1
      · intro h h0
        rw [h0] at h
        exact zero_ne_one h
    rw [hAeq, hBeq]
  rw [hsplit]
  have hA : A.sum (fun w => chi (dot y (w : Vec n))) = (A.card : ℂ) := by
    calc A.sum (fun w => chi (dot y (w : Vec n)))
        = A.sum (fun _ => (1 : ℂ)) := by
          apply Finset.sum_congr rfl
          intro w hw
          simp only [A, mem_filter, mem_univ, true_and] at hw
          simp [chi, hw]
      _ = (A.card : ℂ) := by simp
  have hB : B.sum (fun w => chi (dot y (w : Vec n))) = -((B.card : ℂ)) := by
    calc B.sum (fun w => chi (dot y (w : Vec n)))
        = B.sum (fun _ => (-1 : ℂ)) := by
          apply Finset.sum_congr rfl
          intro w hw
          simp only [B, mem_filter, mem_univ, true_and] at hw
          simp [chi, hw]
      _ = -((B.card : ℂ)) := by simp
  rw [hA, hB, hAB]
  ring

end Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Counting
