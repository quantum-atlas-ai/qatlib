/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LinkInvQFT12.MainResults.SourceModel
import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Alternating

set_option backward.isDefEq.respectTransparency false

/-!
# LinkInvQFT12.MainResults.Lemma6 — two solutions of the conjugation equation (c005)

Krovi--Russell, arXiv:1210.1550 (v2 PDF, §5, Figure 5 discussion, p.21, Lemma 6;
extraction lines 1151–1156).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LinkInvQFT12.MainResults

/-- The `k`-cycle `(0 1 ⋯ (k−1))` on `Fin m` (the paper's `(1 2 ⋯ k)`, written
zero-based).  Used to state the hypothesis that `α` has this `k`-cycle; the paper's
Figure 5 discussion fixes `k ≥ 2`. -/
def kCycle (m k : ℕ) (hk : k ≤ m) : Equiv.Perm (Fin m) :=
  ((List.finRange k).map (fun i : Fin k => (⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ : Fin m))).formPerm

/-- The permutation `σ = (0 k−1)(m−4 m−3)` on `Fin m` — the paper's
`(1 k)(m−2 m−3)`, written zero-based, which appears in the exponent of Lemma 6's
equation `y = α^{(1 k)(m−2 m−3)y}`. -/
def sigmaPerm (m k : ℕ) (hk : 2 ≤ k) (hkm : k + 4 ≤ m) : Equiv.Perm (Fin m) :=
  Equiv.swap ⟨0, by omega⟩ ⟨k - 1, by omega⟩ *
    Equiv.swap ⟨m - 4, by omega⟩ ⟨m - 3, by omega⟩

variable {m k : ℕ}

/-- The transposition `(k−1, m−1)` of the first solution. -/
def tauOne (m k : ℕ) (hk : 2 ≤ k) (hkm : k + 4 ≤ m) : Equiv.Perm (Fin m) :=
  Equiv.swap ⟨k - 1, by omega⟩ ⟨m - 1, by omega⟩

/-- The transposition `(k−1, m−2)` of the second solution. -/
def tauTwo (m k : ℕ) (hk : 2 ≤ k) (hkm : k + 4 ≤ m) : Equiv.Perm (Fin m) :=
  Equiv.swap ⟨k - 1, by omega⟩ ⟨m - 2, by omega⟩

/-- The embedding `j ↦ j` of `Fin k` into `Fin m` for `k ≤ m`. -/
def emb {m k : ℕ} (hk : k ≤ m) (j : Fin k) : Fin m := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩

-- kCycle = formPerm of the embedded range
/-- The `k`-cycle is the `formPerm` of the embedded list `0, …, k−1`. -/
lemma kc_eq_formPerm (hk : k ≤ m) :
    kCycle m k hk = (List.ofFn (emb hk)).formPerm := by
  unfold kCycle emb
  rw [List.ofFn_eq_map]

-- successor formula
/-- The `k`-cycle sends `i` to `i+1` whenever `i+1 < k`. -/
lemma kc_succ (hk : k ≤ m) (i : Fin m) (hi : i.val + 1 < k) :
    kCycle m k hk i = ⟨i.val + 1, Nat.lt_of_lt_of_le hi hk⟩ := by
  unfold kCycle
  have hinj : Function.Injective (fun j : Fin k => (⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩ : Fin m)) := by
    intro a b hab
    exact Fin.ext (congrArg (fun x : Fin m => x.val) hab)
  have hnd := (List.nodup_finRange k).map hinj
  have hget : ((List.finRange k).map (fun j : Fin k => (⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩ : Fin m)))[i.val]'(by simp; omega) = i := by
    simp only [← List.ofFn_eq_map]
    rw [List.getElem_ofFn]
  conv_lhs => rw [← hget]
  rw [List.formPerm_apply_getElem _ hnd i.val (by simp; omega)]
  simp only [← List.ofFn_eq_map]
  rw [List.getElem_ofFn]
  exact Fin.ext (by simp [Nat.mod_eq_of_lt hi])

-- last-point formula
/-- The `k`-cycle sends `k−1` to `0`. -/
lemma kc_last (hk2 : 2 ≤ k) (hk : k ≤ m) :
    kCycle m k hk ⟨k - 1, by omega⟩ = ⟨0, by omega⟩ := by
  unfold kCycle
  have hinj : Function.Injective (fun j : Fin k => (⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩ : Fin m)) := by
    intro a b hab
    exact Fin.ext (congrArg (fun x : Fin m => x.val) hab)
  have hnd := (List.nodup_finRange k).map hinj
  have hget : ((List.finRange k).map (fun j : Fin k => (⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩ : Fin m)))[k - 1]'(by simp; omega) = ⟨k - 1, by omega⟩ := by
    simp only [← List.ofFn_eq_map]
    rw [List.getElem_ofFn]
  conv_lhs => rw [← hget]
  rw [List.formPerm_apply_getElem _ hnd (k - 1) (by simp; omega)]
  simp only [← List.ofFn_eq_map]
  rw [List.getElem_ofFn]
  exact Fin.ext (by
    simp only [List.length_ofFn]
    rw [show k - 1 + 1 = k from Nat.sub_add_cancel (by omega)]
    exact Nat.mod_self k)

-- points at or beyond k are fixed
/-- The `k`-cycle fixes every point whose value is at least `k`. -/
lemma kc_ge (hk : k ≤ m) (i : Fin m) (hi : k ≤ i.val) :
    kCycle m k hk i = i := by
  unfold kCycle
  rw [List.formPerm_apply_of_notMem]
  intro hmem
  rw [List.mem_map] at hmem
  obtain ⟨j, -, hj⟩ := hmem
  have := congrArg Fin.val hj
  simp at this
  omega

/-- Conjugation of a `List.formPerm` acts on the list entries. -/
lemma conj_formPerm {α : Type*} [DecidableEq α] (σ : Equiv.Perm α) (l : List α) :
    σ * l.formPerm * σ⁻¹ = (l.map σ).formPerm := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      rw [List.formPerm_cons_cons, List.map_cons, List.map_cons, List.formPerm_cons_cons]
      calc σ * (Equiv.swap x y * (y :: ys).formPerm) * σ⁻¹
          = (σ * Equiv.swap x y * σ⁻¹) * (σ * (y :: ys).formPerm * σ⁻¹) := by group
        _ = Equiv.swap (σ x) (σ y) * (σ * (y :: ys).formPerm * σ⁻¹) := by
              rw [Equiv.swap_apply_apply]
        _ = Equiv.swap (σ x) (σ y) * ((y :: ys).map σ).formPerm := by rw [ih]

-- sigma is an involution
/-- `σ = (0 k−1)(m−4 m−3)` is an involution. -/
lemma sigma_invol (hk : 2 ≤ k) (hkm : k + 4 ≤ m) :
    sigmaPerm m k hk hkm * sigmaPerm m k hk hkm = 1 := by
  unfold sigmaPerm
  have hnd : ([⟨0, by omega⟩, ⟨k - 1, by omega⟩, ⟨m - 4, by omega⟩,
      ⟨m - 3, by omega⟩] : List (Fin m)).Nodup := by
    simp [List.nodup_cons, Fin.ext_iff]
    omega
  have hcomm : Commute (Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨k - 1, by omega⟩)
      (Equiv.swap (⟨m - 4, by omega⟩ : Fin m) ⟨m - 3, by omega⟩) :=
    Equiv.Perm.Disjoint.commute (Equiv.Perm.disjoint_swap_swap (x := (⟨0, by omega⟩ : Fin m))
      (y := ⟨k - 1, by omega⟩) (z := ⟨m - 4, by omega⟩) (t := ⟨m - 3, by omega⟩) hnd)
  calc Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨k - 1, by omega⟩ *
        Equiv.swap (⟨m - 4, by omega⟩ : Fin m) ⟨m - 3, by omega⟩ *
        (Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨k - 1, by omega⟩ *
          Equiv.swap (⟨m - 4, by omega⟩ : Fin m) ⟨m - 3, by omega⟩)
      = Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨k - 1, by omega⟩ *
        (Equiv.swap (⟨m - 4, by omega⟩ : Fin m) ⟨m - 3, by omega⟩ *
          Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨k - 1, by omega⟩) *
        Equiv.swap (⟨m - 4, by omega⟩ : Fin m) ⟨m - 3, by omega⟩ := by group
    _ = Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨k - 1, by omega⟩ *
        (Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨k - 1, by omega⟩ *
          Equiv.swap (⟨m - 4, by omega⟩ : Fin m) ⟨m - 3, by omega⟩) *
        Equiv.swap (⟨m - 4, by omega⟩ : Fin m) ⟨m - 3, by omega⟩ := by
        rw [hcomm.eq]
    _ = (Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨k - 1, by omega⟩ *
          Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨k - 1, by omega⟩) *
        (Equiv.swap (⟨m - 4, by omega⟩ : Fin m) ⟨m - 3, by omega⟩ *
          Equiv.swap (⟨m - 4, by omega⟩ : Fin m) ⟨m - 3, by omega⟩) := by group
    _ = 1 := by rw [Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]

/-- The conjugate `τ c τ` of the `k`-cycle, the first solution's `k`-cycle `(0 1 ⋯ k−2 m−1)`. -/
def cPerm (m k : ℕ) (hk : 2 ≤ k) (hkm : k + 4 ≤ m) : Equiv.Perm (Fin m) :=
  tauOne m k hk hkm * kCycle m k (by omega) * tauOne m k hk hkm

/-- The transposition `τ₁ = (k−1, m−1)` is an involution. -/
lemma tauOne_mul_self (hk : 2 ≤ k) (hkm : k + 4 ≤ m) :
    tauOne m k hk hkm * tauOne m k hk hkm = 1 := by
  unfold tauOne
  exact Equiv.swap_mul_self _ _

/-- `τ₁` fixes every point other than `k−1` and `m−1`. -/
lemma tauOne_apply_of_ne (hk : 2 ≤ k) (hkm : k + 4 ≤ m) (x : Fin m)
    (h1 : x ≠ ⟨k - 1, by omega⟩) (h2 : x ≠ ⟨m - 1, by omega⟩) :
    tauOne m k hk hkm x = x := by
  unfold tauOne
  exact Equiv.swap_apply_of_ne_of_ne h1 h2

/-- `τ₁` sends `k−1` to `m−1`. -/
lemma tauOne_apply_k1 (hk : 2 ≤ k) (hkm : k + 4 ≤ m) :
    tauOne m k hk hkm (⟨k - 1, by omega⟩ : Fin m) = ⟨m - 1, by omega⟩ := by
  unfold tauOne
  exact Equiv.swap_apply_left _ _

/-- `τ₁` sends `m−1` to `k−1`. -/
lemma tauOne_apply_m1 (hk : 2 ≤ k) (hkm : k + 4 ≤ m) :
    tauOne m k hk hkm (⟨m - 1, by omega⟩ : Fin m) = ⟨k - 1, by omega⟩ := by
  unfold tauOne
  exact Equiv.swap_apply_right _ _

/-- `σ` fixes every point outside `{0, k−1, m−4, m−3}`. -/
lemma sigma_apply_of_ne (hk : 2 ≤ k) (hkm : k + 4 ≤ m) (x : Fin m)
    (h0 : x ≠ ⟨0, by omega⟩) (h1 : x ≠ ⟨k - 1, by omega⟩)
    (h2 : x ≠ ⟨m - 4, by omega⟩) (h3 : x ≠ ⟨m - 3, by omega⟩) :
    sigmaPerm m k hk hkm x = x := by
  unfold sigmaPerm
  simp only [Equiv.Perm.mul_apply]
  have ha : (Equiv.swap (⟨m - 4, by omega⟩ : Fin m) ⟨m - 3, by omega⟩) x = x :=
    Equiv.swap_apply_of_ne_of_ne h2 h3
  rw [ha]
  exact Equiv.swap_apply_of_ne_of_ne h0 h1

/-- `σ` sends `0` to `k−1`. -/
lemma sigma_apply_zero (hk : 2 ≤ k) (hkm : k + 4 ≤ m) :
    sigmaPerm m k hk hkm (⟨0, by omega⟩ : Fin m) = ⟨k - 1, by omega⟩ := by
  unfold sigmaPerm
  simp only [Equiv.Perm.mul_apply]
  have ha : (Equiv.swap (⟨m - 4, by omega⟩ : Fin m) ⟨m - 3, by omega⟩) (⟨0, by omega⟩ : Fin m) = ⟨0, by omega⟩ := by
    apply Equiv.swap_apply_of_ne_of_ne <;> intro h <;> (have := congrArg Fin.val h; simp only [emb, Fin.val_mk] at this; omega)
  rw [ha]
  exact Equiv.swap_apply_left _ _

/-- `σ` fixes `m−1`. -/
lemma sigma_apply_m1 (hk : 2 ≤ k) (hkm : k + 4 ≤ m) :
    sigmaPerm m k hk hkm (⟨m - 1, by omega⟩ : Fin m) = ⟨m - 1, by omega⟩ := by
  unfold sigmaPerm
  simp only [Equiv.Perm.mul_apply]
  have ha : (Equiv.swap (⟨m - 4, by omega⟩ : Fin m) ⟨m - 3, by omega⟩) (⟨m - 1, by omega⟩ : Fin m) = ⟨m - 1, by omega⟩ := by
    apply Equiv.swap_apply_of_ne_of_ne <;> intro h <;> (have := congrArg Fin.val h; simp only [emb, Fin.val_mk] at this; omega)
  rw [ha]
  have hb : (Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨k - 1, by omega⟩) (⟨m - 1, by omega⟩ : Fin m) = ⟨m - 1, by omega⟩ := by
    apply Equiv.swap_apply_of_ne_of_ne <;> intro h <;> (have := congrArg Fin.val h; simp only [emb, Fin.val_mk] at this; omega)
  exact hb

/-- The conjugate cycle `c' = τ₁ c τ₁` sends the embedded `j` to `τ₁` of the embedded `j+1` when `j+1 < k`. -/
lemma cPerm_apply_step (hk : 2 ≤ k) (hkm : k + 4 ≤ m)
    (j : Fin k) (hj : j.val + 1 < k) :
    cPerm m k hk hkm (emb (by omega : k ≤ m) j) =
      tauOne m k hk hkm (emb (by omega : k ≤ m) ⟨j.val + 1, hj⟩) := by
  unfold cPerm
  simp only [Equiv.Perm.mul_apply]
  have hτ : tauOne m k hk hkm (emb (by omega : k ≤ m) j) = emb (by omega : k ≤ m) j := by
    apply tauOne_apply_of_ne hk hkm
    · intro h; have := congrArg Fin.val h; simp only [emb, Fin.val_mk] at this; omega
    · intro h; have := congrArg Fin.val h; simp only [emb, Fin.val_mk] at this; omega
  rw [hτ]
  rw [kc_succ (by omega : k ≤ m) (emb (by omega : k ≤ m) j) hj]
  rfl

/-- The conjugate cycle `c'` fixes the embedded point `k−1`. -/
lemma cPerm_apply_last (hk : 2 ≤ k) (hkm : k + 4 ≤ m) :
    cPerm m k hk hkm (emb (by omega : k ≤ m) ⟨k - 1, by omega⟩) = ⟨k - 1, by omega⟩ := by
  unfold cPerm
  simp only [Equiv.Perm.mul_apply]
  rw [show emb (by omega : k ≤ m) ⟨k - 1, by omega⟩ = (⟨k - 1, by omega⟩ : Fin m) from rfl]
  rw [show tauOne m k hk hkm (⟨k - 1, by omega⟩ : Fin m) = ⟨m - 1, by omega⟩ from tauOne_apply_k1 hk hkm]
  rw [show kCycle m k (by omega) (⟨m - 1, by omega⟩ : Fin m) = ⟨m - 1, by omega⟩ from
    kc_ge (by omega : k ≤ m) _ (by simp; omega)]
  rw [show tauOne m k hk hkm (⟨m - 1, by omega⟩ : Fin m) = ⟨k - 1, by omega⟩ from tauOne_apply_m1 hk hkm]

/-- The conjugate cycle `c'` fixes every point with `k ≤ x < m−4`. -/
lemma cPerm_apply_of_mid (hk : 2 ≤ k) (hkm : k + 4 ≤ m) (x : Fin m)
    (h1 : k ≤ x.val) (h2 : x.val < m - 4) :
    cPerm m k hk hkm x = x := by
  unfold cPerm
  simp only [Equiv.Perm.mul_apply]
  have hx1 : x ≠ ⟨k - 1, by omega⟩ := by intro h; have := congrArg Fin.val h; simp only [emb, Fin.val_mk] at this; omega
  have hx2 : x ≠ ⟨m - 1, by omega⟩ := by intro h; have := congrArg Fin.val h; simp only [emb, Fin.val_mk] at this; omega
  rw [tauOne_apply_of_ne hk hkm x hx1 hx2]
  rw [kc_ge (by omega : k ≤ m) x (by omega)]
  rw [tauOne_apply_of_ne hk hkm x hx1 hx2]

/-- The transposition `τ₂ = (k−1, m−2)` is an involution. -/
lemma tauTwo_mul_self (hk : 2 ≤ k) (hkm : k + 4 ≤ m) :
    tauTwo m k hk hkm * tauTwo m k hk hkm = 1 := by
  unfold tauTwo
  exact Equiv.swap_mul_self _ _

/-- `τ₂` fixes every point other than `k−1` and `m−2`. -/
lemma tauTwo_apply_of_ne (hk : 2 ≤ k) (hkm : k + 4 ≤ m) (x : Fin m)
    (h1 : x ≠ ⟨k - 1, by omega⟩) (h2 : x ≠ ⟨m - 2, by omega⟩) :
    tauTwo m k hk hkm x = x := by
  unfold tauTwo
  exact Equiv.swap_apply_of_ne_of_ne h1 h2

/-- `τ₂` sends `m−2` to `k−1`. -/
lemma tauTwo_apply_m2 (hk : 2 ≤ k) (hkm : k + 4 ≤ m) :
    tauTwo m k hk hkm (⟨m - 2, by omega⟩ : Fin m) = ⟨k - 1, by omega⟩ := by
  unfold tauTwo
  exact Equiv.swap_apply_right _ _

/-- `τ₂` sends `k−1` to `m−2`. -/
lemma tauTwo_apply_k1 (hk : 2 ≤ k) (hkm : k + 4 ≤ m) :
    tauTwo m k hk hkm (⟨k - 1, by omega⟩ : Fin m) = ⟨m - 2, by omega⟩ := by
  unfold tauTwo
  exact Equiv.swap_apply_left _ _

/-- `σ` fixes `m−2`. -/
lemma sigma_apply_m2 (hk : 2 ≤ k) (hkm : k + 4 ≤ m) :
    sigmaPerm m k hk hkm (⟨m - 2, by omega⟩ : Fin m) = ⟨m - 2, by omega⟩ := by
  apply sigma_apply_of_ne hk hkm
  · intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
  · intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
  · intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
  · intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega

/-- Evaluation at `0`: the `(σ τ)`-image is `k−1`. -/
lemma eval_zero (hk : 2 ≤ k) (hkm : k + 4 ≤ m) :
    (sigmaPerm m k hk hkm * tauOne m k hk hkm) (⟨0, by omega⟩ : Fin m) =
      ⟨k - 1, by omega⟩ := by
  have hτ : tauOne m k hk hkm (⟨0, by omega⟩ : Fin m) = ⟨0, by omega⟩ := by
    apply tauOne_apply_of_ne hk hkm
    · intro h; have := congrArg Fin.val h; simp only [emb, Fin.val_mk] at this; omega
    · intro h; have := congrArg Fin.val h; simp only [emb, Fin.val_mk] at this; omega
  simp only [Equiv.Perm.mul_apply]
  rw [hτ]
  exact sigma_apply_zero hk hkm

/-- Evaluation at `k−1`: the `(σ τ)`-image is `m−1`. -/
lemma eval_last (hk : 2 ≤ k) (hkm : k + 4 ≤ m) :
    (sigmaPerm m k hk hkm * tauOne m k hk hkm) (⟨k - 1, by omega⟩ : Fin m) =
      ⟨m - 1, by omega⟩ := by
  have hτ : tauOne m k hk hkm (⟨k - 1, by omega⟩ : Fin m) = ⟨m - 1, by omega⟩ :=
    tauOne_apply_k1 hk hkm
  simp only [Equiv.Perm.mul_apply]
  rw [hτ]
  exact sigma_apply_m1 hk hkm

/-- Evaluation at `1 ≤ n ≤ k−2`: the `(σ τ)`-image is fixed. -/
lemma eval_mid (hk : 2 ≤ k) (hkm : k + 4 ≤ m) (n : ℕ) (hn1 : 1 ≤ n) (hn2 : n ≤ k - 2) :
    (sigmaPerm m k hk hkm * tauOne m k hk hkm)
        (emb (by omega : k ≤ m) ⟨n, by omega⟩) =
      emb (by omega : k ≤ m) ⟨n, by omega⟩ := by
  simp only [Equiv.Perm.mul_apply]
  have hτ : tauOne m k hk hkm (emb (by omega : k ≤ m) ⟨n, by omega⟩) =
      emb (by omega : k ≤ m) ⟨n, by omega⟩ := by
    apply tauOne_apply_of_ne hk hkm
    · intro h; have := congrArg Fin.val h; simp only [emb, Fin.val_mk] at this; omega
    · intro h; have := congrArg Fin.val h; simp only [emb, Fin.val_mk] at this; omega
  rw [hτ]
  exact sigma_apply_of_ne hk hkm _
    (by intro h; have := congrArg Fin.val h; simp only [emb, Fin.val_mk] at this; omega)
    (by intro h; have := congrArg Fin.val h; simp only [emb, Fin.val_mk] at this; omega)
    (by intro h; have := congrArg Fin.val h; simp only [emb, Fin.val_mk] at this; omega)
    (by intro h; have := congrArg Fin.val h; simp only [emb, Fin.val_mk] at this; omega)

/-- The core conjugation identity `σ c' σ = c' c c'⁻¹` for `c' = τ c τ`. -/
lemma sigma_conj_cPerm (hk : 2 ≤ k) (hkm : k + 4 ≤ m) :
    sigmaPerm m k hk hkm * cPerm m k hk hkm * sigmaPerm m k hk hkm =
      cPerm m k hk hkm * kCycle m k (by omega) * (cPerm m k hk hkm)⁻¹ := by
  have hk_le : k ≤ m := by omega
  let L : List (Fin m) := List.ofFn (emb hk_le)
  have hc : kCycle m k (by omega) = L.formPerm := by
    show kCycle m k (by omega) = (List.ofFn (emb hk_le)).formPerm
    exact kc_eq_formPerm hk_le
  have hndL : L.Nodup := by
    rw [show L = List.ofFn (emb hk_le) from rfl, List.nodup_ofFn]
    intro a b hab
    exact Fin.ext (congrArg (fun x : Fin m => x.val) hab)
  have hrot : L.map (sigmaPerm m k hk hkm * tauOne m k hk hkm) =
      (L.map (cPerm m k hk hkm)).rotate (k - 1) := by
    apply List.ext_getElem?
    intro n
    by_cases hn : n < k
    · have hLget : L[n]? = some (emb hk_le ⟨n, hn⟩) := by
        simp [L, List.getElem?_ofFn, hn]
      have hmapF : (L.map (sigmaPerm m k hk hkm * tauOne m k hk hkm))[n]? =
          some ((sigmaPerm m k hk hkm * tauOne m k hk hkm) (emb hk_le ⟨n, hn⟩)) := by
        rw [List.getElem?_map, hLget]
        rfl
      have hGlen : (L.map (cPerm m k hk hkm)).length = k := by simp [L]
      have hmodlt : (n + (k - 1)) % k < k := Nat.mod_lt _ (y := k) (by omega)
      have hrotn : ((L.map (cPerm m k hk hkm)).rotate (k - 1))[n]? =
          some (cPerm m k hk hkm (emb hk_le ⟨(n + (k - 1)) % k, hmodlt⟩)) := by
        rw [List.getElem?_rotate (l := L.map (cPerm m k hk hkm)) (n := k - 1) (m := n)
          (by rw [hGlen]; exact hn)]
        rw [hGlen]
        simp [L, List.getElem?_map, List.getElem?_ofFn, hmodlt]
      rw [hmapF, hrotn]
      congr 1
      have hn_cases : n = 0 ∨ n = k - 1 ∨ (1 ≤ n ∧ n ≤ k - 2) := by omega
      rcases hn_cases with rfl | rfl | ⟨hn1, hn2⟩
      · have hidx : (0 + (k - 1)) % k = k - 1 := by
          rw [Nat.zero_add, Nat.mod_eq_of_lt]; omega
        have hidx_fin : (⟨(0 + (k - 1)) % k, by omega⟩ : Fin k) = ⟨k - 1, by omega⟩ := by
          apply Fin.ext; simpa using hidx
        rw [hidx_fin, cPerm_apply_last]
        show (sigmaPerm m k hk hkm * tauOne m k hk hkm) (emb hk_le ⟨0, hn⟩) = ⟨k - 1, by omega⟩
        rw [show emb hk_le ⟨0, hn⟩ = (⟨0, by omega⟩ : Fin m) from rfl]
        exact eval_zero hk hkm
      · have hidx : (k - 1 + (k - 1)) % k = k - 2 := by
          rw [show k - 1 + (k - 1) = (k - 2) + k from by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt]
          omega
        have hidx_fin : (⟨(k - 1 + (k - 1)) % k, by omega⟩ : Fin k) = ⟨k - 2, by omega⟩ := by
          apply Fin.ext; simpa using hidx
        rw [hidx_fin]
        have hstep := cPerm_apply_step (hk := hk) (hkm := hkm) (⟨k - 2, by omega⟩ : Fin k) (by simp; omega)
        rw [hstep]
        have hidx2 : (⟨k - 2 + 1, by omega⟩ : Fin k) = ⟨k - 1, by omega⟩ := by
          apply Fin.ext
          show k - 2 + 1 = k - 1
          omega
        rw [hidx2, show tauOne m k hk hkm (emb hk_le ⟨k - 1, by omega⟩) = ⟨m - 1, by omega⟩ from by
          rw [show emb hk_le ⟨k - 1, by omega⟩ = (⟨k - 1, by omega⟩ : Fin m) from rfl]
          exact tauOne_apply_k1 hk hkm]
        show (sigmaPerm m k hk hkm * tauOne m k hk hkm) (emb hk_le ⟨k - 1, hn⟩) = ⟨m - 1, by omega⟩
        rw [show emb hk_le ⟨k - 1, hn⟩ = (⟨k - 1, by omega⟩ : Fin m) from rfl]
        exact eval_last hk hkm
      · have hidx : (n + (k - 1)) % k = n - 1 := by
          rw [show n + (k - 1) = (n - 1) + k from by omega, Nat.add_mod_right, Nat.mod_eq_of_lt]
          omega
        have hidx_fin : (⟨(n + (k - 1)) % k, by omega⟩ : Fin k) = ⟨n - 1, by omega⟩ := by
          apply Fin.ext; simpa using hidx
        rw [hidx_fin]
        have hstep := cPerm_apply_step (hk := hk) (hkm := hkm) (⟨n - 1, by omega⟩ : Fin k) (by simp; omega)
        rw [hstep]
        have hidx2 : (⟨n - 1 + 1, by omega⟩ : Fin k) = ⟨n, by omega⟩ := by
          apply Fin.ext; simp; omega
        rw [hidx2]
        have hτn : tauOne m k hk hkm (emb hk_le ⟨n, by omega⟩) = emb hk_le ⟨n, by omega⟩ := by
          apply tauOne_apply_of_ne hk hkm
          · intro h; have := congrArg Fin.val h; simp only [emb, Fin.val_mk] at this; omega
          · intro h; have := congrArg Fin.val h; simp only [emb, Fin.val_mk] at this; omega
        rw [hτn]
        exact eval_mid hk hkm n hn1 hn2
    · have hFnone : (L.map (sigmaPerm m k hk hkm * tauOne m k hk hkm))[n]? = none := by
        rw [List.getElem?_eq_none]; simp [L]; omega
      have hRnone : ((L.map (cPerm m k hk hkm)).rotate (k - 1))[n]? = none := by
        rw [List.getElem?_eq_none]; simp [L]; omega
      rw [hFnone, hRnone]
  have hformEq : (L.map (sigmaPerm m k hk hkm * tauOne m k hk hkm)).formPerm =
      (L.map (cPerm m k hk hkm)).formPerm := by
    apply List.formPerm_eq_of_isRotated
    · exact hndL.map (Equiv.injective _)
    · exact List.IsRotated.symm ⟨k - 1, hrot.symm⟩
  have hLHS : sigmaPerm m k hk hkm * cPerm m k hk hkm * sigmaPerm m k hk hkm =
      (L.map (sigmaPerm m k hk hkm * tauOne m k hk hkm)).formPerm := by
    have hinv : (sigmaPerm m k hk hkm * tauOne m k hk hkm)⁻¹ =
        tauOne m k hk hkm * sigmaPerm m k hk hkm := by
      apply inv_eq_of_mul_eq_one_right
      calc sigmaPerm m k hk hkm * tauOne m k hk hkm * (tauOne m k hk hkm * sigmaPerm m k hk hkm)
          = sigmaPerm m k hk hkm * (tauOne m k hk hkm * tauOne m k hk hkm) * sigmaPerm m k hk hkm := by group
        _ = 1 := by rw [tauOne_mul_self, mul_one, sigma_invol]
    calc sigmaPerm m k hk hkm * cPerm m k hk hkm * sigmaPerm m k hk hkm
        = (sigmaPerm m k hk hkm * tauOne m k hk hkm) * kCycle m k (by omega) *
            (sigmaPerm m k hk hkm * tauOne m k hk hkm)⁻¹ := by
          unfold cPerm
          rw [hinv]
          group
      _ = (L.map (sigmaPerm m k hk hkm * tauOne m k hk hkm)).formPerm := by
          rw [hc, conj_formPerm]
  have hRHS : cPerm m k hk hkm * kCycle m k (by omega) * (cPerm m k hk hkm)⁻¹ =
      (L.map (cPerm m k hk hkm)).formPerm := by
    rw [hc, conj_formPerm]
  rw [hLHS, hRHS, hformEq]

/-- **Lemma 6** (arXiv:1210.1550, p.21).  Let `α` be an element of the alternating
group `Aₘ` (`m ≥ 6`) lying in a conjugacy class with at least four fixed points —
taken to be the last four points `m−4, m−3, m−2, m−1` — and having a `k`-cycle
`(0 1 ⋯ k−1)` with `k ≥ 2` (necessarily `k + 4 ≤ m`).  Then the equation

`y = α^{(0 k−1)(m−4 m−3) · y}`,  i.e.  `y = (σ y) α (σ y)⁻¹`

with `σ = (0 k−1)(m−4 m−3)` and the paper's conjugation convention `x^g = g x g⁻¹`,
has at least two solutions `y ∈ Aₘ`.

The two solutions are the ones exhibited by the paper's proof: conjugates of `α` by
`(k−1, m−1)` and by `(k−1, m−2)` (zero-based for the paper's `(k, m)` and
`(k, m−1)`), i.e. the elements of `Aₘ` agreeing with `α` except that the `k`-cycle
`(0 1 ⋯ k−1)` is replaced by `(0 1 ⋯ k−2, m−1)` respectively `(0 1 ⋯ k−2, m−2)`.
Both conjugates lie in `Aₘ` because `Aₘ` is normal. -/
theorem lemma6_two_solutions
    (m k : ℕ) (hk : 2 ≤ k) (hkm : k + 4 ≤ m)
    (α : ↥(alternatingGroup (Fin m)))
    (hαk : ∀ i : Fin m, i.val < k →
      (α : Equiv.Perm (Fin m)) i = kCycle m k (by omega) i)
    (hfix : ∀ i : Fin m, m - 4 ≤ i.val → (α : Equiv.Perm (Fin m)) i = i) :
    ∃ y₁ y₂ : ↥(alternatingGroup (Fin m)), y₁ ≠ y₂ ∧
      (y₁ : Equiv.Perm (Fin m)) =
        sigmaPerm m k hk hkm * (y₁ : Equiv.Perm (Fin m)) * (α : Equiv.Perm (Fin m)) *
          (sigmaPerm m k hk hkm * (y₁ : Equiv.Perm (Fin m)))⁻¹ ∧
      (y₂ : Equiv.Perm (Fin m)) =
        sigmaPerm m k hk hkm * (y₂ : Equiv.Perm (Fin m)) * (α : Equiv.Perm (Fin m)) *
          (sigmaPerm m k hk hkm * (y₂ : Equiv.Perm (Fin m)))⁻¹ := by
  classical
  let P : Equiv.Perm (Fin m) := (α : Equiv.Perm (Fin m))
  let c : Equiv.Perm (Fin m) := kCycle m k (by omega)
  let β : Equiv.Perm (Fin m) := c⁻¹ * P
  let σ : Equiv.Perm (Fin m) := sigmaPerm m k hk hkm
  let τ₁ : Equiv.Perm (Fin m) := tauOne m k hk hkm
  let τ₂ : Equiv.Perm (Fin m) := tauTwo m k hk hkm
  let ρ : Equiv.Perm (Fin m) := Equiv.swap ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩
  let y₁p : Equiv.Perm (Fin m) := τ₁ * P * τ₁
  let y₂p : Equiv.Perm (Fin m) := τ₂ * P * τ₂
  have hP : P = c * β := by
    simp only [β]
    group
  have hβ_first : ∀ i : Fin m, i.val < k → β i = i := by
    intro i hi
    have hPi : P i = c i := hαk i hi
    simp only [β, Equiv.Perm.mul_apply]
    rw [hPi]
    simp
  have hβ_last : ∀ i : Fin m, m - 4 ≤ i.val → β i = i := by
    intro i hi
    have hPi : P i = i := hfix i hi
    have hci : c i = i := kc_ge (by omega : k ≤ m) i (by omega)
    simp only [β, Equiv.Perm.mul_apply]
    rw [hPi]
    exact Equiv.Perm.inv_eq_iff_eq.mpr hci.symm
  -- generic commutation criterion for permutations of `Fin m`
  have hpres : ∀ (f : Equiv.Perm (Fin m)) (S : Set (Fin m)),
      (∀ x, x ∈ S → f x = x) → ∀ x, x ∉ S → f x ∉ S := by
    intro f S hf x hx hmem
    have h1 : f (f x) = f x := hf (f x) hmem
    have h2 : f x = x := f.injective h1
    exact hx (h2 ▸ hmem)
  have hcomm : ∀ (S : Set (Fin m)) (f g : Equiv.Perm (Fin m)),
      (∀ x, x ∈ S → f x = x) → (∀ x, x ∉ S → g x = x) → f * g = g * f := by
    intro S f g hf hg
    have hfS : ∀ x, x ∉ S → f x ∉ S := hpres f S hf
    have hgS : ∀ x, x ∈ S → g x ∈ S := by
      intro x hx
      by_contra hmem
      have h1 : g (g x) = g x := hg (g x) hmem
      have h2 : g x = x := g.injective h1
      exact (h2 ▸ hmem) hx
    ext x
    by_cases hx : x ∈ S
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hf (g x) (hgS x hx), hf x hx]
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hg x hx, hg (f x) (hfS x hx)]
  let S : Set (Fin m) := {x | x.val < k ∨ m - 4 ≤ x.val}
  have hS_compl : ∀ x : Fin m, x ∉ S → k ≤ x.val ∧ x.val < m - 4 := by
    intro x hx
    have h : ¬ (x.val < k ∨ m - 4 ≤ x.val) := by simpa [S] using hx
    omega
  have hβ_fixes : ∀ x, x ∈ S → β x = x := by
    intro x hx
    have hx' : x.val < k ∨ m - 4 ≤ x.val := by simpa [S] using hx
    rcases hx' with h | h
    · exact hβ_first x h
    · exact hβ_last x h
  have hc_fixes : ∀ x, x ∉ S → c x = x := by
    intro x hx
    exact kc_ge (by omega : k ≤ m) x (hS_compl x hx).1
  have hc'_fixes : ∀ x, x ∉ S → cPerm m k hk hkm x = x := by
    intro x hx
    exact cPerm_apply_of_mid hk hkm x (hS_compl x hx).1 (hS_compl x hx).2
  have hσ_fixes : ∀ x, x ∉ S → σ x = x := by
    intro x hx
    obtain ⟨h1, h2⟩ := hS_compl x hx
    apply sigma_apply_of_ne hk hkm
    · intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    · intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    · intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    · intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
  have hτ_fixes : ∀ x, x ∉ S → τ₁ x = x := by
    intro x hx
    obtain ⟨h1, h2⟩ := hS_compl x hx
    apply tauOne_apply_of_ne hk hkm
    · intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    · intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
  have hβc : β * c = c * β := hcomm S β c hβ_fixes hc_fixes
  have hβc' : β * cPerm m k hk hkm = cPerm m k hk hkm * β :=
    hcomm S β (cPerm m k hk hkm) hβ_fixes hc'_fixes
  have hβσ : β * σ = σ * β := hcomm S β σ hβ_fixes hσ_fixes
  have hβτ : β * τ₁ = τ₁ * β := hcomm S β τ₁ hβ_fixes hτ_fixes
  have hτ₂ : τ₁ * τ₁ = 1 := tauOne_mul_self hk hkm
  have hτβ : τ₁ * β * τ₁ = β := by
    calc τ₁ * β * τ₁ = β * τ₁ * τ₁ := by rw [← hβτ]
      _ = β * (τ₁ * τ₁) := by group
      _ = β := by rw [hτ₂, mul_one]
  have hy₁ : y₁p = cPerm m k hk hkm * β := by
    simp only [y₁p]
    calc τ₁ * P * τ₁ = τ₁ * (c * β) * τ₁ := by rw [hP]
      _ = τ₁ * c * (β * τ₁) := by group
      _ = τ₁ * c * (τ₁ * β) := by rw [hβτ]
      _ = (τ₁ * c * τ₁) * β := by group
      _ = cPerm m k hk hkm * β := rfl
  have hσ2 : σ * σ = 1 := sigma_invol hk hkm
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  have hA : σ * cPerm m k hk hkm * σ =
      cPerm m k hk hkm * c * (cPerm m k hk hkm)⁻¹ := sigma_conj_cPerm hk hkm
  have hkey : σ * cPerm m k hk hkm * c * (cPerm m k hk hkm)⁻¹ * σ =
      cPerm m k hk hkm := by
    calc σ * cPerm m k hk hkm * c * (cPerm m k hk hkm)⁻¹ * σ
        = σ * (cPerm m k hk hkm * c * (cPerm m k hk hkm)⁻¹) * σ := by group
      _ = σ * (σ * cPerm m k hk hkm * σ) * σ := by rw [← hA]
      _ = cPerm m k hk hkm := by
          rw [show σ * (σ * cPerm m k hk hkm * σ) * σ =
              (σ * σ) * cPerm m k hk hkm * (σ * σ) from by group, hσ2]
          group
  have hβc'inv : β * (cPerm m k hk hkm)⁻¹ = (cPerm m k hk hkm)⁻¹ * β := by
    calc β * (cPerm m k hk hkm)⁻¹
        = (cPerm m k hk hkm)⁻¹ * (cPerm m k hk hkm * β) * (cPerm m k hk hkm)⁻¹ := by group
      _ = (cPerm m k hk hkm)⁻¹ * (β * cPerm m k hk hkm) * (cPerm m k hk hkm)⁻¹ := by rw [← hβc']
      _ = (cPerm m k hk hkm)⁻¹ * β := by group
  have hy₁_solves : σ * y₁p * P * (σ * y₁p)⁻¹ = y₁p := by
    rw [hy₁, hP]
    calc σ * (cPerm m k hk hkm * β) * (c * β) * (σ * (cPerm m k hk hkm * β))⁻¹
        = σ * cPerm m k hk hkm * β * c * β * (β⁻¹ * (cPerm m k hk hkm)⁻¹ * σ) := by
            simp only [mul_inv_rev, hσinv]
            group
      _ = σ * cPerm m k hk hkm * β * c * (cPerm m k hk hkm)⁻¹ * σ := by group
      _ = σ * cPerm m k hk hkm * (β * c) * (cPerm m k hk hkm)⁻¹ * σ := by group
      _ = σ * cPerm m k hk hkm * (c * β) * (cPerm m k hk hkm)⁻¹ * σ := by rw [hβc]
      _ = σ * cPerm m k hk hkm * c * (β * (cPerm m k hk hkm)⁻¹) * σ := by group
      _ = σ * cPerm m k hk hkm * c * ((cPerm m k hk hkm)⁻¹ * β) * σ := by rw [hβc'inv]
      _ = σ * cPerm m k hk hkm * c * (cPerm m k hk hkm)⁻¹ * (β * σ) := by group
      _ = σ * cPerm m k hk hkm * c * (cPerm m k hk hkm)⁻¹ * (σ * β) := by rw [hβσ]
      _ = (σ * cPerm m k hk hkm * c * (cPerm m k hk hkm)⁻¹ * σ) * β := by group
      _ = cPerm m k hk hkm * β := by rw [hkey]
  have hy₁_mem : y₁p ∈ alternatingGroup (Fin m) := by
    have hPmem : P ∈ alternatingGroup (Fin m) := α.2
    have hτinv : τ₁⁻¹ = τ₁ := inv_eq_of_mul_eq_one_right hτ₂
    have hy₁_eq : y₁p = τ₁ * P * τ₁⁻¹ := by
      simp only [y₁p]
      rw [hτinv]
    haveI hAnorm : (alternatingGroup (Fin m)).Normal := inferInstance
    have hconj := hAnorm.conj_mem P hPmem τ₁
    rwa [← hy₁_eq] at hconj
  -- the auxiliary transposition ρ = (m−2, m−1)
  have hρ2 : ρ * ρ = 1 := by
    simp only [ρ]
    exact Equiv.swap_mul_self _ _
  let S₂ : Set (Fin m) := {x | x = ⟨m - 2, by omega⟩ ∨ x = ⟨m - 1, by omega⟩}
  have hP_fixes₂ : ∀ x, x ∈ S₂ → P x = x := by
    intro x hx
    have hx' : x = ⟨m - 2, by omega⟩ ∨ x = ⟨m - 1, by omega⟩ := by simpa [S₂] using hx
    rcases hx' with rfl | rfl
    · exact hfix _ (by simp only [Fin.val_mk]; omega)
    · exact hfix _ (by simp only [Fin.val_mk]; omega)
  have hρ_fixes₂ : ∀ x, x ∉ S₂ → ρ x = x := by
    intro x hx
    have hx' : x ≠ ⟨m - 2, by omega⟩ ∧ x ≠ ⟨m - 1, by omega⟩ := by
      have h : ¬ (x = ⟨m - 2, by omega⟩ ∨ x = ⟨m - 1, by omega⟩) := by simpa [S₂] using hx
      exact not_or.mp h
    simp only [ρ]
    exact Equiv.swap_apply_of_ne_of_ne hx'.1 hx'.2
  have hρP : ρ * P = P * ρ := (hcomm S₂ P ρ hP_fixes₂ hρ_fixes₂).symm
  have hσ_fixes₂ : ∀ x, x ∈ S₂ → σ x = x := by
    intro x hx
    have hx' : x = ⟨m - 2, by omega⟩ ∨ x = ⟨m - 1, by omega⟩ := by simpa [S₂] using hx
    rcases hx' with rfl | rfl
    · exact sigma_apply_m2 hk hkm
    · exact sigma_apply_m1 hk hkm
  have hρσ : ρ * σ = σ * ρ := (hcomm S₂ σ ρ hσ_fixes₂ hρ_fixes₂).symm
  have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ2
  have hρτ₁ : ρ * τ₁ * ρ = τ₂ := by
    calc ρ * τ₁ * ρ = ρ * τ₁ * ρ⁻¹ := by rw [hρinv]
      _ = Equiv.swap (ρ (⟨k - 1, by omega⟩ : Fin m)) (ρ (⟨m - 1, by omega⟩ : Fin m)) := by
            rw [show τ₁ = Equiv.swap (⟨k - 1, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ from rfl]
            exact (Equiv.swap_apply_apply ρ _ _).symm
      _ = Equiv.swap (⟨k - 1, by omega⟩ : Fin m) ⟨m - 2, by omega⟩ := by
            have h1 : ρ (⟨k - 1, by omega⟩ : Fin m) = ⟨k - 1, by omega⟩ := by
              simp only [ρ]
              apply Equiv.swap_apply_of_ne_of_ne <;>
                intro h <;> (have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)
            have h2 : ρ (⟨m - 1, by omega⟩ : Fin m) = ⟨m - 2, by omega⟩ := by
              simp only [ρ]
              exact Equiv.swap_apply_right _ _
            rw [h1, h2]
      _ = τ₂ := by
            simp only [τ₂, tauTwo]
  have hy₂p_eq : y₂p = ρ * y₁p * ρ := by
    simp only [y₁p, y₂p]
    calc τ₂ * P * τ₂ = (ρ * τ₁ * ρ) * P * (ρ * τ₁ * ρ) := by rw [hρτ₁]
      _ = ρ * τ₁ * (ρ * P) * ρ * τ₁ * ρ := by group
      _ = ρ * τ₁ * (P * ρ) * ρ * τ₁ * ρ := by rw [hρP]
      _ = ρ * τ₁ * P * (ρ * ρ) * τ₁ * ρ := by group
      _ = ρ * τ₁ * P * τ₁ * ρ := by rw [hρ2]; group
      _ = ρ * (τ₁ * P * τ₁) * ρ := by group
  have hρσρ : ρ * σ * ρ = σ := by
    calc ρ * σ * ρ = (σ * ρ) * ρ := by rw [hρσ]
      _ = σ * (ρ * ρ) := by group
      _ = σ := by rw [hρ2, mul_one]
  have hρPρ : ρ * P * ρ = P := by
    calc ρ * P * ρ = (P * ρ) * ρ := by rw [hρP]
      _ = P * (ρ * ρ) := by group
      _ = P := by rw [hρ2, mul_one]
  have hleft : ρ * (σ * (ρ * y₁p * ρ) * P * (σ * (ρ * y₁p * ρ))⁻¹) * ρ = y₁p := by
    calc ρ * (σ * (ρ * y₁p * ρ) * P * (σ * (ρ * y₁p * ρ))⁻¹) * ρ
        = (ρ * σ * ρ) * y₁p * (ρ * P * ρ) * y₁p⁻¹ * (ρ * σ * ρ) := by
            simp only [mul_inv_rev, hσinv, hρinv]
            group
      _ = σ * y₁p * P * y₁p⁻¹ * σ := by rw [hρσρ, hρPρ]
      _ = σ * y₁p * P * (σ * y₁p)⁻¹ := by
            simp only [mul_inv_rev, hσinv]
            group
      _ = y₁p := hy₁_solves
  have hright : ρ * (ρ * y₁p * ρ) * ρ = y₁p := by
    calc ρ * (ρ * y₁p * ρ) * ρ = (ρ * ρ) * y₁p * (ρ * ρ) := by group
      _ = y₁p := by rw [hρ2]; group
  have hcancel : ρ * (σ * (ρ * y₁p * ρ) * P * (σ * (ρ * y₁p * ρ))⁻¹) * ρ =
      ρ * (ρ * y₁p * ρ) * ρ := by
    rw [hleft, hright]
  have hcancel' : ρ * ((σ * (ρ * y₁p * ρ) * P * (σ * (ρ * y₁p * ρ))⁻¹) * ρ) =
      ρ * ((ρ * y₁p * ρ) * ρ) := by
    rw [← mul_assoc, ← mul_assoc]
    exact hcancel
  have hstep1 : (σ * (ρ * y₁p * ρ) * P * (σ * (ρ * y₁p * ρ))⁻¹) * ρ =
      (ρ * y₁p * ρ) * ρ := mul_left_cancel hcancel'
  have hy₂_solves' : σ * (ρ * y₁p * ρ) * P * (σ * (ρ * y₁p * ρ))⁻¹ = ρ * y₁p * ρ :=
    mul_right_cancel hstep1
  have hy₂_solves : σ * y₂p * P * (σ * y₂p)⁻¹ = y₂p := by
    rw [hy₂p_eq]
    exact hy₂_solves'
  have hy₂_mem : y₂p ∈ alternatingGroup (Fin m) := by
    have hPmem : P ∈ alternatingGroup (Fin m) := α.2
    have hτ₂' : τ₂ * τ₂ = 1 := tauTwo_mul_self hk hkm
    have hτinv : τ₂⁻¹ = τ₂ := inv_eq_of_mul_eq_one_right hτ₂'
    have hy₂_eq : y₂p = τ₂ * P * τ₂⁻¹ := by
      simp only [y₂p]
      rw [hτinv]
    haveI hAnorm : (alternatingGroup (Fin m)).Normal := inferInstance
    have hconj := hAnorm.conj_mem P hPmem τ₂
    rwa [← hy₂_eq] at hconj
  have hy₁_at : y₁p (⟨m - 1, by omega⟩ : Fin m) = ⟨0, by omega⟩ := by
    simp only [y₁p, Equiv.Perm.mul_apply]
    rw [show τ₁ (⟨m - 1, by omega⟩ : Fin m) = ⟨k - 1, by omega⟩ from tauOne_apply_m1 hk hkm]
    rw [show P (⟨k - 1, by omega⟩ : Fin m) = c (⟨k - 1, by omega⟩ : Fin m) from
      hαk _ (by simp only [Fin.val_mk]; omega)]
    rw [show c (⟨k - 1, by omega⟩ : Fin m) = ⟨0, by omega⟩ from kc_last hk (by omega)]
    apply tauOne_apply_of_ne hk hkm
    · intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    · intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
  have hy₂_at : y₂p (⟨m - 1, by omega⟩ : Fin m) = ⟨m - 1, by omega⟩ := by
    simp only [y₂p, Equiv.Perm.mul_apply]
    rw [show τ₂ (⟨m - 1, by omega⟩ : Fin m) = ⟨m - 1, by omega⟩ from by
      apply tauTwo_apply_of_ne hk hkm
      · intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
      · intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega]
    rw [show P (⟨m - 1, by omega⟩ : Fin m) = ⟨m - 1, by omega⟩ from
      hfix _ (by simp only [Fin.val_mk]; omega)]
    apply tauTwo_apply_of_ne hk hkm
    · intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    · intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
  have hy_ne : y₁p ≠ y₂p := by
    intro h
    have h1 : y₁p (⟨m - 1, by omega⟩ : Fin m) = y₂p (⟨m - 1, by omega⟩ : Fin m) := by rw [h]
    rw [hy₁_at, hy₂_at] at h1
    have h2 := congrArg Fin.val h1
    simp only [Fin.val_mk] at h2
    omega
  refine ⟨⟨y₁p, hy₁_mem⟩, ⟨y₂p, hy₂_mem⟩, ?_, ?_, ?_⟩
  · intro h
    exact hy_ne (congrArg Subtype.val h)
  · simpa only [P, σ] using hy₁_solves.symm
  · simpa only [P, σ] using hy₂_solves.symm

end Qatlib.Papers.LinkInvQFT12.MainResults
