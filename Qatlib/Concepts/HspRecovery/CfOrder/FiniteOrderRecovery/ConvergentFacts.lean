/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Qatlib.Concepts.HspRecovery.CfOrder.FiniteOrderRecovery.ConvergentBridge

/-!
# Structural facts for finite continued fractions

Proves positivity, ordering, and endpoint formulas for the continued fraction denominator list
`cfDenoms`. For exact sampling peaks `j = s * M` with `Q = r * M`, the module characterizes
occurrence of the order and counts the successful peak indices.

The integer discrepancy `pairD` supports quantitative bounds on convergents and an obstruction
for moduli that are powers of two. These results analyze continued fraction postprocessing in
order finding [Shor1997].

## Main statements

* `cfDenoms_pairwise`: proves strict increase of the filtered denominator list.
* `d1_peak_iff`: characterizes order membership by coprimality.
* `two_c_D1`: counts order-containing peaks by the totient.
* `two_b_corollary`: excludes specified orders from all denominator candidates.

## References

* [Shor, 1997][Shor1997]
-/

set_option autoImplicit false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.CfOrder.FiniteOrderRecovery

open Finset

/-- Strict increase of the second coordinates of a pair list implies strict increase of the list
obtained by mapping `Prod.snd`. -/
theorem pairwise_map_snd : ∀ (L : List (ℕ × ℕ)),
    L.Pairwise (fun x y => x.2 < y.2) → (L.map Prod.snd).Pairwise (· < ·) := by
  intro L
  induction L with
  | nil => intro _; exact List.Pairwise.nil
  | cons a l ih =>
    intro hw
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hw
    refine List.Pairwise.cons ?_ (ih htail)
    intro y' hy'
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hy'
    exact hhead y hy

/-- In a nonempty list with strictly increasing second coordinates, every second coordinate is
at most that of the last pair. -/
theorem pairwise_le_last : ∀ (L : List (ℕ × ℕ)) (hne : L ≠ []),
    L.Pairwise (fun x y => x.2 < y.2) →
    ∀ x ∈ L, x.2 ≤ (L.getLast hne).2 := by
  intro L
  induction L with
  | nil => intro hne; exact absurd rfl hne
  | cons a l ih =>
    intro hne hw x hx
    match l with
    | [] =>
      have hx' : x = a := (List.mem_singleton.mp hx)
      subst hx'
      exact Nat.le_refl _
    | b :: l' =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hw
      have hlast : (a :: b :: l').getLast hne
          = (b :: l').getLast (List.cons_ne_nil _ _) :=
        List.getLast_cons (List.cons_ne_nil _ _)
      rcases List.mem_cons.mp hx with rfl | hx
      · have hb : b ∈ (b :: l') := List.mem_cons_self
        have hab := hhead b hb
        have hbl : b.2 ≤ ((b :: l').getLast (List.cons_ne_nil _ _)).2 :=
          ih (List.cons_ne_nil _ _) htail b hb
        rw [hlast]
        omega
      · rw [hlast]
        exact ih (List.cons_ne_nil _ _) htail x hx

/-- If the initial denominator is smaller than the numerator, every generated partial quotient
is at least one. -/
theorem cfPartialsAux_tail_pos : ∀ (fuel num den : ℕ), den < num →
    ∀ a ∈ cfPartialsAux fuel num den, 1 ≤ a := by
  intro fuel
  induction fuel with
  | zero => intro num den _ a ha; cases ha
  | succ k ih =>
    intro num den hden a ha
    rcases den with _ | d
    · simp only [cfPartialsAux] at ha; cases ha
    · simp only [cfPartialsAux] at ha
      rcases List.mem_cons.mp ha with hhead | htail
      · subst hhead
        exact (Nat.one_le_div_iff (Nat.succ_pos d)).mpr (by omega)
      · exact ih (d + 1) (num % (d + 1)) (Nat.mod_lt _ (Nat.succ_pos d)) a htail

/-- Positive fuel and a positive denominator produce a nonempty partial quotient list. -/
theorem cfPartialsAux_ne_nil {fuel num den : ℕ} (hd : 0 < den) (hf : 0 < fuel) :
    cfPartialsAux fuel num den ≠ [] := by
  match fuel, den, hf, hd with
  | (k + 1), (d + 1), _, _ => intro h; simp [cfPartialsAux] at h
  | 0, _, hf0, _ => omega

/-- Positive partial quotients and positive initial denominators give strictly increasing
convergent denominators, all larger than the second initial denominator. -/
theorem convPairs_warm : ∀ (as : List ℕ), (∀ a ∈ as, 1 ≤ a) →
    ∀ (p2 p1 : ℕ × ℕ), 1 ≤ p2.2 → 1 ≤ p1.2 →
    (convPairs as p2 p1).Pairwise (fun x y => x.2 < y.2)
      ∧ ∀ y ∈ convPairs as p2 p1, p1.2 < y.2 := by
  intro as
  induction as with
  | nil => intro _ p2 p1 _ _; exact ⟨List.Pairwise.nil, by simp [convPairs]⟩
  | cons a rest ih =>
    intro hpos p2 p1 h2 h1
    have ha : 1 ≤ a := hpos a List.mem_cons_self
    have hrest : ∀ x ∈ rest, 1 ≤ x := fun x hx => hpos x (List.mem_cons_of_mem _ hx)
    have hP2 : 1 ≤ a * p1.2 + p2.2 := by nlinarith
    obtain ⟨sorted, lower⟩ := ih hrest p1 (a * p1.1 + p2.1, a * p1.2 + p2.2) h1 hP2
    simp only [convPairs]
    constructor
    · exact List.Pairwise.cons (fun y hy => lower y hy) sorted
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · dsimp only
      have hmul : 1 * p1.2 ≤ a * p1.2 := Nat.mul_le_mul ha (Nat.le_refl _)
      simp only [Nat.one_mul] at hmul
      omega
    · have h1' := lower y hy
      dsimp only at h1'
      have hkey : p1.2 ≤ a * p1.2 + p2.2 := by
        have hmul : 1 * p1.2 ≤ a * p1.2 := Nat.mul_le_mul ha (Nat.le_refl _)
        simp only [Nat.one_mul] at hmul
        omega
      omega

/-- With positive denominator and fuel at least `den + 1`, the last convergent pair is the
linear combination of the initial pairs with coefficients `num / gcd num den` and `den / gcd
num den`. -/
theorem lastConv_linear : ∀ (den : ℕ), ∀ (num fuel : ℕ), 0 < den → den + 1 ≤ fuel →
    ∀ p2 p1 : ℕ × ℕ,
    (convPairs (cfPartialsAux fuel num den) p2 p1).getLast? =
      some ((num / Nat.gcd num den) * p1.1 + (den / Nat.gcd num den) * p2.1,
            (num / Nat.gcd num den) * p1.2 + (den / Nat.gcd num den) * p2.2) := by
  intro den
  induction den using Nat.strongRecOn with
  | ind den ih =>
    intro num fuel hden hfuel p2 p1
    rcases fuel with _ | k
    · omega
    rcases den with _ | d
    · omega
    have hdpos : (0 : ℕ) < d + 1 := Nat.succ_pos d
    by_cases hmod : num % (d + 1) = 0
    · have htail : cfPartialsAux k (d + 1) 0 = [] := by
        match k with
        | 0 => rfl
        | (k' + 1) => rfl
      have hgcd : Nat.gcd num (d + 1) = d + 1 :=
        Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero hmod)
      have hd1 : num / Nat.gcd num (d + 1) = num / (d + 1) := by rw [hgcd]
      have hd2 : (d + 1) / Nat.gcd num (d + 1) = 1 := by
        rw [hgcd, Nat.div_self hdpos]
      simp only [cfPartialsAux, hmod, htail, convPairs, hd1, hd2, one_mul]
      rfl
    · rcases hρ : num % (d + 1) with _ | r
      · omega
      have hr : num % (d + 1) = r + 1 := hρ
      have hmodlt := Nat.mod_lt num hdpos
      have hρlt : r + 1 < d + 1 := by omega
      have hkpos : 0 < k := by omega
      have htailne : cfPartialsAux k (d + 1) (r + 1) ≠ [] :=
        cfPartialsAux_ne_nil (Nat.succ_pos r) hkpos
      have hconvne : convPairs (cfPartialsAux k (d + 1) (r + 1)) p1
          ((num / (d + 1)) * p1.1 + p2.1, (num / (d + 1)) * p1.2 + p2.2) ≠ [] := by
        cases hlist : cfPartialsAux k (d + 1) (r + 1) with
        | nil => exact absurd hlist htailne
        | cons a as => intro h; simp [convPairs] at h
      have hfuel' : (r + 1) + 1 ≤ k := by omega
      have IH := ih (r + 1) hρlt (d + 1) k (Nat.succ_pos r) hfuel' p1
        ((num / (d + 1)) * p1.1 + p2.1, (num / (d + 1)) * p1.2 + p2.2)
      have hgcd : Nat.gcd num (d + 1) = Nat.gcd (d + 1) (r + 1) := by
        rw [Nat.gcd_comm, Nat.gcd_rec, hr, Nat.gcd_comm]
      simp only [cfPartialsAux, convPairs]
      rw [hρ, List.getLast?_cons_of_ne_nil hconvne, IH, hgcd]
      have h0 := Nat.div_add_mod num (d + 1)
      rw [hr, Nat.mul_comm] at h0
      have hnum : num = (num / (d + 1)) * (d + 1) + (r + 1) := by omega
      obtain ⟨D, hD⟩ := Nat.gcd_dvd_left (d + 1) (r + 1)
      obtain ⟨R, hR⟩ := Nat.gcd_dvd_right (d + 1) (r + 1)
      have hgr0 : 0 < Nat.gcd (d + 1) (r + 1) := by
        rcases Nat.eq_zero_or_pos (Nat.gcd (d + 1) (r + 1)) with h0 | h1
        · rw [h0] at hD; simp at hD
        · exact h1
      have hdg : (d + 1) / Nat.gcd (d + 1) (r + 1) = D :=
        Nat.div_eq_of_eq_mul_left hgr0 (hD.trans (Nat.mul_comm _ _))
      have hrg : (r + 1) / Nat.gcd (d + 1) (r + 1) = R :=
        Nat.div_eq_of_eq_mul_left hgr0 (hR.trans (Nat.mul_comm _ _))
      have hnumg : num = Nat.gcd (d + 1) (r + 1) * ((num / (d + 1)) * D + R) := by
        linear_combination (num / (d + 1)) * hD + 1 * hR + 1 * hnum
      have hkey : num / Nat.gcd (d + 1) (r + 1)
          = (num / (d + 1)) * ((d + 1) / Nat.gcd (d + 1) (r + 1))
            + (r + 1) / Nat.gcd (d + 1) (r + 1) := by
        conv_lhs => rw [hnumg]
        rw [Nat.mul_div_cancel_left _ hgr0, hdg, hrg]
      simp only [Option.some.injEq, Prod.mk.injEq]
      constructor
      · rw [hkey]; ring
      · rw [hkey]; ring

/-- If second coordinates increase strictly and `getLast?` returns `P`, every second coordinate
is at most `P.2`. -/
theorem le_last_opt : ∀ (L : List (ℕ × ℕ)) (P : ℕ × ℕ),
    L.Pairwise (fun x y => x.2 < y.2) → L.getLast? = some P → ∀ x ∈ L, x.2 ≤ P.2 := by
  intro L
  induction L with
  | nil => intro P _ hL; simp at hL
  | cons a l ih =>
    intro P hw hL x hx
    cases l with
    | nil =>
      have hPa : a = P := by simpa [List.getLast?_singleton] using hL
      subst hPa
      have hx' : x = a := List.mem_singleton.mp hx
      subst hx'
      omega
    | cons b lt =>
      rw [List.getLast?_cons_of_ne_nil (List.cons_ne_nil _ _)] at hL
      rcases List.mem_cons.mp hx with rfl | hx
      · obtain ⟨hhead, -⟩ := List.pairwise_cons.mp hw
        have hb := hhead b List.mem_cons_self
        have hble := ih P (List.pairwise_cons.mp hw).2 hL b List.mem_cons_self
        omega
      · exact ih P (List.pairwise_cons.mp hw).2 hL x hx

/-- For `0 < j < Q`, the convergent list begins with `(0, 1)` and `(1, a₁)` for positive `a₁`,
followed by a tail with strictly increasing denominators greater than `a₁`. -/
theorem cf_structure (j Q : ℕ) (hj0 : 0 < j) (hj : j < Q) :
    ∃ (a₁ : ℕ) (W : List (ℕ × ℕ)), 1 ≤ a₁
      ∧ convPairs (cfPartials j Q) (0, 1) (1, 0) = (0, 1) :: (1, a₁) :: W
      ∧ W.Pairwise (fun x y => x.2 < y.2)
      ∧ ∀ y ∈ W, a₁ < y.2 := by
  obtain ⟨q, hQ⟩ : ∃ q, Q = q + 1 := ⟨Q - 1, by omega⟩
  subst hQ
  have hunf : cfPartialsAux (q + 1 + 1) j (q + 1)
      = 0 :: cfPartialsAux (q + 1) (q + 1) j := by
    simp only [cfPartialsAux, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]
  have htpos : ∀ a ∈ cfPartialsAux (q + 1) (q + 1) j, 1 ≤ a :=
    cfPartialsAux_tail_pos (q + 1) (q + 1) j hj
  obtain ⟨a₁, rest, htail⟩ : ∃ a₁ rest, cfPartialsAux (q + 1) (q + 1) j = a₁ :: rest :=
    List.exists_cons_of_ne_nil (cfPartialsAux_ne_nil hj0 (Nat.succ_pos q))
  have ha1 : 1 ≤ a₁ := htpos a₁ (htail ▸ List.mem_cons_self)
  have hrestpos : ∀ x ∈ rest, 1 ≤ x := fun x hx =>
    htpos x (htail ▸ List.mem_cons_of_mem _ hx)
  have hw := convPairs_warm rest hrestpos (0, 1) (1, a₁) (Nat.le_refl 1) ha1
  refine ⟨a₁, convPairs rest (0, 1) (1, a₁), ha1, ?_, hw.1, hw.2⟩
  show (convPairs (cfPartialsAux (q + 1 + 1) j (q + 1)) (0, 1) (1, 0)) = _
  rw [hunf, htail]
  simp only [convPairs]
  simp

/-- The filtered continued fraction denominator list for zero numerator is empty. -/
theorem cfDenoms_zero (Q : ℕ) : cfDenoms 0 Q = [] := by
  cases Q with
  | zero => rfl
  | succ q =>
    simp [cfDenoms, cfPartials, cfPartialsAux, convPairs,
      Nat.div_eq_of_lt (Nat.succ_pos q), Nat.mod_eq_of_lt (Nat.succ_pos q)]

/-- Every member of `cfDenoms j Q` is positive. -/
theorem cfDenoms_pos (j Q : ℕ) : ∀ d ∈ cfDenoms j Q, 0 < d := by
  intro d hd
  have h2 : 2 ≤ d := by simpa using (List.mem_filter.mp hd).2
  omega

/-- For `j < Q`, the filtered continued fraction denominator list is strictly increasing. -/
theorem cfDenoms_pairwise (j Q : ℕ) (hj : j < Q) : (cfDenoms j Q).Pairwise (· < ·) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [cfDenoms_zero Q]; exact List.Pairwise.nil
  · obtain ⟨a₁, W, ha1, hfull, hWsort, hWlower⟩ := cf_structure j Q hj0 hj
    have hw2 : ∀ d ∈ W.map Prod.snd, 2 ≤ d := by
      intro d hd
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hd
      have hlt : a₁ < y.2 := hWlower y hy
      omega
    have hfiltW : (W.map Prod.snd).filter (fun d => decide (2 ≤ d)) = W.map Prod.snd :=
      (List.filter_eq_self).mpr (fun d hd => by simpa using show 2 ≤ d from hw2 d hd)
    show (List.filter (fun d => decide (2 ≤ d))
        ((convPairs (cfPartials j Q) (0, 1) (1, 0)).map Prod.snd)).Pairwise (· < ·)
    rw [hfull]
    simp only [List.map_cons]
    rcases Nat.lt_or_ge a₁ 2 with ha1lt | ha1ge
    · have ha1e : a₁ = 1 := by omega
      subst ha1e
      rw [List.filter_cons_of_neg (by simp), List.filter_cons_of_neg (by simp),
        hfiltW]
      exact pairwise_map_snd _ hWsort
    · rw [List.filter_cons_of_neg (by simp),
        List.filter_cons_of_pos (by simpa using ha1ge), hfiltW]
      refine List.Pairwise.cons ?_ (pairwise_map_snd _ hWsort)
      intro d hd
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hd
      exact hWlower y hy

/-- For `0 < j < Q`, the last convergent pair is the reduced fraction `(j / gcd j Q, Q / gcd j
Q)`. -/
theorem cfLast_pair (j Q : ℕ) (hj0 : 0 < j) (hj : j < Q) :
    (convPairs (cfPartials j Q) (0, 1) (1, 0)).getLast?
      = some (j / Nat.gcd j Q, Q / Nat.gcd j Q) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le hj0 (le_of_lt hj)
  have hlin := lastConv_linear Q j (Q + 1) hQ0 (Nat.le_refl _) (0, 1) (1, 0)
  show (convPairs (cfPartialsAux (Q + 1) j Q) (0, 1) (1, 0)).getLast? = _
  rw [hlin]
  simp

/-- For `0 < j < Q`, the reduced denominator `Q / gcd j Q` belongs to `cfDenoms j Q`. -/
theorem cfDenoms_last_mem (j Q : ℕ) (hj0 : 0 < j) (hj : j < Q) :
    Q / Nat.gcd j Q ∈ cfDenoms j Q := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp (cfLast_pair j Q hj0 hj)
  have hmem : (j / Nat.gcd j Q, Q / Nat.gcd j Q)
      ∈ convPairs (cfPartials j Q) (0, 1) (1, 0) := by
    rw [hys]; exact List.mem_append.mpr (Or.inr (by simp))
  have hdens : Q / Nat.gcd j Q ∈ (convPairs (cfPartials j Q) (0, 1) (1, 0)).map Prod.snd :=
    List.mem_map_of_mem hmem
  have hgcdle : Nat.gcd j Q ≤ j := Nat.gcd_le_left _ hj0
  have hg0 : 0 < Nat.gcd j Q := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left j Q) hj0
  have h2 : 2 ≤ Q / Nat.gcd j Q := by
    by_contra hlt
    have hle1 : Q / Nat.gcd j Q ≤ 1 := by omega
    have hdmg : Q / Nat.gcd j Q * Nat.gcd j Q = Q :=
      Nat.div_mul_cancel (Nat.gcd_dvd_right j Q)
    have hmul : Q / Nat.gcd j Q * Nat.gcd j Q ≤ Nat.gcd j Q := by
      have h1 : Q / Nat.gcd j Q * Nat.gcd j Q ≤ 1 * Nat.gcd j Q :=
        Nat.mul_le_mul (by omega) (Nat.le_refl _)
      simpa using h1
    omega
  exact List.mem_filter.mpr ⟨hdens, by simpa using h2⟩

/-- Every filtered convergent denominator for `0 < j < Q` is at most `Q / gcd j Q`. -/
theorem cfDenoms_le_last (j Q : ℕ) (hj0 : 0 < j) (hj : j < Q) :
    ∀ d ∈ cfDenoms j Q, d ≤ Q / Nat.gcd j Q := by
  intro d hd
  obtain ⟨a₁, W, ha1, hfull, hWsort, hWlower⟩ := cf_structure j Q hj0 hj
  have hdens : d ∈ ((0, 1) :: (1, a₁) :: W).map Prod.snd := by
    rw [← hfull]
    exact (List.mem_filter.mp hd).1
  have hLP := cfLast_pair j Q hj0 hj
  rw [hfull] at hLP
  cases W with
  | nil =>
    have hcomp : ((0, 1) :: (1, a₁) :: []).getLast? = some (1, a₁) := by
      rw [List.getLast?_cons_of_ne_nil (by simp)]
      rfl
    rw [hcomp] at hLP
    have ha1g : a₁ = Q / Nat.gcd j Q := by
      have h := congrArg Prod.snd (show (1, a₁) = (j / Nat.gcd j Q, Q / Nat.gcd j Q) by
        simpa using hLP)
      simpa using h
    simp at hdens
    rcases hdens with rfl | rfl
    · omega
    · omega
  | cons w Wt =>
    rw [List.getLast?_cons_of_ne_nil (List.cons_ne_nil _ _),
      List.getLast?_cons_of_ne_nil (List.cons_ne_nil _ _)] at hLP
    have hmain := le_last_opt (w :: Wt) (j / Nat.gcd j Q, Q / Nat.gcd j Q) hWsort hLP
    rcases List.mem_cons.mp hdens with hd1 | hd1
    · have hd1' : d = 1 := hd1
      subst hd1'
      have hw := hWlower w List.mem_cons_self
      have hwle := hmain w List.mem_cons_self
      omega
    · rcases List.mem_cons.mp hd1 with hd2 | hd2
      · have hd2' : d = a₁ := hd2
        subst hd2'
        have hw := hWlower w List.mem_cons_self
        have hwle := hmain w List.mem_cons_self
        omega
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hd2
        have hyle : y.2 ≤ Q / Nat.gcd j Q := hmain y hy
        omega

/-- For `j < Q`, searching the filtered convergent denominators returns `orderOf u` exactly when
that order occurs in the list. -/
theorem d1Find_cfDenoms {G : Type*} [Group G] [Fintype G] [DecidableEq G] (u : G)
    {j Q : ℕ} (hj : j < Q) :
    d1Find u (cfDenoms j Q) = some (orderOf u) ↔ orderOf u ∈ cfDenoms j Q :=
  d1Find_eq_orderOf (cfDenoms_pos j Q) (cfDenoms_pairwise j Q hj)

/-- At an exact peak `j = s * M` with positive `Q = r * M` and `r ≥ 2`, the order `r` occurs
among the denominators exactly when `s` and `r` are coprime. -/
theorem d1_peak_iff (r M Q : ℕ) (hr : 2 ≤ r) (hQM : r * M = Q) (hQ : 0 < Q)
    (s : ℕ) (hs : s < r) :
    (r ∈ cfDenoms (s * M) Q) ↔ Nat.Coprime s r := by
  have hM0 : 0 < M := by
    rcases M with _ | mM
    · rw [Nat.mul_zero] at hQM; omega
    · omega
  rcases s with _ | s
  · rw [Nat.zero_mul, cfDenoms_zero]
    constructor
    · intro hm; cases hm
    · intro hc
      have hg : Nat.gcd 0 r = 1 := hc
      rw [Nat.gcd_zero_left] at hg
      omega
  · have hj0 : 0 < (s + 1) * M := Nat.mul_pos (Nat.succ_pos s) hM0
    have hj : (s + 1) * M < Q := by
      rw [← hQM]; exact (Nat.mul_lt_mul_right hM0).mpr hs
    have hgcd : Nat.gcd ((s + 1) * M) Q = M * Nat.gcd (s + 1) r := by
      rw [← hQM, Nat.mul_comm (s + 1) M, Nat.mul_comm r M]
      exact Nat.gcd_mul_left M (s + 1) r
    have hQg : Q / Nat.gcd ((s + 1) * M) Q = r / Nat.gcd (s + 1) r := by
      rw [hgcd, ← hQM, Nat.mul_comm r M, Nat.mul_div_mul_left _ _ hM0]
    constructor
    · intro hmem
      have hle := cfDenoms_le_last ((s + 1) * M) Q hj0 hj r hmem
      rw [hQg] at hle
      have hg0 : 0 < Nat.gcd (s + 1) r :=
        Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right _ _) (by omega)
      obtain ⟨k, hk⟩ := Nat.gcd_dvd_right (s + 1) r
      have hdiv : r / Nat.gcd (s + 1) r = k :=
        Nat.div_eq_of_eq_mul_right hg0 hk
      rw [hdiv] at hle
      have hg1 : Nat.gcd (s + 1) r = 1 := by
        by_contra hg
        have hg2 : 2 ≤ Nat.gcd (s + 1) r := by
          by_contra h2; omega
        have h2k : 2 * k ≤ Nat.gcd (s + 1) r * k :=
          Nat.mul_le_mul_right k hg2
        rw [← hk] at h2k
        have hk0 : k = 0 := by omega
        rw [hk0, Nat.mul_zero] at hk
        omega
      exact hg1
    · intro hc
      have hg1 : Nat.gcd (s + 1) r = 1 := hc
      have hQg2 : Q / Nat.gcd ((s + 1) * M) Q = r := by
        rw [hQg, hg1, Nat.div_one]
      rw [← hQg2]
      exact cfDenoms_last_mem ((s + 1) * M) Q hj0 hj

/-- For positive `Q = r * M` and `r ≥ 2`, exactly `Nat.totient r` peak indices below `r` have
`r` among their convergent denominators. -/
theorem two_c_D1 (r M Q : ℕ) (hr : 2 ≤ r) (hQM : r * M = Q) (hQ : 0 < Q) :
    ((Finset.range r).filter (fun s => r ∈ cfDenoms (s * M) Q)).card = Nat.totient r := by
  have hf : (Finset.range r).filter (fun s => r ∈ cfDenoms (s * M) Q)
      = (Finset.range r).filter (fun s => s.gcd r = 1) := by
    refine Finset.filter_congr (fun s hs => ?_)
    simp only [Finset.mem_range] at hs
    rw [d1_peak_iff r M Q hr hQM hQ s hs, Nat.Coprime]
  rw [hf]
  have hf2 : (Finset.range r).filter (fun s => s.gcd r = 1)
      = (Finset.range r).filter (fun a => r.gcd a = 1) :=
    Finset.filter_congr (fun s _ => by rw [Nat.gcd_comm])
  rw [hf2]
  rfl

/-- For positive `Q = r * M`, exactly `r - 1` peak indices below `r` have a convergent
denominator dividing `r`. -/
theorem two_c_D2b (r M Q : ℕ) (hQM : r * M = Q) (hQ : 0 < Q) :
    ((Finset.range r).filter (fun s => ∃ d ∈ cfDenoms (s * M) Q, d ∣ r)).card = r - 1 := by
  have hM0 : 0 < M := by
    rcases M with _ | mM
    · rw [Nat.mul_zero] at hQM; omega
    · omega
  have hiff : ∀ s ∈ Finset.range r, (∃ d ∈ cfDenoms (s * M) Q, d ∣ r) ↔ s ≠ 0 := by
    intro s hs
    simp only [Finset.mem_range] at hs
    constructor
    · rintro ⟨d, hd, -⟩ hs0
      rw [hs0, Nat.zero_mul, cfDenoms_zero] at hd
      cases hd
    · intro hs0
      rcases s with _ | s
      · omega
      · refine ⟨Q / Nat.gcd ((s + 1) * M) Q,
          cfDenoms_last_mem ((s + 1) * M) Q
            (Nat.mul_pos (Nat.succ_pos s) hM0)
            (by rw [← hQM]; exact (Nat.mul_lt_mul_right hM0).mpr hs), ?_⟩
        have hgcd : Nat.gcd ((s + 1) * M) Q = M * Nat.gcd (s + 1) r := by
          rw [← hQM, Nat.mul_comm (s + 1) M, Nat.mul_comm r M]
          exact Nat.gcd_mul_left M (s + 1) r
        rw [hgcd, ← hQM, Nat.mul_comm r M, Nat.mul_div_mul_left _ _ hM0]
        exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)
  rw [Finset.filter_congr hiff]
  have hIco : (Finset.range r).filter (fun s => s ≠ 0) = Finset.Ico 1 r := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hIco]
  simp

/-- The integer discrepancy `P.2 * j - P.1 * Q` of a numerator-denominator pair. -/
def pairD (j Q : ℕ) (P : ℕ × ℕ) : ℤ := (P.2 : ℤ) * j - (P.1 : ℤ) * Q

/-- The discrepancy respects the linear recurrence used to form convergent pairs. -/
theorem pairD_linear (j Q a : ℕ) (p2 p1 : ℕ × ℕ) :
    pairD j Q (a * p1.1 + p2.1, a * p1.2 + p2.2)
      = a * pairD j Q p1 + pairD j Q p2 := by
  simp only [pairD]
  push_cast
  ring

/-- Under the signed Euclidean discrepancy identities for the initial pairs, the next
discrepancy is `ε * (num - a * den)`. -/
theorem pairD_head (j Q num den a : ℕ) (p2 p1 : ℕ × ℕ) (ε : ℤ)
    (hd2 : pairD j Q p2 = ε * num) (hd1 : pairD j Q p1 = -ε * den) :
    pairD j Q (a * p1.1 + p2.1, a * p1.2 + p2.2) = ε * ((num : ℤ) - (a : ℤ) * den) := by
  rw [pairD_linear, hd2, hd1]
  ring

/-- Under the signed Euclidean stage invariants and sufficient fuel, every generated pair
satisfies `P.2 * |pairD j Q P| < Q`. -/
theorem stage_bound (j Q : ℕ) : ∀ (den : ℕ), ∀ (num fuel : ℕ) (p2 p1 : ℕ × ℕ) (ε : ℤ),
    0 < den → den + 1 ≤ fuel → 0 < num → 0 < Q → (ε = 1 ∨ ε = -1) →
    pairD j Q p2 = ε * num → pairD j Q p1 = -ε * den →
    num * p1.2 + den * p2.2 = Q →
    ∀ P ∈ convPairs (cfPartialsAux fuel num den) p2 p1,
      P.2 * (pairD j Q P).natAbs < Q := by
  intro den
  induction den using Nat.strongRecOn with
  | ind den ih =>
    intro num fuel p2 p1 ε hd hf hnum hQ hε hd2 hd1 hI3 P hP
    rcases fuel with _ | k
    · omega
    rcases den with _ | d
    · omega
    have hdpos : (0 : ℕ) < d + 1 := Nat.succ_pos d
    by_cases hmod : num % (d + 1) = 0
    · have hmlist : cfPartialsAux k (d + 1) 0 = [] := by
        match k with
        | 0 => rfl
        | (k' + 1) => rfl
      have hlist : convPairs (cfPartialsAux (k + 1) num (d + 1)) p2 p1
          = [(num / (d + 1) * p1.1 + p2.1, num / (d + 1) * p1.2 + p2.2)] := by
        simp only [cfPartialsAux, hmod, hmlist, convPairs]
      rw [hlist] at hP
      have hP' : P = (num / (d + 1) * p1.1 + p2.1, num / (d + 1) * p1.2 + p2.2) :=
        List.mem_singleton.mp hP
      subst hP'
      have hEd0 : num = num / (d + 1) * (d + 1) := by
        have h0 := Nat.div_add_mod num (d + 1)
        rw [hmod, Nat.add_zero, Nat.mul_comm] at h0
        exact h0.symm
      have hd0 : pairD j Q (num / (d + 1) * p1.1 + p2.1, num / (d + 1) * p1.2 + p2.2)
          = 0 := by
        rw [pairD_head j Q num (d + 1) (num / (d + 1)) p2 p1 ε hd2 hd1]
        have hc : ((num : ℕ) : ℤ) = ((num / (d + 1) : ℕ) : ℤ) * ((d + 1 : ℕ) : ℤ) := by
          exact_mod_cast hEd0
        have hEz : ((num : ℤ) - ((num / (d + 1) : ℕ) : ℤ) * ((d + 1 : ℕ) : ℤ)) = 0 := by
          linear_combination hc
        rw [hEz, mul_zero]
      rw [hd0, Int.natAbs_zero, Nat.mul_zero]
      omega
    · obtain ⟨r, hr⟩ : ∃ r, num % (d + 1) = r + 1 := by
        rcases Nat.eq_zero_or_pos (num % (d + 1)) with h0 | h1
        · omega
        · exact ⟨num % (d + 1) - 1, by omega⟩
      have hEd : num = num / (d + 1) * (d + 1) + (r + 1) := by
        have h0 := Nat.div_add_mod num (d + 1)
        rw [hr, Nat.mul_comm] at h0
        exact h0.symm
      have hmodlt : r + 1 < d + 1 := by
        have := Nat.mod_lt num hdpos
        omega

      have hheadbound : (num / (d + 1) * p1.2 + p2.2) * (r + 1) < Q := by
        have hsplit : (num / (d + 1) * p1.2 + p2.2) * (r + 1)
            = num / (d + 1) * (r + 1) * p1.2 + (r + 1) * p2.2 := by ring
        rw [hsplit]
        rcases Nat.eq_zero_or_pos p1.2 with hp1 | hp1
        · have hI3' : (d + 1) * p2.2 = Q := by
            rw [hp1, Nat.mul_zero, Nat.zero_add] at hI3
            exact hI3
          have hp2pos : 0 < p2.2 := by
            rcases Nat.eq_zero_or_pos p2.2 with h0 | h1
            · rw [h0] at hI3'; simp at hI3'; omega
            · exact h1
          rw [hp1, Nat.mul_zero, Nat.zero_add, ← hI3']
          exact (Nat.mul_lt_mul_right hp2pos).mpr hmodlt
        · have harho : num / (d + 1) * (r + 1) < num := by
            have h1 : num / (d + 1) * (r + 1) ≤ num / (d + 1) * (d + 1) :=
              Nat.mul_le_mul_left _ (Nat.le_of_lt hmodlt)
            omega
          have hlt1 : num / (d + 1) * (r + 1) * p1.2 < num * p1.2 :=
            (Nat.mul_lt_mul_right hp1).mpr harho
          have hle2 : (r + 1) * p2.2 ≤ (d + 1) * p2.2 :=
            Nat.mul_le_mul (Nat.le_of_lt hmodlt) (Nat.le_refl _)
          have hsum : num / (d + 1) * (r + 1) * p1.2 + (r + 1) * p2.2
              < num * p1.2 + (d + 1) * p2.2 :=
            Nat.add_lt_add_of_lt_of_le hlt1 hle2
          exact lt_of_lt_of_le hsum (Nat.le_of_eq hI3)

      have hdhead : pairD j Q (num / (d + 1) * p1.1 + p2.1, num / (d + 1) * p1.2 + p2.2)
          = ε * (r + 1) := by
        have hc : ((num : ℕ) : ℤ)
            = ((num / (d + 1) : ℕ) : ℤ) * ((d + 1 : ℕ) : ℤ) + ((r + 1 : ℕ) : ℤ) := by
          exact_mod_cast hEd
        have hEz2 : ((num : ℤ) - ((num / (d + 1) : ℕ) : ℤ) * ((d + 1 : ℕ) : ℤ))
            = ((r + 1 : ℕ) : ℤ) := by
          linear_combination hc
        rw [pairD_head j Q num (d + 1) (num / (d + 1)) p2 p1 ε hd2 hd1, hEz2,
          Nat.cast_succ]

      have hkm1 : 0 < k := by omega
      have hIH := ih (r + 1) hmodlt (d + 1) k p1
        (num / (d + 1) * p1.1 + p2.1, num / (d + 1) * p1.2 + p2.2) (-ε)
        (Nat.succ_pos r) (by omega) hdpos hQ
        (by rcases hε with h | h <;> simp [h])
        (by rw [hd1])
        (by rw [hdhead, neg_neg, Nat.cast_succ])
        (by linear_combination (p1.2 : ℕ) * hEd.symm + 1 * hI3)

      simp only [cfPartialsAux, convPairs] at hP ⊢
      rw [hr] at hP
      rcases List.mem_cons.mp hP with rfl | hPtail
      · show (num / (d + 1) * p1.2 + p2.2) * (pairD j Q
          (num / (d + 1) * p1.1 + p2.1, num / (d + 1) * p1.2 + p2.2)).natAbs < Q
        rw [hdhead]
        have hn1 : (((r : ℤ)) + 1).natAbs = r + 1 := by
          rcases Int.natAbs_eq ((r : ℤ) + 1) with h | h
          · omega
          · have hA : (0 : ℤ) ≤ ((r : ℤ) + 1).natAbs := Int.natCast_nonneg _
            omega
        have hn2 : (-(((r : ℤ)) + 1)).natAbs = r + 1 := by
          rw [Int.natAbs_neg]
          exact hn1
        rcases hε with h | h
        · rw [h, one_mul, hn1]
          exact hheadbound
        · rw [h, Int.neg_mul, one_mul, hn2]
          exact hheadbound
      · exact hIH P hPtail

/-- For `0 < j < Q`, every convergent pair satisfies `P.2 * |pairD j Q P| < Q`. -/
theorem conv_q_bound (j Q : ℕ) (hj0 : 0 < j) (hj : j < Q)
    (P : ℕ × ℕ) (hP : P ∈ convPairs (cfPartials j Q) (0, 1) (1, 0)) :
    P.2 * (pairD j Q P).natAbs < Q := by
  have hQ : 0 < Q := lt_of_lt_of_le hj0 (le_of_lt hj)
  exact stage_bound j Q Q j (Q + 1) (0, 1) (1, 0) 1 hQ (Nat.le_refl _) hj0 hQ (Or.inl rfl)
    (by simp [pairD]) (by simp [pairD]) (by omega) P hP

/-- For `Q = 2 ^ n`, a convergent with nonzero discrepancy and denominator `2 ^ t * m` for odd
`m` satisfies `4 ^ t * m < Q`. -/
theorem two_b (n j Q t m : ℕ) (hQ2 : Q = 2 ^ n) (hm : ¬2 ∣ m)
    (hj0 : 0 < j) (hj : j < Q)
    (P : ℕ × ℕ) (hP : P ∈ convPairs (cfPartials j Q) (0, 1) (1, 0))
    (hd0 : pairD j Q P ≠ 0) (hq : P.2 = 2 ^ t * m) :
    4 ^ t * m < Q := by
  have hb := conv_q_bound j Q hj0 hj P hP
  have h1 : 0 < (pairD j Q P).natAbs := Int.natAbs_pos.mpr hd0
  have hq1 : 0 < m := Nat.pos_of_ne_zero (by intro h0; rw [h0] at hm; simp at hm)
  have h2tq : 2 ^ t ≤ P.2 * (pairD j Q P).natAbs := by
    rw [hq]
    calc 2 ^ t ≤ 2 ^ t * m := Nat.le_mul_of_pos_right _ hq1
    _ ≤ 2 ^ t * m * (pairD j Q P).natAbs := Nat.le_mul_of_pos_right _ h1
  have hq2n : 2 ^ t < 2 ^ n := by rw [← hQ2]; exact lt_of_le_of_lt h2tq hb
  have htn : t ≤ n := by
    by_contra hcon
    have hle : n ≤ t := by omega
    have hle2 := Nat.pow_le_pow_right (Nat.succ_pos 1) hle
    norm_num at hle2
    omega

  have hpown : ((2 ^ t : ℕ) : ℤ) ∣ ((2 ^ n : ℕ) : ℤ) := by
    refine ⟨((2 ^ (n - t) : ℕ) : ℤ), ?_⟩
    have hexp : t + (n - t) = n := by omega
    have hsplit : (2 ^ n : ℕ) = 2 ^ (t + (n - t)) := by rw [hexp]
    conv_lhs => rw [hsplit, Nat.pow_add, Nat.cast_mul]
  have hdvd : ((2 ^ t : ℕ) : ℤ) ∣ pairD j Q P := by
    have hopen : pairD j Q P = ((P.2 : ℕ) : ℤ) * j - ((P.1 : ℕ) : ℤ) * Q := rfl
    rw [hopen, hq, hQ2]
    push_cast
    exact Int.dvd_sub (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_refl _) _) _)
      (dvd_mul_of_dvd_right hpown _)
  obtain ⟨δ, hδ⟩ := hdvd
  have hδ0 : δ ≠ 0 := by
    intro h0
    rw [h0, Int.mul_zero] at hδ
    exact hd0 hδ
  have hδ1 : 0 < δ.natAbs := Int.natAbs_pos.mpr hδ0
  have habs : (pairD j Q P).natAbs = 2 ^ t * δ.natAbs := by
    have hn : ((2 ^ t : ℕ) : ℤ).natAbs = 2 ^ t := by simp
    rw [hδ, Int.natAbs_mul, hn]

  have h4t : 4 ^ t = 2 ^ t * 2 ^ t := by
    have h1 : (4 : ℕ) ^ t = ((2 : ℕ) ^ 2) ^ t := by
      refine congrArg (fun x : ℕ => x ^ t) ?_
      norm_num
    rw [h1, ← Nat.pow_mul, ← Nat.pow_add]
    have hexp : 2 * t = t + t := by omega
    rw [hexp]
  have hge : 2 ^ t ≤ (pairD j Q P).natAbs := by
    rw [habs]
    exact Nat.le_mul_of_pos_right _ hδ1
  have hfin1 : 4 ^ t * m ≤ P.2 * (pairD j Q P).natAbs := by
    rw [hq, h4t, Nat.mul_assoc, Nat.mul_comm (2 ^ t * m) (pairD j Q P).natAbs]
    exact Nat.mul_le_mul_right _ hge
  exact lt_of_le_of_lt hfin1 hb

/-- Appending a singleton to a list makes its element the result of `getLast?`. -/
theorem getLast?_append_singleton {α : Type*} (a : α) : ∀ (ys : List α),
    (ys ++ [a]).getLast? = some a := by
  intro ys
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    match ys, ih with
    | [], _ => rfl
    | z :: zs, ih2 =>
      show List.getLast? (y :: z :: (zs ++ [a])) = some a
      rw [List.getLast?_cons_cons]
      exact ih2

/-- Under the signed Euclidean stage invariants and sufficient fuel, a generated pair with zero
discrepancy is the last pair in the list. -/
theorem stage_d0_last (j Q : ℕ) : ∀ (den : ℕ), ∀ (num fuel : ℕ) (p2 p1 : ℕ × ℕ) (ε : ℤ),
    0 < den → den + 1 ≤ fuel → 0 < num → 0 < Q → (ε = 1 ∨ ε = -1) →
    pairD j Q p2 = ε * num → pairD j Q p1 = -ε * den →
    num * p1.2 + den * p2.2 = Q →
    ∀ P ∈ convPairs (cfPartialsAux fuel num den) p2 p1,
      pairD j Q P = 0 →
      ∃ ys, convPairs (cfPartialsAux fuel num den) p2 p1 = ys ++ [P] := by
  intro den
  induction den using Nat.strongRecOn with
  | ind den ih =>
    intro num fuel p2 p1 ε hd hf hnum hQ hε hd2 hd1 hI3 P hP hdP0
    rcases fuel with _ | k
    · omega
    rcases den with _ | d
    · omega
    have hdpos : 0 < d + 1 := Nat.succ_pos d
    by_cases hmod : num % (d + 1) = 0
    · have hmlist : cfPartialsAux k (d + 1) 0 = [] := by
        match k with
        | 0 => rfl
        | (k' + 1) => rfl
      have hlist : convPairs (cfPartialsAux (k + 1) num (d + 1)) p2 p1
          = [(num / (d + 1) * p1.1 + p2.1, num / (d + 1) * p1.2 + p2.2)] := by
        simp only [cfPartialsAux, hmod, hmlist, convPairs]
      rw [hlist] at hP
      have hP' : P = (num / (d + 1) * p1.1 + p2.1, num / (d + 1) * p1.2 + p2.2) :=
        List.mem_singleton.mp hP
      rw [hlist]
      exact ⟨[], by simp [hP']⟩
    · obtain ⟨r, hr⟩ : ∃ r, num % (d + 1) = r + 1 := by
        rcases Nat.eq_zero_or_pos (num % (d + 1)) with h0 | h1
        · omega
        · exact ⟨num % (d + 1) - 1, by omega⟩
      have hEd : num = num / (d + 1) * (d + 1) + (r + 1) := by
        have h0 := Nat.div_add_mod num (d + 1)
        rw [hr, Nat.mul_comm] at h0
        exact h0.symm
      have hmodlt : r + 1 < d + 1 := by
        have := Nat.mod_lt num hdpos
        omega
      have hdhead : pairD j Q (num / (d + 1) * p1.1 + p2.1, num / (d + 1) * p1.2 + p2.2)
          = ε * (r + 1) := by
        have hc : ((num : ℕ) : ℤ)
            = ((num / (d + 1) : ℕ) : ℤ) * ((d + 1 : ℕ) : ℤ) + ((r + 1 : ℕ) : ℤ) := by
          exact_mod_cast hEd
        have hEz2 : ((num : ℤ) - ((num / (d + 1) : ℕ) : ℤ) * ((d + 1 : ℕ) : ℤ))
            = ((r + 1 : ℕ) : ℤ) := by
          linear_combination hc
        rw [pairD_head j Q num (d + 1) (num / (d + 1)) p2 p1 ε hd2 hd1, hEz2,
          Nat.cast_succ]
      have hIH := ih (r + 1) hmodlt (d + 1) k p1
        (num / (d + 1) * p1.1 + p2.1, num / (d + 1) * p1.2 + p2.2) (-ε)
        (Nat.succ_pos r) (by omega) hdpos hQ
        (by rcases hε with h | h <;> simp [h])
        (by rw [hd1])
        (by rw [hdhead, neg_neg, Nat.cast_succ])
        (by linear_combination (p1.2 : ℕ) * hEd.symm + 1 * hI3)
      simp only [cfPartialsAux, convPairs] at hP ⊢
      rw [hr] at hP ⊢
      rcases List.mem_cons.mp hP with rfl | hPtail
      · exact absurd hdP0 (by
          rw [hdhead]
          rcases hε with h | h <;> rw [h] <;> omega)
      · obtain ⟨ys, hys⟩ := hIH P hPtail hdP0
        exact ⟨_, by rw [List.cons_append, hys]⟩

/-- An odd natural number dividing a power of two equals one. -/
theorem odd_dvd_two_pow : ∀ (k w : ℕ), ¬2 ∣ w → w ∣ 2 ^ k → w = 1 := by
  intro k
  induction k with
  | zero => intro w _ hdvd; exact Nat.eq_one_of_dvd_one hdvd
  | succ k ih =>
    intro w hw hdvd
    have hc : Nat.Coprime w 2 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hw).symm
    have h2 : w ∣ 2 ^ k * 2 := by rw [← Nat.pow_succ]; exact hdvd
    exact ih w hw (hc.dvd_of_dvd_mul_right h2)

/-- If `Q = 2 ^ n`, `r = 2 ^ u * w` with odd `w ≥ 3`, and `Q ≤ 4 ^ u * w`, then `r` is absent
from `cfDenoms j Q` for `0 < j < Q`. -/
theorem two_b_corollary (n u w j Q r : ℕ) (hQ2 : Q = 2 ^ n) (hr : r = 2 ^ u * w)
    (hw : ¬2 ∣ w) (hw3 : 3 ≤ w) (h4 : Q ≤ 4 ^ u * w) (hj0 : 0 < j) (hj : j < Q) :
    r ∉ cfDenoms j Q := by
  intro hmem
  have hfm := (List.mem_filter.mp hmem).1
  obtain ⟨P, hPmem, hP2⟩ := List.mem_map.mp hfm
  have hlast := stage_d0_last j Q Q j (Q + 1) (0, 1) (1, 0) 1
    (lt_of_lt_of_le hj0 (le_of_lt hj)) (Nat.le_refl _) hj0
    (lt_of_lt_of_le hj0 (le_of_lt hj)) (Or.inl rfl) (by simp [pairD]) (by simp [pairD])
    (by simp) P hPmem
  obtain ⟨t, ht⟩ := List.getLast?_eq_some_iff.mp (cfLast_pair j Q hj0 hj)
  by_cases hdP0 : pairD j Q P = 0
  · obtain ⟨ys, hys⟩ := hlast hdP0
    have hPL : P = (j / Nat.gcd j Q, Q / Nat.gcd j Q) := by
      have hEq : ys ++ [P] = t ++ [(j / Nat.gcd j Q, Q / Nat.gcd j Q)] :=
        hys.symm.trans ht
      have h3 := congrArg List.getLast? hEq
      rw [getLast?_append_singleton, getLast?_append_singleton] at h3
      exact Option.some.inj h3
    have hw1 : w ∣ P.2 := by
      rw [hP2, hr]; exact Nat.dvd_mul_left w (2 ^ u)
    have hQg : P.2 = Q / Nat.gcd j Q := by rw [hPL]
    rw [hQg] at hw1
    have hwQ : w ∣ Q :=
      hw1.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right j Q))
    rw [hQ2] at hwQ
    have := odd_dvd_two_pow n w hw hwQ
    omega
  · exact absurd (two_b n j Q u w hQ2 hw hj0 hj P hPmem hdP0
      (by rw [hP2, hr])) (by omega)

end Qatlib.Concepts.HspRecovery.CfOrder.FiniteOrderRecovery
