/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Data.Fintype.Powerset
public import Qatlib.Concepts.CodingDecoding.FamilyAssembly.AbstractParameterGuarantee

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode Qatlib.Concepts.CodingDecoding.CssTesters Qatlib.Concepts.CodingDecoding.CssTesters.CssTester

open Qatlib.Concepts.CodingDecoding.CssTesters Qatlib.Concepts.CodingDecoding.CssTesters

namespace Qatlib.Concepts.CodingDecoding.FamilyAssembly

open Qatlib

open scoped Classical BigOperators

/-- For `x` between zero and one, the power of one minus `x` is at least one minus `n` times
`x`. -/
private theorem bernoulli_lower_qltc (x : ℝ) (_hx : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    1 - n * x ≤ (1 - x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hx' : (0 : ℝ) ≤ 1 - x := by linarith
    rw [pow_succ]
    have h1 : (1 - n * x) * (1 - x) ≤ (1 - x) ^ n * (1 - x) :=
      mul_le_mul_of_nonneg_right ih hx'
    have hx2 : (0 : ℝ) ≤ x * x := mul_self_nonneg x
    have hnℝ : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg (α := ℝ) n
    have hnx2 : (0 : ℝ) ≤ (n : ℝ) * (x * x) := mul_nonneg hnℝ hx2
    have e : 1 - ((↑(n + 1) : ℝ)) * x = (1 - (n : ℝ) * x) * (1 - x) - (n : ℝ) * (x * x) := by
      push_cast
      ring
    show 1 - ((↑(n + 1) : ℝ)) * x ≤ (1 - x) ^ n * (1 - x)
    linarith [h1, hnx2, e]

/-- The specified constant local dimensions and piecewise multiplicities give strictly positive
`gammaK` under the stated bounds on `t` and `k`. -/
private theorem gammaK_pos_qltc {t k : ℕ} (ht : 4 ≤ t) (_h2k : 2 ≤ k) (hkt : k + 2 ≤ t) :
    0 < gammaK t k (fun _ => 8 * t * 2 ^ t)
        (fun (i : Fin t) (_ : Fin 2) => if (i : ℕ) < k then 1 else 8 * t * 2 ^ t - 1) := by
  classical
  have hkle : k ≤ t := by omega
  set N : ℕ := 8 * t * 2 ^ t with hNdef
  set mm : Fin t → Fin 2 → ℕ :=
    fun (i : Fin t) (_ : Fin 2) => if (i : ℕ) < k then 1 else N - 1 with hmm
  set c : ℝ := 1 / (N : ℝ) with hcdef

  have h2t : (16 : ℕ) ≤ 2 ^ t := by
    have h := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 4 ≤ t by omega)
    simpa using h
  have hN0 : 0 < N := by nlinarith [h2t, ht]
  have hN2 : 2 ≤ N := by nlinarith [h2t, ht]
  have h1N : 1 ≤ N := by omega
  have hN512 : (512 : ℕ) ≤ N := by nlinarith [h2t, ht]
  have hNbound : (128 : ℕ) * t ≤ N := by nlinarith [h2t, ht]
  have htt : (16 : ℕ) ≤ t * t := by nlinarith [ht]
  have hkeyN : (1 : ℕ) ≤ t * t * 2 ^ t := by nlinarith [htt, h2t]
  have hNN : (64 : ℕ) * 2 ^ t ≤ N * N := by
    have h1 : 2 ^ t ≤ (t * t * 2 ^ t) * 2 ^ t :=
      Nat.le_mul_of_pos_left (2 ^ t) (show 0 < t * t * 2 ^ t by omega)
    have h2 : (64 : ℕ) * 2 ^ t ≤ 64 * ((t * t * 2 ^ t) * 2 ^ t) := Nat.mul_le_mul_left _ h1
    calc (64 : ℕ) * 2 ^ t ≤ 64 * ((t * t * 2 ^ t) * 2 ^ t) := h2
      _ = N * N := by rw [hNdef]; ring
  have hNp : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have htℝ : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hcpos : (0 : ℝ) < c := by rw [hcdef]; positivity
  have hc1 : c ≤ 1 := by
    rw [hcdef]
    exact (div_le_one hNp).mpr (by exact_mod_cast h1N)
  have hc512 : c ≤ 1 / 512 := by
    rw [hcdef, div_le_div_iff₀ hNp (by norm_num : (0 : ℝ) < 512), one_mul, one_mul]
    exact_mod_cast hN512

  set L : Finset (Fin t) := Finset.univ.filter fun i : Fin t => (i : ℕ) < k with hLdef
  have hLmem : ∀ i : Fin t, i ∈ L ↔ (i : ℕ) < k := by
    intro i; simp [hLdef]
  have hLcard : L.card = k := by
    have hinj : Set.InjOn (fun j : Fin k => Fin.castLE hkle j)
        (Finset.univ (α := Fin k) : Set (Fin k)) := by
      intro a _ b _ h
      apply Fin.ext
      simpa [Fin.castLE] using congrArg Fin.val h
    have hLeq : L = Finset.image (fun j : Fin k => Fin.castLE hkle j)
        (Finset.univ (α := Fin k)) := by
      ext i
      rw [hLmem i]
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro hi
        exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
      · rintro ⟨j, hj2⟩
        rw [← hj2]
        exact j.isLt
    rw [hLeq, Finset.card_image_of_injOn hinj, Finset.card_univ, Fintype.card_fin]

  have hkey : ((N : ℝ) - 1) / (N : ℝ) = 1 - 1 / (N : ℝ) := by
    field_simp
  have hmu : ∀ (i : Fin t) (b : Fin 2),
      muIB (fun _ => N) mm i b = if (i : ℕ) < k then c else 1 - c := by
    intro i b
    by_cases h : (i : ℕ) < k
    · simp only [muIB, hmm, ite_eq_left h, Nat.cast_one, hcdef]
    · simp only [muIB, hmm, ite_eq_right h, Nat.cast_sub h1N, Nat.cast_one]
      rw [hkey, ← hcdef]
  have hp : ∀ i : Fin t, pIB (fun _ => N) mm i = if (i : ℕ) < k then c else 1 - c := by
    intro i
    rw [pIB, hmu i 0, hmu i 1, min_self]
  have hq : ∀ i : Fin t, qIB (fun _ => N) mm i = if (i : ℕ) < k then 1 - c else c := by
    intro i
    rw [qIB, hmu i 0, hmu i 1, max_self]
    split_ifs <;> ring
  have hS : ∀ i : Fin t, sIB (fun _ => N) mm i - 1 =
      if (i : ℕ) < k then 2 * c - 1 else 1 - 2 * c := by
    intro i
    rw [sIB, hmu i 0, hmu i 1]
    split_ifs <;> ring

  have hFirst : ((-1 : ℝ) ^ k) *
      (Finset.univ.prod fun i : Fin t => sIB (fun _ => N) mm i - 1) = (1 - 2 * c) ^ t := by
    simp only [hS]
    rw [Finset.prod_ite, ← hLdef, Finset.prod_const, hLcard]
    have hcompl : (Finset.univ.filter fun i : Fin t => ¬(i : ℕ) < k) = L ᶜ := by
      ext i; simp [hLdef]
    rw [hcompl, Finset.prod_const, Finset.card_compl, Fintype.card_fin, hLcard]
    have hpoweq : (2 * c - 1 : ℝ) ^ k = (-1 : ℝ) ^ k * (1 - 2 * c) ^ k := by
      rw [show (2 * c - 1 : ℝ) = -(1 - 2 * c) from by ring, neg_pow]
    have hX : (1 - 2 * c) ^ k * (1 - 2 * c) ^ (t - k) = (1 - 2 * c) ^ t := by
      rw [← pow_add, show k + (t - k) = t from by omega]
    have hsq : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by
      rw [← pow_add, show k + k = 2 * k from by omega, pow_mul, pow_two]
      norm_num
    calc ((-1 : ℝ) ^ k) * ((2 * c - 1) ^ k * (1 - 2 * c) ^ (t - k))
        = (((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k)) * ((1 - 2 * c) ^ k * (1 - 2 * c) ^ (t - k)) := by
          rw [hpoweq]; ring
      _ = 1 * (1 - 2 * c) ^ t := by rw [hsq, hX]
      _ = (1 - 2 * c) ^ t := by ring

  have hterm : ∀ s : Finset (Fin t), s.card % 2 = k % 2 → s.card ≠ k →
      (Finset.univ.prod fun i : Fin t =>
        if i ∈ s then qIB (fun _ => N) mm i else pIB (fun _ => N) mm i) ≤ c ^ 2 := by
    intro s hpar hne
    set U : Finset (Fin t) := (s \ L) ∪ (L \ s) with hUdef
    have hUmem : ∀ i : Fin t, i ∈ U ↔ ((i ∈ s ∧ i ∉ L) ∨ (i ∈ L ∧ i ∉ s)) := by
      intro i; simp [hUdef, Finset.mem_union, Finset.mem_sdiff]
    have hfboth : ∀ i ∈ (Finset.univ : Finset (Fin t)),
        (0 : ℝ) ≤ (if i ∈ s then qIB (fun _ => N) mm i else pIB (fun _ => N) mm i) ∧
        (if i ∈ s then qIB (fun _ => N) mm i else pIB (fun _ => N) mm i) ≤
          (if i ∈ U then c else 1) := by
      intro i _
      have hc1c : (1 : ℝ) - c ≤ 1 := by linarith [hc1]
      have h1c : (0 : ℝ) ≤ 1 - c := by linarith [hc1]
      by_cases hiU : i ∈ U
      · rcases (hUmem i).mp hiU with ⟨his, hiL⟩ | ⟨hiL, his⟩
        · rw [ite_eq_left his, hq i,
            ite_eq_right (show ¬((i : ℕ) < k) from (hLmem i).not.mp hiL), ite_eq_left hiU]
          exact ⟨hcpos.le, le_refl _⟩
        · rw [ite_eq_right his, hp i, ite_eq_left ((hLmem i).mp hiL), ite_eq_left hiU]
          exact ⟨hcpos.le, le_refl _⟩
      · rw [ite_eq_right hiU]
        by_cases his : i ∈ s
        · rw [ite_eq_left his, hq i]
          by_cases hik : (i : ℕ) < k
          · simp only [ite_eq_left hik]; exact ⟨h1c, hc1c⟩
          · simp only [ite_eq_right hik]; exact ⟨hcpos.le, hc1⟩
        · rw [ite_eq_right his, hp i]
          by_cases hik : (i : ℕ) < k
          · simp only [ite_eq_left hik]; exact ⟨hcpos.le, hc1⟩
          · simp only [ite_eq_right hik]; exact ⟨h1c, hc1c⟩
    have hUcard : U.card = (s \ L).card + (L \ s).card := by
      have hint : ((s \ L) ∩ (L \ s) : Finset (Fin t)) = ∅ := by
        ext i; simp [Finset.mem_sdiff, Finset.mem_inter]; tauto
      have hu := Finset.card_union_add_card_inter (s \ L) (L \ s)
      rw [hint, Finset.card_empty, ← hUdef] at hu
      omega
    have hI1 : (s ∩ L).card ≤ s.card := Finset.card_le_card Finset.inter_subset_left
    have hI2 : (s ∩ L).card ≤ L.card := Finset.card_le_card Finset.inter_subset_right
    have hsd1 : (s \ L).card + (s ∩ L).card = s.card := by
      have h := Finset.card_sdiff (s := L) (t := s)
      rw [Finset.inter_comm L s] at h
      omega
    have hsd2 : (L \ s).card + (s ∩ L).card = L.card := by
      have h := Finset.card_sdiff (s := s) (t := L)
      omega
    have hU2 : 2 ≤ U.card := by omega
    have hcpow : ∀ n : ℕ, c ^ n ≤ 1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ]
        calc c ^ n * c ≤ 1 * c := mul_le_mul_of_nonneg_right ih hcpos.le
          _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hc1 (by positivity)
          _ = 1 := by ring
    have hfilteq : (Finset.univ.filter fun i : Fin t => i ∈ U) = U := by
      ext i; simp
    calc (Finset.univ.prod fun i : Fin t =>
          if i ∈ s then qIB (fun _ => N) mm i else pIB (fun _ => N) mm i)
        ≤ Finset.univ.prod fun i : Fin t => if i ∈ U then c else 1 :=
          Finset.prod_le_prod₀ (fun i _ => (hfboth i (Finset.mem_univ i)).1)
            (fun i _ => (hfboth i (Finset.mem_univ i)).2)
      _ = c ^ U.card := by
          simp only [Finset.prod_ite, hfilteq, Finset.prod_const, one_pow, mul_one]
      _ ≤ c ^ 2 := by
          calc c ^ U.card = c ^ 2 * c ^ (U.card - 2) := by
                rw [← pow_add]; congr 1; omega
            _ ≤ c ^ 2 * 1 := mul_le_mul_of_nonneg_left (hcpow _) (by positivity)
            _ = c ^ 2 := by ring

  have hSum : (∑ j ∈ Finset.range (t + 1),
      if j % 2 = k % 2 ∧ j ≠ k then scriptB t j (fun _ => N) mm else 0) ≤ 2 ^ t * c ^ 2 := by
    have hcardUniv : (Finset.univ : Finset (Fin t)).card = t := by
      rw [Finset.card_univ, Fintype.card_fin]
    have hstep1 : ∀ j ∈ Finset.range (t + 1),
        (if j % 2 = k % 2 ∧ j ≠ k then scriptB t j (fun _ => N) mm else 0)
        = ∑ s ∈ (Finset.univ.filter fun s : Finset (Fin t) => s.card = j),
            (if j % 2 = k % 2 ∧ j ≠ k then
              (Finset.univ.prod fun i : Fin t =>
                if i ∈ s then qIB (fun _ => N) mm i else pIB (fun _ => N) mm i) else 0) := by
      intro j _
      by_cases h : j % 2 = k % 2 ∧ j ≠ k
      · simp only [h.1, true_and, scriptB, ite_eq_left h.2]
      · simp [h]
    calc (∑ j ∈ Finset.range (t + 1),
            if j % 2 = k % 2 ∧ j ≠ k then scriptB t j (fun _ => N) mm else 0)
        = ∑ j ∈ Finset.range (t + 1),
            ∑ s ∈ (Finset.univ.filter fun s : Finset (Fin t) => s.card = j),
              (if j % 2 = k % 2 ∧ j ≠ k then
                (Finset.univ.prod fun i : Fin t =>
                  if i ∈ s then qIB (fun _ => N) mm i else pIB (fun _ => N) mm i) else 0) :=
          Finset.sum_congr rfl fun j hj => hstep1 j hj
      _ = ∑ j ∈ Finset.range (t + 1),
            ∑ s ∈ (Finset.univ : Finset (Finset (Fin t))),
              (if s.card = j then (if j % 2 = k % 2 ∧ j ≠ k then
                (Finset.univ.prod fun i : Fin t =>
                  if i ∈ s then qIB (fun _ => N) mm i else pIB (fun _ => N) mm i) else 0)
                else 0) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_filter]
      _ = ∑ s ∈ (Finset.univ : Finset (Finset (Fin t))),
            ∑ j ∈ Finset.range (t + 1),
              (if s.card = j then (if j % 2 = k % 2 ∧ j ≠ k then
                (Finset.univ.prod fun i : Fin t =>
                  if i ∈ s then qIB (fun _ => N) mm i else pIB (fun _ => N) mm i) else 0)
                else 0) :=
          Finset.sum_comm
      _ = ∑ s ∈ (Finset.univ : Finset (Finset (Fin t))),
            (if s.card % 2 = k % 2 ∧ s.card ≠ k then
              (Finset.univ.prod fun i : Fin t =>
                if i ∈ s then qIB (fun _ => N) mm i else pIB (fun _ => N) mm i) else 0) :=
          Finset.sum_congr rfl fun s _ => by
            rw [Finset.sum_eq_single (s.card)
              (fun b _ hb => ite_eq_right (Ne.symm hb))
              (fun hb => absurd (Finset.mem_range.mpr
                (lt_of_le_of_lt (Finset.card_le_card (Finset.subset_univ s))
                  (by rw [hcardUniv]; omega))) hb)]
            simp
      _ ≤ ∑ s ∈ (Finset.univ : Finset (Finset (Fin t))), c ^ 2 :=
          Finset.sum_le_sum fun s _ => by
            by_cases h : s.card % 2 = k % 2 ∧ s.card ≠ k
            · rw [ite_eq_left h]; exact hterm s h.1 h.2
            · rw [ite_eq_right h]; positivity
      _ = 2 ^ t * c ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring

  have hbern : (1 : ℝ) - (t : ℝ) * (2 * c) ≤ (1 - 2 * c) ^ t :=
    bernoulli_lower_qltc (2 * c) (by linarith [hc512]) (by linarith [hc512]) t
  have hA : 2 * (t : ℝ) * c ≤ 1 / 64 := by
    rw [hcdef, mul_one_div,
      div_le_div_iff₀ hNp (by norm_num : (0 : ℝ) < 64)]
    have hℝ : (128 : ℝ) * (t : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNbound
    linarith
  have hB : (2 : ℝ) ^ t * c ^ 2 ≤ 1 / 64 := by
    rw [hcdef, one_div_pow, mul_one_div,
      div_le_div_iff₀ (pow_pos hNp 2) (by norm_num : (0 : ℝ) < 64)]
    have hℝ2 : (2 : ℝ) ^ t * 64 ≤ (N : ℝ) * (N : ℝ) := by
      have h4 : (((64 * 2 ^ t : ℕ) : ℝ)) ≤ (((N * N : ℕ) : ℝ)) := by exact_mod_cast hNN
      push_cast at h4
      linarith
    rw [pow_two]
    linarith
  have hlow : (63 : ℝ) / 64 ≤ (1 - 2 * c) ^ t := by
    have h1 : (t : ℝ) * (2 * c) ≤ 1 / 64 := by
      calc (t : ℝ) * (2 * c) = 2 * (t : ℝ) * c := by ring
        _ ≤ 1 / 64 := hA
    calc (63 : ℝ) / 64 = 1 - 1 / 64 := by norm_num
      _ ≤ 1 - (t : ℝ) * (2 * c) := by linarith
      _ ≤ (1 - 2 * c) ^ t := hbern
  have hfinal : 2 ^ t * c ^ 2 < (1 - 2 * c) ^ t :=
    hB.trans_lt ((show (1 : ℝ) / 64 < 63 / 64 by norm_num).trans_le hlow)

  simp only [gammaK]
  rw [hFirst]
  linarith

/-- For admissible `t` and `k`, there exist parameters, a finite field of characteristic two,
and an unbounded size family of chain complexes satisfying the displayed positivity and
dimension conditions. -/
theorem hypothesisFamiliesExist :
    ∀ (t k : ℕ), 4 ≤ t → 2 ≤ k → k + 2 ≤ t →
      ∃ (s : ℕ) (n : Fin t → ℕ) (m : Fin t → Fin 2 → ℕ)
        (K ρ lam ℒ 𝒬 : ℝ) (F : Type) (_hf : Field F) (_ha : Algebra (ZMod 2) F)
        (_hfr : Module.Free (ZMod 2) F) (_hfi : Fintype F)
        (_hfin : Module.Finite (ZMod 2) F) (V : ℕ → ℕ),
        0 < s ∧
        (∀ i : Fin t, 2 ≤ n i) ∧ (∀ i : Fin t, ∀ b : Fin 2, 0 < m i b ∧ m i b < n i) ∧
        1 ≤ K ∧ 0 < ρ ∧ ρ ≤ 1 ∧ 0 ≤ lam ∧ lam < 1 ∧ 0 < ℒ ∧ 0 < 𝒬 ∧
        0 < gammaK t k n m ∧ lam * ℒ < 1 ∧ 0 < (1 - lam * ℒ) / 𝒬 ∧
        Filter.Tendsto V Filter.atTop Filter.atTop ∧
        (∀ ν : ℕ,
          ∃ (κPrev κ κNext α : Type)
            (Fprev : Fintype κPrev) (Fmid : Fintype κ) (Fnext : Fintype κNext)
            (Fα : Fintype α)
            (Dprev : DecidableEq κPrev) (Dmid : DecidableEq κ)
            (Dnext : DecidableEq κNext) (Dα : DecidableEq α)
            (δPrev : Matrix κ κPrev F) (δ : Matrix κNext κ F)
            (_hδ : δ * δPrev = 0) (_part : κ → α)
            (μc μh εc εh : ℝ) (_wF : ℕ),
            letI := Fprev; letI := Fmid; letI := Fnext; letI := Fα
            letI := Dprev; letI := Dmid; letI := Dnext; letI := Dα
            Fintype.card κ = V ν * (Finset.univ.prod fun i : Fin t => n i) *
              elementarySym t n (t - k) ∧
            0 < Fintype.card κ ∧ 0 < Fintype.card κPrev + Fintype.card κNext ∧
            0 < μc ∧ 0 < μh ∧ 0 < εc ∧ 0 < εh) := by
  intro t k ht h2k hkt
  have h2t : (16 : ℕ) ≤ 2 ^ t := by
    have h := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 4 ≤ t by omega)
    simpa using h
  have hN0 : (0 : ℕ) < 8 * t * 2 ^ t := by nlinarith [h2t, ht]
  have hN2 : (2 : ℕ) ≤ 8 * t * 2 ^ t := by nlinarith [h2t, ht]
  have hprod : Finset.univ.prod (fun _ : Fin t => 8 * t * 2 ^ t) = (8 * t * 2 ^ t) ^ t := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have helem : 0 < elementarySym t (fun _ => 8 * t * 2 ^ t) (t - k) := by
    simp only [elementarySym]
    rw [ite_eq_left (Nat.sub_le t k)]
    obtain ⟨p, _, hp2⟩ := Finset.exists_subset_card_eq (n := t - k) (by
      show t - k ≤ (Finset.univ : Finset (Fin t)).card
      rw [Finset.card_univ, Fintype.card_fin]
      omega)
    refine Finset.sum_pos (fun s _ => ?_) ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp2⟩⟩
    exact Finset.prod_pos fun i _ => hN0
  refine ⟨1, fun _ => 8 * t * 2 ^ t,
    fun (i : Fin t) (_ : Fin 2) => if (i : ℕ) < k then 1 else 8 * t * 2 ^ t - 1,
    1, 1, 0, 1, 1, ZMod 2, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, fun ν => ν + 1, ?_⟩
  refine ⟨by norm_num, fun i => by simpa using hN2, ?_, by norm_num, by norm_num,
    by norm_num, le_refl 0, by norm_num, by norm_num, by norm_num, gammaK_pos_qltc ht h2k hkt,
    by norm_num, by norm_num, ?_, ?_⟩
  · intro i b
    show 0 < (if (i : ℕ) < k then 1 else 8 * t * 2 ^ t - 1) ∧
      (if (i : ℕ) < k then 1 else 8 * t * 2 ^ t - 1) < 8 * t * 2 ^ t
    by_cases h : (i : ℕ) < k
    · rw [ite_eq_left h]; exact ⟨by omega, by omega⟩
    · rw [ite_eq_right (by omega : ¬(i : ℕ) < k)]; omega
  · rw [Filter.tendsto_atTop_atTop]
    intro b
    exact ⟨b, fun a ha => by omega⟩
  · intro ν
    refine ⟨Fin 1,
      Fin ((ν + 1) * (Finset.univ.prod fun i : Fin t => 8 * t * 2 ^ t) *
        elementarySym t (fun _ => 8 * t * 2 ^ t) (t - k)), Fin 1, Fin 1,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, 0, 0, Matrix.zero_mul _, fun _ => 0, 1, 1, 1, 1, 1, ?_⟩
    refine ⟨?_, ?_, ?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · simp only [Fintype.card_fin]
    · rw [Fintype.card_fin]
      rw [hprod]
      exact Nat.mul_pos (Nat.mul_pos (Nat.succ_pos ν) (pow_pos hN0 t)) helem
    · simp only [Fintype.card_fin]
      omega

end Qatlib.Concepts.CodingDecoding.FamilyAssembly
