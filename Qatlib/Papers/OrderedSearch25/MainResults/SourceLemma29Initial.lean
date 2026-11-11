/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentGram
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.OrderedSearchInstance

/-!
# Source Lemma 29: uniqueness of the initial matrix

Carolan–Childs–Kovacs-Deak–Schaeffer, fixed arXiv:2503.21090v2, Appendix A,
Lemma 29 and its proof.

The paper's statement: *"The semidefinite program `tr_l A + tr_{n-l} A = 1`
(`0 ≤ l < n`), `A ∈ S^n_+` has the unique solution `A = J_n / n`."*

The proof is the appendix computation: positive semidefiniteness bounds every
entry by the arithmetic mean of the two diagonal entries it touches,
`a_{ij} ≤ sqrt(a_{ii} a_{jj}) ≤ (a_{ii} + a_{jj})/2`, and summing that bound over
one cyclic diagonal gives `1 = tr_l A + tr_{n-l} A ≤ tr A = 1`, so every
inequality is tight; tightness in the arithmetic-geometric mean forces all
diagonal entries to be equal, and `tr A = 1` then fixes them at `1/n`.

Formalisation notes, so the coverage claim stays honest:

* The generalized traces `tr_j` are the frozen `genTrace`
  (`OrderedSearch.TiSdpBridge.genTrace`,
  Equation (1) of the paper). Equation (154) is transcribed literally in the
  hypothesis `hcon`.
* `cycShiftPow n l` is the frozen translation `T = finShiftEquiv n`
  (`OrderedSearch.TiSdpBridge.finShiftEquiv`,
  Equation (4) of the paper) raised to the `l`-th power.
  `genTrace_cyclic_bridge` proves that the cyclic diagonal of residue `l mod n`
  is exactly `tr_l A + tr_{l-n} A`, i.e. Equation (1) regrouping the two
  generalized diagonals of one residue class modulo `n`. Composed with the
  symmetry `tr_{-j} = tr_j` this is the paper's `tr_l A + tr_{n-l} A`.
* The matrices are complex for consistency with `genTrace`; `hSym` is the
  paper's `A ∈ S^n` (symmetric), and positive semidefiniteness together with
  symmetry forces the entries to be real.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OrderedSearch25.MainResults

open scoped BigOperators ComplexOrder
open Matrix

open Qatlib.Concepts.OrderedOracle.TiSdpBridge

/-- The frozen cyclic translation `T = finShiftEquiv n` (Equation (4) of
arXiv:2503.21090v2) raised to the `l`-th power: the shift `i ↦ i + l mod n`. -/
noncomputable def cycShiftPow (n : ℕ) [NeZero n] (l : ℕ) : Equiv.Perm (Fin n) :=
  (finShiftEquiv n) ^ l

/-- The exponentiated cyclic translation acts by addition modulo `n`
(Equation (4) of arXiv:2503.21090v2, iterated `l` times). -/
theorem cycShiftPow_val (n l : ℕ) [NeZero n] (i : Fin n) :
    ((cycShiftPow n l) i).val = ((i : ℕ) + l) % n := by
  induction l with
  | zero => simp [cycShiftPow, Nat.mod_eq_of_lt i.isLt]
  | succ l ih =>
    rw [cycShiftPow, pow_succ', Equiv.Perm.mul_apply]
    change ((((finShiftEquiv n) ^ l) i).val + 1) % n = ((i : ℕ) + (l + 1)) % n
    rw [show ((finShiftEquiv n) ^ l) i = cycShiftPow n l i from rfl, ih, Nat.add_mod,
      Nat.mod_mod, ← Nat.add_mod, add_assoc]

/-- The generalized trace as a sum over the explicit generalized diagonal. -/
theorem genTrace_eq_sum_filter {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (j : ℤ) :
    genTrace A j =
      ∑ p ∈ (Finset.univ.filter fun p : Fin n × Fin n => (p.2 : ℤ) - (p.1 : ℤ) = j),
        A p.1 p.2 := by
  rw [genTrace, ← Finset.sum_product']
  rw [← Finset.sum_filter]
  rfl

/-- Equation (1) regrouped: the cyclic diagonal of residue `l mod n` is the sum
of the two generalized traces `tr_l` and `tr_{l-n}`. This is the identity that
turns Equation (154) into a single sum over `Fin n`. -/
theorem genTrace_cyclic_bridge {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ)
    (l : ℕ) (hl : l < n) :
    genTrace A (l : ℤ) + genTrace A ((l : ℤ) - (n : ℤ))
      = ∑ i : Fin n, A i ((cycShiftPow n l) i) := by
  have hdisj : Disjoint (Finset.univ.filter fun p : Fin n × Fin n => (p.2 : ℤ) - (p.1 : ℤ) = (l : ℤ))
      (Finset.univ.filter fun p : Fin n × Fin n => (p.2 : ℤ) - (p.1 : ℤ) = (l : ℤ) - (n : ℤ)) := by
    rw [Finset.disjoint_filter]
    intro p _ h1 h2
    have hn : (0 : ℤ) < (n : ℤ) := by exact_mod_cast NeZero.pos n
    linarith
  have hset : (Finset.univ.filter fun p : Fin n × Fin n => (p.2 : ℤ) - (p.1 : ℤ) = (l : ℤ))
      ∪ (Finset.univ.filter fun p : Fin n × Fin n => (p.2 : ℤ) - (p.1 : ℤ) = (l : ℤ) - (n : ℤ))
      = (Finset.univ.filter fun p : Fin n × Fin n => (p.2 : ℕ) = ((p.1 : ℕ) + l) % n) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h)
      · have h2 : (p.2 : ℤ) = (p.1 : ℤ) + (l : ℤ) := by linarith
        have h3 : (p.2 : ℕ) = (p.1 : ℕ) + l := by omega
        have h4 : (p.1 : ℕ) + l < n := by omega
        rw [h3, Nat.mod_eq_of_lt h4]
      · have h2 : (p.2 : ℤ) = (p.1 : ℤ) + (l : ℤ) - (n : ℤ) := by linarith
        have h3 : (p.2 : ℕ) + n = (p.1 : ℕ) + l := by omega
        conv_rhs => rw [← h3]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt p.2.isLt]
    · intro h
      rcases Nat.lt_or_ge ((p.1 : ℕ) + l) n with hq | hq
      · left
        have h4 : (p.1 : ℕ) + l = (p.2 : ℕ) := by rw [h, Nat.mod_eq_of_lt hq]
        omega
      · right
        have hq' : ((p.1 : ℕ) + l) % n = (p.1 : ℕ) + l - n := by
          rw [Nat.mod_eq_sub_mod hq, Nat.mod_eq_of_lt (by omega)]
        rw [hq'] at h
        omega
  rw [genTrace_eq_sum_filter, genTrace_eq_sum_filter, ← Finset.sum_union hdisj, hset]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single ((cycShiftPow n l) i)]
  · rw [if_pos (cycShiftPow_val n l i)]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext (by rw [cycShiftPow_val]; exact h))
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The exponentiated translation hits every index: for `i ≠ j` there is a
positive shift `l < n` taking `i` to `j`. This is the covering step that turns
the cyclic-diagonal equalities into entrywise equalities. -/
theorem exists_cycShiftPow_of_ne {n : ℕ} [NeZero n] {i j : Fin n} (hij : i ≠ j) :
    ∃ l, 0 < l ∧ l < n ∧ (cycShiftPow n l) i = j := by
  have hinj : Function.Injective (fun l : Fin n => (cycShiftPow n l.val) i) := by
    intro l l' hl
    have hval : ((cycShiftPow n l.val) i).val = ((cycShiftPow n l'.val) i).val :=
      congrArg Fin.val hl
    rw [cycShiftPow_val, cycShiftPow_val] at hval
    have hmod : ((i : ℕ) + l.val) ≡ ((i : ℕ) + l'.val) [MOD n] := hval
    have hmod' : l.val ≡ l'.val [MOD n] := Nat.ModEq.add_left_cancel' _ hmod
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hmod' l.isLt l'.isLt)
  obtain ⟨l, hl⟩ := Finite.injective_iff_surjective.mp hinj j
  have hl' : (cycShiftPow n l.val) i = j := hl
  have hlne : l ≠ 0 := by
    rintro rfl
    rw [show (0 : Fin n).val = 0 from rfl, cycShiftPow, pow_zero] at hl'
    simp at hl'
    exact hij hl'
  exact ⟨l.val, Fin.pos_iff_ne_zero.mpr hlne, l.isLt, hl⟩

/-- Fixed arXiv:2503.21090v2, Lemma 29 (Appendix A). A symmetric positive
semidefinite `n × n` matrix whose generalized traces satisfy Equation (154),
`tr_l A + tr_{n-l} A = 1` for all `0 ≤ l < n`, is the all-ones matrix scaled by
`1/n`. -/
theorem source_lemma29_unique_initial {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℂ) (hpsd : A.PosSemidef) (hsym : Aᵀ = A)
    (hcon : ∀ l : ℕ, l < n → genTrace A (l : ℤ) + genTrace A ((n : ℤ) - (l : ℤ)) = 1) :
    A = (n : ℂ)⁻¹ • (Matrix.of fun (_ _ : Fin n) => (1 : ℂ)) := by
  classical
  have hn : 0 < n := NeZero.pos n
  -- symmetry of the generalized traces, from `A^T = A`
  have hgen_sym : ∀ j : ℤ, genTrace A (-j) = genTrace A j := by
    intro j
    have h := genTrace_transpose A j
    rw [hsym] at h
    exact h.symm
  -- positive semidefiniteness plus symmetry force real entries
  have him : ∀ i j : Fin n, (A i j).im = 0 := by
    intro i j
    have h1 : star (A j i) = A i j := hpsd.isHermitian.apply i j
    have h2 : A j i = A i j := by
      have hh := congrFun (congrFun hsym i) j
      simpa using hh
    rw [h2] at h1
    have := congrArg Complex.im h1
    simp at this
    linarith
  have hre : ∀ i j : Fin n, A i j = ((A i j).re : ℂ) := by
    intro i j
    have h := him i j
    apply Complex.ext
    · simp
    · simp [h]
  -- the diagonal entries are nonnegative reals
  have hdiag : ∀ i : Fin n, 0 ≤ (A i i).re := by
    intro i
    exact (Complex.le_def.mp (hpsd.diag_nonneg (i := i))).1
  -- the two-by-two principal minor bound of the appendix proof
  have hcs : ∀ i j : Fin n, (A i j).re ^ 2 ≤ (A i i).re * (A j j).re := by
    intro i j
    have hs : A j i = A i j := by
      have hh := congrFun (congrFun hsym i) j
      simpa using hh
    have hB : (A.submatrix ![i, j] ![i, j]).PosSemidef := hpsd.submatrix _
    have hd := hB.det_nonneg
    rw [Matrix.det_fin_two] at hd
    simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at hd
    have h1 := (Complex.le_def.mp hd).1
    simp only [Complex.sub_re, Complex.mul_re, Complex.zero_re] at h1
    rw [him i i, him i j, him j i, him j j] at h1
    have hs' : (A j i).re = (A i j).re := by rw [hs]
    simp only [mul_zero, sub_zero] at h1
    rw [hs'] at h1
    nlinarith
  -- `sqrt (a_ii a_jj) ≤ (a_ii + a_jj) / 2`, the appendix AM-GM step
  have hle : ∀ i j : Fin n, (A i j).re ≤ ((A i i).re + (A j j).re) / 2 := by
    intro i j
    nlinarith [hcs i j, hdiag i, hdiag j, sq_nonneg ((A i i).re - (A j j).re)]
  -- the trace is one, from Equation (154) at `l = 0`
  have htrace : (A.trace).re = 1 := by
    have h0 := hcon 0 hn
    have hz : genTrace A (n : ℤ) = 0 := by
      rw [genTrace_eq_sum_filter]
      refine Finset.sum_eq_zero fun p hp => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have h1 := p.1.isLt
      have h2 := p.2.isLt
      omega
    rw [show ((0 : ℕ) : ℤ) = 0 by norm_num, genTrace_zero, sub_zero, hz, add_zero] at h0
    rw [h0]
    simp
  have hsumdiag : (∑ i : Fin n, (A i i).re) = 1 := by
    rw [← htrace, Matrix.trace]
    simp [Complex.re_sum]
  -- every cyclic diagonal sum is one, Equation (154) in single-sum form
  have hcyc : ∀ l, 0 < l → l < n → ∑ i : Fin n, A i ((cycShiftPow n l) i) = 1 := by
    intro l _ hl
    have hb := genTrace_cyclic_bridge A l hl
    have hs : genTrace A ((l : ℤ) - (n : ℤ)) = genTrace A ((n : ℤ) - (l : ℤ)) := by
      have h := hgen_sym ((l : ℤ) - (n : ℤ))
      rw [show -((l : ℤ) - (n : ℤ)) = (n : ℤ) - (l : ℤ) by ring] at h
      exact h.symm
    rw [← hb, hs]
    exact hcon l hl
  -- the AM-GM upper bound has the same total, so the sum of the slacks is zero
  have hslack : ∀ l, 0 < l → l < n → ∀ i : Fin n,
      (A i ((cycShiftPow n l) i)).re
        = ((A i i).re + (A ((cycShiftPow n l) i) ((cycShiftPow n l) i)).re) / 2 := by
    intro l hl0 hln i
    have hbound : ∑ j ∈ (Finset.univ : Finset (Fin n)),
        ((A j j).re + (A ((cycShiftPow n l) j) ((cycShiftPow n l) j)).re) / 2 = 1 := by
      have hsplit : ∑ j ∈ (Finset.univ : Finset (Fin n)),
          ((A j j).re + (A ((cycShiftPow n l) j) ((cycShiftPow n l) j)).re) / 2
          = ((∑ j : Fin n, (A j j).re)
              + ∑ j : Fin n, (A ((cycShiftPow n l) j) ((cycShiftPow n l) j)).re) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
      rw [hsplit, Equiv.sum_comp (cycShiftPow n l) (fun j : Fin n => (A j j).re), hsumdiag]
      norm_num
    have hsum1 : ∑ j ∈ (Finset.univ : Finset (Fin n)),
        (A j ((cycShiftPow n l) j)).re = 1 := by
      have h := congrArg Complex.re (hcyc l hl0 hln)
      rw [Complex.one_re] at h
      rw [← h, Complex.re_sum]
    have hzeros : ∑ j ∈ (Finset.univ : Finset (Fin n)),
        (((A j j).re + (A ((cycShiftPow n l) j) ((cycShiftPow n l) j)).re) / 2
          - (A j ((cycShiftPow n l) j)).re) = 0 := by
      rw [Finset.sum_sub_distrib, hbound, hsum1]
      ring
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ ((A j j).re + (A ((cycShiftPow n l) j) ((cycShiftPow n l) j)).re) / 2
          - (A j ((cycShiftPow n l) j)).re :=
      fun j _ => by linarith [hle j ((cycShiftPow n l) j)]
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzeros i (Finset.mem_univ i)
    linarith
  -- tightness in AM-GM forces the two diagonal entries of each shifted pair to agree
  have hslack2 : ∀ l, 0 < l → l < n → ∀ i : Fin n,
      (A i i).re = (A ((cycShiftPow n l) i) ((cycShiftPow n l) i)).re := by
    intro l hl0 hln i
    have h2 := hslack l hl0 hln i
    have hcs' := hcs i ((cycShiftPow n l) i)
    have h2' : 2 * (A i ((cycShiftPow n l) i)).re
        = (A i i).re + (A ((cycShiftPow n l) i) ((cycShiftPow n l) i)).re := by linarith
    have hsum : (A i i).re + (A ((cycShiftPow n l) i) ((cycShiftPow n l) i)).re
        = 2 * (A i ((cycShiftPow n l) i)).re := by linarith
    have hsq : ((A i i).re - (A ((cycShiftPow n l) i) ((cycShiftPow n l) i)).re) ^ 2
        = ((A i i).re + (A ((cycShiftPow n l) i) ((cycShiftPow n l) i)).re) ^ 2
          - 4 * ((A i i).re * (A ((cycShiftPow n l) i) ((cycShiftPow n l) i)).re) := by ring
    have hsq2 : ((A i i).re + (A ((cycShiftPow n l) i) ((cycShiftPow n l) i)).re) ^ 2
        = 4 * ((A i ((cycShiftPow n l) i)).re ^ 2) := by
      rw [hsum]; ring
    have hle0 : ((A i i).re - (A ((cycShiftPow n l) i) ((cycShiftPow n l) i)).re) ^ 2 ≤ 0 := by
      rw [hsq, hsq2]
      nlinarith [hcs']
    have hz : (A i i).re - (A ((cycShiftPow n l) i) ((cycShiftPow n l) i)).re = 0 := by
      nlinarith [hle0,
        sq_nonneg ((A i i).re - (A ((cycShiftPow n l) i) ((cycShiftPow n l) i)).re)]
    linarith
  have hdiagAll : ∀ i j : Fin n, (A i i).re = (A j j).re := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · obtain ⟨l, hl0, hln, hshift⟩ := exists_cycShiftPow_of_ne hij
      have hh := hslack2 l hl0 hln i
      rw [hshift] at hh
      exact hh
  have hdiagVal : ∀ i : Fin n, (A i i).re = 1 / (n : ℝ) := by
    intro i
    have hconst : (∑ j : Fin n, (A j j).re) = (n : ℝ) * (A i i).re := by
      rw [Finset.sum_congr rfl (fun j _ => hdiagAll j i), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have htot : (n : ℝ) * (A i i).re = 1 := by
      rw [← hconst, hsumdiag]
    have hnR : (n : ℝ) ≠ 0 := by positivity
    rw [eq_div_iff hnR]
    linarith
  have hentry : ∀ i j : Fin n, (A i j).re = 1 / (n : ℝ) := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
      exact hdiagVal j
    · obtain ⟨l, hl0, hln, hshift⟩ := exists_cycShiftPow_of_ne hij
      have hh := hslack l hl0 hln i
      rw [hdiagVal i, hdiagVal ((cycShiftPow n l) i)] at hh
      rw [← hshift, hh]
      linarith
  ext i j
  rw [hre i j, hentry i j]
  simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one]
  push_cast
  simp [one_div]

end Qatlib.Papers.OrderedSearch25.MainResults
