/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.PottsPartEval07.ExactRecovery.LatticeRounding
public import Qatlib.Papers.PottsPartEval07.ExactRecovery.MacWilliams

@[expose] public section

/-!
# Executable lattice recovery and compressed code enumerators

The decoder reads an approximate weight and rounds to the prescribed integer
lattice. It does not read a desired exact weight. The code-enumerator reduction
uses an explicit partition of actual codewords into the zero word and equal-size
weight classes, as in arXiv:quant-ph/0703023v1, equations (19)--(21) and (29)--(30).
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

open scoped BigOperators
open Qatlib.Papers.PottsPartEval07.ExactRecovery

/-- Round an observed real weight to an integer index of the spacing lattice. -/
def latticeDecode (spacing observation : ℝ) : ℤ :=
  ⌊observation / spacing + 1 / 2⌋

/-- Strict half-spacing error makes the computed decoder recover the lattice index. -/
theorem latticeDecode_eq {spacing observation : ℝ} (hs : 0 < spacing) (index : ℤ)
    (he : |observation - (index : ℝ) * spacing| < spacing / 2) :
    latticeDecode spacing observation = index := by
  apply Int.floor_eq_iff.mpr
  have he' := abs_lt.mp he
  have hlo : (index : ℝ) - 1 / 2 < observation / spacing := by
    apply (lt_div_iff₀ hs).mpr
    nlinarith
  have hhi : observation / spacing < (index : ℝ) + 1 / 2 := by
    apply (div_lt_iff₀ hs).mpr
    nlinarith
  constructor <;> linarith

/-- The real part of the source finite Gauss-phase weight expression. -/
def phaseWeight {terms : ℕ} (base scale : ℝ)
    (coefficient : Fin terms → ℂ) (phase : Fin terms → ℝ) : ℝ :=
  base - scale * (∑ a, coefficient a * Complex.exp ((phase a : ℂ) * Complex.I)).re

/-- Phase errors propagate through the actual finite sum used by the decoder. -/
theorem phaseWeight_error {terms : ℕ} (base scale : ℝ) (hs : 0 ≤ scale)
    (coefficient : Fin terms → ℂ) (hc : ∀ a, ‖coefficient a‖ ≤ 1)
    (phase estimate : Fin terms → ℝ) (ε : ℝ)
    (he : ∀ a, |phase a - estimate a| ≤ ε) :
    |phaseWeight base scale coefficient phase - phaseWeight base scale coefficient estimate|
      ≤ scale * (terms * ε) := by
  have hsum := phase_sum_bound phase estimate coefficient hc ε he
  have hreal := Complex.abs_re_le_norm
    (∑ a, coefficient a * (Complex.exp ((phase a : ℂ) * Complex.I) -
      Complex.exp ((estimate a : ℂ) * Complex.I)))
  have hid : phaseWeight base scale coefficient phase -
      phaseWeight base scale coefficient estimate =
      -(scale * (∑ a, coefficient a * (Complex.exp ((phase a : ℂ) * Complex.I) -
        Complex.exp ((estimate a : ℂ) * Complex.I))).re) := by
    simp only [phaseWeight, Finset.sum_sub_distrib, mul_sub, Complex.sub_re]
    ring
  rw [hid, abs_neg, abs_mul, abs_of_nonneg hs]
  exact mul_le_mul_of_nonneg_left (hreal.trans hsum) hs

/-- A sufficient source precision bound gives exact recovery from approximate phases. -/
theorem phaseDecode_eq {terms : ℕ} (base scale spacing : ℝ)
    (hscale : 0 ≤ scale) (hs : 0 < spacing)
    (coefficient : Fin terms → ℂ) (hc : ∀ a, ‖coefficient a‖ ≤ 1)
    (phase estimate : Fin terms → ℝ) (ε : ℝ)
    (he : ∀ a, |phase a - estimate a| ≤ ε)
    (hprecision : scale * (terms * ε) < spacing / 2) (index : ℤ)
    (hformula : phaseWeight base scale coefficient phase = (index : ℝ) * spacing) :
    latticeDecode spacing (phaseWeight base scale coefficient estimate) = index := by
  apply latticeDecode_eq hs
  rw [← hformula, abs_sub_comm]
  exact (phaseWeight_error base scale hscale coefficient hc phase estimate ε he).trans_lt
    hprecision

/-- The source precision bound leaves a strict half-lattice margin for all phase terms. -/
theorem source_precision {q classes terms : ℕ} (hq : 2 ≤ q) (hc : 0 < classes)
    (ht : terms ≤ classes) (root spacing ε : ℝ) (hr : 0 < root) (hs : 0 < spacing)
    (he : ε ≤ spacing / (4 * root)) :
    (((q : ℝ) - 1) * root / ((q : ℝ) * classes)) * (terms * ε) < spacing / 2 := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hqminus : (0 : ℝ) ≤ (q : ℝ) - 1 := by linarith
  have hcR : (0 : ℝ) < classes := by exact_mod_cast hc
  have htR : (terms : ℝ) ≤ classes := by exact_mod_cast ht
  have hscale : 0 ≤ ((q : ℝ) - 1) * root / ((q : ℝ) * classes) := by positivity
  have hcoef : (((q : ℝ) - 1) * root / ((q : ℝ) * classes)) * terms ≤ root := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < (q : ℝ) * classes)).mpr
    have hm := mul_le_mul_of_nonneg_left htR
      (by positivity : 0 ≤ ((q : ℝ) - 1) * root)
    nlinarith [mul_nonneg hr.le hcR.le]
  calc (((q : ℝ) - 1) * root / ((q : ℝ) * classes)) * (terms * ε)
      ≤ (((q : ℝ) - 1) * root / ((q : ℝ) * classes)) *
          (terms * (spacing / (4 * root))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by positivity)) hscale
    _ = ((((q : ℝ) - 1) * root / ((q : ℝ) * classes)) * terms) *
        (spacing / (4 * root)) := by ring
    _ ≤ root * (spacing / (4 * root)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = spacing / 4 := by field_simp
    _ < spacing / 2 := by linarith

variable {q : ℕ} [NeZero q] {E : Type*} [Fintype E] [DecidableEq E]

/-- An explicit partition of actual codewords into zero and equally sized weight classes. -/
structure WeightClasses (C : Submodule (ZMod q) (E → ZMod q)) (classes size : ℕ) where
  /-- The partition enumerates codewords, rather than just specifying their count. -/
  encode : Option (Fin classes × Fin size) ≃ C
  /-- The distinguished class is the zero codeword. -/
  zero_word : (encode none).val = 0
  /-- Representatives are actual codewords. -/
  representative : Fin classes → C
  /-- Every member of a class has the representative's actual Hamming weight. -/
  same_weight : ∀ i j,
    hammingWeight (encode (some (i, j))).val = hammingWeight (representative i).val

/-- Evaluate a compressed homogeneous enumerator from the recovered integer weights. -/
def compressedEnum {classes : ℕ} (length size : ℕ) (weight : Fin classes → ℕ)
    (x y : ℂ) : ℂ :=
  x ^ length + (size : ℂ) * ∑ i, x ^ (length - weight i) * y ^ weight i

/-- The explicit codeword partition proves the compressed enumerator formula. -/
theorem compressedEnum_eq {classes size : ℕ}
    (C : Submodule (ZMod q) (E → ZMod q)) (partition : WeightClasses C classes size)
    (x y : ℂ) :
    compressedEnum (Fintype.card E) size
      (fun i => hammingWeight (partition.representative i).val) x y = weightEnum C x y := by
  classical
  unfold weightEnum
  rw [← Equiv.sum_comp partition.encode]
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  have hzero : hammingWeight (partition.encode none).val = 0 := by
    rw [partition.zero_word]
    simp [hammingWeight]
  simp only [hzero, partition.same_weight, tsub_zero, pow_zero, mul_one]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold compressedEnum
  rw [Finset.mul_sum]

end Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
