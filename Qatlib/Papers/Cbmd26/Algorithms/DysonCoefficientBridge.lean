/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.CoherentFreshWordBridge
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.FinRange

/-!
# Dyson word coefficients and their mass

`dysonTimeWords` enumerates reversed time-ordered sublists, and `dysonWordCoefficients` assigns
each word its multiplicity times a power of a common step coefficient. `gridWordCoefficients`
extends this construction to an arbitrary sample list, including repeated addresses, and
identifies its weighted matrix sum with the corresponding truncated ordered expansion.

The coefficient mass has a binomial expression and is at most two when the total step weight is
at most `Real.log 2`. These finite combinatorial identities provide the coefficients for the
Dyson circuit construction used with [WangEtAl2026].

## Main statements

* `dysonWordCoefficients_target`: rewrites the weighted word sum as a sum over ordered sublists.
* `gridWordCoefficients_mass`: computes the coefficient mass from the sample-list length.
* `sampled_grid_coefficients_mass_le_two`: bounds the mass of the Hamiltonian grid coefficients.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SharedAncilla.AncillaProduct
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.CoherentSim.TaylorEncoding

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section
namespace CBMD
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator List

/-- Every list of length `k` is the reverse of `List.ofFn f` for some function on `Fin k`. -/
private theorem reverse_ofFn_exists {J : Type} (k : ℕ) (w : List J)
    (hw : w.length = k) : ∃ f : Fin k → J, (List.ofFn f).reverse = w := by
  have hl : w.reverse.length = k := by simpa using! hw
  let f : Fin k → J := fun i => w.reverse.get (Fin.cast hl.symm i)
  refine ⟨f, ?_⟩
  have hf : List.ofFn f = w.reverse :=
    (List.ofFn_congr hl w.reverse.get).symm.trans (List.ofFn_get w.reverse)
  rw [hf, List.reverse_reverse]

/-- A sum over all length-`k` words weighted by their multiplicities in `ws` equals the sum of
`G` over `ws`. -/
theorem finite_word_histogram {J V : Type} [Fintype J] [DecidableEq J]
    [AddCommMonoid V] (k : ℕ) (ws : List (List J))
    (hlen : ∀ w ∈ ws, w.length = k) (G : List J → V) :
    (∑ f : Fin k → J, (ws.count (List.ofFn f).reverse) • G (List.ofFn f).reverse) =
      (ws.map G).sum := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    obtain ⟨f, rfl⟩ := reverse_ofFn_exists k w (hlen w List.mem_cons_self)
    have ht : ∀ w ∈ ws, w.length = k := fun w hw => hlen w (List.mem_cons_of_mem _ hw)
    simp only [List.count_cons, beq_iff_eq, List.reverse_inj, List.ofFn_inj,
      add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
      List.map_cons, List.sum_cons]
    rw [ih ht]
    simp [add_comm]

/-- Mapping a function over a list commutes with enumerating sublists of a fixed length. -/
private theorem sublistsLen_map {J H : Type} (f : J → H) (l : List J) (k : ℕ) :
    (l.map f).sublistsLen k = (l.sublistsLen k).map (List.map f) := by
  induction l generalizing k with
  | nil => cases k <;> simp
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ k => simp [List.sublistsLen_succ_cons, ih, List.map_map, Function.comp_def]

/-- The list of length-`k` sublists of the reversed time grid `List.finRange M`. -/
def dysonTimeWords (M k : ℕ) : List (List (Fin M)) :=
  (List.finRange M).reverse.sublistsLen k

/-- The coefficient of a word of degree at most `K`, given by its multiplicity in
`dysonTimeWords` times `z` to its degree. -/
def dysonWordCoefficients (M K : ℕ) (z : ℂ)
    (w : Σ l : Fin (K + 1), Fin l.val → Fin M) : ℂ :=
  ((dysonTimeWords M w.1.val).count (List.ofFn w.2).reverse : ℂ) * z ^ w.1.val

/-- A reversed word occurs in `dysonTimeWords` exactly once when its unreversed list is a
sublist of `List.finRange M`, and otherwise occurs zero times. -/
theorem dyson_word_count_mask (M k : ℕ) (f : Fin k → Fin M) :
    (dysonTimeWords M k).count (List.ofFn f).reverse =
      if List.ofFn f <+ List.finRange M then 1 else 0 := by
  have hn : (dysonTimeWords M k).Nodup :=
    List.nodup_sublistsLen k (List.nodup_reverse.mpr (List.nodup_finRange M))
  have hm : (List.ofFn f).reverse ∈ dysonTimeWords M k ↔
      List.ofFn f <+ List.finRange M := by
    simp [dysonTimeWords, List.mem_sublistsLen]
  by_cases hf : List.ofFn f <+ List.finRange M
  · rw [if_pos hf]
    exact List.count_eq_one_of_mem hn (hm.mpr hf)
  · rw [if_neg hf]
    exact List.count_eq_zero.mpr (fun h => hf (hm.mp h))

/-- The Dyson coefficient is `z` to the word's degree for an increasing grid sublist, and is
zero otherwise. -/
theorem dysonWordCoefficients_mask (M K : ℕ) (z : ℂ)
    (w : Σ l : Fin (K + 1), Fin l.val → Fin M) :
    dysonWordCoefficients M K z w =
      if List.ofFn w.2 <+ List.finRange M then z ^ w.1.val else 0 := by
  rw [dysonWordCoefficients, dyson_word_count_mask]
  split_ifs <;> simp

/-- The sum of length-`k` word multiplicities times a constant `r` is `M.choose k` times `r`. -/
private theorem dyson_count_mass_degree (M k : ℕ) (r : ℝ) :
    (∑ f : Fin k → Fin M,
      ((dysonTimeWords M k).count (List.ofFn f).reverse : ℝ) * r) =
      (M.choose k : ℝ) * r := by
  have h := finite_word_histogram k (dysonTimeWords M k)
    (fun w hw => (List.mem_sublistsLen.mp hw).2) (fun _ => r)
  simpa [nsmul_eq_mul, dysonTimeWords] using! h

/-- The mass of the Dyson coefficients is the sum over degrees through `K` of `M.choose k` times
`‖z‖ ^ k`. -/
theorem dysonWordCoefficients_mass (M K : ℕ) (z : ℂ) :
    coefficientMass (dysonWordCoefficients M K z) =
      ∑ k : Fin (K + 1), (M.choose k.val : ℝ) * ‖z‖ ^ k.val := by
  simp only [coefficientMass, Fintype.sum_sigma, dysonWordCoefficients,
    norm_mul, Complex.norm_natCast, norm_pow]
  exact Finset.sum_congr rfl (fun k _ => dyson_count_mass_degree M k.val _)

section BranchProducts
variable {J I : Type} [Fintype I] [DecidableEq I]

/-- Before the word length is reached, the Taylor branch equals the product of the first `n`
matrices in reverse order. -/
private theorem taylorBranchWord_prefix (B : J → Matrix I I ℂ) (K : ℕ)
    (w : Σ l : Fin (K + 1), Fin l.val → J) (n : ℕ) (hn : n ≤ K) (hl : n ≤ w.1.val) :
    taylorBranchWord B K n hn (.inl w) =
      ((List.ofFn (fun j : Fin n => B (w.2 ⟨j.val, Nat.lt_of_lt_of_le j.isLt hl⟩))).reverse).prod := by
  induction n with
  | zero => simp [taylorBranchWord]
  | succ n ih =>
    rw [taylorBranchWord, taylorBranchStep, dif_pos (Nat.lt_of_succ_le hl),
      List.ofFn_succ_last, List.reverse_append, List.prod_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons,
      List.prod_nil, Matrix.mul_one]
    rw [ih (Nat.le_of_succ_le hn) (Nat.le_trans (Nat.le_succ n) hl)]
    rfl

/-- A Taylor branch stops changing after its number of steps reaches the encoded word length. -/
private theorem taylorBranchWord_after_length (B : J → Matrix I I ℂ) (K : ℕ)
    (w : Σ l : Fin (K + 1), Fin l.val → J) (n : ℕ) (hn : n ≤ K) (hl : w.1.val ≤ n) :
    taylorBranchWord B K n hn (.inl w) =
      taylorBranchWord B K w.1.val (Nat.le_of_lt_succ w.1.isLt) (.inl w) := by
  revert hn
  induction n, hl using Nat.le_induction with
  | base => intro hn; rfl
  | succ n hle ih =>
    intro hn
    rw [taylorBranchWord, taylorBranchStep, dif_neg (Nat.not_lt.mpr hle), Matrix.one_mul]
    exact ih (Nat.le_of_succ_le hn)

/-- The completed Taylor branch is the matrix product obtained by mapping `B` over the reversed
encoded word. -/
theorem taylorBranchWord_core_list (B : J → Matrix I I ℂ) (K : ℕ)
    (w : Σ l : Fin (K + 1), Fin l.val → J) :
    taylorBranchWord B K K le_rfl (.inl w) = ((List.ofFn w.2).reverse.map B).prod := by
  rw [taylorBranchWord_after_length B K w K le_rfl (Nat.le_of_lt_succ w.1.isLt)]
  rw [taylorBranchWord_prefix B K w w.1.val (Nat.le_of_lt_succ w.1.isLt) le_rfl]
  simp only [List.map_reverse, List.map_ofFn]
  rfl

/-- Multiplying every matrix in a list by the same scalar factors its power at the list length
out of the product. -/
private theorem list_product_uniform_smul (B : J → Matrix I I ℂ) (z : ℂ) (w : List J) :
    (w.map (fun j => z • B j)).prod = z ^ w.length • (w.map B).prod := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, ih,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ]

end BranchProducts

section Coefficients
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The degree-`k` Dyson sum weighted by word multiplicities equals the sum of products over all
reversed grid sublists of length `k`. -/
private theorem dyson_degree_histogram (M k : ℕ) (z : ℂ) (B : Fin M → Matrix I I ℂ) :
    (∑ f : Fin k → Fin M,
      (((dysonTimeWords M k).count (List.ofFn f).reverse : ℂ) * z ^ k) •
        ((List.ofFn f).reverse.map B).prod) =
      ((dysonTimeWords M k).map (fun w => (w.map (fun j => z • B j)).prod)).sum := by
  have hh := finite_word_histogram k (dysonTimeWords M k)
    (fun w hw => (List.mem_sublistsLen.mp hw).2)
    (fun w => z ^ k • (w.map B).prod)
  simp only [← smul_smul, Nat.cast_smul_eq_nsmul] at ⊢
  rw [hh]
  apply congrArg List.sum
  apply List.map_congr_left
  intro w hw
  rw [list_product_uniform_smul, (List.mem_sublistsLen.mp hw).2]

/-- The weighted Taylor branch sum with Dyson coefficients equals the sum of scaled matrix
products over all reversed grid sublists of degrees through `K`. -/
theorem dysonWordCoefficients_target (M K : ℕ) (z : ℂ) (B : Fin M → Matrix I I ℂ) :
    (∑ w : (Σ l : Fin (K + 1), Fin l.val → Fin M),
      dysonWordCoefficients M K z w • taylorBranchWord B K K le_rfl (.inl w)) =
      ∑ k : Fin (K + 1),
        ((dysonTimeWords M k.val).map (fun w => (w.map (fun j => z • B j)).prod)).sum := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  simpa only [dysonWordCoefficients, taylorBranchWord_core_list] using!
    dyson_degree_histogram M k.val z B

end Coefficients

/-- For nonnegative `r` with `M * r ≤ a`, the binomial term `M.choose k * r ^ k` is bounded by
`a ^ k / k.factorial`. -/
private theorem binomial_degree_mass_le (M k : ℕ) (r a : ℝ)
    (hr : 0 ≤ r) (hma : (M : ℝ) * r ≤ a) :
    (M.choose k : ℝ) * r ^ k ≤ a ^ k / (k.factorial : ℝ) := by
  have hc : (M.choose k : ℝ) * (k.factorial : ℝ) ≤ (M : ℝ) ^ k := by
    have h := Nat.descFactorial_le_pow M k
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h
    exact_mod_cast (by simpa only [Nat.mul_comm] using! h)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < k.factorial)).mpr
  calc
    (M.choose k : ℝ) * r ^ k * (k.factorial : ℝ) =
      ((M.choose k : ℝ) * (k.factorial : ℝ)) * r ^ k := by ring
    _ ≤ (M : ℝ) ^ k * r ^ k := mul_le_mul_of_nonneg_right hc (pow_nonneg hr k)
    _ = ((M : ℝ) * r) ^ k := (mul_pow _ _ _).symm
    _ ≤ a ^ k := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hr) hma k

/-- If `M * ‖z‖ ≤ a`, the Dyson coefficient mass is bounded by the exponential series truncated
at degree `K`. -/
theorem dysonWordCoefficients_mass_le_factorial (M K : ℕ) (z : ℂ) (a : ℝ)
    (hma : (M : ℝ) * ‖z‖ ≤ a) :
    coefficientMass (dysonWordCoefficients M K z) ≤
      ∑ k ∈ Finset.range (K + 1), a ^ k / (k.factorial : ℝ) := by
  rw [dysonWordCoefficients_mass, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_le_sum (fun k _ => binomial_degree_mass_le M k.val ‖z‖ a (norm_nonneg _) hma)

/-- If the total step weight is at most a nonnegative `a ≤ Real.log 2`, the Dyson coefficient
mass is at most two. -/
theorem dysonWordCoefficients_mass_le_two (M K : ℕ) (z : ℂ) (a : ℝ)
    (ha : 0 ≤ a) (hma : (M : ℝ) * ‖z‖ ≤ a) (hlog : a ≤ Real.log 2) :
    coefficientMass (dysonWordCoefficients M K z) ≤ 2 := by
  calc
    _ ≤ ∑ k ∈ Finset.range (K + 1), a ^ k / (k.factorial : ℝ) :=
      dysonWordCoefficients_mass_le_factorial M K z a hma
    _ ≤ Real.exp a := Real.sum_le_exp_of_nonneg ha _
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hlog
    _ = 2 := Real.exp_log (by norm_num)

section AddressLists
variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

/-- The coefficient of a sampled word, given by its multiplicity among reversed sublists of
`samples` times `z` to its degree. -/
def gridWordCoefficients (samples : List J) (K : ℕ) (z : ℂ)
    (w : Σ l : Fin (K + 1), Fin l.val → J) : ℂ :=
  ((samples.reverse.sublistsLen w.1.val).count (List.ofFn w.2).reverse : ℂ) * z ^ w.1.val

omit [Fintype J] [Fintype I] [DecidableEq I] in

/-- For a sample list without duplicates, a word has coefficient `z` to its degree exactly when
its list is a sublist of `samples`, and zero otherwise. -/
theorem gridWordCoefficients_mask (samples : List J) (K : ℕ) (z : ℂ)
    (hs : samples.Nodup) (w : Σ l : Fin (K + 1), Fin l.val → J) :
    gridWordCoefficients samples K z w =
      if List.ofFn w.2 <+ samples then z ^ w.1.val else 0 := by
  have hn := List.nodup_sublistsLen w.1.val (List.nodup_reverse.mpr hs)
  have hm : (List.ofFn w.2).reverse ∈ samples.reverse.sublistsLen w.1.val ↔
      List.ofFn w.2 <+ samples := by simp [List.mem_sublistsLen]
  unfold gridWordCoefficients
  by_cases hw : List.ofFn w.2 <+ samples
  · rw [if_pos hw, List.count_eq_one_of_mem hn (hm.mpr hw)]
    simp
  · rw [if_neg hw, List.count_eq_zero.mpr (fun h => hw (hm.mp h))]
    simp

omit [Fintype I] [DecidableEq I] in

/-- The grid coefficient mass is the sum over degrees through `K` of the binomial coefficient of
`samples.length` times the corresponding power of `‖z‖`. -/
theorem gridWordCoefficients_mass (samples : List J) (K : ℕ) (z : ℂ) :
    coefficientMass (gridWordCoefficients samples K z) =
      ∑ k : Fin (K + 1), (samples.length.choose k.val : ℝ) * ‖z‖ ^ k.val := by
  simp only [coefficientMass, Fintype.sum_sigma, gridWordCoefficients,
    norm_mul, Complex.norm_natCast, norm_pow]
  apply Finset.sum_congr rfl
  intro k _
  have h := finite_word_histogram k.val (samples.reverse.sublistsLen k.val)
    (fun w hw => (List.mem_sublistsLen.mp hw).2) (fun _ => ‖z‖ ^ k.val)
  simpa [nsmul_eq_mul] using! h

omit [Fintype I] [DecidableEq I] in

/-- The grid coefficient mass is at most two when `samples.length * ‖z‖` is bounded by a
nonnegative `a ≤ Real.log 2`. -/
theorem gridWordCoefficients_mass_le_two (samples : List J) (K : ℕ) (z : ℂ) (a : ℝ)
    (ha : 0 ≤ a) (hma : (samples.length : ℝ) * ‖z‖ ≤ a) (hlog : a ≤ Real.log 2) :
    coefficientMass (gridWordCoefficients samples K z) ≤ 2 := by
  rw [gridWordCoefficients_mass]
  calc
    _ ≤ ∑ k : Fin (K + 1), a ^ k.val / (k.val.factorial : ℝ) :=
      Finset.sum_le_sum (fun k _ => binomial_degree_mass_le samples.length k.val ‖z‖ a
        (norm_nonneg _) hma)
    _ = ∑ k ∈ Finset.range (K + 1), a ^ k / (k.factorial : ℝ) := Fin.sum_univ_eq_sum_range (fun k : ℕ => a ^ k / (k.factorial : ℝ)) (K + 1)
    _ ≤ Real.exp a := Real.sum_le_exp_of_nonneg ha _
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hlog
    _ = 2 := Real.exp_log (by norm_num)

/-- The weighted Taylor branch sum with grid coefficients equals the sum of products over
reversed sublists of the scaled sample matrices. -/
theorem gridWordCoefficients_target (samples : List J) (K : ℕ) (z : ℂ)
    (B : J → Matrix I I ℂ) :
    (∑ w : (Σ l : Fin (K + 1), Fin l.val → J),
      gridWordCoefficients samples K z w • taylorBranchWord B K K le_rfl (.inl w)) =
      ∑ k : Fin (K + 1),
        ((((samples.map (fun j => z • B j)).reverse).sublistsLen k.val).map List.prod).sum := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  simp only [gridWordCoefficients, taylorBranchWord_core_list,
    ← smul_smul, Nat.cast_smul_eq_nsmul]
  have hh := finite_word_histogram k.val (samples.reverse.sublistsLen k.val)
    (fun w hw => (List.mem_sublistsLen.mp hw).2)
    (fun w => z ^ k.val • (w.map B).prod)
  rw [hh]
  rw [← List.map_reverse, sublistsLen_map, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro w hw
  simp only [Function.comp_apply, list_product_uniform_smul, (List.mem_sublistsLen.mp hw).2]

end AddressLists

/-- The common complex grid coefficient `-i Λ t / M` for Hamiltonian samples scaled by `Λ`. -/
def gridStepCoefficient (t Λ : ℝ) (M : ℕ) : ℂ :=
  -((t / (M : ℝ) : ℝ) : ℂ) * (Complex.I * (Λ : ℂ))

/-- For nonnegative `t` and `Λ` and positive `M`, multiplying the grid-step coefficient norm by
`M` gives `Λ * t`. -/
theorem gridStepCoefficient_norm (t Λ : ℝ) (M : ℕ)
    (ht : 0 ≤ t) (hΛ : 0 ≤ Λ) (hM : 0 < M) :
    (M : ℝ) * ‖gridStepCoefficient t Λ M‖ = Λ * t := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  simp only [gridStepCoefficient, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg ht hMr.le), Complex.norm_I,
    abs_of_nonneg hΛ, one_mul]
  field_simp

section SampleRelation
variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

omit [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I] in

/-- When `Λ • B (address j)` is the Hamiltonian at grid point `j`, scaling this block by
`gridStepCoefficient` gives the corresponding Hamiltonian evolution increment. -/
theorem gridStepCoefficient_sample (M : ℕ) (t Λ : ℝ) (address : Fin M → J)
    (B : J → Matrix I I ℂ) (H : ℝ → Matrix I I ℂ)
    (hB : ∀ j, (Λ : ℂ) • B (address j) = H (t * j.val / M)) (j : Fin M) :
    gridStepCoefficient t Λ M • B (address j) =
      -((t / (M : ℝ) : ℝ) : ℂ) • (Complex.I • H (t * j.val / M)) := by
  rw [← hB j, smul_smul, smul_smul]
  congr 1
  unfold gridStepCoefficient
  ring

omit [Fintype I] [DecidableEq I] in

/-- For nonnegative time and scale, a positive grid size, and `Λ * t ≤ Real.log 2`, the sampled
grid coefficients have mass at most two. -/
theorem sampled_grid_coefficients_mass_le_two (M K : ℕ) (t Λ : ℝ) (address : Fin M → J)
    (ht : 0 ≤ t) (hΛ : 0 ≤ Λ) (hM : 0 < M) (hlog : Λ * t ≤ Real.log 2) :
    coefficientMass (gridWordCoefficients (List.ofFn address) K (gridStepCoefficient t Λ M)) ≤ 2 := by
  apply gridWordCoefficients_mass_le_two _ _ _ (Λ * t) (mul_nonneg hΛ ht) _ hlog
  rw [List.length_ofFn, gridStepCoefficient_norm t Λ M ht hΛ hM]

end SampleRelation
end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
