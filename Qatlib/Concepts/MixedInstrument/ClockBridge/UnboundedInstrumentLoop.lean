/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.ObservedInstrument
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail

/-!
# Unbounded Boolean instrument loops

This module defines the continuation, first-halting, and partial halting maps of a Boolean
instrument loop. Their traces partition halted and pending mass, and their entrywise sums yield
a completely positive, trace non-increasing terminal map.

The stopping law `loopStoppingLaw` includes an explicit never-halting outcome. Its finite-time
masses are first-halting traces, and its nontermination mass is the limit of pending mass. The
instrument and completely positive map framework is described in [Watrous2018].

## Main statements

* `instrument_loop_finite_complete_positivity`: proves positivity properties of finite maps.
* `instrument_loop_terminal_cp_map_actual_limit`: constructs the terminal map as a limit.
* `instrument_loop_stopping_law_and_never_mass`: identifies the stopping and nontermination
  masses.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MixedInstrument.ClockBridge

open Matrix
open scoped ComplexOrder ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- A sequence of finite complex matrices converges exactly when each matrix entry converges. -/
theorem tendsto_matrix_iff_entrywise {m n : Type} [Fintype m] [Fintype n]
    {f : ℕ → Matrix m n ℂ} {g : Matrix m n ℂ} :
    Filter.Tendsto f Filter.atTop (nhds g) ↔
    ∀ i j, Filter.Tendsto (fun k => f k i j) Filter.atTop (nhds (g i j)) := by
  constructor
  · intro h i j
    exact ((continuous_id.matrix_elem i j).tendsto (x := g)).comp h
  · intro h
    have key : Filter.Tendsto (fun k => (fun i j => f k i j : m → n → ℂ))
        Filter.atTop (nhds (fun i j => g i j)) :=
      tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => h i j
    exact key

/-- The traces of a convergent sequence of finite complex square matrices converge to the trace
of the limit. -/
theorem tendsto_matrix_trace {m : Type} [Fintype m]
    {f : ℕ → Matrix m m ℂ} {g : Matrix m m ℂ}
    (h : Filter.Tendsto f Filter.atTop (nhds g)) :
    Filter.Tendsto (fun k => Matrix.trace (f k)) Filter.atTop (nhds (Matrix.trace g)) := by
  have he : ∀ i j, Filter.Tendsto (fun k => f k i j) Filter.atTop (nhds (g i j)) :=
    (tendsto_matrix_iff_entrywise).mp h
  exact tendsto_finsetSum _ fun i _ => he i i

/-- A finite sum of complex series with specified sums has sum equal to the finite sum of those
sums. -/
theorem hasSum_finset_sum {ι : Type} (s : Finset ι) (f : ι → ℕ → ℂ) (g : ι → ℂ)
    (h : ∀ p ∈ s, HasSum (f p) (g p)) :
    HasSum (fun k => ∑ p ∈ s, f p k) (∑ p ∈ s, g p) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact hasSum_zero
  | insert p s hp ih =>
      simp only [Finset.sum_insert hp]
      exact (h p (Finset.mem_insert_self p s)).add
        (ih fun q hq => h q (Finset.mem_insert_of_mem hq))

/-- A nonnegative complex number equals the embedding of its real part. -/
private theorem complex_eq_ofReal_of_nonneg {z : ℂ} (hz : 0 ≤ z) : z = ((z.re : ℂ)) := by
  obtain ⟨hre, him⟩ := RCLike.nonneg_iff.mp hz
  refine Complex.ext ?_ ?_
  · exact (Complex.ofReal_re z.re).symm
  · rw [Complex.ofReal_im]
    exact him

/-- The real part of the product of two embedded real numbers is their real product. -/
private theorem re_ofReal_mul (t B : ℝ) : ((((t : ℝ) : ℂ)) * ((B : ℂ))).re = t * B := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.ofReal_im]
  ring

/-- Taking the real part of the displayed difference of embedded real products gives `a - t *
B`. -/
private theorem re_ofReal_sub_mul (a t B : ℝ) :
    ((((a : ℝ) : ℂ)) - ((t : ℝ) : ℂ) * ((B : ℂ))).re = a - t * B := by
  rw [Complex.sub_re, Complex.ofReal_re, re_ofReal_mul]

/-- A nonnegative complex number has nonnegative real part. -/
theorem complex_re_nonneg_of_le {z : ℂ} (hz : 0 ≤ z) : 0 ≤ z.re :=
  (RCLike.nonneg_iff.mp hz).1

/-- In a positive semidefinite `2 × 2` matrix, the squared norm of the off-diagonal entry is at
most the product of the real diagonal entries. -/
private theorem posSemidef_two_abs_sq_le {S : Matrix (Fin 2) (Fin 2) ℂ} (hS : S.PosSemidef) :
    Complex.normSq (S 0 1) ≤ (S 0 0).re * (S 1 1).re := by
  classical
  have hTF : S 1 0 = (starRingEnd ℂ) (S 0 1) := by
    have hentry := (Matrix.IsHermitian.ext_iff.mp hS.1) 1 0
    exact hentry.symm
  have henn : (0 : ℂ) ≤ S 0 0 := hS.diag_nonneg
  have hdnn : (0 : ℂ) ≤ S 1 1 := hS.diag_nonneg
  have han : S 0 0 = ((S 0 0).re : ℂ) := complex_eq_ofReal_of_nonneg henn
  have hdn : S 1 1 = ((S 1 1).re : ℂ) := complex_eq_ofReal_of_nonneg hdnn
  have hreA : (0 : ℝ) ≤ (S 0 0).re := (RCLike.nonneg_iff.mp henn).1
  have hreD : (0 : ℝ) ≤ (S 1 1).re := (RCLike.nonneg_iff.mp hdnn).1
  have hprod1 : S 0 1 * (starRingEnd ℂ) (S 0 1) = ((Complex.normSq (S 0 1) : ℂ)) := by
    have h := Complex.normSq_eq_conj_mul_self (z := (starRingEnd ℂ) (S 0 1))
    rw [Complex.conj_conj, Complex.normSq_conj] at h
    exact h.symm
  have hprod2 : (starRingEnd ℂ) (S 0 1) * S 0 1 = ((Complex.normSq (S 0 1) : ℂ)) := by
    rw [← Complex.normSq_eq_conj_mul_self]

  have hval : ∀ w : ℂ, star (fun k : Fin 2 => if k = 0 then (1 : ℂ) else -w) ⬝ᵥ
      (S *ᵥ (fun k : Fin 2 => if k = 0 then (1 : ℂ) else -w))
      = S 0 0 - S 0 1 * w - (starRingEnd ℂ) w * S 1 0
        + (starRingEnd ℂ) w * w * S 1 1 := by
    intro w
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Pi.star_apply]
    norm_num
    ring
  have hquad : ∀ w : ℂ, (0 : ℂ) ≤ S 0 0 - S 0 1 * w
      - (starRingEnd ℂ) w * S 1 0 + (starRingEnd ℂ) w * w * S 1 1 := by
    intro w
    rw [← hval w]
    exact hS.dotProduct_mulVec_nonneg _
  rcases eq_or_ne (S 1 1).re 0 with h0 | h0
  · have hd0 : S 1 1 = 0 := by
      rw [hdn, h0, Complex.ofReal_zero]
    have hb0 : S 0 1 = 0 := by
      by_contra hne
      have hBpos : (0 : ℝ) < Complex.normSq (S 0 1) := Complex.normSq_pos.mpr hne
      have hBne : (0 : ℝ) ≠ 2 * Complex.normSq (S 0 1) := by
        intro hcontra
        linarith
      set t : ℝ := ((S 0 0).re + 1) / (2 * Complex.normSq (S 0 1)) with ht
      set w : ℂ := (((t : ℝ) : ℂ)) * (starRingEnd ℂ) (S 0 1) with hw
      have h1 := hquad w
      rw [hd0] at h1
      simp only [mul_zero, add_zero] at h1
      rw [hTF] at h1
      have hc : (starRingEnd ℂ) w = (((t : ℝ) : ℂ)) * S 0 1 := by
        rw [hw, map_mul, Complex.conj_ofReal, Complex.conj_conj]
      rw [hc] at h1
      have hnorm1 : S 0 1 * w = (((t : ℝ) : ℂ)) * ((Complex.normSq (S 0 1) : ℂ)) := by
        rw [hw, ← mul_assoc, mul_comm (S 0 1) (((t : ℝ) : ℂ)), mul_assoc, hprod1]
      have hnorm2 : (((t : ℝ) : ℂ)) * S 0 1 * (starRingEnd ℂ) (S 0 1)
          = (((t : ℝ) : ℂ)) * ((Complex.normSq (S 0 1) : ℂ)) := by
        rw [mul_assoc, hprod1]
      rw [hnorm1, hnorm2] at h1
      have htarget : S 0 0 - ((2 * t : ℝ) : ℂ) * ((Complex.normSq (S 0 1) : ℂ))
          = S 0 0 - (((t : ℝ) : ℂ)) * ((Complex.normSq (S 0 1) : ℂ))
            - (((t : ℝ) : ℂ)) * ((Complex.normSq (S 0 1) : ℂ)) := by
        push_cast
        ring
      rw [← htarget] at h1
      have hre := complex_re_nonneg_of_le h1
      rw [han, re_ofReal_sub_mul] at hre
      rw [ht] at hre
      rw [show 2 * (((S 0 0).re + 1) / (2 * Complex.normSq (S 0 1))) * Complex.normSq (S 0 1)
          = (S 0 0).re + 1 from by field_simp] at hre
      linarith
    rw [h0, mul_zero]
    rw [hb0, Complex.normSq_zero]
  · have hDpos : (0 : ℝ) < (S 1 1).re := lt_of_le_of_ne hreD (Ne.symm h0)
    set d : ℝ := (S 1 1).re with hddef
    have hdne : (((d : ℝ) : ℂ)) ≠ 0 := fun h => h0 (Complex.ofReal_eq_zero.mp h)
    have hdS : S 1 1 = ((d : ℝ) : ℂ) := hdn
    set w : ℂ := (starRingEnd ℂ) (S 0 1) / (((d : ℝ) : ℂ)) with hw
    have h1 := hquad w
    rw [hdS] at h1
    have hc : (starRingEnd ℂ) w = S 0 1 / (((d : ℝ) : ℂ)) := by
      rw [hw, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
    rw [hc, hTF] at h1
    have ht1 : S 0 1 * w = ((Complex.normSq (S 0 1) : ℂ)) / (((d : ℝ) : ℂ)) := by
      have hsplit : S 0 1 * w
          = (S 0 1 * (starRingEnd ℂ) (S 0 1)) / (((d : ℝ) : ℂ)) := by
        rw [hw]; ring
      rw [hsplit, hprod1]
    have ht2 : S 0 1 / (((d : ℝ) : ℂ)) * (starRingEnd ℂ) (S 0 1)
        = ((Complex.normSq (S 0 1) : ℂ)) / (((d : ℝ) : ℂ)) := by
      have hsplit : S 0 1 / (((d : ℝ) : ℂ)) * (starRingEnd ℂ) (S 0 1)
          = (S 0 1 * (starRingEnd ℂ) (S 0 1)) / (((d : ℝ) : ℂ)) := by ring
      rw [hsplit, hprod1]
    have ht3 : S 0 1 / (((d : ℝ) : ℂ)) * w * (((d : ℝ) : ℂ))
        = ((Complex.normSq (S 0 1) : ℂ)) / (((d : ℝ) : ℂ)) := by
      have hsplit : S 0 1 / (((d : ℝ) : ℂ)) * w * (((d : ℝ) : ℂ))
          = (S 0 1 * (starRingEnd ℂ) (S 0 1)) / (((d : ℝ) : ℂ)) := by
        rw [hw]
        field_simp
      rw [hsplit, hprod1]
    rw [ht1, ht2, ht3] at h1
    have htarget : S 0 0 - ((Complex.normSq (S 0 1) : ℂ)) / (((d : ℝ) : ℂ))
        = S 0 0 - ((Complex.normSq (S 0 1) : ℂ)) / (((d : ℝ) : ℂ))
          - ((Complex.normSq (S 0 1) : ℂ)) / (((d : ℝ) : ℂ))
          + ((Complex.normSq (S 0 1) : ℂ)) / (((d : ℝ) : ℂ)) := by ring
    rw [← htarget] at h1
    have hrediv : (((Complex.normSq (S 0 1) : ℂ)) / (((d : ℝ) : ℂ))).re
        = Complex.normSq (S 0 1) / d := by
      rw [← Complex.ofReal_div, Complex.ofReal_re]
    have hre := complex_re_nonneg_of_le h1
    rw [han, Complex.sub_re, Complex.ofReal_re, hrediv] at hre
    exact (div_le_iff₀ hDpos).mp (by linarith : Complex.normSq (S 0 1) / d ≤ (S 0 0).re)

/-- The squared norm of an entry of a positive semidefinite matrix is at most the product of its
two real diagonal entries. -/
theorem posSemidef_abs_sq_le {m : Type} [Fintype m] {N : Matrix m m ℂ}
    (hN : N.PosSemidef) (i j : m) :
    Complex.normSq (N i j) ≤ (N i i).re * (N j j).re := by
  classical
  set e : Fin 2 → m := fun k => if k = 0 then i else j with he
  set S : Matrix (Fin 2) (Fin 2) ℂ := N.submatrix e e with hSdef
  have hS : S.PosSemidef := hN.submatrix e
  have hb : S 0 1 = N i j := by simp [hSdef, he]
  have ha : S 0 0 = N i i := by simp [hSdef, he]
  have hd : S 1 1 = N j j := by simp [hSdef, he]
  have core := posSemidef_two_abs_sq_le hS
  rwa [hb, ha, hd] at core

/-- The norm of any entry of a positive semidefinite operator is at most the real part of its
trace. -/
private theorem posSemidef_abs_entry_le_trace {D : ℕ} {N : Operator D}
    (hN : N.PosSemidef) (i j : Fin D) :
    ‖N i j‖ ≤ (Matrix.trace N).re := by
  have hdiag : ∀ k : Fin D, (0 : ℂ) ≤ N k k := fun _ => hN.diag_nonneg
  have hA : (0 : ℝ) ≤ (N i i).re := (RCLike.nonneg_iff.mp (hdiag i)).1
  have hB : (0 : ℝ) ≤ (N j j).re := (RCLike.nonneg_iff.mp (hdiag j)).1
  have hT : (0 : ℝ) ≤ (Matrix.trace N).re := (RCLike.nonneg_iff.mp hN.trace_nonneg).1
  have htracere : (Matrix.trace N).re = ∑ k : Fin D, (N k k).re := by
    simp [Matrix.trace]
  have hminor : ‖N i j‖ ^ 2 ≤ (N i i).re * (N j j).re := by
    have h := posSemidef_abs_sq_le hN i j
    rwa [← Complex.sq_norm] at h
  have ham : (N i i).re * (N j j).re ≤ (((N i i).re + (N j j).re) / 2) ^ 2 := by
    nlinarith [sq_nonneg ((N i i).re - (N j j).re)]
  have hAT : (N i i).re ≤ (Matrix.trace N).re := by
    rw [htracere]
    exact Finset.single_le_sum (fun k _ => (RCLike.nonneg_iff.mp (hdiag k)).1)
      (Finset.mem_univ i)
  have hBT : (N j j).re ≤ (Matrix.trace N).re := by
    rw [htracere]
    exact Finset.single_le_sum (fun k _ => (RCLike.nonneg_iff.mp (hdiag k)).1)
      (Finset.mem_univ j)
  have hmid : ‖N i j‖ ≤ ((N i i).re + (N j j).re) / 2 := by
    have h2 : ‖N i j‖ ^ 2 ≤ (((N i i).re + (N j j).re) / 2) ^ 2 := le_trans hminor ham
    have h3 : |‖N i j‖| ≤ |((N i i).re + (N j j).re) / 2| := sq_le_sq.mp h2
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at h3
  calc ‖N i j‖ ≤ ((N i i).re + (N j j).re) / 2 := hmid
    _ ≤ (Matrix.trace N).re := by linarith

set_option maxHeartbeats 800000 in

/-- The entrywise sum of a series of positive semidefinite matrices is positive semidefinite
when every entry series is summable. -/
theorem posSemidef_of_tsum_entries {m : Type} [Fintype m] {F : ℕ → Matrix m m ℂ}
    (hF : ∀ k, (F k).PosSemidef) (hs : ∀ i j, Summable fun k => F k i j) :
    (Matrix.of fun i j => ∑' k, F k i j).PosSemidef := by
  classical
  set M : Matrix m m ℂ := Matrix.of fun i j => ∑' k, F k i j with hMdef
  have hMapp : ∀ p q : m, M p q = ∑' k, F k p q := fun p q => rfl
  have hsum : ∀ p q : m, HasSum (fun k => F k p q) (M p q) :=
    fun p q => (hMapp p q) ▸ (hs p q).hasSum
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · show M.conjTranspose = M
    ext p q
    rw [Matrix.conjTranspose_apply, hMapp, hMapp]
    show (starRingEnd ℂ) (∑' k, F k q p) = ∑' k, F k p q
    have hconj : HasSum (fun k => (starRingEnd ℂ) (F k q p))
        ((starRingEnd ℂ) (∑' k, F k q p)) :=
      ((hs q p).hasSum).map (starRingEnd ℂ) (by fun_prop)
    rw [← hconj.tsum_eq]
    exact tsum_congr fun k => (Matrix.IsHermitian.ext_iff.mp (hF k).1) p q
  · intro x
    have hquad (A : Matrix m m ℂ) :
        star x ⬝ᵥ (A *ᵥ x) = ∑ p : m, ∑ q : m, star (x p) * A p q * x q := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    have hint : HasSum (fun k => star x ⬝ᵥ (F k *ᵥ x)) (star x ⬝ᵥ (M *ᵥ x)) := by
      rw [hquad M]
      have hcongr : (fun k => star x ⬝ᵥ (F k *ᵥ x))
          = fun k => ∑ p : m, ∑ q : m, star (x p) * F k p q * x q := funext fun k => hquad (F k)
      rw [hcongr]
      refine hasSum_finset_sum _ _ _ fun p _ => hasSum_finset_sum _ _ _ fun q _ => ?_
      rw [hMapp p q]
      exact ((hs p q).hasSum.mul_left (star (x p))).mul_right (x q)
    have hpart : ∀ n : ℕ, ∑ k ∈ Finset.range n, (star x ⬝ᵥ (F k *ᵥ x))
        = star x ⬝ᵥ ((∑ k ∈ Finset.range n, F k) *ᵥ x) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, Matrix.add_mulVec, dotProduct_add]
    have hpsdn : ∀ n : ℕ, (∑ k ∈ Finset.range n, F k).PosSemidef := by
      intro n
      induction n with
      | zero => exact Matrix.PosSemidef.zero
      | succ n ih =>
          rw [Finset.sum_range_succ]
          exact ih.add (hF n)
    have hnonneg : ∀ n : ℕ, (0 : ℂ) ≤ ∑ k ∈ Finset.range n, (star x ⬝ᵥ (F k *ᵥ x)) := by
      intro n
      rw [hpart n]
      exact (hpsdn n).dotProduct_mulVec_nonneg x
    have htendsto := hint.tendsto_sum_nat
    have hlimre : Filter.Tendsto (fun n => (∑ k ∈ Finset.range n,
        (star x ⬝ᵥ (F k *ᵥ x))).re) Filter.atTop (nhds (star x ⬝ᵥ (M *ᵥ x)).re) :=
      ((Complex.continuous_re.tendsto
        (x := star x ⬝ᵥ (M *ᵥ x))).comp htendsto)
    have hre : (0 : ℝ) ≤ (star x ⬝ᵥ (M *ᵥ x)).re :=
      ge_of_tendsto hlimre (Filter.Eventually.of_forall fun n =>
        complex_re_nonneg_of_le (hnonneg n))
    have hlimim : Filter.Tendsto (fun n => (∑ k ∈ Finset.range n,
        (star x ⬝ᵥ (F k *ᵥ x))).im) Filter.atTop (nhds (star x ⬝ᵥ (M *ᵥ x)).im) :=
      ((Complex.continuous_im.tendsto
        (x := star x ⬝ᵥ (M *ᵥ x))).comp htendsto)
    have him : (star x ⬝ᵥ (M *ᵥ x)).im = 0 := by
      refine tendsto_nhds_unique hlimim ?_
      exact (tendsto_const_nhds (x := (0 : ℝ))).congr fun n =>
        ((RCLike.nonneg_iff.mp (hnonneg n)).2).symm
    exact RCLike.nonneg_iff.mpr ⟨hre, him⟩

/-- The linear map for `n` consecutive false outcomes of a Boolean instrument, starting from the
identity at `n = 0`. -/
noncomputable def loopContinueMap {D : ℕ} (I : Instrument Bool D D) : ℕ → (Operator D →ₗ[ℂ] Operator D)
  | 0 => LinearMap.id
  | n + 1 => (I.branch false).comp (loopContinueMap I n)

/-- The linear map for `n` consecutive false outcomes followed by a true outcome. -/
noncomputable def loopHaltAt {D : ℕ} (I : Instrument Bool D D) (n : ℕ) : Operator D →ₗ[ℂ] Operator D :=
  (I.branch true).comp (loopContinueMap I n)

/-- The sum of the first `n` first-halting maps, representing halting within those attempts. -/
noncomputable def loopPartialMap {D : ℕ} (I : Instrument Bool D D) (n : ℕ) : Operator D →ₗ[ℂ] Operator D :=
  ∑ k ∈ Finset.range n, loopHaltAt I k

/-- The zero-step continuation map is the identity. -/
@[simp] theorem loopContinueMap_zero_apply {D : ℕ} (I : Instrument Bool D D) (X : Operator D) :
    loopContinueMap I 0 X = X := rfl

/-- The continuation map at `n + 1` applies the false branch to the continuation map at `n`. -/
@[simp] theorem loopContinueMap_succ_apply {D : ℕ} (I : Instrument Bool D D) (n : ℕ)
    (X : Operator D) :
    loopContinueMap I (n + 1) X = I.branch false (loopContinueMap I n X) := rfl

/-- The first-halting map after `n` continuations applies the true branch to `loopContinueMap I
n`. -/
@[simp] theorem loopHaltAt_apply {D : ℕ} (I : Instrument Bool D D) (n : ℕ) (X : Operator D) :
    loopHaltAt I n X = I.branch true (loopContinueMap I n X) := rfl

/-- The partial halting map equals the sum of the first `n` first-halting outputs. -/
theorem loopPartialMap_apply {D : ℕ} (I : Instrument Bool D D) (n : ℕ) (X : Operator D) :
    loopPartialMap I n X = ∑ k ∈ Finset.range n, loopHaltAt I k X := by
  rw [loopPartialMap, LinearMap.sum_apply]

/-- The finite continuation map preserves positive semidefiniteness. -/
theorem loopContinueMap_posSemidef {D : ℕ} (I : Instrument Bool D D) (n : ℕ)
    {X : Operator D} (hX : X.PosSemidef) :
    (loopContinueMap I n X).PosSemidef := by
  induction n generalizing X with
  | zero => simpa using hX
  | succ n ih => exact (I.cp false).positive (ih hX)

/-- Each first-halting map preserves positive semidefiniteness. -/
theorem loopHaltAt_posSemidef {D : ℕ} (I : Instrument Bool D D) (n : ℕ)
    {X : Operator D} (hX : X.PosSemidef) :
    (loopHaltAt I n X).PosSemidef :=
  (I.cp true).positive (loopContinueMap_posSemidef I n hX)

/-- The partial halting map preserves positive semidefiniteness. -/
theorem loopPartialMap_posSemidef {D : ℕ} (I : Instrument Bool D D) (n : ℕ)
    {X : Operator D} (hX : X.PosSemidef) :
    (loopPartialMap I n X).PosSemidef := by
  induction n with
  | zero =>
      rw [loopPartialMap_apply]
      simp
      exact Matrix.PosSemidef.zero
  | succ n ih =>
      have hps : loopPartialMap I (n + 1) X = loopPartialMap I n X + loopHaltAt I n X := by
        rw [loopPartialMap_apply, loopPartialMap_apply, Finset.sum_range_succ]
      rw [hps]
      exact ih.add (loopHaltAt_posSemidef I n hX)

/-- The traces of the true and false branch outputs of a Boolean instrument sum to the input
trace. -/
private theorem bool_branch_trace {D : ℕ} (I : Instrument Bool D D) (Y : Operator D) :
    Matrix.trace (I.branch true Y) + Matrix.trace (I.branch false Y) = Matrix.trace Y := by
  have hsumbool : (∑ o : Bool, I.branch o Y) = I.branch false Y + I.branch true Y := by
    simp [add_comm]
  calc Matrix.trace (I.branch true Y) + Matrix.trace (I.branch false Y)
      = Matrix.trace (I.branch true Y + I.branch false Y) := (Matrix.trace_add _ _).symm
    _ = Matrix.trace (I.branch false Y + I.branch true Y) := by rw [add_comm]
    _ = Matrix.trace (∑ o : Bool, I.branch o Y) := by rw [← hsumbool]
    _ = Matrix.trace Y := I.total Y

/-- The traces of the partial halting output and the remaining continuation output sum to the
input trace. -/
theorem loop_trace_partition {D : ℕ} (I : Instrument Bool D D) (n : ℕ) (X : Operator D) :
    Matrix.trace (loopPartialMap I n X) + Matrix.trace (loopContinueMap I n X)
      = Matrix.trace X := by
  induction n generalizing X with
  | zero =>
      rw [loopPartialMap_apply]
      simp
  | succ n ih =>
      have hps : loopPartialMap I (n + 1) X = loopPartialMap I n X + loopHaltAt I n X := by
        rw [loopPartialMap_apply, loopPartialMap_apply, Finset.sum_range_succ]
      rw [hps, Matrix.trace_add, add_assoc, loopHaltAt_apply, loopContinueMap_succ_apply,
        bool_branch_trace]
      exact ih X

/-- Collects the continuation recursion, first-halting and partial-sum formulas, and the trace
partition between halted and pending outputs. -/
theorem instrument_loop_actual_first_halt_and_pending_maps :
    ∀ (D : ℕ) (I : Instrument Bool D D) (n : ℕ) (X : Operator D),
      loopContinueMap I 0 X = X ∧
      loopContinueMap I (n+1) X = I.branch false (loopContinueMap I n X) ∧
      loopHaltAt I n X = I.branch true (loopContinueMap I n X) ∧
      loopPartialMap I n X = ∑ k ∈ Finset.range n, loopHaltAt I k X ∧
      Matrix.trace (loopPartialMap I n X) + Matrix.trace (loopContinueMap I n X) = Matrix.trace X := by
  intro D I n X
  exact ⟨rfl, rfl, rfl, loopPartialMap_apply I n X, loop_trace_partition I n X⟩

/-- The zero linear map on operators is completely positive. -/
private theorem completelyPositive_zero {D : ℕ} :
    CompletelyPositive (0 : Operator D →ₗ[ℂ] Operator D) := by
  intro r A hA
  have hz : ChannelAmplification (0 : Operator D →ₗ[ℂ] Operator D) r A = 0 := by
    ext x y
    simp [ChannelAmplification]
  rw [hz]
  exact Matrix.PosSemidef.zero

/-- The identity linear map on operators is completely positive. -/
private theorem completelyPositive_id {D : ℕ} :
    CompletelyPositive (LinearMap.id : Operator D →ₗ[ℂ] Operator D) := by
  intro r A hA
  have hid : ChannelAmplification (LinearMap.id : Operator D →ₗ[ℂ] Operator D) r A = A := by
    ext x y
    simp [ChannelAmplification]
  rw [hid]
  exact hA

/-- Every finite continuation map is completely positive. -/
theorem loopContinueMap_completelyPositive {D : ℕ} (I : Instrument Bool D D) (n : ℕ) :
    CompletelyPositive (loopContinueMap I n) := by
  induction n with
  | zero => exact completelyPositive_id
  | succ n ih => exact (I.cp false).comp ih

/-- Every first-halting map is completely positive. -/
theorem loopHaltAt_completelyPositive {D : ℕ} (I : Instrument Bool D D) (n : ℕ) :
    CompletelyPositive (loopHaltAt I n) :=
  (I.cp true).comp (loopContinueMap_completelyPositive I n)

/-- Every partial halting map is completely positive. -/
theorem loopPartialMap_completelyPositive {D : ℕ} (I : Instrument Bool D D) (n : ℕ) :
    CompletelyPositive (loopPartialMap I n) := by
  induction n with
  | zero =>
      have h0 : loopPartialMap I 0 = 0 := by
        rw [loopPartialMap]
        simp
      rw [h0]
      exact completelyPositive_zero
  | succ n ih =>
      have hps : loopPartialMap I (n + 1) = loopPartialMap I n + loopHaltAt I n := by
        rw [loopPartialMap, loopPartialMap, Finset.sum_range_succ]
      rw [hps]
      exact ih.add (loopHaltAt_completelyPositive I n)

/-- The continuation, first-halting, and partial halting maps are completely positive, and the
partial halting map is trace non-increasing. -/
theorem instrument_loop_finite_complete_positivity :
    ∀ (D : ℕ) (I : Instrument Bool D D) (n : ℕ),
      CompletelyPositive (loopContinueMap I n) ∧ CompletelyPositive (loopHaltAt I n) ∧
      CompletelyPositive (loopPartialMap I n) ∧ TraceNonIncreasing (loopPartialMap I n) := by
  intro D I n
  refine ⟨loopContinueMap_completelyPositive I n, loopHaltAt_completelyPositive I n,
    loopPartialMap_completelyPositive I n, ?_⟩
  intro A hA
  have hpart := loop_trace_partition I n A
  have hcon : (0 : ℝ) ≤ (Matrix.trace (loopContinueMap I n A)).re :=
    complex_re_nonneg_of_le (loopContinueMap_posSemidef I n hA).trace_nonneg
  have hre : (Matrix.trace (loopPartialMap I n A)).re
      + (Matrix.trace (loopContinueMap I n A)).re = (Matrix.trace A).re := by
    rw [← Complex.add_re, hpart]
  linarith

/-- The coordinate vector equal to one at `i` and zero elsewhere. -/
private def unitVector {D : ℕ} (i : Fin D) : Fin D → ℂ := Pi.single i 1

/-- The outer product of `u` with its conjugate, yielding a positive semidefinite
rank-at-most-one operator. -/
private noncomputable def psdUnitVec {D : ℕ} (u : Fin D → ℂ) : Operator D := vecMulVec u (star u)

/-- The operator `psdUnitVec u` is positive semidefinite. -/
private theorem psdUnitVec_posSemidef {D : ℕ} (u : Fin D → ℂ) :
    (psdUnitVec u).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star u

/-- The `a` coordinate of `unitVector p` is one if `p = a` and zero otherwise. -/
private theorem unitVector_apply {D : ℕ} (p a : Fin D) :
    unitVector p a = if p = a then (1 : ℂ) else 0 := by
  by_cases h : p = a
  · subst h
    simp [unitVector, Pi.single_apply]
  · have h' : a ≠ p := fun he => h he.symm
    simp [unitVector, Pi.single_apply, h, h']

/-- The `(a, b)` entry of `psdUnitVec u` is `u a` times the conjugate of `u b`. -/
private theorem psdUnitVec_apply {D : ℕ} (u : Fin D → ℂ) (a b : Fin D) :
    psdUnitVec u a b = u a * (starRingEnd ℂ) (u b) := rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 800000 in

/-- Each matrix unit is a complex linear combination of four positive semidefinite outer
products of coordinate vectors and their sums. -/
private theorem matrixUnit_eq_pieces {D : ℕ} (p q : Fin D) :
    (Matrix.single p q (1 : ℂ) : Operator D) =
      (1 / 2 : ℂ) • psdUnitVec (unitVector p + unitVector q)
      + (Complex.I / 2) • psdUnitVec (unitVector p + Complex.I • unitVector q)
      - ((1 + Complex.I) / 2) • psdUnitVec (unitVector p)
      - ((1 + Complex.I) / 2) • psdUnitVec (unitVector q) := by
  ext a b
  by_cases hab : a = b
  · subst hab
    by_cases hpa : p = a <;> by_cases hqa : q = a <;>
      simp [psdUnitVec_apply, unitVector_apply, hpa, hqa,
        Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.single_apply, Pi.add_apply, Pi.smul_apply, map_mul, map_add, map_one,
        map_zero] <;>
      refine Complex.ext ?_ ?_ <;> norm_num [Complex.add_re, Complex.mul_re,
        Complex.sub_re, Complex.add_im, Complex.mul_im, Complex.sub_im]
  · by_cases hpa : p = a <;> by_cases hqa : q = a <;> by_cases hpb : p = b <;>
      by_cases hqb : q = b <;>
      simp_all [psdUnitVec_apply, unitVector_apply, hpa, hqa, hpb, hqb, hab,
        Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.single_apply, Pi.add_apply, Pi.smul_apply, map_mul, map_add, map_one,
        map_zero] <;>
      refine Complex.ext ?_ ?_ <;> norm_num [Complex.add_re, Complex.mul_re,
        Complex.sub_re, Complex.add_im, Complex.mul_im, Complex.sub_im]

/-- Every operator is the sum of matrix units scaled by its corresponding entries. -/
private theorem eq_sum_matrixUnit {D : ℕ} (X : Operator D) :
    X = ∑ p : Fin D, ∑ q : Fin D,
      ((X p q : ℂ) • (Matrix.single p q (1 : ℂ) : Operator D)) := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply,
    apply_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single a (fun p _ hp => by
      apply Finset.sum_eq_zero
      intro q _
      have hn : ¬(p = a ∧ q = b) := fun h => hp h.1
      simp [hn])
    (fun hb => absurd (Finset.mem_univ a) hb),
    Finset.sum_eq_single b (fun q _ hq => by
      simp [fun h => hq h])
    (fun hb => absurd (Finset.mem_univ b) hb)]
  simp

/-- A finite sum of summable complex sequences is summable. -/
private theorem summable_finset_sum' {ι : Type} (s : Finset ι) (f : ι → ℕ → ℂ)
    (h : ∀ p ∈ s, Summable (f p)) : Summable fun k => ∑ p ∈ s, f p k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [summable_zero]
  | insert p s hp ih =>
      simp only [Finset.sum_insert hp]
      exact (h p (Finset.mem_insert_self p s)).add
        (ih fun q hq => h q (Finset.mem_insert_of_mem hq))

/-- Each entry of the first-halting outputs is summable over halting times for a positive
semidefinite input. -/
private theorem halt_entry_summable_psd {D : ℕ} (I : Instrument Bool D D)
    {P : Operator D} (hP : P.PosSemidef) (i j : Fin D) :
    Summable fun k => loopHaltAt I k P i j := by
  have hbound : ∀ k, ‖loopHaltAt I k P i j‖ ≤ (Matrix.trace (loopHaltAt I k P)).re :=
    fun k => posSemidef_abs_entry_le_trace (loopHaltAt_posSemidef I k hP) i j
  have hnonneg : ∀ k, (0 : ℝ) ≤ (Matrix.trace (loopHaltAt I k P)).re := fun k =>
    complex_re_nonneg_of_le (loopHaltAt_posSemidef I k hP).trace_nonneg
  have hseries : Summable fun k => (Matrix.trace (loopHaltAt I k P)).re := by
    refine summable_of_sum_range_le (c := (Matrix.trace P).re) hnonneg fun n => ?_
    have hsplit : ∑ k ∈ Finset.range n, (Matrix.trace (loopHaltAt I k P)).re
        = (Matrix.trace (loopPartialMap I n P)).re := by
      simp only [loopPartialMap_apply, Matrix.trace_sum, Complex.re_sum]
    rw [hsplit]
    have hpart := loop_trace_partition I n P
    have hcon : (0 : ℝ) ≤ (Matrix.trace (loopContinueMap I n P)).re :=
      complex_re_nonneg_of_le (loopContinueMap_posSemidef I n hP).trace_nonneg
    have hre : (Matrix.trace (loopPartialMap I n P)).re
        + (Matrix.trace (loopContinueMap I n P)).re = (Matrix.trace P).re := by
      rw [← Complex.add_re, hpart]
    linarith
  exact Summable.of_norm (hseries.of_nonneg_of_le (fun k => norm_nonneg _) hbound)

/-- Each entry of the first-halting outputs is summable for a scalar multiple of `psdUnitVec u`. -/
private theorem halt_entry_summable_unit {D : ℕ} (I : Instrument Bool D D) (c : ℂ)
    (u : Fin D → ℂ) (i j : Fin D) :
    Summable fun k => loopHaltAt I k (c • psdUnitVec u) i j := by
  have hEq : (fun k => loopHaltAt I k (c • psdUnitVec u) i j)
      = fun k => c * loopHaltAt I k (psdUnitVec u) i j := by
    funext k
    rw [map_smul]
    rfl
  rw [hEq]
  exact ((halt_entry_summable_psd I (psdUnitVec_posSemidef u) i j).hasSum.mul_left c).summable

/-- Each entry of the first-halting outputs is summable for a scalar multiple of a matrix unit. -/
private theorem halt_entry_summable_single {D : ℕ} (I : Instrument Bool D D) (c : ℂ)
    (p q : Fin D) (i j : Fin D) :
    Summable fun k => loopHaltAt I k
      (c • (Matrix.single p q (1 : ℂ) : Operator D)) i j := by
  have hEq : ∀ k, loopHaltAt I k (c • (Matrix.single p q (1 : ℂ) : Operator D)) i j
      = c * loopHaltAt I k (Matrix.single p q (1 : ℂ) : Operator D) i j := by
    intro k
    rw [map_smul]
    rfl
  have hcomb : ∀ k, loopHaltAt I k (Matrix.single p q (1 : ℂ) : Operator D) i j
      = (1 / 2 : ℂ) * loopHaltAt I k (psdUnitVec (unitVector p + unitVector q)) i j
        + (Complex.I / 2)
            * loopHaltAt I k (psdUnitVec (unitVector p + Complex.I • unitVector q)) i j
        - ((1 + Complex.I) / 2) * loopHaltAt I k (psdUnitVec (unitVector p)) i j
        - ((1 + Complex.I) / 2) * loopHaltAt I k (psdUnitVec (unitVector q)) i j := by
    intro k
    have h1 : loopHaltAt I k (Matrix.single p q (1 : ℂ) : Operator D)
        = (1 / 2 : ℂ) • loopHaltAt I k (psdUnitVec (unitVector p + unitVector q))
          + (Complex.I / 2)
              • loopHaltAt I k (psdUnitVec (unitVector p + Complex.I • unitVector q))
          - ((1 + Complex.I) / 2) • loopHaltAt I k (psdUnitVec (unitVector p))
          - ((1 + Complex.I) / 2) • loopHaltAt I k (psdUnitVec (unitVector q)) := by
      rw [matrixUnit_eq_pieces p q]
      simp [map_add, map_sub, map_smul]
    rw [h1]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have hgoal : (fun k => loopHaltAt I k
      (c • (Matrix.single p q (1 : ℂ) : Operator D)) i j)
      = fun k => c * ((1 / 2 : ℂ) * loopHaltAt I k (psdUnitVec (unitVector p + unitVector q)) i j
        + (Complex.I / 2)
            * loopHaltAt I k (psdUnitVec (unitVector p + Complex.I • unitVector q)) i j
        - ((1 + Complex.I) / 2) * loopHaltAt I k (psdUnitVec (unitVector p)) i j
        - ((1 + Complex.I) / 2) * loopHaltAt I k (psdUnitVec (unitVector q)) i j) := by
    funext k
    rw [hEq k, hcomb k]
  rw [hgoal]
  have h1 : Summable fun k => (1 / 2 : ℂ)
      * loopHaltAt I k (psdUnitVec (unitVector p + unitVector q)) i j :=
    ((halt_entry_summable_psd I (psdUnitVec_posSemidef _) i j).hasSum.mul_left _).summable
  have h2 : Summable fun k => (Complex.I / 2)
      * loopHaltAt I k (psdUnitVec (unitVector p + Complex.I • unitVector q)) i j :=
    ((halt_entry_summable_psd I (psdUnitVec_posSemidef _) i j).hasSum.mul_left _).summable
  have h3 : Summable fun k => ((1 + Complex.I) / 2)
      * loopHaltAt I k (psdUnitVec (unitVector p)) i j :=
    ((halt_entry_summable_psd I (psdUnitVec_posSemidef _) i j).hasSum.mul_left _).summable
  have h4 : Summable fun k => ((1 + Complex.I) / 2)
      * loopHaltAt I k (psdUnitVec (unitVector q)) i j :=
    ((halt_entry_summable_psd I (psdUnitVec_posSemidef _) i j).hasSum.mul_left _).summable
  exact ((((h1.add h2).sub h3).sub h4).hasSum.mul_left c).summable

/-- For every operator, each entry of its first-halting outputs is summable over halting times. -/
theorem loopHaltAt_entry_summable {D : ℕ} (I : Instrument Bool D D) (X : Operator D)
    (i j : Fin D) : Summable fun k => loopHaltAt I k X i j := by
  have hsplit : (fun k => loopHaltAt I k X i j)
      = fun k => ∑ p : Fin D, ∑ q : Fin D,
          loopHaltAt I k (((X p q : ℂ)) • (Matrix.single p q (1 : ℂ) : Operator D)) i j := by
    funext k
    conv_lhs => rw [eq_sum_matrixUnit X]
    simp only [map_sum, Matrix.sum_apply]
  rw [hsplit]
  refine summable_finset_sum' _ _ fun p _ =>
    summable_finset_sum' _ _ fun q _ => halt_entry_summable_single I _ p q i j

/-- The complex-linear terminal map obtained by summing the first-halting maps entrywise over
all continuation counts. -/
noncomputable def loopTerminalMap {D : ℕ} (I : Instrument Bool D D) :
    Operator D →ₗ[ℂ] Operator D where
  toFun X := fun i j => ∑' k, loopHaltAt I k X i j
  map_add' X Y := by
    funext i j
    have hx : HasSum (fun k => loopHaltAt I k X i j) _ :=
      (loopHaltAt_entry_summable I X i j).hasSum
    have hy : HasSum (fun k => loopHaltAt I k Y i j) _ :=
      (loopHaltAt_entry_summable I Y i j).hasSum
    have hcomb := (hx.add hy).tsum_eq
    simpa [map_add, Matrix.add_apply] using hcomb
  map_smul' c X := by
    funext i j
    have hx : HasSum (fun k => loopHaltAt I k X i j) _ :=
      (loopHaltAt_entry_summable I X i j).hasSum
    have hcomb := (hx.mul_left c).tsum_eq
    simpa [map_smul, Matrix.smul_apply, smul_eq_mul] using hcomb

/-- Each entry of the terminal output equals the infinite sum of the corresponding first-halting
output entries. -/
theorem loopTerminalMap_apply {D : ℕ} (I : Instrument Bool D D) (X : Operator D)
    (i j : Fin D) :
    loopTerminalMap I X i j = ∑' k, loopHaltAt I k X i j := rfl

/-- The terminal map preserves positive semidefiniteness. -/
theorem loopTerminalMap_posSemidef {D : ℕ} (I : Instrument Bool D D)
    {X : Operator D} (hX : X.PosSemidef) :
    (loopTerminalMap I X).PosSemidef :=
  posSemidef_of_tsum_entries (fun k => loopHaltAt_posSemidef I k hX)
    (fun i j => loopHaltAt_entry_summable I X i j)

/-- The partial halting outputs converge to the terminal output on every operator. -/
theorem loopTerminalMap_tendsto {D : ℕ} (I : Instrument Bool D D) (X : Operator D) :
    Filter.Tendsto (fun n => loopPartialMap I n X) Filter.atTop
      (nhds (loopTerminalMap I X)) := by
  rw [tendsto_matrix_iff_entrywise]
  intro i j
  have hEq : (fun n => loopPartialMap I n X i j)
      = fun n => ∑ k ∈ Finset.range n, loopHaltAt I k X i j := by
    funext n
    rw [loopPartialMap_apply, Matrix.sum_apply]
  rw [hEq]
  exact (loopHaltAt_entry_summable I X i j).hasSum.tendsto_sum_nat

/-- The terminal map of a Boolean instrument loop is completely positive. -/
theorem loopTerminalMap_completelyPositive {D : ℕ} (I : Instrument Bool D D) :
    CompletelyPositive (loopTerminalMap I) := by
  intro r A hA
  have hpsd : ∀ k, (ChannelAmplification (loopHaltAt I k) r A).PosSemidef := fun k =>
    (loopHaltAt_completelyPositive I k) r A hA
  have hsum : ∀ x y : Fin r × Fin D,
      Summable fun k => ChannelAmplification (loopHaltAt I k) r A x y := by
    intro x y
    exact loopHaltAt_entry_summable I
      (fun i j => A (x.1, i) (y.1, j)) x.2 y.2
  have hcore := posSemidef_of_tsum_entries hpsd hsum
  have hEq : ChannelAmplification (loopTerminalMap I) r A
      = Matrix.of fun x y => ∑' k, ChannelAmplification (loopHaltAt I k) r A x y := by
    ext x y
    simp only [ChannelAmplification, loopTerminalMap_apply, Matrix.of_apply]
  rw [hEq]
  exact hcore

/-- The terminal map is completely positive and trace non-increasing, and is the limit of the
partial halting maps on every operator. -/
theorem instrument_loop_terminal_cp_map_actual_limit :
    ∀ (D : ℕ) (I : Instrument Bool D D),
      CompletelyPositive (loopTerminalMap I) ∧ TraceNonIncreasing (loopTerminalMap I) ∧
      ∀ X : Operator D, Filter.Tendsto (fun n => loopPartialMap I n X) Filter.atTop
        (nhds (loopTerminalMap I X)) := by
  intro D I
  refine ⟨loopTerminalMap_completelyPositive I, ?_, fun X => loopTerminalMap_tendsto I X⟩
  intro A hA
  have hbound : ∀ n : ℕ, (Matrix.trace (loopPartialMap I n A)).re
      ≤ (Matrix.trace A).re := by
    intro n
    have hpart := loop_trace_partition I n A
    have hcon : (0 : ℝ) ≤ (Matrix.trace (loopContinueMap I n A)).re :=
      complex_re_nonneg_of_le (loopContinueMap_posSemidef I n hA).trace_nonneg
    have hre : (Matrix.trace (loopPartialMap I n A)).re
        + (Matrix.trace (loopContinueMap I n A)).re = (Matrix.trace A).re := by
      rw [← Complex.add_re, hpart]
    linarith
  have ht := tendsto_matrix_trace (loopTerminalMap_tendsto I A)
  have hlim : Filter.Tendsto (fun n => (Matrix.trace (loopPartialMap I n A)).re)
      Filter.atTop (nhds (Matrix.trace (loopTerminalMap I A)).re) :=
    ((Complex.continuous_re.tendsto
      (x := Matrix.trace (loopTerminalMap I A))).comp ht)
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hbound)

/-- The nonnegative extended-real pending mass given by the real trace of the continuation
output. -/
noncomputable def loopPending {D : ℕ} (I : Instrument Bool D D) (ρ : Operator D)
    (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Matrix.trace (loopContinueMap I n ρ)).re

/-- The infimum over all finite continuation counts of `loopPending`. -/
noncomputable def loopNeverMass {D : ℕ} (I : Instrument Bool D D) (ρ : Operator D) :
    ℝ≥0∞ :=
  ⨅ n, loopPending I ρ n

/-- For a positive semidefinite input, pending mass is non-increasing with the continuation
count. -/
theorem loopPending_antitone {D : ℕ} (I : Instrument Bool D D) {ρ : Operator D}
    (hρ : ρ.PosSemidef) : Antitone (loopPending I ρ) := by
  refine antitone_nat_of_succ_le fun k => ?_
  have hkey : Matrix.trace (loopHaltAt I k ρ) + Matrix.trace (loopContinueMap I (k + 1) ρ)
      = Matrix.trace (loopContinueMap I k ρ) := by
    have h1 := loop_trace_partition I (k + 1) ρ
    have h2 := loop_trace_partition I k ρ
    have hps : loopPartialMap I (k + 1) ρ
        = loopPartialMap I k ρ + loopHaltAt I k ρ := by
      rw [loopPartialMap_apply, loopPartialMap_apply, Finset.sum_range_succ]
    rw [hps, Matrix.trace_add] at h1
    linear_combination h1 - h2
  have hre : (Matrix.trace (loopContinueMap I (k + 1) ρ)).re
      ≤ (Matrix.trace (loopContinueMap I k ρ)).re := by
    have hh : (0 : ℝ) ≤ (Matrix.trace (loopHaltAt I k ρ)).re :=
      complex_re_nonneg_of_le (loopHaltAt_posSemidef I k hρ).trace_nonneg
    have hkeyre := congrArg Complex.re hkey
    rw [Complex.add_re] at hkeyre
    linarith
  exact ENNReal.ofReal_le_ofReal hre

/-- For a positive semidefinite input, the finite pending masses converge to `loopNeverMass`. -/
theorem loopPending_tendsto {D : ℕ} (I : Instrument Bool D D) {ρ : Operator D}
    (hρ : ρ.PosSemidef) :
    Filter.Tendsto (loopPending I ρ) Filter.atTop (nhds (loopNeverMass I ρ)) :=
  tendsto_atTop_iInf (loopPending_antitone I hρ)

/-- Summing an extended-nonnegative-real function over `Option ℕ` splits into its value at
`none` and its sum over `some n`. -/
private theorem tsum_option_ennreal (a : ℝ≥0∞) (f : ℕ → ℝ≥0∞) :
    ∑' o : Option ℕ, o.elim a f = a + ∑' n, f n := by
  classical
  have h1 : ∑' p : ℕ ⊕ PUnit, (fun o : Option ℕ => o.elim a f)
      ((@Equiv.optionEquivSumPUnit.{0, 0} ℕ).symm p)
      ≤ ∑' o : Option ℕ, o.elim a f :=
    ENNReal.tsum_comp_le_tsum_of_injective
      (@Equiv.optionEquivSumPUnit.{0, 0} ℕ).symm.injective (fun o : Option ℕ => o.elim a f)
  have h2 : ∑' o : Option ℕ, o.elim a f
      ≤ ∑' p : ℕ ⊕ PUnit, (fun o : Option ℕ => o.elim a f)
          ((@Equiv.optionEquivSumPUnit.{0, 0} ℕ).symm p) := by
    have hinner := ENNReal.tsum_comp_le_tsum_of_injective
      (@Equiv.optionEquivSumPUnit.{0, 0} ℕ).injective
      (fun p => (fun o : Option ℕ => o.elim a f)
        ((@Equiv.optionEquivSumPUnit.{0, 0} ℕ).symm p))
    simpa [Function.LeftInverse] using hinner
  have hinl : ∀ n : ℕ, (fun o : Option ℕ => o.elim a f)
      ((@Equiv.optionEquivSumPUnit.{0, 0} ℕ).symm (Sum.inl n)) = f n := by
    intro n
    rw [Equiv.optionEquivSumPUnit_symm_inl]
    rfl
  have hinr : ∀ u : PUnit.{1}, (fun o : Option ℕ => o.elim a f)
      ((@Equiv.optionEquivSumPUnit.{0, 0} ℕ).symm (Sum.inr u)) = a := by
    intro u
    rw [Equiv.optionEquivSumPUnit_symm_inr]
    rfl
  have hsplit : ∑' p : ℕ ⊕ PUnit, (fun o : Option ℕ => o.elim a f)
      ((@Equiv.optionEquivSumPUnit.{0, 0} ℕ).symm p) = ∑' n, f n + a := by
    rw [tsum_sum_type' (F := fun p => (fun o : Option ℕ => o.elim a f)
      ((@Equiv.optionEquivSumPUnit.{0, 0} ℕ).symm p))]
    simp only [hinl, hinr]
    congr 1
    simp
  rw [le_antisymm h2 h1, hsplit]
  ring

/-- On a density operator, the sum of the first-halting masses equals the nonnegative
extended-real trace of the terminal output. -/
private theorem tsum_haltMass_eq_terminal {D : ℕ} (I : Instrument Bool D D)
    {ρ : Operator D} (hρ : IsDensityOperator ρ) :
    ∑' k, ENNReal.ofReal (Matrix.trace (loopHaltAt I k ρ)).re
      = ENNReal.ofReal (Matrix.trace (loopTerminalMap I ρ)).re := by
  have hnonneg : ∀ k, (0 : ℝ) ≤ (Matrix.trace (loopHaltAt I k ρ)).re := fun k =>
    complex_re_nonneg_of_le (loopHaltAt_posSemidef I k hρ.1).trace_nonneg
  have hsplit : ∀ n : ℕ, ∑ k ∈ Finset.range n, (Matrix.trace (loopHaltAt I k ρ)).re
      = (Matrix.trace (loopPartialMap I n ρ)).re := by
    intro n
    rw [loopPartialMap_apply, Matrix.trace_sum, Complex.re_sum]
  have hbound : ∀ n : ℕ, ∑ k ∈ Finset.range n, (Matrix.trace (loopHaltAt I k ρ)).re ≤ 1 := by
    intro n
    rw [hsplit n]
    have hpart := loop_trace_partition I n ρ
    have hcon : (0 : ℝ) ≤ (Matrix.trace (loopContinueMap I n ρ)).re :=
      complex_re_nonneg_of_le (loopContinueMap_posSemidef I n hρ.1).trace_nonneg
    have hre : (Matrix.trace (loopPartialMap I n ρ)).re
        + (Matrix.trace (loopContinueMap I n ρ)).re = 1 := by
      rw [← Complex.add_re, hpart]
      simp [hρ.2]
    linarith
  have hsum : Summable fun k => (Matrix.trace (loopHaltAt I k ρ)).re :=
    summable_of_sum_range_le (c := (1 : ℝ)) hnonneg hbound
  have hlim : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n,
      (Matrix.trace (loopHaltAt I k ρ)).re) Filter.atTop
      (nhds (Matrix.trace (loopTerminalMap I ρ)).re) := by
    have ht := tendsto_matrix_trace (loopTerminalMap_tendsto I ρ)
    have hlimre : Filter.Tendsto (fun n => (Matrix.trace (loopPartialMap I n ρ)).re)
        Filter.atTop (nhds (Matrix.trace (loopTerminalMap I ρ)).re) :=
      ((Complex.continuous_re.tendsto
        (x := Matrix.trace (loopTerminalMap I ρ))).comp ht)
    have hfun : (fun n => ∑ k ∈ Finset.range n, (Matrix.trace (loopHaltAt I k ρ)).re)
        = fun n => (Matrix.trace (loopPartialMap I n ρ)).re :=
      funext fun n => hsplit n
    rw [hfun]
    exact hlimre
  have hval : ∑' k, (Matrix.trace (loopHaltAt I k ρ)).re
      = (Matrix.trace (loopTerminalMap I ρ)).re :=
    tendsto_nhds_unique (hsum.hasSum.tendsto_sum_nat) hlim
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsum, hval]

/-- On a density operator, terminal halting mass and never-halting mass sum to one. -/
private theorem terminal_plus_never {D : ℕ} (I : Instrument Bool D D)
    {ρ : Operator D} (hρ : IsDensityOperator ρ) :
    ENNReal.ofReal (Matrix.trace (loopTerminalMap I ρ)).re + loopNeverMass I ρ = 1 := by
  have hA : Filter.Tendsto (fun n => (Matrix.trace (loopPartialMap I n ρ)).re)
      Filter.atTop (nhds (Matrix.trace (loopTerminalMap I ρ)).re) :=
    ((Complex.continuous_re.tendsto
      (x := Matrix.trace (loopTerminalMap I ρ))).comp
      (tendsto_matrix_trace (loopTerminalMap_tendsto I ρ)))
  have hA' : Filter.Tendsto
      (fun n => ENNReal.ofReal (Matrix.trace (loopPartialMap I n ρ)).re) Filter.atTop
      (nhds (ENNReal.ofReal (Matrix.trace (loopTerminalMap I ρ)).re)) :=
    (ENNReal.continuous_ofReal.tendsto
      (x := (Matrix.trace (loopTerminalMap I ρ)).re)).comp hA
  have hB : Filter.Tendsto (loopPending I ρ) Filter.atTop (nhds (loopNeverMass I ρ)) :=
    loopPending_tendsto I hρ.1
  have hsum : ∀ n : ℕ, ENNReal.ofReal (Matrix.trace (loopPartialMap I n ρ)).re
      + loopPending I ρ n = 1 := by
    intro n
    have hpart := loop_trace_partition I n ρ
    have hreal : (Matrix.trace (loopPartialMap I n ρ)).re
        + (Matrix.trace (loopContinueMap I n ρ)).re = 1 := by
      rw [← Complex.add_re, hpart]
      simp [hρ.2]
    rw [loopPending, ← ENNReal.ofReal_add
      (complex_re_nonneg_of_le (loopPartialMap_posSemidef I n hρ.1).trace_nonneg)
      (complex_re_nonneg_of_le (loopContinueMap_posSemidef I n hρ.1).trace_nonneg), hreal]
    simp
  have hab := Filter.Tendsto.add hA' hB
  rw [funext hsum] at hab
  exact tendsto_nhds_unique hab tendsto_const_nhds

/-- Inserting a zero term at the start of an extended-nonnegative-real series leaves its sum
unchanged. -/
private theorem tsum_match_succ {g : ℕ → ℝ≥0∞} :
    ∑' n, (match n with | 0 => (0 : ℝ≥0∞) | n + 1 => g n) = ∑' n, g n := by
  have hpart : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1),
      (match k with | 0 => (0 : ℝ≥0∞) | m + 1 => g m) = ∑ k ∈ Finset.range n, g k := by
    intro n
    rw [Finset.sum_range_succ']
    show (∑ k ∈ Finset.range n, (match Nat.succ k with | 0 => (0 : ℝ≥0∞) | m + 1 => g m))
        + (match 0 with | 0 => (0 : ℝ≥0∞) | m + 1 => g m) = ∑ k ∈ Finset.range n, g k
    have h0 : (match 0 with | 0 => (0 : ℝ≥0∞) | m + 1 => g m) = 0 := rfl
    rw [h0, add_zero]
  have hA : ∑' n, (match n with | 0 => (0 : ℝ≥0∞) | m + 1 => g m)
      = ⨆ i : ℕ, ∑ k ∈ Finset.range i, (match k with | 0 => (0 : ℝ≥0∞) | m + 1 => g m) :=
    ENNReal.tsum_eq_iSup_nat
  have hB : ∑' n, g n = ⨆ i : ℕ, ∑ k ∈ Finset.range i, g k := ENNReal.tsum_eq_iSup_nat
  rw [hA, hB]
  refine le_antisymm (iSup_le fun n => ?_) (iSup_le fun n => ?_)
  · match n with
    | 0 => simp
    | m + 1 =>
        rw [hpart m]
        exact le_iSup (fun i => ∑ k ∈ Finset.range i, g k) m
  · rw [← hpart n]
    exact le_iSup
      (fun i => ∑ k ∈ Finset.range i, (match k with | 0 => (0 : ℝ≥0∞) | m + 1 => g m)) (n + 1)

/-- The stopping-time probability mass function, assigning never-halting mass to `none`, zero to
`some 0`, and first-halting mass after `n` continuations to `some (n + 1)`. -/
noncomputable def loopStoppingLaw {D : ℕ} (I : Instrument Bool D D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) : PMF (Option ℕ) :=
  ⟨fun o => o.elim (loopNeverMass I ρ) fun n =>
      match n with
      | 0 => (0 : ℝ≥0∞)
      | k + 1 => ENNReal.ofReal (Matrix.trace (loopHaltAt I k ρ)).re,
    by
      have hts : ∑' o : Option ℕ, o.elim (loopNeverMass I ρ)
          (fun n =>
            match n with
            | 0 => (0 : ℝ≥0∞)
            | k + 1 => ENNReal.ofReal (Matrix.trace (loopHaltAt I k ρ)).re) = 1 := by
        rw [tsum_option_ennreal _ _, tsum_match_succ, tsum_haltMass_eq_terminal I hρ]
        exact (add_comm _ _).trans (terminal_plus_never I hρ)
      exact (Summable.hasSum_iff ENNReal.summable).mpr hts⟩

/-- Collects the pending-mass formula and limit, the stopping-law masses at finite times and
nontermination, and the identity that terminal plus never-halting mass is one. -/
theorem instrument_loop_stopping_law_and_never_mass :
    ∀ (D : ℕ) (I : Instrument Bool D D) (ρ : Operator D) (hρ : IsDensityOperator ρ),
      (∀ n, loopPending I ρ n = ENNReal.ofReal (Matrix.trace (loopContinueMap I n ρ)).re) ∧
      Filter.Tendsto (loopPending I ρ) Filter.atTop (nhds (loopNeverMass I ρ)) ∧
      (loopStoppingLaw I ρ hρ) none = loopNeverMass I ρ ∧
      (loopStoppingLaw I ρ hρ) (some 0) = 0 ∧
      (∀ n, (loopStoppingLaw I ρ hρ) (some (n+1))
        = ENNReal.ofReal (Matrix.trace (loopHaltAt I n ρ)).re) ∧
      ENNReal.ofReal (Matrix.trace (loopTerminalMap I ρ)).re + loopNeverMass I ρ = 1 := by
  intro D I ρ hρ
  exact ⟨fun n => rfl, loopPending_tendsto I hρ.1, rfl, rfl, fun n => rfl,
    terminal_plus_never I hρ⟩
