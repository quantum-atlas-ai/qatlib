/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TensorPCA19.MainResults.Source.EigenvalueTail
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Qatlib.Papers.TensorPCA19.MainResults

namespace Qatlib.Papers.TensorPCA19.MainResults

/-- Squaring a positive real power doubles its exponent. -/
private theorem rpow_twice (x a : ℝ) (hx : 0 < x) :
    (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_two, ← Real.rpow_mul hx.le]
  congr 1
  ring

/-- Increasing a real exponent by one multiplies the positive base once. -/
private theorem rpow_shift (x a : ℝ) (hx : 0 < x) :
    x ^ (a + 1) = x * x ^ a := by
  rw [Real.rpow_add_one hx.ne']
  exact mul_comm _ _

/-- The normalized positive scale has the two scalar identities required by the Chernoff argument. -/
private theorem scalar_constants (J n L u v : ℝ)
    (hJ : 0 < J) (hn : 0 < n) (hL : 0 < L) (hu : 0 < u) (hv : 0 < v) :
    let ξ := Real.sqrt J * u * v / Real.sqrt L
    0 < ξ ∧
      (J * n * u ^ 2 * v ^ 2) * ξ⁻¹ ^ 2 = n * L ∧
      Real.sqrt (J * L) * n * u * v = n * L * ξ := by
  dsimp only
  have hJr : 0 < Real.sqrt J := Real.sqrt_pos.2 hJ
  have hLr : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  refine ⟨by positivity, ?_, ?_⟩
  · rw [inv_pow]
    change (J * n * u ^ 2 * v ^ 2) /
        ((Real.sqrt J * u * v / Real.sqrt L) ^ 2) = n * L
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hJ.le, Real.sq_sqrt hL.le]
    field_simp [hJ.ne', hL.ne', hu.ne', hv.ne']
  · rw [← mul_div_assoc]
    apply (eq_div_iff hLr.ne').2
    rw [Real.sqrt_mul hJ.le]
    calc
      Real.sqrt J * Real.sqrt L * n * u * v * Real.sqrt L =
          Real.sqrt J * (Real.sqrt L) ^ 2 * n * u * v := by ring
      _ = n * L * (Real.sqrt J * u * v) := by
        rw [Real.sq_sqrt hL.le]
        ring

/-- The even-order threshold and tail scale satisfy the exact source constant identities. -/
theorem even_tail_constants (s : SpikedTensor) (hN : 1 < s.N) (hJ : 0 < Jval s) :
    0 < xiEven s ∧
    Aeven s * (xiEven s)⁻¹ ^ 2 = (s.nbos : ℝ) * Real.log (s.N : ℝ) ∧
    EmaxEven s = 2 * (s.nbos : ℝ) * Real.log (s.N : ℝ) * xiEven s := by
  have hn : (0 : ℝ) < s.nbos := by exact_mod_cast s.hnbos
  have hNr : (0 : ℝ) < s.N := by exact_mod_cast s.hN
  have hlog : 0 < Real.log (s.N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  let u := (s.nbos : ℝ) ^ ((s.p : ℝ) / 4 - 1 / 2)
  let v := (s.N : ℝ) ^ ((s.p : ℝ) / 4)
  have hu : 0 < u := Real.rpow_pos_of_pos hn _
  have hv : 0 < v := Real.rpow_pos_of_pos hNr _
  have hnbA : (s.nbos : ℝ) ^ ((s.p : ℝ) / 2) = (s.nbos : ℝ) * u ^ 2 := by
    calc
      _ = (s.nbos : ℝ) ^ (2 * ((s.p : ℝ) / 4 - 1 / 2) + 1) := by congr 1; ring
      _ = (s.nbos : ℝ) * (s.nbos : ℝ) ^ (2 * ((s.p : ℝ) / 4 - 1 / 2)) :=
        rpow_shift _ _ hn
      _ = _ := by rw [← rpow_twice _ _ hn]
  have hNA : (s.N : ℝ) ^ ((s.p : ℝ) / 2) = v ^ 2 := by
    calc
      _ = (s.N : ℝ) ^ (2 * ((s.p : ℝ) / 4)) := by congr 1; ring
      _ = _ := (rpow_twice _ _ hNr).symm
  have hnbE : (s.nbos : ℝ) ^ ((s.p : ℝ) / 4 + 1 / 2) = (s.nbos : ℝ) * u := by
    calc
      _ = (s.nbos : ℝ) ^ (((s.p : ℝ) / 4 - 1 / 2) + 1) := by congr 1; ring
      _ = _ := rpow_shift _ _ hn
  obtain ⟨hξ, hA, hE⟩ := scalar_constants (Jval s) (s.nbos : ℝ)
    (2 * Real.log (s.N : ℝ)) u v hJ hn (by positivity) hu hv
  have hxi : xiEven s = Real.sqrt (Jval s) * u * v / Real.sqrt (2 * Real.log (s.N : ℝ)) := rfl
  refine ⟨by simpa only [hxi] using hξ, ?_, ?_⟩
  · unfold Aeven
    rw [hnbA, hNA, hxi]
    calc
      _ = ((Jval s * (s.nbos : ℝ) * u ^ 2 * v ^ 2) *
          (Real.sqrt (Jval s) * u * v / Real.sqrt (2 * Real.log (s.N : ℝ)))⁻¹ ^ 2) / 2 := by ring
      _ = (s.nbos : ℝ) * Real.log (s.N : ℝ) := by rw [hA]; ring
  · unfold EmaxEven
    rw [hnbE]
    have hroot : 2 * Jval s * Real.log (s.N : ℝ) = Jval s * (2 * Real.log (s.N : ℝ)) := by ring
    rw [hroot, hxi]
    calc
      _ = Real.sqrt (Jval s * (2 * Real.log (s.N : ℝ))) * (s.nbos : ℝ) * u * v := by ring
      _ = _ := by rw [hE]; ring

/-- The odd-order threshold and tail scale satisfy the exact source constant identities. -/
theorem odd_tail_constants (s : SpikedTensor) (hN : 1 < s.N) (hJ : 0 < JvalOdd s) :
    0 < xiOdd s ∧
    Aodd s * (xiOdd s)⁻¹ ^ 2 = (s.nbos : ℝ) * Real.log (s.N : ℝ) ∧
    EmaxOdd s = 2 * (s.nbos : ℝ) * Real.log (s.N : ℝ) * xiOdd s := by
  have hn : (0 : ℝ) < s.nbos := by exact_mod_cast s.hnbos
  have hNr : (0 : ℝ) < s.N := by exact_mod_cast s.hN
  have hlog : 0 < Real.log (s.N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  let u := (s.nbos : ℝ) ^ ((s.p : ℝ) / 2 - 1)
  let v := (s.N : ℝ) ^ ((s.p : ℝ) / 2)
  have hu : 0 < u := Real.rpow_pos_of_pos hn _
  have hv : 0 < v := Real.rpow_pos_of_pos hNr _
  have hnbA : (s.nbos : ℝ) ^ ((s.p : ℝ) - 1) = (s.nbos : ℝ) * u ^ 2 := by
    calc
      _ = (s.nbos : ℝ) ^ (2 * ((s.p : ℝ) / 2 - 1) + 1) := by congr 1; ring
      _ = (s.nbos : ℝ) * (s.nbos : ℝ) ^ (2 * ((s.p : ℝ) / 2 - 1)) :=
        rpow_shift _ _ hn
      _ = _ := by rw [← rpow_twice _ _ hn]
  have hNA : (s.N : ℝ) ^ (s.p : ℝ) = v ^ 2 := by
    calc
      _ = (s.N : ℝ) ^ (2 * ((s.p : ℝ) / 2)) := by congr 1; ring
      _ = _ := (rpow_twice _ _ hNr).symm
  have hnbE : (s.nbos : ℝ) ^ ((s.p : ℝ) / 2) = (s.nbos : ℝ) * u := by
    calc
      _ = (s.nbos : ℝ) ^ (((s.p : ℝ) / 2 - 1) + 1) := by congr 1; ring
      _ = _ := rpow_shift _ _ hn
  obtain ⟨hξ, hA, hE⟩ := scalar_constants (JvalOdd s) (s.nbos : ℝ)
    (Real.log (s.N : ℝ)) u v hJ hn hlog hu hv
  have hxi : xiOdd s = Real.sqrt (JvalOdd s) * u * v / Real.sqrt (Real.log (s.N : ℝ)) := rfl
  refine ⟨by simpa only [hxi] using hξ, ?_, ?_⟩
  · unfold Aodd
    rw [hnbA, hNA, hxi]
    calc
      _ = ((JvalOdd s * (s.nbos : ℝ) * u ^ 2 * v ^ 2) *
          (Real.sqrt (JvalOdd s) * u * v / Real.sqrt (Real.log (s.N : ℝ)))⁻¹ ^ 2) := by ring
      _ = _ := hA
  · unfold EmaxOdd
    rw [hnbE, hxi]
    calc
      _ = 2 * (Real.sqrt (JvalOdd s * Real.log (s.N : ℝ)) * (s.nbos : ℝ) * u * v) := by ring
      _ = _ := by rw [hE]; ring


end Qatlib.Papers.TensorPCA19.MainResults
