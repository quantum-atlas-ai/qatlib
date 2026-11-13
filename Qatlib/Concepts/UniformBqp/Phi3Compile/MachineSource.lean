/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.Phi3Compile.MachineSourceDefs
import Qatlib.Concepts.LocalMachine.LocalTransport.LocalMachine

/-!
# Machine-source and recursive Fourier-sampling estimates

The module verifies the counted recursive Fourier-sampling recovery, a polynomial schedule in
`2^l`, and the final transition of the Fourier machine. Product estimates for `rfsGamma` link
sub-quasipolynomial time bounds to the classical comparison threshold used with
[BernsteinVazirani1997]. The background is described in [BernsteinVazirani1997].

## Main statements

* `rfs_counted_value_recovery`: correct recovery with its exact node count.
* `rfs_time_schedule_poly`: a polynomial bound in `2^l + 1`.
* `cor814_classical_asymptotic_link`: eventual domination by the recursive-sampling comparison
  threshold.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CircuitImpl.Phi3Universal

set_option autoImplicit false

noncomputable section

open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib
open Qatlib.Concepts.LocalMachine.LocalTransport.LocalMachine
open Qatlib.Concepts.CircuitImpl.Phi3Universal

/-- The counted recursive Fourier-sampling recovery has value `rfsValueOf f l x` and count
`rfsNodeCount l`. -/
theorem rfs_counted_value_recovery (f : RfsQuery → Bool) (l : ℕ) (x : RfsQuery) :
    (rfsRecoverCounted f l x).1 = rfsValueOf f l x ∧
      (rfsRecoverCounted f l x).2 = rfsNodeCount l :=
  rfsRecoverCounted_spec f l x

/-- For fixed `c` and `d`, the recursive Fourier-sampling time schedule is bounded by a
polynomial in `2^l + 1`. -/
theorem rfs_time_schedule_poly (c d : ℕ) :
    ∃ c' d' : ℕ, ∀ l : ℕ, rfsTimeSchedule c d l ≤ c' * (2 ^ l + 1) ^ d' :=
  rfsTimeSchedule_polynomial c d

/-- The final Fourier-machine state returns to `q0` by a right move without changing the scanned
symbol, with amplitude one and all other outgoing amplitudes zero. -/
theorem fourier_normal_form (a : FourierSymbol) :
    fourierRule.step FourierState.qf a QtmMove.right FourierState.q0 a = 1 ∧
      ∀ (d : QtmMove) (q' : FourierState) (b : FourierSymbol),
        (d, q', b) ≠ (QtmMove.right, FourierState.q0, a) →
          fourierRule.step FourierState.qf a d q' b = 0 := by
  refine ⟨by unfold fourierRule; simp, ?_⟩
  intro d q' b hne
  show (if d = QtmMove.right ∧ q' = FourierState.q0 ∧ b = a then (1 : ℂ) else 0) = 0
  split
  · next h => exact (hne (by rw [h.1, h.2.1, h.2.2])).elim
  · rfl

/-- Folding multiplication by factors `m / 2^i` that are all at least one cannot decrease the
initial accumulator. -/
private theorem foldl_suffix_ge (m : ℕ) (l : List ℕ)
    (hl : ∀ i ∈ l, 1 ≤ m / 2 ^ i) (acc : ℕ) :
    acc ≤ List.foldl (fun a i => a * (m / 2 ^ i)) acc l := by
  induction l generalizing acc with
  | nil => rfl
  | cons i rest ih =>
      have hfi : 1 ≤ m / 2 ^ i := hl i (by simp)
      have hstep : acc ≤ acc * (m / 2 ^ i) := by nlinarith
      rw [List.foldl_cons]
      exact hstep.trans (ih (fun j hj => hl j (List.mem_cons_of_mem i hj)) _)

/-- If every factor through index `k` is at least `2^k`, the product of the first `j` factors is
at least `2^(k*j)` for `j ≤ k + 1`. -/
private theorem foldl_range_prefix_ge (m k : ℕ)
    (hfactor : ∀ i : ℕ, i ≤ k → 2 ^ k ≤ m / 2 ^ i) :
    ∀ j : ℕ, j ≤ k + 1 → 2 ^ (k * j) ≤
      List.foldl (fun a i => a * (m / 2 ^ i)) 1 (List.range j) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      intro _hj
      have hjk : j ≤ k := by omega
      have hfj := hfactor j hjk
      have hprev := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hexp : k * (j + 1) = k * j + k := by ring
      rw [hexp, Nat.pow_add]
      exact Nat.mul_le_mul hprev hfj

/-- The products of prefixes of the factors `m / 2^i` are monotone in prefix length when every
relevant factor is at least one. -/
private theorem foldl_range_mono (m : ℕ) :
    ∀ j₂ j₁ : ℕ, (∀ i : ℕ, i < j₂ → 1 ≤ m / 2 ^ i) → j₁ ≤ j₂ →
      List.foldl (fun a i => a * (m / 2 ^ i)) 1 (List.range j₁)
        ≤ List.foldl (fun a i => a * (m / 2 ^ i)) 1 (List.range j₂) := by
  intro j₂
  induction j₂ with
  | zero =>
      intro j₁ hge hj
      have : j₁ = 0 := by omega
      subst this
      rfl
  | succ j ih =>
      intro j₁ hge hj
      rcases Nat.lt_or_ge j₁ (j + 1) with hlt | hge1
      · rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact (ih j₁ (fun i hi => hge i (by omega)) (by omega)).trans
          (foldl_suffix_ge m [j] (by simp; exact hge j (by omega)) _)
      · have hj1 : j₁ = j + 1 := by omega
        subst hj1
        rfl

/-- For `m ≥ 2`, `rfsGamma m` is at least `2^((Nat.log 2 m / 2)^2)`. -/
private theorem gamma_ge_two_pow (m : ℕ) (hm : 2 ≤ m) :
    2 ^ ((Nat.log 2 m / 2) ^ 2) ≤ rfsGamma m := by
  have hm0 : m ≠ 0 := by omega
  have hpow : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hm0
  have hfactor : ∀ i : ℕ, i ≤ Nat.log 2 m / 2 → 2 ^ (Nat.log 2 m / 2) ≤ m / 2 ^ i := by
    intro i hi
    have hik : i + Nat.log 2 m / 2 ≤ Nat.log 2 m := by omega
    have h2 : 2 ^ (i + Nat.log 2 m / 2) ≤ 2 ^ Nat.log 2 m :=
      Nat.pow_le_pow_right (by norm_num) hik
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2 ^ i), Nat.mul_comm,
      ← Nat.pow_add]
    exact h2.trans hpow
  have hall : ∀ i : ℕ, i < Nat.log 2 m + 1 → 1 ≤ m / 2 ^ i := by
    intro i hi
    have h1 : 2 ^ i ≤ m :=
      (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega)).trans hpow
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2 ^ i)).mpr (by simpa using! h1)
  rw [rfsGamma, if_neg hm0]
  calc 2 ^ ((Nat.log 2 m / 2) ^ 2)
      ≤ 2 ^ (Nat.log 2 m / 2 * (Nat.log 2 m / 2 + 1)) :=
        Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
          (by rw [Nat.pow_two, Nat.mul_succ]; omega)
    _ ≤ List.foldl (fun a i => a * (m / 2 ^ i)) 1
          (List.range (Nat.log 2 m / 2 + 1)) :=
        foldl_range_prefix_ge m _ hfactor _ (Nat.le_refl _)
    _ ≤ List.foldl (fun a i => a * (m / 2 ^ i)) 1
          (List.range (Nat.log 2 m + 1)) :=
        foldl_range_mono m (Nat.log 2 m + 1) (Nat.log 2 m / 2 + 1) hall (by omega)

/-- Any natural-valued time function eventually bounded by `n^(ε * log n)` for every positive
`ε` is eventually strictly below `rfsGamma (n / 4) / 12` [BernsteinVazirani1997]. -/
theorem cor814_classical_asymptotic_link :
    ∀ T : ℕ → ℕ,
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
          (T n : ℝ) ≤ (n : ℝ) ^ (ε * Real.log n)) →
      ∃ N : ℕ, ∀ n ≥ N, T n < rfsGamma (n / 4) / 12 := by
  intro T hT
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set ε₀ : ℝ := 1 / (2048 * Real.log 2) with hε₀def
  have hε₀pos : (0 : ℝ) < ε₀ := by
    rw [hε₀def]; positivity
  obtain ⟨N₀, hN₀⟩ := hT ε₀ hε₀pos
  refine ⟨max N₀ (2 ^ 64), ?_⟩
  intro n hn
  have hnN : N₀ ≤ n := (Nat.le_max_left _ _).trans hn
  have hn64 : 2 ^ 64 ≤ n := (Nat.le_max_right _ _).trans hn
  have hn4 : (4 : ℕ) ≤ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      _ ≤ n := hn64
  set m := n / 4 with hmdef
  set L := Nat.log 2 m with hLdef
  set k := L / 2 with hkdef
  have hm2 : 2 ≤ m := by
    have := Nat.div_pos hn4 (by norm_num : 0 < 4)
    omega
  have hm0 : m ≠ 0 := by omega
  have hpowm : 2 ^ L ≤ m := Nat.pow_log_le_self 2 hm0
  have h62 : (62 : ℕ) ≤ L := by
    refine Nat.le_log_of_pow_le (by norm_num : 1 < 2) ?_
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 4)]
    have heq : (2 ^ 62 : ℕ) * 4 = 2 ^ 64 := by
      rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← Nat.pow_add]
    exact heq ▸ hn64
  have hk31 : (31 : ℕ) ≤ k := by omega

  have hmLtsucc : m < 2 ^ (L + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
  have hnbig : n < 2 ^ (L + 3) := by
    have hdm := Nat.div_add_mod n 4
    have hr : n % 4 < 4 := Nat.mod_lt n (by norm_num : 0 < 4)
    have h42 : 4 * 2 ^ (L + 1) = 2 ^ (L + 3) := by
      rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← Nat.pow_add,
        show (2 : ℕ) + (L + 1) = L + 3 from by omega]
    have hnle : n ≤ 4 * m + 3 := by omega
    calc n ≤ 4 * m + 3 := hnle
      _ ≤ 4 * (2 ^ (L + 1) - 1) + 3 := by omega
      _ < 4 * 2 ^ (L + 1) := by omega
      _ = 2 ^ (L + 3) := h42
  have hlnn : Real.log n ≤ ((L : ℝ) + 3) * Real.log 2 := by
    have hcast : (n : ℝ) ≤ ((2 ^ (L + 3) : ℕ) : ℝ) := by
      exact_mod_cast hnbig.le
    have hmono := Real.log_le_log (by positivity : (0 : ℝ) < n) hcast
    rw [Nat.cast_pow, Real.log_pow] at hmono
    push_cast at hmono
    exact hmono

  have hTn := hN₀ n hnN
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (n : ℝ))] at hTn
  have hTbound : (T n : ℝ) ≤ Real.exp (ε₀ * (Real.log n) ^ 2) := by
    rw [show ε₀ * (Real.log n) ^ 2 = Real.log n * (ε₀ * Real.log n) from by ring]
    exact hTn

  have hεcalc : ε₀ * (Real.log n) ^ 2 ≤ ((L : ℝ) + 3) ^ 2 * Real.log 2 / 2048 := by
    have hlnn0 : (0 : ℝ) ≤ Real.log n :=
      Real.log_nonneg (by exact_mod_cast (by omega : (1 : ℕ) ≤ n))
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := by positivity
    have hX0 : (0 : ℝ) ≤ ((L : ℝ) + 3) * Real.log 2 := by nlinarith [hlog2pos]
    have haa : (Real.log n) * (Real.log n)
        ≤ (Real.log n) * (((L : ℝ) + 3) * Real.log 2) :=
      mul_le_mul_of_nonneg_left hlnn hlnn0
    have hax : (Real.log n) * (((L : ℝ) + 3) * Real.log 2)
        ≤ ((L : ℝ) + 3) * Real.log 2 * (((L : ℝ) + 3) * Real.log 2) :=
      mul_le_mul_of_nonneg_right hlnn hX0
    have hsq : (Real.log n) ^ 2 ≤ (((L : ℝ) + 3) * Real.log 2) ^ 2 := by
      calc (Real.log n) ^ 2 = (Real.log n) * (Real.log n) := by ring
        _ ≤ (Real.log n) * (((L : ℝ) + 3) * Real.log 2) := haa
        _ ≤ ((L : ℝ) + 3) * Real.log 2 * (((L : ℝ) + 3) * Real.log 2) := hax
        _ = (((L : ℝ) + 3) * Real.log 2) ^ 2 := by ring
    rw [hε₀def]
    field_simp
    nlinarith [hlog2pos, hsq]

  have hLk : L ≤ 2 * k + 1 := by omega
  have hnum : (6 : ℝ) + ((L : ℝ) + 3) ^ 2 / 2048 ≤ (k : ℝ) ^ 2 := by
    have hLkr : ((L : ℝ)) ≤ ((k : ℝ)) * 2 + 1 := by
      have h := hLk
      norm_cast at h ⊢
      linarith
    have hk31r : (31 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk31
    have hstep1 : ((L : ℝ) + 3) ≤ ((k : ℝ)) * 2 + 4 := by linarith
    have hsqL : ((L : ℝ) + 3) ^ 2 ≤ ((k : ℝ) * 2 + 4) ^ 2 := by
      nlinarith [hstep1, sq_nonneg (((L : ℝ) + 3)),
        sq_nonneg ((k : ℝ) * 2 + 4 - ((L : ℝ) + 3))]
    have hkk : ((k : ℝ)) * 31 ≤ ((k : ℝ)) * ((k : ℝ)) :=
      mul_le_mul_of_nonneg_left hk31r (Nat.cast_nonneg k)
    have hexp : ((k : ℝ) * 2 + 4) ^ 2 = 4 * (k : ℝ) * (k : ℝ) + 16 * (k : ℝ) + 16 := by
      ring
    field_simp
    nlinarith [hLkr, hk31r, hsqL, hexp, hkk,
      (by positivity : (0 : ℝ) ≤ ((k : ℕ) : ℝ))]
  have hln48 : Real.log 48 ≤ 6 * Real.log 2 := by
    have h1 := Real.log_le_log (by norm_num : (0 : ℝ) < 48) (by norm_num : (48 : ℝ) ≤ 64)
    have h64 : ((64 : ℝ)) = ((2 : ℝ)) ^ (6 : ℕ) := by norm_num
    rw [h64, Real.log_pow] at h1
    exact h1

  have hApos : (0 : ℝ) < ((2 ^ (k ^ 2) : ℕ) : ℝ) := by positivity
  have hAexp : ((2 ^ (k ^ 2) : ℕ) : ℝ) = Real.exp (((k : ℝ) ^ 2) * Real.log 2) := by
    have e1 : ((2 ^ (k ^ 2) : ℕ) : ℝ) = ((2 : ℝ)) ^ ((k ^ 2 : ℕ)) := Nat.cast_pow _ _
    have e2 : ((2 : ℝ)) ^ ((k ^ 2 : ℕ))
        = Real.exp (((k ^ 2 : ℕ) : ℝ) * Real.log 2) := by
      rw [← Real.log_pow (2 : ℝ) (k ^ 2)]
      exact (Real.exp_log (by norm_num : (0 : ℝ) < ((2 : ℝ)) ^ ((k ^ 2 : ℕ)))).symm
    have e3 : ((k ^ 2 : ℕ) : ℝ) = ((k : ℝ)) ^ 2 := Nat.cast_pow _ _
    rw [e1, e2, e3]

  have hmid : Real.exp (((L : ℝ) + 3) ^ 2 * Real.log 2 / 2048)
      ≤ Real.exp (((k : ℝ) ^ 2) * Real.log 2 - Real.log 48) := by
    refine Real.exp_le_exp.mpr ?_
    have hkey : ((L : ℝ) + 3) ^ 2 / 2048 * Real.log 2 + 6 * Real.log 2
        ≤ (k : ℝ) ^ 2 * Real.log 2 := by
      have h2 := mul_le_mul_of_nonneg_right hnum hlog2pos.le
      linarith
    have hchain : ((L : ℝ) + 3) ^ 2 * Real.log 2 / 2048 + Real.log 48
        ≤ (k : ℝ) ^ 2 * Real.log 2 := by
      calc ((L : ℝ) + 3) ^ 2 * Real.log 2 / 2048 + Real.log 48
          = ((L : ℝ) + 3) ^ 2 / 2048 * Real.log 2 + Real.log 48 := by ring
        _ ≤ ((L : ℝ) + 3) ^ 2 / 2048 * Real.log 2 + 6 * Real.log 2 :=
            add_le_add_right hln48 _
        _ ≤ (k : ℝ) ^ 2 * Real.log 2 := hkey
    linarith
  have hle : (T n : ℝ) ≤ ((2 ^ (k ^ 2) : ℕ) : ℝ) / 48 := by
    have hA48 : Real.exp (((k : ℝ) ^ 2 * Real.log 2) - Real.log 48)
        = ((2 ^ (k ^ 2) : ℕ) : ℝ) / 48 := by
      rw [Real.exp_sub, hAexp, Real.exp_log (by norm_num : (0 : ℝ) < 48)]
    rw [← hA48]
    exact hTbound.trans ((Real.exp_le_exp.mpr hεcalc).trans hmid)

  have hA16 : (16 : ℝ) ≤ ((2 ^ (k ^ 2) : ℕ) : ℝ) := by
    have hk4 : (4 : ℕ) ≤ k := by omega
    have h1 : (16 : ℕ) ≤ k ^ 2 := by
      have h9 := Nat.pow_le_pow_left hk4 2
      simpa using! h9
    have h2 : (16 : ℕ) ≤ 2 ^ (k ^ 2) :=
      (by decide : (16 : ℕ) ≤ 2 ^ 16).trans (Nat.pow_le_pow_right (n := 2) (by norm_num : 0 < 2) h1)
    exact_mod_cast h2
  have hnat : (12 : ℝ) * ((T n : ℝ) + 1) ≤ ((2 ^ (k ^ 2) : ℕ) : ℝ) := by
    have h48 : (48 : ℝ) * (T n : ℝ) ≤ ((2 ^ (k ^ 2) : ℕ) : ℝ) := by
      have h9 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 48)).mp hle
      linarith
    have hq : (4 : ℝ) * ((12 : ℝ) * ((T n : ℝ) + 1))
        ≤ (4 : ℝ) * ((2 ^ (k ^ 2) : ℕ) : ℝ) := by
      have h1 : (4 : ℝ) * ((12 : ℝ) * ((T n : ℝ) + 1))
          = (48 : ℝ) * (T n : ℝ) + (48 : ℝ) := by ring
      rw [h1]
      linarith
    exact (mul_le_mul_iff_of_pos_left (by norm_num : (0 : ℝ) < 4)).mp hq
  have hnat' : 12 * (T n + 1) ≤ 2 ^ (k ^ 2) := by
    have hcast : ((12 * (T n + 1) : ℕ) : ℝ) = (12 : ℝ) * ((T n : ℝ) + 1) := by
      push_cast; ring
    have h2 := hnat
    rw [← hcast] at h2
    exact Nat.cast_le.mp h2
  have hgamma : 12 * (T n + 1) ≤ rfsGamma m :=
    hnat'.trans (gamma_ge_two_pow m hm2)

  have hdm := Nat.div_add_mod (rfsGamma m) 12
  have hmod := Nat.mod_lt (rfsGamma m) (by norm_num : 0 < 12)
  omega

end Qatlib.Concepts.UniformBqp.Phi3Compile

end
