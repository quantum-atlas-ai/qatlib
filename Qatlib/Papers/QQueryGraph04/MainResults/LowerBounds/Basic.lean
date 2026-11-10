/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Qatlib.Concepts.AdversaryBounds.AdvWitness
import Qatlib.Concepts.QueryWordCore.QueryMachinery.NegativeAdversary
import Qatlib.Papers.QQueryGraph04.MainResults.ProblemDefs
import Qatlib.Papers.QQueryGraph04.MainResults.LowerBounds.AdversaryFamily
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.QQueryGraph04.MainResults.LowerBounds

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.AdversaryBounds.AdvWitness
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open scoped Matrix.Norms.L2Operator

section Transfer

variable {X W : Type} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype W] [DecidableEq W]

theorem one_sub_two_sqrt_nonneg {eps : ℝ} (_he0 : 0 ≤ eps) (he1 : eps ≤ 1 / 2) :
    0 ≤ 1 - 2 * Real.sqrt (eps * (1 - eps)) := by
  have hle : Real.sqrt (eps * (1 - eps)) ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    nlinarith
  linarith

theorem query_lower_bound_from_adversary
    (n : ℕ) (input : X → Fin n → Bool) (Gamma : Matrix X X ℂ) (f : X → Bool)
    (C : Circuit ((Fin n × Bool) × W)) (psi : QState ((Fin n × Bool) × W))
    (E : Finset ((Fin n × Bool) × W)) (eps B : ℝ)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hC : IsUnitaryCircuit C) (hpsi : Normalized psi) (he0 : 0 ≤ eps) (he1 : eps ≤ 1 / 2)
    (hsuccess : ∀ x, 1 - eps ≤ MeasureProb
      (Run (workspaceBitOracle (W := W) (input x)) C psi) (if f x then E else Eᶜ))
    (hF : 0 < advFilterBound input Gamma)
    (hB : B * advFilterBound input Gamma ≤ ‖Gamma‖) :
    B * (1 - 2 * Real.sqrt (eps * (1 - eps))) ≤ 2 * (QueryCount C : ℝ) := by
  have hmain := negative_adversary_actual_bounded_error_circuit_lower_bound X W n input Gamma f
    C psi E eps hG hz hC hpsi he0 he1 hsuccess
  have hfac := one_sub_two_sqrt_nonneg he0 he1
  have hmono : (1 - 2 * Real.sqrt (eps * (1 - eps))) * (B * advFilterBound input Gamma) ≤
      (1 - 2 * Real.sqrt (eps * (1 - eps))) * ‖Gamma‖ :=
    mul_le_mul_of_nonneg_left hB hfac
  have h1 : (1 - 2 * Real.sqrt (eps * (1 - eps))) * (B * advFilterBound input Gamma) ≤
      2 * (QueryCount C : ℝ) * advFilterBound input Gamma := hmono.trans hmain
  have h2 : (1 - 2 * Real.sqrt (eps * (1 - eps))) * (B * advFilterBound input Gamma) =
      B * (1 - 2 * Real.sqrt (eps * (1 - eps))) * advFilterBound input Gamma := by ring
  rw [h2] at h1
  have h1' : advFilterBound input Gamma * (B * (1 - 2 * Real.sqrt (eps * (1 - eps))))
      ≤ advFilterBound input Gamma * (2 * (QueryCount C : ℝ)) := by
    have e1 : advFilterBound input Gamma * (B * (1 - 2 * Real.sqrt (eps * (1 - eps))))
        = B * (1 - 2 * Real.sqrt (eps * (1 - eps))) * advFilterBound input Gamma := by
      ring
    have e2 : advFilterBound input Gamma * (2 * (QueryCount C : ℝ))
        = 2 * (QueryCount C : ℝ) * advFilterBound input Gamma := by ring
    rw [e1, e2]; exact h1
  exact (mul_le_mul_iff_right₀ hF).mp h1'

theorem query_lower_bound_omega
    (n : ℕ) (input : X → Fin n → Bool) (Gamma : Matrix X X ℂ) (f : X → Bool)
    (C : Circuit ((Fin n × Bool) × W)) (psi : QState ((Fin n × Bool) × W))
    (E : Finset ((Fin n × Bool) × W)) (B : ℝ)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hC : IsUnitaryCircuit C) (hpsi : Normalized psi)
    (hsuccess : ∀ x, 1 - 1 / 10 ≤ MeasureProb
      (Run (workspaceBitOracle (W := W) (input x)) C psi) (if f x then E else Eᶜ))
    (hF : 0 < advFilterBound input Gamma)
    (hB : B * advFilterBound input Gamma ≤ ‖Gamma‖) :
    B / 5 ≤ (QueryCount C : ℝ) := by
  have h := query_lower_bound_from_adversary n input Gamma f C psi E (1 / 10 : ℝ) B
    hG hz hC hpsi (by norm_num) (by norm_num) hsuccess hF hB
  have hfac : (1 : ℝ) - 2 * Real.sqrt ((1 / 10) * (1 - 1 / 10)) = 2 / 5 := by
    have h9 : (1 / 10 : ℝ) * (1 - 1 / 10) = (3 / 10) ^ 2 := by norm_num
    rw [h9, Real.sqrt_sq (by norm_num)]
    norm_num
  rw [hfac] at h
  linarith

end Transfer

theorem theorem19_d_one_case (N : ℕ) (hN : 0 < N) {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit ((Fin N × Bool) × W)) (psi : QState ((Fin N × Bool) × W))
    (E : Finset ((Fin N × Bool) × W))
    (hC : IsUnitaryCircuit C) (hpsi : Normalized psi)
    (hsuccess : ∀ x : Option (Fin N), 1 - 1 / 10 ≤ MeasureProb
      (Run (workspaceBitOracle (W := W) (advStarInput x)) C psi) (if x.isSome then E else Eᶜ)) :
    Real.sqrt (N : ℝ) / 5 ≤ (QueryCount C : ℝ) := by
  have h := (negative_adversary_star_actual_search_witness N hN).2.2.2.2 W C psi E (1 / 10 : ℝ)
    hC hpsi (by norm_num) (by norm_num) hsuccess
  have hfac : (1 : ℝ) - 2 * Real.sqrt ((1 / 10) * (1 - 1 / 10)) = 2 / 5 := by
    have h9 : (1 / 10 : ℝ) * (1 - 1 / 10) = (3 / 10) ^ 2 := by norm_num
    rw [h9, Real.sqrt_sq (by norm_num)]
    norm_num
  rw [hfac] at h
  linarith

theorem theorem19_lower_bound (d N : ℕ) (_hd : 0 < d) (_hN : d ≤ N)
    (M : ℕ) (hM : 0 < M) (input : Fin M → Fin N → Bool)
    (Gamma : Matrix (Fin M) (Fin M) ℂ) (f : Fin M → Bool) (c : ℝ)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hF : 0 < advFilterBound input Gamma)
    (hnorm : c * Real.sqrt ((d : ℝ) * (N : ℝ)) * advFilterBound input Gamma ≤ ‖Gamma‖) :
    ∀ {W : Type} [Fintype W] [DecidableEq W]
      (C : Circuit ((Fin N × Bool) × W)) (psi : QState ((Fin N × Bool) × W))
      (E : Finset ((Fin N × Bool) × W)),
      IsUnitaryCircuit C → Normalized psi →
      (∀ x, 1 - 1 / 10 ≤ MeasureProb
        (Run (workspaceBitOracle (W := W) (input x)) C psi) (if f x then E else Eᶜ)) →
      c * Real.sqrt ((d : ℝ) * (N : ℝ)) / 5 ≤ (QueryCount C : ℝ) := by
  haveI : NeZero M := ⟨by omega⟩
  intro W _ _ C psi E hC hpsi hs
  exact query_lower_bound_omega N input Gamma f C psi E (c * Real.sqrt ((d : ℝ) * (N : ℝ)))
    hG hz hC hpsi hs hF hnorm

theorem lemma20_lower_bound (n : ℕ) (_hn : 0 < n)
    (M : ℕ) (hM : 0 < M) (input : Fin M → Fin n → Bool)
    (Gamma : Matrix (Fin M) (Fin M) ℂ) (f : Fin M → Bool) (c : ℝ)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hF : 0 < advFilterBound input Gamma)
    (hnorm : c * (n : ℝ) * advFilterBound input Gamma ≤ ‖Gamma‖) :
    ∀ {W : Type} [Fintype W] [DecidableEq W]
      (C : Circuit ((Fin n × Bool) × W)) (psi : QState ((Fin n × Bool) × W))
      (E : Finset ((Fin n × Bool) × W)),
      IsUnitaryCircuit C → Normalized psi →
      (∀ x, 1 - 1 / 10 ≤ MeasureProb
        (Run (workspaceBitOracle (W := W) (input x)) C psi) (if f x then E else Eᶜ)) →
      c * (n : ℝ) / 5 ≤ (QueryCount C : ℝ) := by
  haveI : NeZero M := ⟨by omega⟩
  intro W _ _ C psi E hC hpsi hs
  exact query_lower_bound_omega n input Gamma f C psi E (c * (n : ℝ)) hG hz hC hpsi hs hF hnorm

theorem corollary21_lower_bound (n : ℕ) (_hn : 0 < n)
    (M : ℕ) (hM : 0 < M) (input : Fin M → Fin n → Bool)
    (Gamma : Matrix (Fin M) (Fin M) ℂ) (f : Fin M → Bool) (c : ℝ)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hF : 0 < advFilterBound input Gamma)
    (hnorm : c * (n : ℝ) * advFilterBound input Gamma ≤ ‖Gamma‖) :
    ∀ {W : Type} [Fintype W] [DecidableEq W]
      (C : Circuit ((Fin n × Bool) × W)) (psi : QState ((Fin n × Bool) × W))
      (E : Finset ((Fin n × Bool) × W)),
      IsUnitaryCircuit C → Normalized psi →
      (∀ x, 1 - 1 / 10 ≤ MeasureProb
        (Run (workspaceBitOracle (W := W) (input x)) C psi) (if f x then E else Eᶜ)) →
      c * (n : ℝ) / 5 ≤ (QueryCount C : ℝ) := by
  haveI : NeZero M := ⟨by omega⟩
  intro W _ _ C psi E hC hpsi ps
  exact query_lower_bound_omega n input Gamma f C psi E (c * (n : ℝ)) hG hz hC hpsi ps hF hnorm

theorem theorem22_lower_bound (n m k : ℕ) (_hn : 0 < n) (_hk : 0 < k) (_hm : m = k * n)
    (M : ℕ) (hM : 0 < M) (input : Fin M → Fin n → Bool)
    (Gamma : Matrix (Fin M) (Fin M) ℂ) (f : Fin M → Bool) (c : ℝ)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hF : 0 < advFilterBound input Gamma)
    (hnorm : c * Real.sqrt ((n : ℝ) * (m : ℝ)) * advFilterBound input Gamma ≤ ‖Gamma‖) :
    ∀ {W : Type} [Fintype W] [DecidableEq W]
      (C : Circuit ((Fin n × Bool) × W)) (psi : QState ((Fin n × Bool) × W))
      (E : Finset ((Fin n × Bool) × W)),
      IsUnitaryCircuit C → Normalized psi →
      (∀ x, 1 - 1 / 10 ≤ MeasureProb
        (Run (workspaceBitOracle (W := W) (input x)) C psi) (if f x then E else Eᶜ)) →
      c * Real.sqrt ((n : ℝ) * (m : ℝ)) / 5 ≤ (QueryCount C : ℝ) := by
  haveI : NeZero M := ⟨by omega⟩
  intro W _ _ C psi E hC hpsi hs
  exact query_lower_bound_omega n input Gamma f C psi E (c * Real.sqrt ((n : ℝ) * (m : ℝ)))
    hG hz hC hpsi hs hF hnorm

theorem theorem23_lower_bound (n : ℕ) (_hn : 0 < n)
    (M : ℕ) (hM : 0 < M) (input : Fin M → Fin (n * n) → Bool)
    (Gamma : Matrix (Fin M) (Fin M) ℂ) (f : Fin M → Bool) (c : ℝ)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hF : 0 < advFilterBound input Gamma)
    (hnorm : c * (n : ℝ) * Real.sqrt (n : ℝ) * advFilterBound input Gamma ≤ ‖Gamma‖) :
    ∀ {W : Type} [Fintype W] [DecidableEq W]
      (C : Circuit ((Fin (n * n) × Bool) × W)) (psi : QState ((Fin (n * n) × Bool) × W))
      (E : Finset ((Fin (n * n) × Bool) × W)),
      IsUnitaryCircuit C → Normalized psi →
      (∀ x, 1 - 1 / 10 ≤ MeasureProb
        (Run (workspaceBitOracle (W := W) (input x)) C psi) (if f x then E else Eᶜ)) →
      c * (n : ℝ) * Real.sqrt (n : ℝ) / 5 ≤ (QueryCount C : ℝ) := by
  haveI : NeZero M := ⟨by omega⟩
  intro W _ _ C psi E hC hpsi hs
  exact query_lower_bound_omega (n * n) input Gamma f C psi E
    (c * (n : ℝ) * Real.sqrt (n : ℝ)) hG hz hC hpsi hs hF hnorm

theorem theorem24_lower_bound (n m k : ℕ) (_hn : 0 < n) (_hk : 0 < k) (_hm : m = k * (n + 1))
    (M : ℕ) (hM : 0 < M) (input : Fin M → Fin n → Bool)
    (Gamma : Matrix (Fin M) (Fin M) ℂ) (f : Fin M → Bool) (c : ℝ)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hF : 0 < advFilterBound input Gamma)
    (hnorm : c * Real.sqrt ((n : ℝ) * (m : ℝ)) * advFilterBound input Gamma ≤ ‖Gamma‖) :
    ∀ {W : Type} [Fintype W] [DecidableEq W]
      (C : Circuit ((Fin n × Bool) × W)) (psi : QState ((Fin n × Bool) × W))
      (E : Finset ((Fin n × Bool) × W)),
      IsUnitaryCircuit C → Normalized psi →
      (∀ x, 1 - 1 / 10 ≤ MeasureProb
        (Run (workspaceBitOracle (W := W) (input x)) C psi) (if f x then E else Eᶜ)) →
      c * Real.sqrt ((n : ℝ) * (m : ℝ)) / 5 ≤ (QueryCount C : ℝ) := by
  haveI : NeZero M := ⟨by omega⟩
  intro W _ _ C psi E hC hpsi hs
  exact query_lower_bound_omega n input Gamma f C psi E (c * Real.sqrt ((n : ℝ) * (m : ℝ)))
    hG hz hC hpsi hs hF hnorm

end Qatlib.Papers.QQueryGraph04.MainResults.LowerBounds
