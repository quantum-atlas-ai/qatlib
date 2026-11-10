/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.CausalSearch.NativeOracle
import Qatlib.Papers.QAOAScaling23.SearchFees.ActualFees
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.CausalSearch
open scoped Classical
open Qatlib.Concepts.WalkSearch.QuantumAccess
open SearchFees

def publicSchedule (B N : ℕ) : List ℕ :=
  interleavePlain (geometricSearchSchedule B (5*B+8*(N+1)))

def publicOracle {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (B N : ℕ) (current : I) :=
  oracleCode U hU seed cost (publicSchedule B N) current

theorem public_budget_cap (p Q C N : ℝ) (hp : 0<p) (hpQ : p≤Q)
    (hC : 1≤C) (hN : 1≤N) (B : ℕ)
    (hB : 15*C*N/Real.sqrt p≤(B:ℝ)) : 1≤(B:ℝ)*Real.sqrt Q := by
  have hs : 0<Real.sqrt p := Real.sqrt_pos.2 hp
  have hCN : 1≤C*N := by nlinarith
  have hb : 15*C*N≤(B:ℝ)*Real.sqrt p := (div_le_iff₀ hs).mp hB
  have hsq : Real.sqrt p≤Real.sqrt Q := Real.sqrt_le_sqrt hpQ
  have hmono := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg B : (0:ℝ)≤B)
  linarith

theorem public_confidence_union (N : ℕ) :
    (2:ℝ)^N*(25/32:ℝ)^(8*(N+1))≤1/6 := by
  have hb : (25/32:ℝ)^8≤1/6 := by norm_num
  rw [pow_mul]
  have hp := pow_le_pow_left₀ (by positivity : 0≤(25/32:ℝ)^8) hb (N+1)
  calc
    (2:ℝ)^N*((25/32:ℝ)^8)^(N+1)≤(2:ℝ)^N*(1/6:ℝ)^(N+1) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _=(1/6:ℝ)*(1/3:ℝ)^N := by rw [pow_succ,show (1/3:ℝ)=2*(1/6) by norm_num,mul_pow]; ring
    _≤(1/6:ℝ)*1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (by norm_num : (0:ℝ)≤1/3) (by norm_num)) (by norm_num)
    _=1/6 := by ring
end Qatlib.Papers.QAOAScaling23.CausalSearch
