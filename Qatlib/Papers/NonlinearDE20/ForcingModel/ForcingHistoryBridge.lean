/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinearDE20.HistorySystem.FiniteHistoryEuler
import Qatlib.Papers.NonlinearDE20.ForcingModel.ForcingMarginal
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

namespace Qatlib.Papers.NonlinearDE20.ForcingModel.Counter
open Qatlib.Papers.NonlinearDE20.HistorySystem.History

def basis (a i : Fin 2) : ℂ := if i=a then 1 else 0

def tensorBasis (a : Fin 2) (m : ℕ) (p : Fin 2×Tail m) : ℂ :=
  basis a p.1*∏ j : Fin m,basis a (p.2 j)

theorem tensorBasis_eq (a : Fin 2) (m : ℕ) (p : Fin 2×Tail m) :
    tensorBasis a m p=if p.1=a ∧ p.2=(fun _=>a) then 1 else 0 := by
  have hp : (∏ j : Fin m,basis a (p.2 j))=if p.2=(fun _=>a) then 1 else 0 := by
    by_cases h : p.2=(fun _=>a)
    · simp [h,basis]
    · have hj : ∃ j : Fin m,p.2 j≠a := by
        by_contra hn
        push Not at hn
        exact h (funext hn)
      obtain ⟨j,hj⟩ := hj
      have hz : (∏ k : Fin m,basis a (p.2 k))=0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (by simp [basis,hj])
      simp [h,hz]
  rw [tensorBasis,hp]
  by_cases ha : p.1=a <;> by_cases ht : p.2=(fun _=>a) <;> simp [basis,ha,ht]

def forcingRhs (m : ℕ) (k : ℕ) : Fin 2×Tail m→ℂ :=
  if k=0 then tensorBasis 0 m else (1/10:ℂ) • tensorBasis 1 m

def forcingTerminal (m : ℕ) : Fin 2×Tail m→ℂ :=
  fun p=>(historyInverse 2 (1:Matrix (Fin 2×Tail m) (Fin 2×Tail m) ℂ)*ᵥ
    (fun q : Fin 2×(Fin 2×Tail m)=>forcingRhs m q.1.val q.2)) (1,p)

theorem forcingTerminal_actual (m : ℕ) :
    forcingTerminal m=tensorBasis 0 m+(1/10:ℂ) • tensorBasis 1 m := by
  have h := eulerHistory_eq_inverse 1 (1:Matrix (Fin 2×Tail m) (Fin 2×Tail m) ℂ) (forcingRhs m)
  funext p
  have hh := congrFun h (1,p)
  dsimp only [eulerHistory] at hh
  rw [forcingTerminal,← hh]
  simp [eulerSequence,forcingRhs,Matrix.one_mulVec]

theorem copiedAmplitude_terminal (m : ℕ) : copiedAmplitude m=(10:ℂ) • forcingTerminal m := by
  rw [forcingTerminal_actual]
  funext p
  simp only [Pi.smul_apply,Pi.add_apply,tensorBasis_eq,copiedAmplitude,smul_eq_mul]
  ring

def sliceOuter {J : Type} (v : J→ℂ) : Matrix J J ℂ :=Matrix.vecMulVec v (star v)

theorem copiedDensity_terminal (m : ℕ) :
    copiedDensity m=(100/101:ℝ) • sliceOuter (forcingTerminal m) := by
  rw [copiedDensity,copiedAmplitude_terminal]
  ext p q
  simp only [Matrix.smul_apply,Matrix.vecMulVec,Pi.star_apply,Pi.smul_apply,
    sliceOuter,smul_eq_mul,star_mul]
  norm_num
  ring

theorem terminal_slice_trace (m : ℕ) (hm : 0 < m) :
    (sliceOuter (forcingTerminal m)).trace.re=(101/100:ℝ) := by
  have h := congrArg (fun z : ℂ=>z.re) (congrArg Matrix.trace (copiedDensity_terminal m))
  rw [copiedDensity_trace m hm,Matrix.trace_smul] at h
  simp only [Complex.one_re,Complex.smul_re] at h
  norm_num at h
  linarith

def conditionSlice {J : Type} [Fintype J] (v : J→ℂ) : Matrix J J ℂ :=
  ((sliceOuter v).trace.re)⁻¹ • sliceOuter v

theorem terminal_condition_density (m : ℕ) (hm : 0 < m) :
    conditionSlice (forcingTerminal m)=copiedDensity m := by
  rw [conditionSlice,terminal_slice_trace m hm,copiedDensity_terminal]
  norm_num

theorem actual_history_forcing_counterexample (m : ℕ) (hm : 0 < m) :
    Matrix.traceNorm (reduced (conditionSlice (forcingTerminal m))-targetDensity)=20/101 := by
  rw [terminal_condition_density m hm,forcing_traceNorm_counterexample m hm]

end Qatlib.Papers.NonlinearDE20.ForcingModel.Counter
