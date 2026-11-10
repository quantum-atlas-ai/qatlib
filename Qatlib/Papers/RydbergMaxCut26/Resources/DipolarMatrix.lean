/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Resources.DipolarDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix Qatlib
open Qatlib.Foundations.PureStateMath
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.Resources.Matrix
open Qatlib.Papers.RydbergMaxCut26.Resources.Counts Qatlib.Papers.RydbergMaxCut26.Resources.Dipolar
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase

theorem pair_repr {n : ℕ} (s : SitePair n) : s.1=Sym2.mk (endpoints s).1 (endpoints s).2 :=
  (Sym2.sortEquiv.left_inv s.1).symm

theorem support_iff {n : ℕ} (e s : SitePair n) :
    (((endpoints e).1=(endpoints s).1 ∨ (endpoints e).1=(endpoints s).2) ∧
      ((endpoints e).2=(endpoints s).1 ∨ (endpoints e).2=(endpoints s).2)) ↔ e=s := by
  constructor
  · intro h
    have hs : s.1=Sym2.mk (endpoints e).1 (endpoints e).2 :=
      (Sym2.mem_and_mem_iff (endpoints_distinct e)).mp ⟨by
        rw [pair_repr s,Sym2.mem_iff]
        exact h.1,by
        rw [pair_repr s,Sym2.mem_iff]
        exact h.2⟩
    exact Subtype.ext ((pair_repr e).trans hs.symm)
  · rintro rfl
    exact ⟨Or.inl rfl,Or.inr rfl⟩

def testBloch {n : ℕ} (s : SitePair n) (i : Fin n) (a : Fin 3) : ℝ :=
  if i=(endpoints s).1 ∨ i=(endpoints s).2 then if a=0 then 1 else 0 else 0

theorem test_density {n : ℕ} (s : SitePair n) :
    (productState (testBloch s)).PosSemidef ∧ (productState (testBloch s)).trace=1 := by
  apply product_density
  intro i
  by_cases hi : i=(endpoints s).1 ∨ i=(endpoints s).2
  · simp [testBloch,sqnorm,hi]
  · simp [testBloch,sqnorm,hi]

theorem pair_probe_trace {n : ℕ} (e s : SitePair n) :
    ((pairPauli (endpoints e).1 (endpoints e).2 0+
      pairPauli (endpoints e).1 (endpoints e).2 1)*productState (testBloch s)).trace=
      if e=s then 1 else 0 := by
  rw [Matrix.add_mul,Matrix.trace_add,pair_product_trace _ _ _ (endpoints_distinct e),
    pair_product_trace _ _ _ (endpoints_distinct e)]
  by_cases he : e=s
  · subst e
    simp [testBloch]
  · have hs : ¬((endpoints e).1=(endpoints s).1 ∨ (endpoints e).1=(endpoints s).2) ∨
      ¬((endpoints e).2=(endpoints s).1 ∨ (endpoints e).2=(endpoints s).2) :=
      not_and_or.mp (fun h => he ((support_iff e s).mp h))
    rcases hs with h|h <;> simp [testBloch,h,he]

theorem coefficient_recovery {n : ℕ} (w : SitePair n → ℝ) (s : SitePair n) :
    energy (secondaryHamiltonian endpoints w) (productState (testBloch s))=w s := by
  simp only [secondaryHamiltonian,energy,Matrix.sum_mul,Matrix.trace_sum,Matrix.smul_mul,
    Matrix.trace_smul,pair_probe_trace]
  simp

theorem secondary_injective {n : ℕ} (w v : SitePair n → ℝ)
    (h : secondaryHamiltonian endpoints w=secondaryHamiltonian endpoints v) : w=v := by
  funext s
  have he := congrArg (fun H => energy H (productState (testBloch s))) h
  simpa only [coefficient_recovery] using he

theorem no_exact_static_matrix {n : ℕ} (C3 : ℝ) (hC3 : 0 < C3)
    (position : Fin n → EuclideanSpace ℝ (Fin 3)) (hinj : Function.Injective position)
    (w : SitePair n → ℝ) (hmissing : ∃ s,w s=0) :
    rydbergHamiltonian C3 position 0≠secondaryHamiltonian endpoints w := by
  intro h
  have he : secondaryHamiltonian endpoints
      (fun s => coupling C3 position (endpoints s).1 (endpoints s).2)=secondaryHamiltonian endpoints w := by
    simpa only [rydbergHamiltonian,zero_div,zero_smul,add_zero,secondaryHamiltonian] using h
  have hm := secondary_injective _ w he
  obtain ⟨s,hs⟩ := hmissing
  exact zero_nonedge_obstruction C3 hC3 position hinj w s hs (fun e => congrFun hm e)
end Qatlib.Papers.RydbergMaxCut26.Resources.Matrix
