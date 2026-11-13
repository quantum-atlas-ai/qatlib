/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CircDepthShen26.ShortTimeBlock.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Bounded Physical Density for Coarse-Site Auxiliary Registers (Lemma 22)

This module formalizes Lemma 22 (Appendix A, p. 61) of Shen et al., proving that
when node workspaces, directed connection arrays, and leaf registers assigned to
`v` coarse sites each have bounded per-site occupancy and bounded per-object
size, their total qubit count is `O(v)` and every coarse site carries at most a
constant number of auxiliary qubits.

## Main statements

* `source_lemma22_boundedPhysicalDensity`: Lemma 22, total `O(v)` and uniform
  per-site bounds for coarse-site workspace families.

## References

* [Shen et al., 2026][ShenEtAl2026CircDepth], Appendix A, Lemma 22, p. 61.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.CircDepthShen26.ShortTimeBlock

namespace Qatlib.Papers.CircDepthShen26.ShortTimeBlock

open scoped BigOperators

/-- **Lemma 22 (Bounded physical density).** Fixed arXiv:2610.01839v2,
Lemma 22, p. 61.  Node workspaces, connection arrays and leaf registers are
assigned to coarse sites; if each family has bounded per-site occupancy and
bounded per-object size, then their total size is `O(v)` and every coarse site
carries a constant number of auxiliary qubits. -/
theorem source_lemma22_boundedPhysicalDensity
    {V E G : Type*} [Fintype V] [Fintype E] [Fintype G]
    (v : ℕ) (hv : 1 ≤ v)
    (siteV : V → Fin v) (siteE : E → Fin v) (siteG : G → Fin v)
    (sizeV : V → ℕ) (sizeE : E → ℕ) (sizeG : G → ℕ)
    (cV cE cG qV qE qG : ℕ)
    (hV : ∀ x, sizeV x ≤ cV) (hE : ∀ e, sizeE e ≤ cE) (hG : ∀ g, sizeG g ≤ cG)
    (hcardV : ∀ s : Fin v,
      (Finset.univ.filter (fun x : V => siteV x = s)).card ≤ qV)
    (hcardE : ∀ s : Fin v,
      (Finset.univ.filter (fun e : E => siteE e = s)).card ≤ qE)
    (hcardG : ∀ s : Fin v,
      (Finset.univ.filter (fun g : G => siteG g = s)).card ≤ qG) :
    ∃ C q : ℕ, 0 < C ∧
      (∑ x : V, sizeV x) + (∑ e : E, sizeE e) + (∑ g : G, sizeG g) ≤ C * v ∧
      (∀ s : Fin v,
        (∑ x ∈ Finset.univ.filter (fun x : V => siteV x = s), sizeV x) +
        (∑ e ∈ Finset.univ.filter (fun e : E => siteE e = s), sizeE e) +
        (∑ g ∈ Finset.univ.filter (fun g : G => siteG g = s), sizeG g) ≤ q) := by
  classical
  by_cases _htriv : 1 ≤ v
  swap
  · exact False.elim (_htriv hv)
  let q := qV * cV + qE * cE + qG * cG
  let C := q + 1
  have hfiberV (s : Fin v) :
      (∑ x ∈ Finset.univ.filter (fun x : V => siteV x = s), sizeV x) ≤ qV * cV := by
    calc
      _ ≤ (Finset.univ.filter (fun x : V => siteV x = s)).card * cV :=
        Finset.sum_le_card_nsmul _ _ _ (fun x _ => hV x)
      _ ≤ qV * cV := Nat.mul_le_mul_right cV (hcardV s)
  have hfiberE (s : Fin v) :
      (∑ e ∈ Finset.univ.filter (fun e : E => siteE e = s), sizeE e) ≤ qE * cE := by
    calc
      _ ≤ (Finset.univ.filter (fun e : E => siteE e = s)).card * cE :=
        Finset.sum_le_card_nsmul _ _ _ (fun e _ => hE e)
      _ ≤ qE * cE := Nat.mul_le_mul_right cE (hcardE s)
  have hfiberG (s : Fin v) :
      (∑ g ∈ Finset.univ.filter (fun g : G => siteG g = s), sizeG g) ≤ qG * cG := by
    calc
      _ ≤ (Finset.univ.filter (fun g : G => siteG g = s)).card * cG :=
        Finset.sum_le_card_nsmul _ _ _ (fun g _ => hG g)
      _ ≤ qG * cG := Nat.mul_le_mul_right cG (hcardG s)
  have htotalV : (∑ x : V, sizeV x) ≤ v * (qV * cV) := by
    calc
      _ = ∑ s : Fin v, ∑ x ∈ Finset.univ.filter (fun x : V => siteV x = s),
          sizeV x := by
        rw [Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_univ (siteV x))]
      _ ≤ ∑ _ : Fin v, qV * cV := Finset.sum_le_sum (fun s _ => hfiberV s)
      _ = v * (qV * cV) := by simp
  have htotalE : (∑ e : E, sizeE e) ≤ v * (qE * cE) := by
    calc
      _ = ∑ s : Fin v, ∑ e ∈ Finset.univ.filter (fun e : E => siteE e = s),
          sizeE e := by
        rw [Finset.sum_fiberwise_of_maps_to (fun e _ => Finset.mem_univ (siteE e))]
      _ ≤ ∑ _ : Fin v, qE * cE := Finset.sum_le_sum (fun s _ => hfiberE s)
      _ = v * (qE * cE) := by simp
  have htotalG : (∑ g : G, sizeG g) ≤ v * (qG * cG) := by
    calc
      _ = ∑ s : Fin v, ∑ g ∈ Finset.univ.filter (fun g : G => siteG g = s),
          sizeG g := by
        rw [Finset.sum_fiberwise_of_maps_to (fun g _ => Finset.mem_univ (siteG g))]
      _ ≤ ∑ _ : Fin v, qG * cG := Finset.sum_le_sum (fun s _ => hfiberG s)
      _ = v * (qG * cG) := by simp
  refine ⟨C, q, Nat.succ_pos q, ?_, ?_⟩
  · calc
      _ ≤ v * (qV * cV) + v * (qE * cE) + v * (qG * cG) :=
        Nat.add_le_add (Nat.add_le_add htotalV htotalE) htotalG
      _ = q * v := by simp only [q, Nat.add_mul, Nat.mul_comm v]
      _ ≤ C * v := Nat.mul_le_mul_right v (Nat.le_succ q)
  · intro s
    exact Nat.add_le_add (Nat.add_le_add (hfiberV s) (hfiberE s)) (hfiberG s)

end Qatlib.Papers.CircDepthShen26.ShortTimeBlock
