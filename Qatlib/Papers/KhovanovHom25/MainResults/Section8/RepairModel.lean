/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.SectorPredicates

/-!
# Actual finite bipartite-repair optimization

A coloring deletes exactly the monochromatic edges, counted with their source
weights, and all loops. Costs are computed from the graph. Minimizing over the
finite coloring space defines the repair optimum. No cost, cycle bound or
optimality conclusion is stored as an unconstrained structure field.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.KhovanovHom25.MainResults.RepairModel

open Qatlib.Papers.KhovanovHom25.MainResults

/-- The actual monochromatic undirected edge weight removed by a two-coloring. -/
def edgeCost {ℓ : ℕ} (p : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (S : Finset (Vertex ℓ)) (c : Vertex ℓ → Bool) : ℚ :=
  (1 / 2) * ∑ v ∈ S, ∑ w ∈ S, if c v = c w then (edgeWeightAt p m v w : ℚ) else 0

/-- A coloring's total repair cost is computed from loops and deleted edges. -/
def cost {ℓ : ℕ} (p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ) (d : Fin t → Fin ℓ)
    (S : Finset (Vertex ℓ)) (c : Vertex ℓ → Bool) : ℚ :=
  loopSum p t m d S + edgeCost p m S c

/-- The edge-repair optimum is a minimum over actual finite coloring executions. -/
def edgeMin {ℓ : ℕ} (p : ℕ) (m : Fin p → Fin ℓ × Fin ℓ) (S : Finset (Vertex ℓ)) : ℚ := by
  classical
  exact (Finset.univ.image (fun c : Vertex ℓ → Bool => edgeCost p m S c)).min'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- The total repair optimum is computed independently by minimizing total costs. -/
def totalMin {ℓ : ℕ} (p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ) (d : Fin t → Fin ℓ)
    (S : Finset (Vertex ℓ)) : ℚ := by
  classical
  exact (Finset.univ.image (fun c : Vertex ℓ → Bool => cost p t m d S c)).min'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- Every edge deletion cost is nonnegative because every graph weight is nonnegative. -/
theorem edgeCost_nonneg {ℓ : ℕ} (p : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (S : Finset (Vertex ℓ)) (c : Vertex ℓ → Bool) : 0 ≤ edgeCost p m S c := by
  unfold edgeCost
  positivity

/-- Every actual coloring supplies an upper certificate for the edge-repair optimum. -/
theorem edgeMin_le {ℓ : ℕ} (p : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (S : Finset (Vertex ℓ)) (c : Vertex ℓ → Bool) : edgeMin p m S ≤ edgeCost p m S c := by
  classical
  unfold edgeMin
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩)

/-- The minimum edge cost is attained by an actual finite coloring. -/
theorem edgeMin_attained {ℓ : ℕ} (p : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (S : Finset (Vertex ℓ)) : ∃ c : Vertex ℓ → Bool, edgeCost p m S c = edgeMin p m S := by
  classical
  have hmem : edgeMin p m S ∈ Finset.univ.image (fun c : Vertex ℓ → Bool => edgeCost p m S c) :=
    Finset.min'_mem _ _
  obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hmem
  exact ⟨c, hc⟩

/-- Every actual coloring bounds the total repair optimum above. -/
theorem totalMin_le {ℓ : ℕ} (p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) (S : Finset (Vertex ℓ)) (c : Vertex ℓ → Bool) :
    totalMin p t m d S ≤ cost p t m d S c := by
  classical
  unfold totalMin
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩)

/-- The total optimum is also attained by an actual coloring, not an arbitrary cost witness. -/
theorem totalMin_attained {ℓ : ℕ} (p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) (S : Finset (Vertex ℓ)) :
    ∃ c : Vertex ℓ → Bool, cost p t m d S c = totalMin p t m d S := by
  classical
  have hmem : totalMin p t m d S ∈
      Finset.univ.image (fun c : Vertex ℓ → Bool => cost p t m d S c) := Finset.min'_mem _ _
  obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hmem
  exact ⟨c, hc⟩

/-- Actual total repair decomposes into the loop weight and the optimized edge deletion cost. -/
theorem decomposition {ℓ : ℕ} (p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) (S : Finset (Vertex ℓ)) :
    totalMin p t m d S = loopSum p t m d S + edgeMin p m S := by
  apply le_antisymm
  · obtain ⟨c, hc⟩ := edgeMin_attained p m S
    have h := totalMin_le p t m d S c
    simpa only [cost, hc] using h
  · obtain ⟨c, hc⟩ := totalMin_attained p t m d S
    have h := edgeMin_le p m S c
    rw [← hc, cost]
    linarith

/-- A verified bipartition deletes no non-loop edges from the actual sector. -/
theorem edgeCost_zero {ℓ : ℕ} (p : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (S : Finset (Vertex ℓ)) (c : Vertex ℓ → Bool)
    (hc : ∀ v ∈ S, ∀ w ∈ S, edgeWeightAt p m v w ≠ 0 → c v ≠ c w) :
    edgeCost p m S c = 0 := by
  unfold edgeCost
  rw [mul_eq_zero]
  right
  apply Finset.sum_eq_zero
  intro v hv
  apply Finset.sum_eq_zero
  intro w hw
  by_cases h : c v = c w
  · rw [ite_eq_left h]
    have hz : edgeWeightAt p m v w = 0 := by
      by_contra he
      exact hc v hv w hw he h
    rw [hz, Nat.cast_zero]
  · exact ite_eq_right h

/-- A genuinely bipartite sector has total repair optimum equal to its loop weight. -/
theorem bipartite_total {ℓ : ℕ} (p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) (S : Finset (Vertex ℓ)) (c : Vertex ℓ → Bool)
    (hc : ∀ v ∈ S, ∀ w ∈ S, edgeWeightAt p m v w ≠ 0 → c v ≠ c w) :
    totalMin p t m d S = loopSum p t m d S := by
  have hz := edgeCost_zero p m S c hc
  have hmin : edgeMin p m S = 0 := by
    apply le_antisymm
    · simpa only [hz] using edgeMin_le p m S c
    · obtain ⟨c', hc'⟩ := edgeMin_attained p m S
      rw [← hc']
      exact edgeCost_nonneg p m S c'
  rw [decomposition, hmin, add_zero]

end Qatlib.Papers.KhovanovHom25.MainResults.RepairModel
