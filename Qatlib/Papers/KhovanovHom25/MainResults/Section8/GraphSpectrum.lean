/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.GraphEdges
public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.WeightedForm
public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.RepairModel

/-!
# Ground energy of the actual fixed-particle Khovanov graph matrix

The variational energy is computed from the original source matrix restricted
to its true particle sector. Edge symmetry, positivity and the sector closure
are proved from the generating transpositions. Repair bounds evaluate actual
coloring vectors, with no free scalar standing for a smallest eigenvalue.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace Qatlib.Papers.KhovanovHom25.MainResults.GraphSpectrum

open Qatlib.Papers.KhovanovHom25.MainResults

/-- The actual finite carrier of a fixed particle sector. -/
abbrev Sector (ℓ k : ℕ) := ↥(vertexSet ℓ k)

/-- A sum on the actual sector carrier is the corresponding source finset sum. -/
theorem sum_sector {ℓ k : ℕ} (f : Vertex ℓ → ℝ) :
    (∑ v : Sector ℓ k, f v.val) = ∑ v ∈ vertexSet ℓ k, f v :=
  Finset.sum_coe_sort (vertexSet ℓ k) f

/-- Two sums on the actual sector carrier are exactly the corresponding source finset sums. -/
theorem sum_sector₂ {ℓ k : ℕ} (f : Vertex ℓ → Vertex ℓ → ℝ) :
    (∑ v : Sector ℓ k, ∑ u : Sector ℓ k, f v.val u.val) =
      ∑ v ∈ vertexSet ℓ k, ∑ u ∈ vertexSet ℓ k, f v u := by
  calc
    _ = ∑ v : Sector ℓ k, ∑ u ∈ vertexSet ℓ k, f v.val u := by
      apply Finset.sum_congr rfl
      intro v _
      exact sum_sector (fun u => f v.val u)
    _ = _ := sum_sector (fun v => ∑ u ∈ vertexSet ℓ k, f v u)

/-- Source loop weights evaluated on the actual sector carrier. -/
def loop {ℓ k : ℕ} (p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ) (d : Fin t → Fin ℓ)
    (v : Sector ℓ k) : ℝ := (loopWeightAt p t m d v.val : ℝ)

/-- Actual source edge weights, including all multiplicities. -/
def edge {ℓ k : ℕ} (p : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (v u : Sector ℓ k) : ℝ := (edgeWeightAt p m v.val u.val : ℝ)

/-- The original source signless matrix restricted to the requested particle sector. -/
def matrix {ℓ k : ℕ} (p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ) (d : Fin t → Fin ℓ)
    (v u : Sector ℓ k) : ℝ := signlessMatrix p t m d v.val u.val

/-- The ground energy is fixed by the actual matrix's nonzero Rayleigh tests. -/
def ground {ℓ : ℕ} (k p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ) (d : Fin t → Fin ℓ) : ℝ :=
  RayleighMin.bottom (matrix (k := k) p t m d)

/-- The sector carrier has precisely the paper's binomial number of vertices. -/
theorem sector_card (ℓ k : ℕ) : Fintype.card (Sector ℓ k) = Nat.choose ℓ k := by
  rw [Fintype.card_coe, vertexSet, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The actual source restriction equals the signless matrix built from its sector weights. -/
theorem matrix_eq {ℓ k : ℕ} (p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ) (d : Fin t → Fin ℓ) :
    matrix (k := k) p t m d = WeightedForm.matrix (loop p t m d) (edge p m) := by
  funext v u
  by_cases h : v = u
  · subst u
    simp only [matrix, signlessMatrix, signlessLap, WeightedForm.matrix, ite_true]
    dsimp only [loop, edge]
    calc
      _ = 2 * (loopWeightAt p t m d v.val : ℝ) +
          ∑ w ∈ vertexSet ℓ k, (edgeWeightAt p m v.val w : ℝ) :=
        GraphEdges.degree_sector k p t m d v.property
      _ = _ := congrArg (fun z => 2 * (loopWeightAt p t m d v.val : ℝ) + z)
        (sum_sector (k := k) (fun w => (edgeWeightAt p m v.val w : ℝ))).symm
  · have hval : v.val ≠ u.val := fun hv => h (Subtype.ext hv)
    simp only [matrix, signlessMatrix, signlessLap, WeightedForm.matrix,
      ite_eq_right hval, ite_eq_right h, edge]
    norm_cast

/-- Every source loop weight is nonnegative. -/
theorem loop_nonneg {ℓ k : ℕ} (p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) (v : Sector ℓ k) : 0 ≤ loop p t m d v := by
  unfold loop loopWeightAt
  positivity

/-- The actual source matrix is positive semidefinite in every particle sector. -/
theorem matrix_psd {ℓ k : ℕ} (p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) (x : Sector ℓ k → ℝ) :
    0 ≤ RayleighMin.quadratic (matrix p t m d) x := by
  rw [matrix_eq]
  apply WeightedForm.quadratic_nonneg
  · exact loop_nonneg p t m d
  · intro v u
    exact Nat.cast_nonneg _
  · intro v
    rw [edge, GraphEdges.weight_diag, Nat.cast_zero]
  · intro v u
    unfold edge
    exact_mod_cast GraphEdges.weight_symm p m v.val u.val

/-- The coloring cost on the actual sector is exactly the source finite repair computation. -/
theorem cost_eq {ℓ k : ℕ} (p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ) (d : Fin t → Fin ℓ)
    (c : Vertex ℓ → Bool) :
    WeightedForm.repairCost (loop (k := k) p t m d) (edge p m) (fun v => c v.val) =
      (RepairModel.cost p t m d (vertexSet ℓ k) c : ℝ) := by
  unfold WeightedForm.repairCost loop edge RepairModel.cost RepairModel.edgeCost loopSum
  push_cast
  rw [sum_sector (k := k) (fun v => (loopWeightAt p t m d v : ℝ)),
    sum_sector₂ (k := k) (fun v u => if c v = c u then (edgeWeightAt p m v u : ℝ) else 0)]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  split_ifs <;> norm_cast

/-- A concrete coloring bounds the actual ground energy with the correct source factor four. -/
theorem ground_le_color {ℓ : ℕ} (k p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) (hne : (vertexSet ℓ k).Nonempty) (c : Vertex ℓ → Bool) :
    ground k p t m d ≤
      4 * (RepairModel.cost p t m d (vertexSet ℓ k) c : ℝ) / (Nat.choose ℓ k : ℝ) := by
  obtain ⟨v, hv⟩ := hne
  let : Nonempty (Sector ℓ k) := ⟨⟨v, hv⟩⟩
  have h := WeightedForm.bottom_le_repair (loop (k := k) p t m d) (edge p m)
    (fun u => c u.val) (loop_nonneg p t m d) (by
      intro u
      rw [edge, GraphEdges.weight_diag, Nat.cast_zero])
  simpa only [ground, matrix_eq, cost_eq, sector_card] using h

/-- Minimizing actual coloring executions gives a genuine repair upper bound for the ground energy. -/
theorem ground_le_repair {ℓ : ℕ} (k p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) (hne : (vertexSet ℓ k).Nonempty) :
    ground k p t m d ≤
      4 * (RepairModel.totalMin p t m d (vertexSet ℓ k) : ℝ) / (Nat.choose ℓ k : ℝ) := by
  obtain ⟨c, hc⟩ := RepairModel.totalMin_attained p t m d (vertexSet ℓ k)
  simpa only [hc] using ground_le_color k p t m d hne c

/-- A genuine source-sector kernel vector forces zero actual ground energy. -/
theorem ground_zero_of_kernel {ℓ : ℕ} (k p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) (hker : HasSectorKernel k p t m d) : ground k p t m d = 0 := by
  obtain ⟨x, ⟨v, hv, hxv⟩, hrows⟩ := hker
  let : Nonempty (Sector ℓ k) := ⟨⟨v, hv⟩⟩
  apply RayleighMin.bottom_zero_of_kernel (matrix p t m d) (matrix_psd p t m d)
    (fun u => x u.val)
  · intro hx
    exact hxv (congrFun hx ⟨v, hv⟩)
  · intro u
    unfold matrix
    calc
      _ = ∑ w ∈ vertexSet ℓ k, signlessMatrix p t m d u.val w * x w :=
        sum_sector (fun w => signlessMatrix p t m d u.val w * x w)
      _ = 0 := hrows u.val u.property

/-- Every nonempty actual source sector has nonnegative ground energy. -/
theorem ground_nonneg {ℓ : ℕ} (k p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) (hne : (vertexSet ℓ k).Nonempty) : 0 ≤ ground k p t m d := by
  obtain ⟨v, hv⟩ := hne
  let : Nonempty (Sector ℓ k) := ⟨⟨v, hv⟩⟩
  exact RayleighMin.bottom_nonneg (matrix p t m d) (matrix_psd p t m d)

/-- Twisted-unknot repair removes exactly its actual loops in every particle sector. -/
theorem path_repair (N k : ℕ) :
    RepairModel.totalMin N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i) (vertexSet (N + 1) k) =
      loopSum N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i) (vertexSet (N + 1) k) := by
  apply RepairModel.bipartite_total N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i)
    (vertexSet (N + 1) k) PathModel.color
  intro v _ w _ h
  exact PathModel.hop_color ((path_adj_iff N v w).mp h)

/-- A genuine alternating-color Rayleigh test bounds the twisted-unknot ground energy. -/
theorem path_ground_le (N k : ℕ) (hk : k ≤ N + 1) :
    ground k N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i) ≤
      4 * (loopSum N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i)
        (vertexSet (N + 1) k) : ℝ) / (Nat.choose (N + 1) k : ℝ) := by
  have h := ground_le_repair k N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i)
    (path_connected N k hk).1
  simpa only [path_repair] using h

/-- The zero- and one-particle actual ground energies vanish by their genuine sector kernels. -/
theorem path_ground_zero (N k : ℕ) (hk : k ≤ 1) (hne : k ≤ N + 1) :
    ground k N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i) = 0 :=
  ground_zero_of_kernel k N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i)
    (path_sector_kernel N k hk hne)

/-- The exact binomial cancellation in the source twisted-unknot Rayleigh bound. -/
theorem path_binomial (N k : ℕ) (hk : 2 ≤ k) (hNk : k ≤ N + 1) :
    4 * ((N : ℝ) * (1 / 2) * (Nat.choose (N - 1) (k - 2) : ℝ)) /
        (Nat.choose (N + 1) k : ℝ) =
      2 * (k : ℝ) * ((k : ℝ) - 1) / ((N : ℝ) + 1) := by
  have hN : 1 ≤ N := by omega
  have h1 := Nat.add_one_mul_choose_eq (N - 1) (k - 2)
  rw [Nat.sub_add_cancel hN, show k - 2 + 1 = k - 1 by omega] at h1
  have h2 := Nat.add_one_mul_choose_eq N (k - 1)
  rw [Nat.sub_add_cancel (show 1 ≤ k by omega)] at h2
  have hnat : (N + 1) * N * Nat.choose (N - 1) (k - 2) =
      Nat.choose (N + 1) k * k * (k - 1) := by
    calc
      _ = (N + 1) * (N * Nat.choose (N - 1) (k - 2)) := by ring
      _ = (N + 1) * (Nat.choose N (k - 1) * (k - 1)) := by rw [h1]
      _ = ((N + 1) * Nat.choose N (k - 1)) * (k - 1) := by ring
      _ = _ := by rw [h2]
  have hr : ((N + 1 : ℕ) : ℝ) * (N : ℝ) * (Nat.choose (N - 1) (k - 2) : ℝ) =
      (Nat.choose (N + 1) k : ℝ) * (k : ℝ) * ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_sub (show 1 ≤ k by omega)] at hr
  have hcp : (0 : ℝ) < (Nat.choose (N + 1) k : ℝ) := by exact_mod_cast Nat.choose_pos hNk
  rw [div_eq_div_iff hcp.ne' (by positivity : (N : ℝ) + 1 ≠ 0)]
  nlinarith

end Qatlib.Papers.KhovanovHom25.MainResults.GraphSpectrum
