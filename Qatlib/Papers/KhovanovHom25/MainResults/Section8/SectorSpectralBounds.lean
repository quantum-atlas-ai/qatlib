/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.GraphSpectrum

/-!
# Computed fixed-sector repair and spectral bounds for twisted unknots

The graph data comes from the public Khovanov model. The statements use an
actual finite coloring minimum and an actual Rayleigh infimum, including
the factor of four in the energy estimate and the one-particle kernel.
Section 8 of [Schmidhuber et al.][SchmidhuberEtAl2025Khovanov] in
[arXiv v2](https://arxiv.org/abs/2501.12378v2) supplies the source problem.
-/

@[expose] public section

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.KhovanovHom25.MainResults
open Qatlib.Papers.KhovanovHom25.MainResults

/-- **Corrected Lemma31**, fixed v2 p.52: the actual finite-coloring repair
optimum decomposes into loop weight and optimal edge deletion, and every
concrete coloring supplies a computed upper certificate. The source's
base-cycle quantity `2ϒ` omits particle-sector lift multiplicities; it is
replaced here by the actual deleted-edge weight rather than assumed as a bound. -/
theorem repair_cost_decomposition_and_bound {ℓ k p t : ℕ} (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) (c : Vertex ℓ → Bool) :
    RepairModel.totalMin p t m d (vertexSet ℓ k) =
        loopSum p t m d (vertexSet ℓ k) + RepairModel.edgeMin p m (vertexSet ℓ k) ∧
      RepairModel.totalMin p t m d (vertexSet ℓ k) ≤
        loopSum p t m d (vertexSet ℓ k) + RepairModel.edgeCost p m (vertexSet ℓ k) c := by
  exact ⟨RepairModel.decomposition p t m d (vertexSet ℓ k),
    RepairModel.totalMin_le p t m d (vertexSet ℓ k) c⟩

/-- **Corrected Proposition32**, fixed v2 p.52: an actual alternating-color
Rayleigh test bounds the actual fixed-sector ground energy by four times the
computed repair optimum divided by the sector size. The factor four from
Theorem24 was missing in the source display and is retained here. -/
theorem ground_energy_le_repair_mean (n k p t : ℕ) (m : Fin p → Fin (n + k) × Fin (n + k))
    (d : Fin t → Fin (n + k)) (hcardpos : 0 < Nat.choose (n + k) k) :
    GraphSpectrum.ground k p t m d ≤
      4 * (RepairModel.totalMin p t m d (vertexSet (n + k) k) : ℝ) /
        (Nat.choose (n + k) k : ℝ) := by
  apply GraphSpectrum.ground_le_repair k p t m d
  apply Finset.card_pos.mp
  simpa only [vertexSet, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] using hcardpos

/-- **Corollary37**, fixed v2 p.54: the actual fixed-sector ground energy
is bounded by `2k(k-1)/(N+1)`. The proof constructs the alternating coloring
test, computes every loop, and performs the exact binomial cancellation.
No spectral upper bound is assumed. -/
theorem twisted_unknot_ground_energy_le (N n k : ℕ) (hk : n + k = N + 1) :
    GraphSpectrum.ground k N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i) ≤
      2 * (k : ℝ) * ((k : ℝ) - 1) / ((N : ℝ) + 1) := by
  have hNk : k ≤ N + 1 := by omega
  by_cases hk1 : k ≤ 1
  · rw [GraphSpectrum.path_ground_zero N k hk1 hNk]
    interval_cases k <;> norm_num
  · have hk2 : 2 ≤ k := by omega
    have hloop := theorem29_loop_sum (twistedUnknotEdges N) (fun i => Fin.elim0 i)
      (by intro a; apply Fin.ne_of_val_ne; simp only [twistedUnknotEdges, Fin.val_castSucc, Fin.val_succ]; omega)
      hk2 hNk
    have hbound := GraphSpectrum.path_ground_le N k hNk
    rw [hloop] at hbound
    norm_num only [Nat.cast_zero, zero_mul, zero_add, add_zero] at hbound
    have hsub : N + 1 - 2 = N - 1 := by omega
    rw [hsub] at hbound
    push_cast at hbound
    rwa [GraphSpectrum.path_binomial N k hk2 hNk] at hbound

/-- **Corollary37**, fixed v2 p.54: the zero- and one-particle sectors
have genuine nonzero kernel vectors. The alternating vector is evaluated
inside the requested sector, and its source-matrix equation is proved exactly. -/
theorem twisted_unknot_kernel_at_most_one_particle (N n k : ℕ) (hk : n + k = N + 1)
    (h0 : k = 0 ∨ k = 1) :
    HasSectorKernel k N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i) := by
  apply path_sector_kernel N k
  · rcases h0 with rfl | rfl <;> omega
  · omega

end Qatlib.Papers.KhovanovHom25.MainResults
