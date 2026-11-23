/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PairAdjoint
public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.FlowEnergy
public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.GraphSpectrum

/-!
# Exact quadratic and ground-energy bridge for two particles

The ordered-pair encoding is an equivalence with the actual two-particle
sector. Multiplying by the proved parity sign preserves mass and changes the
source signless edge squares into the difference squares of the actual pair
flow. The finite-flow lower bound therefore applies to the actual source
matrix, rather than to a free scalar or an assumed spectral inequality.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace Qatlib.Papers.KhovanovHom25.MainResults.PairEnergy

open Qatlib.Papers.KhovanovHom25.MainResults

/-- The ordered-pair encoding is a genuine equivalence with the source two-particle sector. -/
def sectorEquiv (N : ℕ) : PairFlow.Pair N ≃ GraphSpectrum.Sector (N + 1) 2 :=
  Equiv.ofBijective (fun p => ⟨PairBridge.vertex p, PairBridge.vertex_mem p⟩) (by
    constructor
    · intro p q h
      exact PairBridge.vertex_injective (congrArg Subtype.val h)
    · intro v
      obtain ⟨p, hp⟩ := PairBridge.vertex_surjective v.val v.property
      exact ⟨p, Subtype.ext hp⟩)

/-- The equivalence evaluates to the actual occupied-site pair. -/
theorem sectorEquiv_val (N : ℕ) (p : PairFlow.Pair N) :
    (sectorEquiv N p).val = PairBridge.vertex p := rfl

/-- A source vector is transported through the actual parity conjugation. -/
def transform {N : ℕ} (x : GraphSpectrum.Sector (N + 1) 2 → ℝ) (p : PairFlow.Pair N) : ℝ :=
  SectorKernel.sign PathModel.color (PairBridge.vertex p) * x (sectorEquiv N p)

/-- The actual parity conjugation and coordinate equivalence preserve squared mass. -/
theorem mass_eq {N : ℕ} (x : GraphSpectrum.Sector (N + 1) 2 → ℝ) :
    PairFlow.mass (transform x) = RayleighMin.mass x := by
  unfold PairFlow.mass transform RayleighMin.mass
  simp only [mul_pow, WeightedForm.sign_sq, one_mul]
  exact (sectorEquiv N).sum_comp (fun v => x v ^ 2)

/-- On an actual edge, parity conjugation changes a difference square into a signless square. -/
theorem edge_square {N : ℕ} (x : GraphSpectrum.Sector (N + 1) 2 → ℝ)
    (p q : PairFlow.Pair N) (h : PairFlow.Adj p q) :
    (transform x p - transform x q) ^ 2 =
      (x (sectorEquiv N p) + x (sectorEquiv N q)) ^ 2 := by
  have hc := PathModel.hop_color (PairBridge.pair_hop p q h)
  have hs := SectorKernel.sign_flip PathModel.color hc
  unfold transform
  rw [hs]
  have hfactor :
      SectorKernel.sign PathModel.color (PairBridge.vertex p) * x (sectorEquiv N p) -
        -SectorKernel.sign PathModel.color (PairBridge.vertex p) * x (sectorEquiv N q) =
      SectorKernel.sign PathModel.color (PairBridge.vertex p) *
        (x (sectorEquiv N p) + x (sectorEquiv N q)) := by ring
  rw [hfactor, mul_pow, WeightedForm.sign_sq, one_mul]

/-- The transported pair-flow energy is exactly the actual source matrix quadratic form. -/
theorem quadratic_eq {N : ℕ} (x : GraphSpectrum.Sector (N + 1) 2 → ℝ) :
    PairFlow.energy (transform x) =
      RayleighMin.quadratic
        (GraphSpectrum.matrix N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i)) x := by
  rw [GraphSpectrum.matrix_eq, WeightedForm.quadratic_energy]
  · have hloops : (∑ v : GraphSpectrum.Sector (N + 1) 2,
        GraphSpectrum.loop N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i) v * x v ^ 2) =
        ∑ p : PairFlow.Pair N, if PairFlow.IsLoop p then x (sectorEquiv N p) ^ 2 / 2 else 0 := by
      rw [← (sectorEquiv N).sum_comp]
      apply Finset.sum_congr rfl
      intro p _
      simp only [GraphSpectrum.loop, sectorEquiv_val, PairBridge.vertex_loop]
      split_ifs <;> norm_num
      ring
    have hedges : (∑ v : GraphSpectrum.Sector (N + 1) 2,
        ∑ u : GraphSpectrum.Sector (N + 1) 2,
          GraphSpectrum.edge N (twistedUnknotEdges N) v u * (x v + x u) ^ 2) =
        ∑ p : PairFlow.Pair N, ∑ q : PairFlow.Pair N,
          if PairFlow.Adj p q then (transform x p - transform x q) ^ 2 else 0 := by
      rw [← (sectorEquiv N).sum_comp]
      apply Finset.sum_congr rfl
      intro p _
      rw [← (sectorEquiv N).sum_comp]
      apply Finset.sum_congr rfl
      intro q _
      simp only [GraphSpectrum.edge, sectorEquiv_val, PairBridge.pair_edge]
      by_cases h : PairFlow.Adj p q
      · rw [ite_eq_left h, ite_eq_left h]
        simp only [Nat.cast_one, one_mul]
        exact (edge_square x p q h).symm
      · simp only [ite_eq_right h, Nat.cast_zero, zero_mul]
    rw [hloops, hedges]
    unfold PairFlow.energy PairFlow.loopEnergy PairFlow.edgeEnergy transform
    simp only [mul_pow, WeightedForm.sign_sq, one_mul]
    have heq : (∑ p : PairFlow.Pair N, if PairFlow.IsLoop p then x (sectorEquiv N p) ^ 2 / 2 else 0) =
        (∑ p : PairFlow.Pair N, if PairFlow.IsLoop p then x (sectorEquiv N p) ^ 2 else 0) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> simp only [zero_div]
    rw [heq]
    ring
  · intro v
    rw [GraphSpectrum.edge, GraphEdges.weight_diag, Nat.cast_zero]
  · intro v u
    unfold GraphSpectrum.edge
    exact_mod_cast GraphEdges.weight_symm N (twistedUnknotEdges N) v.val u.val

/-- Every actual nonzero source Rayleigh test satisfies the constructive two-particle gap. -/
theorem quotient_lower {N : ℕ} (x : GraphSpectrum.Sector (N + 1) 2 → ℝ) (hx : x ≠ 0) :
    1 / (2 * ((N : ℝ) + 1) ^ 2) ≤
      RayleighMin.quotient
        (GraphSpectrum.matrix N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i)) x := by
  have hmass : 0 < PairFlow.mass (transform x) := by
    rw [mass_eq]
    exact RayleighMin.mass_pos x hx
  have h := PairFlow.ratio_lower (transform x) hmass
  simpa only [mass_eq, quadratic_eq, RayleighMin.quotient] using h

/-- The actual two-particle source ground energy has a uniform positive lower bound. -/
theorem ground_lower (N : ℕ) (hN : 1 ≤ N) :
    1 / (2 * ((N : ℝ) + 1) ^ 2) ≤
      GraphSpectrum.ground 2 N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i) := by
  obtain ⟨v, hv⟩ := (path_connected N 2 (by omega)).1
  let : Nonempty (GraphSpectrum.Sector (N + 1) 2) := ⟨⟨v, hv⟩⟩
  unfold GraphSpectrum.ground RayleighMin.bottom
  apply le_csInf
  · refine ⟨RayleighMin.quotient
      (GraphSpectrum.matrix N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i)) (fun _ => 1),
      (fun _ => 1), ?_, rfl⟩
    intro h
    have hh := congrFun h ⟨v, hv⟩
    norm_num at hh
  · rintro r ⟨x, hx, rfl⟩
    exact quotient_lower x hx

end Qatlib.Papers.KhovanovHom25.MainResults.PairEnergy
