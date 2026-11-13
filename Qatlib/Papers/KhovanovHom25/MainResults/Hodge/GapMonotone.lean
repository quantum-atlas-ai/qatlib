/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KhovanovHom25.MainResults.Hodge.ChainMap

set_option backward.isDefEq.respectTransparency false

/-!
# Monotonicity of the Hodge Spectral Gap under Chain Maps and R1 Moves

This module proves Propositions 17 and 18 on the Hodge spectral gap of cochain
complexes: any degreewise injective chain map whose adjoint is also a chain map
intertwines the Hodge Laplacians, transports nonzero eigenvectors while preserving
their eigenvalues, and therefore cannot increase the positive spectral gap.

## Main statements

* `chainMap_comm_lap`: a chain map with chain-map adjoint commutes with the Hodge Laplacians.
* `proposition17_eigenvector_transport`: injective chain maps transport nonzero Laplacian eigenvectors.
* `proposition17_gap_monotone`: monotonicity `spectralGap L i ≤ spectralGap K i` of the Hodge gap.
* `proposition17`: combined eigenvector-transport and gap-monotonicity theorem.
* `proposition18`: specialization of Hodge gap monotonicity to Reidemeister `R1` moves.

## References

* [Schmidhuber et al., 2025][SchmidhuberEtAl2025Khovanov], Propositions 17 and 18,
  Section 6.2--6.3, pp. 36--37.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open scoped BigOperators ComplexInnerProductSpace

namespace Qatlib.Papers.KhovanovHom25.MainResults

open CochainComplex

variable {K L : CochainComplex}

/-- `f` commutes with the Hodge Laplacians when it is a chain map and its
adjoint is a chain map. -/
theorem chainMap_comm_lap (f : ChainMap K L) (hf : f.AdjointChainMap) :
    ∀ (i : ℕ) (x : K.C i), f.f i (K.lap i x) = L.lap i (f.f i x)
  | 0, x => by
    have hK : K.lap 0 x = K.dAdj 0 (K.d 0 x) := by simp [lap, lapDown]
    have hL : L.lap 0 (f.f 0 x) = L.dAdj 0 (L.d 0 (f.f 0 x)) := by
      simp [lap, lapDown]
    rw [hK, hL, ← f.comm 0 x, ← hf 0 (K.d 0 x)]
  | i + 1, x => by
    have hK : K.lap (i + 1) x =
        K.dAdj (i + 1) (K.d (i + 1) x) + K.d i (K.dAdj i x) := by
      simp [lap, lapDown]
    have hL : L.lap (i + 1) (f.f (i + 1) x) =
        L.dAdj (i + 1) (L.d (i + 1) (f.f (i + 1) x)) +
          L.d i (L.dAdj i (f.f (i + 1) x)) := by
      simp [lap, lapDown]
    rw [hK, hL, map_add, hf (i + 1) (K.d (i + 1) x), f.comm (i + 1) x,
      f.comm i (K.dAdj i x), hf i x]

/-- **Proposition 17 (eigenvector transport)**: under an injective chain map whose adjoint
is a chain map, a nonzero eigenvector of `Δ^K` is mapped to a nonzero eigenvector of `Δ^L`
with the same eigenvalue. -/
theorem proposition17_eigenvector_transport (f : ChainMap K L)
    (hf : f.AdjointChainMap) (i : ℕ) (hinj : Function.Injective (f.f i))
    {lam : ℂ} {x : K.C i} (hx : x ≠ 0) (h : K.lap i x = lam • x) :
    f.f i x ≠ 0 ∧ L.lap i (f.f i x) = lam • f.f i x := by
  refine ⟨?_, ?_⟩
  · intro hzero
    apply hx
    apply hinj
    rw [hzero, map_zero]
  · rw [← chainMap_comm_lap f hf i x, h, map_smul]

namespace CochainComplex

/-- The positive spectrum of the Hodge Laplacian `Δᵢ`. -/
def positiveSpectrum (K : CochainComplex) (i : ℕ) : Set ℝ :=
  {r : ℝ | 0 < r ∧ ∃ x : K.C i, x ≠ 0 ∧
    K.lap i x = (r : ℂ) • x}

/-- The Hodge spectral gap of `Δᵢ`, defined as the infimum of its positive spectrum. -/
def spectralGap (K : CochainComplex) (i : ℕ) : ℝ :=
  sInf (CochainComplex.positiveSpectrum K i)

end CochainComplex

/-- **Proposition 17 (gap monotonicity)**: if `f` is an injective chain map in degree `i`
whose adjoint is a chain map and `Δᵢ^K` has nonempty positive spectrum, then
`spectralGap L i ≤ spectralGap K i`. -/
theorem proposition17_gap_monotone (f : ChainMap K L)
    (hf : f.AdjointChainMap) (i : ℕ) (hinj : Function.Injective (f.f i))
    (hne : (CochainComplex.positiveSpectrum K i).Nonempty) :
    CochainComplex.spectralGap L i ≤ CochainComplex.spectralGap K i := by
  have hsub : CochainComplex.positiveSpectrum K i ⊆ CochainComplex.positiveSpectrum L i := by
    rintro r ⟨hr, x, hx, hlap⟩
    obtain ⟨hfx, hflap⟩ := proposition17_eigenvector_transport f hf i hinj hx hlap
    exact ⟨hr, f.f i x, hfx, hflap⟩
  have hbdd : BddBelow (CochainComplex.positiveSpectrum L i) := by
    refine ⟨0, ?_⟩
    rintro r ⟨hr, -⟩
    exact le_of_lt hr
  exact csInf_le_csInf hbdd hne hsub

/-- **Proposition 17**: combined eigenvector-transport and Hodge spectral-gap monotonicity. -/
theorem proposition17 (f : ChainMap K L) (hf : f.AdjointChainMap) (i : ℕ)
    (hinj : Function.Injective (f.f i)) :
    (∀ {lam : ℂ} {x : K.C i}, x ≠ 0 → K.lap i x = lam • x →
        f.f i x ≠ 0 ∧ L.lap i (f.f i x) = lam • f.f i x) ∧
      ((CochainComplex.positiveSpectrum K i).Nonempty →
        CochainComplex.spectralGap L i ≤ CochainComplex.spectralGap K i) :=
  ⟨fun hx h => proposition17_eigenvector_transport f hf i hinj hx h,
    fun hne => proposition17_gap_monotone f hf i hinj hne⟩

/-- Data of a Reidemeister `R1` move: two cochain complexes related by a degreewise
injective chain map `F` whose adjoint is also a chain map. -/
structure R1Data where
  /-- The source cochain complex. -/
  C : CochainComplex
  /-- The target cochain complex. -/
  D : CochainComplex
  /-- The `R1` chain map `F₁`. -/
  F : ChainMap C D
  /-- `F₁` is injective in every degree. -/
  inj : ∀ i, Function.Injective (F.f i)
  /-- The adjoint of `F₁` is again a chain map. -/
  adj : F.AdjointChainMap

/-- **Proposition 18**: the Hodge spectral gap never increases under a Reidemeister `R1` move. -/
theorem proposition18 (R : R1Data) (i : ℕ)
    (hne : (CochainComplex.positiveSpectrum R.C i).Nonempty) :
    CochainComplex.spectralGap R.D i ≤ CochainComplex.spectralGap R.C i :=
  proposition17_gap_monotone R.F R.adj i (R.inj i) hne

end Qatlib.Papers.KhovanovHom25.MainResults
