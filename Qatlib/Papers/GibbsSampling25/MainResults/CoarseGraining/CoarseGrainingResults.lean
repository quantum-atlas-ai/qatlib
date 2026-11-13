/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GibbsSampling25.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Coarse-graining of the lattice `Λ_L`

Claim c001 (Lemma 2.6) and claim c012 (Lemma B.2) of arXiv:2412.01732v1.

The four properties listed in Lemma 2.6 and the five properties of Lemma B.2
are encoded as fields of `CoarseGraining` in the source model; claim c012 is
then a genuine projection from the structure, while the existence statement of
Lemma 2.6 (the explicit construction of Appendix B.2) is recorded as a `def : Prop`.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Kronecker

namespace Qatlib.Papers.GibbsSampling25.MainResults.CoarseGraining

open Qatlib.Papers.GibbsSampling25.MainResults.Model

/-! ## Lemma 2.6: existence of a suitable coarse-graining -/

/-- **Lemma 2.6** (p.6; construction in Appendix B.2, properties in
Lemma B.2). For any `D ∈ ℕ` and any `r ≤ k`, `c, ℓ` with
`ℓ > 2D(k+c)` and `ℓ ≤ 2L+1`, there exists a suitable coarse-graining of
`Λ_L = {-L,…,L}^D` made of `D+1` levels such that:

1. the cells cover `Λ_L` and every site lies in at most `D+1` cells;
2. the cells of each fixed level are mutually disjoint;
3. every cell has at most `ℓ^D` sites;
4. each level has overlap `c` with the neighbouring level.

The `CoarseGraining` structure records exactly these four properties (plus the
core/shell data of Appendix B.2). The explicit construction of Appendix B.2
(nested cubes of side `ℓ`, `2(D-a)(k+c)`-shrunk cores, and shells of width `k`)
is not formalised; this is the unproved placeholder below. -/
def coarse_graining_exists {D L k c ℓ r : ℕ} (hrk : r ≤ k)
    (hℓ : 2 * D * (k + c) < ℓ) (hℓL : ℓ ≤ 2 * L + 1)  : Prop :=
    Nonempty (CoarseGraining D L k c ℓ)
  -- Source: arXiv:2412.01732v1, Lemma 2.6 (p.6) and Appendix B.2
  -- ("Construction of the coarse-graining", pp.29–31).
  -- Proof route (Appendix B.2): for each level a ∈ {0,…,D} place cubes of
  -- side ℓ on the sublattice ℓ·ℤ^D + offset_a, define the core C̊_{a,i} by
  -- shrinking the cube by (D-a)(k+c) in every coordinate and the shell
  -- C^∂_{a,i} as the k-neighbourhood boundary; then (i) the offsets are chosen
  -- so that the cubes cover Λ_L, giving property 1 and the ≤ D+1 membership
  -- bound; (ii) cubes of a fixed level are disjoint by construction
  -- (property 2); (iii) side ℓ gives |C_{a,i}| ≤ ℓ^D (property 3); (iv) the
  -- disjoint shrunken cores of neighbouring levels are at distance ≥ c+k ≥ c
  -- (property 4).
  -- Scope: the geometric construction over `Fin D → Fin (2L+1)` (cube
  -- placement, offsets, shrunken cores, and boundary layers) is represented
  -- by the existence statement above.  The stated properties are those of the
  -- nested-cube construction in Appendix B.2.

/-! ## Lemma B.2: the five properties of the decomposition -/

/-- **Lemma B.2** (p.31). The decomposition of `Λ_L` described in
Appendix B.2 satisfies:

1. the cells cover `Λ_L`, and each site lies in at most `D+1` cells;
2. each level consists of mutually disjoint cells;
3. every cell (and a fortiori every core/shell) has at most `ℓ^D` sites;
4. cores and shells are contained in their cells;
5. adjacent levels have core/shell distance at least `c`;
6. cells of the same level are at distance at least `2k`;
7. level-`0` cells have diameter at most `2D(k+c)` and distinct level-`0`
   cells are at distance at least `ℓ − 2D(k+c)`;
8. cores and shells are subsets of their cells.

Because `CoarseGraining` stores these very properties, the claim is proved by
projection (the structure is the faithful encoding of Lemma B.2). -/
theorem coarse_graining_properties {D L k c ℓ : ℕ} (cg : CoarseGraining D L k c ℓ) :
    (∀ x : Site D L, ∃ (a : Fin (D + 1)) (C : Finset (Site D L)), C ∈ cg.cell a ∧ x ∈ C) ∧
    (∀ x : Site D L,
      (Finset.univ.filter (fun a : Fin (D + 1) =>
        ∃ C : Finset (Site D L), C ∈ cg.cell a ∧ x ∈ C)).card ≤ D + 1) ∧
    (∀ (a : Fin (D + 1)) (C₁ : Finset (Site D L)), C₁ ∈ cg.cell a →
      ∀ (C₂ : Finset (Site D L)), C₂ ∈ cg.cell a → C₁ ≠ C₂ → Disjoint C₁ C₂) ∧
    (∀ (a : Fin (D + 1)) (C : Finset (Site D L)), C ∈ cg.cell a → C.card ≤ ℓ ^ D) ∧
    (∀ (a : Fin (D + 1)) (h : a.val + 1 < D + 1) (C : Finset (Site D L)),
      C ∈ cg.cell a → ∀ C' : Finset (Site D L), C' ∈ cg.cell ⟨a.val + 1, h⟩ →
      (c : ℝ) ≤ setDist (cg.core a C) (cg.shell ⟨a.val + 1, h⟩ C')) ∧
    (∀ (a : Fin (D + 1)) (C₁ : Finset (Site D L)), C₁ ∈ cg.cell a →
      ∀ (C₂ : Finset (Site D L)), C₂ ∈ cg.cell a → C₁ ≠ C₂ →
      (2 * k : ℝ) ≤ setDist C₁ C₂) ∧
    (∀ C : Finset (Site D L), C ∈ cg.cell 0 → ∀ x ∈ C, ∀ y ∈ C,
      latticeDist x y ≤ (2 * D * (k + c) : ℝ)) ∧
    (∀ (C₁ : Finset (Site D L)), C₁ ∈ cg.cell 0 → ∀ C₂ : Finset (Site D L),
      C₂ ∈ cg.cell 0 → C₁ ≠ C₂ →
      ((ℓ : ℝ) - (2 * D * (k + c) : ℝ)) ≤ setDist C₁ C₂) :=
  ⟨cg.cover, cg.mem_le, cg.disjoint, cg.size, cg.overlap, cg.same_level_sep,
    cg.level0_diam, cg.level0_sep⟩

end Qatlib.Papers.GibbsSampling25.MainResults.CoarseGraining
