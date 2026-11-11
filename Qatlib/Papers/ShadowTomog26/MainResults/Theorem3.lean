/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ShadowTomog26.MainResults.Core
import Qatlib.Papers.ShadowTomog26.MainResults.Theorem1

/-!
# Block-product graph-body minimax bounds

This module encodes the block-product optimization of Theorem 3 in [XuEtAl2026]. `BlockFamily`
records local bodies and their coordinatewise product inclusion in a common outer body;
`blockForm`, `betaProduct`, and `deltaTauBlock` give the weighted product objective and its
simplex infimum.

The construction `toBodies` turns the product body into a `GraphBodies` instance. This transfers
the global bounds and exact-value statements, with the theta identity, combined-body perfection,
and equality of graph parameters supplied where needed.

## Main statements

* `betaProduct_eq_support` and `delta_toBodies` identify the block and global formulations.
* `source_theorem3_lower` and `source_theorem3_interval` bound the block value.
* `source_theorem3_tight_hperfect` and `source_theorem3_tight_perfect` give sufficient
  conditions for equality.
* `source_theorem3_beta_product_form` exposes the nested infimum and supremum formula.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ShadowTomog26.MainResults

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {Blk : Type*} [Fintype Blk] [DecidableEq Blk]

/-- Data for a finite family of local bodies in the coordinatewise unit cube and a common
nonempty outer body containing all their coordinatewise products. It also specifies a union
graph, a complementary Lovasz parameter, and a product representation for every
independent-set indicator of that graph. -/
structure BlockFamily (V : Type*) (Blk : Type*) [Fintype V] [DecidableEq V] [Fintype Blk] where
  Gunion : SimpleGraph V
  BETA : Blk → Set (V → ℝ)
  TH : Set (V → ℝ)
  lovaszComplement : ℝ
  beta_nonempty : ∀ j, (BETA j).Nonempty
  th_nonempty : TH.Nonempty
  beta_unit : ∀ j v, v ∈ BETA j → ∀ i, 0 ≤ v i ∧ v i ≤ 1
  th_unit : ∀ v ∈ TH, ∀ i, 0 ≤ v i ∧ v i ≤ 1

  product_subset_theta : ∀ t : Blk → V → ℝ, (∀ j, t j ∈ BETA j) →
    (fun i => ∏ j, t j i) ∈ TH

  stab_subset_beta : ∀ I : Finset V, Gunion.IsIndepSet (I : Set V) →
    ∃ t : Blk → V → ℝ, (∀ j, t j ∈ BETA j) ∧
      ∀ i, (if i ∈ I then (1 : ℝ) else 0) = ∏ j, t j i

variable (F : BlockFamily V Blk)

/-- The weighted sum `∑ i, w i * ∏ j, t j i` of coordinatewise products of block vectors. -/
def blockForm (w : V → ℝ) (t : Blk → V → ℝ) : ℝ := ∑ i, w i * ∏ j, t j i

/-- The set of vertex vectors obtained as coordinatewise products of one vector from each local
body `F.BETA j`. -/
def blockBody : Set (V → ℝ) :=
  {v | ∃ t : Blk → V → ℝ, (∀ j, t j ∈ F.BETA j) ∧ ∀ i, v i = ∏ j, t j i}

/-- The supremum of `blockForm w t` over choices of one vector `t j` from each local body. -/
def betaProduct (w : V → ℝ) : ℝ :=
  sSup {x : ℝ | ∃ t : Blk → V → ℝ, (∀ j, t j ∈ F.BETA j) ∧ x = blockForm w t}

/-- The infimum of the block-product support value `betaProduct F w` over vertex probability
weights. -/
def deltaTauBlock : ℝ := sInf ((fun w => betaProduct F w) '' probSimplex V)

omit [Nonempty V] [DecidableEq Blk] in

/-- The support value of `blockBody F` equals the supremum defining `betaProduct F`. -/
lemma betaProduct_eq_support (w : V → ℝ) :
    supportFun (blockBody F) w = betaProduct F w := by
  unfold supportFun betaProduct
  congr 1
  ext x
  constructor
  · rintro ⟨v, ⟨t, ht, hv⟩, rfl⟩
    refine ⟨t, ht, ?_⟩
    unfold blockForm
    exact Finset.sum_congr rfl (fun i _ => by rw [hv i])
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun i => ∏ j, t j i, ⟨t, ht, fun i => rfl⟩, ?_⟩
    rfl

omit [Nonempty V] [DecidableEq Blk] in

/-- The coordinatewise product body is nonempty because every local body is nonempty. -/
lemma blockBody_nonempty : (blockBody F).Nonempty := by
  let t : Blk → V → ℝ := fun j => Classical.choose (F.beta_nonempty j)
  have ht : ∀ j, t j ∈ F.BETA j := fun j => Classical.choose_spec (F.beta_nonempty j)
  exact ⟨fun i => ∏ j, t j i, t, ht, fun i => rfl⟩

omit [Nonempty V] [DecidableEq Blk] in

/-- The coordinatewise product body is contained in the common outer body `F.TH`. -/
lemma blockBody_subset_theta : blockBody F ⊆ F.TH := by
  rintro v ⟨t, ht, hv⟩
  have hp := F.product_subset_theta t ht
  have hveq : v = (fun i => ∏ j, t j i) := funext hv
  rw [hveq]; exact hp

omit [Nonempty V] [DecidableEq Blk] in

/-- Every coordinate of every point in the block-product body lies between zero and one. -/
lemma blockBody_unit : ∀ v ∈ blockBody F, ∀ i, 0 ≤ v i ∧ v i ≤ 1 := by
  rintro v ⟨t, ht, hv⟩ i
  rw [hv i]
  exact ⟨Finset.prod_nonneg (fun j _ => (F.beta_unit j (t j) (ht j) i).1),
    Finset.prod_le_one₀ (fun j _ => (F.beta_unit j (t j) (ht j) i).1)
      (fun j _ => (F.beta_unit j (t j) (ht j) i).2)⟩

/-- The `GraphBodies` system with graph `F.Gunion`, beta body `blockBody F`, and outer body
`F.TH`. Its required inclusions and coordinate bounds follow from the fields of `F`. -/
def toBodies : GraphBodies V where
  G := F.Gunion
  BETA := blockBody F
  TH := F.TH
  lovaszComplement := F.lovaszComplement
  beta_nonempty := blockBody_nonempty F
  theta_nonempty := F.th_nonempty
  beta_subset_theta := blockBody_subset_theta F
  beta_unit := blockBody_unit F
  theta_unit := F.th_unit
  stab_subset_beta := fun I hI => F.stab_subset_beta I hI

omit [Nonempty V] [DecidableEq Blk] in

/-- The global beta simplex infimum of `toBodies F` equals the block parameter `deltaTauBlock
F`. -/
lemma delta_toBodies : delta (toBodies F) = deltaTauBlock F := by
  have hb : ∀ w, beta (toBodies F) w = betaProduct F w := fun w => by
    unfold beta
    exact betaProduct_eq_support F w
  unfold delta deltaTauBlock
  congr 1
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, (hb w).symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, hb w⟩

omit [DecidableEq Blk] in

/-- The block parameter is at least the reciprocal fractional chromatic number of the union
graph [XuEtAl2026]. -/
theorem source_theorem3_lower :
    1 / fractionalChromatic F.Gunion ≤ deltaTauBlock F := by
  have h := source_theorem1_lower (toBodies F)
  rw [delta_toBodies F] at h
  exact h

omit [DecidableEq Blk] in

/-- Assuming the theta-minimum identity for `toBodies F`, the block parameter lies between the
reciprocal fractional chromatic number of the union graph and the reciprocal stored
complementary Lovasz parameter. -/
theorem source_theorem3_interval (h38 : thetaMin (toBodies F) = 1 / F.lovaszComplement) :
    1 / fractionalChromatic F.Gunion ≤ deltaTauBlock F ∧
      deltaTauBlock F ≤ 1 / F.lovaszComplement := by
  have h := source_theorem1_bounds (toBodies F) h38
  rw [delta_toBodies F] at h
  exact h

omit [DecidableEq Blk] in

/-- If the combined graph-body system `toBodies F` is hbar-perfect, the block parameter equals
the reciprocal fractional chromatic number of the union graph. -/
theorem source_theorem3_tight_hperfect (h : IsHPerfect (toBodies F)) :
    deltaTauBlock F = 1 / fractionalChromatic F.Gunion := by
  have h1 := source_theorem1_hperfect (toBodies F) h
  rw [← delta_toBodies F]
  simpa [toBodies] using h1

omit [DecidableEq Blk] in

/-- If the theta-minimum identity holds and the union graph's fractional chromatic number equals
the stored complementary Lovasz parameter, the block parameter equals their common
reciprocal. -/
theorem source_theorem3_tight_perfect (h38 : thetaMin (toBodies F) = 1 / F.lovaszComplement)
    (hcoinc : fractionalChromatic F.Gunion = F.lovaszComplement) :
    deltaTauBlock F = 1 / fractionalChromatic F.Gunion := by
  obtain ⟨hlo, hhi⟩ := source_theorem3_interval F h38
  have : 1 / F.lovaszComplement = 1 / fractionalChromatic F.Gunion := by rw [← hcoinc]
  rw [this] at hhi
  exact le_antisymm hhi hlo

omit [Nonempty V] [DecidableEq Blk] in

/-- The block parameter is the simplex infimum of the supremum of `∑ i, w i * ∏ j, t j i` over
vectors from the local bodies. This is the defining nested optimization written explicitly. -/
theorem source_theorem3_beta_product_form :
    deltaTauBlock F
      = sInf ((fun w => sSup {x : ℝ | ∃ t : Blk → V → ℝ,
          (∀ j, t j ∈ F.BETA j) ∧ x = blockForm w t}) '' probSimplex V) := rfl

end Qatlib.Papers.ShadowTomog26.MainResults
