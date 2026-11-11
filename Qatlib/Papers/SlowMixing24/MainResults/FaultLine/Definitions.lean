/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SlowMixing24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# FaultLine/Definitions — geometric vocabulary of Section 4.4/4.5

Fixed arXiv:2411.04300v2. Regions (Definition 4.4/4.5), fault lines
(Definition 4.5) and the `c₀`-region families of Definition 4.6 (pp. 23--27).

These structures record the geometry used by Lemmas 4.4--4.18 without
committing to a particular lattice embedding; the analytic content of the
paper is stated over them in `Localization.lean`, `FeynmanKac.lean`,
`FaultLineSupport.lean` and `Locality.lean`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal BigOperators

namespace Qatlib.Papers.SlowMixing24.MainResults.FaultLine

open Qatlib.Papers.SlowMixing24.MainResults
open Qatlib.Concepts.LindbladFlow.GkslSemigroup
open Qatlib.Foundations.PureStateMath

/-- A connected region `R` of the lattice (Definition 4.4/4.5): a set of sites
together with its geometric boundary. -/
structure Region (n : ℕ) where
  /-- The sites of the region. -/
  carrier : Finset (Fin n)
  /-- Boundary size `|∂R|` in the lattice metric. -/
  boundarySize : ℕ
  /-- The region is connected (kept abstract). -/
  connected : Prop

/-- The complement region. -/
noncomputable def Region.compl {n : ℕ} (R : Region n) : Finset (Fin n) :=
  Finset.univ \ R.carrier

/-- A fault line (Definition 4.5): the set of defect bonds crossed by the
boundary between a region `R` and its complement, together with the number of
defects `k`. -/
structure FaultLine (n : ℕ) where
  /-- The region delimited by the fault line. -/
  region : Region n
  /-- The defect bonds (edge set of the lattice). -/
  defects : Finset (Fin n × Fin n)
  /-- The length `ℓ` of the fault line. -/
  length : ℕ
  /-- The number `k` of defects. -/
  k : ℕ
  /-- `k` is the number of defect bonds. -/
  k_eq : k = defects.card

/-- A family of geometric regions of size at most `c₀ √n`, as in Definition 4.6
and Lemma 4.13/4.14: the regions supporting `A` and `C` sit far from each
other and are separated by fault lines of at most `k` defects. -/
structure C0RegionFamily (n : ℕ) where
  /-- The region `R_A` carrying `A`. -/
  RA : Region n
  /-- The region `R_C` carrying `C`. -/
  RC : Region n
  /-- The constant `c₀`. -/
  c0 : ℝ
  /-- The maximal number `k` of defects on a fault line. -/
  k : ℕ
  /-- `c₀ > 0`. -/
  c0_pos : 0 < c0
  /-- `|R_A| ≤ c₀ √n`. -/
  sizeA : (RA.carrier.card : ℝ) ≤ c0 * Real.sqrt (n : ℝ)
  /-- `|R_C| ≤ c₀ √n`. -/
  sizeC : (RC.carrier.card : ℝ) ≤ c0 * Real.sqrt (n : ℝ)

/-- Graph distance between two lattice sites. In this model the lattice graph
is kept implicit, so the distance is the discrete metric; everything stated
with it is faithful to "sites at lattice distance `d`" only for `d = 1`
(disjointness), which is the usage of Definition 4.6 in the paper. -/
def sitesDist {n : ℕ} (x y : Fin n) : ℕ := if x = y then 0 else 1

/-- `A` and `C` are regions at distance at least `d` from each other. -/
def RegionsSeparated {n : ℕ} (F : C0RegionFamily n) (d : ℕ) : Prop :=
  ∀ x ∈ F.RA.carrier, ∀ y ∈ F.RC.carrier, d ≤ sitesDist x y

/-- The Gibbs weight of a region: sum of the matrix elements of `e^{-βH}`
between configurations in a set `S` (used in the Feynman--Kac expansion of
Lemma 4.8). -/
noncomputable def regionGibbs {n : ℕ} (H : Op n) (β : ℝ)
    (S : Finset (Fin (2 ^ n))) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ S, ((gibbsBolt H β) x y).re

/-- The projector `Π` of Lemma 4.11: its range is spanned by the
computational-basis configurations that contain a fault line with at most `k`
defects. -/
def ProjectsOntoFaultLines {n : ℕ} (P : Projector n) (k : ℕ) : Prop :=
  ∃ S : Finset (Fin (2 ^ n)),
    (∀ z : Fin (2 ^ n), P.mat z z ≠ 0 ↔ z ∈ S) ∧
      ∀ z ∈ S, ∃ F : FaultLine n, F.k ≤ k

/-- The `c₀`-regions `(A, B, C)` of Definition 4.6 of the 2D Ising model:
`A ⊆ S⁺`, `C ⊆ S⁻` are symmetric parts, `B` is the remainder, and every fault
line of a configuration in `A ∪ C` has at least `c₀ √n` defects. -/
structure C0Regions (n : ℕ) where
  /-- The constant `c₀`. -/
  c0 : ℝ
  /-- `c₀ > 0`. -/
  c0_pos : 0 < c0
  /-- Configurations of the plus region. -/
  A : Finset (St n)
  /-- Configurations of the bottleneck. -/
  B : Finset (St n)
  /-- Configurations of the minus region. -/
  C : Finset (St n)
  /-- `A ∪ B ∪ C` is everything. -/
  partition : A ∪ B ∪ C = Finset.univ
  /-- `A` and `B` are disjoint. -/
  disjoint_AB : Disjoint A B
  /-- `A` and `C` are disjoint. -/
  disjoint_AC : Disjoint A C
  /-- `B` and `C` are disjoint. -/
  disjoint_BC : Disjoint B C
  /-- Every configuration of `A` has a monochromatic plus crossing both from
  top to bottom and from left to right (Definition 4.6). -/
  plus_crossing : Prop
  /-- The analogous minus-crossing property for `C`. -/
  minus_crossing : Prop
  /-- Every fault line of a configuration in `A ∪ C` has at least `⌈c₀√n⌉`
  defects. -/
  few_defects : Prop

/-- The Lindbladian Gibbs sampler of [CKG23], as a structured package: `J`
constant-local jump operators on an `r`-dimensional lattice at inverse
temperature `β`. The analytic construction of (189) is kept abstract. -/
structure CKGSampler (n : ℕ) where
  /-- The Lindbladian. -/
  G : Gksl n
  /-- Number of constant-local jump operators. -/
  J : ℝ
  /-- `J > 0`. -/
  J_pos : 0 < J
  /-- Inverse temperature. -/
  β : ℝ
  /-- `β ≥ 0`. -/
  β_nonneg : 0 ≤ β
  /-- The lattice dimension. -/
  dim : ℕ
  /-- The underlying Hamiltonian is constant-local. -/
  constant_local : Prop

/-- A truncation of a [CKG23] sampler: `Gt` is obtained from `G` by replacing
the operators `B_a, L_a` by their truncations `B̃_a, L̃_a` of Eq. (191) at time
`R β`. -/
structure CKGTruncation {n : ℕ} (S : CKGSampler n) where
  /-- The truncated Lindbladian. -/
  Gt : Gksl n
  /-- The truncation time parameter `R`. -/
  R : ℝ
  /-- `R > 0`. -/
  R_pos : 0 < R
  /-- `Gt` is obtained by the truncation (191). -/
  is_truncation : Prop

/-- `X'` lies within distance `ρ` of the region `X`. In this model the lattice
geometry is kept one-dimensional, so the distance between sites `j, x : Fin n`
is `|j − x|` (the paper's Euclidean distance on the lattice). -/
def withinRadius {n : ℕ} (X' X : Finset (Fin n)) (ρ : ℝ) : Prop :=
  ∀ j ∈ X', ∃ x ∈ X, |(j : ℝ) - (x : ℝ)| ≤ ρ

end Qatlib.Papers.SlowMixing24.MainResults.FaultLine
