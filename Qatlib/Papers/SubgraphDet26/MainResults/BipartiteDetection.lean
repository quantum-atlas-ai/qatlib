/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SubgraphDet26.MainResults.CertificateSearch

set_option backward.isDefEq.respectTransparency false

/-!
# Complete bipartite graph detection (Theorem 1.4; §5.3)

Paper: Gilani–Zhou, *Superlinear Quantum Query Lower Bounds for Subgraph Detection*,
fixed arXiv:2609.40263v1.

* Theorem 1.4, Eqs. (4), (5): the `K_{r,r}`-detection exponent sequence `β_r`;
* Theorem 5.4, Eq. (64): the `K_{r,r}` lower bound for fixed `2 ≤ h < r`;
* Lemma 5.5: the bipartite graph with bounded matching extensions;
* Lemma 5.6, Eq. (67): `m(K_{r,r}, h) = r(h−1)`;
* Corollary 5.7, Eq. (69): the sequence `β_r` of Eq. (68).

Theorem 1.4, Theorem 5.4, Lemma 5.5, Lemma 5.6 and Corollary 5.7 were removed:
their proofs need the certificate-count and crossing-count estimates for the random
bipartite graph of Lemma 5.5 and König's theorem (Lemma 5.6), none of which are in
the library; the statements are preserved in the branch history at `161317a85`.

The input model is the balanced bipartite adjacency matrix `Fin n × Fin n → Bool`
(the paper promises a known bipartition; a general `n`-vertex graph has `n/2` per
part, and the exponent is unaffected by this normalisation).
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Qatlib.Papers.SubgraphDet26.MainResults

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Matrix

/-! ## Bipartite graphs, inputs and certificates -/

/-- A bipartite graph with parts `Fin a` and `Fin b`, given by its adjacency `Bool`
matrix. -/
structure BipGraph (a b : ℕ) where
  adj : Fin a → Fin b → Bool

/-- `x` contains a copy of `K_{r,r}` (an `r × r` all-ones submatrix). -/
def bipContainsCopy {a b : ℕ} (x : Fin a × Fin b → Bool) (r : ℕ) : Prop :=
  ∃ s : Finset (Fin a) × Finset (Fin b),
    s.1.card = r ∧ s.2.card = r ∧ ∀ u ∈ s.1, ∀ v ∈ s.2, x (u, v) = true

/-- The bipartite detection function `Sub_{K_{r,r}}` on balanced bipartite inputs. -/
def BipDetectFunction (a b r : ℕ) : (Fin a × Fin b → Bool) → Bool :=
  fun x => if bipContainsCopy x r then true else false

/-- Edge-set certificates of the possible `K_{r,r}` copies. -/
def bipCertificateFamily (a b r : ℕ) : Finset (Finset (Fin a × Fin b)) :=
  (Finset.univ.filter (fun s : Finset (Fin a) × Finset (Fin b) =>
    s.1.card = r ∧ s.2.card = r)).image (fun s => s.1.product s.2)

/-- Number of `K_{r,r}` copies in a bipartite graph. -/
def bipCliqueCount {a b : ℕ} (G : BipGraph a b) (r : ℕ) : ℕ :=
  (Finset.univ.filter (fun s : Finset (Fin a) × Finset (Fin b) =>
    s.1.card = r ∧ s.2.card = r ∧
      ∀ u ∈ s.1, ∀ v ∈ s.2, G.adj u v = true)).card

/-- The edge sets of the `K_{r,r}` copies of `G` (the family `F` of Lemma 5.5). -/
def bipCopyEdgeFamily {a b : ℕ} (G : BipGraph a b) (r : ℕ) :
    Finset (Finset (Fin a × Fin b)) :=
  (Finset.univ.filter (fun s : Finset (Fin a) × Finset (Fin b) =>
    s.1.card = r ∧ s.2.card = r ∧
      ∀ u ∈ s.1, ∀ v ∈ s.2, G.adj u v = true)).image (fun s => s.1.product s.2)

/-- A matching in a bipartite graph with possibly different part sizes. -/
def IsMatchingPair {a b : ℕ} (M : Finset (Fin a × Fin b)) : Prop :=
  ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → e1.1 ≠ e2.1 ∧ e1.2 ≠ e2.2

/-- Number of `K_{r,r}` copies of `G` whose edge set contains the matching `M`. -/
def bipCopiesContaining {a b : ℕ} (G : BipGraph a b) (r : ℕ)
    (M : Finset (Fin a × Fin b)) : ℕ :=
  ((Finset.univ.filter (fun s : Finset (Fin a) × Finset (Fin b) =>
    s.1.card = r ∧ s.2.card = r ∧
      ∀ u ∈ s.1, ∀ v ∈ s.2, G.adj u v = true)).filter
    fun s => M ⊆ s.1.product s.2).card

/-- `Q(f_n) ≥ n^{e-o(1)}` on balanced bipartite inputs. -/
def AsymptoticBipLowerBound (f : (n : ℕ) → (Fin n × Fin n → Bool) → Bool) (e : ℝ) : Prop :=
  ∀ ε > 0, ∃ n0 : ℕ, ∀ n ≥ n0,
    QueryLowerBound (f n) (Nat.floor ((n : ℝ) ^ (e - ε)))

/-- Search version of `AsymptoticBipLowerBound` (edge-set certificates). -/
def AsymptoticBipSearchLowerBound
    (F : (n : ℕ) → Finset (Finset (Fin n × Fin n))) (e : ℝ) : Prop :=
  ∀ ε > 0, ∃ n0 : ℕ, ∀ n ≥ n0,
    SearchLowerBound (F n) (Nat.floor ((n : ℝ) ^ (e - ε)))

/-- The exponent of Theorem 5.4 / Eq. (68):
`(2hr/((h+1)(r+h))) (1 − (h−1)/r + (h−1)/(2r²))`. -/
def bipartiteExponent (r h : ℕ) : ℝ :=
  (2 * (h : ℝ) * (r : ℝ) / (((h : ℝ) + 1) * ((r : ℝ) + (h : ℝ)))) *
    (1 - ((h : ℝ) - 1) / (r : ℝ) + ((h : ℝ) - 1) / (2 * (r : ℝ) ^ 2))

/-! ## Theorem 1.4 -/


/-! ## Theorem 5.4 -/


/-! ## Lemma 5.5 -/


/-! ## Lemma 5.6 -/


/-! ## Corollary 5.7 -/


end Qatlib.Papers.SubgraphDet26.MainResults
