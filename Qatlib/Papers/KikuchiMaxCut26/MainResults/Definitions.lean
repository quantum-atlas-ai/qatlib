/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order

set_option backward.isDefEq.respectTransparency false

/-!
# Kikuchi graphs: source model

Bakshi--Basu--Kothari--Li, *Sharp Bounds on the Eigenvalues of Kikuchi Graphs and
Applications to Quantum Max Cut*, fixed arXiv:2605.14994v1 (2026-05-14).
PDF SHA-256 fa5c3dd53c547fa65041c7f2b8f96fcb55cc3370746c787f54e7961abdb03afc.

This file records the paper's concrete objects (Definition 2.1, page 3): the level-`k`
Kikuchi graph `F_k(G)` on the `k`-element subsets `([n] choose k)` of the vertex set,
with `S ~ T` exactly when the symmetric difference `S ∆ T` is an edge of `G`, together
with its degree matrix `D_G^(k)`, adjacency matrix `A_G^(k)`, signed Laplacian
`L_G^(k) = D - A`, unsigned (signless) Laplacian `Q_G^(k) = D + A`, and the one-parameter
family `L_{b,G}^(k) = D + b A` of Section 3 (page 3).

The ordered eigenvalues of a Hermitian matrix are taken from Mathlib's
`Matrix.IsHermitian.eigenvalues₀ : Fin (Fintype.card ι) → ℝ`, which is antitone
(`Matrix.IsHermitian.eigenvalues₀_antitone`), so index `0` is the largest eigenvalue
and the last index is the smallest.  This is the same convention used elsewhere in the
library (`Qatlib.Concepts.SpectralSketch.SpectrumPerturb`).

Boundary: this is the paper-layer model of the source objects; it does not restate any
shared `Foundations`/`Concepts` result and does not introduce axioms.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators symmDiff
open Matrix

namespace Qatlib.Papers.KikuchiMaxCut26.MainResults

/-! ## The vertex set `([n] choose k)` -/

/-- The `k`-element subsets of a finite type `α`, i.e. the vertex set `([n] choose k)` of the
level-`k` Kikuchi graph when `α = Fin n` (Definition 2.1, arXiv:2605.14994v1, page 3). -/
abbrev KSub (α : Type*) [DecidableEq α] (k : ℕ) := {S : Finset α // S.card = k}

variable {α : Type*} [DecidableEq α]

instance (n k : ℕ) : Fintype (KSub (Fin n) k) := by
  unfold KSub; infer_instance

instance (n k : ℕ) : DecidableEq (KSub (Fin n) k) := by
  unfold KSub; infer_instance

/-- `([n] choose k)` is nonempty as soon as `k ≤ n`. -/
theorem kSub_nonempty {n k : ℕ} (hk : k ≤ n) : Nonempty (KSub (Fin n) k) := by
  refine ⟨⟨(Finset.univ : Finset (Fin k)).image (fun i => ⟨i.1, lt_of_lt_of_le i.2 hk⟩), ?_⟩⟩
  rw [Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using congrArg Fin.val h))]
  simp

/-! ## The level-`k` Kikuchi graph -/

/-- The level-`k` Kikuchi graph `F_k(G)` (Definition 2.1, arXiv:2605.14994v1, page 3):
two `k`-sets `S, T` are adjacent iff their symmetric difference is an edge of `G`, i.e.
`S ⊕ T = {i,j}` with `{i,j} ∈ E(G)`. -/
def kikuchiGraph {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : SimpleGraph (KSub (Fin n) k) where
  Adj S T := ∃ i j : Fin n, G.Adj i j ∧ S.1 \ T.1 = {i} ∧ T.1 \ S.1 = {j}
  symm := ⟨by
    intro S T h
    obtain ⟨i, j, hadj, h1, h2⟩ := h
    exact ⟨j, i, G.adj_symm hadj, h2, h1⟩⟩
  loopless := ⟨fun S h => by
    obtain ⟨i, j, hadj, h1, h2⟩ := h
    have h0 : S.1 \ S.1 = ∅ := Finset.sdiff_self S.1
    rw [h1] at h0
    have h1' : ({i} : Finset (Fin n)).card = 1 := by simp
    rw [h0] at h1'
    simp at h1'⟩

/-! ## The matrices `A_G^(k)`, `D_G^(k)`, `L_G^(k)`, `Q_G^(k)` -/

variable {n : ℕ}

/-- The adjacency matrix `A_G^(k)` of the level-`k` Kikuchi graph (Definition 2.1,
arXiv:2605.14994v1, page 3). -/
def adjMatrix (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    Matrix (KSub (Fin n) k) (KSub (Fin n) k) ℝ := by
  classical
  exact (kikuchiGraph G k).adjMatrix ℝ

/-- The degree matrix `D_G^(k)`: diagonal, with the degree of `S` in `F_k(G)`
(Definition 2.1, arXiv:2605.14994v1, page 3). -/
def degMatrix (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    Matrix (KSub (Fin n) k) (KSub (Fin n) k) ℝ := by
  classical
  exact (kikuchiGraph G k).degMatrix ℝ

/-- The signed Laplacian `L_G^(k) = D_G^(k) - A_G^(k)` of the Kikuchi graph
(Definition 2.1, arXiv:2605.14994v1, page 3). -/
def lapMatrix (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    Matrix (KSub (Fin n) k) (KSub (Fin n) k) ℝ := by
  classical
  exact (kikuchiGraph G k).lapMatrix ℝ

/-- The unsigned (signless) Laplacian `Q_G^(k) = D_G^(k) + A_G^(k)`
(Definition 2.1, arXiv:2605.14994v1, page 3). -/
def signlessMatrix (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    Matrix (KSub (Fin n) k) (KSub (Fin n) k) ℝ :=
  degMatrix G k + adjMatrix G k

/-- The two-case Laplacian family `L_{b,G}^(k) = D_G^(k) + b · A_G^(k)` of Section 3
(arXiv:2605.14994v1, page 3); `b = -1` gives the signed Laplacian and `b = 1` the
signless one. -/
def signedLaplacian (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) (b : ℝ) :
    Matrix (KSub (Fin n) k) (KSub (Fin n) k) ℝ :=
  degMatrix G k + b • adjMatrix G k

/-- Unfolding lemma: `L_G^(k) = D_G^(k) - A_G^(k)`. -/
theorem lapMatrix_eq_sub (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    lapMatrix G k = degMatrix G k - adjMatrix G k := by
  simp only [lapMatrix, degMatrix, adjMatrix, SimpleGraph.lapMatrix]

/-- The signed Laplacian `L_G^(k)` is symmetric. -/
theorem lapMatrix_isSymm (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    (lapMatrix G k).IsSymm := by
  classical
  exact (kikuchiGraph G k).isSymm_lapMatrix ℝ

/-- The signed Laplacian `L_G^(k)` is Hermitian. -/
theorem lapMatrix_isHermitian (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    (lapMatrix G k).IsHermitian :=
  lapMatrix_isSymm G k

/-- The signed Laplacian `L_G^(k)` is positive semidefinite. -/
theorem lapMatrix_posSemidef (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    (lapMatrix G k).PosSemidef := by
  classical
  exact (kikuchiGraph G k).posSemidef_lapMatrix ℝ

/-- The signed Laplacian is `2A_G^(k)` below the signless Laplacian:
`Q_G^(k) - L_G^(k) = 2 A_G^(k)` (identity used in the proof of Proposition 2.2,
arXiv:2605.14994v1, page 3). -/
theorem signless_sub_lap (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    signlessMatrix G k - lapMatrix G k = (2 : ℝ) • adjMatrix G k := by
  simp only [signlessMatrix, lapMatrix, degMatrix, adjMatrix, SimpleGraph.lapMatrix]
  module

/-- The number of edges `m = |E(G)|` of the base graph. -/
def edgeCount (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ := G.edgeFinset.card

/-- The edges of `G` as an unordered list of ordered pairs `(i, j)` with `i < j`
(the sums `Σ_{{i,j}∈E}` of the paper). -/
def edgePairs (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p : Fin n × Fin n => G.Adj p.1 p.2 ∧ p.1 < p.2)

/-! ## Ordered eigenvalues -/

/-- Largest eigenvalue of a Hermitian matrix, in the decreasing `eigenvalues₀` indexing
(equals `0` for an empty index type, where all matrices are empty). -/
def lamMax {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : A.IsHermitian) : ℝ :=
  if h : Fintype.card ι = 0 then 0
  else hA.eigenvalues₀ ⟨0, Nat.pos_of_ne_zero h⟩

/-- Smallest eigenvalue of a Hermitian matrix, in the decreasing `eigenvalues₀` indexing
(equals `0` for an empty index type). -/
def lamMin {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : A.IsHermitian) : ℝ :=
  if h : Fintype.card ι = 0 then 0
  else hA.eigenvalues₀ ⟨Fintype.card ι - 1, by have := Nat.pos_of_ne_zero h; omega⟩

/-- `λmax` is the value of `eigenvalues₀` at index `0`. -/
theorem lamMax_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (h : Fintype.card ι ≠ 0) :
    lamMax A hA = hA.eigenvalues₀ ⟨0, Nat.pos_of_ne_zero h⟩ := by
  unfold lamMax
  simp [h]

/-- `λmin` is the value of `eigenvalues₀` at the last index. -/
theorem lamMin_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (h : Fintype.card ι ≠ 0) :
    lamMin A hA = hA.eigenvalues₀ ⟨Fintype.card ι - 1,
      by have := Nat.pos_of_ne_zero h; omega⟩ := by
  unfold lamMin
  simp [h]

/-! ## The Brouwer error scale `θ_r` -/

/-- `θ_0 = 0`, `θ_r = θ_{r-1} + 2√r - 1`  (equation (17), arXiv:2605.14994v1, page 10). -/
def theta : ℕ → ℝ
  | 0 => 0
  | r + 1 => theta r + 2 * Real.sqrt (r + 1 : ℝ) - 1

/-- Closed form `θ_r = 2 Σ_{s=1}^{r} √s - r` (equation (17), arXiv:2605.14994v1, page 10). -/
theorem theta_eq_sum (r : ℕ) :
    theta r = 2 * (∑ s ∈ Finset.Icc 1 r, Real.sqrt (s : ℝ)) - r := by
  induction r with
  | zero => simp [theta]
  | succ n ih =>
    rw [theta, ih, Finset.sum_Icc_succ_top (by omega)]
    push_cast
    ring

end Qatlib.Papers.KikuchiMaxCut26.MainResults
