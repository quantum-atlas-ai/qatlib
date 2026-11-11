/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SparseNetwork13 — electrical-network model

Fixed source: Guoming Wang, *Efficient Quantum Algorithms for Analyzing Large Sparse
Electrical Networks*, arXiv:1311.1851 **v10 (24 Jul 2017)**.

This file is the shared model layer of the paper block.  It records the
notation of §2.1--§2.3 (p.3--7):

* `ElecNetwork` — a connected weighted undirected electrical network given by
  the two endpoint maps and a strictly positive edge-conductance field (§2.2);
* `incident` — the signed vertex–edge incidence matrix `B_G` of Eq. (3);
* `weightMatrix` — the edge-conductance matrix `W_G` of Eq. (4);
* `laplacian` — the combinatorial Laplacian `L_G = B_G W_G B_Gᵀ` of Eq. (6);
* `normalizedLaplacian` — `L̄_G = D_G^{-1/2} L_G D_G^{-1/2}` of Eq. (7), encoded
  through the weighted degree diagonal `D_G` of Eq. (1);
* `energy` — the dissipated power `E(f) = ∑_e f(e)² / w_e` of Eq. (27);
* `flowFromPotential` — the flow `i = W_G B_Gᵀ v` induced by a potential `v`
  (Ohm's law, Eq. (20));  the paper's electrical flow `i = W_G B_Gᵀ L_G⁺ i_ext`
  is the special case `v = L_G⁺ i_ext`.

Everything here is definitional: this module carries no `sorry`.
-/

set_option autoImplicit false
noncomputable section

open Matrix BigOperators

namespace Qatlib.Papers.SparseNetwork13.MainResults.Model

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- A connected weighted electrical network: each edge `e` joins a tail `tail e`
to a head `head e`, carries conductance `w e > 0`, and is not a self-loop.  The
orientation is bookkeeping only (§2.2, p.5): the network itself is undirected. -/
structure ElecNetwork (V E : Type) where
  /-- The tail `e⁻` of an oriented edge. -/
  tail : E → V
  /-- The head `e⁺` of an oriented edge. -/
  head : E → V
  /-- The edge conductance `w_e > 0` (§2.2). -/
  w : E → ℝ
  /-- Conductances are strictly positive. -/
  w_pos : ∀ e, 0 < w e
  /-- No self-loops. -/
  nonloop : ∀ e, head e ≠ tail e

/-- The signed vertex–edge incidence matrix `B_G` of Eq. (3): entry `+1` at the
tail, `-1` at the head, and `0` elsewhere. -/
def incident (G : ElecNetwork V E) : Matrix V E ℝ :=
  fun v e => if v = G.tail e then (1 : ℝ) else if v = G.head e then (-1 : ℝ) else 0

/-- The edge-conductance matrix `W_G = ∑_e w_e |e⟩⟨e|` of Eq. (4), i.e. the
diagonal matrix of the conductances. -/
def weightMatrix (G : ElecNetwork V E) : Matrix E E ℝ := Matrix.diagonal G.w

/-- The weighted degree `deg(v) = ∑_{e ∈ E(v)} w_e` of §2.2 (Eq. just above (1)). -/
def weightedDegree (G : ElecNetwork V E) (v : V) : ℝ :=
  ∑ e, if v = G.tail e ∨ v = G.head e then G.w e else 0

/-- The weighted degree matrix `D_G = ∑_v deg(v)|v⟩⟨v|` of Eq. (1). -/
def degreeMatrix (G : ElecNetwork V E) : Matrix V V ℝ :=
  Matrix.diagonal (weightedDegree G)

/-- The combinatorial Laplacian `L_G = B_G W_G B_Gᵀ = D_G - A_G` of Eq. (6). -/
def laplacian (G : ElecNetwork V E) : Matrix V V ℝ :=
  incident G * weightMatrix G * (incident G)ᵀ

/-- The dissipated power / energy `E(f) = ∑_e f(e)²/w_e` of Eq. (27). -/
def energy (G : ElecNetwork V E) (f : E → ℝ) : ℝ :=
  ∑ e, f e ^ 2 / G.w e

/-- The flow `i = W_G B_Gᵀ v` induced by a vertex potential `v` (Ohm's law,
Eq. (20)).  Applied to `v = L_G⁺ i_ext` this is the electrical flow
`i = W_G B_Gᵀ L_G⁺ i_ext` of Lemma 2. -/
def flowFromPotential (G : ElecNetwork V E) (v : V → ℝ) : E → ℝ :=
  weightMatrix G *ᵥ ((incident G)ᵀ *ᵥ v)

/-- The weighted degree of a vertex in the modified graph `G′` of §4.1
(Eq. (88)): the same as `weightedDegree` plus the special hyperedge of weight
`lam`.  Used by Lemma 7. -/
def weightedDegreeMod (G : ElecNetwork V E) (lam : ℝ) (v : V) : ℝ :=
  weightedDegree G v + lam

/-- The normalized Laplacian `L̄_G = D_G^{-1/2} L_G D_G^{-1/2}` of Eq. (7):
the matrix whose `(u,v)` entry is `L_G u v / sqrt(deg u · deg v)` for positive
degrees and `0` when a degree vanishes. -/
def normalizedLaplacian (G : ElecNetwork V E) : Matrix V V ℝ :=
  fun u v =>
    if 0 < weightedDegree G u ∧ 0 < weightedDegree G v then
      laplacian G u v / Real.sqrt (weightedDegree G u * weightedDegree G v)
    else 0

/-- **The incidence matrix acts as a difference of potentials**: for any
potential field `v`, the `e`-th component of `B_Gᵀ v` is `v(e⁻) − v(e⁺)`. -/
theorem incident_transpose_mulVec_apply (G : ElecNetwork V E) (v : V → ℝ) (e : E) :
    ((incident G)ᵀ *ᵥ v) e = v (G.tail e) - v (G.head e) := by
  have hstep : ∀ x, (incident G)ᵀ e x * v x =
      (if x = G.tail e then v x else 0) + (if x = G.head e then - v x else 0) := by
    intro x
    rw [Matrix.transpose_apply]
    by_cases h1 : x = G.tail e
    · subst h1
      have hne : G.tail e ≠ G.head e := fun h => G.nonloop e h.symm
      simp [incident, hne]
    · by_cases h2 : x = G.head e
      · subst h2; simp [incident, h1]
      · simp [incident, h1, h2]
  rw [show ((incident G)ᵀ *ᵥ v) e = ∑ x, (incident G)ᵀ e x * v x by
        simp [Matrix.mulVec, dotProduct]]
  rw [Finset.sum_congr rfl (fun x _ => hstep x), Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp
  ring

/-- **Ohm's law, componentwise** (§2.3, Eq. (20)): the flow induced by `v` on
edge `e` equals `w_e · (v(e⁻) − v(e⁺))`. -/
theorem flowFromPotential_apply (G : ElecNetwork V E) (v : V → ℝ) (e : E) :
    flowFromPotential G v e = G.w e * (v (G.tail e) - v (G.head e)) := by
  simp only [flowFromPotential, weightMatrix]
  rw [Matrix.mulVec_diagonal, incident_transpose_mulVec_apply]

/-- `B_G` applied to a flow `f` is `x ↦ ∑_e B_G x e · f e` (componentwise form of
the flow-conservation operator, Eq. (26)). -/
theorem incident_mulVec_apply (G : ElecNetwork V E) (f : E → ℝ) (x : V) :
    (incident G *ᵥ f) x = ∑ e, incident G x e * f e := by
  simp [Matrix.mulVec, dotProduct]

/-- **Ohm's law in inverse form**: dividing the induced flow by the conductance
recovers the potential drop `B_Gᵀ v`.  This is the identity behind the
orthogonality computation of Lemma 2's proof (p.7). -/
theorem flowFromPotential_div_weight (G : ElecNetwork V E) (v : V → ℝ) (e : E) :
    flowFromPotential G v e / G.w e = ((incident G)ᵀ *ᵥ v) e := by
  rw [flowFromPotential_apply, incident_transpose_mulVec_apply]
  have hw : G.w e ≠ 0 := ne_of_gt (G.w_pos e)
  field_simp

/-- **The flow induced by `v` pushes forward to `L_G v`**: applying `B_G` to
`W_G B_Gᵀ v` recovers `L_G v`.  This is Eq. (22) at the level of the Laplacian. -/
theorem incident_mulVec_flowFromPotential (G : ElecNetwork V E) (v : V → ℝ) :
    incident G *ᵥ flowFromPotential G v = laplacian G *ᵥ v := by
  simp only [flowFromPotential, laplacian]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- If `v` solves the Laplacian system `L_G v = i_ext` (Eq. (22)--(23)), then the
induced flow `i = W_G B_Gᵀ v` is a flow consistent with `i_ext`: `B_G i = i_ext`
(Eq. (21), Kirchhoff's current law). -/
theorem incident_mulVec_flow_of_laplacian (G : ElecNetwork V E) (v : V → ℝ)
    {iext : V → ℝ} (hL : laplacian G *ᵥ v = iext) :
    incident G *ᵥ flowFromPotential G v = iext := by
  rw [incident_mulVec_flowFromPotential, hL]

end Qatlib.Papers.SparseNetwork13.MainResults.Model
