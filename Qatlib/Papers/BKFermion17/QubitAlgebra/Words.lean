/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BKFermion17.GraphWords
public import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs

@[expose] public section

/-!
# Pauli words for the general qubit edge algebra

This module develops the word-level bookkeeping behind the general graph edge algebra of
[SetiaWhitfield2018]. For an indexed simple graph, the vertex word puts `Z` on every incident
edge, while the edge word puts `X` on its own edge and `Z` on the preceding incident edges at its
two endpoints. The resulting symplectic pairing has a direct endpoint reading: two distinct edges
pair nontrivially exactly when they share one endpoint, and a vertex pairs nontrivially with an
edge exactly when it is an endpoint of that edge.

The main results are the endpoint tests for the `Z` letter, the two symplectic-pairing formulas,
and the resulting orthogonality patterns for the endpoint-coincidence count. They are the input
for the matrix-level (anti)commutation theorems in
`Qatlib.Papers.BKFermion17.QubitAlgebra.Relations`.

## Main statements

* `edgeWord_eq_Z_iff`: the edge word has `Z` at `f` exactly in one of the four oriented
  "before" configurations at the endpoints.
* `symplecticForm_edge_edge_eq`: the pairing of two edge words is the parity of the two
  one-sided `Z` incidences.
* `symplecticForm_vertex_edge_eq`: the pairing of a vertex word with an edge word is the
  incidence indicator.
* `edgeWord_z_sum_eq_one_of_share`: edges sharing one endpoint contribute exactly one
  `Z` incidence to the pairing.
* `edgeWord_z_sum_eq_zero_of_none`: edges with no common endpoint contribute no `Z` incidence.

## References

* [Setia and Whitfield, 2018][SetiaWhitfield2018]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.BKFermion17.QubitAlgebra

open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Papers.BKFermion17.GraphWords

variable {M E : ℕ}

/-- The number of endpoint coincidences between two indexed edges. -/
def endpointCoincidence (G : IndexedGraph M E) (e f : Fin E) : ℕ :=
  (if G.left e = G.left f then 1 else 0) + (if G.left e = G.right f then 1 else 0) +
    (if G.right e = G.left f then 1 else 0) + (if G.right e = G.right f then 1 else 0)

/-- The number of endpoints of the edge `e` equal to the vertex `v`. -/
def vertexEndpointCoincidence (G : IndexedGraph M E) (v : Fin M) (e : Fin E) : ℕ :=
  (if v = G.left e then 1 else 0) + (if v = G.right e then 1 else 0)

/-- The graph edge word puts `X` at edge `f` exactly when `f` is the edge itself. -/
theorem edgeWord_eq_X_iff (G : IndexedGraph M E) (e f : Fin E) :
    edgeWord G e f = Pauli1.X ↔ f = e := by
  unfold edgeWord
  by_cases h : f = e
  · simp [h]
  · simp only [h, ↓reduceIte]
    split_ifs <;> simp

/-- The graph edge word has `X` on its own edge. -/
theorem edgeWord_self (G : IndexedGraph M E) (e : Fin E) :
    edgeWord G e e = Pauli1.X := by
  simp [edgeWord]

/-- The graph edge word puts `Z` at edge `f` exactly in one of the four oriented endpoint
configurations in which `f` precedes the other endpoint of `e`. -/
theorem edgeWord_eq_Z_iff (G : IndexedGraph M E) (e f : Fin E) :
    edgeWord G e f = Pauli1.Z ↔
      (G.left e = G.left f ∧ G.right f < G.right e) ∨
      (G.left e = G.right f ∧ G.left f < G.right e) ∨
      (G.right e = G.left f ∧ G.right f < G.left e) ∨
      (G.right e = G.right f ∧ G.left f < G.left e) := by
  unfold edgeWord before incident otherEndpoint
  by_cases hfe : f = e
  · subst f
    simp only [↓reduceIte]
    constructor
    · intro h
      exact (Pauli1.noConfusion h)
    · rintro (⟨h, hlt⟩ | ⟨h, hlt⟩ | ⟨h, hlt⟩ | ⟨h, hlt⟩) <;> omega
  · simp only [hfe, ↓reduceIte]
    have he_ne : G.left e ≠ G.right e := ne_of_lt (G.ordered e)
    have hf_ne : G.left f ≠ G.right f := ne_of_lt (G.ordered f)
    by_cases hll : G.left e = G.left f <;>
      by_cases hlr : G.left e = G.right f <;>
      by_cases hrl : G.right e = G.left f <;>
      by_cases hrr : G.right e = G.right f <;>
      simp_all <;> omega

/-- The graph vertex word puts `Z` at edge `e` exactly when the vertex is incident to `e`. -/
theorem vertexWord_eq_Z_iff (G : IndexedGraph M E) (v : Fin M) (e : Fin E) :
    vertexWord G v e = Pauli1.Z ↔ incident G v e := by
  unfold vertexWord incident
  by_cases h : G.left e = v ∨ G.right e = v <;> simp [h]

/-- A single-site Pauli label pairs trivially with itself. -/
theorem siteForm_self (a : Pauli1) : siteForm a a = 0 := by
  cases a <;> rfl

/-- The single-site pairing of `X` with an identity or `Z` label is one exactly at `Z`. -/
theorem siteForm_X_of_I_or_Z (a : Pauli1) (ha : a = Pauli1.I ∨ a = Pauli1.Z) :
    siteForm Pauli1.X a = if a = Pauli1.Z then 1 else 0 := by
  rcases ha with rfl | rfl <;> rfl

/-- The single-site pairing of an identity or `Z` label with `X` is one exactly at `Z`. -/
theorem siteForm_of_I_or_Z_X (a : Pauli1) (ha : a = Pauli1.I ∨ a = Pauli1.Z) :
    siteForm a Pauli1.X = if a = Pauli1.Z then 1 else 0 := by
  rcases ha with rfl | rfl <;> rfl

/-- A graph edge word different from `X` is either the identity or `Z`. -/
theorem edgeWord_eq_I_or_Z (G : IndexedGraph M E) (e f : Fin E)
    (h : edgeWord G e f ≠ Pauli1.X) : edgeWord G e f = Pauli1.I ∨ edgeWord G e f = Pauli1.Z := by
  unfold edgeWord at h ⊢
  split_ifs at h ⊢ <;> simp_all

/-- A graph vertex word is either the identity or `Z`. -/
theorem vertexWord_eq_I_or_Z (G : IndexedGraph M E) (v : Fin M) (e : Fin E) :
    vertexWord G v e = Pauli1.I ∨ vertexWord G v e = Pauli1.Z := by
  unfold vertexWord
  split_ifs <;> simp

/-- At a site different from both edges, two edge words pair trivially. -/
theorem siteForm_edgeWord_eq_zero (G : IndexedGraph M E) {e f i : Fin E}
    (hie : i ≠ e) (hif : i ≠ f) : siteForm (edgeWord G e i) (edgeWord G f i) = 0 := by
  have he : edgeWord G e i ≠ Pauli1.X := by
    intro h
    exact hie ((edgeWord_eq_X_iff G e i).1 h)
  have hf : edgeWord G f i ≠ Pauli1.X := by
    intro h
    exact hif ((edgeWord_eq_X_iff G f i).1 h)
  rcases edgeWord_eq_I_or_Z G e i he with he' | he' <;>
    rcases edgeWord_eq_I_or_Z G f i hf with hf' | hf' <;>
    simp [he', hf', siteForm, siteX, siteZ]

/-- The symplectic pairing of two edge words is the parity of the two one-sided `Z`
incidences. -/
theorem symplecticForm_edge_edge_eq (G : IndexedGraph M E) (e f : Fin E) :
    symplecticForm (symplecticX (edgeWord G e), symplecticZ (edgeWord G e))
        (symplecticX (edgeWord G f), symplecticZ (edgeWord G f))
      = (if edgeWord G e f = Pauli1.Z then 1 else 0) +
        (if edgeWord G f e = Pauli1.Z then 1 else 0) := by
  rw [symplecticForm_eq_sum_site]
  by_cases hef : e = f
  · subst f
    have hzero : ∀ i : Fin E, siteForm (edgeWord G e i) (edgeWord G e i) = 0 :=
      fun i => siteForm_self _
    rw [Finset.sum_eq_zero (fun i _ => hzero i)]
    simp [edgeWord_self]
  · have hsum :
        (∑ i, siteForm (edgeWord G e i) (edgeWord G f i))
          = siteForm (edgeWord G e e) (edgeWord G f e) +
            siteForm (edgeWord G e f) (edgeWord G f f) := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun i => siteForm (edgeWord G e i) (edgeWord G f i)) (Finset.mem_univ e)]
      congr 1
      refine Finset.sum_eq_single f ?_ ?_
      · intro i hi hif
        exact siteForm_edgeWord_eq_zero G (Finset.mem_erase.1 hi).1 hif
      · intro hf
        exact False.elim (hf (Finset.mem_erase.2 ⟨fun h => hef h.symm, Finset.mem_univ f⟩))
    rw [hsum]
    have hfe : edgeWord G f e ≠ Pauli1.X := by
      intro h
      exact hef ((edgeWord_eq_X_iff G f e).1 h)
    have hef' : edgeWord G e f ≠ Pauli1.X := by
      intro h
      exact hef ((edgeWord_eq_X_iff G e f).1 h).symm
    rw [edgeWord_self, edgeWord_self]
    rw [siteForm_X_of_I_or_Z _ (edgeWord_eq_I_or_Z G f e hfe),
      siteForm_of_I_or_Z_X _ (edgeWord_eq_I_or_Z G e f hef')]
    ring

/-- At a site different from the edge, a vertex word and an edge word pair trivially. -/
theorem siteForm_vertexWord_edgeWord_eq_zero (G : IndexedGraph M E) (v : Fin M)
    {e i : Fin E} (hie : i ≠ e) :
    siteForm (vertexWord G v i) (edgeWord G e i) = 0 := by
  have he : edgeWord G e i ≠ Pauli1.X := by
    intro h
    exact hie ((edgeWord_eq_X_iff G e i).1 h)
  rcases vertexWord_eq_I_or_Z G v i with hv | hv <;>
    rcases edgeWord_eq_I_or_Z G e i he with he' | he' <;>
    simp [hv, he', siteForm, siteX, siteZ]

/-- The symplectic pairing of a vertex word with an edge word is the incidence
indicator. -/
theorem symplecticForm_vertex_edge_eq (G : IndexedGraph M E) (v : Fin M) (e : Fin E) :
    symplecticForm (symplecticX (vertexWord G v), symplecticZ (vertexWord G v))
        (symplecticX (edgeWord G e), symplecticZ (edgeWord G e))
      = if incident G v e then 1 else 0 := by
  rw [symplecticForm_eq_sum_site]
  rw [← Finset.add_sum_erase Finset.univ
    (fun i => siteForm (vertexWord G v i) (edgeWord G e i)) (Finset.mem_univ e)]
  have hrest : (∑ i ∈ Finset.univ.erase e,
      siteForm (vertexWord G v i) (edgeWord G e i)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    exact siteForm_vertexWord_edgeWord_eq_zero G v (Finset.mem_erase.1 hi).1
  rw [hrest, add_zero]
  rw [edgeWord_self]
  rw [siteForm_of_I_or_Z_X _ (vertexWord_eq_I_or_Z G v e)]
  by_cases h : incident G v e
  · simp [(vertexWord_eq_Z_iff G v e).2 h, h]
  · have hz : vertexWord G v e ≠ Pauli1.Z := fun hz => h ((vertexWord_eq_Z_iff G v e).1 hz)
    simp [hz, h]

/-- Two vertex words pair trivially. -/
theorem symplecticForm_vertex_vertex_eq (G : IndexedGraph M E) (v w : Fin M) :
    symplecticForm (symplecticX (vertexWord G v), symplecticZ (vertexWord G v))
        (symplecticX (vertexWord G w), symplecticZ (vertexWord G w)) = 0 := by
  rw [symplecticForm_eq_sum_site]
  refine Finset.sum_eq_zero ?_
  intro i _
  rcases vertexWord_eq_I_or_Z G v i with hv | hv <;>
    rcases vertexWord_eq_I_or_Z G w i with hw | hw <;>
    simp [hv, hw, siteForm, siteX, siteZ]

/-- The two order indicators of distinct vertices add to one. -/
theorem indicator_lt_add_of_ne {a b : Fin M} (h : a ≠ b) :
    (if a < b then (1 : ZMod 2) else 0) + (if b < a then 1 else 0) = 1 := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · simp [hlt, not_lt_of_gt hlt]
  · simp [hlt, not_lt_of_gt hlt]

/-- Two distinct indexed edges share exactly one endpoint, with the non-shared endpoints
distinct. -/
def ShareOneEndpoint (G : IndexedGraph M E) (e f : Fin E) : Prop :=
  (G.left e = G.left f ∧ G.right e ≠ G.right f) ∨
    (G.left e = G.right f ∧ G.left f ≠ G.right e) ∨
    (G.right e = G.left f ∧ G.left e ≠ G.right f) ∨
    (G.right e = G.right f ∧ G.left e ≠ G.left f)

/-- Two indexed edges have no common endpoint. -/
def NoEndpointCoincidence (G : IndexedGraph M E) (e f : Fin E) : Prop :=
  G.left e ≠ G.left f ∧ G.left e ≠ G.right f ∧
    G.right e ≠ G.left f ∧ G.right e ≠ G.right f

instance shareOneEndpointDecidable (G : IndexedGraph M E) (e f : Fin E) :
    Decidable (ShareOneEndpoint G e f) := by
  unfold ShareOneEndpoint
  infer_instance

instance noEndpointCoincidenceDecidable (G : IndexedGraph M E) (e f : Fin E) :
    Decidable (NoEndpointCoincidence G e f) := by
  unfold NoEndpointCoincidence
  infer_instance

/-- When two edges share their left endpoints, exactly one of the two oriented edge words
contributes `Z` at the site of the other. -/
theorem edgeWord_z_sum_eq_one_shared_left_left (G : IndexedGraph M E) {e f : Fin E}
    (hll : G.left e = G.left f) (hrr : G.right e ≠ G.right f) :
    (if edgeWord G e f = Pauli1.Z then (1 : ZMod 2) else 0) +
      (if edgeWord G f e = Pauli1.Z then 1 else 0) = 1 := by
  simp only [edgeWord_eq_Z_iff]
  have hlr : G.left e ≠ G.right f := by
    intro hh
    have hf := G.ordered f
    omega
  have hrl : G.right e ≠ G.left f := by
    intro hh
    have he := G.ordered e
    omega
  have hrr' : G.right f ≠ G.right e := fun hh => hrr hh.symm
  have hf1 : G.left f ≠ G.right f := ne_of_lt (G.ordered f)
  have hf2 : G.right f ≠ G.left f := fun hh => hf1 hh.symm
  have he1 : G.left e ≠ G.right e := ne_of_lt (G.ordered e)
  have he2 : G.right e ≠ G.left e := fun hh => he1 hh.symm
  have hlr' : G.left f ≠ G.right e := fun hh => hrl hh.symm
  simp [hll, hrl, hrr, hrr', hf1, hf2, hlr']
  exact indicator_lt_add_of_ne hrr'

/-- When the left endpoint of `e` is the right endpoint of `f`, the `e` word contributes the
unique `Z` at the other edge. -/
theorem edgeWord_z_sum_eq_one_shared_left_right (G : IndexedGraph M E) {e f : Fin E}
    (hlr : G.left e = G.right f) (hdist : G.left f ≠ G.right e) :
    (if edgeWord G e f = Pauli1.Z then (1 : ZMod 2) else 0) +
      (if edgeWord G f e = Pauli1.Z then 1 else 0) = 1 := by
  simp only [edgeWord_eq_Z_iff]
  have h1 : G.left f ≠ G.left e := by
    intro hh
    have hf := G.ordered f
    have hh' : G.left f = G.right f := by rw [← hlr]; exact hh
    omega
  have h3 : G.right f ≠ G.right e := by
    intro hh
    have he := G.ordered e
    have hh' : G.left e = G.right e := hlr.trans hh
    omega
  have hnot : ¬ (G.right e < G.left f) := by
    have he := G.ordered e
    have hf := G.ordered f
    rw [hlr] at he
    omega
  have hlt_e : G.right f < G.right e := by
    have he := G.ordered e
    rw [hlr] at he
    exact he
  have hlt_f : G.left f < G.right e := by
    have hf := G.ordered f
    have he := G.ordered e
    rw [hlr] at he
    omega
  have hf1 : G.left f ≠ G.right f := ne_of_lt (G.ordered f)
  have hf2 : G.right f ≠ G.left f := fun hh => hf1 hh.symm
  have h3' : G.right e ≠ G.right f := fun hh => h3 hh.symm
  simp [hlr, h3, h3', hdist, hnot, hlt_e, hlt_f, hf1, hf2]

/-- When the right endpoint of `e` is the left endpoint of `f`, the `f` word contributes the
unique `Z` at the other edge. -/
theorem edgeWord_z_sum_eq_one_shared_right_left (G : IndexedGraph M E) {e f : Fin E}
    (hrl : G.right e = G.left f) (hdist : G.left e ≠ G.right f) :
    (if edgeWord G e f = Pauli1.Z then (1 : ZMod 2) else 0) +
      (if edgeWord G f e = Pauli1.Z then 1 else 0) = 1 := by
  simp only [edgeWord_eq_Z_iff]
  have h1 : G.left f ≠ G.left e := by
    intro hh
    have he := G.ordered e
    have hh' : G.left e = G.right e := by rw [← hh, ← hrl]
    omega
  have h4 : G.right e ≠ G.right f := by
    intro hh
    have hf := G.ordered f
    have hh' : G.left f = G.right f := by rw [← hrl]; exact hh
    omega
  have hlt : G.left e < G.right f := by
    have he := G.ordered e
    have hf := G.ordered f
    rw [hrl] at he
    omega
  have hnot : ¬ (G.right f < G.left e) := not_lt_of_ge (le_of_lt hlt)
  have h1' : G.left e ≠ G.left f := fun hh => h1 hh.symm
  have h4' : G.right f ≠ G.right e := fun hh => h4 hh.symm
  have hf1 : G.left f ≠ G.right f := ne_of_lt (G.ordered f)
  have hf2 : G.right f ≠ G.left f := fun hh => hf1 hh.symm
  simp [hrl, h1, h1', hdist, hlt, hnot, hf1, hf2]

/-- When two edges share their right endpoints, exactly one of the two oriented edge words
contributes `Z` at the site of the other. -/
theorem edgeWord_z_sum_eq_one_shared_right_right (G : IndexedGraph M E) {e f : Fin E}
    (hrr : G.right e = G.right f) (hll : G.left e ≠ G.left f) :
    (if edgeWord G e f = Pauli1.Z then (1 : ZMod 2) else 0) +
      (if edgeWord G f e = Pauli1.Z then 1 else 0) = 1 := by
  simp only [edgeWord_eq_Z_iff]
  have h2 : G.left e ≠ G.right f := by
    intro hh
    have he := G.ordered e
    have hh' : G.left e = G.right e := hh.trans hrr.symm
    omega
  have h4 : G.left f ≠ G.right e := by
    intro hh
    have hf := G.ordered f
    have hh' : G.left f = G.right f := hh.trans hrr
    omega
  have hll' : G.left f ≠ G.left e := fun hh => hll hh.symm
  have h2' : G.right f ≠ G.left e := fun hh => h2 hh.symm
  have hf1 : G.left f ≠ G.right f := ne_of_lt (G.ordered f)
  have hf2 : G.right f ≠ G.left f := fun hh => hf1 hh.symm
  simp [hrr, hll, hll', h2, h2', hf1, hf2]
  exact indicator_lt_add_of_ne hll'

/-- When two edges share one endpoint, exactly one of the two oriented edge words contributes
`Z` at the site of the other. -/
theorem edgeWord_z_sum_eq_one_of_share (G : IndexedGraph M E) (e f : Fin E)
    (h : ShareOneEndpoint G e f) :
    (if edgeWord G e f = Pauli1.Z then (1 : ZMod 2) else 0) +
      (if edgeWord G f e = Pauli1.Z then 1 else 0) = 1 := by
  rcases h with h | h | h | h
  · exact edgeWord_z_sum_eq_one_shared_left_left G h.1 h.2
  · exact edgeWord_z_sum_eq_one_shared_left_right G h.1 h.2
  · exact edgeWord_z_sum_eq_one_shared_right_left G h.1 h.2
  · exact edgeWord_z_sum_eq_one_shared_right_right G h.1 h.2

/-- Two edges with no common endpoint contribute no `Z` at each other's site, so both
`Z`-indicator summands vanish. -/
theorem edgeWord_z_sum_eq_zero_of_none (G : IndexedGraph M E) (e f : Fin E)
    (h : NoEndpointCoincidence G e f) :
    (if edgeWord G e f = Pauli1.Z then (1 : ZMod 2) else 0) +
      (if edgeWord G f e = Pauli1.Z then 1 else 0) = 0 := by
  simp only [edgeWord_eq_Z_iff]
  rcases h with ⟨h1, h2, h3, h4⟩
  have h1' : G.left f ≠ G.left e := fun hh => h1 hh.symm
  have h2' : G.right f ≠ G.left e := fun hh => h2 hh.symm
  have h3' : G.left f ≠ G.right e := fun hh => h3 hh.symm
  have h4' : G.right f ≠ G.right e := fun hh => h4 hh.symm
  simp [h1, h1', h2, h2', h3, h3', h4, h4']

/-- Two distinct indexed edges either share exactly one endpoint or have no common endpoint. -/
theorem shareOneEndpoint_or_noCoincidence (G : IndexedGraph M E) {e f : Fin E}
    (hne : e ≠ f) : ShareOneEndpoint G e f ∨ NoEndpointCoincidence G e f := by
  by_cases hll : G.left e = G.left f
  · left
    left
    refine ⟨hll, ?_⟩
    intro hrr
    exact hne (G.simple (by simp [hll, hrr]))
  · by_cases hlr : G.left e = G.right f
    · left
      right
      left
      refine ⟨hlr, ?_⟩
      intro hfe
      have he := G.ordered e
      have hf := G.ordered f
      omega
    · by_cases hrl : G.right e = G.left f
      · left
        right
        right
        left
        refine ⟨hrl, ?_⟩
        intro hef
        have he := G.ordered e
        have hf := G.ordered f
        omega
      · by_cases hrr : G.right e = G.right f
        · left
          right
          right
          right
          exact ⟨hrr, hll⟩
        · right
          exact ⟨hll, hlr, hrl, hrr⟩

end Qatlib.Papers.BKFermion17.QubitAlgebra
