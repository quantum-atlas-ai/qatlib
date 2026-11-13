/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SubgraphDet26.MainResults.GraphModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lower bounds from chromatic number (Theorems 1.3, 5.2; Corollaries 5.3; Lemma 5.1)

Paper: Gilani–Zhou, *Superlinear Quantum Query Lower Bounds for Subgraph Detection*,
fixed arXiv:2609.40263v1.

* Theorem 1.3, Eq. (3): `Q(Sub_H) = Ω(Q(Clique_r))` for `r = min{c,6}`,
  some `r ≥ α₀ c/log log c`, and `r = c` under Hadwiger's conjecture;
* Lemma 5.1: `χ(core H) = χ(H)` and the core of a connected graph is connected;
* Theorem 5.2, Eq. (62): reduction through a `K_r` minor of the core;
* Corollary 5.3, Eq. (63): the restatement of Theorem 1.3.

The homomorphism core is presented through the concrete predicate `IsCore` (a
minimal retract), since the paper defines it up to isomorphism.
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

/-! ## Comparing query complexities -/

/-- `Q(f) = Ω(Q(g))`: a lower bound for `g` transfers to `f` with a constant factor,
eventually in `n`. -/
def AsymptoticQueryDominates (f g : (n : ℕ) → (EdgeIndex n → Bool) → Bool) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, ∀ n ≥ n0, ∀ T : ℕ,
    QueryLowerBound (g n) T →
      QueryLowerBound (f n) (Nat.floor (c * (T : ℝ)))

/-- Search version of `AsymptoticQueryDominates`. -/
def AsymptoticSearchDominates
    (F G : (n : ℕ) → Finset (Finset (EdgeIndex n))) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, ∀ n ≥ n0, ∀ T : ℕ,
    SearchLowerBound (G n) T →
      SearchLowerBound (F n) (Nat.floor (c * (T : ℝ)))

/-- Edge-set certificates of the copies of a fixed pattern `H` in `K_n` (used for
`Sub_H` search). -/
def subgraphEdgeFamily {m n : ℕ} (H : FinGraph (Fin m)) : Finset (Finset (EdgeIndex n)) :=
  (Finset.univ.filter (fun f : Fin m → Fin n => Function.Injective f)).image
    (fun f => Finset.univ.filter fun e : EdgeIndex n =>
      ∃ a b : Fin m, H.adj a b = true ∧ e.val.1 = f a ∧ e.val.2 = f b)

/-! ## Homomorphism cores -/

/-- Edge count of a finite graph. -/
def edgeCount {V : Type*} [Fintype V] [DecidableEq V] (G : FinGraph V) : ℕ :=
  ((Finset.univ.product Finset.univ).filter (fun p : V × V => G.adj p.1 p.2 = true)).card

/-- `C` is a retract of `H`: a subgraph together with an idempotent homomorphism
`H → C` fixing `C`. -/
def IsRetract {V : Type*} (H C : FinGraph V) : Prop :=
  (∀ a b, C.adj a b = true → H.adj a b = true) ∧
    ∃ φ : V → V, IsHom H C φ ∧ (∀ a, φ (φ a) = φ a) ∧
      (∀ a b, C.adj a b = true → φ a = a)

/-- `C` is a homomorphism core of `H`: a retract of minimum edge count (`core(H)` is
well defined up to isomorphism). -/
def IsCore {V : Type*} [Fintype V] [DecidableEq V] (H C : FinGraph V) : Prop :=
  IsRetract H C ∧ ∀ D : FinGraph V, IsRetract H D → edgeCount C ≤ edgeCount D

/-- **Open conjecture / complexity hypothesis — not proved in Qatlib.** Hadwiger's conjecture, as used in Theorem 1.3 (iii): every graph contains a
`K_{χ(G)}` minor. -/
def HadwigerConjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : FinGraph V),
    HasCliqueMinor G (chromaticNumber G)

/-! ## Theorem 1.3 -/

/-! ## Theorems 1.3, 5.2 and Corollary 5.3

Paper: Theorem 1.3 (Eq. (3)), Theorem 5.2 (Eq. (62)) and Corollary 5.3 (Eq. (63)),
fixed arXiv:2609.40263v1.  All three reduce `K_r` detection to `H` detection through
a clique minor of the core at constant query overhead; the inputs they rely on (the
Dalirrooyfard–Vassilevska Williams reduction, the Delcourt–Postle colouring theorem
and Hadwiger's conjecture) are external combinatorial results not formalised in the
library, so the scaffolds were removed (statements preserved in the branch history
at `161317a85`).  -/

/-! ## Lemma 5.1 -/

/-- Lemma 5.1: for every core `C` of `H`, `χ(C) = χ(H)`, and the core is connected
on its non-isolated vertices whenever `H` is connected.
Note on fidelity: the paper states "the core of a connected graph is connected".
Under the spanning formulation here (`IsRetract` keeps the vertex set, so `C` may
carry isolated vertices not incident to any `C`-edge), `Connected C` itself is
false in general — e.g. `H` a path on three vertices retracted onto one edge with
the third vertex isolated.  The provable, faithful reading is connectivity between
vertices incident to `C`-edges, which is what is proved below.
Proof: `χ(C) ≤ χ(H)` by restricting a colouring of `H` (every `C`-edge is an
`H`-edge), `χ(H) ≤ χ(C)` by pulling a colouring of `C` back along the retraction
`φ` (`IsHom H C φ`), and connectivity by mapping `H`-walks through `φ`
(`Relation.ReflTransGen.map`) and using that `φ` fixes every vertex incident to a
`C`-edge. -/
theorem lemma51_core_properties {m : ℕ} (H C : FinGraph (Fin m)) (hcore : IsCore H C) :
    chromaticNumber C = chromaticNumber H ∧
    (Connected H → ∀ a b : Fin m,
      (∃ c, C.adj a c = true) → (∃ c, C.adj b c = true) →
      Relation.ReflTransGen (fun x y => C.adj x y = true) a b) := by
  obtain ⟨⟨hsubedge, φ, hhom, -, hfix⟩, -⟩ := hcore
  have hrestrict : ∀ c : ℕ, Colorable H c → Colorable C c := fun c ⟨col, hcol⟩ =>
    ⟨col, fun a b hab => hcol a b (hsubedge a b hab)⟩
  have hlift : ∀ c : ℕ, Colorable C c → Colorable H c := fun c ⟨col, hcol⟩ =>
    ⟨col ∘ φ, fun a b hab => hcol (φ a) (φ b) (hhom a b hab)⟩
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · rcases Set.eq_empty_or_nonempty {c : ℕ | Colorable C c} with hCE | hCE
    · have hHC : ∀ c : ℕ, ¬ Colorable H c := by
        intro c hcH
        have hmem : c ∈ {c : ℕ | Colorable C c} := hrestrict c hcH
        rw [hCE] at hmem
        exact hmem
      have hHE : {c : ℕ | Colorable H c} = ∅ := by
        ext c
        simp [hHC c]
      simp [chromaticNumber, hCE, hHE]
    · have hHE := hCE.mono fun c hc => hlift c hc
      exact Nat.sInf_le (Set.mem_setOf_eq.mpr
        (hrestrict _ (Set.mem_setOf_eq.mp (Nat.sInf_mem hHE))))
  · rcases Set.eq_empty_or_nonempty {c : ℕ | Colorable C c} with hCE | hCE
    · have hHC : ∀ c : ℕ, ¬ Colorable H c := by
        intro c hcH
        have hmem : c ∈ {c : ℕ | Colorable C c} := hrestrict c hcH
        rw [hCE] at hmem
        exact hmem
      have hHE : {c : ℕ | Colorable H c} = ∅ := by
        ext c
        simp [hHC c]
      simp [chromaticNumber, hCE, hHE]
    · exact Nat.sInf_le (Set.mem_setOf_eq.mpr
        (hlift _ (Set.mem_setOf_eq.mp (Nat.sInf_mem hCE))))
  · intro hconn a b ⟨c, hc⟩ ⟨c', hc'⟩
    have hφa : φ a = a := hfix a c hc
    have hφb : φ b = b := hfix b c' hc'
    have hmap : Relation.ReflTransGen (fun x y => C.adj x y = true) (φ a) (φ b) :=
      Relation.ReflTransGen.lift φ (p := fun x y => C.adj x y = true)
        (fun x y hxy => hhom x y hxy) a b (hconn a b)
    rwa [hφa, hφb] at hmap

end Qatlib.Papers.SubgraphDet26.MainResults
