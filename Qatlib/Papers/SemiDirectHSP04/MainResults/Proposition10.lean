/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.SemidirectGroup
import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.AlgorithmicInterface

/-!
# Transport of hidden-subgroup solvers along group isomorphisms

`proposition10_reduction` transfers a hidden-subgroup solver across a group isomorphism using
compatible encodings. Its hypotheses provide subgroup transport, oracle periodicity, and a token
map with polynomial cardinality growth, yielding a polynomial token-cardinality query bound for
the source encoding. See [InuiLeGall2007] for the mathematical setting.

## Main statements

* `proposition10_reduction`: transports the solver and its query bound through the supplied
  isomorphism and token map.

## References

* [Inui and Le Gall, 2007][InuiLeGall2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP04.MainResults.Proposition10

open Qatlib.Papers.SemiDirectHSP04.MainResults.Model

/-- Under the subgroup, oracle-transport, and polynomial encoding-size hypotheses, an isomorphic
target group's polynomial-query solver yields a polynomial-query solver for the source
encoding. See [Inui and Le Gall, 2007, Proposition 10][InuiLeGall2007]. -/
theorem proposition10_reduction
    {G G' : Type*} [Group G] [Group G'] [DecidableEq G]
    (e : BlackBoxEncoding G) (e' : BlackBoxEncoding G')
    (pi : G ≃* G')
    (hKnown : HasPolynomialQueryHSPSolver G')

    (hmap : ∀ H : Subgroup G, ∃ H' : Subgroup G', (H' : Set G') = pi '' (H : Set G))

    (hperiodic : ∀ (H : Subgroup G) (f : G → Bool),
        (∀ a b : G, f a = f b ↔ ∃ h : H, a * h = b) →
        ∃ H' : Subgroup G', (H' : Set G') = pi '' (H : Set G) ∧
          ∀ a b : G', (f ∘ pi.symm) a = (f ∘ pi.symm) b ↔ ∃ h : H', a * h = b)

    (hiii : ∃ (c : ℕ) (inv : e'.Token → e.Token),
        (∀ t : e'.Token, pi (e.enc (inv t)) = e'.enc t) ∧ e'.size ≤ e.size ^ c) :
    HasPolyQuerySolverFor e := by
  classical

  have _ := hperiodic
  letI : DecidableEq e.Token := e.decEq

  obtain ⟨s', c', hb⟩ := hKnown e'
  simp only [HSPSolver.HasQueryBound] at hb
  obtain ⟨T, hTcard, hTagree⟩ := hb

  obtain ⟨c, inv, hcompat, hsize⟩ := hiii

  let S : Finset e.Token := T.image inv
  have hScard : S.card ≤ e.size ^ (c * c') := by
    calc S.card = (T.image inv).card := rfl
      _ ≤ T.card := Finset.card_image_le
      _ ≤ e'.size ^ c' := hTcard
      _ ≤ (e.size ^ c) ^ c' := Nat.pow_le_pow_left hsize c'
      _ = e.size ^ (c * c') := by rw [pow_mul]

  let solver : HSPSolver e :=
    { output := fun f => (s'.output (fun t' => f (inv t'))).image pi.symm
      correct := by
        intro H f hf

        obtain ⟨H', hH'set⟩ := hmap H

        have hg : IsHSOracle e' H' (fun t' => f (inv t')) := by
          intro a b
          constructor
          · intro heq
            obtain ⟨h, hh⟩ := (hf (inv a) (inv b)).mp heq
            refine ⟨⟨pi h, ?_⟩, ?_⟩
            · change pi ↑h ∈ (H' : Set G')
              rw [hH'set]
              exact ⟨h, h.2, rfl⟩
            · have hmul := congrArg (fun z => pi z) hh
              change pi (e.enc (inv a) * ↑h) = pi (e.enc (inv b)) at hmul
              rw [map_mul, hcompat a, hcompat b] at hmul
              exact hmul
          · rintro ⟨h', hh'⟩
            have hh'set : (h' : G') ∈ (pi '' (H : Set G)) := by
              rw [← hH'set]; exact h'.2
            obtain ⟨h, hhH, hheq⟩ := hh'set
            have hmain : e'.enc a * pi h = e'.enc b := by
              rw [hheq]; exact hh'
            rw [← hcompat a, ← hcompat b, ← map_mul] at hmain
            have hinj : e.enc (inv a) * h = e.enc (inv b) := pi.injective hmain
            exact (hf (inv a) (inv b)).mpr ⟨⟨h, hhH⟩, hinj⟩

        have hgen := s'.correct H' (fun t' => f (inv t')) hg

        have hcoe : (↑((s'.output (fun t' => f (inv t'))).image pi.symm) : Set G)
            = pi.symm '' (↑(s'.output (fun t' => f (inv t'))) : Set G') := by
          rw [Finset.coe_image]
        rw [hcoe]
        change Subgroup.closure
          (⇑pi.symm.toMonoidHom '' (↑(s'.output (fun t' => f (inv t'))) : Set G')) = H
        rw [← MonoidHom.map_closure pi.symm.toMonoidHom
          (↑(s'.output (fun t' => f (inv t'))) : Set G')]
        rw [hgen]
        have hH'map : H' = Subgroup.map pi.toMonoidHom H := by
          apply Subgroup.ext
          intro x
          rw [Subgroup.mem_map_equiv]
          constructor
          · intro hx
            change x ∈ (H' : Set G') at hx
            rw [hH'set] at hx
            obtain ⟨y, hy, hyx⟩ := hx
            rw [← hyx]
            simpa using hy
          · intro hx
            change x ∈ (H' : Set G')
            rw [hH'set]
            exact ⟨pi.symm x, hx, pi.apply_symm_apply x⟩
        rw [hH'map, Subgroup.map_map]
        have hcomp : pi.symm.toMonoidHom.comp pi.toMonoidHom = MonoidHom.id G := by
          ext x; simp
        rw [hcomp, Subgroup.map_id] }
  refine ⟨solver, c * c', ?_⟩
  simp only [HSPSolver.HasQueryBound]
  refine ⟨S, hScard, ?_⟩
  intro f f' hagree
  have hs'eq : s'.output (fun t' => f (inv t'))
      = s'.output (fun t' => f' (inv t')) := by
    apply hTagree
    intro t ht
    have hmem : inv t ∈ S := by
      change inv t ∈ T.image inv
      exact Finset.mem_image_of_mem inv ht
    exact hagree (inv t) hmem
  show (s'.output (fun t' => f (inv t'))).image pi.symm
      = (s'.output (fun t' => f' (inv t'))).image pi.symm
  rw [hs'eq]

end Qatlib.Papers.SemiDirectHSP04.MainResults.Proposition10
