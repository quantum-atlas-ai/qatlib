/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitLang.LocGates
public import Qatlib.Concepts.CircuitLang.SelSplit

@[expose] public section

/-!
# Constructive completion of an injective wire selection into a split

`SelSplit` carries the completion of an injective `LocSel` as a contract; this module
discharges that contract constructively. The complementary wires
are enumerated in ascending wire order through `Finset.orderIsoOfFin` applied to the
complement of the selection image, and joint bijectivity follows from the disjointness
of the image and its complement. Any injective selection of wires, adjacent or not, in
any order, is completed to a usable split; nothing here claims a compilation algorithm.

## Main statements

* `mkSplit`: every injective selection of `k` of `m + k` wires completes to a
  `SplitSel m k`.
* `mkCompl_notSel`: a filled complementary wire is never a selected wire.
* `mkCompl_lt`: completing the canonical last-wire selection enumerates exactly the
  prefix wires below `m`.
* `exCompl_val`: a concrete non-adjacent, non-monotone selection on three wires has
  the single untouched wire as its complement.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CircuitLang.WireReg
open Qatlib.Concepts.CircuitLang.LocGates
open Qatlib.Concepts.CircuitLang.SelSplit

namespace Qatlib.Concepts.CircuitLang.SelFill

/-- The finite set of wires hit by a selection. -/
def selImage {n k : ℕ} (s : LocSel n k) : Finset (Wire n) :=
  Finset.image s.sel Finset.univ

/-- An injective selection hits exactly `k` distinct wires. -/
theorem selImage_card {n k : ℕ} (s : LocSel n k) : (selImage s).card = k := by
  rw [selImage, Finset.card_image_of_injective Finset.univ s.inj, Finset.card_univ,
    Fintype.card_fin]

/-- A selected wire lies in the selection image. -/
theorem mem_selImage {n k : ℕ} (s : LocSel n k) (j : Fin k) :
    s.sel j ∈ selImage s :=
  Finset.mem_image_of_mem _ (Finset.mem_univ j)

/-- The ascending enumeration of the complementary wires of a selection. -/
noncomputable def complIso {m k : ℕ} (s : LocSel (m + k) k) :
    Fin m ≃o ((selImage s)ᶜ : Finset (Wire (m + k))) :=
  Finset.orderIsoOfFin _
    (by rw [Finset.card_compl, selImage_card, Fintype.card_fin]; omega)

/-- The constructive completion of an injective selection into a wire split: the
complement is the ascending enumeration of the unselected wires. -/
noncomputable def mkSplit {m k : ℕ} (s : LocSel (m + k) k) : SplitSel m k where
  sel := s.sel
  compl := fun i => (complIso s i : Wire (m + k))
  bij := by
    constructor
    · intro a b hab
      match a, b with
      | Sum.inl i, Sum.inl i' =>
        have hab' : ((complIso s) i : Wire (m + k)) = ↑((complIso s) i') := hab
        exact congrArg Sum.inl ((complIso s).toEquiv.injective (Subtype.ext hab'))
      | Sum.inl i, Sum.inr j =>
        have hab' : ((complIso s) i : Wire (m + k)) = s.sel j := hab
        exact absurd (mem_selImage s j) (by
          have hp := (complIso s i).2
          rw [hab'] at hp
          exact Finset.mem_compl.mp hp)
      | Sum.inr j, Sum.inl i' =>
        have hab' : s.sel j = ((complIso s) i' : Wire (m + k)) := hab
        exact absurd (mem_selImage s j) (by
          have hp := (complIso s i').2
          rw [← hab'] at hp
          exact Finset.mem_compl.mp hp)
      | Sum.inr j, Sum.inr j' =>
        have hab' : s.sel j = s.sel j' := hab
        exact congrArg Sum.inr (s.inj hab')
    · intro w
      by_cases hw : w ∈ selImage s
      · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hw
        exact ⟨Sum.inr j, hj⟩
      · obtain ⟨i, hi⟩ := (complIso s).surjective ⟨w, by
          simpa [Finset.mem_compl] using hw⟩
        refine ⟨Sum.inl i, ?_⟩
        have hcoe : ((complIso s) i : Wire (m + k)) = w := congrArg Subtype.val hi
        exact hcoe

/-- A filled complementary wire is never a selected wire, by construction. -/
theorem mkCompl_notSel {m k : ℕ} (s : LocSel (m + k) k) (i : Fin m) (j : Fin k) :
    (mkSplit s).compl i ≠ s.sel j := by
  intro h
  have hp : (mkSplit s).compl i ∈ (selImage s)ᶜ := (complIso s i).2
  rw [h] at hp
  exact (Finset.mem_compl.mp hp) (mem_selImage s j)

/-- Completing the canonical last-wire selection enumerates exactly the prefix wires:
every filled complementary wire is below `m`. -/
theorem mkCompl_lt (m k : ℕ) (i : Fin m) :
    (((mkSplit (lastSel m k)).compl i : Wire (m + k)) : ℕ) < m := by
  by_contra hlt
  push Not at hlt
  have hmem : ((mkSplit (lastSel m k)).compl i : Wire (m + k)) ∈
      selImage (lastSel m k) := by
    refine Finset.mem_image.mpr ⟨⟨(((mkSplit (lastSel m k)).compl i:
      Wire (m + k)) : ℕ) - m, by omega⟩, Finset.mem_univ _, ?_⟩
    show (Fin.natAdd m ⟨(((mkSplit (lastSel m k)).compl i : Wire (m + k)) : ℕ) - m,
      by omega⟩ : Wire (m + k)) = (mkSplit (lastSel m k)).compl i
    apply Fin.ext
    have hval : (Fin.natAdd m ⟨(((mkSplit (lastSel m k)).compl i : Wire (m + k)) : ℕ) - m,
      by omega⟩ : Wire (m + k)).val =
        m + ((((mkSplit (lastSel m k)).compl i : Wire (m + k)) : ℕ) - m) := rfl
    omega
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
  exact mkCompl_notSel (lastSel m k) i j hj.symm

/-- A concrete non-adjacent, non-monotone selection: targets wire two then wire zero of
a three-wire register. -/
def exSel : LocSel 3 2 where
  sel j := if j = 0 then ⟨2, by omega⟩ else ⟨0, by omega⟩
  inj := by decide

/-- The concrete selection really hits wire two first and wire zero second. -/
theorem exSel_vals : exSel.sel ⟨0, by omega⟩ = ⟨2, by omega⟩ ∧
    exSel.sel ⟨1, by omega⟩ = ⟨0, by omega⟩ := by
  simp [exSel]

set_option maxHeartbeats 400000 in
/-- The filled complement of the concrete selection is the single untouched wire one. -/
theorem exCompl_val :
    ((mkSplit (m := 1) (k := 2) exSel).compl ⟨0, by omega⟩ : Wire 3).val = 1 := by
  have h0 : (mkSplit (m := 1) (k := 2) exSel).compl ⟨0, by omega⟩ ≠
      exSel.sel ⟨1, by omega⟩ :=
    mkCompl_notSel (m := 1) (k := 2) exSel ⟨0, by omega⟩ ⟨1, by omega⟩
  have h2 : (mkSplit (m := 1) (k := 2) exSel).compl ⟨0, by omega⟩ ≠
      exSel.sel ⟨0, by omega⟩ :=
    mkCompl_notSel (m := 1) (k := 2) exSel ⟨0, by omega⟩ ⟨0, by omega⟩
  rw [exSel_vals.2] at h0
  rw [exSel_vals.1] at h2
  have hc := ((mkSplit (m := 1) (k := 2) exSel).compl ⟨0, by omega⟩ :
    Wire 3).isLt
  rcases hv : ((mkSplit (m := 1) (k := 2) exSel).compl ⟨0, by omega⟩ :
      Wire 3).val with _ | _ | _ | _
  · exact absurd (show (mkSplit (m := 1) (k := 2) exSel).compl ⟨0, by omega⟩ =
      ⟨0, by omega⟩ by apply Fin.ext; omega) h0
  · rfl
  · exact absurd (show (mkSplit (m := 1) (k := 2) exSel).compl ⟨0, by omega⟩ =
      ⟨2, by omega⟩ by apply Fin.ext; omega) h2
  · omega

end Qatlib.Concepts.CircuitLang.SelFill
