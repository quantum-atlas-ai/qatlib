/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.IntWordFraming.WordFraming.FourierRecovery
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.IntWordFraming.WordFraming
set_option warningAsError false

namespace Qatlib.Papers.AbelianDecomp01.MainResults

lemma addOrderOf_pi_single_dep {ι : Type*} [DecidableEq ι] (d : ι → ℕ)
    (hd : ∀ i, 0 < d i) (i : ι) :
    addOrderOf (Pi.single i (1 : ZMod (d i)) : (j : ι) → ZMod (d j)) = d i := by
  rw [addOrderOf_eq_iff (hd i)]
  refine ⟨?_, ?_⟩
  · ext j
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  · intro mm hmm hmm0 hzero
    have hi : (mm : ZMod (d i)) = 0 := by
      have := congrFun hzero i
      simpa [Pi.single_eq_same] using! this
    have hdvd : d i ∣ mm := (ZMod.natCast_eq_zero_iff mm (d i)).mp hi
    have hle : d i ≤ mm := Nat.le_of_dvd hmm0 hdvd
    omega

theorem source_theorem7_cyclic_direct_sum
    {C : Type*} [AddCommGroup C] [Finite C] {m n : ℕ}
    (p : CompactAbelianPresentation C m n) (hp : p.Valid) :
    ∃ (g : {r : Fin m // p.run.coeff r ≠ 1} → C)
      (φ : C ≃+ (∀ r : {r : Fin m // p.run.coeff r ≠ 1}, ZMod (p.run.coeff r))),
      (∀ r, φ (g r) = Pi.single r 1) ∧
      (∀ r, addOrderOf (g r) = p.run.coeff r) ∧
      Fintype.card {r : Fin m // p.run.coeff r ≠ 1} ≤ m := by
  classical
  have hfin : p.run.isFinite = true :=
    (compactRecovery_finite_iff p hp).mpr inferInstance
  have hne : ∀ r : Fin m, p.run.coeff r ≠ 0 := by
    simpa only [NormalizedSmithData.isFinite, decide_eq_true_eq] using! hfin
  have hpos : ∀ r : Fin m, 0 < p.run.coeff r := fun r => Nat.pos_of_ne_zero (hne r)
  refine ⟨fun r => (compactRecoveryEquiv p hp).symm (Pi.single r 1),
    compactRecoveryEquiv p hp, ?_, ?_, ?_⟩
  · intro r
    simp
  · intro r
    rw [AddEquiv.addOrderOf_eq]
    exact addOrderOf_pi_single_dep (ι := {r : Fin m // p.run.coeff r ≠ 1})
      (fun r => p.run.coeff r) (fun r => hpos r) r
  · calc Fintype.card {r : Fin m // p.run.coeff r ≠ 1}
        ≤ Fintype.card (Fin m) := Fintype.card_subtype_le _
      _ = m := Fintype.card_fin m

theorem source_theorem7_generator_words
    {C : Type*} [AddCommGroup C] [Finite C] {m n : ℕ}
    (p : CompactAbelianPresentation C m n) (hp : p.Valid)
    (r : {r : Fin m // p.run.coeff r ≠ 1}) :
    addOrderOf (generatorWordMap p.generators
        (fun i => p.run.reduction.leftInverse i (r : Fin m))) = p.run.coeff (r : Fin m) := by
  classical
  have hpos : ∀ r : Fin m, 0 < p.run.coeff r := by
    have hfin : p.run.isFinite = true :=
      (compactRecovery_finite_iff p hp).mpr inferInstance
    have hne : ∀ r : Fin m, p.run.coeff r ≠ 0 := by
      simpa only [NormalizedSmithData.isFinite, decide_eq_true_eq] using! hfin
    intro r
    exact Nat.pos_of_ne_zero (hne r)
  have hsingle : (fun s : {i : Fin m // p.run.coeff i ≠ 1} =>
      if (s : Fin m) = (r : Fin m) then (1 : ZMod (p.run.coeff (s : Fin m))) else 0) =
      Pi.single r 1 := by
    funext s
    by_cases h : (s : Fin m) = (r : Fin m)
    · have hs : s = r := Subtype.ext h
      subst hs
      rw [if_pos rfl, Pi.single_eq_same]
    · have hs : s ≠ r := fun hs => h (by rw [hs])
      rw [if_neg h, Pi.single_eq_of_ne hs]
  calc addOrderOf (generatorWordMap p.generators
          (fun i => p.run.reduction.leftInverse i (r : Fin m)))
      = addOrderOf (compactRecoveryEquiv p hp (generatorWordMap p.generators
          (fun i => p.run.reduction.leftInverse i (r : Fin m)))) :=
        (AddEquiv.addOrderOf_eq (compactRecoveryEquiv p hp) _).symm
    _ = addOrderOf (fun s : {i : Fin m // p.run.coeff i ≠ 1} =>
          if (s : Fin m) = (r : Fin m) then (1 : ZMod (p.run.coeff (s : Fin m))) else 0) := by
        rw [compactRecovery_generator p hp (r : Fin m)]
    _ = addOrderOf (Pi.single r 1) := by rw [hsingle]
    _ = p.run.coeff (r : Fin m) :=
        addOrderOf_pi_single_dep (ι := {i : Fin m // p.run.coeff i ≠ 1})
          (fun s => p.run.coeff (s : Fin m)) (fun s => hpos (s : Fin m)) r

end Qatlib.Papers.AbelianDecomp01.MainResults
