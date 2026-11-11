/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BosonFock.BosonOperators.BosonPermanent
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Complex.BigOperators

/-!
# Finite bosonic sectors and second quantization

`Sector` is the Hilbert space indexed by occupations of a fixed particle number. `create` and
`annihilate` connect adjacent sectors with square-root occupation coefficients, while
`cutCreate` restricts creation to a finite particle cutoff. The module proves graded commutation
relations, operator norm bounds, and the compatibility of the permanent formula `gamma` with
second quantization.

The mathematical background is described in [BratteliRobinson1997II].

## Main statements

* `graded_creation_annihilation`: basis, vacuum, and graded commutation identities.
* `sector_and_polynomial_norm_bounds`: sector and cutoff polynomial norm estimates.
* `second_quantization_permanent_bridge`: unitary mode transformations, ladder operators, and
  boson weights.

## References

* [Bratteli and Robinson, 1997][BratteliRobinson1997II]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib
open scoped BigOperators Classical Matrix Matrix.Norms.L2Operator

/-- The type of mode occupations with fixed total particle number, identified with
`FockOccupation`. -/
abbrev Occupation := FockOccupation
/-- The complex Euclidean Hilbert space indexed by occupations of `n` particles in `m` modes. -/
abbrev Sector (m n : ℕ) := EuclideanSpace ℂ (Occupation m n)
/-- The unit coordinate vector corresponding to the occupation `s`. -/
def basis {m n : ℕ} (s : Occupation m n) : Sector m n := WithLp.toLp 2 (Pi.single s 1)
/-- The occupation with zero particles in every mode. -/
def vacuum (m : ℕ) : Occupation m 0 := ⟨fun _ => 0, by simp⟩
/-- The particle number operator on the `n`-particle sector, equal to `n` times the identity. -/
def number (m n : ℕ) : Matrix (Occupation m n) (Occupation m n) ℂ := (n : ℂ) • 1

/-- The creation matrix from sector `n` to sector `n + 1`, adding one particle in mode `i` with
coefficient `sqrt (s i + 1)`. -/
def create (m n : ℕ) (i : Fin m) : Matrix (Occupation m (n+1)) (Occupation m n) ℂ :=
  fun t s => if ∀ j, (t.val j : ℕ) = (s.val j : ℕ) + if j = i then 1 else 0
    then (Real.sqrt ((s.val i : ℕ) + 1) : ℂ) else 0
/-- The annihilation matrix from sector `n + 1` to sector `n`, defined as the adjoint of
creation in mode `i`. -/
def annihilate (m n : ℕ) (i : Fin m) := (create m n i).conjTranspose
/-- The occupation basis containing all particle sectors from zero through the cutoff `Q`. -/
abbrev CutBasis (m Q : ℕ) := (n : Fin (Q+1)) × Occupation m n.val
/-- The creation matrix on the cutoff basis, raising occupation in mode `i` when the resulting
sector lies within the cutoff. -/
def cutCreate (m Q : ℕ) (i : Fin m) : Matrix (CutBasis m Q) (CutBasis m Q) ℂ :=
  fun t s => if t.1.val = s.1.val+1 ∧
    (∀ j, (t.2.val j : ℕ) = (s.2.val j : ℕ) + if j = i then 1 else 0)
    then (Real.sqrt ((s.2.val i : ℕ) + 1) : ℂ) else 0

/-- The ordered product of cutoff ladder matrices specified by a list, with `true` selecting
creation and `false` its adjoint. -/
def cutWord (m Q : ℕ) (w : List (Fin m × Bool)) : Matrix (CutBasis m Q) (CutBasis m Q) ℂ :=
  w.foldr (fun a B => (if a.2 then cutCreate m Q a.1 else (cutCreate m Q a.1).conjTranspose) * B) 1

/-- The mode label at position `a` in the list repeating each mode according to occupation `s`. -/
def rowAt {m n : ℕ} (s : Occupation m n) (a : Fin n) : Fin m :=
  (bosonRows (fun i => (s.val i : ℕ))).get ⟨a.val, by
    rw [(bosonRows_length _).trans s.property]; exact a.isLt⟩
/-- The matrix obtained from `U` by repeating its rows and columns according to occupations `r`
and `s`. -/
def occupationMatrix {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (r s : Occupation m n) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => U (rowAt r a) (rowAt s b)
/-- The fixed-particle matrix whose entries are permanents of repeated mode matrices divided by
the square root of the two occupation factorial products. -/
def gamma (m n : ℕ) (U : Matrix (Fin m) (Fin m) ℂ) : Matrix (Occupation m n) (Occupation m n) ℂ :=
  fun r s => Matrix.permanent (occupationMatrix U r s) /
    (Real.sqrt ((∏ i, (r.val i : ℕ).factorial) * (∏ i, (s.val i : ℕ).factorial)) : ℂ)

/-- Two occupations are equal when their particle counts agree in every mode. -/
@[ext]
private theorem occupation_ext {m n : ℕ} {s t : Occupation m n}
    (h : ∀ j, (s.val j : ℕ) = (t.val j : ℕ)) : s = t :=
  Subtype.ext (funext fun j => Fin.ext (h j))

/-- The occupation of any mode is at most the total particle number. -/
private theorem occupation_val_le {m n : ℕ} (s : Occupation m n) (j : Fin m) :
    (s.val j : ℕ) ≤ n := by
  have h1 := Finset.single_le_sum (f := fun k : Fin m => (s.val k : ℕ))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have h2 := s.property
  omega

/-- The sum of occupations in two distinct modes is at most the total particle number. -/
private theorem occupation_add_le {m n : ℕ} (s : Occupation m n) {j i : Fin m} (hji : j ≠ i) :
    (s.val j : ℕ) + (s.val i : ℕ) ≤ n := by
  have h1 := Finset.add_le_sum (f := fun k : Fin m => (s.val k : ℕ))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j) (Finset.mem_univ i) hji
  have h2 := s.property
  try dsimp at h1
  omega

/-- The occupation obtained by adding one particle in mode `i`. -/
private def bump {m n : ℕ} (s : Occupation m n) (i : Fin m) : Occupation m (n + 1) :=
  ⟨fun j => ⟨(s.val j : ℕ) + if j = i then 1 else 0, by
    have hle := occupation_val_le s j
    split_ifs <;> omega⟩, by
    simp only [Finset.sum_add_distrib, s.property, Fintype.sum_ite_eq']⟩

/-- Adding a particle increases the count in mode `i` by one and leaves other counts unchanged. -/
@[simp]
private theorem bump_val {m n : ℕ} (s : Occupation m n) (i j : Fin m) :
    ((bump s i).val j : ℕ) = (s.val j : ℕ) + if j = i then 1 else 0 := rfl

/-- The entrywise one-particle increment condition is equivalent to equality with `bump s i`. -/
private theorem step_iff_eq_bump {m n : ℕ} {t : Occupation m (n + 1)} {s : Occupation m n} {i : Fin m} :
    (∀ j, (t.val j : ℕ) = (s.val j : ℕ) + if j = i then 1 else 0) ↔ t = bump s i :=
  ⟨fun h => occupation_ext h, fun h j => by rw [h, bump_val]⟩

/-- Adding a particle in a fixed mode is injective on occupations. -/
private theorem bump_injective {m n : ℕ} (i : Fin m) {s₁ s₂ : Occupation m n}
    (h : bump s₁ i = bump s₂ i) : s₁ = s₂ := by
  ext j
  have hj := congrArg (fun t : Occupation m (n + 1) => (t.val j : ℕ)) h
  dsimp [bump] at hj
  omega

/-- Adding particles in two modes commutes. -/
private theorem bump_comm {m n : ℕ} (s : Occupation m n) (i j : Fin m) :
    bump (bump s j) i = bump (bump s i) j := by
  ext k
  simp only [bump_val]
  omega

/-- The occupation obtained by removing one particle from a mode with positive occupation. -/
private def unbump {m n : ℕ} (t : Occupation m (n + 1)) (i : Fin m) (h : 0 < (t.val i : ℕ)) :
    Occupation m n :=
  ⟨fun j => ⟨(t.val j : ℕ) - if j = i then 1 else 0, by
    by_cases hji : j = i
    · subst hji
      have hlt := (t.val j).isLt
      simp; omega
    · have hle := occupation_add_le t hji
      simp [hji]; omega⟩, by
    have h1 : ∀ j : Fin m, ((t.val j : ℕ) - if j = i then 1 else 0) + (if j = i then 1 else 0) = (t.val j : ℕ) := by
      intro j
      by_cases hji : j = i
      · subst hji; simp; omega
      · simp [hji]
    have h2 : (∑ j : Fin m, ((t.val j : ℕ) - if j = i then 1 else 0)) + (∑ j : Fin m, if j = i then 1 else 0) = n + 1 := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun j _ => h1 j, t.property]
    rw [Fintype.sum_ite_eq'] at h2
    dsimp
    omega⟩

/-- Removing a particle subtracts one in the chosen mode and leaves all other counts unchanged. -/
@[simp]
private theorem unbump_val {m n : ℕ} (t : Occupation m (n + 1)) (i : Fin m)
    (h : 0 < (t.val i : ℕ)) (j : Fin m) :
    ((unbump t i h).val j : ℕ) = (t.val j : ℕ) - if j = i then 1 else 0 := rfl

/-- Adding back a particle after removing it from an occupied mode recovers the original
occupation. -/
private theorem bump_unbump {m n : ℕ} (t : Occupation m (n + 1)) (i : Fin m) (h : 0 < (t.val i : ℕ)) :
    bump (unbump t i h) i = t := by
  ext j
  simp only [bump_val, unbump_val]
  by_cases hji : j = i
  · subst hji; simp; omega
  · simp [hji]

/-- A creation matrix entry is `sqrt (s i + 1)` at the incremented occupation and zero
elsewhere. -/
private theorem create_apply_bump {m n : ℕ} (i : Fin m) (t : Occupation m (n + 1)) (s : Occupation m n) :
    create m n i t s = if t = bump s i then (Real.sqrt ((s.val i : ℕ) + 1) : ℂ) else 0 := by
  unfold create
  simp only [step_iff_eq_bump]

/-- An annihilation matrix entry is `sqrt (s i + 1)` exactly when its input occupation is `bump
s i`. -/
private theorem annihilate_apply_bump {m n : ℕ} (i : Fin m) (s : Occupation m n) (t : Occupation m (n + 1)) :
    annihilate m n i s t = if t = bump s i then (Real.sqrt ((s.val i : ℕ) + 1) : ℂ) else 0 := by
  change star (create m n i t s) = _
  rw [create_apply_bump]
  split_ifs <;> simp

/-- An annihilation entry equals the square root of the input occupation in mode `i` when the
output removes that particle, and is zero otherwise. -/
private theorem annihilate_apply_formula {m n : ℕ} (i : Fin m) (s : Occupation m n) (t : Occupation m (n + 1)) :
    annihilate m n i s t =
      if ∀ j, (t.val j : ℕ) = (s.val j : ℕ) + if j = i then 1 else 0
      then (Real.sqrt (t.val i : ℕ) : ℂ) else 0 := by
  rw [annihilate_apply_bump]
  simp only [step_iff_eq_bump]
  split_ifs with h
  · rw [h, bump_val]
    simp
  · rfl

/-- An entry of annihilation after creation is the product of the two square-root coefficients
when the corresponding incremented occupations agree, and zero otherwise. -/
private theorem annihilate_mul_create_entry {m n : ℕ} (i j : Fin m) (r s : Occupation m n) :
    (annihilate m n i * create m n j) r s =
      if bump r i = bump s j then
        (Real.sqrt ((r.val i : ℕ) + 1) : ℂ) * (Real.sqrt ((s.val j : ℕ) + 1) : ℂ)
      else 0 := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (bump s j)]
  · rw [annihilate_apply_bump, create_apply_bump, if_pos rfl]
    by_cases h : bump r i = bump s j
    · rw [if_pos h.symm, if_pos h]
    · have h' : bump s j ≠ bump r i := fun hs => h hs.symm
      rw [if_neg h', if_neg h, zero_mul]
  · intro t _ ht
    rw [create_apply_bump, if_neg ht, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- An entry of creation after annihilation is determined by removing a particle from an
occupied input mode and then adding one in the creation mode. -/
private theorem create_mul_annihilate_entry {m n : ℕ} (i j : Fin m) (r s : Occupation m (n + 1)) :
    (create m n j * annihilate m n i) r s =
      if h : 0 < (s.val i : ℕ) then
        if r = bump (unbump s i h) j then
          (Real.sqrt (((unbump s i h).val j : ℕ) + 1) : ℂ) * (Real.sqrt (s.val i : ℕ) : ℂ)
        else 0
      else 0 := by
  rw [Matrix.mul_apply]
  by_cases h : 0 < (s.val i : ℕ)
  · rw [dif_pos h, Finset.sum_eq_single (unbump s i h)]
    · rw [create_apply_bump, annihilate_apply_bump, if_pos (bump_unbump s i h).symm]
      have hval : (((unbump s i h).val i : ℕ) : ℝ) + 1 = (s.val i : ℕ) := by
        rw [unbump_val, if_pos rfl]
        exact_mod_cast Nat.sub_add_cancel h
      rw [hval]
      split_ifs <;> ring
    · intro u _ hu
      have hne : s ≠ bump u i := by
        intro hsu
        apply hu
        apply bump_injective i
        rw [bump_unbump, hsu]
      rw [annihilate_apply_bump, if_neg hne, mul_zero]
    · intro hm
      exact absurd (Finset.mem_univ _) hm
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun u _ => ?_
    have hne : s ≠ bump u i := by
      intro hsu
      apply h
      rw [hsu, bump_val, if_pos rfl]
      omega
    rw [annihilate_apply_bump, if_neg hne, mul_zero]

/-- On the vacuum sector, annihilation in mode `i` after creation in mode `j` is the identity
times the Kronecker delta of the modes. -/
private theorem ccr_zero {m : ℕ} (i j : Fin m) :
    annihilate m 0 i * create m 0 j = (if i = j then (1 : ℂ) else 0) • 1 := by
  ext r s
  have hr0 : ∀ k, (r.val k : ℕ) = 0 := fun k => Nat.eq_zero_of_le_zero (occupation_val_le r k)
  have hs0 : ∀ k, (s.val k : ℕ) = 0 := fun k => Nat.eq_zero_of_le_zero (occupation_val_le s k)
  have hrs : r = s := occupation_ext fun k => by rw [hr0 k, hs0 k]
  rw [annihilate_mul_create_entry, Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos (by rw [hrs]), if_pos rfl, if_pos hrs, hr0 i, hs0 i]
    simp
  · have hne : bump r i ≠ bump s j := by
      intro h
      have hi := congrArg (fun t : Occupation m 1 => (t.val i : ℕ)) h
      dsimp [bump] at hi
      rw [hr0 i, hs0 i, if_pos rfl, if_neg hij] at hi
      omega
    rw [if_neg hne, if_neg hij, zero_smul]

/-- On each positive particle sector, annihilation followed by creation minus creation followed
by annihilation equals the identity times the mode Kronecker delta. -/
private theorem ccr_succ {m n : ℕ} (i j : Fin m) :
    annihilate m (n + 1) i * create m (n + 1) j - create m n j * annihilate m n i =
      (if i = j then (1 : ℂ) else 0) • 1 := by
  ext r s
  rw [Matrix.sub_apply, annihilate_mul_create_entry, create_mul_annihilate_entry,
    Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, one_smul]
    by_cases hrs : r = s
    · subst hrs
      rw [if_pos rfl, if_pos rfl]
      have hsq1 : (Real.sqrt ((r.val i : ℕ) + 1) : ℂ) * (Real.sqrt ((r.val i : ℕ) + 1) : ℂ) =
          ((r.val i : ℕ) : ℂ) + 1 := by
        norm_cast
        rw [Real.mul_self_sqrt (by positivity)]
      by_cases hpos : 0 < (r.val i : ℕ)
      · rw [dif_pos hpos, if_pos (bump_unbump r i hpos).symm]
        have hval : (((unbump r i hpos).val i : ℕ) : ℝ) + 1 = (r.val i : ℕ) := by
          rw [unbump_val, if_pos rfl]
          exact_mod_cast Nat.sub_add_cancel hpos
        rw [hval, hsq1]
        have hsq2 : (Real.sqrt (r.val i : ℕ) : ℂ) * (Real.sqrt (r.val i : ℕ) : ℂ) =
            ((r.val i : ℕ) : ℂ) := by
          norm_cast
          rw [Real.mul_self_sqrt (by positivity)]
        rw [hsq2]
        ring
      · rw [dif_neg hpos, hsq1]
        have hz : (r.val i : ℕ) = 0 := by omega
        simp [hz]
    · have hne1 : bump r i ≠ bump s i := fun h => hrs (bump_injective i h)
      rw [if_neg hne1, if_neg hrs]
      by_cases hpos : 0 < (s.val i : ℕ)
      · rw [dif_pos hpos, bump_unbump s i hpos, if_neg hrs, sub_zero]
      · rw [dif_neg hpos, sub_zero]
  · rw [if_neg hij, zero_smul, sub_eq_zero]
    by_cases hpos : 0 < (s.val i : ℕ)
    · rw [dif_pos hpos]
      have heq_iff : bump r i = bump s j ↔ r = bump (unbump s i hpos) j := by
        constructor
        · intro h
          apply bump_injective i
          rw [h, ← bump_comm, bump_unbump s i hpos]
        · rintro rfl
          rw [← bump_comm, bump_unbump]
      by_cases hb : bump r i = bump s j
      · have hr : r = bump (unbump s i hpos) j := heq_iff.mp hb
        rw [if_pos hb, if_pos hr]
        have h1 : ((unbump s i hpos).val j : ℕ) = (s.val j : ℕ) := by
          rw [unbump_val, if_neg (Ne.symm hij), Nat.sub_zero]
        have h2 : (r.val i : ℕ) + 1 = (s.val i : ℕ) := by
          have hi := congrArg (fun t : Occupation m (n + 2) => (t.val i : ℕ)) hb
          dsimp [bump] at hi
          rw [if_pos rfl, if_neg hij, Nat.add_zero] at hi
          exact hi
        rw [h1]
        have h2' : ((r.val i : ℕ) : ℝ) + 1 = (s.val i : ℕ) := by exact_mod_cast h2
        rw [h2', mul_comm]
      · have hr : r ≠ bump (unbump s i hpos) j := fun h => hb (heq_iff.mpr h)
        rw [if_neg hb, if_neg hr]
    · rw [dif_neg hpos]
      have hne : bump r i ≠ bump s j := by
        intro hb
        have hi := congrArg (fun t : Occupation m (n + 2) => (t.val i : ℕ)) hb
        dsimp [bump] at hi
        rw [if_pos rfl, if_neg hij, Nat.add_zero] at hi
        omega
      rw [if_neg hne]

/-- Creation in two modes commutes as a map between the corresponding graded sectors. -/
private theorem create_comm {m n : ℕ} (i j : Fin m) :
    create m (n + 1) i * create m n j = create m (n + 1) j * create m n i := by
  ext t s
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single (bump s j), Finset.sum_eq_single (bump s i)]
  · simp only [create_apply_bump, bump_comm s i j, if_true]
    split_ifs with h
    · by_cases hij : i = j
      · subst hij; rfl
      · have h1 : ((bump s j).val i : ℕ) = (s.val i : ℕ) := by
          rw [bump_val, if_neg hij, Nat.add_zero]
        have h2 : ((bump s i).val j : ℕ) = (s.val j : ℕ) := by
          rw [bump_val, if_neg (Ne.symm hij), Nat.add_zero]
        rw [h1, h2, mul_comm]
    · ring
  · intro u _ hu
    rw [create_apply_bump i, if_neg hu, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro u _ hu
    rw [create_apply_bump j, if_neg hu, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Below the cutoff, the same-sector entries of adjoint cutoff creation times cutoff creation
agree with graded annihilation times creation. -/
private theorem cutCreate_conjTranspose_mul_entry {m Q : ℕ} (i j : Fin m)
    {k : Fin (Q + 1)} (hk : k.val < Q) (t₂ s₂ : Occupation m k.val) :
    ((cutCreate m Q i).conjTranspose * cutCreate m Q j) ⟨k, t₂⟩ ⟨k, s₂⟩ =
      (annihilate m k.val i * create m k.val j) t₂ s₂ := by
  rw [Matrix.mul_apply]
  have hk1 : k.val + 1 < Q + 1 := Nat.succ_lt_succ hk
  let u₀ : CutBasis m Q := ⟨⟨k.val + 1, hk1⟩, bump s₂ j⟩
  rw [Finset.sum_eq_single u₀]
  · change star (cutCreate m Q i u₀ ⟨k, t₂⟩) * cutCreate m Q j u₀ ⟨k, s₂⟩ = _
    unfold cutCreate
    simp only [u₀, step_iff_eq_bump, true_and, and_self, if_true]
    rw [annihilate_mul_create_entry]
    by_cases hb : bump t₂ i = bump s₂ j
    · rw [if_pos hb.symm, if_pos hb]
      simp
    · have hb' : bump s₂ j ≠ bump t₂ i := fun h => hb h.symm
      rw [if_neg hb', if_neg hb, star_zero, zero_mul]
  · rintro ⟨uk, u₂⟩ _ hu
    have hcz : cutCreate m Q j ⟨uk, u₂⟩ ⟨k, s₂⟩ = 0 := by
      unfold cutCreate
      rw [if_neg]
      rintro ⟨huk, hstep⟩
      apply hu
      have huk' : uk = ⟨k.val + 1, hk1⟩ := Fin.ext huk
      subst huk'
      have hu₂ : u₂ = bump s₂ j := step_iff_eq_bump.mp hstep
      subst hu₂
      rfl
    rw [hcz, mul_zero]
  · intro hm; exact absurd (Finset.mem_univ _) hm

/-- The vacuum-sector entries of cutoff creation times adjoint cutoff creation vanish. -/
private theorem cutCreate_mul_conjTranspose_entry_zero {m Q : ℕ} (i j : Fin m)
    {k : Fin (Q + 1)} (hk0 : k.val = 0) (t₂ s₂ : Occupation m k.val) :
    (cutCreate m Q j * (cutCreate m Q i).conjTranspose) ⟨k, t₂⟩ ⟨k, s₂⟩ = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun u _ => ?_
  have hcz : cutCreate m Q j ⟨k, t₂⟩ u = 0 := by
    unfold cutCreate
    rw [if_neg]
    rintro ⟨h1, _⟩
    dsimp at h1
    omega
  rw [hcz, zero_mul]

/-- On a positive sector within the cutoff, cutoff creation times adjoint cutoff creation agrees
with graded creation times annihilation. -/
private theorem cutCreate_mul_conjTranspose_entry_succ {m Q n : ℕ} (i j : Fin m)
    (hklt : n + 1 < Q + 1) (t₂ s₂ : Occupation m (n + 1)) :
    (cutCreate m Q j * (cutCreate m Q i).conjTranspose) ⟨⟨n + 1, hklt⟩, t₂⟩ ⟨⟨n + 1, hklt⟩, s₂⟩ =
      (create m n j * annihilate m n i) t₂ s₂ := by
  rw [Matrix.mul_apply, create_mul_annihilate_entry]
  by_cases hpos : 0 < (s₂.val i : ℕ)
  · rw [dif_pos hpos]
    let u₀ : CutBasis m Q := ⟨⟨n, by omega⟩, unbump s₂ i hpos⟩
    rw [Finset.sum_eq_single u₀]
    · change cutCreate m Q j ⟨⟨n + 1, hklt⟩, t₂⟩ u₀ * star (cutCreate m Q i ⟨⟨n + 1, hklt⟩, s₂⟩ u₀) = _
      unfold cutCreate
      simp only [u₀, step_iff_eq_bump, true_and]
      rw [if_pos (bump_unbump s₂ i hpos).symm]
      have hval : (((unbump s₂ i hpos).val i : ℕ) : ℝ) + 1 = (s₂.val i : ℕ) := by
        rw [unbump_val, if_pos rfl]
        exact_mod_cast Nat.sub_add_cancel hpos
      rw [hval]
      split_ifs <;> simp
    · rintro ⟨⟨uk, huklt⟩, u₂⟩ _ hu
      have hcz : cutCreate m Q i ⟨⟨n + 1, hklt⟩, s₂⟩ ⟨⟨uk, huklt⟩, u₂⟩ = 0 := by
        unfold cutCreate
        rw [if_neg]
        rintro ⟨huk, hsu⟩
        have huk' : uk = n := by dsimp at huk; omega
        subst huk'
        apply hu
        have hs₂ : s₂ = bump u₂ i := step_iff_eq_bump.mp hsu
        have hu₂ : u₂ = unbump s₂ i hpos := by
          apply bump_injective i
          rw [bump_unbump, hs₂]
        subst hu₂
        rfl
      change _ * star (cutCreate m Q i ⟨⟨n + 1, hklt⟩, s₂⟩ ⟨⟨uk, huklt⟩, u₂⟩) = 0
      rw [hcz, star_zero, mul_zero]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · rw [dif_neg hpos]
    refine Finset.sum_eq_zero fun ⟨⟨uk, huklt⟩, u₂⟩ _ => ?_
    have hcz : cutCreate m Q i ⟨⟨n + 1, hklt⟩, s₂⟩ ⟨⟨uk, huklt⟩, u₂⟩ = 0 := by
      unfold cutCreate
      rw [if_neg]
      rintro ⟨huk, hsu⟩
      have huk' : uk = n := by dsimp at huk; omega
      subst huk'
      have hs₂ : s₂ = bump u₂ i := step_iff_eq_bump.mp hsu
      apply hpos
      rw [hs₂, bump_val, if_pos rfl]
      omega
    change _ * star (cutCreate m Q i ⟨⟨n + 1, hklt⟩, s₂⟩ ⟨⟨uk, huklt⟩, u₂⟩) = 0
    rw [hcz, star_zero, mul_zero]

/-- Occupation basis vectors have inner product one when their labels agree and zero otherwise. -/
private theorem inner_basis {m n : ℕ} (s t : Occupation m n) :
    inner ℂ (basis s) (basis t) = if s = t then 1 else 0 := by
  change inner ℂ (EuclideanSpace.single s (1 : ℂ)) (basis t) = _
  rw [EuclideanSpace.inner_single_left]
  simp [basis]

/-- The occupation basis is orthonormal, the vacuum is unit, and the ladder matrices satisfy
their adjoint, number operator, and graded commutation identities. The cutoff commutator
agrees with the mode Kronecker delta on each sector below the cutoff. -/
theorem graded_creation_annihilation :
    (∀ (m n : ℕ) (s t : Occupation m n),
      inner ℂ (basis s) (basis t) = if s=t then 1 else 0) ∧
    (∀ m, ‖basis (vacuum m)‖ = 1) ∧
    (∀ (m n : ℕ) (i : Fin m),
      annihilate m n i = (create m n i).conjTranspose ∧
      (∀ s t, annihilate m n i s t =
        if ∀ j, (t.val j : ℕ) = (s.val j : ℕ) + if j = i then 1 else 0
        then (Real.sqrt (t.val i : ℕ) : ℂ) else 0) ∧
      number m (n+1) * create m n i - create m n i * number m n = create m n i) ∧
    (∀ (m : ℕ) (i j : Fin m),
      annihilate m 0 i * create m 0 j = (if i=j then (1:ℂ) else 0) • 1) ∧
    (∀ (m n : ℕ) (i j : Fin m),
      annihilate m (n+1) i * create m (n+1) j - create m n j * annihilate m n i =
        (if i=j then (1:ℂ) else 0) • 1) ∧
    (∀ (m n : ℕ) (i j : Fin m),
      create m (n+1) i * create m n j = create m (n+1) j * create m n i) ∧
    (∀ (m Q : ℕ) (i j : Fin m) (s t : CutBasis m Q),
      s.1.val < Q → t.1 = s.1 →
      ((cutCreate m Q i).conjTranspose * cutCreate m Q j -
        cutCreate m Q j * (cutCreate m Q i).conjTranspose) t s =
        if i=j ∧ t=s then 1 else 0) := by
  refine ⟨fun m n s t => inner_basis s t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_basis, if_pos rfl]
    simp
  · intro m n i
    refine ⟨rfl, annihilate_apply_formula i, ?_⟩
    ext t s
    simp only [number, Matrix.sub_apply, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  · intro m i j
    exact ccr_zero i j
  · intro m n i j
    exact ccr_succ i j
  · intro m n i j
    exact create_comm i j
  · rintro m Q i j ⟨⟨kval, hklt⟩, s₂⟩ ⟨kt, t₂⟩ hlt hkt
    dsimp at hkt hlt
    subst hkt
    rw [Matrix.sub_apply, cutCreate_conjTranspose_mul_entry i j hlt t₂ s₂]
    rcases kval with _ | n
    · rw [cutCreate_mul_conjTranspose_entry_zero i j rfl t₂ s₂, sub_zero]
      have h0 := congrFun (congrFun (ccr_zero (m := m) i j) t₂) s₂
      rw [h0, Matrix.smul_apply, Matrix.one_apply]
      by_cases hij : i = j <;> by_cases hts : t₂ = s₂ <;> simp [hij, hts]
    · rw [cutCreate_mul_conjTranspose_entry_succ i j hklt t₂ s₂]
      have h1 := congrFun (congrFun (ccr_succ (m := m) (n := n) i j) t₂) s₂
      rw [Matrix.sub_apply] at h1
      rw [h1, Matrix.smul_apply, Matrix.one_apply]
      by_cases hij : i = j <;> by_cases hts : t₂ = s₂ <;> simp [hij, hts]

/-- A uniform squared Euclidean output estimate with nonnegative constant `C` bounds the matrix
operator norm by `C`. -/
private theorem l2_opNorm_le_of_mulVec_sq {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x : J → ℂ, ∑ i : I, ‖A.mulVec x i‖ ^ 2 ≤ C ^ 2 * ∑ j : J, ‖x j‖ ^ 2) :
    ‖A‖ ≤ C := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
  have hx := h x.ofLp
  rw [← EuclideanSpace.norm_sq_eq] at hx
  have hTx : ∑ i : I, ‖A.mulVec x.ofLp i‖ ^ 2 =
      ‖(((Matrix.toEuclideanLin (𝕜 := ℂ) (m := I) (n := J)).trans
        LinearMap.toContinuousLinearMap A) x)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  rw [hTx, ← mul_pow] at hx
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp hx

/-- Annihilation applied to a vector at occupation `s` is `sqrt (s i + 1)` times the input at
`bump s i`. -/
private theorem annihilate_mulVec_apply {m n : ℕ} (i : Fin m) (y : Occupation m (n + 1) → ℂ)
    (s : Occupation m n) :
    (annihilate m n i).mulVec y s = (Real.sqrt ((s.val i : ℕ) + 1) : ℂ) * y (bump s i) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (bump s i)]
  · rw [annihilate_apply_bump, if_pos rfl]
  · intro t _ ht
    rw [annihilate_apply_bump, if_neg ht, zero_mul]
  · intro hm; exact absurd (Finset.mem_univ _) hm

/-- The squared norm of a weighted annihilation output is bounded by `n + 1` times the
coefficient squared norm and the input squared norm. -/
private theorem weighted_annihilate_mulVec_sq (m n : ℕ) (u : Fin m → ℂ)
    (y : Occupation m (n + 1) → ℂ) :
    ∑ s : Occupation m n, ‖(∑ i, star (u i) • annihilate m n i).mulVec y s‖ ^ 2 ≤
      (n + 1 : ℝ) * (∑ i, Complex.normSq (u i)) * ∑ t : Occupation m (n + 1), ‖y t‖ ^ 2 := by
  let U : ℝ := ∑ i : Fin m, Complex.normSq (u i)
  have hU : 0 ≤ U := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (u i)
  have hpt : ∀ s : Occupation m n,
      ‖(∑ i, star (u i) • annihilate m n i).mulVec y s‖ ^ 2 ≤
        U * ∑ i : Fin m, (((bump s i).val i : ℕ) : ℝ) * ‖y (bump s i)‖ ^ 2 := by
    intro s
    have hmul : (∑ i, star (u i) • annihilate m n i).mulVec y s =
        ∑ i : Fin m, star (u i) * ((Real.sqrt ((s.val i : ℕ) + 1) : ℂ) * y (bump s i)) := by
      rw [Matrix.sum_mulVec, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.smul_mulVec, Pi.smul_apply, annihilate_mulVec_apply, smul_eq_mul]
    rw [hmul]
    calc ‖∑ i : Fin m, star (u i) * ((Real.sqrt ((s.val i : ℕ) + 1) : ℂ) * y (bump s i))‖ ^ 2
        ≤ (∑ i : Fin m, ‖star (u i) * ((Real.sqrt ((s.val i : ℕ) + 1) : ℂ) * y (bump s i))‖) ^ 2 := by
          gcongr
          exact norm_sum_le _ _
      _ = (∑ i : Fin m, ‖u i‖ * (Real.sqrt ((s.val i : ℕ) + 1) * ‖y (bump s i)‖)) ^ 2 := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul, norm_star, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      _ ≤ (∑ i : Fin m, ‖u i‖ ^ 2) *
            ∑ i : Fin m, (Real.sqrt ((s.val i : ℕ) + 1) * ‖y (bump s i)‖) ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
      _ = U * ∑ i : Fin m, (((bump s i).val i : ℕ) : ℝ) * ‖y (bump s i)‖ ^ 2 := by
          congr 1
          · refine Finset.sum_congr rfl fun i _ => Complex.sq_norm (u i)
          · refine Finset.sum_congr rfl fun i _ => ?_
            rw [mul_pow, Real.sq_sqrt (by positivity)]
            have hb : (((bump s i).val i : ℕ) : ℝ) = (s.val i : ℕ) + 1 := by
              rw [bump_val, if_pos rfl]
              push_cast
              rfl
            rw [hb]
  calc ∑ s : Occupation m n, ‖(∑ i, star (u i) • annihilate m n i).mulVec y s‖ ^ 2
      ≤ ∑ s : Occupation m n, U * ∑ i : Fin m, (((bump s i).val i : ℕ) : ℝ) * ‖y (bump s i)‖ ^ 2 :=
        Finset.sum_le_sum fun s _ => hpt s
    _ = U * ∑ i : Fin m, ∑ s : Occupation m n, (((bump s i).val i : ℕ) : ℝ) * ‖y (bump s i)‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ U * ∑ i : Fin m, ∑ t : Occupation m (n + 1), ((t.val i : ℕ) : ℝ) * ‖y t‖ ^ 2 := by
        gcongr with i _
        have hinj : ∀ s₁ ∈ (Finset.univ : Finset (Occupation m n)),
            ∀ s₂ ∈ (Finset.univ : Finset (Occupation m n)),
            bump s₁ i = bump s₂ i → s₁ = s₂ := fun s₁ _ s₂ _ h => bump_injective i h
        rw [← Finset.sum_image (f := fun t : Occupation m (n + 1) => ((t.val i : ℕ) : ℝ) * ‖y t‖ ^ 2) hinj]
        exact Finset.sum_le_univ_sum_of_nonneg fun t => by positivity
    _ = (n + 1 : ℝ) * U * ∑ t : Occupation m (n + 1), ‖y t‖ ^ 2 := by
        rw [Finset.sum_comm]
        have hsum : ∀ t : Occupation m (n + 1),
            (∑ i : Fin m, ((t.val i : ℕ) : ℝ) * ‖y t‖ ^ 2) = (n + 1 : ℝ) * ‖y t‖ ^ 2 := by
          intro t
          rw [← Finset.sum_mul]
          have ht : (∑ i : Fin m, ((t.val i : ℕ) : ℝ)) = (n + 1 : ℝ) := by
            exact_mod_cast t.property
          rw [ht]
        simp only [hsum, ← Finset.mul_sum]
        ring

/-- The weighted annihilation operator has norm at most `sqrt (n + 1)` times the Euclidean norm
of its mode coefficients. -/
private theorem weighted_annihilate_norm_le (m n : ℕ) (u : Fin m → ℂ) :
    ‖∑ i, star (u i) • annihilate m n i‖ ≤
      Real.sqrt (n + 1) * Real.sqrt (∑ i, Complex.normSq (u i)) := by
  let U : ℝ := ∑ i : Fin m, Complex.normSq (u i)
  have hU : 0 ≤ U := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (u i)
  let C : ℝ := Real.sqrt (n + 1) * Real.sqrt U
  refine l2_opNorm_le_of_mulVec_sq _ C (by positivity) fun y => ?_
  have hC2 : C ^ 2 = (n + 1 : ℝ) * U := by
    dsimp [C]
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hU]
  rw [hC2]
  exact weighted_annihilate_mulVec_sq m n u y

/-- The weighted creation operator has norm at most `sqrt (n + 1)` times the Euclidean norm of
its mode coefficients. -/
private theorem weighted_create_norm_le (m n : ℕ) (u : Fin m → ℂ) :
    ‖∑ i, u i • create m n i‖ ≤
      Real.sqrt (n + 1) * Real.sqrt (∑ i, Complex.normSq (u i)) := by
  have hconj : (∑ i, u i • create m n i).conjTranspose = ∑ i, star (u i) • annihilate m n i := by
    ext s t
    simp [Matrix.sum_apply, Matrix.smul_apply, annihilate]
  rw [← Matrix.l2_opNorm_conjTranspose, hconj]
  exact weighted_annihilate_norm_le m n u

/-- Adjoint cutoff creation acts by graded annihilation on the next input sector below the
cutoff and vanishes at the top sector. -/
private theorem cutCreate_conjTranspose_mulVec_apply {m Q : ℕ} (i : Fin m)
    (y : CutBasis m Q → ℂ) (k : Fin (Q + 1)) (s₂ : Occupation m k.val) :
    (cutCreate m Q i).conjTranspose.mulVec y ⟨k, s₂⟩ =
      if h : k.val < Q then
        (annihilate m k.val i).mulVec (fun t₂ => y ⟨⟨k.val + 1, Nat.succ_lt_succ h⟩, t₂⟩) s₂
      else 0 := by
  by_cases h : k.val < Q
  · rw [dif_pos h, annihilate_mulVec_apply]
    let t₀ : CutBasis m Q := ⟨⟨k.val + 1, Nat.succ_lt_succ h⟩, bump s₂ i⟩
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single t₀]
    · change star (cutCreate m Q i t₀ ⟨k, s₂⟩) * y t₀ = _
      unfold cutCreate
      simp only [t₀, step_iff_eq_bump, and_self, if_true]
      simp
    · rintro ⟨⟨tk, htk⟩, t₂⟩ _ ht
      have hcz : cutCreate m Q i ⟨⟨tk, htk⟩, t₂⟩ ⟨k, s₂⟩ = 0 := by
        unfold cutCreate
        rw [if_neg]
        rintro ⟨htk', hstep⟩
        dsimp at htk'
        subst htk'
        have ht₂ : t₂ = bump s₂ i := step_iff_eq_bump.mp hstep
        subst ht₂
        exact ht rfl
      change star (cutCreate m Q i ⟨⟨tk, htk⟩, t₂⟩ ⟨k, s₂⟩) * _ = 0
      rw [hcz, star_zero, zero_mul]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · rw [dif_neg h, Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun ⟨⟨tk, htk⟩, t₂⟩ _ => ?_
    have hcz : cutCreate m Q i ⟨⟨tk, htk⟩, t₂⟩ ⟨k, s₂⟩ = 0 := by
      unfold cutCreate
      rw [if_neg]
      rintro ⟨htk', _⟩
      dsimp at htk'
      omega
    change star (cutCreate m Q i ⟨⟨tk, htk⟩, t₂⟩ ⟨k, s₂⟩) * _ = 0
    rw [hcz, star_zero, zero_mul]

/-- A weighted sum of cutoff creation matrices has norm at most `sqrt Q` times the Euclidean
norm of its coefficients. -/
private theorem weighted_cutCreate_norm_le (m Q : ℕ) (u : Fin m → ℂ) :
    ‖∑ i, u i • cutCreate m Q i‖ ≤
      Real.sqrt Q * Real.sqrt (∑ i, Complex.normSq (u i)) := by
  let U : ℝ := ∑ i : Fin m, Complex.normSq (u i)
  have hU : 0 ≤ U := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (u i)
  let C : ℝ := Real.sqrt Q * Real.sqrt U
  let B : Matrix (CutBasis m Q) (CutBasis m Q) ℂ :=
    ∑ i, star (u i) • (cutCreate m Q i).conjTranspose
  have hconj : (∑ i, u i • cutCreate m Q i).conjTranspose = B := by
    ext s t
    simp [B, Matrix.sum_apply, Matrix.smul_apply]
  rw [← Matrix.l2_opNorm_conjTranspose, hconj]
  refine l2_opNorm_le_of_mulVec_sq B C (by positivity) fun y => ?_
  have hC2 : C ^ 2 = (Q : ℝ) * U := by
    dsimp [C]
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hU]
  rw [hC2]
  let g (k : Fin (Q + 1)) : ℝ := ∑ t₂ : Occupation m k.val, ‖y ⟨k, t₂⟩‖ ^ 2
  have hg_nonneg : ∀ k, 0 ≤ g k := fun k => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsector : ∀ k : Fin (Q + 1),
      (∑ s₂ : Occupation m k.val, ‖B.mulVec y ⟨k, s₂⟩‖ ^ 2) ≤
        if h : k.val < Q then (Q : ℝ) * U * g ⟨k.val + 1, Nat.succ_lt_succ h⟩ else 0 := by
    intro k
    by_cases h : k.val < Q
    · rw [dif_pos h]
      have hB : ∀ s₂ : Occupation m k.val,
          B.mulVec y ⟨k, s₂⟩ =
            (∑ i, star (u i) • annihilate m k.val i).mulVec
              (fun t₂ => y ⟨⟨k.val + 1, Nat.succ_lt_succ h⟩, t₂⟩) s₂ := by
        intro s₂
        simp only [B, Matrix.sum_mulVec, Finset.sum_apply, Matrix.smul_mulVec,
          Pi.smul_apply, cutCreate_conjTranspose_mulVec_apply, dif_pos h]
      simp only [hB]
      have hsq := weighted_annihilate_mulVec_sq m k.val u
        (fun t₂ => y ⟨⟨k.val + 1, Nat.succ_lt_succ h⟩, t₂⟩)
      have hkQ : (k.val + 1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
      have hg_pos : 0 ≤ g ⟨k.val + 1, Nat.succ_lt_succ h⟩ := hg_nonneg _
      exact hsq.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hkQ hU) hg_pos)
    · rw [dif_neg h]
      have hB0 : ∀ s₂ : Occupation m k.val, B.mulVec y ⟨k, s₂⟩ = 0 := by
        intro s₂
        simp [B, Matrix.sum_mulVec, Finset.sum_apply, Matrix.smul_mulVec,
          cutCreate_conjTranspose_mulVec_apply, dif_neg h]
      simp [hB0]
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  calc ∑ k : Fin (Q + 1), ∑ s₂ : Occupation m k.val, ‖B.mulVec y ⟨k, s₂⟩‖ ^ 2
      ≤ ∑ k : Fin (Q + 1),
          (if h : k.val < Q then (Q : ℝ) * U * g ⟨k.val + 1, Nat.succ_lt_succ h⟩ else 0) :=
        Finset.sum_le_sum fun k _ => hsector k
    _ = ∑ j : Fin Q, (Q : ℝ) * U * g (Fin.succ j) := by
        rw [Fin.sum_univ_castSucc]
        have hlast : ¬ ((Fin.last Q).val < Q) := Nat.lt_irrefl Q
        rw [dif_neg hlast, add_zero]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hj : (Fin.castSucc j).val < Q := j.isLt
        rw [dif_pos hj]
        rfl
    _ ≤ (Q : ℝ) * U * ∑ k' : Fin (Q + 1), g k' := by
        rw [Fin.sum_univ_succ, mul_add]
        have h0 : 0 ≤ (Q : ℝ) * U * g 0 := mul_nonneg (by positivity) (hg_nonneg 0)
        rw [← Finset.mul_sum]
        linarith

/-- The sum of squared magnitudes of a single-mode indicator vector is one. -/
private theorem single_normSq_sum {m : ℕ} (i : Fin m) :
    ∑ j : Fin m, Complex.normSq ((fun k : Fin m => if k = i then (1 : ℂ) else 0) j) = 1 := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro hm; exact absurd (Finset.mem_univ _) hm

/-- Each cutoff creation matrix has operator norm at most `sqrt Q`. -/
private theorem cutCreate_norm_le {m Q : ℕ} (i : Fin m) :
    ‖cutCreate m Q i‖ ≤ Real.sqrt Q := by
  have h := weighted_cutCreate_norm_le m Q (fun k : Fin m => if k = i then (1 : ℂ) else 0)
  have hsum : (∑ j : Fin m, (fun k : Fin m => if k = i then (1 : ℂ) else 0) j • cutCreate m Q j) = cutCreate m Q i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  rw [hsum, single_normSq_sum i, Real.sqrt_one, mul_one] at h
  exact h

/-- A word of cutoff creation and annihilation matrices has norm at most `sqrt Q` raised to the
word length. -/
private theorem cutWord_norm_le (m Q : ℕ) (w : List (Fin m × Bool)) :
    ‖cutWord m Q w‖ ≤ (Real.sqrt Q) ^ w.length := by
  induction w with
  | nil =>
    simp only [cutWord, List.foldr_nil, List.length_nil, pow_zero]
    refine l2_opNorm_le_of_mulVec_sq 1 1 zero_le_one fun x => ?_
    simp [Matrix.one_mulVec]
  | cons a w ih =>
    simp only [cutWord, List.foldr_cons, List.length_cons, pow_succ']
    let M : Matrix (CutBasis m Q) (CutBasis m Q) ℂ :=
      if a.2 then cutCreate m Q a.1 else (cutCreate m Q a.1).conjTranspose
    have hM : ‖M‖ ≤ Real.sqrt Q := by
      dsimp [M]
      split_ifs
      · exact cutCreate_norm_le a.1
      · rw [Matrix.l2_opNorm_conjTranspose]
        exact cutCreate_norm_le a.1
    calc ‖M * cutWord m Q w‖
        ≤ ‖M‖ * ‖cutWord m Q w‖ := Matrix.l2_opNorm_mul M (cutWord m Q w)
      _ ≤ Real.sqrt Q * (Real.sqrt Q) ^ w.length := by
          gcongr

/-- Creation and annihilation satisfy sector norm bounds, and weighted creation satisfies the
corresponding cutoff bound. A finite polynomial in cutoff ladder matrices is bounded by the
sum of coefficient norms times the word-length powers of `sqrt Q`. -/
theorem sector_and_polynomial_norm_bounds :
    (∀ (m n : ℕ) (i : Fin m),
      ‖create m n i‖ ≤ Real.sqrt (n+1) ∧ ‖annihilate m n i‖ ≤ Real.sqrt (n+1)) ∧
    (∀ (m n : ℕ) (u : Fin m → ℂ),
      ‖∑ i, u i • create m n i‖ ≤ Real.sqrt (n+1) * Real.sqrt (∑ i, Complex.normSq (u i)) ∧
      ‖∑ i, star (u i) • annihilate m n i‖ ≤
        Real.sqrt (n+1) * Real.sqrt (∑ i, Complex.normSq (u i))) ∧
    (∀ (m Q : ℕ) (u : Fin m → ℂ),
      ‖∑ i, u i • cutCreate m Q i‖ ≤ Real.sqrt Q * Real.sqrt (∑ i, Complex.normSq (u i))) ∧
    (∀ (m Q : ℕ) (terms : List (ℂ × List (Fin m × Bool))),
      ‖(terms.map (fun t => t.1 • cutWord m Q t.2)).sum‖ ≤
        (terms.map (fun t => ‖t.1‖ * (Real.sqrt Q)^t.2.length)).sum) := by
  refine ⟨?_, fun m n u => ⟨weighted_create_norm_le m n u, weighted_annihilate_norm_le m n u⟩,
    weighted_cutCreate_norm_le, ?_⟩
  · intro m n i
    have hc : ‖create m n i‖ ≤ Real.sqrt (n + 1) := by
      have h := weighted_create_norm_le m n (fun k : Fin m => if k = i then (1 : ℂ) else 0)
      have hsum : (∑ j : Fin m, (fun k : Fin m => if k = i then (1 : ℂ) else 0) j • create m n j) = create m n i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj; simp [hj]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      rw [hsum, single_normSq_sum i, Real.sqrt_one, mul_one] at h
      exact h
    refine ⟨hc, ?_⟩
    unfold annihilate
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hc
  · intro m Q terms
    induction terms with
    | nil => simp
    | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons]
      calc ‖t.1 • cutWord m Q t.2 + (ts.map (fun x => x.1 • cutWord m Q x.2)).sum‖
          ≤ ‖t.1 • cutWord m Q t.2‖ + ‖(ts.map (fun x => x.1 • cutWord m Q x.2)).sum‖ :=
            norm_add_le _ _
        _ ≤ ‖t.1‖ * (Real.sqrt Q) ^ t.2.length +
              (ts.map (fun x => ‖x.1‖ * (Real.sqrt Q) ^ x.2.length)).sum := by
            rw [norm_smul]
            gcongr
            exact cutWord_norm_le m Q t.2

/-- The mode-count function of an assignment of particle positions to modes. -/
private def occFn {m n : ℕ} (f : Fin n → Fin m) : Fin m → ℕ :=
  fun i => ∑ j : Fin n, if f j = i then 1 else 0

/-- Permuting particle positions preserves their mode-count function. -/
private theorem occFn_comp_perm {m n : ℕ} (f : Fin n → Fin m) (σ : Equiv.Perm (Fin n)) :
    occFn (fun j => f (σ j)) = occFn f := by
  funext i
  simp only [occFn]
  exact Fintype.sum_equiv σ (fun j => if f (σ j) = i then (1 : ℕ) else 0)
    (fun j => if f j = i then (1 : ℕ) else 0) (fun _ => rfl)

/-- The total count of a mode assignment equals the number of particle positions. -/
private theorem occFn_sum {m n : ℕ} (f : Fin n → Fin m) : ∑ i, occFn f i = n := by
  have hcomm : ∑ i : Fin m, ∑ j : Fin n, (if f j = i then (1 : ℕ) else 0)
      = ∑ j : Fin n, ∑ i : Fin m, (if f j = i then (1 : ℕ) else 0) :=
    Finset.sum_comm (f := fun i j => if f j = i then (1 : ℕ) else 0)
  have hinner : ∀ j : Fin n, ∑ i : Fin m, (if f j = i then (1 : ℕ) else 0) = 1 := by
    intro j
    simp
  simp only [occFn]
  rw [hcomm]
  simp [hinner]

/-- Each mode count is at most the number of particle positions. -/
private theorem occFn_le {m n : ℕ} (f : Fin n → Fin m) (i : Fin m) : occFn f i ≤ n := by
  have hle : occFn f i ≤ ∑ i', occFn f i' :=
    Finset.single_le_sum (fun i' _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [occFn_sum] at hle
  exact hle

/-- The occupation associated with the mode counts of a particle assignment. -/
private def occOf {m n : ℕ} (f : Fin n → Fin m) : Occupation m n :=
  ⟨fun i => ⟨occFn f i, by have := occFn_le f i; omega⟩, occFn_sum f⟩

/-- The count of mode `i` in the occupation of an assignment is `occFn f i`. -/
@[simp]
private theorem occOf_val {m n : ℕ} (f : Fin n → Fin m) (i : Fin m) :
    ((occOf f).val i : ℕ) = occFn f i := rfl

/-- An assignment has occupation `s` exactly when its mode-count function equals the counts of
`s`. -/
private theorem occOf_eq_iff {m n : ℕ} (f : Fin n → Fin m) (s : Occupation m n) :
    occOf f = s ↔ occFn f = fun i => (s.val i : ℕ) := by
  constructor
  · rintro rfl; rfl
  · intro h; ext i; exact congrFun h i

/-- Pointwise equivalent predicates define finite subtypes of equal cardinality. -/
private theorem card_subtype_iff {α : Type*} (p q : α → Prop)
    [Fintype { x // p x }] [Fintype { x // q x }] (h : ∀ a, p a ↔ q a) :
    Fintype.card { x // p x } = Fintype.card { x // q x } := by
  exact Fintype.card_congr
    (Equiv.ofBijective (fun x : { x // p x } => (⟨(x : α), (h _).1 x.2⟩ : { x // q x }))
      ⟨fun x y hxy => Subtype.ext (by simpa using hxy),
        fun y => ⟨⟨(y : α), (h _).2 y.2⟩, Subtype.ext (by simp)⟩⟩)

/-- The fiber of a mode assignment at `i` has cardinality `occFn f i`. -/
private theorem card_fiber_subtype {m n : ℕ} (f : Fin n → Fin m) (i : Fin m) :
    Fintype.card { j : Fin n // f j = i } = occFn f i := by
  rw [Fintype.card_subtype, Finset.card_filter]
  rfl

/-- Given an equivalence between two finite types, the number of equivalences between them
equals the number of permutations of the source. -/
private theorem card_perm_equiv_perm {α β : Type*} [Fintype α] [Fintype β]
    [Fintype (α ≃ β)] [Fintype (Equiv.Perm α)] (e : α ≃ β) :
    Fintype.card (α ≃ β) = Fintype.card (Equiv.Perm α) := by
  exact Fintype.card_congr
    { toFun := fun f1 => f1.trans e.symm
      invFun := fun f2 => f2.trans e
      left_inv := fun f1 => Equiv.ext fun a => by simp
      right_inv := fun f2 => Equiv.ext fun a => by simp }

/-- Assignments with equal mode counts are related by a number of position permutations equal to
the product of the count factorials. -/
private theorem perm_fiber_card {m n : ℕ} (f g : Fin n → Fin m) (h : occFn f = occFn g) :
    Fintype.card { τ : Equiv.Perm (Fin n) // ∀ j, f (τ j) = g j } = ∏ i, (occFn f i).factorial := by
  have hkey : ∀ (π : ∀ i : Fin m, ({j : Fin n // g j = i} ≃ {j : Fin n // f j = i}))
      (a : Fin n), Equiv.ofFiberEquiv π a
      = ((π (g a)) (⟨a, rfl⟩ : {j : Fin n // g j = g a}) : Fin n) := by
    intro π a; simp; rfl
  have hinj : ∀ π π' : ∀ i : Fin m, ({j : Fin n // g j = i} ≃ {j : Fin n // f j = i}),
      Equiv.ofFiberEquiv π = Equiv.ofFiberEquiv π' → π = π' := by
    intro π π' heq
    funext i
    ext x
    have htr : ∀ (πx : ∀ i : Fin m, ({j : Fin n // g j = i} ≃ {j : Fin n // f j = i})),
        ((πx i) x : Fin n)
          = ((πx (g (x : Fin n))) (⟨(x : Fin n), rfl⟩ :
              {j : Fin n // g j = g (x : Fin n)}) : Fin n) := by
      intro πx
      cases x with
      | mk a ha => subst ha; rfl
    rw [htr π, htr π', ← hkey π (x : Fin n), ← hkey π' (x : Fin n)]
    exact congrArg (fun z : Fin n => (z : ℕ)) (Equiv.ext_iff.mp heq (x : Fin n))
  have hsurj : ∀ τ : { τ : Equiv.Perm (Fin n) // ∀ j, f (τ j) = g j },
      ∃ π : ∀ i : Fin m, ({j : Fin n // g j = i} ≃ {j : Fin n // f j = i}),
        Equiv.ofFiberEquiv π = (τ : Equiv.Perm (Fin n)) := by
    intro τ
    let hblock : ∀ i : Fin m, ({j : Fin n // g j = i} ≃ {j : Fin n // f j = i}) := fun i =>
      Equiv.ofBijective
        (fun x : {j : Fin n // g j = i} =>
          (⟨(τ : Equiv.Perm (Fin n)) (x : Fin n), by
            have h1 := τ.2 (x : Fin n)
            rw [x.2] at h1
            exact h1⟩ : {j : Fin n // f j = i}))
        ⟨fun x y hxy =>
            Subtype.ext ((τ : Equiv.Perm (Fin n)).injective (by simpa using hxy)),
          fun y =>
            ⟨(⟨(τ : Equiv.Perm (Fin n)).symm (y : Fin n), by
                have h2 := τ.2 ((τ : Equiv.Perm (Fin n)).symm (y : Fin n))
                rw [Equiv.apply_symm_apply] at h2
                exact h2.symm.trans y.2⟩ : {j : Fin n // g j = i}),
              Subtype.ext (Equiv.apply_symm_apply _ _)⟩⟩
    refine ⟨hblock, Equiv.ext fun a => ?_⟩
    show (Equiv.ofFiberEquiv hblock) a = ((τ : Equiv.Perm (Fin n)) a : Fin n)
    rw [hkey hblock a]
    rfl
  have hbij : (∀ i : Fin m, {j : Fin n // g j = i} ≃ {j : Fin n // f j = i}) ≃
      { τ : Equiv.Perm (Fin n) // ∀ j, f (τ j) = g j } :=
    Equiv.ofBijective
      (fun π => ⟨Equiv.ofFiberEquiv π, fun j => Equiv.ofFiberEquiv_map π j⟩)
      ⟨fun π π' hpp => hinj π π' (congrArg Subtype.val hpp),
        fun τ => let ⟨π, hπ⟩ := hsurj τ; ⟨π, Subtype.ext hπ⟩⟩
  rw [Fintype.card_congr hbij.symm, Fintype.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hce : Fintype.card {j : Fin n // g j = i} = Fintype.card {j : Fin n // f j = i} := by
    rw [card_fiber_subtype, card_fiber_subtype, ← h]
  have e₀ : {j : Fin n // g j = i} ≃ {j : Fin n // f j = i} := Fintype.equivOfCardEq hce
  rw [card_perm_equiv_perm e₀, Fintype.card_perm, card_fiber_subtype g i, ← h]

/-- The number of permutations taking one mode assignment to another is the product of
occupation factorials when counts agree, and zero otherwise. -/
private theorem card_perm_fiber {m n : ℕ} (f g : Fin n → Fin m) :
    Fintype.card { τ : Equiv.Perm (Fin n) // ∀ j, f (τ j) = g j }
      = if occFn f = occFn g then ∏ i, (occFn f i).factorial else 0 := by
  by_cases h : occFn f = occFn g
  · rw [if_pos h, perm_fiber_card f g h]
  · rw [if_neg h, Fintype.card_eq_zero_iff]
    refine ⟨fun τ => h ?_⟩
    have h2 : (fun j => f ((τ : Equiv.Perm (Fin n)) j)) = g := funext fun j => τ.2 j
    exact (occFn_comp_perm f (τ : Equiv.Perm (Fin n))).symm.trans (by rw [h2])

/-- Summing a function over permutations of an assignment equals the occupation factorial
product times the sum over assignments with the same counts. -/
private theorem sum_perm_comp {m n : ℕ} (f₀ : Fin n → Fin m) (Φ : (Fin n → Fin m) → ℂ) :
    ∑ σ : Equiv.Perm (Fin n), Φ (fun j => f₀ (σ j))
      = ((∏ i, (occFn f₀ i).factorial : ℕ) : ℂ) * ∑ g : Fin n → Fin m,
          (if occFn g = occFn f₀ then (1 : ℂ) else 0) * Φ g := by
  have hphi : ∀ (F : Fin n → Fin m) (σ : Equiv.Perm (Fin n)),
      (fun j => f₀ (σ j)) = F → Φ (fun j => f₀ (σ j)) = Φ F := by
    intro F σ h; rw [h]
  rw [← Finset.sum_fiberwise_of_maps_to
      (t := (Finset.univ : Finset (Fin n → Fin m)))
      (g := fun σ : Equiv.Perm (Fin n) => fun j => f₀ (σ j))
      (fun σ _ => Finset.mem_univ _)
      (f := fun σ : Equiv.Perm (Fin n) => Φ (fun j => f₀ (σ j)))]
  have hterm : ∀ F : Fin n → Fin m,
      (∑ σ ∈ (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (fun j => f₀ (σ j)) = F)), Φ (fun j => f₀ (σ j)))
        = ((if occFn F = occFn f₀ then (1 : ℂ) else 0) * Φ F) *
          ((∏ i, (occFn f₀ i).factorial : ℕ) : ℂ) := by
    intro F
    have hone : (∑ σ ∈ (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (fun j => f₀ (σ j)) = F)), Φ F)
        = (∑ σ ∈ (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (fun j => f₀ (σ j)) = F)), (1 : ℂ)) * Φ F := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun σ _ => (one_mul _).symm
    have hone2 : (∑ σ ∈ (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (fun j => f₀ (σ j)) = F)), (1 : ℂ))
        = (Fintype.card { τ : Equiv.Perm (Fin n) // (fun j => f₀ (τ j)) = F } : ℂ) := by
      rw [Finset.sum_const, Nat.smul_one_eq_cast, Fintype.card_subtype]
    rw [Finset.sum_congr rfl
        (fun σ hσ => hphi F σ (by simpa [Finset.mem_filter] using hσ)),
      hone, hone2,
      card_subtype_iff (fun τ : Equiv.Perm (Fin n) => (fun j => f₀ (τ j)) = F)
        (fun τ : Equiv.Perm (Fin n) => ∀ j, f₀ (τ j) = F j)
        (fun τ => funext_iff),
      card_perm_fiber f₀ F]
    by_cases h : occFn f₀ = occFn F
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [if_neg h, if_neg (fun hc => h hc.symm), Nat.cast_zero, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl (fun F _ => hterm F), ← Finset.sum_mul]
  exact mul_comm _ _

/-- The sum of the occurrence indicator over list positions equals the list count. -/
private theorem sum_get_count {α : Type*} [DecidableEq α] (L : List α) (a : α) :
    ∑ p : Fin L.length, (if L.get p = a then (1 : ℕ) else 0) = L.count a := by
  induction L with
  | nil => simp
  | cons x t ih =>
      show (∑ p : Fin (t.length + 1), (if (x :: t).get p = a then (1 : ℕ) else 0))
        = List.count a (x :: t)
      rw [Fin.sum_univ_succ]
      have e0 : (if (x :: t).get 0 = a then (1 : ℕ) else 0)
          = (if x = a then (1 : ℕ) else 0) := rfl
      have es : ∀ p : Fin t.length,
          (if (x :: t).get (Fin.succ p) = a then (1 : ℕ) else 0)
            = (if t.get p = a then (1 : ℕ) else 0) := fun p => rfl
      rw [e0, Finset.sum_congr rfl (fun p _ => es p), ih, List.count_cons]
      by_cases hxa : x = a
      · subst hxa; simp [Nat.add_comm]
      · simp [hxa]

/-- The repeated mode list contains mode `i₀` exactly `s i₀` times. -/
private theorem count_bosonRows {m : ℕ} (s : Fin m → ℕ) (i₀ : Fin m) :
    (bosonRows s).count i₀ = s i₀ := by
  induction m with
  | zero => exact absurd i₀.isLt (Nat.not_lt_zero _)
  | succ m ih =>
      have hsplit : bosonRows s = List.replicate (s 0) (0 : Fin (m + 1))
          ++ List.map (Fin.succ : Fin m → Fin (m + 1))
              (bosonRows (fun j : Fin m => s ((Fin.succ : Fin m → Fin (m + 1)) j))) := by
        have hfun1 : (fun j : Fin m =>
              List.replicate (s ((Fin.succ : Fin m → Fin (m + 1)) j))
                ((Fin.succ : Fin m → Fin (m + 1)) j))
            = (fun j : Fin m => List.map (Fin.succ : Fin m → Fin (m + 1))
                (List.replicate (s ((Fin.succ : Fin m → Fin (m + 1)) j)) j)) :=
          funext fun j => List.map_replicate.symm
        rw [bosonRows, List.finRange_succ, List.flatMap_cons, List.flatMap_map, hfun1,
          ← List.map_flatMap,
          show (List.finRange m).flatMap
              (fun j : Fin m => List.replicate (s ((Fin.succ : Fin m → Fin (m + 1)) j)) j)
            = bosonRows (fun j : Fin m => s ((Fin.succ : Fin m → Fin (m + 1)) j)) from rfl]
      rw [hsplit, List.count_append]
      rcases Fin.eq_zero_or_eq_succ i₀ with rfl | ⟨j, rfl⟩
      · have h0 : (List.map (Fin.succ : Fin m → Fin (m + 1))
            (bosonRows (fun j : Fin m => s ((Fin.succ : Fin m → Fin (m + 1)) j)))).count
            (0 : Fin (m + 1)) = 0 :=
          List.count_eq_zero_of_not_mem (fun hmem => by
            rcases List.mem_map.mp hmem with ⟨p, _, hp⟩
            exact Fin.succ_ne_zero p hp)
        rw [List.count_replicate_self, h0, Nat.add_zero]
      · rw [List.count_map_of_injective _ (Fin.succ : Fin m → Fin (m + 1))
          (Fin.succ_injective _) j]
        have hne : (List.replicate (s 0) (0 : Fin (m + 1))).count
            ((Fin.succ : Fin m → Fin (m + 1)) j) = 0 := by
          refine List.count_eq_zero_of_not_mem (fun hmem => ?_)
          rw [List.mem_replicate] at hmem
          exact Fin.succ_ne_zero j hmem.2
        rw [hne, Nat.zero_add, ih (fun j : Fin m => s ((Fin.succ : Fin m → Fin (m + 1)) j))]

/-- The mode counts of `rowAt s` equal the counts of occupation `s`. -/
private theorem occFn_rowAt {m n : ℕ} (s : Occupation m n) :
    occFn (rowAt s) = fun i => (s.val i : ℕ) := by
  funext i
  let L := bosonRows (fun k => (s.val k : ℕ))
  have hlen : L.length = n := (bosonRows_length (fun k => (s.val k : ℕ))).trans s.property
  simp only [occFn, rowAt]
  have heq : (∑ a : Fin n, if L.get ⟨a.val, by rw [hlen]; exact a.isLt⟩ = i then (1 : ℕ) else 0) =
      ∑ q : Fin L.length, if L.get q = i then (1 : ℕ) else 0 :=
    Fintype.sum_equiv (finCongr hlen.symm)
      (fun a : Fin n => if L.get ⟨a.val, by rw [hlen]; exact a.isLt⟩ = i then (1 : ℕ) else 0)
      (fun q : Fin L.length => if L.get q = i then (1 : ℕ) else 0)
      (fun _ => rfl)
  exact heq.trans ((sum_get_count L i).trans (count_bosonRows (fun k => (s.val k : ℕ)) i))

/-- Converting the repeated mode list of `s` back to an occupation recovers `s`. -/
@[simp]
private theorem occOf_rowAt {m n : ℕ} (s : Occupation m n) :
    occOf (rowAt s) = s := by
  rw [occOf_eq_iff, occFn_rowAt]

/-- Any assignment with occupation `s` is a permutation of the repeated mode list of `s`. -/
private theorem exists_perm_rowAt {m n : ℕ} (s : Occupation m n) (f : Fin n → Fin m)
    (hf : occOf f = s) : ∃ τ : Equiv.Perm (Fin n), ∀ b, rowAt s (τ b) = f b := by
  have hf' : occFn (rowAt s) = occFn f := by
    rw [occFn_rowAt, ← (occOf_eq_iff f s).mp hf]
  have hpos : 0 < Fintype.card { τ : Equiv.Perm (Fin n) // ∀ j, rowAt s (τ j) = f j } := by
    rw [perm_fiber_card (rowAt s) f hf']
    exact Finset.prod_pos fun i _ => Nat.factorial_pos _
  rcases Fintype.card_pos_iff.mp hpos with ⟨τ, hτ⟩
  exact ⟨τ, hτ⟩

/-- Replacing the column mode list by any assignment with the same occupation preserves the
associated permanent sum. -/
private theorem perm_col_replace {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (r s : Occupation m n) (f : Fin n → Fin m) (hf : occOf f = s) :
    (∑ σ : Equiv.Perm (Fin n), ∏ b : Fin n, U (rowAt r (σ b)) (f b)) =
      Matrix.permanent (occupationMatrix U r s) := by
  rcases exists_perm_rowAt s f hf with ⟨τ, hτ⟩
  have hprod : ∀ σ : Equiv.Perm (Fin n),
      (∏ b : Fin n, U (rowAt r (σ b)) (f b)) =
        ∏ b : Fin n, U (rowAt r ((σ * τ.symm) b)) (rowAt s b) := by
    intro σ
    simp only [← hτ]
    exact Fintype.prod_equiv τ
      (fun b => U (rowAt r (σ b)) (rowAt s (τ b)))
      (fun b => U (rowAt r ((σ * τ.symm) b)) (rowAt s b))
      (fun b => by simp)
  simp only [hprod, Matrix.permanent, occupationMatrix]
  exact Fintype.sum_equiv (Equiv.mulRight τ.symm)
    (fun σ => ∏ b : Fin n, U (rowAt r ((σ * τ.symm) b)) (rowAt s b))
    (fun σ => ∏ b : Fin n, U (rowAt r (σ b)) (rowAt s b))
    (fun _ => rfl)

/-- The permanent of an occupation matrix is the row occupation factorial product times the sum
over assignments with that row occupation. -/
private theorem permanent_occupationMatrix_row_sum {m n : ℕ}
    (U : Matrix (Fin m) (Fin m) ℂ) (r s : Occupation m n) :
    Matrix.permanent (occupationMatrix U r s) =
      ((∏ i, (r.val i : ℕ).factorial : ℕ) : ℂ) *
        ∑ g : Fin n → Fin m, (if occOf g = r then (1 : ℂ) else 0) *
          ∏ b : Fin n, U (g b) (rowAt s b) := by
  have h1 := sum_perm_comp (rowAt r) (fun g => ∏ b : Fin n, U (g b) (rowAt s b))
  rw [occFn_rowAt] at h1
  simp only [← occOf_eq_iff] at h1
  exact h1

/-- The real product of the factorials of all mode occupations. -/
private def factProd {m n : ℕ} (s : Occupation m n) : ℝ :=
  ∏ i : Fin m, ((s.val i : ℕ).factorial : ℝ)

/-- The occupation factorial product is strictly positive. -/
private theorem factProd_pos {m n : ℕ} (s : Occupation m n) : 0 < factProd s :=
  Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos (s.val i : ℕ)

/-- The occupation factorial product is nonnegative. -/
private theorem factProd_nonneg {m n : ℕ} (s : Occupation m n) : 0 ≤ factProd s :=
  le_of_lt (factProd_pos s)

/-- Casting the natural occupation factorial product to the reals gives `factProd`. -/
private theorem factProd_cast {m n : ℕ} (s : Occupation m n) :
    (((∏ i : Fin m, (s.val i : ℕ).factorial : ℕ) : ℝ)) = factProd s := by
  unfold factProd
  push_cast
  rfl

/-- An entry of `gamma` is the occupation permanent divided by the separate square roots of the
row and column factorial products. -/
private theorem gamma_apply_factProd {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (r s : Occupation m n) :
    gamma m n U r s =
      Matrix.permanent (occupationMatrix U r s) /
        ((Real.sqrt (factProd r) : ℂ) * (Real.sqrt (factProd s) : ℂ)) := by
  unfold gamma
  rw [factProd_cast, factProd_cast, Real.sqrt_mul (factProd_nonneg r), Complex.ofReal_mul]

/-- Second quantization of the identity mode matrix is the identity on each particle sector. -/
private theorem gamma_one (m n : ℕ) :
    gamma m n (1 : Matrix (Fin m) (Fin m) ℂ) = 1 := by
  ext r s
  rw [gamma_apply_factProd, permanent_occupationMatrix_row_sum, Matrix.one_apply]
  have hprod : ∀ g : Fin n → Fin m,
      (∏ b : Fin n, (1 : Matrix (Fin m) (Fin m) ℂ) (g b) (rowAt s b)) =
        if g = rowAt s then 1 else 0 := by
    intro g
    by_cases hgs : g = rowAt s
    · subst hgs
      simp
    · rw [if_neg hgs]
      have hne : ∃ b : Fin n, g b ≠ rowAt s b := by
        by_contra hc
        apply hgs
        funext b
        by_contra hgb
        exact hc ⟨b, hgb⟩
      rcases hne with ⟨b₀, hb₀⟩
      refine Finset.prod_eq_zero (Finset.mem_univ b₀) ?_
      simp [hb₀]
  simp only [hprod]
  rw [Finset.sum_eq_single (rowAt s)]
  · rw [if_pos rfl, mul_one, occOf_rowAt]
    by_cases hrs : r = s
    · subst hrs
      simp only [ite_true, mul_one]
      have hsq : ((Real.sqrt (factProd r) : ℂ) * (Real.sqrt (factProd r) : ℂ)) =
          ((∏ i, (r.val i : ℕ).factorial : ℕ) : ℂ) := by
        norm_cast
        rw [Real.mul_self_sqrt (factProd_nonneg r), ← factProd_cast]
      rw [hsq, div_self]
      exact_mod_cast ne_of_gt (Finset.prod_pos fun i _ => Nat.factorial_pos _)
    · have hsr : s ≠ r := fun h => hrs h.symm
      rw [if_neg hsr, if_neg hrs, mul_zero, zero_div]
  · intro g _ hg
    rw [if_neg hg, mul_zero]
  · intro hm; exact absurd (Finset.mem_univ _) hm

/-- The permanent of a conjugate transpose is the complex conjugate of the permanent. -/
private theorem permanent_conjTranspose {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.permanent M.conjTranspose = star (Matrix.permanent M) := by
  rw [← Matrix.permanent_transpose]
  simp only [Matrix.permanent, Matrix.transpose_apply, Matrix.conjTranspose_apply,
    star_sum, star_prod]

/-- The permanent construction `gamma` commutes with conjugate transpose. -/
private theorem gamma_conjTranspose (m n : ℕ) (U : Matrix (Fin m) (Fin m) ℂ) :
    gamma m n U.conjTranspose = (gamma m n U).conjTranspose := by
  ext r s
  rw [Matrix.conjTranspose_apply, gamma_apply_factProd, gamma_apply_factProd]
  have hocc : occupationMatrix U.conjTranspose r s = (occupationMatrix U s r).conjTranspose := by
    ext a b
    rfl
  rw [hocc, permanent_conjTranspose, star_div₀, star_mul',
    Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal]
  ring

/-- The permanent construction `gamma` preserves multiplication of mode matrices. -/
private theorem gamma_mul (m n : ℕ) (U V : Matrix (Fin m) (Fin m) ℂ) :
    gamma m n (U * V) = gamma m n U * gamma m n V := by
  ext r t
  rw [Matrix.mul_apply, gamma_apply_factProd]
  have hterm : ∀ s : Occupation m n,
      gamma m n U r s * gamma m n V s t =
        (∑ h : Fin n → Fin m,
          if occOf h = s then
            (∑ σ : Equiv.Perm (Fin n), ∏ b : Fin n, U (rowAt r (σ b)) (h b)) *
              (∏ b : Fin n, V (h b) (rowAt t b))
          else 0) /
          ((Real.sqrt (factProd r) : ℂ) * (Real.sqrt (factProd t) : ℂ)) := by
    intro s
    rw [gamma_apply_factProd, gamma_apply_factProd, permanent_occupationMatrix_row_sum V s t]
    have hFs_sq : ((Real.sqrt (factProd s) : ℂ) * (Real.sqrt (factProd s) : ℂ)) =
        ((∏ i, (s.val i : ℕ).factorial : ℕ) : ℂ) := by
      norm_cast
      rw [Real.mul_self_sqrt (factProd_nonneg s), ← factProd_cast]
    have hFs_ne : (Real.sqrt (factProd s) : ℂ) ≠ 0 := by
      exact_mod_cast Real.sqrt_ne_zero'.mpr (factProd_pos s)
    have hsum_eq :
        Matrix.permanent (occupationMatrix U r s) *
          ∑ h : Fin n → Fin m, (if occOf h = s then (1 : ℂ) else 0) *
            ∏ b : Fin n, V (h b) (rowAt t b) =
        ∑ h : Fin n → Fin m,
          if occOf h = s then
            (∑ σ : Equiv.Perm (Fin n), ∏ b : Fin n, U (rowAt r (σ b)) (h b)) *
              (∏ b : Fin n, V (h b) (rowAt t b))
          else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      by_cases hhs : occOf h = s
      · rw [if_pos hhs, if_pos hhs, one_mul, perm_col_replace U r s h hhs]
      · rw [if_neg hhs, if_neg hhs, zero_mul, mul_zero]
    rw [← hFs_sq, ← hsum_eq]
    generalize Matrix.permanent (occupationMatrix U r s) = P
    generalize (∑ h : Fin n → Fin m, (if occOf h = s then (1 : ℂ) else 0) *
      ∏ b : Fin n, V (h b) (rowAt t b)) = S
    generalize (Real.sqrt (factProd r) : ℂ) = R
    generalize (Real.sqrt (factProd t) : ℂ) = T
    have h1 : P / (R * (Real.sqrt (factProd s) : ℂ)) *
        (((Real.sqrt (factProd s) : ℂ) * (Real.sqrt (factProd s) : ℂ)) * S /
          ((Real.sqrt (factProd s) : ℂ) * T)) =
        (P * S * ((Real.sqrt (factProd s) : ℂ) * (Real.sqrt (factProd s) : ℂ))) /
          ((R * T) * ((Real.sqrt (factProd s) : ℂ) * (Real.sqrt (factProd s) : ℂ))) := by
      ring
    rw [h1, mul_div_mul_right _ _ (mul_ne_zero hFs_ne hFs_ne)]
  simp only [hterm, ← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  have hsingle : ∀ h : Fin n → Fin m,
      (∑ s : Occupation m n,
        if occOf h = s then
          (∑ σ : Equiv.Perm (Fin n), ∏ b : Fin n, U (rowAt r (σ b)) (h b)) *
            (∏ b : Fin n, V (h b) (rowAt t b))
        else 0) =
      ∑ σ : Equiv.Perm (Fin n),
        ∏ b : Fin n, (U (rowAt r (σ b)) (h b) * V (h b) (rowAt t b)) := by
    intro h
    rw [Fintype.sum_ite_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← Finset.prod_mul_distrib]
  simp only [hsingle]
  rw [Finset.sum_comm, Matrix.permanent]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [occupationMatrix, Matrix.mul_apply]
  exact Fintype.prod_sum (fun b k => U (rowAt r (σ b)) k * V k (rowAt t b))

/-- Adding a particle in mode `j` multiplies the occupation factorial product by the new
occupation count in that mode. -/
private theorem factProd_bump {m n : ℕ} (u : Occupation m n) (j : Fin m) :
    factProd (bump u j) = ((u.val j : ℕ) + 1 : ℝ) * factProd u := by
  unfold factProd
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
    bump_val, if_pos rfl, Nat.factorial_succ]
  have hrest : (∏ k ∈ Finset.univ.erase j, (((bump u j).val k : ℕ).factorial : ℝ)) =
      ∏ k ∈ Finset.univ.erase j, ((u.val k : ℕ).factorial : ℝ) := by
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [bump_val, if_neg (Finset.ne_of_mem_erase hk), Nat.add_zero]
  rw [hrest]
  push_cast
  ring

/-- The mode assignment obtained by appending one mode label to an assignment. -/
private abbrev snocMode {m n : ℕ} (f : Fin n → Fin m) (i : Fin m) : Fin (n + 1) → Fin m :=
  Fin.snoc (α := fun _ => Fin m) f i

/-- Appending mode `j` to an assignment increments its occupation in mode `j`. -/
private theorem occOf_snocMode {m n : ℕ} (g₀ : Fin n → Fin m) (j : Fin m) :
    occOf (snocMode g₀ j) = bump (occOf g₀) j := by
  ext k
  simp only [occOf_val, bump_val, occFn, snocMode]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last, eq_comm]

/-- Second quantization intertwines creation in mode `i` with the linear combination of creation
operators weighted by column `i` of the mode matrix. -/
private theorem gamma_create (m n : ℕ) (U : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) :
    gamma m (n + 1) U * create m n i =
      (∑ j, U j i • create m n j) * gamma m n U := by
  ext r s
  have hR_ne : (Real.sqrt (factProd r) : ℂ) ≠ 0 :=
    by exact_mod_cast Real.sqrt_ne_zero'.mpr (factProd_pos r)
  have hS_ne : (Real.sqrt (factProd s) : ℂ) ≠ 0 :=
    by exact_mod_cast Real.sqrt_ne_zero'.mpr (factProd_pos s)
  have hsi_ne : (Real.sqrt ((s.val i : ℕ) + 1) : ℂ) ≠ 0 :=
    by exact_mod_cast Real.sqrt_ne_zero'.mpr (by positivity)
  have hLHS : (gamma m (n + 1) U * create m n i) r s =
      (((∏ k, (r.val k : ℕ).factorial : ℕ) : ℂ) *
        ∑ g : Fin (n + 1) → Fin m, (if occOf g = r then (1 : ℂ) else 0) *
          ∏ b : Fin (n + 1), U (g b) (snocMode (rowAt s) i b)) /
        ((Real.sqrt (factProd r) : ℂ) * (Real.sqrt (factProd s) : ℂ)) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (bump s i)]
    · rw [create_apply_bump, if_pos rfl, gamma_apply_factProd, factProd_bump s i,
        Real.sqrt_mul (by positivity), Complex.ofReal_mul]
      have hper : Matrix.permanent (occupationMatrix U r (bump s i)) =
          ((∏ k, (r.val k : ℕ).factorial : ℕ) : ℂ) *
            ∑ g : Fin (n + 1) → Fin m, (if occOf g = r then (1 : ℂ) else 0) *
              ∏ b : Fin (n + 1), U (g b) (snocMode (rowAt s) i b) := by
        have hsnoc : occOf (snocMode (rowAt s) i) = bump s i := by
          rw [occOf_snocMode, occOf_rowAt]
        rw [← perm_col_replace U r (bump s i) (snocMode (rowAt s) i) hsnoc]
        have h1 := sum_perm_comp (rowAt r)
          (fun g => ∏ b : Fin (n + 1), U (g b) (snocMode (rowAt s) i b))
        rw [occFn_rowAt] at h1
        simp only [← occOf_eq_iff] at h1
        exact h1
      rw [hper]
      generalize ((∏ k, (r.val k : ℕ).factorial : ℕ) : ℂ) *
        ∑ g : Fin (n + 1) → Fin m, (if occOf g = r then (1 : ℂ) else 0) *
          ∏ b : Fin (n + 1), U (g b) (snocMode (rowAt s) i b) = P
      have hdiv : P / ((Real.sqrt (factProd r) : ℂ) *
          ((Real.sqrt ((s.val i : ℕ) + 1) : ℂ) * (Real.sqrt (factProd s) : ℂ))) *
          (Real.sqrt ((s.val i : ℕ) + 1) : ℂ) =
          (P * (Real.sqrt ((s.val i : ℕ) + 1) : ℂ)) /
          (((Real.sqrt (factProd r) : ℂ) * (Real.sqrt (factProd s) : ℂ)) *
            (Real.sqrt ((s.val i : ℕ) + 1) : ℂ)) := by ring
      rw [hdiv, mul_div_mul_right _ _ hsi_ne]
    · intro t _ ht
      rw [create_apply_bump, if_neg ht, mul_zero]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  have hRHS_inner : ∀ (j : Fin m) (u : Occupation m n),
      create m n j r u * gamma m n U u s =
        (((∏ k, (r.val k : ℕ).factorial : ℕ) : ℂ) *
          ∑ g₀ : Fin n → Fin m,
            if occOf g₀ = u ∧ r = bump u j then
              ∏ a : Fin n, U (g₀ a) (rowAt s a)
            else 0) /
          ((Real.sqrt (factProd r) : ℂ) * (Real.sqrt (factProd s) : ℂ)) := by
    intro j u
    rw [create_apply_bump, gamma_apply_factProd, permanent_occupationMatrix_row_sum U u s]
    by_cases hru : r = bump u j
    · rw [if_pos hru]
      have hFr : factProd r = ((u.val j : ℕ) + 1 : ℝ) * factProd u := by
        rw [hru, factProd_bump]
      have hFu_sq : ((Real.sqrt (factProd u) : ℂ) * (Real.sqrt (factProd u) : ℂ)) =
          ((∏ k, (u.val k : ℕ).factorial : ℕ) : ℂ) := by
        norm_cast
        rw [Real.mul_self_sqrt (factProd_nonneg u), ← factProd_cast]
      have huj_sq : ((Real.sqrt ((u.val j : ℕ) + 1) : ℂ) * (Real.sqrt ((u.val j : ℕ) + 1) : ℂ)) =
          (((u.val j : ℕ) + 1 : ℝ) : ℂ) := by
        norm_cast
        rw [Real.mul_self_sqrt (by positivity)]
      have hFr_cast : ((∏ k, (r.val k : ℕ).factorial : ℕ) : ℂ) =
          (((u.val j : ℕ) + 1 : ℝ) : ℂ) * ((∏ k, (u.val k : ℕ).factorial : ℕ) : ℂ) := by
        have h1 : (factProd r : ℂ) = (((u.val j : ℕ) + 1 : ℝ) : ℂ) * (factProd u : ℂ) := by
          exact_mod_cast hFr
        rw [← factProd_cast, ← factProd_cast] at h1
        exact_mod_cast h1
      have hR_split : (Real.sqrt (factProd r) : ℂ) =
          (Real.sqrt ((u.val j : ℕ) + 1) : ℂ) * (Real.sqrt (factProd u) : ℂ) := by
        rw [hFr, Real.sqrt_mul (by positivity), Complex.ofReal_mul]
      have hFu_ne : (Real.sqrt (factProd u) : ℂ) ≠ 0 :=
        by exact_mod_cast Real.sqrt_ne_zero'.mpr (factProd_pos u)
      have huj_ne : (Real.sqrt ((u.val j : ℕ) + 1) : ℂ) ≠ 0 :=
        by exact_mod_cast Real.sqrt_ne_zero'.mpr (by positivity)
      have hsum_simp : (∑ g₀ : Fin n → Fin m, (if occOf g₀ = u then (1 : ℂ) else 0) *
            ∏ a : Fin n, U (g₀ a) (rowAt s a)) =
          ∑ g₀ : Fin n → Fin m,
            if occOf g₀ = u ∧ r = bump u j then
              ∏ a : Fin n, U (g₀ a) (rowAt s a)
            else 0 := by
        refine Finset.sum_congr rfl fun g₀ _ => ?_
        by_cases hg₀ : occOf g₀ = u <;> simp [hg₀, hru]
      rw [hsum_simp, hFr_cast, ← hFu_sq, ← huj_sq, hR_split]
      rw [← mul_div_assoc, ← mul_div_mul_left _ _ huj_ne]
      ring
    · rw [if_neg hru, zero_mul]
      have hzero : (∑ g₀ : Fin n → Fin m,
          if occOf g₀ = u ∧ r = bump u j then ∏ a : Fin n, U (g₀ a) (rowAt s a) else 0) = 0 := by
        refine Finset.sum_eq_zero fun g₀ _ => ?_
        simp [hru]
      rw [hzero, mul_zero, zero_div]
  rw [hLHS]
  have hRHS_expand : (((∑ j, U j i • create m n j) * gamma m n U) r s) =
      ∑ j : Fin m, U j i * ∑ u : Occupation m n, create m n j r u * gamma m n U u s := by
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  rw [hRHS_expand]
  simp only [hRHS_inner, ← Finset.sum_div, ← mul_div_assoc, ← Finset.mul_sum,
    mul_left_comm (U _ i)]
  congr 2
  have hcollapse : ∀ j : Fin m,
      U j i * (∑ u : Occupation m n, ∑ g₀ : Fin n → Fin m,
        if occOf g₀ = u ∧ r = bump u j then ∏ a : Fin n, U (g₀ a) (rowAt s a) else 0) =
      ∑ g₀ : Fin n → Fin m,
        (if bump (occOf g₀) j = r then (1 : ℂ) else 0) *
          (U j i * ∏ a : Fin n, U (g₀ a) (rowAt s a)) := by
    intro j
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g₀ _ => ?_
    rw [Finset.sum_eq_single (occOf g₀)]
    · by_cases hbr : r = bump (occOf g₀) j
      · rw [if_pos ⟨rfl, hbr⟩, if_pos hbr.symm, one_mul]
      · have hbr' : bump (occOf g₀) j ≠ r := fun h => hbr h.symm
        rw [if_neg (fun h => hbr h.2), if_neg hbr', zero_mul, mul_zero]
    · intro u _ hu
      rw [if_neg (fun h => hu h.1.symm)]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  rw [Finset.sum_congr rfl fun j _ => hcollapse j]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n + 1) => Fin m)).symm
    (fun g : Fin (n + 1) → Fin m =>
      (if occOf g = r then (1 : ℂ) else 0) *
        ∏ b : Fin (n + 1), U (g b) (snocMode (rowAt s) i b))
    (fun p : Fin m × (Fin n → Fin m) =>
      (if bump (occOf p.2) p.1 = r then (1 : ℂ) else 0) *
        (U p.1 i * ∏ a : Fin n, U (p.2 a) (rowAt s a)))
    ?_
  intro g
  simp only [Fin.snocEquiv_symm_apply]
  have hsnoc_self : snocMode (Fin.init g) (g (Fin.last n)) = g :=
    Fin.snoc_init_self g
  have hocc_g : bump (occOf (Fin.init g)) (g (Fin.last n)) = occOf g := by
    rw [← occOf_snocMode, hsnoc_self]
  rw [hocc_g]
  congr 1
  rw [Fin.prod_univ_castSucc]
  simp [snocMode, Fin.init, Fin.snoc_castSucc, Fin.snoc_last, mul_comm]

/-- For a unitary mode matrix, the adjoint of `gamma` times `gamma` is the identity. -/
private theorem gamma_unitary_left (m n : ℕ) (U : Matrix.unitaryGroup (Fin m) ℂ) :
    (gamma m n U.val).conjTranspose * gamma m n U.val = 1 := by
  have hU : U.val.conjTranspose * U.val = 1 := Matrix.mem_unitaryGroup_iff'.mp U.property
  rw [← gamma_conjTranspose, ← gamma_mul, hU, gamma_one]

/-- For a unitary mode matrix, `gamma` times its adjoint is the identity. -/
private theorem gamma_unitary_right (m n : ℕ) (U : Matrix.unitaryGroup (Fin m) ℂ) :
    gamma m n U.val * (gamma m n U.val).conjTranspose = 1 := by
  have hU : U.val * U.val.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp U.property
  rw [← gamma_conjTranspose, ← gamma_mul, hU, gamma_one]

/-- For a unitary mode matrix, second quantization intertwines annihilation with the combination
weighted by the conjugates of its column entries. -/
private theorem gamma_annihilate (m n : ℕ) (U : Matrix.unitaryGroup (Fin m) ℂ) (i : Fin m) :
    gamma m n U.val * annihilate m n i =
      (∑ j, star (U.val j i) • annihilate m n j) * gamma m (n + 1) U.val := by
  have h1 := congrArg Matrix.conjTranspose (gamma_create m n U.val i)
  have hconj_sum : (∑ j, U.val j i • create m n j).conjTranspose =
      ∑ j, star (U.val j i) • annihilate m n j := by
    ext s t
    simp [Matrix.sum_apply, Matrix.smul_apply, annihilate]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hconj_sum] at h1
  change annihilate m n i * (gamma m (n + 1) U.val).conjTranspose =
    (gamma m n U.val).conjTranspose * (∑ j, star (U.val j i) • annihilate m n j) at h1
  calc gamma m n U.val * annihilate m n i
      = gamma m n U.val * (annihilate m n i *
          ((gamma m (n + 1) U.val).conjTranspose * gamma m (n + 1) U.val)) := by
        rw [gamma_unitary_left, Matrix.mul_one]
    _ = gamma m n U.val * ((annihilate m n i * (gamma m (n + 1) U.val).conjTranspose) *
          gamma m (n + 1) U.val) := by
        rw [Matrix.mul_assoc (annihilate m n i)]
    _ = gamma m n U.val * (((gamma m n U.val).conjTranspose *
          (∑ j, star (U.val j i) • annihilate m n j)) * gamma m (n + 1) U.val) := by
        rw [h1]
    _ = (gamma m n U.val * (gamma m n U.val).conjTranspose) *
          (∑ j, star (U.val j i) • annihilate m n j) * gamma m (n + 1) U.val := by
        simp only [Matrix.mul_assoc]
    _ = (∑ j, star (U.val j i) • annihilate m n j) * gamma m (n + 1) U.val := by
        rw [gamma_unitary_right, Matrix.one_mul]

/-- For a collision-free input assignment, the squared magnitude of the second-quantized
transition entry equals the corresponding `bosonWeight` of the selected mode columns. -/
private theorem gamma_bosonWeight (m n : ℕ) (U : Matrix.unitaryGroup (Fin m) ℂ)
    (f : Fin n → Fin m) (s r : Occupation m n)
    (hf : Function.Injective f)
    (hs : ∀ i, (s.val i : ℕ) = (Finset.univ.filter (fun a => f a = i)).card) :
    Complex.normSq (gamma m n U.val r s) = bosonWeight (U.val.submatrix id f) r := by
  have hocc : occOf f = s := by
    rw [occOf_eq_iff]
    funext i
    rw [hs i, Finset.card_filter]
    rfl
  have hs_le : ∀ i : Fin m, (s.val i : ℕ) ≤ 1 := by
    intro i
    rw [hs i]
    refine Finset.card_le_one.mpr fun a ha b hb => hf ?_
    rw [(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2]
  have hs_fact : factProd s = 1 := by
    unfold factProd
    refine Finset.prod_eq_one fun i _ => ?_
    have hle := hs_le i
    have h1 : (s.val i : ℕ).factorial = 1 := by
      interval_cases (s.val i : ℕ) <;> rfl
    exact_mod_cast h1
  have hper : Matrix.permanent (bosonRowMatrix (U.val.submatrix id f) r) =
      Matrix.permanent (occupationMatrix U.val r s) := by
    have h1 : Matrix.permanent (bosonRowMatrix (U.val.submatrix id f) r) =
        ∑ σ : Equiv.Perm (Fin n), ∏ b : Fin n, U.val (rowAt r (σ b)) (f b) := rfl
    rw [h1, perm_col_replace U.val r s f hocc]
  rw [gamma_apply_factProd, hs_fact, Real.sqrt_one, Complex.ofReal_one, mul_one,
    map_div₀, Complex.normSq_ofReal, Real.mul_self_sqrt (factProd_nonneg r),
    bosonWeight, hper, ← factProd_cast]

/-- The permanent construction preserves identity, products, and adjoints and gives isometries
for unitary mode matrices. It intertwines ladder operators and identifies squared transition
amplitudes from collision-free inputs with boson weights. -/
theorem second_quantization_permanent_bridge :
    (∀ (m n : ℕ) (U V : Matrix.unitaryGroup (Fin m) ℂ),
      (gamma m n U.val).conjTranspose * gamma m n U.val = 1 ∧
      gamma m n (U.val * V.val) = gamma m n U.val * gamma m n V.val ∧
      gamma m n U.val.conjTranspose = (gamma m n U.val).conjTranspose) ∧
    (∀ (m n : ℕ), gamma m n (1 : Matrix (Fin m) (Fin m) ℂ) = 1) ∧
    (∀ (m n : ℕ) (U : Matrix.unitaryGroup (Fin m) ℂ) (i : Fin m),
      gamma m (n+1) U.val * create m n i =
        (∑ j, U.val j i • create m n j) * gamma m n U.val ∧
      gamma m n U.val * annihilate m n i =
        (∑ j, star (U.val j i) • annihilate m n j) * gamma m (n+1) U.val) ∧
    (∀ (m n : ℕ) (U : Matrix.unitaryGroup (Fin m) ℂ)
      (f : Fin n → Fin m) (s r : Occupation m n),
      Function.Injective f →
      (∀ i, (s.val i : ℕ) = (Finset.univ.filter (fun a => f a = i)).card) →
      Complex.normSq (gamma m n U.val r s) = bosonWeight (U.val.submatrix id f) r) :=
  ⟨fun m n U V => ⟨gamma_unitary_left m n U, gamma_mul m n U.val V.val, gamma_conjTranspose m n U.val⟩,
   gamma_one,
   fun m n U i => ⟨gamma_create m n U.val i, gamma_annihilate m n U i⟩,
   gamma_bosonWeight⟩

end Qatlib.Concepts.BosonFock.BosonOperators
