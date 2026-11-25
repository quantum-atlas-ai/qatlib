/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset.Basic
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Data.Multiset.Replicate
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Counting-matrix form of the sumset criterion (Theorem S2, equivalent formulations)

Fixed arXiv:2607.29382v2, Supplement page S5, Eqs. (S12)–(S13), and the centred form on
page S6, `N (λ − m·1) = −(λ − m·1)`.  For a spectrum `Λ = {λ_0, …, λ_{K−1}}` the paper
restates the criterion `c − Λ ⊆ Σ_q(Λ)` of
`Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset.KappaWitness` as the existence of a
`K × K` matrix `N` of multiplicities with row sums `q` and weighted column sums `c − λ_j`:

`Σ_l N_{jl} = q`,  `Σ_l N_{jl} λ_l = c − λ_j`.

This module proves that equivalence.  The passage between multisets of *values* and
multiplicities of *labels* is made explicit through a chosen preimage
`preimageLabel lam`, which is where repeated spectral values are handled: a value `λ` with
several preimages may be realised by any of them.

* `sum_count_eq_card`, `sum_count_mul` — multiplicities of a multiset of labels add up to
  its cardinality and weight its label sum;
* `sumOf_iff_exists_labelMultiset` — `SumOf q (univ.image lam) s` holds exactly when some
  multiset of `q` labels has label sum `s`;
* `kappaWitness_iff_exists_countMatrix` — the matrix form of Theorem S2's criterion.

The `c = Σ Λ` choice with `N = J − I` that certifies `κ(Λ) ≤ K − 1` is
`kappaWitness_card_sub_one` in the public statement layer and is not restated here.
-/

open Finset
open scoped BigOperators

namespace Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset

open Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset

set_option autoImplicit false

/-- The multiplicities of a multiset of labels add up to its cardinality. -/
theorem sum_count_eq_card {K : ℕ} (m : Multiset (Fin K)) :
    (∑ l : Fin K, m.count l) = m.card := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have hc : ∀ l : Fin K, (a ::ₘ s).count l = s.count l + (if l = a then 1 else 0) := by
      intro l
      rw [Multiset.count_cons]
    calc (∑ l : Fin K, (a ::ₘ s).count l)
        = ∑ l : Fin K, (s.count l + if l = a then 1 else 0) :=
          Finset.sum_congr rfl (fun l _ => hc l)
      _ = (∑ l : Fin K, s.count l) + ∑ l : Fin K, (if l = a then 1 else 0) :=
          Finset.sum_add_distrib
      _ = s.card + 1 := by
          rw [ih, Finset.sum_ite_eq']
          simp
      _ = (a ::ₘ s).card := by rw [Multiset.card_cons]

/-- Reading a multiset of labels through `lam` and weighting labels by multiplicities give
the same real number. -/
theorem sum_count_mul {K : ℕ} (m : Multiset (Fin K)) (lam : Fin K → ℝ) :
    (∑ l : Fin K, (m.count l : ℝ) * lam l) = (m.map lam).sum := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have hc : ∀ l : Fin K,
        ((a ::ₘ s).count l : ℝ) = (s.count l : ℝ) + ((if l = a then 1 else 0 : ℕ) : ℝ) := by
      intro l
      rw [Multiset.count_cons]
      push_cast
      ring
    calc (∑ l : Fin K, ((a ::ₘ s).count l : ℝ) * lam l)
        = ∑ l : Fin K,
            ((s.count l : ℝ) * lam l + ((if l = a then 1 else 0 : ℕ) : ℝ) * lam l) := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [hc l, add_mul]
      _ = (∑ l : Fin K, (s.count l : ℝ) * lam l) +
            ∑ l : Fin K, ((if l = a then 1 else 0 : ℕ) : ℝ) * lam l := Finset.sum_add_distrib
      _ = (s.map lam).sum + lam a := by
          rw [ih]
          congr 1
          rw [Finset.sum_eq_single a]
          · simp
          · intro l _ hl
            simp [hl]
          · intro h
            simp at h
      _ = ((a ::ₘ s).map lam).sum := by
          rw [Multiset.map_cons, Multiset.sum_cons, add_comm]

/-- **Equivalent formulation of the sumset criterion** (Eqs. (S12)–(S13), page S5):
`SumOf q (univ.image lam) s` holds exactly when some multiset of `q` labels has label sum
`s`. -/
theorem sumOf_iff_exists_labelMultiset {K q : ℕ} {lam : Fin K → ℝ} {s : ℝ} :
    SumOf q (Finset.univ.image lam) s ↔
      ∃ p : Multiset (Fin K), p.card = q ∧ (p.map lam).sum = s := by
  constructor
  · rintro ⟨m, hmcard, hmem, hmsum⟩
    refine ⟨m.attach.map (fun x => (Finset.mem_image.mp (hmem x.val x.property)).choose), ?_, ?_⟩
    · rw [Multiset.card_map, Multiset.card_attach]
      exact hmcard
    · have hsl : m.attach.map (fun x : {a // a ∈ m} => x.val) = m := by
        simp
      have hlm : (m.attach.map
            (fun x => (Finset.mem_image.mp (hmem x.val x.property)).choose)).map lam =
          m.attach.map (fun x : {a // a ∈ m} => x.val) := by
        rw [Multiset.map_map]
        refine Multiset.map_congr rfl (fun x _ => ?_)
        exact ((Finset.mem_image.mp (hmem x.val x.property)).choose_spec).2
      rw [hlm, hsl]
      exact hmsum
  · rintro ⟨p, hpcard, hpsum⟩
    refine ⟨p.map lam, ?_, ?_, hpsum⟩
    · rw [Multiset.card_map]
      exact hpcard
    · intro x hx
      obtain ⟨l, -, rfl⟩ := Multiset.mem_map.mp hx
      exact Finset.mem_image_of_mem lam (Finset.mem_univ l)

/-- **Theorem S2, counting-matrix form** (Eqs. (S12)–(S13), page S5): the sumset criterion
for the spectrum `λ` is equivalent to the existence of a `K × K` multiplicity matrix whose
rows sum to `q` and whose weighted column sums are `c − λ_j`. -/
theorem kappaWitness_iff_exists_countMatrix {K : ℕ} (lam : Fin K → ℝ) (q : ℕ) :
    KappaWitness (Finset.univ.image lam) q ↔
      ∃ (N : Fin K → Fin K → ℕ) (c : ℝ),
        (∀ j, (∑ l, N j l) = q) ∧ (∀ j, (∑ l, (N j l : ℝ) * lam l) = c - lam j) := by
  constructor
  · rintro ⟨c, hc⟩
    have hlab : ∀ j : Fin K, ∃ p : Multiset (Fin K), p.card = q ∧ (p.map lam).sum = c - lam j :=
      fun j => sumOf_iff_exists_labelMultiset.mp
        (hc (lam j) (Finset.mem_image_of_mem lam (Finset.mem_univ j)))
    choose p hpcard hpsum using hlab
    exact ⟨fun j l => (p j).count l, c, fun j => by rw [sum_count_eq_card, hpcard],
      fun j => by rw [sum_count_mul, hpsum]⟩
  · rintro ⟨N, c, hrow, hval⟩
    refine ⟨c, fun a ha => ?_⟩
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp ha
    rw [← hj]
    refine sumOf_iff_exists_labelMultiset.mpr
      ⟨Finset.univ.val.bind (fun l => Multiset.replicate (N j l) l), ?_, ?_⟩
    · rw [Multiset.card_bind]
      calc (Finset.univ.val.map (fun l : Fin K => (Multiset.replicate (N j l) l).card)).sum
          = ∑ l : Fin K, N j l := by
            rw [Finset.sum_eq_multiset_sum]
            simp
        _ = q := hrow j
    · rw [Multiset.map_bind]
      simp only [Multiset.map_replicate]
      rw [Multiset.sum_bind]
      calc (Finset.univ.val.map
            (fun l : Fin K => (Multiset.replicate (N j l) (lam l)).sum)).sum
          = ∑ l : Fin K, N j l • lam l := by
            rw [Finset.sum_eq_multiset_sum]
            simp [Multiset.sum_replicate]
        _ = ∑ l : Fin K, (N j l : ℝ) * lam l := by
            refine Finset.sum_congr rfl (fun l _ => ?_)
            rw [nsmul_eq_mul]
        _ = c - lam j := hval j

end Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset
