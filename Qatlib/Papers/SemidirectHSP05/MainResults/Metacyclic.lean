/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemidirectHSP05.MainResults.HspMainResults

/-!
# Geometric sums and metacyclic solution counts

This module develops finite geometric sums in a commutative ring and counting identities
associated with the metacyclic case of [BaconChildsVanDam2005]. For a nonidentity unit whose pth
power is one, with p prime, `matSum_injective` separates the first p partial sums;
multiplication by a unit preserves their cardinality.

## Main statements

* `matSum_injective`: Geometric partial sums with indices below p are distinct under the
  prime-order hypotheses.
* `card_solvable_targets`: Each unit input has exactly p attainable targets.
* `card_solvable_pairs_totient`: The number of solvable pairs with unit input over ZMod N is
  φ(N) * p.

## References

* [Bacon et al., 2005][BaconChildsVanDam2005]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP05.MainResults.Metacyclic

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The sum of the powers `μ ^ i` for natural indices `i < b`. -/
def matSum (μ : R) (b : ℕ) : R := ∑ i ∈ Finset.range b, μ ^ i

/-- The geometric sum of length `m + n` splits into the length-m sum plus `μ ^ m` times the
length-n sum [BaconChildsVanDam2005]. -/
lemma matSum_add (μ : R) (m n : ℕ) :
    matSum μ (m + n) = matSum μ m + μ ^ m * matSum μ n := by
  unfold matSum
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]

/-- For `b' ≤ b`, the length-b geometric sum splits at `b'` into its initial segment and a
shifted tail. -/
lemma matSum_sub (μ : R) (b b' : ℕ) (h : b' ≤ b) :
    matSum μ b = matSum μ b' + μ ^ b' * matSum μ (b - b') := by
  conv_lhs => rw [← Nat.add_sub_of_le h]
  rw [matSum_add]

/-- A unit can be cancelled from the right of an equality of products. -/
lemma mul_right_cancel_of_isUnit {a b x : R} (hx : IsUnit x) (h : a * x = b * x) : a = b := by
  obtain ⟨v, rfl⟩ := hx
  have hv : (↑v : R) * (↑v⁻¹ : R) = 1 := Units.mul_inv v
  have h1 : a * ((↑v : R) * (↑v⁻¹ : R)) = b * ((↑v : R) * (↑v⁻¹ : R)) := by
    rw [← mul_assoc, ← mul_assoc, h]
  rw [hv, mul_one, mul_one] at h1
  exact h1

/-- For prime `p` and a unit `μ ≠ 1` satisfying `μ ^ p = 1`, equal geometric sums with indices
below `p` have equal indices [BaconChildsVanDam2005]. -/
theorem matSum_injective {p : ℕ} (hp : p.Prime) {μ : R} (hu : IsUnit μ)
    (hμp : μ ^ p = 1) (hμ1 : μ ≠ 1) {b b' : ℕ} (hb : b < p) (hb' : b' < p)
    (h : matSum μ b = matSum μ b') : b = b' := by
  obtain ⟨u, rfl⟩ := hu
  have hup : u ^ p = 1 := by
    ext
    simpa using hμp

  have key : ∀ ⦃d d' : ℕ⦄, d' ≤ d → d < p → d' < p →
      matSum (↑u : R) d = matSum (↑u : R) d' → d = d' := by
    intro d d' hdle hd hd' hdd
    rcases eq_or_lt_of_le hdle with heq | hlt
    · exact heq.symm
    · exfalso
      set k : ℕ := d - d' with hkdef
      have hkpos : 0 < k := Nat.sub_pos_of_lt hlt
      have hklt : k < p := lt_of_le_of_lt (Nat.sub_le d d') hd
      have hsub := matSum_sub (μ := (↑u : R)) d d' hdle

      have hzero : (↑u : R) ^ d' * matSum (↑u : R) k = 0 := by
        have h1 : matSum (↑u : R) d' + (↑u : R) ^ d' * matSum (↑u : R) k
            = matSum (↑u : R) d' := by
          rw [← hsub]; exact hdd
        exact add_eq_left.mp h1

      have hMk : matSum (↑u : R) k = 0 := by
        set U : Rˣ := u ^ d' with hU
        have hUR : (↑u : R) ^ d' = (↑U : R) := by
          rw [← Units.val_pow_eq_pow_val, ← hU]
        have hU0 : (↑U : R) * matSum (↑u : R) k = 0 := by
          rw [← hUR]; exact hzero
        have hUU : (↑(U⁻¹) * ↑U : R) = 1 := Units.inv_mul U
        calc matSum (↑u : R) k
            = (↑(U⁻¹) * ↑U) * matSum (↑u : R) k := by rw [hUU, one_mul]
          _ = ↑(U⁻¹) * ((↑U : R) * matSum (↑u : R) k) := by rw [mul_assoc]
          _ = ↑(U⁻¹) * 0 := by rw [hU0]
          _ = 0 := mul_zero _

      have hμk : (↑u : R) ^ k = 1 := by
        have hgeom :=
          HspMainResults.theorem4_geometric_sum (↑u : R) k
        rw [show (∑ j ∈ Finset.range k, (↑u : R) ^ j) = matSum (↑u : R) k from rfl,
          hMk, mul_zero] at hgeom
        exact sub_eq_zero.mp hgeom.symm
      have huk : u ^ k = 1 := by
        ext
        simpa using hμk

      have hcop : Nat.gcd p k = 1 := by
        have hnot : ¬ p ∣ k := by
          intro hdvd
          have := Nat.le_of_dvd hkpos hdvd
          omega
        exact hp.coprime_iff_not_dvd.mpr hnot
      have h1 : orderOf u ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hup
      have h2 : orderOf u ∣ k := orderOf_dvd_iff_pow_eq_one.mpr huk
      have hgcd : orderOf u ∣ Nat.gcd p k := Nat.dvd_gcd h1 h2
      rw [hcop] at hgcd
      have hord : orderOf u = 1 := Nat.dvd_one.mp hgcd
      have hu1 : u = 1 := orderOf_eq_one_iff.mp hord
      exact hμ1 (by rw [hu1]; rfl)
  rcases le_total b' b with hle | hle
  · exact key hle hb hb' h
  · exact (key hle hb' hb h.symm).symm

/-- Multiplying the first `p` geometric partial sums by a unit gives a finite image of
cardinality `p` under the prime-order hypotheses on `μ` [BaconChildsVanDam2005]. -/
theorem card_image_mul {p : ℕ} (hp : p.Prime) {μ x : R} [DecidableEq R] (hu : IsUnit μ)
    (hμp : μ ^ p = 1) (hμ1 : μ ≠ 1) (hx : IsUnit x) :
    (Finset.univ.image (fun b : Fin p => matSum μ (b : ℕ) * x)).card = p := by
  have hinj : Function.Injective (fun b : Fin p => matSum μ (b : ℕ) * x) := by
    intro b1 b2 hb
    have heq : matSum μ (b1 : ℕ) = matSum μ (b2 : ℕ) :=
      mul_right_cancel_of_isUnit hx hb
    exact Fin.ext (matSum_injective hp hu hμp hμ1 b1.isLt b2.isLt heq)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- For a unit input `x`, exactly `p` targets can be expressed as `matSum μ b * x` with `b < p`
under the prime-order hypotheses on `μ`. -/
theorem card_solvable_targets {p : ℕ} (hp : p.Prime) {μ x : R} [Fintype R] [DecidableEq R]
    (hu : IsUnit μ) (hμp : μ ^ p = 1) (hμ1 : μ ≠ 1) (hx : IsUnit x) :
    (Finset.univ.filter (fun w : R => ∃ b : Fin p, matSum μ (b : ℕ) * x = w)).card = p := by
  have himg : (Finset.univ.filter (fun w : R =>
        ∃ b : Fin p, matSum μ (b : ℕ) * x = w))
      = Finset.univ.image (fun b : Fin p => matSum μ (b : ℕ) * x) := by
    ext w
    simp [Finset.mem_image, eq_comm]
  rw [himg]
  exact card_image_mul hp hu hμp hμ1 hx

/-- Over `ZMod N`, the number of pairs with unit first coordinate and a solvable geometric-sum
equation equals the number of units times `p`. -/
theorem card_solvable_pairs (N p : ℕ) [Fact p.Prime] [NeZero N] {μ : ZMod N}
    (hu : IsUnit μ) (hμp : μ ^ p = 1) (hμ1 : μ ≠ 1) :
    (Finset.univ.filter (fun xw : ZMod N × ZMod N =>
        IsUnit xw.1 ∧ ∃ b : Fin p, matSum μ (b : ℕ) * xw.1 = xw.2)).card
      = (Finset.univ.filter (fun x : ZMod N => IsUnit x)).card * p := by
  classical

  have h1 : (Finset.univ.filter (fun xw : ZMod N × ZMod N =>
        IsUnit xw.1 ∧ ∃ b : Fin p, matSum μ (b : ℕ) * xw.1 = xw.2)).card
      = ∑ x : ZMod N, ∑ w : ZMod N,
          (if (IsUnit x ∧ ∃ b : Fin p, matSum μ (b : ℕ) * x = w) then (1 : ℕ) else 0) := by
    have hprod : (∑ x : ZMod N, ∑ w : ZMod N,
          (if (IsUnit x ∧ ∃ b : Fin p, matSum μ (b : ℕ) * x = w) then (1 : ℕ) else 0))
        = (Finset.univ.filter (fun xw : ZMod N × ZMod N =>
            IsUnit xw.1 ∧ ∃ b : Fin p, matSum μ (b : ℕ) * xw.1 = xw.2)).card := by
      rw [← Fintype.sum_prod_type'
        (fun x w => if (IsUnit x ∧ ∃ b : Fin p, matSum μ (b : ℕ) * x = w) then (1 : ℕ) else 0)]
      exact Finset.sum_boole _ Finset.univ
    exact hprod.symm

  have hinner : ∀ x : ZMod N,
      (∑ w : ZMod N,
          (if (IsUnit x ∧ ∃ b : Fin p, matSum μ (b : ℕ) * x = w) then (1 : ℕ) else 0))
        = if IsUnit x then p else 0 := by
    intro x
    by_cases hx : IsUnit x
    · rw [if_pos hx, Finset.sum_boole]
      have hfilter : (Finset.univ.filter (fun w : ZMod N =>
            IsUnit x ∧ ∃ b : Fin p, matSum μ (b : ℕ) * x = w))
          = Finset.univ.filter (fun w : ZMod N =>
              ∃ b : Fin p, matSum μ (b : ℕ) * x = w) := by
        apply Finset.filter_congr
        intro w _
        exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
      rw [hfilter]
      exact card_solvable_targets (Fact.out) hu hμp hμ1 hx
    · rw [if_neg hx]
      apply Finset.sum_eq_zero
      intro w _
      rw [if_neg (fun h => hx h.1)]
  rw [h1]
  simp only [hinner]
  have h2 : (∑ x : ZMod N, (if IsUnit x then p else 0))
      = (Finset.univ.filter (fun x : ZMod N => IsUnit x)).card * p := by
    have hsum : (∑ x : ZMod N, (if IsUnit x then (1 : ℕ) else 0))
        = (Finset.univ.filter (fun x : ZMod N => IsUnit x)).card :=
      Finset.sum_boole _ _
    rw [← hsum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : IsUnit x <;> simp [hx]
  exact h2

/-- The number of elements of `ZMod N` that are units equals the Euler totient `Nat.totient N`. -/
theorem card_units_filter (N : ℕ) [NeZero N] :
    (Finset.univ.filter (fun x : ZMod N => IsUnit x)).card = Nat.totient N := by
  classical
  have heq : Fintype.card {x : ZMod N // IsUnit x} = Fintype.card (ZMod N)ˣ :=
    Fintype.card_congr
      { toFun := fun x => x.2.unit
        invFun := fun u => ⟨(↑u : ZMod N), Units.isUnit u⟩
        left_inv := fun x => Subtype.ext x.2.unit_spec
        right_inv := fun u => Units.ext (IsUnit.unit_spec (Units.isUnit u)) }
  rw [← Fintype.card_subtype (fun x : ZMod N => IsUnit x), heq,
    ZMod.card_units_eq_totient N]

/-- Under the stated prime-order conditions on `μ`, the number of solvable pairs with unit input
over `ZMod N` equals `Nat.totient N * p`. This is a metacyclic counting ingredient for
[BaconChildsVanDam2005]. -/
theorem card_solvable_pairs_totient (N p : ℕ) [Fact p.Prime] [NeZero N] {μ : ZMod N}
    (hu : IsUnit μ) (hμp : μ ^ p = 1) (hμ1 : μ ≠ 1) :
    (Finset.univ.filter (fun xw : ZMod N × ZMod N =>
        IsUnit xw.1 ∧ ∃ b : Fin p, matSum μ (b : ℕ) * xw.1 = xw.2)).card
      = Nat.totient N * p := by
  rw [card_solvable_pairs N p hu hμp hμ1, card_units_filter N]

end Qatlib.Papers.SemidirectHSP05.MainResults.Metacyclic
