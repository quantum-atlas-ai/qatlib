/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.OrderRecovery.ReducedOrderDenominator
import Qatlib.Concepts.PeriodSampling.OrderRecovery.OrderFactorConsumers

/-!
# Order recovery from two reduced denominators

This module combines two phase samples using `pairLCMOrderDecode`: it decodes their reduced
denominators, forms their least common multiple, and verifies the resulting exponent. The
arithmetic and factor consumer extend the modular order-finding setting of [Shor1997].

When the gcd of the two spectral indices is coprime to the order, good phase windows recover the
full order. Counting such index pairs gives a uniform success probability bound for two
independent samples.

## Main statements

* `reduced_order_pair_lcm_arithmetic`: the least common multiple of two reduced denominators
  equals the order under the coprimality condition.
* `pair_lcm_order_soundness_and_actual_work`: sound exponent and factor outputs with explicit
  work bounds.
* `pair_lcm_order_actual_fresh_success_bound`: success probability at least `(8 / π²)² / 4`.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.PeriodSampling.OrderRecovery
open scoped Classical BigOperators
set_option autoImplicit false

/-- Decodes two reduced rational denominators, verifies their least common multiple as an
exponent of `a`, and records total scan work and the verification exponent. -/
def pairLCMOrderDecode (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (yz : Fin M×Fin M) :
    Option ℕ × (ℕ×ℕ) :=
  let x := reducedOrderDecode N M yz.1
  let y := reducedOrderDecode N M yz.2
  match x.1,y.1 with
  | some (_,q),some (_,v) =>
    let candidate := Nat.lcm q v
    (if orderVerificationProduct N a candidate=1 then some candidate else none,
      (x.2+y.2,candidate))
  | _,_ => (none,(x.2+y.2,0))

/-- Applies `orderFactor` to an exponent returned by the two-sample least-common-multiple
decoder. -/
def pairLCMFactor (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (yz : Fin M×Fin M) : Option ℕ :=
  (pairLCMOrderDecode N M a yz).1.bind (orderFactor N a)

/-- Counts index pairs in `Fin r × Fin r` whose gcd is coprime to `r`. -/
def orderCoprimePairCount (r : ℕ) : ℕ :=
  (Finset.univ.filter fun st : Fin r×Fin r => Nat.Coprime (Nat.gcd st.1.val st.2.val) r).card

/-- For positive `r` and indices below `r`, the least common multiple of `r / gcd(s, r)` and `r
/ gcd(t, r)` equals `r` when `gcd(s, t)` is coprime to `r`. -/
theorem reduced_order_pair_lcm_arithmetic :
    ∀ (r s t : ℕ), 0<r → s<r → t<r → Nat.Coprime (Nat.gcd s t) r →
      Nat.lcm (r/Nat.gcd s r) (r/Nat.gcd t r)=r := by
  intro r s t hr hs ht hc
  rw [Nat.div_lcm_eq_div_gcd (Nat.gcd_dvd_right s r) (Nat.gcd_dvd_right t r)]
  have hg : Nat.gcd (Nat.gcd s r) (Nat.gcd t r) = Nat.gcd (Nat.gcd s t) r := by
    simp [Nat.gcd_left_comm, Nat.gcd_comm]
  rw [hg, hc.gcd_eq_one, Nat.div_one]

/-- Under the nontriviality and clock-size hypotheses, two good phase windows recover the exact
order whenever the gcd of their spectral indices is coprime to it [Shor1997]. -/
theorem pair_lcm_order_actual_good_event :
    ∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (s t : Fin (orderOf a)) (y z : Fin M),
      1<N → 1<orderOf a → 2*N^2<M → Nat.Coprime (Nat.gcd s.val t.val) (orderOf a) →
      phaseDistance ((s.val:ℝ)/(orderOf a:ℝ)) ((y.val:ℝ)/M)≤1/(M:ℝ) →
      phaseDistance ((t.val:ℝ)/(orderOf a:ℝ)) ((z.val:ℝ)/M)≤1/(M:ℝ) →
      (pairLCMOrderDecode N M a (y,z)).1=some (orderOf a) := by
  intro N M _ a s t y z hN hr hsize hc hy hz
  have hd := reduced_order_denominator_of_every_good_phase N M a s y hN hr hsize hy
  have he := reduced_order_denominator_of_every_good_phase N M a t z hN hr hsize hz
  have hl := reduced_order_pair_lcm_arithmetic (orderOf a) s.val t.val
    (modular_order_pos N a) s.isLt t.isLt hc
  simp only [pairLCMOrderDecode, hd, he, hl, orderVerificationProduct_eq_pow,
    pow_orderOf_eq_one, ite_true]

/-- The pair decoder uses at most `N * (N + 1)` scan tests and verification exponent at most `N
^ 2`, returning only positive exponents with `a ^ q = 1`. Every successful `pairLCMFactor`
output is a nontrivial divisor of `N` [Shor1997]. -/
theorem pair_lcm_order_soundness_and_actual_work :
    ∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (y z : Fin M),
      (pairLCMOrderDecode N M a (y,z)).2.1≤N*(N+1) ∧
      (pairLCMOrderDecode N M a (y,z)).2.2≤N^2 ∧
      (∀ q, (pairLCMOrderDecode N M a (y,z)).1=some q → 0<q ∧ a^q=1) ∧
      (∀ d, pairLCMFactor N M a (y,z)=some d → 1<d ∧ d<N ∧ d∣N) := by
  intro N M _ a y z
  have hfac (d : ℕ) (hd : pairLCMFactor N M a (y,z)=some d) : 1<d ∧ d<N ∧ d∣N := by
    unfold pairLCMFactor at hd
    cases hq : (pairLCMOrderDecode N M a (y,z)).1 with
    | none => simp [hq] at hd
    | some q => exact orderFactor_sound N a q d (by simpa [hq] using! hd)
  refine ⟨?_, ?_, ?_, hfac⟩
  all_goals
    have hx := reducedOrderDecode_count N M y
    have hy := reducedOrderDecode_count N M z
    unfold pairLCMOrderDecode
    (try dsimp only)
    cases hd : (reducedOrderDecode N M y).1 with
    | none =>
      simp
      all_goals omega
    | some x =>
      obtain ⟨p,q⟩ := x
      have hq := reducedOrderDecode_sound N M y p q hd
      cases he : (reducedOrderDecode N M z).1 with
      | none =>
        simp
        all_goals omega
      | some x =>
        obtain ⟨u,v⟩ := x
        have hv := reducedOrderDecode_sound N M z u v he
        (try dsimp only)
        first
        | omega
        | exact (Nat.lcm_le_mul hq.1 hv.1).trans (by simpa [pow_two] using! Nat.mul_le_mul hq.2 hv.2)
        | intro j hj
          split at hj
          · cases Option.some.inj hj
            exact ⟨Nat.lcm_pos hq.1 hv.1, by
              simpa [orderVerificationProduct_eq_pow] using!
                ‹orderVerificationProduct N a (Nat.lcm q v)=1›⟩
          · simp at hj
/-- The set of pairs of indices below `r` both divisible by `d`. -/
private def orderDivisiblePairs (r d : ℕ) : Finset (Fin r×Fin r) :=
  Finset.univ.filter fun st => d ∣ st.1.val ∧ d ∣ st.2.val

/-- For positive `d` dividing `r`, at most `(r / d) ^ 2` pairs of indices below `r` are both
divisible by `d`. -/
private theorem orderDivisiblePairs_card (r d : ℕ) (hd : 0<d) (hdr : d∣r) :
    (orderDivisiblePairs r d).card ≤ (r/d)^2 := by
  let f : Fin r×Fin r → Fin (r/d)×Fin (r/d) := fun st =>
    (⟨st.1.val/d, (Nat.div_lt_iff_lt_mul hd).mpr (by rw [Nat.div_mul_cancel hdr]; exact st.1.isLt)⟩,
     ⟨st.2.val/d, (Nat.div_lt_iff_lt_mul hd).mpr (by rw [Nat.div_mul_cancel hdr]; exact st.2.isLt)⟩)
  have h := Finset.card_le_card_of_injOn f (s := orderDivisiblePairs r d) (t := Finset.univ)
    (fun st _ => Finset.mem_univ (f st)) (by
      intro st hs uv hu hh
      have hs' := (Finset.mem_filter.mp hs).2
      have hu' := (Finset.mem_filter.mp hu).2
      have h1 := congrArg (fun z : Fin (r/d)×Fin (r/d) => z.1.val) hh
      have h2 := congrArg (fun z : Fin (r/d)×Fin (r/d) => z.2.val) hh
      apply Prod.ext <;> apply Fin.ext
      · have hm := congrArg (fun n : ℕ => n*d) h1
        simpa only [f, Nat.div_mul_cancel hs'.1, Nat.div_mul_cancel hu'.1] using! hm
      · have hm := congrArg (fun n : ℕ => n*d) h2
        simpa only [f, Nat.div_mul_cancel hs'.2, Nat.div_mul_cancel hu'.2] using! hm)
  simpa [pow_two] using! h

/-- For `r ≥ 2`, the sum of `1 / d²` over integers from two through `r` is at most `3 / 4 - 1 /
r`. -/
private theorem reciprocal_square_sum (r : ℕ) (hr : 2≤r) :
    (∑ d ∈ Finset.Icc 2 r, 1/(d:ℝ)^2) ≤ 3/4-1/(r:ℝ) := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hrp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
    have hsp : (0:ℝ)<(r+1:ℕ) := by positivity
    have he : 1/((r+1:ℕ):ℝ)^2 ≤ 1/(r:ℝ)-1/((r+1:ℕ):ℝ) := by
      rw [Nat.cast_add, Nat.cast_one]
      field_simp
      nlinarith
    linarith

/-- For `r > 1`, at least `r² / 4` index pairs below `r` have gcd coprime to `r`. This count
supports the two-sample order-finding success bound [Shor1997]. -/
theorem coprime_order_pair_uniform_constant :
    ∀ (r : ℕ), 1<r → (r:ℝ)^2/4≤(orderCoprimePairCount r:ℝ) := by
  intro r hr
  let bad := Finset.univ.filter fun st : Fin r×Fin r => ¬ Nat.Coprime (Nat.gcd st.1.val st.2.val) r
  let ds := (Finset.Icc 2 r).filter fun d => d∣r
  have hcover : bad ⊆ ds.biUnion (orderDivisiblePairs r) := by
    intro st hs
    have hs' := (Finset.mem_filter.mp hs).2
    let d := Nat.gcd (Nat.gcd st.1.val st.2.val) r
    have hd1 : d≠1 := hs'
    have hd0 : 0<d := Nat.gcd_pos_of_pos_right _ (by omega)
    have hd2 : 2≤d := by omega
    have hdr : d∣r := Nat.gcd_dvd_right _ _
    have hle : d≤r := Nat.le_of_dvd (by omega) hdr
    apply Finset.mem_biUnion.mpr
    refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd2,hle⟩,hdr⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _),
      (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)⟩
  have hcard : bad.card ≤ ∑ d ∈ ds, (r/d)^2 :=
    (Finset.card_le_card hcover).trans ((Finset.card_biUnion_le).trans
      (Finset.sum_le_sum fun d hd => orderDivisiblePairs_card r d
        (by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1; omega)
        (Finset.mem_filter.mp hd).2))
  have hbad : (bad.card:ℝ) ≤ (r:ℝ)^2*(3/4) := by
    calc
      _ ≤ ∑ d ∈ ds, ((r/d:ℕ):ℝ)^2 := by exact_mod_cast hcard
      _ = (r:ℝ)^2 * ∑ d ∈ ds, 1/(d:ℝ)^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        have hd' := (Finset.mem_filter.mp hd).2
        have hdpos : 0<d := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1; omega
        rw [Nat.cast_div hd' (by positivity)]
        ring
      _ ≤ (r:ℝ)^2 * ∑ d ∈ Finset.Icc 2 r, 1/(d:ℝ)^2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (by intros; positivity)) (sq_nonneg _)
      _ ≤ (r:ℝ)^2*(3/4) := mul_le_mul_of_nonneg_left
        ((reciprocal_square_sum r (by omega)).trans (sub_le_self _ (by positivity))) (sq_nonneg _)
  have htotal : orderCoprimePairCount r + bad.card = r^2 := by
    have h :=
        Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun st : Fin r×Fin r => Nat.Coprime (Nat.gcd st.1.val st.2.val) r)
    simpa [orderCoprimePairCount, bad, pow_two] using! h
  have htotalR : (orderCoprimePairCount r:ℝ)+(bad.card:ℝ)=(r:ℝ)^2 := by exact_mod_cast htotal
  linarith

/-- Under the nontriviality and clock-size hypotheses, two independent samples from
`modularOrderLaw` recover the exact order with probability at least `(8 / π²)² / 4`
[Shor1997]. -/
theorem pair_lcm_order_actual_fresh_success_bound :
    ∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0<M),
      1<N → 1<orderOf a → 2*N^2<M →
      (∑ yz ∈ Finset.univ.filter (fun yz : Fin M×Fin M =>
        (pairLCMOrderDecode N M a yz).1=some (orderOf a)),
        (modularOrderLaw N M a hM).prob yz.1*(modularOrderLaw N M a hM).prob yz.2) ≥
          (8/Real.pi^2)^2/4 := by
  intro N M _ a hM hN hr hsize
  let r := orderOf a
  let c : ℝ := 8/Real.pi^2
  let good := Finset.univ.filter fun yz : Fin M×Fin M =>
    (pairLCMOrderDecode N M a yz).1=some r
  let cop := Finset.univ.filter fun st : Fin r×Fin r => Nat.Coprime (Nat.gcd st.1.val st.2.val) r
  let kernel := fun (s : Fin r) (y : Fin M) => ‖qpeKernel M ((s.val:ℝ)/(r:ℝ)) y‖^2
  let window := fun s : Fin r => Finset.univ.filter fun y : Fin M =>
    phaseDistance ((s.val:ℝ)/(r:ℝ)) ((y.val:ℝ)/M) ≤ 1/(M:ℝ)
  let mass := fun st : Fin r×Fin r => ∑ yz ∈ good, kernel st.1 yz.1 * kernel st.2 yz.2
  have hc : 0≤c := by positivity
  have hkernel (s : Fin r) (y : Fin M) : 0≤kernel s y := sq_nonneg _
  have hm (st : Fin r×Fin r) (hs : st∈cop) : c^2 ≤ mass st := by
    have hsub : (window st.1).product (window st.2) ⊆ good := by
      intro yz hyz
      obtain ⟨hy,hz⟩ := Finset.mem_product.mp hyz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        pair_lcm_order_actual_good_event N M a st.1 st.2 yz.1 yz.2 hN hr hsize
          (Finset.mem_filter.mp hs).2 (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2⟩
    have hw1 : c ≤ ∑ y ∈ window st.1, kernel st.1 y :=
      offgrid_phase_window_probability M _ (by nlinarith)
    have hw2 : c ≤ ∑ y ∈ window st.2, kernel st.2 y :=
      offgrid_phase_window_probability M _ (by nlinarith)
    calc
      _ ≤ (∑ y ∈ window st.1, kernel st.1 y)*(∑ z ∈ window st.2, kernel st.2 z) := by
        simpa [pow_two] using! mul_le_mul hw1 hw2 hc (hc.trans hw1)
      _ = ∑ yz ∈ (window st.1).product (window st.2), kernel st.1 yz.1*kernel st.2 yz.2 := by
        exact (Finset.sum_mul_sum (window st.1) (window st.2)
          (kernel st.1) (kernel st.2)).trans
          (Finset.sum_product (window st.1) (window st.2)
            (fun yz : Fin M×Fin M => kernel st.1 yz.1*kernel st.2 yz.2)).symm
      _ ≤ mass st := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (by intro yz _ _; exact mul_nonneg (hkernel _ _) (hkernel _ _))
  have hmass : (orderCoprimePairCount r:ℝ)*c^2 ≤ ∑ st, mass st := by
    calc
      _ = ∑ _st ∈ cop, c^2 := by simp [cop, orderCoprimePairCount]
      _ ≤ ∑ st ∈ cop, mass st := Finset.sum_le_sum hm
      _ ≤ ∑ st, mass st := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (by intro st _ _; exact Finset.sum_nonneg fun yz _ => mul_nonneg (hkernel _ _) (hkernel _ _))
  have hp (yz : Fin M×Fin M) :
      (modularOrderLaw N M a hM).prob yz.1*(modularOrderLaw N M a hM).prob yz.2 =
        (1/(r:ℝ)^2)*∑ st : Fin r×Fin r, kernel st.1 yz.1*kernel st.2 yz.2 := by
    rw [modular_order_born_uniform_orbit_spectrum N M a hM _ hN,
      modular_order_born_uniform_orbit_spectrum N M a hM _ hN, Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    dsimp [kernel,r]
    ring
  have he : (∑ yz ∈ good, (modularOrderLaw N M a hM).prob yz.1*(modularOrderLaw N M a hM).prob yz.2) =
      (1/(r:ℝ)^2)*∑ st, mass st := by
    simp_rw [hp]
    rw [← Finset.mul_sum, Finset.sum_comm]
  change c^2/4 ≤ ∑ yz ∈ good, _
  rw [he]
  have hrp : (0:ℝ)<r := by exact_mod_cast modular_order_pos N a
  calc
    c^2/4 = (1/(r:ℝ)^2)*((r:ℝ)^2/4*c^2) := by field_simp
    _ ≤ (1/(r:ℝ)^2)*((orderCoprimePairCount r:ℝ)*c^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (coprime_order_pair_uniform_constant r hr) (sq_nonneg c)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)
end Qatlib.Concepts.PeriodSampling.OrderRecovery
