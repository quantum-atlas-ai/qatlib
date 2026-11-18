/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
public import Qatlib.Concepts.StabilizerAlg.NearUniformGen.NearUniformGenerationSubgoalQuan
public import Qatlib.Papers.ExactSimon97.MainResults.GeneralSampler

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped BigOperators Classical

/-!
# Theorem 1 of [EttingerHoyer1999]: generating the hidden subgroup of an Abelian HSP

Theorem 1 states: for `γ : G → R` fulfilling the Abelian subgroup promise with respect
to a subgroup `H` of a finite Abelian group `G`, there is a quantum algorithm that
outputs a subset `X ⊆ G` generating `H` with probability at least `1 - 1/|G|`, using
`O(log |G|)` evaluations of `γ`.

The mathematical content established here:

* `unifOnSub`: the uniform law on a finite subgroup as a `FinDist` on the ambient group,
  and `unifOnSub_exact`: it satisfies the near-uniformness condition with `δ = 0`.
* `genFail_lt`: `l` independent uniform samples of a finite Abelian subgroup `H` fail to
  generate `H` with probability strictly below `|H| · (1/2)^l`, via the maximal-subgroup
  covering imported from the public library (`nearUniformGenerationSubgoal`).
* `genSampleCount`/`genSuccess_ge`: with `l = 2 * (Nat.log 2 |G| + 1) + 1` samples the
  generation probability is at least `1 - 1/|G|`; the count is `O(log |G|)`.
* `theorem1_generation`: interface assembly — any per-experiment sampling law that is
  uniform on the promise subgroup generates `H` with the Theorem 1 probability using
  `l` experiments (one evaluation of `γ` each).
* On a product of cyclic groups (`AbGroup n m`): `annann_eq` (the double character
  annihilator returns the subgroup), `fourierBorn_unif` (the Born law of Fourier
  measurement of a coset state is exactly `unifOnSub (annihilatorGen K)`, by the public
  `bornProb_genCosetState_uniform`), and `theorem1_abelian_AbGroup`: `l` annihilator
  samples generate the annihilator, hence re-annihilating recovers `K` itself with
  probability at least `1 - 1/|G|`.

Interface boundary: coherent coset-state preparation from `γ` and independence across
repeated experiments are taken as the standard idealized sampling interface; the
single-experiment Born distribution is the cited public theorem.
-/

namespace Qatlib.Papers.NoncommHSP98.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.StabilizerAlg.NearUniformGen
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.ExactSimon97.MainResults

section UniformSubgroup

variable {G : Type} [AddCommGroup G] [Fintype G]

/-- The sum of `1/c` over a finite set is the normalized cardinality. -/
theorem sum_one_div {ι : Type*} {c : ℝ} (s : Finset ι) :
    ∑ _g ∈ s, (1 : ℝ) / c = (s.card : ℝ) / c := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, ih]
    push_cast
    ring

/-- The uniform law on a finite subgroup, viewed as a distribution on the ambient group. -/
noncomputable def unifOnSub (H : AddSubgroup G) : FinDist G where
  prob g := if g ∈ H then 1 / (Fintype.card ↥H : ℝ) else 0
  nonneg g := by
    have hposc : (0 : ℝ) < Fintype.card ↥H := by exact_mod_cast Fintype.card_pos
    split
    · exact div_nonneg zero_le_one (le_of_lt hposc)
    · exact le_refl 0
  sum_one := by
    classical
    have hpos : (0 : ℝ) < Fintype.card ↥H := by exact_mod_cast Fintype.card_pos
    have hcard : (Finset.univ.filter (fun g => g ∈ H) : Finset G).card =
        Fintype.card ↥H := by
      have himg : (Finset.univ.filter (fun g => g ∈ H) : Finset G) =
          (Finset.univ.image (Subtype.val : ↥H → G)) := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hg
          exact ⟨⟨g, hg⟩, rfl⟩
        · rintro ⟨x, rfl⟩
          exact x.2
      rw [himg, Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ]
    calc ∑ g : G, (if g ∈ H then 1 / (Fintype.card ↥H : ℝ) else 0)
        = ∑ g ∈ (Finset.univ.filter (fun g => g ∈ H) : Finset G),
            1 / (Fintype.card ↥H : ℝ) := by rw [Finset.sum_filter]
      _ = ((Finset.univ.filter (fun g => g ∈ H) : Finset G).card : ℝ) /
            (Fintype.card ↥H : ℝ) := sum_one_div _
      _ = 1 := by
          rw [hcard]
          exact div_self hpos.ne'

/-- Summing the uniform subgroup law over a finite set of subgroup elements gives the
normalized cardinality, so the near-uniformness condition of
`nearUniformGenerationSubgoal` holds with `δ = 0`. -/
theorem unifOnSub_exact (H : AddSubgroup G) (L : Finset ↥H) :
    ∑ g ∈ L, (unifOnSub H).prob (g : G) = (L.card : ℝ) / (Fintype.card ↥H : ℝ) := by
  classical
  have hpos : (0 : ℝ) < Fintype.card ↥H := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ g ∈ L, (unifOnSub H).prob (g : G) = 1 / (Fintype.card ↥H : ℝ) := by
    intro g _
    simp [unifOnSub, g.2]
  rw [Finset.sum_congr rfl hterm]
  exact sum_one_div L

end UniformSubgroup

section ProbEventApi

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- The total mass of the independent sample-record law is one. -/
theorem probOfTotal {L : ℕ} (p : FinDist X) : ∑ ω : Fin L → X, p.probOf ω = 1 := by
  classical
  unfold FinDist.probOf
  show (∑ ω ∈ (Finset.univ : Finset (Fin L → X)), ∏ i, p.prob (ω i)) = 1
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  simp [p.sum_one]

omit [DecidableEq X] in
/-- The complementary event of an independent sample-record event has probability
`1 - p.probEvent E`. -/
theorem probEventCompl {L : ℕ} (p : FinDist X) (E : (Fin L → X) → Prop) [DecidablePred E] :
    p.probEvent (fun ω => ¬ E ω) = 1 - p.probEvent E := by
  classical
  have hsplit : (Finset.univ.filter (fun ω => ¬ E ω)).sum (p.probOf (L := L)) +
      (Finset.univ.filter (fun ω => E ω)).sum (p.probOf (L := L)) =
      ∑ ω, p.probOf (L := L) ω := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hE : E ω <;> simp [hE]
  unfold FinDist.probEvent
  linarith [hsplit, probOfTotal (L := L) p]

omit [DecidableEq X] in
/-- Pointwise-equal laws assign equal probabilities to sample-record events. -/
theorem probEventCongrLaw {L : ℕ} {p q : FinDist X} (h : ∀ g, p.prob g = q.prob g)
    (E : (Fin L → X) → Prop) [DecidablePred E] :
    p.probEvent E = q.probEvent E := by
  classical
  unfold FinDist.probEvent FinDist.probOf
  apply Finset.sum_congr rfl
  intro ω _
  exact Finset.prod_congr rfl (fun i _ => h (ω i))

end ProbEventApi

section Generation

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- `l` independent uniform samples of a finite Abelian subgroup fail to generate it with
probability strictly below `|H| · (1/2)^l`: the maximal-subgroup cover has fewer than
`|H|` members and each proper subgroup misses at least half of `H`. -/
theorem genFail_lt (H : AddSubgroup G) (l : ℕ) :
    FinDist.probEvent (L := l) (unifOnSub H)
        (fun hs => AddSubgroup.closure (Set.range hs) ≠ H) <
      (Fintype.card ↥H : ℝ) * (1 / 2 : ℝ) ^ l := by
  have hnear : ∀ L : Finset ↥H,
      |∑ g ∈ L, (unifOnSub H).prob (g : G) - (L.card : ℝ) / (Fintype.card ↥H : ℝ)| ≤ 0 := by
    intro L
    rw [unifOnSub_exact H L, sub_self, abs_zero]
  obtain ⟨maxs, -, -, hcount, hbound⟩ :=
    nearUniformGenerationSubgoal l G H (unifOnSub H) 0 (le_refl 0) hnear
  simp only [mul_zero, add_zero, zero_add, add_zero] at hbound
  have hcast : (maxs.card : ℝ) < (Fintype.card ↥H : ℝ) := by exact_mod_cast hcount
  calc FinDist.probEvent (L := l) (unifOnSub H)
        (fun hs => AddSubgroup.closure (Set.range hs) ≠ H)
      ≤ (maxs.card : ℝ) * (1 / 2 : ℝ) ^ l := by simpa only [zero_add] using hbound
    _ < (Fintype.card ↥H : ℝ) * (1 / 2 : ℝ) ^ l :=
        mul_lt_mul_of_pos_right hcast (by positivity)

/-- The number of uniform samples used by the Theorem 1 generation routine. -/
def genSampleCount (c : ℕ) : ℕ := 2 * (Nat.log 2 c + 1) + 1

/-- The sample count is `O(log c)`. -/
theorem genSampleCount_le (c : ℕ) : genSampleCount c ≤ 3 * Nat.log 2 c + 3 := by
  unfold genSampleCount
  omega

/-- At the Theorem 1 sample count the power-of-two denominator dominates `2 * c²`. -/
theorem two_pow_genSample {c : ℕ} (hc : 2 ≤ c) :
    2 * (c : ℝ) ^ 2 ≤ (2 : ℝ) ^ (genSampleCount c) := by
  have hpos : (0 : ℝ) < (c : ℝ) := Nat.cast_pos.mpr (by omega)
  have hhigh : c < 2 ^ (Nat.log 2 c).succ :=
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) c
  have hcastpow : ((2 : ℕ) ^ (Nat.log 2 c).succ : ℝ) =
      (2 : ℝ) ^ (Nat.log 2 c).succ := by
    push_cast
    rfl
  have h2k : (c : ℝ) < 2 * (2 : ℝ) ^ Nat.log 2 c := by
    have hlt : (c : ℝ) < ((2 : ℕ) ^ (Nat.log 2 c).succ : ℝ) := by exact_mod_cast hhigh
    rw [hcastpow, pow_succ] at hlt
    have hcomm : 2 * (2 : ℝ) ^ Nat.log 2 c = (2 : ℝ) ^ Nat.log 2 c * 2 :=
      mul_comm _ _
    linarith
  have hpow : (2 : ℝ) ^ (genSampleCount c) = 8 * ((2 : ℝ) ^ Nat.log 2 c) ^ 2 := by
    have hexp : genSampleCount c = 2 * Nat.log 2 c + 3 := by unfold genSampleCount; omega
    rw [hexp, pow_add]
    have h2k2 : 2 * Nat.log 2 c = Nat.log 2 c * 2 := by omega
    rw [h2k2, pow_mul]
    ring
  rw [hpow]
  have hsq : (c : ℝ) ^ 2 = 4 * ((c : ℝ) / 2) ^ 2 := by
    field_simp
    ring
  rw [hsq]
  have hd : (c : ℝ) / 2 ≤ (2 : ℝ) ^ Nat.log 2 c := by
    have hcomm : 2 * (2 : ℝ) ^ Nat.log 2 c = (2 : ℝ) ^ Nat.log 2 c * 2 := mul_comm _ _
    field_simp
    linarith
  nlinarith [hd, mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg ((c : ℝ) / 2))]

/-- One half to a power is the reciprocal of the matching power of two. -/
theorem halfPowInv (k : ℕ) : (1 / 2 : ℝ) ^ k = ((2 : ℝ) ^ k)⁻¹ := by
  rw [div_pow]
  norm_num

/-- With `l = genSampleCount |G|` uniform samples, the generated subgroup equals `H` with
probability at least `1 - 1/|G|`. This is the sampling core of Theorem 1. -/
theorem genSuccess_ge (H : AddSubgroup G) (hG : 2 ≤ Fintype.card G) :
    1 - 1 / (Fintype.card G : ℝ) ≤
      FinDist.probEvent (L := genSampleCount (Fintype.card G)) (unifOnSub H)
        (fun hs => AddSubgroup.closure (Set.range hs) = H) := by
  classical
  have hcGpos : (0 : ℝ) < (Fintype.card G : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  have hcardH : (Fintype.card ↥H : ℝ) ≤ (Fintype.card G : ℝ) := by
    have := Fintype.card_subtype_le (p := fun g => g ∈ H)
    exact_mod_cast this
  have hpow := two_pow_genSample (c := Fintype.card G) hG
  have hfail : FinDist.probEvent (L := genSampleCount (Fintype.card G)) (unifOnSub H)
      (fun hs => AddSubgroup.closure (Set.range hs) ≠ H) ≤ 1 / (Fintype.card G : ℝ) := by
    have hlt := genFail_lt H (genSampleCount (Fintype.card G))
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (genSampleCount (Fintype.card G)) := by positivity
    have hkey : (Fintype.card ↥H : ℝ) * (Fintype.card G : ℝ) ≤
        (2 : ℝ) ^ (genSampleCount (Fintype.card G)) := by
      have h4 : (Fintype.card G : ℝ) *
          ((Fintype.card G : ℝ) - (Fintype.card ↥H : ℝ)) ≥ 0 :=
        mul_nonneg hcGpos.le (by linarith)
      nlinarith [hpow, h4, sq_nonneg (Fintype.card G : ℝ)]
    have hbound : (Fintype.card ↥H : ℝ) * (1 / 2 : ℝ) ^
        (genSampleCount (Fintype.card G)) ≤ 1 / (Fintype.card G : ℝ) := by
      have hBpos : (0 : ℝ) < (1 / 2 : ℝ) ^ genSampleCount (Fintype.card G) := by positivity
      have h2lpos : (0 : ℝ) < (2 : ℝ) ^ genSampleCount (Fintype.card G) := by positivity
      have h3 : (2 : ℝ) ^ genSampleCount (Fintype.card G) *
          (1 / 2 : ℝ) ^ genSampleCount (Fintype.card G) = 1 := by
        rw [halfPowInv, mul_inv_cancel₀ h2lpos.ne']
      have h4 : (Fintype.card ↥H : ℝ) * (1 / 2 : ℝ) ^ genSampleCount (Fintype.card G) *
          (Fintype.card G : ℝ) ≤ 1 := by
        calc (Fintype.card ↥H : ℝ) * (1 / 2 : ℝ) ^ genSampleCount (Fintype.card G) *
                (Fintype.card G : ℝ)
            = ((Fintype.card ↥H : ℝ) * (Fintype.card G : ℝ)) *
                (1 / 2 : ℝ) ^ genSampleCount (Fintype.card G) := by ring
          _ ≤ (2 : ℝ) ^ genSampleCount (Fintype.card G) *
                (1 / 2 : ℝ) ^ genSampleCount (Fintype.card G) :=
              mul_le_mul_of_nonneg_right hkey hBpos.le
          _ = 1 := h3
      have hstep : (Fintype.card ↥H : ℝ) * (1 / 2 : ℝ) ^ genSampleCount (Fintype.card G) =
          ((Fintype.card ↥H : ℝ) * (1 / 2 : ℝ) ^ genSampleCount (Fintype.card G) *
            (Fintype.card G : ℝ)) * (Fintype.card G : ℝ)⁻¹ := by
        field_simp
      have key2 : ((Fintype.card ↥H : ℝ) * (1 / 2 : ℝ) ^ genSampleCount (Fintype.card G) *
          (Fintype.card G : ℝ)) * (Fintype.card G : ℝ)⁻¹ ≤
          1 / (Fintype.card G : ℝ) := by
        have h5 : ((Fintype.card ↥H : ℝ) * (1 / 2 : ℝ) ^ genSampleCount (Fintype.card G) *
            (Fintype.card G : ℝ)) * (Fintype.card G : ℝ)⁻¹ =
            ((Fintype.card ↥H : ℝ) * (1 / 2 : ℝ) ^ genSampleCount (Fintype.card G) *
            (Fintype.card G : ℝ)) * (1 / (Fintype.card G : ℝ)) := by
          rw [one_div (a := (Fintype.card G : ℝ))]
        rw [h5]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right h4 (div_nonneg zero_le_one hcGpos.le)
      rw [hstep]
      exact key2
    exact le_trans (le_of_lt hlt) hbound
  have hcompl := probEventCompl (L := genSampleCount (Fintype.card G)) (unifOnSub H)
    (fun hs => AddSubgroup.closure (Set.range hs) ≠ H)
  have hcongr := asp_probability_congr (genSampleCount (Fintype.card G)) (unifOnSub H)
    (fun hs : Fin (genSampleCount (Fintype.card G)) → G =>
      ¬(AddSubgroup.closure (Set.range hs) ≠ H))
    (fun hs => AddSubgroup.closure (Set.range hs) = H)
    (fun hs => by simp)
  rw [hcongr] at hcompl
  linarith

/-- The Abelian subgroup promise on an oracle `γ`: values agree exactly on cosets of `H`,
written additively. -/
def AbelianPromise (H : AddSubgroup G) {R : Type*} (γ : G → R) : Prop :=
  (∀ x y, (∃ h ∈ H, x + h = y) → γ x = γ y) ∧
    (∀ x y, γ x = γ y → ∃ h ∈ H, x + h = y)

/-- A generic uniform-subgroup sampling lemma: independent draws from the supplied
law generate `H` with the stated probability. Fourier sampling for a hidden subgroup
is uniform on its annihilator instead; the later recovery lemma applies this result
to that annihilator. No oracle-query circuit or its charge is constructed here. -/
theorem theorem1_generation (hG : 2 ≤ Fintype.card G) (H : AddSubgroup G)
    {R : Type*} (γ : G → R) (_hγ : AbelianPromise H γ) (μ : FinDist G)
    (hμ : ∀ g, μ.prob g = (unifOnSub H).prob g) :
    1 - 1 / (Fintype.card G : ℝ) ≤
      FinDist.probEvent (L := genSampleCount (Fintype.card G)) μ
        (fun hs => AddSubgroup.closure (Set.range hs) = H) := by
  rw [probEventCongrLaw hμ]
  exact genSuccess_ge H hG

end Generation

section Annihilator

variable {n : ℕ} {m : Fin n → ℕ} [hne : ∀ i, NeZero (m i)]

/-- A label in the annihilator of `K` pairs trivially with every element of `K`. -/
theorem annPair_eq_one {K : AddSubgroup (AbGroup n m)} {h k : AbGroup n m}
    (hh : h ∈ annihilatorGen K) (hk : k ∈ K) : charPair (m := m) h k = 1 := by
  have hmem : charPairChar (m := m) h ∈ characterAnnihilator K :=
    mem_annihilatorGen.mp hh
  have hval := (mem_characterAnnihilator K _).mp hmem ⟨k, hk⟩
  have heval : charPairChar (m := m) h (↑(⟨k, hk⟩ : ↥K)) = charPair (m := m) h k := rfl
  rwa [heval] at hval

/-- Two subgroups of a finite Abelian group that are nested with equal cardinality
coincide. -/
theorem addSubgroup_eq_of_le_of_card {G' : Type} [AddCommGroup G'] [Fintype G']
    {K L : AddSubgroup G'} (h : K ≤ L) (hc : Fintype.card ↥K = Fintype.card ↥L) :
    K = L := by
  classical
  have hmem : ∀ x : G', x ∈ K → x ∈ L := fun x hx =>
    SetLike.mem_coe.mp (SetLike.coe_subset_coe.mpr h (SetLike.mem_coe.mpr hx))
  have hinj : Function.Injective
      (fun (x : ↥K) => (⟨(x : G'), hmem (x : G') x.2⟩ : ↥L)) := by
    intro a b hab
    have h' : (a : G') = (b : G') := congrArg (fun y : ↥L => (y : G')) hab
    exact Subtype.ext h'
  have hcardimg : (Finset.image
      (fun (x : ↥K) => (⟨(x : G'), hmem (x : G') x.2⟩ : ↥L)) Finset.univ).card =
      Fintype.card ↥L := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    exact hc
  have hfull : (Finset.image
      (fun (x : ↥K) => (⟨(x : G'), hmem (x : G') x.2⟩ : ↥L)) Finset.univ) = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      (by rw [hcardimg, Finset.card_univ])
  apply AddSubgroup.ext
  intro g
  constructor
  · exact hmem g
  · intro hg
    have hmemimg : (⟨g, hg⟩ : ↥L) ∈ (Finset.image
        (fun (x : ↥K) => (⟨(x : G'), hmem (x : G') x.2⟩ : ↥L)) Finset.univ) := by
      rw [hfull]
      exact Finset.mem_univ _
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hmemimg
    have hgx : (x : G') = g := congrArg (fun y : ↥L => (y : G')) hx
    exact hgx ▸ x.2

/-- Every subgroup of a product of cyclic groups is contained in its double character
annihilator. -/
theorem le_annann (K : AddSubgroup (AbGroup n m)) :
    K ≤ annihilatorGen (annihilatorGen K) := by
  intro g hg
  rw [mem_annihilatorGen, mem_characterAnnihilator]
  intro h
  show charPair (m := m) g ↑h = 1
  rw [charPair_comm]
  exact annPair_eq_one h.2 hg

/-- The double character annihilator of a subgroup of a product of cyclic groups is the
subgroup itself, by `|ann K| * |K| = |G|`. -/
theorem annann_eq (K : AddSubgroup (AbGroup n m)) :
    annihilatorGen (annihilatorGen K) = K := by
  have hcard1 := card_annihilatorGen_mul (annihilatorGen K)
  have hcard2 := card_annihilatorGen_mul K
  have hpos : 0 < Fintype.card ↥(annihilatorGen K) := Fintype.card_pos
  have hcanc : Fintype.card ↥(annihilatorGen (annihilatorGen K)) *
      Fintype.card ↥(annihilatorGen K) =
      Fintype.card ↥K * Fintype.card ↥(annihilatorGen K) := by
    rw [hcard1, ← hcard2]
    exact mul_comm _ _
  have hcard : Fintype.card ↥(annihilatorGen (annihilatorGen K)) = Fintype.card ↥K :=
    Nat.mul_right_cancel hpos hcanc
  exact (addSubgroup_eq_of_le_of_card (le_annann K) hcard.symm).symm

/-- The Born probability of Fourier measurement of a coset state equals the uniform
subgroup law on the annihilator-label subgroup, so the sampling interface of
the generic sampling lemma applies to the annihilator subgroup, not the hidden
subgroup itself. -/
theorem fourierBorn_unif (K : AddSubgroup (AbGroup n m)) (s : AbGroup n m)
    (g : AbGroup n m) :
    BornProb (FG (m := m) (abelianCosetState K s)) g = (unifOnSub (annihilatorGen K)).prob g := by
  rw [bornProb_genCosetState_uniform]
  by_cases hg : g ∈ annihilatorGen K <;> simp [hg, unifOnSub]

/-- Theorem 1 for a product of cyclic groups: `genSampleCount |G|` uniform annihilator
labels — the per-experiment readout law of Fourier sampling on coset states of `K`, by
`fourierBorn_unif` — generate the annihilator, so re-annihilating their span recovers
`K` itself with probability at least `1 - 1/|G|`. The output of the procedure is the
generated subgroup, which is a generating set for the subgroup it names. -/
theorem theorem1_abelian_AbGroup (K : AddSubgroup (AbGroup n m))
    (hG : 2 ≤ Fintype.card (AbGroup n m)) :
    1 - 1 / (Fintype.card (AbGroup n m) : ℝ) ≤
      FinDist.probEvent (L := genSampleCount (Fintype.card (AbGroup n m)))
        (unifOnSub (annihilatorGen K))
        (fun hs => annihilatorGen (AddSubgroup.closure (Set.range hs)) = K) := by
  classical
  have hmono := asp_probability_mono (genSampleCount (Fintype.card (AbGroup n m)))
    (unifOnSub (annihilatorGen K))
    (E := fun hs => AddSubgroup.closure (Set.range hs) = annihilatorGen K)
    (F := fun hs => annihilatorGen (AddSubgroup.closure (Set.range hs)) = K)
    (fun hs hhs => by rw [hhs]; exact annann_eq K)
  exact le_trans (genSuccess_ge (annihilatorGen K) hG) hmono

end Annihilator

end Qatlib.Papers.NoncommHSP98.MainResults
