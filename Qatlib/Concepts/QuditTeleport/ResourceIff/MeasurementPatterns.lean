/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.MeasurementPatternsDefs
import Qatlib.Foundations.PureStateMath.BornBridge.PartialTraceCovariance
import Qatlib.Concepts.FiniteLocc.LOCCProgram.PositiveBranchDecomposition
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationInstrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.BellTeleportationInstrument
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditResourceMarginalConverse
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditMaxEntResourceTeleportation
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditPureResourceMaxEntForm
import Qatlib.Concepts.QuditTeleport.CommLowerBound.CommBoundRestrictedStat
import Qatlib.Concepts.QuditTeleport.QdLoccModel.RedundantCodingReliability
import Qatlib.Concepts.QuditTeleport.MessagingBounds.PrearrivalMessageGuessingStat
import Qatlib.Concepts.QuditTeleport.MessagingBounds.CollapsedMessageGuessingStat
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceMarginalConverse
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntResourceTeleportation
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditPureResourceMaxEntForm
import Qatlib.Concepts.QuditTeleport.CommLowerBound.CommBoundRestrictedTele
import Qatlib.Concepts.QuditTeleport.MessagingBounds.PrearrivalMessageGuessingTele
import Qatlib.Concepts.QuditTeleport.MessagingBounds.CollapsedMessageGuessingTele
import Qatlib.Concepts.QuditTeleport.MessagingBounds.RedundantCodingReliability

/-!
# LOCC teleportation branches and resource bounds

This module develops operator identities and leaf decompositions for finite LOCC teleportation
in the setting of [BennettEtAl1993Teleportation]. It proves that each leaf of a successful
protocol with a positive semidefinite resource acts on Bob's output as a scalar multiple of the
identity, and relates the number of leaves to the protocol's communication cost.

Polarization and positivity arguments reduce the branch analysis to pure inputs. For a
normalized pure resource, `pure_resource_scalar_bound` bounds the scalar of a contractive local
product branch by `1 / n²`.

## Main statements

* `eq_smul_id_of_posSummand`: a positive linear summand of the identity is scalar.
* `loccChannel_eq_sum_leafOps`: decomposition of an LOCC channel into local leaf operators.
* `loccLeafScalars_sum_one`: successful teleportation has leaf scalars summing to one.
* `loccLeafCount_le_two_pow_loccBits`: leaf count is bounded by the exponential of communication
  cost.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.BlockEncoding.LinearCombination

namespace Qatlib.Concepts.QuditTeleport.ResourceIff

open Qatlib.Concepts.QuditTeleport.ResourceIff
open Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds
open Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
open scoped Classical BigOperators ComplexOrder

/-- For every positive dimension, the actual qudit teleportation branches form an instrument
whose forgotten channel is the identity. Each outcome has probability `1 / n²` on density
operators and its conditional state is the input. -/
theorem clause1_conj1 :
    (∀ (n : ℕ) [NeZero n],
      ∃ I : Instrument (Fin n × Fin n) n n,
        (∀ (ρ : Operator n) (o : Fin n × Fin n), I.branch o ρ = quditActualBranchCore n o ρ) ∧
        (∀ ρ : Operator n, I.forget.map ρ = ρ) ∧
        (∀ (ρ : Operator n) (_hρ : IsDensityOperator ρ) (o : Fin n × Fin n),
          instrumentProb I ρ o = 1 / (n : ℝ) ^ 2 ∧
          ∀ hp : 0 < instrumentProb I ρ o, I.conditionalState ρ o hp = ρ)) :=
  qudit_actual_instrument_and_conditional_recovery

/-- Each corrected qubit teleportation branch acts as one quarter of the identity even with an
arbitrary finite reference system, and summing the branches recovers the joint operator. -/
theorem clause1_conj2 :
    (∀ (R : ℕ) (ρ : Matrix (Fin 2 × Fin R) (Fin 2 × Fin R) ℂ) (o : Bool × Bool),
      tensorLeft (teleportCorrectedInstrument.branch o) ρ = (1 / 4 : ℂ) • ρ ∧
        (∑ o : Bool × Bool, tensorLeft (teleportCorrectedInstrument.branch o) ρ) = ρ) :=
  bell_reference_channel_identity

/-- Collects the resource marginal converse, maximally entangled resource teleportation and pure
resource characterization together with the restricted communication, message guessing, and
redundant coding statements. -/
theorem clause1_conj5 :
    QuditResourceMarginalConverse ∧ QuditMaxEntResourceTeleportation ∧
      QuditPureResourceMaxEntForm ∧ CommBoundRestricted ∧
      PrearrivalMessageGuessing ∧ CollapsedMessageGuessing ∧ RedundantCodingReliability :=
  ⟨quditResourceMarginalConverse, quditMaxEntResourceTeleportation,
    quditPureResourceMaxEntForm, commBoundRestricted,
    prearrivalMessageGuessing, collapsedMessageGuessing, redundantCodingReliability⟩

/-- A positive semidefinite operator bounded above by `outerProduct v` is a scalar multiple of
that outer product. -/
theorem psd_summand_outerProduct {n : ℕ} (v : QState (Fin n)) (A : Operator n)
    (hA : A.PosSemidef) (hB : (outerProduct v - A).PosSemidef) :
    ∃ c : ℂ, A = c • outerProduct v := by
  classical
  have hker : ∀ w : Fin n → ℂ, Qatlib.Foundations.PureStateMath.Inner v w = 0 → A *ᵥ w = 0 := by
    intro w hw
    have hsum : star w ⬝ᵥ (A *ᵥ w) + star w ⬝ᵥ ((outerProduct v - A) *ᵥ w) = 0 := by
      rw [← dotProduct_add, ← Matrix.add_mulVec, add_sub_cancel, outerProduct_mulVec, hw,
        zero_smul, dotProduct_zero]
    have hre : (star w ⬝ᵥ (A *ᵥ w)).re = 0 := by
      have hre2 := congrArg Complex.re hsum
      simp only [Complex.add_re, Complex.zero_re] at hre2
      have h1 : 0 ≤ (star w ⬝ᵥ (A *ᵥ w)).re := hA.re_dotProduct_nonneg w
      have h2 : 0 ≤ (star w ⬝ᵥ ((outerProduct v - A) *ᵥ w)).re := hB.re_dotProduct_nonneg w
      linarith
    have hi : (star w ⬝ᵥ (A *ᵥ w)).im = 0 :=
      (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg w)).2.symm
    have hq : star w ⬝ᵥ (A *ᵥ w) = 0 := by
      apply Complex.ext <;> simp [hre, hi]
    exact hA.dotProduct_mulVec_zero_iff.mp hq
  by_cases hv : v = 0
  · subst hv
    refine ⟨0, ?_⟩
    have hzero : A = 0 := by
      ext i j
      have h :=
          hker (Qatlib.Foundations.PureStateMath.Ket j)
          (by simp [Qatlib.Foundations.PureStateMath.Inner])
      have hcon := congrFun h i
      rw [mulVec_ket_apply] at hcon
      simpa using! hcon
    simp [hzero]
  · obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin n, v i₀ ≠ 0 := by
      simpa only [ne_eq, funext_iff, not_forall] using! hv
    have hvi₀ : star (v i₀) ≠ 0 := by simp [hi₀]
    have hkey : ∀ (k j : Fin n), star (v i₀) * A k j = star (v j) * A k i₀ := by
      intro k j
      let w : Fin n → ℂ :=
          star (v j) • Qatlib.Foundations.PureStateMath.Ket i₀ - star
          (v i₀) • Qatlib.Foundations.PureStateMath.Ket j
      have hIn : Qatlib.Foundations.PureStateMath.Inner v w = 0 := by
        rw [inner_apply]
        simp only [starRingEnd_apply, w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub]
        rw [Finset.sum_sub_distrib]
        have hs0 : (∑ x, star (v x) * (star (v j) * Qatlib.Foundations.PureStateMath.Ket i₀ x)) = star (v j) * star (v i₀) := by
          have h1 : (∑ x, star (v x) * (star (v j) * Qatlib.Foundations.PureStateMath.Ket i₀ x)) =
              (∑ x, star (v j) * (star (v x) * Qatlib.Foundations.PureStateMath.Ket i₀ x)) :=
            Finset.sum_congr rfl (fun x _ => by ring)
          rw [h1, ← Finset.mul_sum]
          have h2 : (∑ x, star (v x) * Qatlib.Foundations.PureStateMath.Ket i₀ x) = star (v i₀) := by
            rw [Finset.sum_eq_single i₀]
            · simp
            · intro b _ hb
              simp [Qatlib.Foundations.PureStateMath.Ket, hb]
            · intro hi
              exact absurd (Finset.mem_univ i₀) hi
          rw [h2]
        have hs1 : (∑ x, star (v x) * (star (v i₀) * Qatlib.Foundations.PureStateMath.Ket j x)) = star (v i₀) * star (v j) := by
          have h1 : (∑ x, star (v x) * (star (v i₀) * Qatlib.Foundations.PureStateMath.Ket j x)) =
              (∑ x, star (v i₀) * (star (v x) * Qatlib.Foundations.PureStateMath.Ket j x)) :=
            Finset.sum_congr rfl (fun x _ => by ring)
          rw [h1, ← Finset.mul_sum]
          have h2 : (∑ x, star (v x) * Qatlib.Foundations.PureStateMath.Ket j x) = star (v j) := by
            rw [Finset.sum_eq_single j]
            · simp
            · intro b _ hb
              simp [Qatlib.Foundations.PureStateMath.Ket, hb]
            · intro hi
              exact absurd (Finset.mem_univ j) hi
          rw [h2]
        rw [hs0, hs1]
        ring
      have hAw := hker w hIn
      have hcon := congrFun hAw k
      simp only [w, Matrix.mulVec_sub, Matrix.mulVec_smul, mulVec_ket_apply,
        Pi.sub_apply, Pi.smul_apply] at hcon
      exact (eq_of_sub_eq_zero hcon).symm
    have hherm : ∀ (a b : Fin n), A a b = star (A b a) := by
      intro a b
      have hh := congrFun (congrFun hA.1 a) b
      simp only [Matrix.conjTranspose_apply] at hh
      exact hh.symm
    refine ⟨star (A i₀ i₀) / (v i₀ * star (v i₀)), ?_⟩
    ext k j
    simp only [Matrix.smul_apply, outerProduct_apply, starRingEnd_apply, smul_eq_mul]
    have hrow' : ∀ a : Fin n, v i₀ * A a i₀ = v a * star (A i₀ i₀) := by
      intro a
      have h1 : star (star (v i₀) * A i₀ a) = star (star (v a) * A i₀ i₀) :=
        congrArg star (hkey i₀ a)
      simp only [star_mul', star_star] at h1
      rw [← hherm a i₀] at h1
      exact h1
    have hcne : v i₀ * star (v i₀) ≠ 0 := mul_ne_zero hi₀ hvi₀
    have hcross : A k j * (v i₀ * star (v i₀)) = star (A i₀ i₀) * v k * star (v j) := by
      calc A k j * (v i₀ * star (v i₀)) = (star (v i₀) * A k j) * v i₀ := by ring
        _ = (star (v j) * A k i₀) * v i₀ := by rw [hkey k j]
        _ = star (v j) * (v i₀ * A k i₀) := by ring
        _ = star (v j) * (v k * star (A i₀ i₀)) := by rw [hrow' k]
        _ = star (A i₀ i₀) * v k * star (v j) := by ring
    have hdiv : A k j = star (A i₀ i₀) * v k * star (v j) / (v i₀ * star (v i₀)) :=
      eq_div_of_mul_eq hcne hcross
    rw [hdiv, div_mul_eq_mul_div]
    ring

/-- The rank one operator `|v⟩⟨w|`, with entries `v i * star (w j)`. -/
private noncomputable def ketBra {n : ℕ} (v w : QState (Fin n)) : Operator n :=
  Matrix.of fun i j => v i * star (w j)

/-- Evaluates the entries of `ketBra v w` as `v i * star (w j)`. -/
private theorem ketBra_apply {n : ℕ} (v w : QState (Fin n)) (i j : Fin n) :
    ketBra v w i j = v i * star (w j) := rfl

/-- Expresses `ketBra v w` as a complex linear combination of four outer products by
polarization. -/
private theorem ketBra_polarization {n : ℕ} (v w : QState (Fin n)) :
    ketBra v w = (1 / 4 : ℂ) • (outerProduct (v + w) - outerProduct (v - w)) +
      (Complex.I / 4) •
        (outerProduct (v + (Complex.I : ℂ) • w) - outerProduct (v - (Complex.I : ℂ) • w)) := by
  ext i j
  simp only [ketBra_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    outerProduct_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    starRingEnd_apply, star_add, star_sub, star_mul]
  have hI : star (Complex.I : ℂ) = -Complex.I := by
    rw [Complex.star_def]
    exact Complex.conj_I
  rw [hI]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Expands `outerProduct (v + t • w)` into the two diagonal outer products and the two mixed
ket bra terms. -/
private theorem outerProduct_add_smul {n : ℕ} (v w : QState (Fin n)) (t : ℂ) :
    outerProduct (v + t • w) =
      outerProduct v + star t • ketBra v w + t • ketBra w v + (t * star t) • outerProduct w := by
  ext i j
  simp only [outerProduct_apply, Matrix.add_apply, Matrix.smul_apply, ketBra_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, starRingEnd_apply, star_add, star_mul]
  ring

/-- Expands an operator in the matrix units formed from computational basis ket bra operators. -/
private theorem matrix_eq_sum_ketBra {n : ℕ} (σ : Operator n) :
    σ = ∑ k : Fin n, ∑ l : Fin n, σ k l • ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, ketBra_apply, smul_eq_mul]
  have hx : ∀ x : Fin n,
      (∑ x_1, σ x x_1 * (Qatlib.Foundations.PureStateMath.Ket x i * star (Qatlib.Foundations.PureStateMath.Ket x_1 j))) = if i = x then σ x j else 0 := by
    intro x
    by_cases hix : i = x
    · subst hix
      rw [Finset.sum_eq_single j]
      · simp [Qatlib.Foundations.PureStateMath.Ket]
      · intro b _ hb
        have hbj : ¬ (j = b) := Ne.symm hb
        simp [Qatlib.Foundations.PureStateMath.Ket, hbj]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    · have hz : ∀ x_1, σ x x_1 * (Qatlib.Foundations.PureStateMath.Ket x i * star (Qatlib.Foundations.PureStateMath.Ket x_1 j)) = 0 := by
        intro x_1
        simp [Qatlib.Foundations.PureStateMath.Ket, hix]
      simp only [hz, Finset.sum_const_zero, if_neg hix]
  rw [Finset.sum_congr rfl (fun x _ => hx x)]
  simp

/-- A complex linear map that fixes every outer product fixes every operator. -/
theorem eq_of_outerProduct_fixed {n : ℕ} (G : Operator n → Operator n)
    (hadd : ∀ A B : Operator n, G (A + B) = G A + G B)
    (hsmul : ∀ (c : ℂ) (A : Operator n), G (c • A) = c • G A)
    (hfix : ∀ v : QState (Fin n), G (outerProduct v) = outerProduct v) :
    ∀ σ : Operator n, G σ = σ := by
  classical
  have hmap_sum : ∀ (ι : Type) (s : Finset ι) (f : ι → Operator n),
      G (∑ i ∈ s, f i) = ∑ i ∈ s, G (f i) := by
    intro ι s f
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      have key : G ((0 : ℂ) • (0 : Operator n)) = (0 : ℂ) • G 0 := hsmul 0 0
      rw [smul_zero, zero_smul] at key
      exact key
    | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  have hsub : ∀ A B : Operator n, G (A - B) = G A - G B := by
    intro A B
    have h1 : (A - B : Operator n) = A + (-1 : ℂ) • B := by
      rw [neg_one_smul, sub_eq_add_neg]
    rw [h1, hadd, hsmul, neg_one_smul]
    exact (sub_eq_add_neg _ _).symm
  have hbra : ∀ v w : QState (Fin n), G (ketBra v w) = ketBra v w := by
    intro v w
    rw [ketBra_polarization, hadd, hsmul, hsmul, hsub, hsub, hfix, hfix, hfix, hfix]
  intro σ
  have hsum : σ = ∑ k : Fin n, ∑ l : Fin n, σ k l • ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l) :=
    matrix_eq_sum_ketBra σ
  rw [hsum, hmap_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [hmap_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [hsmul, hbra]

/-- If a complex linear map scales each outer product individually, its scalars agree on any two
distinct computational basis vectors. It scales both associated off diagonal matrix units by
that common scalar. -/
private theorem posSummand_basis_pair {n : ℕ} (M : Operator n → Operator n)
    (hadd : ∀ A B : Operator n, M (A + B) = M A + M B)
    (hsmul : ∀ (c : ℂ) (A : Operator n), M (c • A) = c • M A)
    (s : QState (Fin n) → ℂ)
    (hs : ∀ v : QState (Fin n), M (outerProduct v) = s v • outerProduct v)
    (k l : Fin n) (hkl : k ≠ l) :
    s (Qatlib.Foundations.PureStateMath.Ket k) = s (Qatlib.Foundations.PureStateMath.Ket l) ∧
      M (ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l)) = s (Qatlib.Foundations.PureStateMath.Ket k) • ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l) ∧
      M (ketBra (Qatlib.Foundations.PureStateMath.Ket l) (Qatlib.Foundations.PureStateMath.Ket k)) = s (Qatlib.Foundations.PureStateMath.Ket k) • ketBra (Qatlib.Foundations.PureStateMath.Ket l) (Qatlib.Foundations.PureStateMath.Ket k) := by
  have hlk : l ≠ k := Ne.symm hkl
  set X : Operator n := M (ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l)) with hX
  set Y : Operator n := M (ketBra (Qatlib.Foundations.PureStateMath.Ket l) (Qatlib.Foundations.PureStateMath.Ket k)) with hY
  have vk : ∀ t : ℂ, (Qatlib.Foundations.PureStateMath.Ket k + t • Qatlib.Foundations.PureStateMath.Ket l : QState (Fin n)) k = 1 := by
    intro t
    simp [Qatlib.Foundations.PureStateMath.Ket, Pi.add_apply, Pi.smul_apply, hkl]
  have vl : ∀ t : ℂ, (Qatlib.Foundations.PureStateMath.Ket k + t • Qatlib.Foundations.PureStateMath.Ket l : QState (Fin n)) l = t := by
    intro t
    simp [Qatlib.Foundations.PureStateMath.Ket, Pi.add_apply, Pi.smul_apply, hlk]
  have ekk : ∀ t : ℂ, outerProduct (Qatlib.Foundations.PureStateMath.Ket k + t • Qatlib.Foundations.PureStateMath.Ket l : QState (Fin n)) k k = 1 := by
    intro t
    simp only [outerProduct_apply, vk, starRingEnd_apply]
    simp
  have ekl : ∀ t : ℂ, outerProduct (Qatlib.Foundations.PureStateMath.Ket k + t • Qatlib.Foundations.PureStateMath.Ket l : QState (Fin n)) k l = star t := by
    intro t
    simp only [outerProduct_apply, vk, vl, starRingEnd_apply, one_mul]
  have ell : ∀ t : ℂ, outerProduct (Qatlib.Foundations.PureStateMath.Ket k + t • Qatlib.Foundations.PureStateMath.Ket l : QState (Fin n)) l l = t * star t := by
    intro t
    simp only [outerProduct_apply, vl, starRingEnd_apply]
  have fkk : outerProduct (Qatlib.Foundations.PureStateMath.Ket k : QState (Fin n)) k k = 1 :=
      by simp [outerProduct_apply]
  have fkl : outerProduct (Qatlib.Foundations.PureStateMath.Ket k : QState (Fin n)) k l = 0 :=
      by simp [outerProduct_apply, ket_ne hlk]
  have fll : outerProduct (Qatlib.Foundations.PureStateMath.Ket k : QState (Fin n)) l l = 0 :=
      by simp [outerProduct_apply, ket_ne hlk]
  have gkk : outerProduct (Qatlib.Foundations.PureStateMath.Ket l : QState (Fin n)) k k = 0 :=
      by simp [outerProduct_apply, ket_ne hkl]
  have gkl : outerProduct (Qatlib.Foundations.PureStateMath.Ket l : QState (Fin n)) k l = 0 :=
      by simp [outerProduct_apply, ket_ne hkl]
  have gll : outerProduct (Qatlib.Foundations.PureStateMath.Ket l : QState (Fin n)) l l = 1 :=
      by simp [outerProduct_apply]
  have hopij : ∀ (t : ℂ) (i j : Fin n),
      outerProduct (Qatlib.Foundations.PureStateMath.Ket k + t • Qatlib.Foundations.PureStateMath.Ket l) i j =
        outerProduct (Qatlib.Foundations.PureStateMath.Ket k) i j + star t * ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l) i j +
          t * ketBra (Qatlib.Foundations.PureStateMath.Ket l) (Qatlib.Foundations.PureStateMath.Ket k) i j + (t * star t) * outerProduct (Qatlib.Foundations.PureStateMath.Ket l) i j := by
    intro t i j
    have h :=
        congrFun (congrFun (outerProduct_add_smul (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l) t) i) j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h
    exact h
  have hmain : ∀ t : ℂ,
      s (Qatlib.Foundations.PureStateMath.Ket k + t • Qatlib.Foundations.PureStateMath.Ket l) • outerProduct (Qatlib.Foundations.PureStateMath.Ket k + t • Qatlib.Foundations.PureStateMath.Ket l) =
        s (Qatlib.Foundations.PureStateMath.Ket k) • outerProduct (Qatlib.Foundations.PureStateMath.Ket k) + star t • X + t • Y +
          (t * star t) • s (Qatlib.Foundations.PureStateMath.Ket l) • outerProduct (Qatlib.Foundations.PureStateMath.Ket l) := by
    intro t
    rw [← hs (Qatlib.Foundations.PureStateMath.Ket k + t • Qatlib.Foundations.PureStateMath.Ket l), outerProduct_add_smul (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l) t,
      hadd, hadd, hadd,
      hsmul (star t) (ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l)),
      hsmul t (ketBra (Qatlib.Foundations.PureStateMath.Ket l) (Qatlib.Foundations.PureStateMath.Ket k)),
      hsmul (t * star t) (outerProduct (Qatlib.Foundations.PureStateMath.Ket l)),
      hs (Qatlib.Foundations.PureStateMath.Ket k), hs (Qatlib.Foundations.PureStateMath.Ket l), ← hX, ← hY]
  have Ekk : ∀ t : ℂ, s (Qatlib.Foundations.PureStateMath.Ket k + t • Qatlib.Foundations.PureStateMath.Ket l) = s (Qatlib.Foundations.PureStateMath.Ket k) + star t * X k k + t * Y k k := by
    intro t
    have h := congrFun (congrFun (hmain t) k) k
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h
    rw [ekk, fkk, gkk] at h
    linear_combination h
  have Ekl : ∀ t : ℂ, s (Qatlib.Foundations.PureStateMath.Ket k + t • Qatlib.Foundations.PureStateMath.Ket l) * star t = star t * X k l + t * Y k l := by
    intro t
    have h := congrFun (congrFun (hmain t) k) l
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h
    rw [ekl, fkl, gkl] at h
    linear_combination h
  have Ell : ∀ t : ℂ, s (Qatlib.Foundations.PureStateMath.Ket k + t • Qatlib.Foundations.PureStateMath.Ket l) * (t * star t) =
      star t * X l l + t * Y l l + (t * star t) * s (Qatlib.Foundations.PureStateMath.Ket l) := by
    intro t
    have h := congrFun (congrFun (hmain t) l) l
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h
    rw [ell, fll, gll] at h
    linear_combination h
  have star1 : star (1 : ℂ) = 1 := by simp
  have starm1 : star (-1 : ℂ) = -1 := by simp
  have starI : star (Complex.I : ℂ) = -Complex.I := by rw [Complex.star_def]; exact Complex.conj_I
  have starmI : star (-Complex.I : ℂ) = Complex.I := by rw [Complex.star_def]; simp
  have Ekk1 : s (Qatlib.Foundations.PureStateMath.Ket k + (1:ℂ) • Qatlib.Foundations.PureStateMath.Ket l) = s (Qatlib.Foundations.PureStateMath.Ket k) + X k k + Y k k := by
    have h := Ekk 1
    rw [star1] at h
    linear_combination h
  have Ekl1 : s (Qatlib.Foundations.PureStateMath.Ket k + (1:ℂ) • Qatlib.Foundations.PureStateMath.Ket l) = X k l + Y k l := by
    have h := Ekl 1
    rw [star1] at h
    linear_combination h
  have EkkM : s (Qatlib.Foundations.PureStateMath.Ket k + (-1:ℂ) • Qatlib.Foundations.PureStateMath.Ket l) = s (Qatlib.Foundations.PureStateMath.Ket k) - X k k - Y k k := by
    have h := Ekk (-1)
    rw [starm1] at h
    linear_combination h
  have EklM : s (Qatlib.Foundations.PureStateMath.Ket k + (-1:ℂ) • Qatlib.Foundations.PureStateMath.Ket l) = X k l + Y k l := by
    have h := Ekl (-1)
    rw [starm1] at h
    linear_combination -h
  have EkkI : s (Qatlib.Foundations.PureStateMath.Ket k + Complex.I • Qatlib.Foundations.PureStateMath.Ket l) =
      s (Qatlib.Foundations.PureStateMath.Ket k) + (-Complex.I) * X k k + Complex.I * Y k k := by
    have h := Ekk Complex.I
    rw [starI] at h
    linear_combination h
  have EklI : s (Qatlib.Foundations.PureStateMath.Ket k + Complex.I • Qatlib.Foundations.PureStateMath.Ket l) = X k l - Y k l := by
    have h := Ekl Complex.I
    rw [starI] at h
    linear_combination h * Complex.I +
      Complex.I_sq * (s (Qatlib.Foundations.PureStateMath.Ket k + Complex.I • Qatlib.Foundations.PureStateMath.Ket l) - X k l + Y k l)
  have EkkMI : s (Qatlib.Foundations.PureStateMath.Ket k + (-Complex.I) • Qatlib.Foundations.PureStateMath.Ket l) =
      s (Qatlib.Foundations.PureStateMath.Ket k) + Complex.I * X k k + (-Complex.I) * Y k k := by
    have h := Ekk (-Complex.I)
    rw [starmI] at h
    linear_combination h
  have EklMI : s (Qatlib.Foundations.PureStateMath.Ket k + (-Complex.I) • Qatlib.Foundations.PureStateMath.Ket l) = X k l - Y k l := by
    have h := Ekl (-Complex.I)
    rw [starmI] at h
    linear_combination h * (-Complex.I) +
      Complex.I_sq * (s (Qatlib.Foundations.PureStateMath.Ket k + (-Complex.I) • Qatlib.Foundations.PureStateMath.Ket l) - X k l + Y k l)
  have Ell1 : s (Qatlib.Foundations.PureStateMath.Ket k + (1:ℂ) • Qatlib.Foundations.PureStateMath.Ket l) = X l l + Y l l + s (Qatlib.Foundations.PureStateMath.Ket l) := by
    have h := Ell 1
    rw [star1] at h
    linear_combination h
  have EllM : s (Qatlib.Foundations.PureStateMath.Ket k + (-1:ℂ) • Qatlib.Foundations.PureStateMath.Ket l) = -X l l - Y l l + s (Qatlib.Foundations.PureStateMath.Ket l) := by
    have h := Ell (-1)
    rw [starm1] at h
    linear_combination h
  have hab : s (Qatlib.Foundations.PureStateMath.Ket k + (1:ℂ) • Qatlib.Foundations.PureStateMath.Ket l) = s (Qatlib.Foundations.PureStateMath.Ket k + (-1:ℂ) • Qatlib.Foundations.PureStateMath.Ket l) := by
    linear_combination Ekl1 - EklM
  have hcd : s (Qatlib.Foundations.PureStateMath.Ket k + Complex.I • Qatlib.Foundations.PureStateMath.Ket l) = s (Qatlib.Foundations.PureStateMath.Ket k + (-Complex.I) • Qatlib.Foundations.PureStateMath.Ket l) := by
    linear_combination EklI - EklMI
  have hxy : X k k + Y k k = 0 := by
    linear_combination (EkkM - Ekk1 + hab) / 2
  have hxy2a : (2 * Complex.I) * (X k k - Y k k) = 0 := by
    linear_combination EkkI - EkkMI - hcd
  have hxy2 : X k k - Y k k = 0 := by
    cases mul_eq_zero.mp hxy2a with
    | inl h => exact absurd h (mul_ne_zero (by norm_num) Complex.I_ne_zero)
    | inr h => exact h
  have hxkk : X k k = 0 := by linear_combination (hxy + hxy2) / 2
  have hykk : Y k k = 0 := by linear_combination (hxy - hxy2) / 2
  have ha : s (Qatlib.Foundations.PureStateMath.Ket k + (1:ℂ) • Qatlib.Foundations.PureStateMath.Ket l) = s (Qatlib.Foundations.PureStateMath.Ket k) := by
    linear_combination Ekk1 + hxkk + hykk
  have hcI : s (Qatlib.Foundations.PureStateMath.Ket k + Complex.I • Qatlib.Foundations.PureStateMath.Ket l) = s (Qatlib.Foundations.PureStateMath.Ket k) := by
    linear_combination EkkI - Complex.I * hxkk + Complex.I * hykk
  have hsumkl : X k l + Y k l = s (Qatlib.Foundations.PureStateMath.Ket k) := by
    linear_combination ha - Ekl1
  have hdiffkl : X k l - Y k l = s (Qatlib.Foundations.PureStateMath.Ket k) := by
    linear_combination hcI - EklI
  have hykl : Y k l = 0 := by linear_combination (hsumkl - hdiffkl) / 2
  have hxkl : X k l = s (Qatlib.Foundations.PureStateMath.Ket k) := by
    linear_combination (hsumkl + hdiffkl) / 2
  have hcL : s (Qatlib.Foundations.PureStateMath.Ket k) = s (Qatlib.Foundations.PureStateMath.Ket l) := by
    linear_combination (Ell1 + EllM - 2 * ha + hab) / 2
  have M1 : ∀ i j : Fin n,
      X i j + Y i j = s (Qatlib.Foundations.PureStateMath.Ket k) * (ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l) i j + ketBra (Qatlib.Foundations.PureStateMath.Ket l) (Qatlib.Foundations.PureStateMath.Ket k) i j) := by
    intro i j
    have h := congrFun (congrFun (hmain 1) i) j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star1, one_mul] at h
    rw [ha, ← hcL] at h
    have hop1 := hopij 1 i j
    simp only [star1, one_mul, mul_one] at hop1
    rw [hop1] at h
    linear_combination -h
  have M2 : ∀ i j : Fin n,
      X i j - Y i j = s (Qatlib.Foundations.PureStateMath.Ket k) * (ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l) i j - ketBra (Qatlib.Foundations.PureStateMath.Ket l) (Qatlib.Foundations.PureStateMath.Ket k) i j) := by
    intro i j
    have h := congrFun (congrFun (hmain Complex.I) i) j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, starI] at h
    simp only [mul_neg, Complex.I_mul_I, neg_neg, one_mul, neg_mul] at h
    rw [hcI, ← hcL] at h
    have hop1 := hopij Complex.I i j
    simp only [starI, mul_neg, Complex.I_mul_I, neg_neg, one_mul, neg_mul] at hop1
    rw [hop1] at h
    linear_combination h * (-Complex.I) +
      Complex.I_sq * (X i j - Y i j - s (Qatlib.Foundations.PureStateMath.Ket k) *
        (ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l) i j - ketBra (Qatlib.Foundations.PureStateMath.Ket l) (Qatlib.Foundations.PureStateMath.Ket k) i j))
  refine ⟨hcL, ?_, ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    linear_combination (M1 i j + M2 i j) / 2
  · ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    linear_combination (M1 i j - M2 i j) / 2

/-- A complex linear map on a nonzero dimensional operator space is a scalar multiple of the
identity if both it and its complement preserve positive semidefiniteness. -/
theorem eq_smul_id_of_posSummand {n : ℕ} [NeZero n] (M : Operator n → Operator n)
    (hadd : ∀ A B : Operator n, M (A + B) = M A + M B)
    (hsmul : ∀ (c : ℂ) (A : Operator n), M (c • A) = c • M A)
    (hpos : ∀ A : Operator n, A.PosSemidef → (M A).PosSemidef)
    (hcomp : ∀ A : Operator n, A.PosSemidef → (A - M A).PosSemidef) :
    ∃ c : ℂ, ∀ σ : Operator n, M σ = c • σ := by
  classical
  have hcv : ∀ v : QState (Fin n), ∃ c : ℂ, M (outerProduct v) = c • outerProduct v := by
    intro v
    exact psd_summand_outerProduct v (M (outerProduct v))
      (hpos _ (outerProduct_posSemidef v)) (hcomp _ (outerProduct_posSemidef v))
  set s : QState (Fin n) → ℂ := fun v => Classical.choose (hcv v) with hsdef
  have hs : ∀ v : QState (Fin n), M (outerProduct v) = s v • outerProduct v := by
    intro v
    show M (outerProduct v) = Classical.choose (hcv v) • outerProduct v
    exact Classical.choose_spec (hcv v)
  set k₀ : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  have hconst : ∀ k : Fin n, s (Qatlib.Foundations.PureStateMath.Ket k) = s (Qatlib.Foundations.PureStateMath.Ket k₀) := by
    intro k
    by_cases hk : k = k₀
    · rw [hk]
    · exact (posSummand_basis_pair M hadd hsmul s hs k₀ k (Ne.symm hk)).1.symm
  have hbasis : ∀ k l : Fin n,
      M (ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l)) = s (Qatlib.Foundations.PureStateMath.Ket k₀) • ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l) := by
    intro k l
    by_cases hkl : k = l
    · subst hkl
      have h1 : ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket k) = outerProduct (Qatlib.Foundations.PureStateMath.Ket k) := by
        ext i j
        simp only [ketBra_apply, outerProduct_apply, starRingEnd_apply]
      rw [h1, hs, hconst]
    · have hp := posSummand_basis_pair M hadd hsmul s hs k l hkl
      rw [hp.2.1, hconst]
  have hmap_sum : ∀ (ι : Type) (t : Finset ι) (f : ι → Operator n),
      M (∑ i ∈ t, f i) = ∑ i ∈ t, M (f i) := by
    intro ι t f
    induction t using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      have key : M ((0 : ℂ) • (0 : Operator n)) = (0 : ℂ) • M 0 := hsmul 0 0
      rw [smul_zero, zero_smul] at key
      exact key
    | @insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  refine ⟨s (Qatlib.Foundations.PureStateMath.Ket k₀), ?_⟩
  intro σ
  have hsumexp := matrix_eq_sum_ketBra σ
  have hterm : ∀ k l : Fin n,
      M (σ k l • ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l)) = s (Qatlib.Foundations.PureStateMath.Ket k₀) • (σ k l • ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l)) := by
    intro k l
    rw [hsmul, hbasis, smul_smul, smul_smul, mul_comm]
  have hleft : M σ = ∑ k : Fin n, ∑ l : Fin n, s (Qatlib.Foundations.PureStateMath.Ket k₀) • (σ k l • ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l)) :=
    calc M σ = M (∑ k : Fin n, ∑ l : Fin n, σ k l • ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l)) :=
          congrArg M hsumexp
      _ = ∑ k : Fin n, M (∑ l : Fin n, σ k l • ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l)) := by
          rw [hmap_sum]
      _ = ∑ k : Fin n, ∑ l : Fin n, M (σ k l • ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l)) :=
          Finset.sum_congr rfl fun k _ =>
            hmap_sum (Fin n) Finset.univ fun l => σ k l • ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l)
      _ = ∑ k : Fin n, ∑ l : Fin n, s (Qatlib.Foundations.PureStateMath.Ket k₀) • (σ k l • ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l)) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hterm k l
  have hright : (∑ k : Fin n, ∑ l : Fin n, s (Qatlib.Foundations.PureStateMath.Ket k₀) • (σ k l • ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l))) =
      s (Qatlib.Foundations.PureStateMath.Ket k₀) • σ :=
    calc (∑ k : Fin n, ∑ l : Fin n, s (Qatlib.Foundations.PureStateMath.Ket k₀) • (σ k l • ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l)))
        = ∑ k : Fin n, s (Qatlib.Foundations.PureStateMath.Ket k₀) • ∑ l : Fin n, σ k l • ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l) :=
          Finset.sum_congr rfl fun k _ => by rw [Finset.smul_sum]
      _ = s (Qatlib.Foundations.PureStateMath.Ket k₀) • ∑ k : Fin n, ∑ l : Fin n, σ k l • ketBra (Qatlib.Foundations.PureStateMath.Ket k) (Qatlib.Foundations.PureStateMath.Ket l) := by
          rw [Finset.smul_sum]
      _ = s (Qatlib.Foundations.PureStateMath.Ket k₀) • σ := congrArg (fun x => s (Qatlib.Foundations.PureStateMath.Ket k₀) • x) hsumexp.symm
  rw [hleft, hright]

/-- Every natural number is bounded by two raised to the ceiling of its base two logarithm. -/
theorem nat_le_two_pow_ceil_log (n : ℕ) :
    n ≤ 2 ^ (Nat.ceil (Real.log n / Real.log 2)) := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases n with _ | n
  · simp
  · have hdiv : Real.log ((n + 1 : ℕ) : ℝ) / Real.log 2 ≤
        (Nat.ceil (Real.log ((n + 1 : ℕ) : ℝ) / Real.log 2) : ℕ) :=
      Nat.le_ceil _
    have hmul : Real.log ((n + 1 : ℕ) : ℝ) ≤
        (Nat.ceil (Real.log ((n + 1 : ℕ) : ℝ) / Real.log 2) : ℕ) * Real.log 2 :=
      (div_le_iff₀ h2).mp hdiv
    have hlog : Real.log ((2 : ℝ) ^ (Nat.ceil (Real.log ((n + 1 : ℕ) : ℝ) / Real.log 2))) =
        (Nat.ceil (Real.log ((n + 1 : ℕ) : ℝ) / Real.log 2) : ℕ) * Real.log 2 :=
      Real.log_pow _ _
    have hnpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have h2pos : 0 < (2 : ℝ) ^ (Nat.ceil (Real.log ((n + 1 : ℕ) : ℝ) / Real.log 2)) := by positivity
    have hle : ((n + 1 : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (Nat.ceil (Real.log ((n + 1 : ℕ) : ℝ) / Real.log 2)) := by
      rw [← Real.log_le_log_iff hnpos h2pos, hlog]
      exact hmul
    exact_mod_cast hle

/-- The number of leaves of an LOCC protocol is at most `2 ^ LoccBits proto`. -/
theorem loccLeafCount_le_two_pow_loccBits {D E : ℕ} (proto : LoccProtocol D E) :
    LoccLeafCount proto ≤ 2 ^ LoccBits proto := by
  induction proto with
  | halt => simp [LoccLeafCount, LoccBits]
  | stepA n ks next ih =>
    have hsup : ∀ i : Fin n, LoccBits (next i) ≤
        Finset.univ.sup fun i => LoccBits (next i) :=
      fun i => Finset.le_sup (f := fun j => LoccBits (next j)) (Finset.mem_univ i)
    have hsum : (Finset.univ.sum fun i => LoccLeafCount (next i)) ≤
        (Finset.univ.sum fun i => 2 ^ LoccBits (next i)) :=
      Finset.sum_le_sum fun i _ => ih i
    have hpow : (Finset.univ.sum fun i => 2 ^ LoccBits (next i)) ≤
        (Finset.univ.sum fun _ : Fin n => 2 ^ (Finset.univ.sup fun i => LoccBits (next i))) :=
      Finset.sum_le_sum fun i _ => pow_le_pow_right₀ (by norm_num) (hsup i)
    have hcard : (Finset.univ.sum fun _ : Fin n =>
        2 ^ (Finset.univ.sup fun i => LoccBits (next i))) =
        n * 2 ^ (Finset.univ.sup fun i => LoccBits (next i)) := by
      rw [Finset.sum_const, Finset.card_fin, smul_eq_mul]
    have hceil : n ≤ 2 ^ (Nat.ceil (Real.log n / Real.log 2)) :=
      nat_le_two_pow_ceil_log n
    calc
      LoccLeafCount (LoccProtocol.stepA n ks next)
          = Finset.univ.sum fun i => LoccLeafCount (next i) := rfl
      _ ≤ Finset.univ.sum fun i => 2 ^ LoccBits (next i) := hsum
      _ ≤ Finset.univ.sum fun _ : Fin n =>
          2 ^ (Finset.univ.sup fun i => LoccBits (next i)) := hpow
      _ = n * 2 ^ (Finset.univ.sup fun i => LoccBits (next i)) := hcard
      _ ≤ 2 ^ (Nat.ceil (Real.log n / Real.log 2)) *
          2 ^ (Finset.univ.sup fun i => LoccBits (next i)) :=
        Nat.mul_le_mul_right _ hceil
      _ = 2 ^ (Nat.ceil (Real.log n / Real.log 2) +
          Finset.univ.sup fun i => LoccBits (next i)) := (pow_add _ _ _).symm
      _ = 2 ^ LoccBits (LoccProtocol.stepA n ks next) := rfl
  | stepB n ks next ih =>
    have hsup : ∀ i : Fin n, LoccBits (next i) ≤
        Finset.univ.sup fun i => LoccBits (next i) :=
      fun i => Finset.le_sup (f := fun j => LoccBits (next j)) (Finset.mem_univ i)
    have hsum : (Finset.univ.sum fun i => LoccLeafCount (next i)) ≤
        (Finset.univ.sum fun i => 2 ^ LoccBits (next i)) :=
      Finset.sum_le_sum fun i _ => ih i
    have hpow : (Finset.univ.sum fun i => 2 ^ LoccBits (next i)) ≤
        (Finset.univ.sum fun _ : Fin n => 2 ^ (Finset.univ.sup fun i => LoccBits (next i))) :=
      Finset.sum_le_sum fun i _ => pow_le_pow_right₀ (by norm_num) (hsup i)
    have hcard : (Finset.univ.sum fun _ : Fin n =>
        2 ^ (Finset.univ.sup fun i => LoccBits (next i))) =
        n * 2 ^ (Finset.univ.sup fun i => LoccBits (next i)) := by
      rw [Finset.sum_const, Finset.card_fin, smul_eq_mul]
    have hceil : n ≤ 2 ^ (Nat.ceil (Real.log n / Real.log 2)) :=
      nat_le_two_pow_ceil_log n
    calc
      LoccLeafCount (LoccProtocol.stepB n ks next)
          = Finset.univ.sum fun i => LoccLeafCount (next i) := rfl
      _ ≤ Finset.univ.sum fun i => 2 ^ LoccBits (next i) := hsum
      _ ≤ Finset.univ.sum fun _ : Fin n =>
          2 ^ (Finset.univ.sup fun i => LoccBits (next i)) := hpow
      _ = n * 2 ^ (Finset.univ.sup fun i => LoccBits (next i)) := hcard
      _ ≤ 2 ^ (Nat.ceil (Real.log n / Real.log 2)) *
          2 ^ (Finset.univ.sup fun i => LoccBits (next i)) :=
        Nat.mul_le_mul_right _ hceil
      _ = 2 ^ (Nat.ceil (Real.log n / Real.log 2) +
          Finset.univ.sup fun i => LoccBits (next i)) := (pow_add _ _ _).symm
      _ = 2 ^ LoccBits (LoccProtocol.stepB n ks next) := rfl

/-- Any lower bound on an LOCC protocol's leaf count is also a lower bound on `2 ^ LoccBits
proto`. -/
theorem loccBits_pow_ge_of_leafCount {D E : ℕ} {proto : LoccProtocol D E} {m : ℕ}
    (h : m ≤ LoccLeafCount proto) : m ≤ 2 ^ LoccBits proto :=
  h.trans (loccLeafCount_le_two_pow_loccBits proto)

/-- Lists the pairs of accumulated local operators along all leaves of an LOCC protocol,
composing each local step with the operators of its continuation. -/
noncomputable def loccLeafOps {D E : ℕ} : LoccProtocol D E → List (Operator D × Operator E)
  | .halt => [(1, 1)]
  | .stepA _ ks next => Finset.univ.toList.flatMap fun i =>
      (loccLeafOps (next i)).map fun p => (p.1 * ks i, p.2)
  | .stepB _ ks next => Finset.univ.toList.flatMap fun i =>
      (loccLeafOps (next i)).map fun p => (p.1, p.2 * ks i)

/-- Rewrites a mapped sum over a flattened list as the sum of the mapped sums over its
constituent lists. -/
private theorem list_sum_flatMap {α β γ : Type} [AddCommMonoid γ] (l : List α)
    (f : α → List β) (g : β → γ) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.flatMap_cons, List.map_cons, List.sum_cons, List.map_append,
      List.sum_append, ih]

/-- Moves fixed left and right matrix factors outside a mapped list sum. -/
private theorem list_sum_map_sandwich {α ι : Type} [Fintype ι] [DecidableEq ι] (l : List α)
    (A B : Matrix ι ι ℂ) (g : α → Matrix ι ι ℂ) :
    (l.map fun x => A * g x * B).sum = A * (l.map g).sum * B := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [List.map_cons, List.sum_cons]
    noncomm_ring

/-- Splits a mapped list sum into the contribution of a chosen member and the sum after erasing
one occurrence. -/
private theorem list_map_sum_erase {α : Type} {m : ℕ} (f : α → Operator m) :
    ∀ (l : List α) (p : α), p ∈ l → (l.map f).sum = f p + ((l.erase p).map f).sum := by
  classical
  intro l
  induction l with
  | nil => intro p hp; cases hp
  | cons x l ih =>
    intro p hp
    by_cases hx : x = p
    · subst hx
      simp [List.erase_cons_head]
    · rw [List.erase_cons_tail (by simp [hx])]
      simp only [List.map_cons, List.sum_cons]
      rw [ih p (List.mem_of_ne_of_mem (fun h => hx h.symm) hp)]
      abel

/-- Conjugation by a tensor product of local operator products equals successive conjugation by
the corresponding tensor product operators. -/
private theorem tensorGate_sandwich_mul {D E : ℕ} (a a' : Operator D) (b b' : Operator E)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    TensorGate (a * a') (b * b') * ρ * (TensorGate (a * a') (b * b'))ᴴ =
      TensorGate a b * (TensorGate a' b' * ρ * (TensorGate a' b')ᴴ) * (TensorGate a b)ᴴ := by
  rw [← tensorGate_mul, Matrix.conjTranspose_mul]
  noncomm_ring

/-- A finite sum in the first factor commutes with `TensorGate`. -/
private theorem sum_tensorGate_left {I J m : ℕ} (f : Fin m → Operator I) (g : Operator J) :
    (∑ i : Fin m, TensorGate (f i) g) = TensorGate (∑ i : Fin m, f i) g := by
  ext x y
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [Matrix.sum_apply, tensorGate_apply, Finset.sum_mul]

/-- A finite sum in the second factor commutes with `TensorGate`. -/
private theorem sum_tensorGate_right {I J m : ℕ} (g : Operator I) (f : Fin m → Operator J) :
    (∑ i : Fin m, TensorGate g (f i)) = TensorGate g (∑ i : Fin m, f i) := by
  ext x y
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [Matrix.sum_apply, tensorGate_apply, Finset.mul_sum]

set_option maxHeartbeats 1000000

/-- Expresses an LOCC channel as the sum of conjugations by the tensor products of its leaf
operators. -/
theorem loccChannel_eq_sum_leafOps {D E : ℕ} (P : LoccProtocol D E)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    LoccChannel P ρ =
      ((loccLeafOps P).map fun p => TensorGate p.1 p.2 * ρ * (TensorGate p.1 p.2)ᴴ).sum := by
  induction P generalizing ρ with
  | halt =>
    simp only [loccLeafOps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, tensorGate_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    rfl
  | stepA m ks next ih =>
    have hkey : ∀ (i : Fin m) (p : Operator D × Operator E),
        TensorGate (p.1 * ks i) p.2 * ρ * (TensorGate (p.1 * ks i) p.2)ᴴ =
          TensorGate p.1 p.2 * (TensorGate (ks i) (1 : Operator E) * ρ *
            (TensorGate (ks i) (1 : Operator E))ᴴ) * (TensorGate p.1 p.2)ᴴ := by
      intro i p
      have h := tensorGate_sandwich_mul p.1 (ks i) p.2 (1 : Operator E) ρ
      simpa [Matrix.mul_one] using! h
    calc LoccChannel (LoccProtocol.stepA m ks next) ρ
        = ∑ i : Fin m, LoccChannel (next i)
            (TensorGate (ks i) (1 : Operator E) * ρ * (TensorGate (ks i) (1 : Operator E))ᴴ) := rfl
      _ = ∑ i : Fin m, ((loccLeafOps (next i)).map fun p =>
            TensorGate p.1 p.2 * (TensorGate (ks i) (1 : Operator E) * ρ *
              (TensorGate (ks i) (1 : Operator E))ᴴ) * (TensorGate p.1 p.2)ᴴ).sum :=
          Finset.sum_congr rfl fun i _ =>
            ih i (TensorGate (ks i) (1 : Operator E) * ρ *
              (TensorGate (ks i) (1 : Operator E))ᴴ)
      _ = ((Finset.univ.toList.flatMap fun i =>
              (loccLeafOps (next i)).map fun p => (p.1 * ks i, p.2)).map fun p =>
            TensorGate p.1 p.2 * ρ * (TensorGate p.1 p.2)ᴴ).sum :=
          calc (∑ i : Fin m, ((loccLeafOps (next i)).map fun p =>
                    TensorGate p.1 p.2 * (TensorGate (ks i) (1 : Operator E) * ρ *
                      (TensorGate (ks i) (1 : Operator E))ᴴ) * (TensorGate p.1 p.2)ᴴ).sum)
              = (∑ i : Fin m,
                    (((loccLeafOps (next i)).map fun p => (p.1 * ks i, p.2)).map fun p =>
                      TensorGate p.1 p.2 * ρ * (TensorGate p.1 p.2)ᴴ).sum) :=
                Finset.sum_congr rfl fun i _ => by
                  congr 1
                  rw [List.map_map]
                  exact List.map_congr_left fun p _ => (hkey i p).symm
            _ = (Finset.univ.toList.map fun i =>
                    (((loccLeafOps (next i)).map fun p => (p.1 * ks i, p.2)).map fun p =>
                      TensorGate p.1 p.2 * ρ * (TensorGate p.1 p.2)ᴴ).sum).sum :=
                (Finset.sum_map_toList _ _).symm
            _ = ((Finset.univ.toList.flatMap fun i =>
                    (loccLeafOps (next i)).map fun p => (p.1 * ks i, p.2)).map fun p =>
                  TensorGate p.1 p.2 * ρ * (TensorGate p.1 p.2)ᴴ).sum :=
                (list_sum_flatMap _ _ _).symm
      _ = ((loccLeafOps (LoccProtocol.stepA m ks next)).map fun p =>
            TensorGate p.1 p.2 * ρ * (TensorGate p.1 p.2)ᴴ).sum := rfl
  | stepB m ks next ih =>
    have hkey : ∀ (i : Fin m) (p : Operator D × Operator E),
        TensorGate p.1 (p.2 * ks i) * ρ * (TensorGate p.1 (p.2 * ks i))ᴴ =
          TensorGate p.1 p.2 * (TensorGate (1 : Operator D) (ks i) * ρ *
            (TensorGate (1 : Operator D) (ks i))ᴴ) * (TensorGate p.1 p.2)ᴴ := by
      intro i p
      have h := tensorGate_sandwich_mul p.1 (1 : Operator D) p.2 (ks i) ρ
      simpa [Matrix.one_mul] using! h
    calc LoccChannel (LoccProtocol.stepB m ks next) ρ
        = ∑ i : Fin m, LoccChannel (next i)
            (TensorGate (1 : Operator D) (ks i) * ρ * (TensorGate (1 : Operator D) (ks i))ᴴ) := rfl
      _ = ∑ i : Fin m, ((loccLeafOps (next i)).map fun p =>
            TensorGate p.1 p.2 * (TensorGate (1 : Operator D) (ks i) * ρ *
              (TensorGate (1 : Operator D) (ks i))ᴴ) * (TensorGate p.1 p.2)ᴴ).sum :=
          Finset.sum_congr rfl fun i _ =>
            ih i (TensorGate (1 : Operator D) (ks i) * ρ *
              (TensorGate (1 : Operator D) (ks i))ᴴ)
      _ = ((Finset.univ.toList.flatMap fun i =>
              (loccLeafOps (next i)).map fun p => (p.1, p.2 * ks i)).map fun p =>
            TensorGate p.1 p.2 * ρ * (TensorGate p.1 p.2)ᴴ).sum :=
          calc (∑ i : Fin m, ((loccLeafOps (next i)).map fun p =>
                    TensorGate p.1 p.2 * (TensorGate (1 : Operator D) (ks i) * ρ *
                      (TensorGate (1 : Operator D) (ks i))ᴴ) * (TensorGate p.1 p.2)ᴴ).sum)
              = (∑ i : Fin m,
                    (((loccLeafOps (next i)).map fun p => (p.1, p.2 * ks i)).map fun p =>
                      TensorGate p.1 p.2 * ρ * (TensorGate p.1 p.2)ᴴ).sum) :=
                Finset.sum_congr rfl fun i _ => by
                  congr 1
                  rw [List.map_map]
                  exact List.map_congr_left fun p _ => (hkey i p).symm
            _ = (Finset.univ.toList.map fun i =>
                    (((loccLeafOps (next i)).map fun p => (p.1, p.2 * ks i)).map fun p =>
                      TensorGate p.1 p.2 * ρ * (TensorGate p.1 p.2)ᴴ).sum).sum :=
                (Finset.sum_map_toList _ _).symm
            _ = ((Finset.univ.toList.flatMap fun i =>
                    (loccLeafOps (next i)).map fun p => (p.1, p.2 * ks i)).map fun p =>
                  TensorGate p.1 p.2 * ρ * (TensorGate p.1 p.2)ᴴ).sum :=
                (list_sum_flatMap _ _ _).symm
      _ = ((loccLeafOps (LoccProtocol.stepB m ks next)).map fun p =>
            TensorGate p.1 p.2 * ρ * (TensorGate p.1 p.2)ᴴ).sum := rfl

/-- The leaf count of an LOCC protocol equals the length of its list of local leaf operators. -/
theorem loccLeafCount_eq_length {D E : ℕ} (P : LoccProtocol D E) :
    LoccLeafCount P = (loccLeafOps P).length := by
  induction P with
  | halt => rfl
  | stepA m ks next ih =>
    calc LoccLeafCount (LoccProtocol.stepA m ks next)
        = ∑ i : Fin m, LoccLeafCount (next i) := rfl
      _ = ∑ i : Fin m, (loccLeafOps (next i)).length :=
          Finset.sum_congr rfl fun i _ => ih i
      _ = (Finset.univ.toList.map fun i => (loccLeafOps (next i)).length).sum :=
          (Finset.sum_map_toList _ _).symm
      _ = (Finset.univ.toList.flatMap fun i =>
            (loccLeafOps (next i)).map fun p => (p.1 * ks i, p.2)).length := by
          rw [List.length_flatMap]
          simp only [List.length_map]
      _ = (loccLeafOps (LoccProtocol.stepA m ks next)).length := rfl
  | stepB m ks next ih =>
    calc LoccLeafCount (LoccProtocol.stepB m ks next)
        = ∑ i : Fin m, LoccLeafCount (next i) := rfl
      _ = ∑ i : Fin m, (loccLeafOps (next i)).length :=
          Finset.sum_congr rfl fun i _ => ih i
      _ = (Finset.univ.toList.map fun i => (loccLeafOps (next i)).length).sum :=
          (Finset.sum_map_toList _ _).symm
      _ = (Finset.univ.toList.flatMap fun i =>
            (loccLeafOps (next i)).map fun p => (p.1, p.2 * ks i)).length := by
          rw [List.length_flatMap]
          simp only [List.length_map]
      _ = (loccLeafOps (LoccProtocol.stepB m ks next)).length := rfl

/-- For a complete LOCC protocol, the tensor products of its leaf operators satisfy the Kraus
completeness relation. -/
theorem loccComplete_leafOps {D E : ℕ} {P : LoccProtocol D E} (h : LoccComplete P) :
    ((loccLeafOps P).map fun p => (TensorGate p.1 p.2)ᴴ * TensorGate p.1 p.2).sum = 1 := by
  revert h
  induction P with
  | halt =>
    intro _
    simp [loccLeafOps, tensorGate_one, Matrix.conjTranspose_one]
  | stepA m ks next ih =>
    intro h
    obtain ⟨hK, hall⟩ := h
    have ih' : ∀ i : Fin m,
        ((loccLeafOps (next i)).map fun p => (TensorGate p.1 p.2)ᴴ * TensorGate p.1 p.2).sum = 1 :=
      fun i => ih i (hall i)
    have hsplit : ∀ (i : Fin m) (p : Operator D × Operator E),
        (TensorGate (p.1 * ks i) p.2)ᴴ * TensorGate (p.1 * ks i) p.2 =
          (TensorGate (ks i) (1 : Operator E))ᴴ *
            ((TensorGate p.1 p.2)ᴴ * TensorGate p.1 p.2) * TensorGate (ks i) (1 : Operator E) := by
      intro i p
      have h1 : TensorGate (p.1 * ks i) p.2 =
          TensorGate p.1 p.2 * TensorGate (ks i) (1 : Operator E) := by
        rw [tensorGate_mul, Matrix.mul_one]
      rw [h1, Matrix.conjTranspose_mul]
      noncomm_ring
    calc ((loccLeafOps (LoccProtocol.stepA m ks next)).map fun p =>
          (TensorGate p.1 p.2)ᴴ * TensorGate p.1 p.2).sum
        = ((Finset.univ.toList.flatMap fun i =>
              (loccLeafOps (next i)).map fun p => (p.1 * ks i, p.2)).map fun p =>
            (TensorGate p.1 p.2)ᴴ * TensorGate p.1 p.2).sum := rfl
      _ = (Finset.univ.toList.map fun i =>
              (((loccLeafOps (next i)).map fun p => (p.1 * ks i, p.2)).map fun p =>
                (TensorGate p.1 p.2)ᴴ * TensorGate p.1 p.2).sum).sum := list_sum_flatMap _ _ _
      _ = ∑ i : Fin m, (((loccLeafOps (next i)).map fun p => (p.1 * ks i, p.2)).map fun p =>
              (TensorGate p.1 p.2)ᴴ * TensorGate p.1 p.2).sum := Finset.sum_map_toList _ _
      _ = ∑ i : Fin m, ((loccLeafOps (next i)).map fun p =>
              (TensorGate (p.1 * ks i) p.2)ᴴ * TensorGate (p.1 * ks i) p.2).sum := by
            apply Finset.sum_congr rfl
            intro i _
            congr 1
            rw [List.map_map]
            exact List.map_congr_left fun p _ => rfl
      _ = ∑ i : Fin m, ((loccLeafOps (next i)).map fun p =>
              (TensorGate (ks i) (1 : Operator E))ᴴ *
                ((TensorGate p.1 p.2)ᴴ * TensorGate p.1 p.2) *
                TensorGate (ks i) (1 : Operator E)).sum := by
            apply Finset.sum_congr rfl
            intro i _
            congr 1
            exact List.map_congr_left fun p _ => hsplit i p
      _ = ∑ i : Fin m, (TensorGate (ks i) (1 : Operator E))ᴴ *
              ((loccLeafOps (next i)).map fun p =>
                (TensorGate p.1 p.2)ᴴ * TensorGate p.1 p.2).sum *
              TensorGate (ks i) (1 : Operator E) := by
            apply Finset.sum_congr rfl
            intro i _
            exact list_sum_map_sandwich _ _ _ _
      _ = ∑ i : Fin m,
              (TensorGate (ks i) (1 : Operator E))ᴴ * TensorGate (ks i) (1 : Operator E) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [ih' i, Matrix.mul_one]
      _ = ∑ i : Fin m, TensorGate ((ks i)ᴴ * ks i) (1 : Operator E) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [tensorGate_conjTranspose, Matrix.conjTranspose_one, tensorGate_mul,
              Matrix.mul_one]
      _ = TensorGate (∑ i : Fin m, (ks i)ᴴ * ks i) (1 : Operator E) := sum_tensorGate_left _ _
      _ = 1 := by rw [hK, tensorGate_one]
  | stepB m ks next ih =>
    intro h
    obtain ⟨hK, hall⟩ := h
    have ih' : ∀ i : Fin m,
        ((loccLeafOps (next i)).map fun p => (TensorGate p.1 p.2)ᴴ * TensorGate p.1 p.2).sum = 1 :=
      fun i => ih i (hall i)
    have hsplit : ∀ (i : Fin m) (p : Operator D × Operator E),
        (TensorGate p.1 (p.2 * ks i))ᴴ * TensorGate p.1 (p.2 * ks i) =
          (TensorGate (1 : Operator D) (ks i))ᴴ *
            ((TensorGate p.1 p.2)ᴴ * TensorGate p.1 p.2) * TensorGate (1 : Operator D) (ks i) := by
      intro i p
      have h1 : TensorGate p.1 (p.2 * ks i) =
          TensorGate p.1 p.2 * TensorGate (1 : Operator D) (ks i) := by
        rw [tensorGate_mul, Matrix.mul_one]
      rw [h1, Matrix.conjTranspose_mul]
      noncomm_ring
    calc ((loccLeafOps (LoccProtocol.stepB m ks next)).map fun p =>
          (TensorGate p.1 p.2)ᴴ * TensorGate p.1 p.2).sum
        = ((Finset.univ.toList.flatMap fun i =>
              (loccLeafOps (next i)).map fun p => (p.1, p.2 * ks i)).map fun p =>
            (TensorGate p.1 p.2)ᴴ * TensorGate p.1 p.2).sum := rfl
      _ = (Finset.univ.toList.map fun i =>
              (((loccLeafOps (next i)).map fun p => (p.1, p.2 * ks i)).map fun p =>
                (TensorGate p.1 p.2)ᴴ * TensorGate p.1 p.2).sum).sum := list_sum_flatMap _ _ _
      _ = ∑ i : Fin m, (((loccLeafOps (next i)).map fun p => (p.1, p.2 * ks i)).map fun p =>
              (TensorGate p.1 p.2)ᴴ * TensorGate p.1 p.2).sum := Finset.sum_map_toList _ _
      _ = ∑ i : Fin m, ((loccLeafOps (next i)).map fun p =>
              (TensorGate p.1 (p.2 * ks i))ᴴ * TensorGate p.1 (p.2 * ks i)).sum := by
            apply Finset.sum_congr rfl
            intro i _
            congr 1
            rw [List.map_map]
            exact List.map_congr_left fun p _ => rfl
      _ = ∑ i : Fin m, ((loccLeafOps (next i)).map fun p =>
              (TensorGate (1 : Operator D) (ks i))ᴴ *
                ((TensorGate p.1 p.2)ᴴ * TensorGate p.1 p.2) *
                TensorGate (1 : Operator D) (ks i)).sum := by
            apply Finset.sum_congr rfl
            intro i _
            congr 1
            exact List.map_congr_left fun p _ => hsplit i p
      _ = ∑ i : Fin m, (TensorGate (1 : Operator D) (ks i))ᴴ *
              ((loccLeafOps (next i)).map fun p =>
                (TensorGate p.1 p.2)ᴴ * TensorGate p.1 p.2).sum *
              TensorGate (1 : Operator D) (ks i) := by
            apply Finset.sum_congr rfl
            intro i _
            exact list_sum_map_sandwich _ _ _ _
      _ = ∑ i : Fin m,
              (TensorGate (1 : Operator D) (ks i))ᴴ * TensorGate (1 : Operator D) (ks i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [ih' i, Matrix.mul_one]
      _ = ∑ i : Fin m, TensorGate (1 : Operator D) ((ks i)ᴴ * ks i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [tensorGate_conjTranspose, Matrix.conjTranspose_one, tensorGate_mul,
              Matrix.mul_one]
      _ = TensorGate (1 : Operator D) (∑ i : Fin m, (ks i)ᴴ * ks i) := sum_tensorGate_right _ _
      _ = 1 := by rw [hK, tensorGate_one]

/-- The map on Bob's output obtained by adjoining resource `ω` to an input, applying the local
operators `a` and `b`, and tracing out Alice. -/
noncomputable def loccLeafMap {n : ℕ} (a : Operator (n * n)) (b : Operator n)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) : Operator n → Operator n :=
  fun ρ => loccBobMarginal n (TensorGate a b * teleportLoccJoint n ρ ω * (TensorGate a b)ᴴ)

/-- Taking Bob's marginal preserves addition. -/
theorem loccBobMarginal_add {n : ℕ}
    (X Y : Matrix (Fin (n * n) × Fin n) (Fin (n * n) × Fin n) ℂ) :
    loccBobMarginal n (X + Y) = loccBobMarginal n X + loccBobMarginal n Y := by
  simp only [loccBobMarginal, relabelGate, Matrix.reindex_apply, Matrix.submatrix_add,
    Pi.add_apply, partialTrace_add]

/-- Taking Bob's marginal preserves complex scalar multiplication. -/
theorem loccBobMarginal_smul {n : ℕ} (c : ℂ)
    (X : Matrix (Fin (n * n) × Fin n) (Fin (n * n) × Fin n) ℂ) :
    loccBobMarginal n (c • X) = c • loccBobMarginal n X := by
  simp only [loccBobMarginal, relabelGate, Matrix.reindex_apply, Matrix.submatrix_smul,
    Pi.smul_apply, partialTrace_smul]

/-- Bob's marginal of the zero operator is zero. -/
theorem loccBobMarginal_zero {n : ℕ} :
    loccBobMarginal n (0 : Matrix (Fin (n * n) × Fin n) (Fin (n * n) × Fin n) ℂ) = 0 := by
  have h := loccBobMarginal_smul (n := n) 0
    (0 : Matrix (Fin (n * n) × Fin n) (Fin (n * n) × Fin n) ℂ)
  simpa [zero_smul] using! h

/-- Adjoining a fixed teleportation resource preserves addition of input operators. -/
theorem teleportLoccJoint_add {n : ℕ} (ρ σ : Operator n)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    teleportLoccJoint n (ρ + σ) ω = teleportLoccJoint n ρ ω + teleportLoccJoint n σ ω := by
  ext x y
  simp only [teleportLoccJoint, Matrix.add_apply, add_mul]

/-- Adjoining a fixed teleportation resource preserves complex scalar multiplication of the
input. -/
theorem teleportLoccJoint_smul {n : ℕ} (c : ℂ) (ρ : Operator n)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    teleportLoccJoint n (c • ρ) ω = c • teleportLoccJoint n ρ ω := by
  ext x y
  simp only [teleportLoccJoint, Matrix.smul_apply, smul_eq_mul, mul_assoc]

/-- The map induced by a fixed pair of local leaf operators and a fixed resource preserves
addition. -/
theorem loccLeafMap_add {n : ℕ} {a : Operator (n * n)} {b : Operator n}
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (ρ σ : Operator n) :
    loccLeafMap a b ω (ρ + σ) = loccLeafMap a b ω ρ + loccLeafMap a b ω σ := by
  simp only [loccLeafMap, teleportLoccJoint_add, Matrix.mul_add, Matrix.add_mul,
    loccBobMarginal_add]

/-- The map induced by a fixed pair of local leaf operators and a fixed resource preserves
complex scalar multiplication. -/
theorem loccLeafMap_smul {n : ℕ} {a : Operator (n * n)} {b : Operator n}
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (c : ℂ) (ρ : Operator n) :
    loccLeafMap a b ω (c • ρ) = c • loccLeafMap a b ω ρ := by
  simp only [loccLeafMap, teleportLoccJoint_smul, Matrix.mul_smul, Matrix.smul_mul,
    loccBobMarginal_smul]

/-- Taking Bob's marginal commutes with a mapped list sum. -/
private theorem loccBobMarginal_list_sum {n : ℕ} {α : Type} (l : List α)
    (f : α → Matrix (Fin (n * n) × Fin n) (Fin (n * n) × Fin n) ℂ) :
    loccBobMarginal n (l.map f).sum = (l.map fun p => loccBobMarginal n (f p)).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, loccBobMarginal_zero]
  | cons x l ih => simp only [List.map_cons, List.sum_cons, loccBobMarginal_add, ih]

/-- For a successful LOCC teleportation protocol, the sum of all leaf maps recovers each input
density operator. -/
theorem loccTeleport_sum_leafMap {n : ℕ} [NeZero n]
    (proto : LoccProtocol (n * n) n) (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (h : LoccTeleportSuccess n proto ω) (ρ : Operator n) (hρ : IsDensityOperator ρ) :
    ((loccLeafOps proto).map fun p => loccLeafMap p.1 p.2 ω ρ).sum = ρ := by
  obtain ⟨_, htele⟩ := h
  have hchan := loccChannel_eq_sum_leafOps proto (teleportLoccJoint n ρ ω)
  have key := congrArg (loccBobMarginal n) hchan
  rw [loccBobMarginal_list_sum] at key
  rw [htele ρ hρ] at key
  simpa only [loccLeafMap] using! key.symm

/-- Regroups the input and resource indices into Alice's combined register and Bob's register. -/
private def loccJointEquiv (n : ℕ) : (Fin n × (Fin n × Fin n)) ≃ (Fin (n * n) × Fin n) :=
  (Equiv.prodAssoc (Fin n) (Fin n) (Fin n)).symm.trans
    ((finProdFinEquiv (m := n) (n := n)).prodCongr (Equiv.refl (Fin n)))

/-- The joint teleportation operator is the tensor product of the input and resource, relabeled
into the LOCC register convention. -/
theorem teleportLoccJoint_eq_relabel {n : ℕ} (ρ : Operator n)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    teleportLoccJoint n ρ ω = relabelGate (loccJointEquiv n) (TensorGate ρ ω) := by
  ext x y
  obtain ⟨u, b⟩ := x
  obtain ⟨v, d⟩ := y
  simp [teleportLoccJoint, tensorGate_apply, relabelGate, Matrix.reindex_apply,
    loccJointEquiv, Equiv.prodAssoc, Equiv.prodCongr, finProdFinEquiv]

/-- A local leaf map with a positive semidefinite resource sends positive semidefinite inputs to
positive semidefinite outputs. -/
theorem loccLeafMap_pos {n : ℕ} {a : Operator (n * n)} {b : Operator n}
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hω : ω.PosSemidef)
    (ρ : Operator n) (hρ : ρ.PosSemidef) :
    (loccLeafMap a b ω ρ).PosSemidef := by
  have hj : (teleportLoccJoint n ρ ω).PosSemidef := by
    rw [teleportLoccJoint_eq_relabel]
    exact converse_relabel_positive (loccJointEquiv n) _
      (Qatlib.Foundations.PureStateMath.BornBridge.posSemidef_tensorGate hρ hω)
  have hs : (TensorGate a b * teleportLoccJoint n ρ ω * (TensorGate a b)ᴴ).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using!
      hj.conjTranspose_mul_mul_same (TensorGate a b)ᴴ
  exact partialTrace_posSemidef (converse_relabel_positive _ _ hs)

/-- A local leaf map sends the zero operator to zero. -/
theorem loccLeafMap_zero {n : ℕ} {a : Operator (n * n)} {b : Operator n}
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    loccLeafMap a b ω (0 : Operator n) = 0 := by
  have h := @loccLeafMap_smul n a b ω (0 : ℂ) (0 : Operator n)
  simpa [zero_smul] using! h

/-- A mapped list sum vanishes when every mapped value is zero. -/
private theorem list_sum_map_zero {α : Type} {n : ℕ} (l : List α) (f : α → Operator n)
    (hf : ∀ p, f p = 0) : (l.map f).sum = 0 := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, hf, ih]; simp

/-- Moves a fixed complex scalar outside a mapped list sum of operators. -/
private theorem list_sum_map_smul {α : Type} {n : ℕ} (c : ℂ) (l : List α)
    (f : α → Operator n) : (l.map fun p => c • f p).sum = c • (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, smul_add]

/-- A list sum of scalar multiples of a fixed operator equals the sum of the scalars times that
operator. -/
private theorem list_sum_map_smul_const {α : Type} {n : ℕ} (l : List α) (c : α → ℂ)
    (X : Operator n) : (l.map fun p => c p • X).sum = ((l.map c).sum) • X := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, add_smul]

/-- A mapped list sum of positive semidefinite operators is positive semidefinite. -/
private theorem list_sum_posSemidef {n : ℕ} {α : Type} (l : List α) (f : α → Operator n)
    (hf : ∀ p, (f p).PosSemidef) : (l.map f).sum.PosSemidef := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil]; exact PosSemidef.zero
  | cons x l ih => simp only [List.map_cons, List.sum_cons]; exact (hf x).add ih

/-- In positive dimension, the outer product of the zeroth computational basis vector is a
density operator. -/
theorem isDensity_outerProduct_ket_zero {n : ℕ} [NeZero n] :
    IsDensityOperator (outerProduct (Qatlib.Foundations.PureStateMath.Ket (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n))) := by
  refine ⟨outerProduct_posSemidef _, ?_⟩
  show (∑ x, Qatlib.Foundations.PureStateMath.Ket (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n) x *
    star (Qatlib.Foundations.PureStateMath.Ket (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n) x)) = 1
  rw [Finset.sum_eq_single (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n)]
  · simp [Qatlib.Foundations.PureStateMath.Ket]
  · intro b _ hb
    have hb0 : b ≠ 0 := by simpa using! hb
    simp [Qatlib.Foundations.PureStateMath.Ket, hb0]
  · intro hk; exact absurd (Finset.mem_univ _) hk

/-- For a successful LOCC teleportation protocol, the sum of all leaf maps fixes every positive
semidefinite operator. -/
theorem loccTeleport_sum_leafMap_psd {n : ℕ} [NeZero n]
    (proto : LoccProtocol (n * n) n) (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (h : LoccTeleportSuccess n proto ω) (A : Operator n) (hA : A.PosSemidef) :
    ((loccLeafOps proto).map fun p => loccLeafMap p.1 p.2 ω A).sum = A := by
  by_cases ht : Matrix.trace A = 0
  · have hz : A = 0 := (PosSemidef.trace_eq_zero_iff hA).mp ht
    subst hz
    exact list_sum_map_zero _ _ fun p => loccLeafMap_zero ω
  · have hnn : 0 ≤ Matrix.trace A := PosSemidef.trace_nonneg hA
    have him : (Matrix.trace A).im = 0 := (Complex.nonneg_iff.mp hnn).2.symm
    have hre : 0 < (Matrix.trace A).re := by
      by_contra hlt
      have hre0 : (Matrix.trace A).re = 0 := by
        have h1 := (Complex.nonneg_iff.mp hnn).1
        linarith
      have hz : Matrix.trace A = 0 := by
        apply Complex.ext <;> simp [hre0, him]
      exact ht hz
    set t := (Matrix.trace A).re with htdef
    have hre' : 0 < t := by rw [htdef]; exact hre
    have htrace : Matrix.trace A = (t : ℂ) := by
      apply Complex.ext <;> simp [him, htdef]
    have hρ : IsDensityOperator (((1 / t : ℝ) : ℂ) • A) := by
      refine ⟨hA.smul ?_, ?_⟩
      · have h1 : (0:ℝ) ≤ 1 / t := by positivity
        exact Complex.nonneg_iff.mpr ⟨by simpa using! h1, by simp⟩
      · rw [trace_smul, smul_eq_mul, htrace]
        rw [← Complex.ofReal_mul, div_mul_cancel₀ _ (ne_of_gt hre'), Complex.ofReal_one]
    have hsum := loccTeleport_sum_leafMap proto ω h _ hρ
    have hkey : ∀ p : Operator (n * n) × Operator n,
        loccLeafMap p.1 p.2 ω (((1 / t : ℝ) : ℂ) • A) =
          ((1 / t : ℝ) : ℂ) • loccLeafMap p.1 p.2 ω A := fun p => loccLeafMap_smul ω _ _
    rw [show ((loccLeafOps proto).map fun p =>
              loccLeafMap p.1 p.2 ω (((1 / t : ℝ) : ℂ) • A)).sum =
          ((loccLeafOps proto).map fun p =>
            ((1 / t : ℝ) : ℂ) • loccLeafMap p.1 p.2 ω A).sum from
        congrArg List.sum (List.map_congr_left fun p _ => hkey p),
      list_sum_map_smul] at hsum
    have h3 : (((t : ℝ) : ℂ)) * (((1 / t : ℝ) : ℂ)) = 1 := by
      rw [← Complex.ofReal_mul, mul_comm, div_mul_cancel₀ _ (ne_of_gt hre'),
        Complex.ofReal_one]
    have h2 := congrArg (fun z : Operator n => (((t : ℝ) : ℂ)) • z) hsum
    simp only [smul_smul] at h2
    rw [h3, one_smul, one_smul] at h2
    exact h2

/-- For a successful LOCC teleportation protocol with a positive semidefinite resource,
subtracting any leaf output from a positive semidefinite input leaves a positive
semidefinite operator. -/
theorem loccLeafMap_compl_pos {n : ℕ} [NeZero n]
    (proto : LoccProtocol (n * n) n) (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hω : ω.PosSemidef) (h : LoccTeleportSuccess n proto ω)
    (p : Operator (n * n) × Operator n) (hp : p ∈ loccLeafOps proto)
    (A : Operator n) (hA : A.PosSemidef) :
    (A - loccLeafMap p.1 p.2 ω A).PosSemidef := by
  have her := list_map_sum_erase (fun q : Operator (n * n) × Operator n =>
    loccLeafMap q.1 q.2 ω A) (loccLeafOps proto) p hp
  have hsum := loccTeleport_sum_leafMap_psd proto ω h A hA
  rw [hsum] at her
  have her' : A = _ + loccLeafMap p.1 p.2 ω A := her.trans (add_comm _ _)
  have hsub : A - loccLeafMap p.1 p.2 ω A = _ := sub_eq_of_eq_add her'
  rw [hsub]
  exact list_sum_posSemidef _ _ (fun q => loccLeafMap_pos ω hω A hA)

/-- Each leaf map of a successful LOCC teleportation protocol with a positive semidefinite
resource is a scalar multiple of the identity on operators. -/
theorem loccLeafMap_eq_smul {n : ℕ} [NeZero n]
    (proto : LoccProtocol (n * n) n) (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hω : ω.PosSemidef) (h : LoccTeleportSuccess n proto ω)
    (p : Operator (n * n) × Operator n) (hp : p ∈ loccLeafOps proto) :
    ∃ c : ℂ, ∀ ρ : Operator n, loccLeafMap p.1 p.2 ω ρ = c • ρ :=
  eq_smul_id_of_posSummand (fun ρ => loccLeafMap p.1 p.2 ω ρ)
    (fun A B => loccLeafMap_add ω A B)
    (fun c A => loccLeafMap_smul ω c A)
    (fun A hA => loccLeafMap_pos ω hω A hA)
    (fun A hA => loccLeafMap_compl_pos proto ω hω h p hp A hA)

/-- Extracts a leaf map's scalar from its zeroth diagonal entry on the outer product of the
zeroth computational basis vector. -/
noncomputable def loccLeafScalar {n : ℕ} [NeZero n] (a : Operator (n * n)) (b : Operator n)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) : ℂ :=
  loccLeafMap a b ω (outerProduct (Qatlib.Foundations.PureStateMath.Ket (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n)))
    (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n)
    (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n)

/-- Every leaf map of a successful LOCC teleportation protocol with a positive semidefinite
resource scales all operators by its `loccLeafScalar`. -/
theorem loccLeafMap_smul_id_on_leaves {n : ℕ} [NeZero n]
    (proto : LoccProtocol (n * n) n) (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hω : ω.PosSemidef) (h : LoccTeleportSuccess n proto ω) :
    ∀ p ∈ loccLeafOps proto, ∀ ρ : Operator n,
      loccLeafMap p.1 p.2 ω ρ = loccLeafScalar p.1 p.2 ω • ρ := by
  intro p hp
  obtain ⟨c, hc⟩ := loccLeafMap_eq_smul proto ω hω h p hp
  have hsc : loccLeafScalar p.1 p.2 ω = c := by
    have h00 := congrFun (congrFun (hc
      (outerProduct (Qatlib.Foundations.PureStateMath.Ket (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n))))
      (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n))
      (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n)
    simp only [Matrix.smul_apply, outerProduct_apply] at h00
    simpa [loccLeafScalar, Qatlib.Foundations.PureStateMath.Ket] using! h00
  rw [hsc]
  exact hc

/-- The leaf scalars of a successful LOCC teleportation protocol with a positive semidefinite
resource sum to one. -/
theorem loccLeafScalars_sum_one {n : ℕ} [NeZero n]
    (proto : LoccProtocol (n * n) n) (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hω : ω.PosSemidef) (h : LoccTeleportSuccess n proto ω) :
    ((loccLeafOps proto).map fun p => loccLeafScalar p.1 p.2 ω).sum = 1 := by
  have hX := isDensity_outerProduct_ket_zero (n := n)
  have hsum := loccTeleport_sum_leafMap proto ω h _ hX
  have hkey : ∀ p ∈ loccLeafOps proto, loccLeafMap p.1 p.2 ω
        (outerProduct (Qatlib.Foundations.PureStateMath.Ket (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n))) =
      loccLeafScalar p.1 p.2 ω •
        (outerProduct (Qatlib.Foundations.PureStateMath.Ket (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n))) :=
    fun p hp => loccLeafMap_smul_id_on_leaves proto ω hω h p hp _
  rw [show ((loccLeafOps proto).map fun p => loccLeafMap p.1 p.2 ω
            (outerProduct (Qatlib.Foundations.PureStateMath.Ket (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n)))).sum =
        ((loccLeafOps proto).map fun p => loccLeafScalar p.1 p.2 ω •
          (outerProduct (Qatlib.Foundations.PureStateMath.Ket (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n)))).sum from
      congrArg List.sum (List.map_congr_left hkey),
    list_sum_map_smul_const] at hsum
  have h00 := congrFun (congrFun hsum
    (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n))
    (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n)
  simp only [Matrix.smul_apply, outerProduct_apply] at h00
  simpa [Qatlib.Foundations.PureStateMath.Ket] using! h00

/-- The product of an input vector and a resource vector, indexed by Alice's combined register
and Bob's register. -/
private def loccJointVec {n : ℕ} (ψ : QState (Fin n)) (W : QState (Fin n × Fin n)) :
    QState (Fin (n * n) × Fin n) :=
  fun x => ψ ((finProdFinEquiv (m := n) (n := n)).symm x.1).1 *
    W (((finProdFinEquiv (m := n) (n := n)).symm x.1).2, x.2)

/-- Adjoining two pure outer products gives the outer product of their joint vector. -/
private theorem teleportLoccJoint_outerProduct {n : ℕ} (ψ : QState (Fin n))
    (W : QState (Fin n × Fin n)) :
    teleportLoccJoint n (outerProduct ψ) (outerProduct W) = outerProduct (loccJointVec ψ W) := by
  ext x y
  obtain ⟨u, b⟩ := x
  obtain ⟨v, d⟩ := y
  simp only [teleportLoccJoint, loccJointVec, outerProduct_apply]
  rw [map_mul (starRingEnd ℂ)]
  ac_rfl

/-- Expresses a matrix vector product coordinate as the sum of matrix entries times vector
coordinates. -/
private theorem mulVec_eq_sum {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (x : QState ι) (i : ι) : (A *ᵥ x) i = ∑ j, A i j * x j := by
  simp [Matrix.mulVec, dotProduct]

/-- Conjugating an outer product by `K` gives the outer product of `K *ᵥ v`. -/
private theorem sandwich_outerProduct {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (v : QState ι) :
    K * outerProduct v * Kᴴ = outerProduct (K *ᵥ v) := by
  ext i j
  have hL : ∑ k, (∑ l, K i l * (v l * star (v k))) * star (K j k) =
      (∑ l, K i l * v l) * (∑ k, star (K j k) * star (v k)) := by
    have h1 : ∀ k : ι, (∑ l, K i l * (v l * star (v k))) * star (K j k) =
        (∑ l, K i l * v l) * (star (K j k) * star (v k)) := by
      intro k
      have h2 : (∑ l, K i l * (v l * star (v k))) = star (v k) * (∑ l, K i l * v l) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [h2]
      ring
    rw [Finset.sum_congr rfl fun k _ => h1 k, ← Finset.mul_sum]
  have hR : (K *ᵥ v) i * star ((K *ᵥ v) j) =
      (∑ l, K i l * v l) * (∑ k, star (K j k) * star (v k)) := by
    rw [mulVec_eq_sum, mulVec_eq_sum]
    have h2 : star (∑ k, K j k * v k) = ∑ k, star (K j k) * star (v k) := by
      rw [star_sum]
      exact Finset.sum_congr rfl fun k _ => (star_mul _ _).trans (mul_comm _ _)
    rw [h2]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, outerProduct_apply,
    ← Complex.star_def]
  exact hL.trans hR.symm

/-- Computes Bob's marginal of a pure outer product by summing over Alice's register. -/
private theorem loccBobMarginal_outerProduct {n : ℕ} (z : QState (Fin (n * n) × Fin n)) :
    loccBobMarginal n (outerProduct z) = fun k k' =>
      ∑ u : Fin (n * n), z (u, k) * star (z (u, k')) := by
  ext k k'
  simp only [loccBobMarginal, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    PartialTrace, outerProduct_apply]
  simp only [Equiv.prodComm]
  exact Finset.sum_congr rfl fun x _ => rfl

/-- If `1 - A` is positive semidefinite, the quadratic form of `A` is bounded above by the
squared norm form. -/
private theorem quad_le_of_psd_sub {m : Type} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (h : PosSemidef (1 - A)) (x : QState m) :
    star x ⬝ᵥ (A *ᵥ x) ≤ star x ⬝ᵥ x := by
  have hh := h.dotProduct_mulVec_nonneg x
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub] at hh
  have hh2 := Complex.nonneg_iff.mp hh
  refine Complex.le_def.mpr ⟨?_, ?_⟩
  · have hre := hh2.1
    simp only [Complex.sub_re] at hre
    linarith
  · have him := hh2.2
    simp only [Complex.sub_im] at him
    exact (sub_eq_zero.mp him.symm).symm

/-- A tensor product of matrices acts on a product vector by applying each matrix to its
corresponding factor. -/
private theorem tensorGate_mulVec_prod {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (U : Matrix I I ℂ) (V : Matrix J J ℂ)
    (x : QState I) (y : QState J) :
    TensorGate U V *ᵥ (fun p : I × J => x p.1 * y p.2) =
      fun p : I × J => (U *ᵥ x) p.1 * (V *ᵥ y) p.2 := by
  ext ⟨i, j⟩
  simp only [TensorGate, mulVec_eq_sum, Matrix.kroneckerMap_apply]
  rw [Fintype.sum_prod_type]
  have h1 : ∑ a, ∑ b, U i a * V j b * (x a * y b) =
      (∑ a, U i a * x a) * (∑ b, V j b * y b) := by
    have h2 : ∀ a, (∑ b, U i a * V j b * (x a * y b)) =
        (U i a * x a) * (∑ b, V j b * y b) := by
      intro a
      have h3 : ∀ b, U i a * V j b * (x a * y b) = (U i a * x a) * (V j b * y b) := fun b => by ring
      rw [Finset.sum_congr rfl fun b _ => h3 b, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun a _ => h2 a, ← Finset.sum_mul]
  exact h1

/-- If a row family's Gram matrix is a scalar multiple of the outer product of a nonzero vector,
every row is proportional to that vector. The scalar is the sum of the squared moduli of the
proportionality coefficients. -/
private theorem product_of_rank_one_gram {m n : ℕ} (Z : Fin m → Fin n → ℂ)
    (ψ : QState (Fin n)) (d : ℂ)
    (h : ∀ k k', ∑ u : Fin m, Z u k * star (Z u k') = d * ψ k * star (ψ k')) (hψ : ψ ≠ 0) :
    ∃ p : Fin m → ℂ, (∀ u k, Z u k = p u * ψ k) ∧ d = ∑ u, p u * star (p u) := by
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : Fin n, ψ k₀ ≠ 0 := by
    simpa only [ne_eq, funext_iff, not_forall] using! hψ
  have hne : ψ k₀ * star (ψ k₀) ≠ 0 := by
    intro hz
    rcases mul_eq_zero.mp hz with h | h
    · exact hk₀ h
    · exact hk₀ (star_eq_zero.mp h)
  have h00 : ∑ u : Fin m, Z u k₀ * star (Z u k₀) = d * (ψ k₀ * star (ψ k₀)) := by
    rw [h k₀ k₀, mul_assoc]
  have hcol : ∀ (u : Fin m) (k : Fin n), Z u k * ψ k₀ = Z u k₀ * ψ k := by
    intro u k
    have hsq : ∑ u' : Fin m, (Z u' k * ψ k₀ - Z u' k₀ * ψ k) *
        star (Z u' k * ψ k₀ - Z u' k₀ * ψ k) = 0 := by
      simp only [star_sub, star_mul, mul_sub, sub_mul, Finset.sum_sub_distrib]
      have e1 : (∑ x, Z x k * ψ k₀ * (star (ψ k₀) * star (Z x k))) =
          ψ k₀ * star (ψ k₀) * (d * ψ k * star (ψ k)) := by
        have h1 : ∀ x, Z x k * ψ k₀ * (star (ψ k₀) * star (Z x k)) =
            (ψ k₀ * star (ψ k₀)) * (Z x k * star (Z x k)) := fun x => by ring
        rw [Finset.sum_congr rfl fun x _ => h1 x, ← Finset.mul_sum, h k k]
      have e2 : (∑ x, Z x k₀ * ψ k * (star (ψ k₀) * star (Z x k))) =
          ψ k * star (ψ k₀) * (d * ψ k₀ * star (ψ k)) := by
        have h1 : ∀ x, Z x k₀ * ψ k * (star (ψ k₀) * star (Z x k)) =
            (ψ k * star (ψ k₀)) * (Z x k₀ * star (Z x k)) := fun x => by ring
        rw [Finset.sum_congr rfl fun x _ => h1 x, ← Finset.mul_sum, h k₀ k]
      have e3 : (∑ x, Z x k * ψ k₀ * (star (ψ k) * star (Z x k₀))) =
          ψ k₀ * star (ψ k) * (d * ψ k * star (ψ k₀)) := by
        have h1 : ∀ x, Z x k * ψ k₀ * (star (ψ k) * star (Z x k₀)) =
            (ψ k₀ * star (ψ k)) * (Z x k * star (Z x k₀)) := fun x => by ring
        rw [Finset.sum_congr rfl fun x _ => h1 x, ← Finset.mul_sum, h k k₀]
      have e4 : (∑ x, Z x k₀ * ψ k * (star (ψ k) * star (Z x k₀))) =
          ψ k * star (ψ k) * (d * ψ k₀ * star (ψ k₀)) := by
        have h1 : ∀ x, Z x k₀ * ψ k * (star (ψ k) * star (Z x k₀)) =
            (ψ k * star (ψ k)) * (Z x k₀ * star (Z x k₀)) := fun x => by ring
        rw [Finset.sum_congr rfl fun x _ => h1 x, ← Finset.mul_sum, h k₀ k₀]
      rw [e1, e2, e3, e4]
      ring
    have hterm : ∀ u' : Fin m, Z u' k * ψ k₀ - Z u' k₀ * ψ k = 0 := by
      intro u'
      have hsumr : (∑ u'' : Fin m, Complex.normSq (Z u'' k * ψ k₀ - Z u'' k₀ * ψ k)) = 0 := by
        apply Complex.ofReal_eq_zero.mp
        rw [Complex.ofReal_sum]
        have h9 : (∑ u'' : Fin m,
              ((Complex.normSq (Z u'' k * ψ k₀ - Z u'' k₀ * ψ k) : ℝ) : ℂ)) =
            ∑ u'' : Fin m, (Z u'' k * ψ k₀ - Z u'' k₀ * ψ k) *
              star (Z u'' k * ψ k₀ - Z u'' k₀ * ψ k) :=
          Finset.sum_congr rfl fun u'' _ => (Complex.mul_conj _).symm
        rw [h9, hsq]
      have hnn : 0 ≤ Complex.normSq (Z u' k * ψ k₀ - Z u' k₀ * ψ k) :=
        Complex.normSq_nonneg _
      have hle : Complex.normSq (Z u' k * ψ k₀ - Z u' k₀ * ψ k) ≤
          ∑ u'' : Fin m, Complex.normSq (Z u'' k * ψ k₀ - Z u'' k₀ * ψ k) :=
        Finset.single_le_sum
          (fun (u'' : Fin m) (_ : u'' ∈ Finset.univ) =>
            Complex.normSq_nonneg (Z u'' k * ψ k₀ - Z u'' k₀ * ψ k))
          (Finset.mem_univ u')
      rw [hsumr] at hle
      have hz : Complex.normSq (Z u' k * ψ k₀ - Z u' k₀ * ψ k) = 0 :=
        le_antisymm hle hnn
      exact Complex.normSq_eq_zero.mp hz
    exact sub_eq_zero.mp (hterm u)
  refine ⟨fun u => Z u k₀ / ψ k₀, ?_, ?_⟩
  · intro u k
    show Z u k = Z u k₀ / ψ k₀ * ψ k
    have h1 : Z u k * ψ k₀ = (Z u k₀ / ψ k₀ * ψ k) * ψ k₀ := by
      rw [hcol u k]
      field_simp [hk₀]
    exact mul_right_cancel₀ hk₀ h1
  · show d = ∑ u : Fin m, (Z u k₀ / ψ k₀) * star (Z u k₀ / ψ k₀)
    have h1 : ∀ u : Fin m, (Z u k₀ / ψ k₀) * star (Z u k₀ / ψ k₀) =
        (Z u k₀ * star (Z u k₀)) / (ψ k₀ * star (ψ k₀)) := by
      intro u
      rw [Complex.star_def, map_div₀ (starRingEnd ℂ)]
      field_simp
    rw [Finset.sum_congr rfl fun u _ => h1 u, ← Finset.sum_div, h00,
      mul_div_cancel_right₀ d hne]

/-- If a complex linear map sends every nonzero vector to a product with that vector as its
second factor, the first factor can be chosen independently of the input. -/
private theorem const_product_amplitude {m n : ℕ} [NeZero n]
    (S : QState (Fin n) → QState (Fin m × Fin n))
    (hadd : ∀ (ψ φ : QState (Fin n)) (u : Fin m) (k : Fin n),
      S (ψ + φ) (u, k) = S ψ (u, k) + S φ (u, k))
    (hsmul : ∀ (c : ℂ) (ψ : QState (Fin n)) (u : Fin m) (k : Fin n),
      S (c • ψ) (u, k) = c * S ψ (u, k))
    (hp : ∀ ψ : QState (Fin n), ψ ≠ 0 → ∃ p : Fin m → ℂ, ∀ u k, S ψ (u, k) = p u * ψ k) :
    ∃ χ : Fin m → ℂ, ∀ (ψ : QState (Fin n)) (u : Fin m) (k : Fin n),
      S ψ (u, k) = χ u * ψ k := by
  have hindep : ∀ (ψ φ : QState (Fin n)), ψ ≠ 0 → φ ≠ 0 →
      (∀ c : ℂ, φ ≠ c • ψ) → ∀ (a b : ℂ), a • ψ + b • φ = 0 → a = 0 ∧ b = 0 := by
    intro ψ φ hψ hφ hne a b hab
    have hb : b = 0 := by
      by_contra hbnz
      apply hne (-(b⁻¹ * a))
      funext x
      have h := congrFun hab x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
      have h0 : a * ψ x = -(b * φ x) := add_eq_zero_iff_eq_neg.mp h
      have h1 : b * φ x = -(a * ψ x) := by rw [h0, neg_neg]
      have h2 : φ x = -(b⁻¹ * a) * ψ x := by
        calc φ x = b⁻¹ * (b * φ x) := by
              rw [← mul_assoc, inv_mul_cancel₀ hbnz, one_mul]
          _ = b⁻¹ * (-(a * ψ x)) := by rw [h1]
          _ = -(b⁻¹ * a) * ψ x := by ring
      rw [h2, Pi.smul_apply, smul_eq_mul]
    refine ⟨?_, hb⟩
    obtain ⟨x₀, hx₀⟩ : ∃ x : Fin n, ψ x ≠ 0 := by
      simpa only [ne_eq, funext_iff, not_forall] using! hψ
    have h := congrFun hab x₀
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [hb, zero_mul, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hx₀
  have hzero : ∀ u k, S (0 : QState (Fin n)) (u, k) = 0 := by
    intro u k
    have h := hsmul (0 : ℂ) 0 u k
    rw [zero_smul, zero_mul] at h
    exact h
  set e₀ : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ with he₀
  have hket : (Qatlib.Foundations.PureStateMath.Ket e₀ : QState (Fin n)) ≠ 0 := by
    intro hz
    have := congrFun hz e₀
    simp [Qatlib.Foundations.PureStateMath.Ket] at this
  obtain ⟨p₀, hp₀⟩ := hp (Qatlib.Foundations.PureStateMath.Ket e₀) hket
  have hkey : ∀ ψ : QState (Fin n), ψ ≠ 0 → ∀ u k, S ψ (u, k) = p₀ u * ψ k := by
    intro ψ hψ u k
    by_cases hdep : ∃ c : ℂ, ψ = c • Qatlib.Foundations.PureStateMath.Ket e₀
    · obtain ⟨c, hc⟩ := hdep
      have h1 : S ψ (u, k) = c * S (Qatlib.Foundations.PureStateMath.Ket e₀) (u, k) := by
        rw [hc, hsmul]
      rw [h1, hp₀ u k]
      have h2 : ψ k = c * Qatlib.Foundations.PureStateMath.Ket e₀ k := by
        rw [hc, Pi.smul_apply, smul_eq_mul]
      rw [h2]
      ring
    · have hsym : ∀ c : ℂ, Qatlib.Foundations.PureStateMath.Ket e₀ ≠ c • ψ := by
        intro c hc
        apply hdep
        by_cases hc0 : c = 0
        · subst hc0
          simp only [zero_smul] at hc
          exact absurd hc hket
        · refine ⟨c⁻¹, ?_⟩
          funext x
          have hx := congrFun hc x
          simp only [Pi.smul_apply, smul_eq_mul] at hx
          calc ψ x = c⁻¹ * (c * ψ x) := by
                rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
            _ = c⁻¹ * Qatlib.Foundations.PureStateMath.Ket e₀ x := by rw [hx]
            _ = (c⁻¹ • Qatlib.Foundations.PureStateMath.Ket e₀) x := by rw [Pi.smul_apply, smul_eq_mul]
      have hsum : ψ + Qatlib.Foundations.PureStateMath.Ket e₀ ≠ 0 := by
        intro hz
        apply hdep
        refine ⟨(-1 : ℂ), ?_⟩
        funext x
        have hx := congrFun hz x
        simp only [Pi.add_apply, Pi.zero_apply] at hx
        have h1 : Qatlib.Foundations.PureStateMath.Ket e₀ x = -ψ x :=
          add_eq_zero_iff_eq_neg.mp (by rw [add_comm]; exact hx)
        rw [Pi.smul_apply, smul_eq_mul, h1]
        ring
      obtain ⟨p', hpp'⟩ := hp (ψ + Qatlib.Foundations.PureStateMath.Ket e₀) hsum
      obtain ⟨p, hpp⟩ := hp ψ hψ
      have heq : (p' u - p u) • ψ + (p' u - p₀ u) • Qatlib.Foundations.PureStateMath.Ket e₀ = 0 := by
        funext x
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul]
        have h1 : S (ψ + Qatlib.Foundations.PureStateMath.Ket e₀) (u,
            x) = p' u * (ψ + Qatlib.Foundations.PureStateMath.Ket e₀) x := hpp' u x
        have h2 : S (ψ + Qatlib.Foundations.PureStateMath.Ket e₀) (u, x) = S ψ (u, x) + S (Qatlib.Foundations.PureStateMath.Ket e₀) (u, x) :=
          hadd ψ (Qatlib.Foundations.PureStateMath.Ket e₀) u x
        have h3 : S ψ (u, x) = p u * ψ x := hpp u x
        have h4 : S (Qatlib.Foundations.PureStateMath.Ket e₀) (u,
            x) = p₀ u * Qatlib.Foundations.PureStateMath.Ket e₀ x := hp₀ u x
        rw [h2, h3, h4] at h1
        simp only [Pi.add_apply] at h1
        have h5 : p' u * ψ x + p' u * Qatlib.Foundations.PureStateMath.Ket e₀ x = p u * ψ x + p₀ u * Qatlib.Foundations.PureStateMath.Ket e₀ x := by
          rw [← mul_add]
          exact h1.symm
        linear_combination h5
      obtain ⟨ha, hb⟩ :=
          hindep ψ (Qatlib.Foundations.PureStateMath.Ket e₀) hψ hket hsym _ _ heq
      have hp_eq : p u = p₀ u :=
        (sub_eq_zero.mp ha).symm.trans (sub_eq_zero.mp hb)
      rw [hpp, hp_eq]
  refine ⟨p₀, ?_⟩
  intro ψ u k
  by_cases hψ : ψ = 0
  · rw [hψ, hzero, Pi.zero_apply, mul_zero]
  · exact hkey ψ hψ u k

/-- The sum of the squared complex norms of the coordinates of a finite vector. -/
private noncomputable def nrm2 {ι : Type} [Fintype ι] (v : QState ι) : ℝ := ∑ i, ‖v i‖ ^ 2

/-- The squared coordinate norm `nrm2` is nonnegative. -/
private theorem nrm2_nonneg {ι : Type} [Fintype ι] (v : QState ι) : 0 ≤ nrm2 v :=
  Finset.sum_nonneg fun i _ => sq_nonneg (‖v i‖)

/-- The squared coordinate norm equals the real part of the vector's inner product with itself. -/
private theorem nrm2_eq_re_inner {ι : Type} [Fintype ι] (v : QState ι) :
    nrm2 v = (Qatlib.Foundations.PureStateMath.Inner v v).re := by
  rw [nrm2, ← norm_toEuclidean_fromVec_sq, norm_toEuclidean_sq_eq_re_inner]

/-- The inner product of a vector with itself is the complex embedding of `nrm2 v`. -/
private theorem inner_self_eq_ofReal_nrm2 {ι : Type} [Fintype ι] (v : QState ι) :
    (Qatlib.Foundations.PureStateMath.Inner v v : ℂ) = (nrm2 v : ℝ) := by
  rw [inner_self, ← Complex.ofReal_sum, nrm2]

/-- The squared norm of an inner product is bounded by the product of the squared coordinate
norms. -/
private theorem abs_inner_sq_le {ι : Type} [Fintype ι] (x y : QState ι) :
    ‖Qatlib.Foundations.PureStateMath.Inner x y‖ ^ 2 ≤ nrm2 x * nrm2 y := by
  have h1 : ‖Qatlib.Foundations.PureStateMath.Inner x y‖ ≤ ‖toEuclidean_fromVec x‖ * ‖toEuclidean_fromVec y‖ := by
    rw [← inner_euclidean_fromVec]
    exact norm_inner_le_norm (toEuclidean_fromVec x) (toEuclidean_fromVec y)
  have h5 : ‖Qatlib.Foundations.PureStateMath.Inner x y‖ ^ 2 ≤ (‖toEuclidean_fromVec x‖ * ‖toEuclidean_fromVec y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [mul_pow, norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq] at h5
  exact h5

/-- The joint input and resource vector after applying the tensor product of the two local
operators. -/
private noncomputable def loccGateVec {n : ℕ} (a : Operator (n * n)) (b : Operator n)
    (ψ : QState (Fin n)) (W : QState (Fin n × Fin n)) : QState (Fin (n * n) × Fin n) :=
  TensorGate a b *ᵥ loccJointVec ψ W

/-- Conjugating a pure joint teleportation operator by the local tensor product gives the outer
product of `loccGateVec`. -/
private theorem teleport_sandwich_outerProduct {n : ℕ} (a : Operator (n * n)) (b : Operator n)
    (ψ : QState (Fin n)) (W : QState (Fin n × Fin n)) :
    TensorGate a b * teleportLoccJoint n (outerProduct ψ) (outerProduct W) * (TensorGate a b)ᴴ
      = outerProduct (loccGateVec a b ψ W) := by
  rw [teleportLoccJoint_outerProduct, sandwich_outerProduct]
  rfl

/-- Moves a matrix adjoint across the conjugated dot product. -/
private theorem dotProduct_star_mulVec_adjoint {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (u v : QState ι) :
    star u ⬝ᵥ (Mᴴ *ᵥ v) = star (M *ᵥ u) ⬝ᵥ v := by
  have hL : star u ⬝ᵥ (Mᴴ *ᵥ v) = ∑ i, ∑ j, star (u i) * star (M j i) * v j := by
    simp only [dotProduct, Pi.star_apply, mulVec_eq_sum, Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ac_rfl
  have hR : star (M *ᵥ u) ⬝ᵥ v = ∑ j, ∑ i, star (u i) * star (M j i) * v j := by
    simp only [dotProduct, Pi.star_apply, mulVec_eq_sum, star_sum, star_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul]
  rw [hL, hR, Finset.sum_comm]

/-- Summing a matrix row against computational basis coordinates selects the corresponding
matrix entry. -/
private theorem ket_gate_sum {n : ℕ} (b : Operator n) (i' l : Fin n) :
    (∑ k : Fin n, b k l * Qatlib.Foundations.PureStateMath.Ket k i') = b i' l := by
  rw [Finset.sum_eq_single i']
  · simp [Qatlib.Foundations.PureStateMath.Ket]
  · intro k _ hk
    have hk' : ¬ (i' = k) := fun h => hk h.symm
    simp [Qatlib.Foundations.PureStateMath.Ket, hk']
  · intro hi
    exact absurd (Finset.mem_univ i') hi

/-- Expands the `(u, k)` coordinate of the locally transformed joint vector for computational
basis input `k` as a sum over the input and resource indices. -/
private theorem loccGateVec_ket_expand {n : ℕ} (a : Operator (n * n)) (b : Operator n)
    (W : QState (Fin n × Fin n)) (k : Fin n) (u : Fin (n * n)) :
    loccGateVec a b (Qatlib.Foundations.PureStateMath.Ket k) W (u, k)
      = ∑ i' : Fin n, ∑ m : Fin n, ∑ l : Fin n,
        a u (finProdFinEquiv (i', m)) * b k l * Qatlib.Foundations.PureStateMath.Ket k i' * W (m, l) := by
  rw [loccGateVec, mulVec_eq_sum, Fintype.sum_prod_type]
  have hre : (∑ u' : Fin (n * n), ∑ k' : Fin n,
        TensorGate a b (u, k) (u', k') * loccJointVec (Qatlib.Foundations.PureStateMath.Ket k) W (u', k'))
      = ∑ i' : Fin n, ∑ m : Fin n, ∑ l : Fin n,
        TensorGate a b (u, k) (finProdFinEquiv (i', m), l) *
          loccJointVec (Qatlib.Foundations.PureStateMath.Ket k) W (finProdFinEquiv (i', m), l) := by
    rw [← Equiv.sum_comp (e := (finProdFinEquiv (m := n) (n := n)))
      (g := fun u' => ∑ k' : Fin n,
        TensorGate a b (u, k) (u', k') * loccJointVec (Qatlib.Foundations.PureStateMath.Ket k) W (u', k'))]
    rw [Fintype.sum_prod_type]
  rw [hre]
  simp only [tensorGate_apply, loccJointVec]
  have hsymm : ∀ (i' m : Fin n),
      (finProdFinEquiv (m := n) (n := n)).symm (finProdFinEquiv (i', m)) = (i', m) :=
    fun i' m => (finProdFinEquiv (m := n) (n := n)).symm_apply_apply _
  simp only [hsymm]
  exact Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun m _ =>
    Finset.sum_congr rfl fun l _ => by ac_rfl

/-- Rewrites the sum of diagonal input and Bob coordinates of `loccGateVec` using Alice's
operator and Bob's action on the resource rows. -/
private theorem loccGateVec_ket_sum {n : ℕ} (a : Operator (n * n)) (b : Operator n)
    (W : QState (Fin n × Fin n)) (u : Fin (n * n)) :
    (∑ k : Fin n, loccGateVec a b (Qatlib.Foundations.PureStateMath.Ket k) W (u, k))
      = ∑ i' : Fin n, ∑ m : Fin n,
        a u (finProdFinEquiv (i', m)) * (b *ᵥ fun l : Fin n => W (m, l)) i' := by
  have hexp : ∀ k : Fin n, loccGateVec a b (Qatlib.Foundations.PureStateMath.Ket k) W (u, k)
      = ∑ i' : Fin n, ∑ m : Fin n, ∑ l : Fin n,
        a u (finProdFinEquiv (i', m)) * b k l * Qatlib.Foundations.PureStateMath.Ket k i' * W (m, l) :=
    fun k => loccGateVec_ket_expand a b W k u
  rw [show (∑ k : Fin n, loccGateVec a b (Qatlib.Foundations.PureStateMath.Ket k) W (u, k))
      = (∑ k : Fin n, ∑ i' : Fin n, ∑ m : Fin n, ∑ l : Fin n,
          a u (finProdFinEquiv (i', m)) * b k l * Qatlib.Foundations.PureStateMath.Ket k i' * W (m, l)) from
      Finset.sum_congr rfl fun k _ => hexp k]
  have hswap : (∑ k : Fin n, ∑ i' : Fin n, ∑ m : Fin n, ∑ l : Fin n,
        a u (finProdFinEquiv (i', m)) * b k l * Qatlib.Foundations.PureStateMath.Ket k i' * W (m, l))
      = (∑ i' : Fin n, ∑ m : Fin n, ∑ l : Fin n, ∑ k : Fin n,
        a u (finProdFinEquiv (i', m)) * b k l * Qatlib.Foundations.PureStateMath.Ket k i' * W (m, l)) :=
    Finset.sum_comm.trans (Finset.sum_congr rfl fun i' _ =>
      Finset.sum_comm.trans (Finset.sum_congr rfl fun m _ => Finset.sum_comm))
  rw [hswap]
  have hstep : ∀ (i' m : Fin n),
      (∑ l : Fin n, ∑ k : Fin n,
        a u (finProdFinEquiv (i', m)) * b k l * Qatlib.Foundations.PureStateMath.Ket k i' * W (m, l))
      = (∑ l : Fin n, a u (finProdFinEquiv (i', m)) * (b i' l * W (m, l))) := by
    intro i' m
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show (∑ k : Fin n,
          a u (finProdFinEquiv (i', m)) * b k l * Qatlib.Foundations.PureStateMath.Ket k i' * W (m, l))
        = (a u (finProdFinEquiv (i', m)) * W (m, l)) * ∑ k : Fin n, b k l * Qatlib.Foundations.PureStateMath.Ket k i' from by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ac_rfl,
      ket_gate_sum b i' l]
    ac_rfl
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun m _ => ?_
  rw [hstep i' m, ← Finset.mul_sum, ← mulVec_eq_sum b (fun l => W (m, l)) i']

/-- Expands the complex conjugate of a coordinate of `aᴴ *ᵥ χ` as a sum involving entries of
`a`. -/
private theorem star_conjTranspose_mulVec {n : ℕ} (a : Operator (n * n))
    (χ : Fin (n * n) → ℂ) (x : Fin (n * n)) :
    star ((aᴴ *ᵥ χ) x) = ∑ u : Fin (n * n), star (χ u) * a u x := by
  rw [mulVec_eq_sum, star_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Matrix.conjTranspose_apply, star_mul, star_star]

/-- Expresses the contraction of computational basis leaf outputs against `χ` as a sum of inner
products between Alice's adjoint slices and Bob's transformed resource rows. -/
private theorem trace_profile {n : ℕ} (a : Operator (n * n)) (b : Operator n)
    (χ : Fin (n * n) → ℂ) (W : QState (Fin n × Fin n)) :
    (∑ k : Fin n, ∑ u : Fin (n * n), star (χ u) * loccGateVec a b (Qatlib.Foundations.PureStateMath.Ket k) W (u, k))
      = ∑ m : Fin n,
        Qatlib.Foundations.PureStateMath.Inner (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))
          (b *ᵥ fun l : Fin n => W (m, l)) := by
  have hu : ∀ u : Fin (n * n),
      (∑ k : Fin n, star (χ u) * loccGateVec a b (Qatlib.Foundations.PureStateMath.Ket k) W (u, k))
        = star (χ u) * ∑ i' : Fin n, ∑ m : Fin n,
          a u (finProdFinEquiv (i', m)) * (b *ᵥ fun l : Fin n => W (m, l)) i' := by
    intro u
    rw [← Finset.mul_sum, loccGateVec_ket_sum]
  have hL : (∑ k : Fin n, ∑ u : Fin (n * n), star (χ u) * loccGateVec a b (Qatlib.Foundations.PureStateMath.Ket k) W (u, k))
      = (∑ i' : Fin n, ∑ m : Fin n, (∑ u : Fin (n * n),
          star (χ u) * a u (finProdFinEquiv (i', m))) * (b *ᵥ fun l : Fin n => W (m, l)) i') := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun u _ => hu u]
    have hin : ∀ u : Fin (n * n),
        star (χ u) * (∑ i' : Fin n, ∑ m : Fin n,
          a u (finProdFinEquiv (i', m)) * (b *ᵥ fun l : Fin n => W (m, l)) i')
        = (∑ i' : Fin n, ∑ m : Fin n,
          star (χ u) * a u (finProdFinEquiv (i', m)) * (b *ᵥ fun l : Fin n => W (m, l)) i') := by
      intro u
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i' _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ac_rfl
    rw [Finset.sum_congr rfl fun u _ => hin u]
    have hsw : (∑ u : Fin (n * n), ∑ i' : Fin n, ∑ m : Fin n,
          star (χ u) * a u (finProdFinEquiv (i', m)) * (b *ᵥ fun l : Fin n => W (m, l)) i')
        = (∑ i' : Fin n, ∑ m : Fin n, ∑ u : Fin (n * n),
          star (χ u) * a u (finProdFinEquiv (i', m)) * (b *ᵥ fun l : Fin n => W (m, l)) i') :=
      Finset.sum_comm.trans (Finset.sum_congr rfl fun i' _ => Finset.sum_comm)
    rw [hsw]
    refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_mul]
  have hinner : ∀ m : Fin n,
      Qatlib.Foundations.PureStateMath.Inner (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))
        (b *ᵥ fun l : Fin n => W (m, l))
      = ∑ i' : Fin n, star ((aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))
          * (b *ᵥ fun l : Fin n => W (m, l)) i' := by
    intro m
    rw [inner_apply]
    simp only [← Complex.star_def]
  have hR : (∑ m : Fin n, Qatlib.Foundations.PureStateMath.Inner (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))
        (b *ᵥ fun l : Fin n => W (m, l)))
      = (∑ i' : Fin n, ∑ m : Fin n, (∑ u : Fin (n * n),
          star (χ u) * a u (finProdFinEquiv (i', m))) * (b *ᵥ fun l : Fin n => W (m, l)) i') := by
    rw [Finset.sum_congr rfl fun m _ => hinner m, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun m _ => ?_
    rw [star_conjTranspose_mulVec]
  rw [hL, hR]

/-- Moves one adjoint factor across the inner product in the squared norm of `aᴴ *ᵥ χ`. -/
private theorem adjoint_profile {n : ℕ} (a : Operator (n * n)) (χ : Fin (n * n) → ℂ) :
    Qatlib.Foundations.PureStateMath.Inner (aᴴ *ᵥ χ) (aᴴ *ᵥ χ) = Qatlib.Foundations.PureStateMath.Inner χ (a *ᵥ (aᴴ *ᵥ χ)) := by
  have hL : Qatlib.Foundations.PureStateMath.Inner (aᴴ *ᵥ χ) (aᴴ *ᵥ χ)
      = ∑ x : Fin (n * n), (∑ u : Fin (n * n), star (χ u) * a u x) * (aᴴ *ᵥ χ) x := by
    rw [inner_apply]
    simp only [← Complex.star_def]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [star_conjTranspose_mulVec]
  have hmid : (∑ x : Fin (n * n), (∑ u : Fin (n * n), star (χ u) * a u x) * (aᴴ *ᵥ χ) x)
      = (∑ u : Fin (n * n), star (χ u) * (a *ᵥ (aᴴ *ᵥ χ)) u) := by
    have h1 : (∑ x : Fin (n * n), (∑ u : Fin (n * n), star (χ u) * a u x) * (aᴴ *ᵥ χ) x)
        = (∑ x : Fin (n * n), ∑ u : Fin (n * n), star (χ u) * a u x * (aᴴ *ᵥ χ) x) :=
      Finset.sum_congr rfl fun x _ => Finset.sum_mul _ _ _
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [show (∑ x : Fin (n * n), star (χ u) * a u x * (aᴴ *ᵥ χ) x)
        = (∑ x : Fin (n * n), star (χ u) * (a u x * (aᴴ *ᵥ χ) x)) from
          Finset.sum_congr rfl fun x _ => by ac_rfl,
      ← Finset.mul_sum, ← mulVec_eq_sum a (aᴴ *ᵥ χ) u]
  rw [hL, hmid]
  exact (inner_apply _ _).symm

/-- The squared coordinate norm of a product vector is the product of the squared coordinate
norms of its factors. -/
private theorem nrm2_prod {ι κ : Type} [Fintype ι] [Fintype κ]
    (f : QState ι) (g : QState κ) :
    nrm2 (fun p : ι × κ => f p.1 * g p.2) = nrm2 f * nrm2 g := by
  simp only [nrm2, Fintype.sum_prod_type, norm_mul, mul_pow]
  rw [Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm, Finset.sum_mul]

/-- If `TensorGate a b` is a contraction in the positive semidefinite order, the product of the
squared norms of its local outputs is bounded by that of its inputs. -/
private theorem quad_prod_bound {n : ℕ} (a : Operator (n * n)) (b : Operator n)
    (hcontr : PosSemidef (1 - (TensorGate a b)ᴴ * TensorGate a b))
    (x : QState (Fin (n * n))) (y : QState (Fin n)) :
    nrm2 (a *ᵥ x) * nrm2 (b *ᵥ y) ≤ nrm2 x * nrm2 y := by
  classical
  set z : QState (Fin (n * n) × Fin n) := fun p => x p.1 * y p.2 with hdef
  set z' : QState (Fin (n * n) × Fin n) := fun p => (a *ᵥ x) p.1 * (b *ᵥ y) p.2 with hdef'
  have hg : TensorGate a b *ᵥ z = z' := tensorGate_mulVec_prod a b x y
  have hq := quad_le_of_psd_sub ((TensorGate a b)ᴴ * TensorGate a b) hcontr z
  have hL : star z ⬝ᵥ (((TensorGate a b)ᴴ * TensorGate a b) *ᵥ z) = star z' ⬝ᵥ z' := by
    rw [← Matrix.mulVec_mulVec, hg]
    exact (dotProduct_star_mulVec_adjoint (TensorGate a b) z z').trans
      (congrArg (fun w => star w ⬝ᵥ z') hg)
  rw [hL] at hq
  have hle :
      Qatlib.Foundations.PureStateMath.Inner z' z' ≤ Qatlib.Foundations.PureStateMath.Inner z z := hq
  rw [inner_self_eq_ofReal_nrm2, inner_self_eq_ofReal_nrm2] at hle
  have hre := (Complex.le_def.mp hle).1
  simp only [Complex.ofReal_re] at hre
  rw [hdef, hdef', nrm2_prod, nrm2_prod] at hre
  exact hre

/-- For a normalized pure resource, a contractive local product branch that scales every nonzero
pure input by a common scalar has scalar at most `1 / n²` in the complex order. -/
private theorem pure_resource_scalar_bound {n : ℕ} [NeZero n]
    (a : Operator (n * n)) (b : Operator n) (W : QState (Fin n × Fin n)) (d : ℂ)
    (hW : Normalized W)
    (hcontr : PosSemidef (1 - (TensorGate a b)ᴴ * TensorGate a b))
    (hd : ∀ ψ : QState (Fin n), ψ ≠ 0 →
      loccBobMarginal n
        (TensorGate a b * teleportLoccJoint n (outerProduct ψ) (outerProduct W) *
          (TensorGate a b)ᴴ) = d • outerProduct ψ) :
    d ≤ (1 / (n : ℂ) ^ 2) := by
  classical
  have hgram : ∀ (ψ : QState (Fin n)) (_hψ : ψ ≠ 0) (k k' : Fin n),
      ∑ u : Fin (n * n), loccGateVec a b ψ W (u, k) * star (loccGateVec a b ψ W (u, k'))
        = d * ψ k * star (ψ k') := by
    intro ψ hψ k k'
    have h1 := hd ψ hψ
    rw [teleport_sandwich_outerProduct, loccBobMarginal_outerProduct] at h1
    have h2 := congrFun (congrFun h1 k) k'
    simp only [Matrix.smul_apply, outerProduct_apply, smul_eq_mul] at h2
    rw [← mul_assoc] at h2
    exact h2
  have hprod : ∀ (ψ : QState (Fin n)) (hψ : ψ ≠ 0),
      ∃ p : Fin (n * n) → ℂ, (∀ u k, loccGateVec a b ψ W (u, k) = p u * ψ k) ∧
        d = ∑ u, p u * star (p u) :=
    fun ψ hψ => product_of_rank_one_gram (fun u k => loccGateVec a b ψ W (u, k)) ψ d
      (fun k k' => hgram ψ hψ k k') hψ
  have hadd : ∀ (ψ φ : QState (Fin n)) (u : Fin (n * n)) (k : Fin n),
      loccGateVec a b (ψ + φ) W (u, k)
        = loccGateVec a b ψ W (u, k) + loccGateVec a b φ W (u, k) := by
    intro ψ φ u k
    simp only [loccGateVec]
    have h1 : loccJointVec (ψ + φ) W = loccJointVec ψ W + loccJointVec φ W := by
      funext x
      obtain ⟨u', k'⟩ := x
      simp only [loccJointVec, Pi.add_apply]
      ring
    rw [h1, Matrix.mulVec_add]
    rfl
  have hsmul : ∀ (c : ℂ) (ψ : QState (Fin n)) (u : Fin (n * n)) (k : Fin n),
      loccGateVec a b (c • ψ) W (u, k) = c * loccGateVec a b ψ W (u, k) := by
    intro c ψ u k
    simp only [loccGateVec]
    have h1 : loccJointVec (c • ψ) W = c • loccJointVec ψ W := by
      funext x
      obtain ⟨u', k'⟩ := x
      simp only [loccJointVec, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h1, Matrix.mulVec_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
  obtain ⟨χ, hχ⟩ := const_product_amplitude (m := n * n)
    (fun ψ : QState (Fin n) => loccGateVec a b ψ W) hadd hsmul
    (fun ψ hψ => (hprod ψ hψ).imp fun p hp => hp.1)
  have hc : (∑ u : Fin (n * n), χ u * star (χ u)) = ((nrm2 χ : ℝ) : ℂ) := by
    have h1 : (∑ u : Fin (n * n), χ u * star (χ u)) = Qatlib.Foundations.PureStateMath.Inner χ χ := by
      rw [inner_apply]
      exact Finset.sum_congr rfl fun u _ => mul_comm _ _
    rw [h1, inner_self_eq_ofReal_nrm2]
  have hd_eq : d = ((nrm2 χ : ℝ) : ℂ) := by
    have hket : (Qatlib.Foundations.PureStateMath.Ket (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n) : QState (Fin n)) ≠ 0 := by
      intro h
      have h0 := congrFun h (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n)
      simp [Qatlib.Foundations.PureStateMath.Ket] at h0
    obtain ⟨p, hp, hdp⟩ :=
        hprod (Qatlib.Foundations.PureStateMath.Ket (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n)) hket
    have hkey : ∀ u : Fin (n * n), p u = χ u := by
      intro u
      have h1 := hp u (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n)
      have h2 := hχ (Qatlib.Foundations.PureStateMath.Ket (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n)) u
        (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n)
      simp [Qatlib.Foundations.PureStateMath.Ket] at h1 h2
      exact h1.symm.trans h2
    rw [hdp, ← hc]
    exact Finset.sum_congr rfl fun u _ => by rw [hkey]
  have hket_chi : ∀ (k : Fin n) (u : Fin (n * n)), loccGateVec a b (Qatlib.Foundations.PureStateMath.Ket k) W (u, k) = χ u := by
    intro k u
    have h := hχ (Qatlib.Foundations.PureStateMath.Ket k) u k
    simp [Qatlib.Foundations.PureStateMath.Ket] at h
    exact h
  have hsum_chi : (∑ u : Fin (n * n), star (χ u) * χ u) = ((nrm2 χ : ℝ) : ℂ) := by
    rw [show (∑ u : Fin (n * n), star (χ u) * χ u) = (∑ u : Fin (n * n), χ u * star (χ u)) from
        Finset.sum_congr rfl fun u _ => mul_comm _ _, hc]
  have halpha : ((n : ℂ) * ((nrm2 χ : ℝ) : ℂ))
      = ∑ m : Fin n, Qatlib.Foundations.PureStateMath.Inner (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))
          (b *ᵥ fun l : Fin n => W (m, l)) := by
    have h1 : (∑ k : Fin n, ∑ u : Fin (n * n), star (χ u) * loccGateVec a b (Qatlib.Foundations.PureStateMath.Ket k) W (u, k))
        = ((n : ℂ) * ((nrm2 χ : ℝ) : ℂ)) := by
      rw [show (∑ k : Fin n, ∑ u : Fin (n * n), star (χ u) * loccGateVec a b (Qatlib.Foundations.PureStateMath.Ket k) W (u, k))
          = (∑ k : Fin n, ∑ u : Fin (n * n), star (χ u) * χ u) from
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun u _ =>
            congrArg (fun t => star (χ u) * t) (hket_chi k u)]
      rw [Finset.sum_congr rfl fun k _ => hsum_chi, Finset.sum_const, nsmul_eq_mul,
        Finset.card_fin]
    exact h1.symm.trans (trace_profile a b χ W)
  have hadj :
      Qatlib.Foundations.PureStateMath.Inner (aᴴ *ᵥ χ)
      (aᴴ *ᵥ χ) = Qatlib.Foundations.PureStateMath.Inner χ (a *ᵥ (aᴴ *ᵥ χ)) :=
      adjoint_profile a χ
  have hBC : (nrm2 (aᴴ *ᵥ χ)) ^ 2 ≤ nrm2 χ * nrm2 (a *ᵥ (aᴴ *ᵥ χ)) := by
    have h1 : (nrm2 (aᴴ *ᵥ χ)) = (Qatlib.Foundations.PureStateMath.Inner χ (a *ᵥ (aᴴ *ᵥ χ))).re :=
      (nrm2_eq_re_inner (aᴴ *ᵥ χ)).trans (congrArg Complex.re hadj)
    have h2 : (Qatlib.Foundations.PureStateMath.Inner χ (a *ᵥ (aᴴ *ᵥ χ))).re ≤ ‖Qatlib.Foundations.PureStateMath.Inner χ (a *ᵥ (aᴴ *ᵥ χ))‖ :=
      Complex.re_le_norm _
    have h3 : ‖Qatlib.Foundations.PureStateMath.Inner χ (a *ᵥ (aᴴ *ᵥ χ))‖ ^ 2 ≤ nrm2 χ * nrm2 (a *ᵥ (aᴴ *ᵥ χ)) :=
      abs_inner_sq_le χ _
    have h4 : 0 ≤ nrm2 χ * nrm2 (a *ᵥ (aᴴ *ᵥ χ)) := mul_nonneg (nrm2_nonneg _) (nrm2_nonneg _)
    have h5 : ‖Qatlib.Foundations.PureStateMath.Inner χ (a *ᵥ (aᴴ *ᵥ χ))‖ ≤ Real.sqrt (nrm2 χ * nrm2 (a *ᵥ (aᴴ *ᵥ χ))) :=
      (Real.le_sqrt (norm_nonneg _) h4).mpr h3
    rw [h1]
    have h6 : (Qatlib.Foundations.PureStateMath.Inner χ (a *ᵥ (aᴴ *ᵥ χ))).re ≤ Real.sqrt (nrm2 χ * nrm2 (a *ᵥ (aᴴ *ᵥ χ))) :=
      le_trans h2 h5
    have h7 : 0 ≤ (Qatlib.Foundations.PureStateMath.Inner χ (a *ᵥ (aᴴ *ᵥ χ))).re := by
      rw [← h1]
      exact nrm2_nonneg _
    exact (Real.le_sqrt h7 h4).mp h6
  have hphi : (∑ m : Fin n, nrm2 (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m))))
      = nrm2 (aᴴ *ᵥ χ) := by
    simp only [nrm2]
    rw [Finset.sum_comm]
    rw [← Fintype.sum_prod_type (fun p : Fin n × Fin n =>
      ‖(aᴴ *ᵥ χ) (finProdFinEquiv (m := n) (n := n) p)‖ ^ 2)]
    exact (Equiv.sum_comp (e := (finProdFinEquiv (m := n) (n := n)))
      (fun x => ‖(aᴴ *ᵥ χ) x‖ ^ 2))
  have hbeta : (∑ m : Fin n, nrm2 (fun l : Fin n => W (m, l))) = nrm2 W := by
    simp only [nrm2]
    rw [← Fintype.sum_prod_type (fun p : Fin n × Fin n => ‖W p‖ ^ 2)]
  have hW' : nrm2 W = 1 := hW
  have hinv : (1 / (n : ℂ) ^ 2) = (((1 / (n : ℝ) ^ 2 : ℝ)) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_natCast]
  have hcast_le : ∀ r s : ℝ, ((r : ℝ) : ℂ) ≤ ((s : ℝ) : ℂ) ↔ r ≤ s := by
    intro r s
    rw [Complex.le_def]
    simp [Complex.ofReal_re, Complex.ofReal_im]
  have hgamma : ∀ m : Fin n,
      nrm2 (a *ᵥ (aᴴ *ᵥ χ)) * nrm2 (b *ᵥ fun l : Fin n => W (m, l))
        ≤ nrm2 (aᴴ *ᵥ χ) * nrm2 (fun l : Fin n => W (m, l)) :=
    fun m => quad_prod_bound a b hcontr (aᴴ *ᵥ χ) (fun l => W (m, l))
  by_cases hB0 : nrm2 (a *ᵥ (aᴴ *ᵥ χ)) = 0
  · have hA0 : nrm2 (aᴴ *ᵥ χ) = 0 := by
      have h1 := hBC
      rw [hB0, mul_zero] at h1
      exact sq_eq_zero_iff.mp (le_antisymm h1 (sq_nonneg _))
    have hphi0 : ∀ m : Fin n,
        nrm2 (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m))) = 0 := by
      intro m
      have h1 : nrm2 (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))
          ≤ ∑ m' : Fin n, nrm2 (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m'))) :=
        Finset.single_le_sum
          (fun (m' : Fin n) (_ : m' ∈ Finset.univ) =>
            nrm2_nonneg (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m'))))
          (Finset.mem_univ m)
      rw [hphi, hA0] at h1
      exact le_antisymm h1 (nrm2_nonneg _)
    have hinner0 : ∀ m : Fin n,
        Qatlib.Foundations.PureStateMath.Inner (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))
          (b *ᵥ fun l : Fin n => W (m, l)) = 0 := by
      intro m
      have h1 : ‖Qatlib.Foundations.PureStateMath.Inner (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))
          (b *ᵥ fun l : Fin n => W (m, l))‖ ^ 2 ≤
          nrm2 (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m))) *
            nrm2 (b *ᵥ fun l : Fin n => W (m, l)) := abs_inner_sq_le _ _
      rw [hphi0 m, zero_mul] at h1
      have h2 : ‖Qatlib.Foundations.PureStateMath.Inner (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))
          (b *ᵥ fun l : Fin n => W (m, l))‖ = 0 :=
        sq_eq_zero_iff.mp (le_antisymm h1 (sq_nonneg _))
      exact norm_eq_zero.mp h2
    have hC0 : nrm2 χ = 0 := by
      have h1 : ((n : ℂ) * ((nrm2 χ : ℝ) : ℂ)) = 0 := by
        rw [halpha]
        exact Finset.sum_eq_zero fun m _ => hinner0 m
      have h2 : ((n : ℝ) : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero, Nat.cast_ne_zero]
        exact NeZero.ne n
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h h2
      · exact Complex.ofReal_eq_zero.mp h
    have hfinal : nrm2 χ ≤ 1 / (n : ℝ) ^ 2 := by
      rw [hC0]
      exact div_nonneg zero_le_one (sq_nonneg _)
    rw [hd_eq, hinv]
    exact (hcast_le _ _).mpr hfinal
  · have hBpos : 0 < nrm2 (a *ᵥ (aᴴ *ᵥ χ)) :=
      lt_of_le_of_ne (nrm2_nonneg _) (Ne.symm hB0)
    have hwm : ∀ m : Fin n, nrm2 (b *ᵥ fun l : Fin n => W (m, l))
        ≤ (nrm2 (aᴴ *ᵥ χ) / nrm2 (a *ᵥ (aᴴ *ᵥ χ))) * nrm2 (fun l : Fin n => W (m, l)) := by
      intro m
      have h1 := hgamma m
      have h2 : nrm2 (b *ᵥ fun l : Fin n => W (m, l))
          = (nrm2 (a *ᵥ (aᴴ *ᵥ χ)) * nrm2 (b *ᵥ fun l : Fin n => W (m, l))) /
            nrm2 (a *ᵥ (aᴴ *ᵥ χ)) :=
        (mul_div_cancel_left₀ _ hB0).symm
      rw [h2]
      have h3 : (nrm2 (a *ᵥ (aᴴ *ᵥ χ)) * nrm2 (b *ᵥ fun l : Fin n => W (m, l))) /
            nrm2 (a *ᵥ (aᴴ *ᵥ χ))
          ≤ (nrm2 (aᴴ *ᵥ χ) * nrm2 (fun l : Fin n => W (m, l))) /
            nrm2 (a *ᵥ (aᴴ *ᵥ χ)) :=
        div_le_div_of_nonneg_right h1 (le_of_lt hBpos)
      rw [div_mul_eq_mul_div]
      exact h3
    have hsumw : (∑ m : Fin n, nrm2 (b *ᵥ fun l : Fin n => W (m, l)))
        ≤ nrm2 (aᴴ *ᵥ χ) / nrm2 (a *ᵥ (aᴴ *ᵥ χ)) := by
      have h1 : (∑ m : Fin n, nrm2 (b *ᵥ fun l : Fin n => W (m, l)))
          ≤ ∑ m : Fin n,
            (nrm2 (aᴴ *ᵥ χ) / nrm2 (a *ᵥ (aᴴ *ᵥ χ))) * nrm2 (fun l : Fin n => W (m, l)) :=
        Finset.sum_le_sum fun m _ => hwm m
      rw [← Finset.mul_sum, hbeta, hW', mul_one] at h1
      exact h1
    have hper : ∀ m : Fin n,
        ‖Qatlib.Foundations.PureStateMath.Inner (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))
          (b *ᵥ fun l : Fin n => W (m, l))‖ ≤
          Real.sqrt (nrm2 (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))) *
            Real.sqrt (nrm2 (b *ᵥ fun l : Fin n => W (m, l))) := by
      intro m
      have h1 : ‖Qatlib.Foundations.PureStateMath.Inner (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))
          (b *ᵥ fun l : Fin n => W (m, l))‖ ^ 2 ≤
          nrm2 (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m))) *
            nrm2 (b *ᵥ fun l : Fin n => W (m, l)) := abs_inner_sq_le _ _
      have h4 : 0 ≤ nrm2 (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m))) *
          nrm2 (b *ᵥ fun l : Fin n => W (m, l)) :=
        mul_nonneg (nrm2_nonneg _) (nrm2_nonneg _)
      have h5 : ‖Qatlib.Foundations.PureStateMath.Inner (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))
          (b *ᵥ fun l : Fin n => W (m, l))‖ ≤ Real.sqrt
            (nrm2 (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m))) *
              nrm2 (b *ᵥ fun l : Fin n => W (m, l))) :=
        (Real.le_sqrt (norm_nonneg _) h4).mpr h1
      rw [← Real.sqrt_mul (nrm2_nonneg
        (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m))))]
      exact h5
    have hsq : (∑ m : Fin n,
          Real.sqrt (nrm2 (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))) *
            Real.sqrt (nrm2 (b *ᵥ fun l : Fin n => W (m, l)))) ^ 2 ≤
        (∑ m : Fin n, nrm2 (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))) *
          ∑ m : Fin n, nrm2 (b *ᵥ fun l : Fin n => W (m, l)) := by
      have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun m : Fin n => Real.sqrt (nrm2 (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))))
        (fun m : Fin n => Real.sqrt (nrm2 (b *ᵥ fun l : Fin n => W (m, l))))
      simp only [Real.sq_sqrt (nrm2_nonneg _)] at h1
      exact h1
    have hnonneg : 0 ≤ ∑ m : Fin n,
        Real.sqrt (nrm2 (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))) *
          Real.sqrt (nrm2 (b *ᵥ fun l : Fin n => W (m, l))) :=
      Finset.sum_nonneg fun m _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hstep2 : ∑ m : Fin n,
          Real.sqrt (nrm2 (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))) *
            Real.sqrt (nrm2 (b *ᵥ fun l : Fin n => W (m, l)))
        ≤ Real.sqrt ((∑ m : Fin n,
            nrm2 (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))) *
          ∑ m : Fin n, nrm2 (b *ᵥ fun l : Fin n => W (m, l))) := by
      rw [Real.le_sqrt hnonneg (mul_nonneg
          (Finset.sum_nonneg fun m _ => nrm2_nonneg _)
          (Finset.sum_nonneg fun m _ => nrm2_nonneg _))]
      exact hsq
    have hAB : nrm2 (aᴴ *ᵥ χ) * (nrm2 (aᴴ *ᵥ χ) / nrm2 (a *ᵥ (aᴴ *ᵥ χ))) ≤ nrm2 χ := by
      have h1 : nrm2 (aᴴ *ᵥ χ) * (nrm2 (aᴴ *ᵥ χ) / nrm2 (a *ᵥ (aᴴ *ᵥ χ)))
          = (nrm2 (aᴴ *ᵥ χ)) ^ 2 / nrm2 (a *ᵥ (aᴴ *ᵥ χ)) := by
        rw [sq, mul_div_assoc]
      rw [h1]
      have h2 : (nrm2 (aᴴ *ᵥ χ)) ^ 2 / nrm2 (a *ᵥ (aᴴ *ᵥ χ))
          ≤ (nrm2 χ * nrm2 (a *ᵥ (aᴴ *ᵥ χ))) / nrm2 (a *ᵥ (aᴴ *ᵥ χ)) :=
        div_le_div_of_nonneg_right hBC (nrm2_nonneg _)
      rwa [mul_div_cancel_right₀ _ hB0] at h2
    have hcs : (∑ m : Fin n,
          ‖Qatlib.Foundations.PureStateMath.Inner (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))
            (b *ᵥ fun l : Fin n => W (m, l))‖)
        ≤ Real.sqrt (nrm2 χ) := by
      have h1 : (∑ m : Fin n,
            ‖Qatlib.Foundations.PureStateMath.Inner (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))
              (b *ᵥ fun l : Fin n => W (m, l))‖)
          ≤ ∑ m : Fin n,
            Real.sqrt (nrm2 (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))) *
              Real.sqrt (nrm2 (b *ᵥ fun l : Fin n => W (m, l))) :=
        Finset.sum_le_sum fun m _ => hper m
      have h2 : (∑ m : Fin n, nrm2 (fun i' : Fin n => (aᴴ *ᵥ χ) (finProdFinEquiv (i', m)))) *
            ∑ m : Fin n, nrm2 (b *ᵥ fun l : Fin n => W (m, l))
          ≤ nrm2 (aᴴ *ᵥ χ) * (nrm2 (aᴴ *ᵥ χ) / nrm2 (a *ᵥ (aᴴ *ᵥ χ))) := by
        rw [hphi]
        exact mul_le_mul_of_nonneg_left hsumw (nrm2_nonneg _)
      have h3 := le_trans hstep2 (Real.sqrt_le_sqrt h2)
      have h4 : Real.sqrt (nrm2 (aᴴ *ᵥ χ) *
          (nrm2 (aᴴ *ᵥ χ) / nrm2 (a *ᵥ (aᴴ *ᵥ χ)))) ≤ Real.sqrt (nrm2 χ) :=
        Real.sqrt_le_sqrt hAB
      exact le_trans h1 (le_trans h3 h4)
    have hmain : (n : ℝ) * nrm2 χ ≤ Real.sqrt (nrm2 χ) := by
      have hre : (((n : ℂ) * ((nrm2 χ : ℝ) : ℂ)) : ℂ).re = (n : ℝ) * nrm2 χ := by
        rw [Complex.mul_re, ← Complex.ofReal_natCast n]
        simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      rw [← hre, halpha]
      exact le_trans (Complex.re_le_norm _) (le_trans (norm_sum_le _ _) hcs)
    have hfinal : nrm2 χ ≤ 1 / (n : ℝ) ^ 2 := by
      by_cases hC0 : nrm2 χ = 0
      · rw [hC0]
        exact div_nonneg zero_le_one (sq_nonneg _)
      · have hCpos : 0 < nrm2 χ := lt_of_le_of_ne (nrm2_nonneg _) (Ne.symm hC0)
        have h1 : ((n : ℝ) * nrm2 χ) ^ 2 ≤ nrm2 χ := by
          have h2 : ((n : ℝ) * nrm2 χ) ^ 2 ≤ (Real.sqrt (nrm2 χ)) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (nrm2_nonneg _)) hmain 2
          rwa [Real.sq_sqrt (nrm2_nonneg _)] at h2
        have h3 : (n : ℝ) ^ 2 * nrm2 χ ^ 2 ≤ nrm2 χ := by
          rwa [mul_pow] at h1
        have h4 : (n : ℝ) ^ 2 * nrm2 χ ≤ 1 := by
          have hdiv := div_le_div_of_nonneg_right h3 (le_of_lt hCpos)
          have h5 : (nrm2 χ) ^ 2 / nrm2 χ = nrm2 χ := by
            rw [sq, mul_div_cancel_right₀ _ hC0]
          rw [mul_div_assoc, h5, div_self hC0] at hdiv
          exact hdiv
        have h6 : 0 < (n : ℝ) ^ 2 :=
          sq_pos_of_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne n))
        rw [le_div_iff₀ h6, mul_comm]
        exact h4
    rw [hd_eq, hinv]
    exact (hcast_le _ _).mpr hfinal

end Qatlib.Concepts.QuditTeleport.ResourceIff
