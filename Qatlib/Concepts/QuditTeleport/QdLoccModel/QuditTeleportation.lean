/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportationDefs
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationInstrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.CountedQuditTeleportation
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditResourceMarginalConverse
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditMaxEntCharacterization
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditMaxEntResourceTeleportation
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditPureResourceMaxEntForm
import Qatlib.Concepts.QuditTeleport.QdLoccModel.RedundantCodingReliability
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceMarginalConverse
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntCharacterization
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntResourceTeleportation
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditPureResourceMaxEntForm
import Qatlib.Concepts.QuditTeleport.MessagingBounds.RedundantCodingReliability
import Qatlib.Concepts.QuditTeleport.CommLowerBound.CommBoundRestrictedTele
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportationCommBound
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportationBranchMarginal
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportationPurity
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportationWeyl
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportationPurityAssembly
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportationMEProtocol

/-!
# Qudit teleportation resources and communication

`g4` assembles resource necessity and sufficiency, communication counting, message guessing,
explicit qudit protocol properties, and repeated-observation reliability. For a positive
semidefinite resource, perfect teleportation with unitary corrections forces purity and a
maximally mixed receiver marginal.

Conversely, orthonormal-family maximally entangled resources support a finite complete
measurement with unitary corrections, as expressed by `clause4_clause1b`. These results develop
resource and communication properties of teleportation [BennettEtAl1993Teleportation].

## Main statements

* `clause4_clause1`: A positive semidefinite resource enabling perfect teleportation in nonzero
  dimension with unitary corrections is a normalized pure state with maximally mixed receiver
  marginal [BennettEtAl1993Teleportation].
* `clause4_clause1b`: A resource formed from two orthonormal families supports a finite
  teleportation protocol with unitary corrections and perfect recovery
  [BennettEtAl1993Teleportation].
* `g4`: The combined theorem for qudit teleportation resources, outcome and bit counts, guessing
  bounds, composite systems, explicit protocol recovery, and redundant-coding reliability
  [BennettEtAl1993Teleportation].

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds
open Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
open scoped ComplexOrder

end Qatlib.Concepts.QuditTeleport.QdLoccModel

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportation

open Matrix

end Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportation

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportation

open Matrix
open scoped BigOperators ComplexOrder

/-- A double sum over two finite types equals the corresponding sum over their product. -/
private theorem sum2_merge {α β : Type} [Fintype α] [Fintype β] (g : α → β → ℂ) :
    (∑ a : α, ∑ b : β, g a b) = ∑ p : α × β, g p.1 p.2 :=
  (Fintype.sum_prod_type (fun p => g p.1 p.2)).symm

/-- Merging a double finite sum into a product-indexed sum preserves its product with a fixed
complex scalar. -/
private theorem sum2_merge_mul {α β : Type} [Fintype α] [Fintype β] (g : α → β → ℂ) (s : ℂ) :
    ((∑ a : α, ∑ b : β, g a b) * s) = (∑ p : α × β, g p.1 p.2) * s :=
  congrArg (fun z => z * s) (sum2_merge g)

/-- Four finite sums can be grouped into two sums over pairs of indices. -/
private theorem sum4_merge22 {α β : Type} [Fintype α] [Fintype β]
    (g : α → α → β → β → ℂ) :
    (∑ a1 : α, ∑ a2 : α, ∑ b1 : β, ∑ b2 : β, g a1 a2 b1 b2)
      = (∑ p : α × α, ∑ q : β × β, g p.1 p.2 q.1 q.2) := by
  rw [sum2_merge]
  exact Finset.sum_congr rfl (fun p _ => sum2_merge _)

/-- The first and third indices of a triple finite complex sum can be interchanged. -/
private theorem sum3_swap_first_third {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (F : α → β → γ → ℂ) :
    (∑ a : α, ∑ b : β, ∑ c : γ, F a b c) = (∑ c : γ, ∑ b : β, ∑ a : α, F a b c) := by
  calc (∑ a : α, ∑ b : β, ∑ c : γ, F a b c)
      = (∑ b : β, ∑ a : α, ∑ c : γ, F a b c) := Finset.sum_comm
    _ = (∑ b : β, ∑ c : γ, ∑ a : α, F a b c) :=
        Finset.sum_congr rfl (fun b _ => Finset.sum_comm)
    _ = (∑ c : γ, ∑ b : β, ∑ a : α, F a b c) := Finset.sum_comm

open Matrix
open scoped BigOperators

open Matrix
open scoped BigOperators

open Matrix
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000
open Matrix Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.ResourceIff
open scoped BigOperators ComplexOrder MatrixOrder

open Matrix Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.ResourceIff
open scoped BigOperators ComplexOrder MatrixOrder

set_option autoImplicit false
set_option maxHeartbeats 800000

open Matrix
open scoped BigOperators ComplexOrder

open Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds
open Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.ResourceIff

/-- The complex-linear map sending `ρ` to `C * ρ * Cᴴ`. -/
noncomputable def clause4Aux_conjLin (n : ℕ) (C : Operator n) : Operator n →ₗ[ℂ] Operator n where
  toFun := fun ρ => C * ρ * C.conjTranspose
  map_add' := by
    intro A B
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' := by
    intro c A
    simp [Matrix.mul_smul, Matrix.smul_mul]

/-- A positive semidefinite resource enabling perfect teleportation in nonzero dimension with
unitary corrections is a normalized pure state with maximally mixed receiver marginal
[BennettEtAl1993Teleportation]. -/
theorem clause4_clause1 : ∀ (n : ℕ) (_hn : NeZero n)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ),
    ω.PosSemidef →
    (∃ (κ : Type) (_hκ : Fintype κ) (P : QdLoccTeleport n κ) (U : κ → Operator n),
      QdLoccUnitaryCorr P U ∧ QdLoccPerfect P ω) →
    ∃ Ψ : QState (Fin n × Fin n),
      Normalized Ψ ∧ ω = outerProduct Ψ ∧
        PartialTrace (relabelGate (Equiv.prodComm (Fin n) (Fin n)) ω)
          = (1 / (n : ℂ)) • (1 : Operator n) := by
  intro n hn ω hω hex
  obtain ⟨κ, hκ, P, U, hU, hperf⟩ := hex
  obtain ⟨Ψ, hΨn, hΨe⟩ := g8p_mixed_purity P U hU ω hω hperf
  exact ⟨Ψ, hΨn, hΨe, g8p_bobMarginal P U hU ω hω hperf⟩

/-- A resource formed from two orthonormal families supports a finite teleportation protocol
with unitary corrections and perfect recovery [BennettEtAl1993Teleportation]. -/
theorem clause4_clause1b : ∀ (n : ℕ) (u v : Fin n → QState (Fin n)),
    QuditOrthonormalFamily n u → QuditOrthonormalFamily n v →
    ∃ (κ : Type) (_hκ : Fintype κ) (P : QdLoccTeleport n κ) (U : κ → Operator n),
      QdLoccUnitaryCorr P U ∧
        QdLoccPerfect P (outerProduct (quditMaxEntResource n u v)) := by
  intro n u v hu hv
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    haveI : IsEmpty (Fin 0 × Fin 0) := ⟨fun p => Fin.elim0 p.1⟩
    refine ⟨Fin 0 × Fin 0, inferInstance,
      { kraus := fun _ => 0
        krausComplete := by
          ext i j
          exact Fin.elim0 i.1
        corr := fun _ => 0
        msgCode := fun _ => [] }, fun _ => 0, ?_, ?_⟩
    · refine ⟨fun o => (IsEmpty.false o).elim, fun o ρ => (IsEmpty.false o).elim⟩
    · intro ρ
      show (∑ k : Fin 0 × Fin 0, _) = ρ
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      ext i j
      exact Fin.elim0 i
  · haveI : NeZero n := ⟨ne_of_gt hn⟩
    set Ψ : QState (Fin n × Fin n) := quditMaxEntResource n u v
    set B : Fin n × Fin n → Operator n := fun o => quditResourceBranchKraus n Ψ o
    set U0 : Fin n × Fin n → Operator n := fun o => (n : ℂ) • (B o).conjTranspose
    have hcorr : ∀ (o : Fin n × Fin n) (ρ : Operator n),
        (clause4Aux_conjLin n (U0 o)) ρ = U0 o * ρ * (U0 o).conjTranspose := fun o ρ => rfl
    refine ⟨Fin n × Fin n, inferInstance,
      { kraus := clause4Aux_meKraus n
        krausComplete := clause4Aux_meKraus_complete n
        corr := fun o => clause4Aux_conjLin n (U0 o)
        msgCode := fun _ => [] }, U0, ?_, ?_⟩
    · refine ⟨?_, hcorr⟩
      intro o
      exact (quditMaxEntResourceTeleportation n u v hu hv o).1
    · intro ρ
      show (∑ o : Fin n × Fin n,
          (clause4Aux_conjLin n (U0 o)) (qdBranchMarginal (clause4Aux_meKraus n o)
            (outerProduct Ψ) ρ)) = ρ
      have hbr : ∀ o : Fin n × Fin n,
          qdBranchMarginal (clause4Aux_meKraus n o) (outerProduct Ψ) ρ = conjBranch (B o) ρ :=
        fun o => clause4Aux_branch_me n Ψ o ρ
      have hstep : ∀ o : Fin n × Fin n,
          (clause4Aux_conjLin n (U0 o)) (qdBranchMarginal (clause4Aux_meKraus n o) (outerProduct Ψ) ρ)
            = ((n : ℂ) • (B o).conjTranspose * B o) * ρ
                * (((n : ℂ) • (B o).conjTranspose * B o)).conjTranspose := by
        intro o
        rw [hcorr, hbr, conjBranch_apply]
        have hU0 : U0 o = (n : ℂ) • (B o).conjTranspose := rfl
        rw [hU0]
        have hconj : ((n : ℂ) • (B o).conjTranspose).conjTranspose
            = (n : ℂ) • (B o) := by simp
        rw [hconj]
        have hstar : (starRingEnd ℂ) ((n : ℂ)) = (n : ℂ) := by simp
        simp only [Matrix.mul_assoc, Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
          Matrix.conjTranspose_conjTranspose, Complex.star_def, hstar]
      rw [Finset.sum_congr rfl (fun o _ => hstep o)]
      have hbranch : ∀ o : Fin n × Fin n,
          ((n : ℂ) • (B o).conjTranspose * B o) * ρ
              * (((n : ℂ) • (B o).conjTranspose * B o)).conjTranspose
            = (1 / (n : ℂ) ^ 2) • ρ :=
        fun o => (quditMaxEntResourceTeleportation n u v hu hv o).2 ρ
      rw [Finset.sum_congr rfl (fun o _ => hbranch o)]
      rw [← Finset.sum_smul, qudit_uniform_scalar_sum n, one_smul]

/-- The combined theorem for qudit teleportation resources, outcome and bit counts, guessing
bounds, composite systems, explicit protocol recovery, and redundant-coding reliability
[BennettEtAl1993Teleportation]. -/
theorem g4 :

  (∀ (n : ℕ) (_hn : NeZero n) (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ),
    ω.PosSemidef →
    (∃ (κ : Type) (_hκ : Fintype κ) (P : QdLoccTeleport n κ) (U : κ → Operator n),
      QdLoccUnitaryCorr P U ∧ QdLoccPerfect P ω) →
    ∃ Ψ : QState (Fin n × Fin n),
      Normalized Ψ ∧ ω = outerProduct Ψ ∧
        PartialTrace (relabelGate (Equiv.prodComm (Fin n) (Fin n)) ω)
          = (1 / (n : ℂ)) • (1 : Operator n))

  ∧ (∀ (n : ℕ) (u v : Fin n → QState (Fin n)),
    QuditOrthonormalFamily n u → QuditOrthonormalFamily n v →
    ∃ (κ : Type) (_hκ : Fintype κ) (P : QdLoccTeleport n κ) (U : κ → Operator n),
      QdLoccUnitaryCorr P U ∧
        QdLoccPerfect P (outerProduct (quditMaxEntResource n u v)))

  ∧ (∀ (n : ℕ) (κ : Type) (_hκ : Fintype κ) (P : QdLoccTeleport n κ)
      (U : κ → Operator n) (Ψ : QState (Fin n × Fin n)),
    Normalized Ψ → QdLoccUnitaryCorr P U → QdLoccPerfect P (outerProduct Ψ) →
    (QdLoccMsgConsistent P → ∀ k k' : κ, P.msgCode k = P.msgCode k' →
      QdSameConjugation n (U k) (U k')) ∧
    n * n ≤ Fintype.card κ ∧ n * n ≤ 2 ^ qdMessageBits κ ∧
    (Function.Injective P.msgCode → n * n ≤ 2 ^ (qdCommCost P + 1)))

  ∧ (∀ (κ σ : Type) (_hκ : Fintype κ) (_hd : DecidableEq σ) (p : κ → ℝ),
    (∀ k, 0 ≤ p k) → ∑ k, p k = 1 → ∀ m : κ → σ,
    (∃ g : σ,
      1 / ((Fintype.card (Set.range m) : ℕ) : ℝ) ≤ qdGuessMass p m g) ∧
    (∀ a b : κ, a ≠ b → m a = m b →
      ∃ g : σ, p a + p b ≤ qdGuessMass p m g))

  ∧ (∀ (n : ℕ) (_hn : NeZero n) (σ : Type) (_hσ : Fintype σ) (_hd : DecidableEq σ)
      (m : Fin n × Fin n → σ),
    (Function.Injective m →
      qdBestGuessMass (qdUniform n) m = 1 / ((n * n : ℕ) : ℝ)) ∧
    (¬ Function.Injective m →
      2 / ((n * n : ℕ) : ℝ) ≤ qdBestGuessMass (qdUniform n) m ∧
        qdBestGuessMass (qdUniform n) m ≤ 1) ∧
    ((∃ c : σ, ∀ o : Fin n × Fin n, m o = c) →
      qdBestGuessMass (qdUniform n) m = 1) ∧
    (∀ g : σ → Fin n × Fin n,
      qdDecodeMass (qdUniform n) m g ≤
        ((Fintype.card (Set.range m) : ℕ) : ℝ) / ((n * n : ℕ) : ℝ)))

  ∧ (∀ (n k : ℕ) (_hk : 1 ≤ k) (κc : Type) (_hc : Fintype κc)
      (P : QdLoccTeleport (n ^ k) κc) (U : κc → Operator (n ^ k))
      (Ψ : QState (Fin (n ^ k) × Fin (n ^ k))),
    Normalized Ψ → QdLoccUnitaryCorr P U →
      QdLoccPerfect P (outerProduct Ψ) →
    n ^ k * n ^ k ≤ Fintype.card κc ∧ n ^ k * n ^ k ≤ 2 ^ qdMessageBits κc ∧
    (Function.Injective P.msgCode → n ^ k * n ^ k ≤ 2 ^ (qdCommCost P + 1)))

  ∧ (∀ (n : ℕ) (h : NeZero n),
    (∀ (rho : Operator n) (o : Fin n × Fin n),
      @quditActualBranchCore n h o rho = (1 / (n : ℂ) ^ 2) • rho) ∧
    (∀ rho : Operator n, (@quditCorrectedInstrument n h).forget.map rho = rho) ∧
    (∀ o : Fin n × Fin n,
      (quditMessage n (Nat.clog 2 n) o).length = 2 * Nat.clog 2 n ∧
        quditDecodeMessage n (Nat.clog 2 n) (quditMessage n (Nat.clog 2 n) o)
          = some o) ∧
    Function.Injective (quditMessage n (Nat.clog 2 n)) ∧
    n ≤ 2 ^ Nat.clog 2 n)

  ∧ (QuditResourceMarginalConverse ∧ QuditMaxEntCharacterization ∧
    QuditMaxEntResourceTeleportation ∧ QuditPureResourceMaxEntForm ∧
    RedundantCodingReliability)
  := by
  exact ⟨clause4_clause1, clause4_clause1b, clause4_clause2, clause4_clause3, clause4_clause4, clause4_clause5,
    clause4_clause6, clause4_clause7⟩
