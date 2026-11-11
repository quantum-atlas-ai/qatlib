/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.Eq9MaxEntMarginals
import Qatlib.Concepts.QuditTeleport.ResourceIff.Eq9MaxEntCharacterizationTele
import Qatlib.Concepts.QuditTeleport.ResourceIff.Eq9ResourceTeleportationTele
import Qatlib.Concepts.QuditTeleport.ResourceIff.FourFixedCorrectionsMaxEntConverseTele
import Qatlib.Concepts.QuditTeleport.ResourceIff.PureResourceConverseConsumer
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceMarginalConverse
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntCharacterization
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntResourceTeleportation
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditPureResourceMaxEntForm
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws

/-!
# Maximally entangled resources for exact teleportation

The Eq. (9) resource form of [BennettEtAl1993Teleportation] has maximally mixed marginals and
possesses fixed unitary corrections. Conversely, a normalized pure resource satisfying the fixed
correction teleportation condition has this maximally entangled form.

The module also presents the corresponding qudit results: orthonormal family resource
representations, maximally mixed marginals, explicit branch corrections, and necessity of the
representation for normalized pure resources. `c004_eq9_iff_maximally_entangled` collects these
qudit characterization and teleportation properties.

## Main statements

* `c004_eq9_max_ent_marginals` and `c004_eq9_characterization` relate the qubit resource form to
  its marginal.
* `c004_qubit_pure_resource_eq9` derives the Eq. (9) form from exact fixed correction
  teleportation.
* `c004_max_ent_sufficient` constructs a unitary correction for each qudit resource branch.
* `c004_fixed_corrections_necessary` derives the qudit maximally entangled resource
  representation.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.QuditTeleport.ResourceIff
open Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Foundations.PureStateMath.Reflection
open Matrix
open scoped Classical BigOperators ComplexOrder

namespace Qatlib.Papers.QTeleport93.MainResults.ResourceCharacterization

/-- An Eq. (9) resource built from two orthonormal pairs has both single qubit marginals equal
to half the identity. -/
theorem c004_eq9_max_ent_marginals : Eq9MaxEntMarginals :=
  eq9MaxEntMarginals

/-- A normalized pure two qubit state with a maximally mixed partial trace has the Eq. (9)
resource representation in orthonormal local pairs. -/
theorem c004_eq9_characterization : Eq9MaxEntCharacterization :=
  eq9MaxEntCharacterization

/-- For an Eq. (9) resource from orthonormal pairs, twice the adjoint of each branch Kraus
operator is unitary and corrects that branch to one quarter of the input
[BennettEtAl1993Teleportation]. -/
theorem c004_eq9_resource_teleportation : Eq9ResourceTeleportation :=
  eq9ResourceTeleportation

/-- A positive resource satisfying the four fixed correction teleportation condition has its
receiver marginal equal to half the identity. -/
theorem c004_four_fixed_corrections_converse : FourFixedCorrectionsMaxEntConverse :=
  fourFixedCorrectionsMaxEntConverse

/-- A normalized pure two qubit resource supporting teleportation with four fixed corrections
has an Eq. (9) representation using orthonormal local pairs [BennettEtAl1993Teleportation]. -/
theorem c004_qubit_pure_resource_eq9
    (K : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (U : Fin 4 → Operator 2) (Ψ : QState (Fin 2 × Fin 2)) (hΨ : Normalized Ψ)
    (htele : FourFixedCorrectionsTeleport K U (outerProduct Ψ)) :
    ∃ u v p q : QState (Fin 2), eq9OrthoPairs u v p q ∧ eq9Resource u v p q = Ψ :=
  pure_resource_teleportation_eq9 K U Ψ hΨ htele

/-- A positive qudit resource satisfying the fixed correction teleportation condition has its
receiver marginal equal to `1 / n` times the identity. -/
theorem c004_qudit_marginal_converse : QuditResourceMarginalConverse :=
  quditResourceMarginalConverse

/-- Resources represented by two orthonormal local families have maximally mixed marginals, and
every normalized pure state with the specified maximally mixed marginal has such a
representation. -/
theorem c004_qudit_max_ent_characterization : QuditMaxEntCharacterization :=
  quditMaxEntCharacterization

/-- For a qudit resource built from orthonormal local families, `n` times each branch Kraus
adjoint is unitary and corrects the branch to the input scaled by `1 / n^2`. -/
theorem c004_qudit_max_ent_teleportation : QuditMaxEntResourceTeleportation :=
  quditMaxEntResourceTeleportation

/-- A normalized pure resource supporting fixed correction qudit teleportation has a maximally
entangled representation in orthonormal local families. -/
theorem c004_qudit_pure_resource_form : QuditPureResourceMaxEntForm :=
  quditPureResourceMaxEntForm

/-- For the specified maximally entangled qudit resource and outcome, `n` times the branch Kraus
adjoint is a unitary correction yielding the input scaled by `1 / n^2`
[BennettEtAl1993Teleportation]. -/
theorem c004_max_ent_sufficient
    (n : ℕ) [NeZero n] (u v : Fin n → QState (Fin n))
    (hu : QuditOrthonormalFamily n u) (hv : QuditOrthonormalFamily n v)
    (o : Fin n × Fin n) :
    ((n : ℂ) • (quditResourceBranchKraus n (quditMaxEntResource n u v) o)ᴴ ∈
        Matrix.unitaryGroup (Fin n) ℂ) ∧
      ∀ ρ : Operator n,
        (((n : ℂ) • (quditResourceBranchKraus n (quditMaxEntResource n u v) o)ᴴ *
            quditResourceBranchKraus n (quditMaxEntResource n u v) o) * ρ *
          ((n : ℂ) • (quditResourceBranchKraus n (quditMaxEntResource n u v) o)ᴴ *
            quditResourceBranchKraus n (quditMaxEntResource n u v) o)ᴴ)
          = (1 / (n : ℂ) ^ 2) • ρ :=
  quditMaxEntResourceTeleportation n u v hu hv o

/-- A normalized pure qudit resource supporting the stated fixed correction teleportation
condition is a maximally entangled sum over two orthonormal local families
[BennettEtAl1993Teleportation]. -/
theorem c004_fixed_corrections_necessary
    (n : ℕ) [NeZero n]
    (K : Fin n × Fin n → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (U : Fin n × Fin n → Operator n) (Ψ : QState (Fin n × Fin n))
    (hΨ : Normalized Ψ)
    (htele : QuditFixedCorrectionsTeleport n K U (outerProduct Ψ)) :
    ∃ u v : Fin n → QState (Fin n),
      QuditOrthonormalFamily n u ∧ QuditOrthonormalFamily n v ∧
        quditMaxEntResource n u v = Ψ :=
  quditPureResourceMaxEntForm n K U Ψ hΨ htele

/-- Bundles the qudit maximally entangled characterization, teleportation sufficiency, marginal
necessity, and pure resource representation results. -/
theorem c004_eq9_iff_maximally_entangled :
    QuditMaxEntCharacterization ∧ QuditMaxEntResourceTeleportation ∧
      QuditResourceMarginalConverse ∧ QuditPureResourceMaxEntForm :=
  ⟨quditMaxEntCharacterization, quditMaxEntResourceTeleportation,
    quditResourceMarginalConverse, quditPureResourceMaxEntForm⟩

end Qatlib.Papers.QTeleport93.MainResults.ResourceCharacterization
