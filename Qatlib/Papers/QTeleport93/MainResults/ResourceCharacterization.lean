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

theorem c004_eq9_max_ent_marginals : Eq9MaxEntMarginals :=
  eq9MaxEntMarginals

theorem c004_eq9_characterization : Eq9MaxEntCharacterization :=
  eq9MaxEntCharacterization

theorem c004_eq9_resource_teleportation : Eq9ResourceTeleportation :=
  eq9ResourceTeleportation

theorem c004_four_fixed_corrections_converse : FourFixedCorrectionsMaxEntConverse :=
  fourFixedCorrectionsMaxEntConverse

theorem c004_qubit_pure_resource_eq9
    (K : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (U : Fin 4 → Operator 2) (Ψ : QState (Fin 2 × Fin 2)) (hΨ : Normalized Ψ)
    (htele : FourFixedCorrectionsTeleport K U (outerProduct Ψ)) :
    ∃ u v p q : QState (Fin 2), eq9OrthoPairs u v p q ∧ eq9Resource u v p q = Ψ :=
  pure_resource_teleportation_eq9 K U Ψ hΨ htele

theorem c004_qudit_marginal_converse : QuditResourceMarginalConverse :=
  quditResourceMarginalConverse

theorem c004_qudit_max_ent_characterization : QuditMaxEntCharacterization :=
  quditMaxEntCharacterization

theorem c004_qudit_max_ent_teleportation : QuditMaxEntResourceTeleportation :=
  quditMaxEntResourceTeleportation

theorem c004_qudit_pure_resource_form : QuditPureResourceMaxEntForm :=
  quditPureResourceMaxEntForm

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

theorem c004_eq9_iff_maximally_entangled :
    QuditMaxEntCharacterization ∧ QuditMaxEntResourceTeleportation ∧
      QuditResourceMarginalConverse ∧ QuditPureResourceMaxEntForm :=
  ⟨quditMaxEntCharacterization, quditMaxEntResourceTeleportation,
    quditResourceMarginalConverse, quditPureResourceMaxEntForm⟩

end Qatlib.Papers.QTeleport93.MainResults.ResourceCharacterization
