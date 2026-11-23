module

import Qatlib.Papers.DihHSPSieve03.MainResults.Algorithm2Concrete

set_option autoImplicit false

namespace QatlibTests.DihHSPSieve03PairingConsumer

open Qatlib.Concepts.HspRecovery.OpenSieve
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian
open Qatlib.Papers.DihHSPSieve03.MainResults

/-- Ordinary-module consumer for the concrete general-modulus collision endpoint. -/
theorem concrete_algorithm2_consumer :
    ShiftRecoveryEndpoint 5 1 (generalCollisionLedger 5 3) ∧
      generalCollisionQueryCount 5 3 = 6 ∧
      (∀ u : ZMod 5, u ≠ (2 : ZMod 5) →
        generalCollisionRun (affineSlopeOracle 5 (2 : ZMod 5)) 3 (some u) = 0) ∧
      generalCollisionRun (affineSlopeOracle 5 (2 : ZMod 5)) 3 (some (2 : ZMod 5)) = 1 := by
  exact algorithm2_concrete_main

end QatlibTests.DihHSPSieve03PairingConsumer
