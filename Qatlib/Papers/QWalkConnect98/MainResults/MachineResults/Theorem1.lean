/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkConnect98.MainResults.MachineResults.MachineDefs
set_option warningAsError false

namespace Qatlib.Papers.QWalkConnect98.MainResults.MachineResults

set_option autoImplicit false

def QRHLClosedUnderReduces : Prop :=
  ∀ {A B : List Bool → Prop}, InQRHL B → Reduces A B → InQRHL A

def USTCONInQRHL : Prop :=
  ∀ (d : ℕ) (decode : List Bool → GraphInstance d), 3 ≤ d →
    InQRHL (fun x => InstanceConnected (decode x))

theorem theorem1_SL_subset_QRHL (A : List Bool → Prop) (hSL : InSL A)
    (hUSTCON : USTCONInQRHL) (hclosed : QRHLClosedUnderReduces) : InQRHL A := by
  obtain ⟨d, decode, hd, hred⟩ := hSL
  exact hclosed (hUSTCON d decode hd) hred

end Qatlib.Papers.QWalkConnect98.MainResults.MachineResults
