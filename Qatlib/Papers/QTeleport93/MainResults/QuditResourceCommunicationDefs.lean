/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportation
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Papers.QTeleport93.MainResults

def Clause11MessageWidth (n : ℕ) : ℕ := 2 * Nat.clog 2 n

def Clause11BranchCount (n : ℕ) : ℕ := n * n

noncomputable def Clause11GuessMass (n : ℕ) : ℝ := 1 / ((Clause11BranchCount n : ℕ) : ℝ)

end Qatlib.Papers.QTeleport93.MainResults
