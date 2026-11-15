/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.QuditF1024

@[expose] public section

namespace Qatlib.Papers.MagicDistill24.Triorthogonal

def U1SeventhExactThirdLevel : Prop :=
  InQuditThirdLevel u1Seventh ∧ ¬IsQuditClifford u1Seventh

end Qatlib.Papers.MagicDistill24.Triorthogonal
