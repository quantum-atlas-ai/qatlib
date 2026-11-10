/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkFind.SearchAlgorithm
set_option autoImplicit false
namespace Qatlib.Concepts.WalkFind.UniqueCollision

def NativeJohnsonData : Prop := NativeJohnsonDataContract
end Qatlib.Concepts.WalkFind.UniqueCollision
