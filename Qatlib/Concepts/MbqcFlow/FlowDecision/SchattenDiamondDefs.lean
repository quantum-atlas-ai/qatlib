/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Basic state-space imports for Schatten developments

Provides the qubit and finite-state imports used by the Schatten interface. The imported
`QState` and `Operator` types supply the finite-dimensional vector and matrix language for
subsequent norm calculations.

This module adds no declarations of its own. The underlying finite-dimensional quantum state
formalism is described in [NielsenChuang2010].

## Main statements

* `QState` and `Operator`: imported finite-dimensional state and operator types.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
