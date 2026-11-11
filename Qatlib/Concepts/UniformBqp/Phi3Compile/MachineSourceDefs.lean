/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.LocalMachineDefs
import Qatlib.Concepts.CircuitImpl.Phi3Universal.Phi3UniversalityTheorem1Quan
import Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp
import Qatlib.Concepts.UniformBqp.OracleAmplify.StandardOracleTidyAmplificationStre

/-!
# Dependencies for machine-source constructions

This module gathers local-machine definitions, Phi3 universality, uniform BQP interfaces, and
tidy standard-oracle amplification for machine-source constructions. It provides the common
imports used by the source-level estimates and circuit translations. The background is described
in [BernsteinVazirani1997].

## Main statements

* `LocalQTM`: the imported local quantum Turing-machine interface.
* `standardOracleTidyAmplification`: the imported clean-output amplification theorem.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
