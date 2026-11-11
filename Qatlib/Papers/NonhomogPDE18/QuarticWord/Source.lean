/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonhomogPDE18.CubicWord.Source

/-!
# Quartic phase synthesis on wave functions

Defines the wave-operator sides of equation (11), using cubic and sixth-degree phases together
with linear and quadratic coordinate shears. The five phase blocks combine to produce the
quartic exponent 6t x_j^2 x_k x_l; separate constants record the reported gate counts. See
[ArrazolaEtAl2019].

## Main statements

* `eq11_decomposition`: the gate word equals the target quartic phase operator.
* `reported_gate_counts`: the recorded counts are 873 and 1749.

## References

* [Arrazola et al., 2019][ArrazolaEtAl2019]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NonhomogPDE18.QuarticWord

open Qatlib.Papers.NonhomogPDE18.WaveModel
open Qatlib.Papers.NonhomogPDE18.CubicWord (cubeGate cube_inclusion_exclusion)

/-- Multiplication by the sixth-degree phase with exponent `c * (x i) ^ 6` on mode `i`. -/
def sixthGate (c : ℝ) (i : Mode) : Wave → Wave :=
  multOp (cexpI (fun x => c * (x i) ^ 6))

/-- The composite linear-shear, quadratic-shear, and phase word on the right-hand side of
equation (11). -/
def eq11RHS (t : ℝ) : Wave → Wave :=
  subOp (sh k l) ∘
  (subOp (shSq k j) ∘
    (cubeGate t k ∘
      (subOp (shSqInv k j) ∘
        (subOp (shInv k l) ∘
          (subOp (shSq k j) ∘
            (cubeGate (-t) k ∘
              (subOp (shSqInv k j) ∘
                (subOp (sh k l) ∘
                  (cubeGate (-t) k ∘
                    (subOp (shInv k l) ∘
                      (subOp (shSq l j) ∘
                        (cubeGate (-t) l ∘
                          (subOp (shSqInv l j) ∘
                            (cubeGate t k ∘
                              (sixthGate t j ∘
                                cubeGate t l)))))))))))))))

/-- The target multiplication operator with phase exponent 6t x_j^2 x_k x_l. -/
def eq11LHS (t : ℝ) : Wave → Wave :=
  multOp (cexpI (fun x => 6 * t * (x j) ^ 2 * (x k) * (x l)))

/-- The cubic phase on mode `k` conjugated by shears adding `x_l` and `x_j^2` to that
coordinate. -/
def b11A (t : ℝ) : Wave → Wave :=
  (subOp (sh k l) ∘
      (subOp (shSq k j) ∘ (cubeGate t k ∘ subOp (shSqInv k j)))) ∘
    subOp (shInv k l)

/-- The negative cubic phase on mode `k` conjugated by the quadratic shear from mode `j`. -/
def b11B (t : ℝ) : Wave → Wave :=
  subOp (shSq k j) ∘ (cubeGate (-t) k ∘ subOp (shSqInv k j))

/-- The negative cubic phase on mode `k` conjugated by the linear shear from mode `l`. -/
def b11C (t : ℝ) : Wave → Wave :=
  subOp (sh k l) ∘ (cubeGate (-t) k ∘ subOp (shInv k l))

/-- The negative cubic phase on mode `l` conjugated by the quadratic shear from mode `j`. -/
def b11D (t : ℝ) : Wave → Wave :=
  subOp (shSq l j) ∘ (cubeGate (-t) l ∘ subOp (shSqInv l j))

/-- The composite of cubic phases on modes `k` and `l` and a sixth-degree phase on mode `j`,
each with coefficient `t`. -/
def b11E (t : ℝ) : Wave → Wave :=
  cubeGate t k ∘ (sixthGate t j ∘ cubeGate t l)

/-- The first block multiplies by the phase with exponent t(x_k + x_l + x_j^2)^3. -/
theorem b11A_eq (t : ℝ) :
    b11A t = multOp (cexpI (fun x => t * (x k + x l + (x j) ^ 2) ^ 3)) := by
  unfold b11A cubeGate
  have h1 :
      subOp (shSq k j) ∘
          (multOp (cexpI (fun x => t * (x k) ^ 3)) ∘ subOp (shSqInv k j)) =
        multOp (cexpI (fun x => t * (x k + (x j) ^ 2) ^ 3)) := by
    rw [conj_mult (shSqInv_comp_shSq (i := k) (m := j) (by decide))]
    congr 1
  rw [h1]
  rw [Function.comp_assoc]
  rw [conj_mult (shInv_comp_sh (i := k) (m := l) (by decide))]
  congr 1

/-- The second block multiplies by the phase with exponent -t(x_k + x_j^2)^3. -/
theorem b11B_eq (t : ℝ) :
    b11B t = multOp (cexpI (fun x => (-t) * (x k + (x j) ^ 2) ^ 3)) := by
  unfold b11B cubeGate
  rw [conj_mult (shSqInv_comp_shSq (i := k) (m := j) (by decide))]
  congr 1

/-- The third block multiplies by the phase with exponent -t(x_k + x_l)^3. -/
theorem b11C_eq (t : ℝ) :
    b11C t = multOp (cexpI (fun x => (-t) * (x k + x l) ^ 3)) := by
  unfold b11C cubeGate
  rw [conj_mult (shInv_comp_sh (i := k) (m := l) (by decide))]
  congr 1

/-- The fourth block multiplies by the phase with exponent -t(x_l + x_j^2)^3. -/
theorem b11D_eq (t : ℝ) :
    b11D t = multOp (cexpI (fun x => (-t) * (x l + (x j) ^ 2) ^ 3)) := by
  unfold b11D cubeGate
  rw [conj_mult (shSqInv_comp_shSq (i := l) (m := j) (by decide))]
  congr 1

/-- The final block multiplies by the phase with exponent t(x_k^3 + x_j^6 + x_l^3). -/
theorem b11E_eq (t : ℝ) :
    b11E t =
      multOp (cexpI (fun x =>
        t * (x k) ^ 3 + t * (x j) ^ 6 + t * (x l) ^ 3)) := by
  unfold b11E cubeGate sixthGate
  exact merge_three _ _ _

/-- The source quartic gate word factors into the five phase blocks in order. -/
theorem eq11RHS_eq_blocks (t : ℝ) :
    eq11RHS t = b11A t ∘ (b11B t ∘ (b11C t ∘ (b11D t ∘ b11E t))) := by
  unfold eq11RHS b11A b11B b11C b11D b11E
  simp only [Function.comp_assoc]

/-- The sum of the five block exponents simplifies to 6t x_j^2 x_k x_l. -/
theorem eq11_exponent (t : ℝ) (x : Mode → ℝ) :
    t * (x k + x l + (x j) ^ 2) ^ 3 + (-t) * (x k + (x j) ^ 2) ^ 3 +
        (-t) * (x k + x l) ^ 3 + (-t) * (x l + (x j) ^ 2) ^ 3 +
          (t * (x k) ^ 3 + t * (x j) ^ 6 + t * (x l) ^ 3) =
      6 * t * (x j) ^ 2 * (x k) * (x l) := by
  ring

/-- The quartic gate word equals the target phase multiplication operator. See [Arrazola et al.,
equation (11)][ArrazolaEtAl2019]. -/
theorem eq11_decomposition (t : ℝ) : eq11RHS t = eq11LHS t := by
  rw [eq11RHS_eq_blocks, b11A_eq, b11B_eq, b11C_eq, b11D_eq, b11E_eq, merge_five]
  unfold eq11LHS
  congr 1
  funext x
  simp only [cexpI_apply]
  congr 1
  congr 1
  exact_mod_cast eq11_exponent t x

/-- The recorded universal-gate count, 873. -/
def reportedUniversalGateCount : ℕ := 873

/-- The recorded X-only gate count, 1749. -/
def reportedXOnlyGateCount : ℕ := 1749

/-- The two recorded gate counts are 873 universal gates and 1749 X-only gates. -/
theorem reported_gate_counts :
    reportedUniversalGateCount = 873 ∧ reportedXOnlyGateCount = 1749 :=
  ⟨rfl, rfl⟩

end Qatlib.Papers.NonhomogPDE18.QuarticWord
