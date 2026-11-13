/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonhomogPDE18.WaveModel.Defs

/-!
# Cubic phase synthesis on wave functions

Defines the wave-operator sides of equation (10) using cubic phases and coordinate shears. Five
conjugated phase blocks combine by cubic inclusion-exclusion to give the phase with exponent 2t
x_j x_k x_l. See [ArrazolaEtAl2019].

## Main statements

* `cube_inclusion_exclusion`: the cubic polarization identity isolates the product xyz.
* `eq10_decomposition`: the gate word equals the target cubic phase operator.

## References

* [Arrazola et al., 2019][ArrazolaEtAl2019]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NonhomogPDE18.CubicWord

open Qatlib.Papers.NonhomogPDE18.WaveModel

/-- Multiplication by the cubic phase with exponent `c * (x i) ^ 3` on mode `i`. -/
def cubeGate (c : ℝ) (i : Mode) : Wave → Wave :=
  multOp (cexpI (fun x => c * (x i) ^ 3))

/-- The composite shear and cubic phase word on the right-hand side of equation (10). -/
def eq10RHS (t : ℝ) : Wave → Wave :=
  subOp (sh j k) ∘
  (subOp (sh j l) ∘
    (cubeGate (t / 3) j ∘
      (subOp (shInv j l) ∘
        (subOp (shInv j k) ∘
          (subOp (sh k l) ∘
            (cubeGate (-(t / 3)) k ∘
              (subOp (shInv k l) ∘
                (subOp (sh l j) ∘
                  (cubeGate (-(t / 3)) l ∘
                    (subOp (shInv l j) ∘
                      (subOp (sh j k) ∘
                        (cubeGate (-(t / 3)) j ∘
                          (subOp (shInv j k) ∘
                            (cubeGate (t / 3) j ∘
                              (cubeGate (t / 3) k ∘
                                cubeGate (t / 3) l)))))))))))))))

/-- The target multiplication operator with phase exponent 2t x_j x_k x_l. -/
def eq10LHS (t : ℝ) : Wave → Wave :=
  multOp (cexpI (fun x => 2 * t * (x j) * (x k) * (x l)))

/-- The cubic phase on mode `j` conjugated by the shears adding modes `k` and `l`. -/
def blockA (t : ℝ) : Wave → Wave :=
  (subOp (sh j k) ∘
      (subOp (sh j l) ∘ (cubeGate (t / 3) j ∘ subOp (shInv j l)))) ∘
    subOp (shInv j k)

/-- The negative cubic phase on mode `k` conjugated by the shear adding mode `l`. -/
def blockB (t : ℝ) : Wave → Wave :=
  subOp (sh k l) ∘ (cubeGate (-(t / 3)) k ∘ subOp (shInv k l))

/-- The negative cubic phase on mode `l` conjugated by the shear adding mode `j`. -/
def blockC (t : ℝ) : Wave → Wave :=
  subOp (sh l j) ∘ (cubeGate (-(t / 3)) l ∘ subOp (shInv l j))

/-- The negative cubic phase on mode `j` conjugated by the shear adding mode `k`. -/
def blockD (t : ℝ) : Wave → Wave :=
  subOp (sh j k) ∘ (cubeGate (-(t / 3)) j ∘ subOp (shInv j k))

/-- The composite of the three single-mode cubic phases with coefficient `t / 3`. -/
def blockE (t : ℝ) : Wave → Wave :=
  cubeGate (t / 3) j ∘ (cubeGate (t / 3) k ∘ cubeGate (t / 3) l)

/-- Cubic inclusion-exclusion for three complex numbers equals six times their product. -/
theorem cube_inclusion_exclusion (x y z : ℂ) :
    (x + y + z) ^ 3 - (y + z) ^ 3 - (z + x) ^ 3 - (x + y) ^ 3 +
      x ^ 3 + y ^ 3 + z ^ 3 = 6 * x * y * z := by
  ring

/-- The first conjugated block multiplies by the phase with exponent (t/3)(x_j + x_k + x_l)^3. -/
theorem blockA_eq (t : ℝ) :
    blockA t = multOp (cexpI (fun x => (t / 3) * (x j + x k + x l) ^ 3)) := by
  unfold blockA cubeGate
  have h1 :
      subOp (sh j l) ∘
          (multOp (cexpI (fun x => (t / 3) * (x j) ^ 3)) ∘ subOp (shInv j l)) =
        multOp (cexpI (fun x => (t / 3) * (x j + x l) ^ 3)) := by
    rw [conj_mult (shInv_comp_sh (i := j) (m := l) (by decide))]
    congr 1
  rw [h1]
  rw [Function.comp_assoc]
  rw [conj_mult (shInv_comp_sh (i := j) (m := k) (by decide))]
  congr 1

/-- The second block multiplies by the phase with exponent -(t/3)(x_k + x_l)^3. -/
theorem blockB_eq (t : ℝ) :
    blockB t = multOp (cexpI (fun x => (-(t / 3)) * (x k + x l) ^ 3)) := by
  unfold blockB cubeGate
  rw [conj_mult (shInv_comp_sh (i := k) (m := l) (by decide))]
  congr 1

/-- The third block multiplies by the phase with exponent -(t/3)(x_l + x_j)^3. -/
theorem blockC_eq (t : ℝ) :
    blockC t = multOp (cexpI (fun x => (-(t / 3)) * (x l + x j) ^ 3)) := by
  unfold blockC cubeGate
  rw [conj_mult (shInv_comp_sh (i := l) (m := j) (by decide))]
  congr 1

/-- The fourth block multiplies by the phase with exponent -(t/3)(x_j + x_k)^3. -/
theorem blockD_eq (t : ℝ) :
    blockD t = multOp (cexpI (fun x => (-(t / 3)) * (x j + x k) ^ 3)) := by
  unfold blockD cubeGate
  rw [conj_mult (shInv_comp_sh (i := j) (m := k) (by decide))]
  congr 1

/-- The final block multiplies by the phase with exponent (t/3)(x_j^3 + x_k^3 + x_l^3). -/
theorem blockE_eq (t : ℝ) :
    blockE t =
      multOp (cexpI (fun x =>
        (t / 3) * (x j) ^ 3 + (t / 3) * (x k) ^ 3 + (t / 3) * (x l) ^ 3)) := by
  unfold blockE cubeGate
  exact merge_three _ _ _

/-- The source cubic gate word factors into the five phase blocks in order. -/
theorem eq10RHS_eq_blocks (t : ℝ) :
    eq10RHS t = blockA t ∘ (blockB t ∘ (blockC t ∘ (blockD t ∘ blockE t))) := by
  unfold eq10RHS blockA blockB blockC blockD blockE
  simp only [Function.comp_assoc]

/-- The sum of the five block exponents simplifies to 2t x_j x_k x_l. -/
theorem eq10_exponent (t : ℝ) (x : Mode → ℝ) :
    (t / 3) * (x j + x k + x l) ^ 3 + (-(t / 3)) * (x k + x l) ^ 3 +
        (-(t / 3)) * (x l + x j) ^ 3 + (-(t / 3)) * (x j + x k) ^ 3 +
          ((t / 3) * (x j) ^ 3 + (t / 3) * (x k) ^ 3 + (t / 3) * (x l) ^ 3) =
      2 * t * (x j) * (x k) * (x l) := by
  ring

/-- The cubic gate word equals the target phase multiplication operator. See [Arrazola et al.,
equation (10)][ArrazolaEtAl2019]. -/
theorem eq10_decomposition (t : ℝ) : eq10RHS t = eq10LHS t := by
  rw [eq10RHS_eq_blocks, blockA_eq, blockB_eq, blockC_eq, blockD_eq, blockE_eq,
    merge_five]
  unfold eq10LHS
  congr 1
  funext x
  simp only [cexpI_apply]
  congr 1
  congr 1
  exact_mod_cast eq10_exponent t x

end Qatlib.Papers.NonhomogPDE18.CubicWord
