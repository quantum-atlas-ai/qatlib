/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeProductSliceCloseness
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeMvPolynomial

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open scoped Classical BigOperators

/-- Bounds both product-slice variance and influence differences by forty-eight times the
squared degree over the square root of the dimension. -/
theorem cube_product_slice_moment_error {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {n d : ℕ}
    {f : (Fin n → Bool) → ℝ} (hb : ∀ x, f x ∈ Set.Icc 0 1) (hd : CubeDegreeLE d f) :
    |cubeVar n (muWeight p n) f-cubeVar n (nuWeight p n) f| ≤ 48*(d : ℝ)^2/Real.sqrt (n : ℝ) ∧
    ∀ i, |cubeInf n (muWeight p n) f i-cubeInf n (nuWeight p n) f i| ≤
      48*(d : ℝ)^2/Real.sqrt (n : ℝ) := by
  have h2 : CubeDegreeLE (2*d) (fun x => f x^2) := by
    simpa only [two_mul,pow_two] using cube_degree_mul hd hd
  have hb2 (x) : f x^2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact sq_nonneg _
    · nlinarith [(hb x).1,(hb x).2]
  have he := cube_product_slice_expectation_error hp0 hp1 hb hd
  have he2 := cube_product_slice_expectation_error hp0 hp1 hb2 h2
  have hwμ := muWeight_cubeWeight hp0.le hp1.le n
  have hwν := nuWeight_cubeWeight hp0 hp1 n
  have hmμ := cube_expect_range hwμ hb
  have hmν := cube_expect_range hwν hb
  have hc : 0 ≤ 8*(d : ℝ)^2/Real.sqrt (n : ℝ) := by positivity
  have h2c : 8*((2*d : ℕ) : ℝ)^2/Real.sqrt (n : ℝ) =
      4*(8*(d : ℝ)^2/Real.sqrt (n : ℝ)) := by push_cast; ring
  rw [h2c] at he2
  constructor
  · rw [cube_var_eq_second_moment_sub_sq n hwμ f, cube_var_eq_second_moment_sub_sq n hwν f]
    have hsq : |(cubeExpect n (muWeight p n) f)^2-(cubeExpect n (nuWeight p n) f)^2| ≤
        2*|cubeExpect n (muWeight p n) f-cubeExpect n (nuWeight p n) f| := by
      rw [show (cubeExpect n (muWeight p n) f)^2-(cubeExpect n (nuWeight p n) f)^2 =
        (cubeExpect n (muWeight p n) f-cubeExpect n (nuWeight p n) f)*
          (cubeExpect n (muWeight p n) f+cubeExpect n (nuWeight p n) f) by ring,
        abs_mul,abs_of_nonneg (show 0 ≤ cubeExpect n (muWeight p n) f+cubeExpect n (nuWeight p n) f by linarith [hmμ.1,hmν.1])]
      calc
        _ ≤ |cubeExpect n (muWeight p n) f-cubeExpect n (nuWeight p n) f| * 2 :=
          mul_le_mul_of_nonneg_left (by linarith [hmμ.2,hmν.2]) (abs_nonneg _)
        _ = _ := by ring
    have ht := abs_sub_le (cubeExpect n (muWeight p n) (fun x => f x^2)-cubeExpect n (nuWeight p n) (fun x => f x^2))
      0 ((cubeExpect n (muWeight p n) f)^2-(cubeExpect n (nuWeight p n) f)^2)
    have hre : (cubeExpect n (muWeight p n) (fun x => f x^2)-(cubeExpect n (muWeight p n) f)^2)-
        (cubeExpect n (nuWeight p n) (fun x => f x^2)-(cubeExpect n (nuWeight p n) f)^2) =
      (cubeExpect n (muWeight p n) (fun x => f x^2)-cubeExpect n (nuWeight p n) (fun x => f x^2))-
        ((cubeExpect n (muWeight p n) f)^2-(cubeExpect n (nuWeight p n) f)^2) := by ring
    rw [hre]
    simp only [sub_zero,zero_sub,abs_neg] at ht
    have hs := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2)
    rw [show 48*(d : ℝ)^2/Real.sqrt (n : ℝ) = 6*(8*(d : ℝ)^2/Real.sqrt (n : ℝ)) by ring]
    linarith only [ht,hsq,hs,he2]
  · intro i
    let g := fun x => f x-f (cubeFlip x i)
    have hg : CubeDegreeLE d g := cube_degree_sub hd (cube_degree_flip hd i)
    have hgsq : CubeDegreeLE (2*d) (fun x => g x^2) := by
      simpa only [two_mul,pow_two] using cube_degree_mul hg hg
    have hgb (x) : g x^2 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact sq_nonneg _
      · have ha : |g x| ≤ 1 := abs_le.2 ⟨by dsimp [g]; linarith [(hb x).1,(hb (cubeFlip x i)).2],
            by dsimp [g]; linarith [(hb x).2,(hb (cubeFlip x i)).1]⟩
        nlinarith [sq_abs (g x),abs_nonneg (g x)]
    have hi := cube_product_slice_expectation_error hp0 hp1 hgb hgsq
    rw [h2c] at hi
    change |cubeExpect n (muWeight p n) (fun x => g x^2)-cubeExpect n (nuWeight p n)
        (fun x => g x^2)| ≤ _
    apply hi.trans
    rw [show 48*(d : ℝ)^2/Real.sqrt (n : ℝ) = 6*(8*(d : ℝ)^2/Real.sqrt (n : ℝ)) by ring]
    linarith only [hc]

end Qatlib.Concepts.ProbabilityCore.DistributionAA
