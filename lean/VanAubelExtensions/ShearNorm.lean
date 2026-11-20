/-
Copyright (c) 2026 mindofcharles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mindofcharles
-/

import VanAubelExtensions.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Sharp scalar estimates for shear operators

The quadratic identity and inequality provide the norm bounds used by
`ExceptionalNorm`.
-/

namespace VanAubelExtensions

noncomputable section

/-- For `0 ≤ t`, the largest singular value of a two-dimensional shear of size `t`. -/
def shearNorm (t : ℝ) : ℝ := (Real.sqrt (t ^ 2 + 4) + t) / 2

theorem shearNorm_pos {t : ℝ} (ht : 0 ≤ t) : 0 < shearNorm t := by
  have hs : 0 < Real.sqrt (t ^ 2 + 4) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
  dsimp [shearNorm]
  positivity

theorem shearNorm_quadratic (t : ℝ) : shearNorm t ^ 2 - t * shearNorm t - 1 = 0 := by
  have hs := Real.sq_sqrt (show 0 ≤ t ^ 2 + 4 by nlinarith [sq_nonneg t])
  dsimp [shearNorm]
  nlinarith

@[simp] theorem shearNorm_zero : shearNorm 0 = 1 := by
  have hs := Real.sq_sqrt (show 0 ≤ (4 : ℝ) by norm_num)
  have hn := Real.sqrt_nonneg (4 : ℝ)
  dsimp [shearNorm]
  norm_num only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_add]
  nlinarith

theorem shearNorm_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    shearNorm s ≤ shearNorm t := by
  have hsq : s ^ 2 + 4 ≤ t ^ 2 + 4 := by nlinarith
  have hroot := Real.sqrt_le_sqrt hsq
  dsimp [shearNorm]
  linarith

theorem one_le_shearNorm {t : ℝ} (ht : 0 ≤ t) : 1 ≤ shearNorm t := by
  have hp := shearNorm_pos ht
  have hq := shearNorm_quadratic t
  nlinarith [mul_nonneg ht hp.le]

/-- The sharp quadratic estimate for the shear, including the zero parameter. -/
theorem shear_quadratic_bound {t : ℝ} (ht : 0 ≤ t) (a b : ℝ) :
    (a + t * b) ^ 2 + b ^ 2 ≤ shearNorm t ^ 2 * (a ^ 2 + b ^ 2) := by
  let q := shearNorm t
  have hq : 0 < q := shearNorm_pos ht
  have hrel : q ^ 2 - t * q - 1 = 0 := shearNorm_quadratic t
  have hid : q * (q ^ 2 * (a ^ 2 + b ^ 2) - ((a + t * b) ^ 2 + b ^ 2)) =
      t * (q * a - b) ^ 2 := by
    linear_combination (q * a ^ 2 + (q + t) * b ^ 2) * hrel
  have hh := mul_nonneg ht (sq_nonneg (q * a - b))
  rw [← hid] at hh
  have hnonneg := nonneg_of_mul_nonneg_right hh hq
  linarith

/-- The same bound for a complex shear with an arbitrary unit phase. -/
theorem complex_shear_bound {t : ℝ} (ht : 0 ≤ t) (c a b : ℂ) (hc : ‖c‖ = 1) :
    ‖a + c * (t : ℂ) * star b‖ ^ 2 + ‖b‖ ^ 2 ≤
      shearNorm t ^ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hb : ‖a + c * (t : ℂ) * star b‖ ≤ ‖a‖ + t * ‖b‖ := by
    calc
      _ ≤ ‖a‖ + ‖c * (t : ℂ) * star b‖ := norm_add_le _ _
      _ = ‖a‖ + t * ‖b‖ := by
        rw [norm_mul, norm_mul, hc, norm_star, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ht, one_mul]
  have hs : ‖a + c * (t : ℂ) * star b‖ ^ 2 ≤ (‖a‖ + t * ‖b‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (mul_nonneg ht (norm_nonneg _)))).mpr hb
  nlinarith [shear_quadratic_bound ht ‖a‖ ‖b‖]

end

end VanAubelExtensions
