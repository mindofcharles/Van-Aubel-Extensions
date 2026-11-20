/-
Copyright (c) 2026 mindofcharles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mindofcharles
-/

import VanAubelExtensions.Rigidity
import VanAubelExtensions.ComplexAffineTransfer

/-!
# Configuration-dependent defects and the common-operator characterization

Formal counterparts of the defect and common-parallelogram results in
`paper/van-aubel-edge-operator-realizations-and-rigidity.md`.
-/

namespace VanAubelExtensions

noncomputable section

section RealOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The failure of the prescribed opposite-center relation on one quadruple. -/
def operatorDefect (K L₁ L₂ L₃ L₄ : V →ₗ[ℝ] V) (A B C D : V) : V :=
  operatorCenter L₃ C D - operatorCenter L₁ A B -
    K (operatorCenter L₄ D A - operatorCenter L₂ B C)

theorem operatorDefect_sub_origin (K L₁ L₂ L₃ L₄ : V →ₗ[ℝ] V) (O A B C D : V) :
    operatorDefect K L₁ L₂ L₃ L₄ (A - O) (B - O) (C - O) (D - O) =
      operatorDefect K L₁ L₂ L₃ L₄ A B C D := by
  simp only [operatorDefect, operatorCenter, map_add, map_sub, map_smul]
  module

/-- The cyclic defect formula does not require any complex-structure hypothesis. -/
theorem operatorDefect_cyclic (K L₁ L₂ L₃ L₄ : V →ₗ[ℝ] V) (A B C D : V) :
    (2 : ℝ) • operatorDefect K L₁ L₂ L₃ L₄ A B C D =
      (K - L₁) (B - A) + ((LinearMap.id : V →ₗ[ℝ] V) + K.comp L₂) (C - B) +
        (L₃ - K) (D - C) - ((LinearMap.id : V →ₗ[ℝ] V) + K.comp L₄) (A - D) := by
  simp only [operatorDefect, operatorCenter, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.id_apply, LinearMap.comp_apply, map_sub, map_add, map_smul]
  module

/-- With one common edge operator, the universal target is forced to be that
operator, and its square is forced to be minus the identity. -/
theorem universalCommonOperatorIdentity_iff (H L : V →ₗ[ℝ] V) :
    UniversalOperatorIdentity H L L L L ↔ H = L ∧ IsLinearComplexStructure L := by
  constructor
  · intro h
    have hC (v : V) : v - L v = -(H v + H (L v)) := by
      have hv := congrArg (fun x : V => (2 : ℝ) • x) (h 0 0 v 0)
      simpa [operatorCenter, map_smul, map_sub, map_add, sub_eq_add_neg] using hv
    have hD (v : V) : v + L v = H v - H (L v) := by
      have hv := congrArg (fun x : V => (2 : ℝ) • x) (h 0 0 0 v)
      simpa [operatorCenter, map_smul, map_sub, map_add, sub_eq_add_neg] using hv
    have hHL : H = L := by
      ext v
      have htwo : (2 : ℝ) • H v = (2 : ℝ) • L v := by
        calc
          (2 : ℝ) • H v = (H v - H (L v)) - -(H v + H (L v)) := by module
          _ = (v + L v) - (v - L v) := by rw [← hD v, ← hC v]
          _ = (2 : ℝ) • L v := by module
      simpa [smul_smul] using congrArg (fun x : V => (2 : ℝ)⁻¹ • x) htwo
    refine ⟨hHL, ?_⟩
    intro v
    have hv := hD v
    rw [hHL] at hv
    calc
      L (L v) = L v - (L v - L (L v)) := by module
      _ = L v - (v + L v) := by rw [← hv]
      _ = -v := by module
  · rintro ⟨hHL, hL⟩
    subst H
    simpa using universalOperatorIdentity_of_parametrization L 0 hL

theorem exists_universalCommonOperatorIdentity_iff (L : V →ₗ[ℝ] V) :
    (∃ H, UniversalOperatorIdentity H L L L L) ↔ IsLinearComplexStructure L := by
  simp only [universalCommonOperatorIdentity_iff, exists_eq_left]

/-- Intrinsic affine form of the common-operator characterization. -/
theorem affineUniversalCommonOperatorIdentity_iff
    {E : Type*} [AddTorsor V E] [Nonempty E] (H L : V →ₗ[ℝ] V) :
    AffineUniversalOperatorIdentity (E := E) H L L L L ↔
      H = L ∧ IsLinearComplexStructure L := by
  rw [affineUniversalOperatorIdentity_iff, universalCommonOperatorIdentity_iff]

/-- Among fixed directly similar parallelograms, the two signed square
operators are exactly the complex structures. -/
theorem similarParallelogram_complexStructure_iff [Nontrivial V]
    (J : V →ₗ[ℝ] V) (hJ : IsLinearComplexStructure J) (a b : ℝ) :
    IsLinearComplexStructure (a • LinearMap.id + b • J) ↔
      a = 0 ∧ (b = 1 ∨ b = -1) := by
  constructor
  · intro hL
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hz : complexScalarAction J ⟨a ^ 2 - b ^ 2 + 1, 2 * a * b⟩ v = 0 := by
      have heq := hL v
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
        map_add, map_smul] at heq
      rw [hJ v] at heq
      calc
        complexScalarAction J ⟨a ^ 2 - b ^ 2 + 1, 2 * a * b⟩ v =
            (a • (a • v + b • J v) + b • (a • J v + b • -v)) + v := by
              simp only [complexScalarAction]; module
        _ = -v + v := by rw [heq]
        _ = 0 := by module
    have hc := (complexScalarAction_eq_zero_iff J hJ hv).mp hz
    have hre := congrArg Complex.re hc
    have him := congrArg Complex.im hc
    simp only [Complex.zero_re, Complex.zero_im] at hre him
    have ha : a = 0 := by
      rcases mul_eq_zero.mp (show a * b = 0 by nlinarith [him]) with ha | hb
      · exact ha
      · nlinarith [sq_nonneg a]
    refine ⟨ha, ?_⟩
    exact sq_eq_one_iff.mp (by nlinarith [hre, ha])
  · rintro ⟨rfl, rfl | rfl⟩ <;>
      simpa [IsLinearComplexStructure, hJ] using hJ

end RealOperators

section AffineDefects

variable {V E : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V E]

/-- The defect defined intrinsically by the four affine centers. -/
def affineOperatorDefect (K L₁ L₂ L₃ L₄ : V →ₗ[ℝ] V) (A B C D : E) : V :=
  (affineOperatorCenter L₃ C D -ᵥ affineOperatorCenter L₁ A B) -
    K (affineOperatorCenter L₄ D A -ᵥ affineOperatorCenter L₂ B C)

theorem affineOperatorDefect_eq_coordinates
    (K L₁ L₂ L₃ L₄ : V →ₗ[ℝ] V) (O A B C D : E) :
    affineOperatorDefect K L₁ L₂ L₃ L₄ A B C D =
      operatorDefect K L₁ L₂ L₃ L₄ (A -ᵥ O) (B -ᵥ O) (C -ᵥ O) (D -ᵥ O) := by
  unfold affineOperatorDefect operatorDefect
  rw [← vsub_sub_vsub_cancel_right
    (affineOperatorCenter L₃ C D) (affineOperatorCenter L₁ A B) O]
  rw [← vsub_sub_vsub_cancel_right
    (affineOperatorCenter L₄ D A) (affineOperatorCenter L₂ B C) O]
  simp only [affineOperatorCenter_vsub]

theorem affineOperatorDefect_cyclic
    (K L₁ L₂ L₃ L₄ : V →ₗ[ℝ] V) (A B C D : E) :
    (2 : ℝ) • affineOperatorDefect K L₁ L₂ L₃ L₄ A B C D =
      (K - L₁) (B -ᵥ A) + ((LinearMap.id : V →ₗ[ℝ] V) + K.comp L₂) (C -ᵥ B) +
        (L₃ - K) (D -ᵥ C) - ((LinearMap.id : V →ₗ[ℝ] V) + K.comp L₄) (A -ᵥ D) := by
  rw [affineOperatorDefect_eq_coordinates K L₁ L₂ L₃ L₄ A, operatorDefect_cyclic]
  simp only [vsub_sub_vsub_cancel_right]

end AffineDefects

end

end VanAubelExtensions
