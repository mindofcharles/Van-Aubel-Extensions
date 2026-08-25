/-
Copyright (c) 2026 mindofcharles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mindofcharles
-/

import VanAubelExtensions.CenterIdentity

/-!
# The midpoint J-square

Part of the formalization of `paper/van-aubel-complex-structure-identity.md`.
-/

namespace VanAubelExtensions

noncomputable section

open scoped InnerProductSpace

section MidpointSquare

variable {V₀ E₀ : Type*} [AddCommGroup V₀] [Module ℝ V₀] [AddTorsor V₀ E₀]

/-- The four side-midpoints of any center quadrilateral satisfying the Van
Aubel vector identity form a `J`-parallelogram, with adjacent sides related by
the same quarter-turn. -/
theorem centerSideMidpoints_form_J_square
    (J : V₀ →ₗ[ℝ] V₀) (ε : ℝ)
    (P Q R S : E₀) (h : R -ᵥ P = ε • J (S -ᵥ Q)) :
    let U₁ := midpoint ℝ P Q
    let U₂ := midpoint ℝ Q R
    let U₃ := midpoint ℝ R S
    let U₄ := midpoint ℝ S P
    U₂ -ᵥ U₁ = ε • J (U₃ -ᵥ U₂) ∧
      U₃ -ᵥ U₄ = U₂ -ᵥ U₁ ∧
      U₄ -ᵥ U₁ = U₃ -ᵥ U₂ := by
  dsimp only
  have h₁₂ : midpoint ℝ Q R -ᵥ midpoint ℝ P Q =
      (2 : ℝ)⁻¹ • (R -ᵥ P) := by
    rw [midpoint_comm (R := ℝ) P Q]
    simpa using midpoint_vsub_midpoint_same_left (R := ℝ) Q R P
  have h₂₃ : midpoint ℝ R S -ᵥ midpoint ℝ Q R =
      (2 : ℝ)⁻¹ • (S -ᵥ Q) := by
    rw [midpoint_comm (R := ℝ) Q R]
    simpa using midpoint_vsub_midpoint_same_left (R := ℝ) R S Q
  have h₃₄ : midpoint ℝ R S -ᵥ midpoint ℝ S P =
      midpoint ℝ Q R -ᵥ midpoint ℝ P Q := by
    rw [midpoint_comm (R := ℝ) R S, midpoint_comm (R := ℝ) P Q]
    have hleft := midpoint_vsub_midpoint_same_left (R := ℝ) S R P
    have hright := midpoint_vsub_midpoint_same_left (R := ℝ) Q R P
    rw [hleft, hright]
  have h₄₁ : midpoint ℝ S P -ᵥ midpoint ℝ P Q =
      midpoint ℝ R S -ᵥ midpoint ℝ Q R := by
    rw [midpoint_comm (R := ℝ) S P, midpoint_comm (R := ℝ) Q R]
    have hleft := midpoint_vsub_midpoint_same_left (R := ℝ) P S Q
    have hright := midpoint_vsub_midpoint_same_left (R := ℝ) R S Q
    rw [hleft, hright]
  refine ⟨?_, h₃₄, h₄₁⟩
  calc
    midpoint ℝ Q R -ᵥ midpoint ℝ P Q = (2 : ℝ)⁻¹ • (R -ᵥ P) := h₁₂
    _ = (2 : ℝ)⁻¹ • (ε • J (S -ᵥ Q)) := by rw [h]
    _ = ε • J ((2 : ℝ)⁻¹ • (S -ᵥ Q)) := by
      rw [map_smul]
      module
    _ = ε • J (midpoint ℝ R S -ᵥ midpoint ℝ Q R) := by rw [h₂₃]

/-- Section 6 of the paper specialized to the four centers constructed on
`AB`, `BC`, `CD`, and `DA`. -/
theorem vanAubelCenters_midpointSquare
    (J : V₀ →ₗ[ℝ] V₀) (hJ_sq : ∀ v, J (J v) = -v)
    (ε : ℝ) (hε_sq : ε ^ 2 = 1) (A B C D : E₀) :
    let P := affineSquareCenter J ε A B
    let Q := affineSquareCenter J ε B C
    let R := affineSquareCenter J ε C D
    let S := affineSquareCenter J ε D A
    let U₁ := midpoint ℝ P Q
    let U₂ := midpoint ℝ Q R
    let U₃ := midpoint ℝ R S
    let U₄ := midpoint ℝ S P
    U₂ -ᵥ U₁ = ε • J (U₃ -ᵥ U₂) ∧
      U₃ -ᵥ U₄ = U₂ -ᵥ U₁ ∧
      U₄ -ᵥ U₁ = U₃ -ᵥ U₂ := by
  dsimp only
  exact centerSideMidpoints_form_J_square J ε _ _ _ _
    (affineVanAubelIdentity J hJ_sq ε hε_sq A B C D)

/-- Under an orthogonal complex structure, adjacent sides of the midpoint
parallelogram have equal length. -/
theorem centerSideMidpoints_adjacent_norm_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {F : Type*} [AddTorsor H F] (J : OrthogonalComplexStructure H)
    (ε : ℝ) (hε_sq : ε ^ 2 = 1) (P Q R S : F)
    (h : R -ᵥ P = ε • J (S -ᵥ Q)) :
    ‖midpoint ℝ Q R -ᵥ midpoint ℝ P Q‖ =
      ‖midpoint ℝ R S -ᵥ midpoint ℝ Q R‖ := by
  have hs := (centerSideMidpoints_form_J_square J.toLinearMap ε P Q R S h).1
  rw [hs, norm_smul]
  change ‖ε‖ * ‖J _‖ = _
  rw [J.norm_map]
  rcases sq_eq_one_iff.mp hε_sq with rfl | rfl <;> simp

/-- Under an orthogonal complex structure, adjacent sides of the midpoint
parallelogram are orthogonal. -/
theorem centerSideMidpoints_adjacent_inner_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {F : Type*} [AddTorsor H F] (J : OrthogonalComplexStructure H)
    (ε : ℝ) (P Q R S : F) (h : R -ᵥ P = ε • J (S -ᵥ Q)) :
    inner ℝ (midpoint ℝ Q R -ᵥ midpoint ℝ P Q)
      (midpoint ℝ R S -ᵥ midpoint ℝ Q R) = 0 := by
  have hs := (centerSideMidpoints_form_J_square J.toLinearMap ε P Q R S h).1
  rw [hs, real_inner_smul_left]
  change ε * inner ℝ (J _) _ = 0
  rw [J.inner_map_self_eq_zero]
  simp

end MidpointSquare

end

end VanAubelExtensions
