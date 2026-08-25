/-
Copyright (c) 2026 mindofcharles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mindofcharles
-/

import VanAubelExtensions.Basic

/-!
# Algebraic and affine center identities

Part of the formalization of `paper/van-aubel-complex-structure-identity.md`.
-/

namespace VanAubelExtensions

noncomputable section

open scoped InnerProductSpace

section LinearIdentity

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The center of the square erected on the directed edge `X ⟶ Y`.

Here points have temporarily been identified with their position vectors.
The affine version below removes this choice of origin. -/
def squareCenter (J : V →ₗ[ℝ] V) (ε : ℝ) (X Y : V) : V :=
  (2 : ℝ)⁻¹ • (X + Y + ε • J (Y - X))

/-- Translating both endpoints translates the square center by the same amount.
This records explicitly that `squareCenter` is independent of the chosen
origin. -/
theorem squareCenter_translate (J : V →ₗ[ℝ] V) (ε : ℝ) (X Y t : V) :
    squareCenter J ε (X + t) (Y + t) = squareCenter J ε X Y + t := by
  simp only [squareCenter, add_sub_add_right_eq_sub]
  module

/-- The algebraic core of Van Aubel's theorem.

The assumptions are deliberately minimal: `V` is any real module, `J` is a
linear complex structure, and `ε` is either sign (expressed as `ε² = 1`). -/
theorem vanAubelIdentity (J : V →ₗ[ℝ] V) (hJ_sq : ∀ v, J (J v) = -v)
    (ε : ℝ) (hε_sq : ε ^ 2 = 1) (A B C D : V) :
    squareCenter J ε C D - squareCenter J ε A B =
      ε • J (squareCenter J ε D A - squareCenter J ε B C) := by
  rcases sq_eq_one_iff.mp hε_sq with rfl | rfl
  · simp only [squareCenter, one_smul, map_sub, map_smul, map_add, hJ_sq]
    module
  · simp only [squareCenter, neg_smul, one_smul, map_sub, map_smul, map_add, map_neg,
      hJ_sq]
    module

end LinearIdentity

section AffineIdentity

variable {V E : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V E]

/-- The square center constructed directly in an affine space. -/
def affineSquareCenter (J : V →ₗ[ℝ] V) (ε : ℝ) (X Y : E) : E :=
  (2 : ℝ)⁻¹ • ((Y -ᵥ X) + ε • J (Y -ᵥ X)) +ᵥ X

/-- Coordinates of an affine square center relative to an arbitrary origin. -/
theorem affineSquareCenter_vsub (J : V →ₗ[ℝ] V) (ε : ℝ) (O X Y : E) :
    affineSquareCenter J ε X Y -ᵥ O =
      squareCenter J ε (X -ᵥ O) (Y -ᵥ O) := by
  simp only [affineSquareCenter, vadd_vsub_assoc, squareCenter]
  rw [← vsub_sub_vsub_cancel_right Y X O]
  module

/-- Van Aubel's identity for arbitrary ordered points in an affine space.

Coincident points and zero-length edges require no separate cases because the
center formula remains meaningful. -/
theorem affineVanAubelIdentity (J : V →ₗ[ℝ] V) (hJ_sq : ∀ v, J (J v) = -v)
    (ε : ℝ) (hε_sq : ε ^ 2 = 1) (A B C D : E) :
    affineSquareCenter J ε C D -ᵥ affineSquareCenter J ε A B =
      ε • J (affineSquareCenter J ε D A -ᵥ affineSquareCenter J ε B C) := by
  rw [← vsub_sub_vsub_cancel_right (affineSquareCenter J ε C D)
      (affineSquareCenter J ε A B) A]
  rw [← vsub_sub_vsub_cancel_right (affineSquareCenter J ε D A)
      (affineSquareCenter J ε B C) A]
  simp only [affineSquareCenter_vsub]
  exact vanAubelIdentity J hJ_sq ε hε_sq (A -ᵥ A) (B -ᵥ A) (C -ᵥ A) (D -ᵥ A)

end AffineIdentity

end

end VanAubelExtensions
