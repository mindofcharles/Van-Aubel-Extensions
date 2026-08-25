/-
Copyright (c) 2026 mindofcharles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mindofcharles
-/

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.Midpoint
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Basic complex-structure infrastructure

Part of the formalization of `paper/van-aubel-complex-structure-identity.md`.
-/

namespace VanAubelExtensions

noncomputable section

open scoped InnerProductSpace

/-- An orthogonal complex structure on a real inner-product space.

Bundling `J` this way records both metric preservation and the equation
`J² = -I`.  The equivalence field is natural because `-J` is the inverse of
`J` whenever `J² = -I`. -/
structure OrthogonalComplexStructure (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] where
  toLinearIsometryEquiv : V ≃ₗᵢ[ℝ] V
  sq_apply : ∀ v, toLinearIsometryEquiv (toLinearIsometryEquiv v) = -v

namespace OrthogonalComplexStructure

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

instance : CoeFun (OrthogonalComplexStructure V) fun _ => V → V :=
  ⟨fun J => J.toLinearIsometryEquiv⟩

/-- The underlying real-linear map. -/
def toLinearMap (J : OrthogonalComplexStructure V) : V →ₗ[ℝ] V :=
  J.toLinearIsometryEquiv.toLinearMap

/-- The underlying linear isometry. -/
def toLinearIsometry (J : OrthogonalComplexStructure V) : V →ₗᵢ[ℝ] V :=
  J.toLinearIsometryEquiv.toLinearIsometry

@[simp]
theorem norm_map (J : OrthogonalComplexStructure V) (v : V) : ‖J v‖ = ‖v‖ :=
  J.toLinearIsometryEquiv.norm_map v

@[simp]
theorem map_ne_zero (J : OrthogonalComplexStructure V) {v : V} (hv : v ≠ 0) : J v ≠ 0 := by
  simpa using J.toLinearIsometryEquiv.injective.ne hv

/-- Transport an orthogonal complex structure across a linear isometry. -/
def transport (e : V ≃ₗᵢ[ℝ] W) (J : OrthogonalComplexStructure W) :
    OrthogonalComplexStructure V where
  toLinearIsometryEquiv := e.trans (J.toLinearIsometryEquiv.trans e.symm)
  sq_apply v := by simp [J.sq_apply]

/-- Reversing every quarter-turn gives the other orientation. -/
def neg (J : OrthogonalComplexStructure V) : OrthogonalComplexStructure V where
  toLinearIsometryEquiv := J.toLinearIsometryEquiv.trans (LinearIsometryEquiv.neg ℝ)
  sq_apply v := by simp [J.sq_apply]

@[simp]
theorem neg_apply (J : OrthogonalComplexStructure V) (v : V) : J.neg v = -J v := rfl

/-- A quarter-turn is orthogonal to the original vector. -/
theorem inner_map_self_eq_zero (J : OrthogonalComplexStructure V) (v : V) :
    ⟪J v, v⟫_ℝ = 0 := by
  have hneg : ⟪J v, v⟫_ℝ = -⟪J v, v⟫_ℝ := by
    calc
      ⟪J v, v⟫_ℝ = ⟪J v, -J (J v)⟫_ℝ := by rw [J.sq_apply]; simp
      _ = -⟪J v, J (J v)⟫_ℝ := by simp
      _ = -⟪v, J v⟫_ℝ := by rw [J.toLinearIsometryEquiv.inner_map_map]
      _ = -⟪J v, v⟫_ℝ := by rw [real_inner_comm]
  linarith

@[simp]
theorem inner_self_map_eq_zero (J : OrthogonalComplexStructure V) (v : V) :
    ⟪v, J v⟫_ℝ = 0 := by
  rw [real_inner_comm, J.inner_map_self_eq_zero]

/-- The inverse quarter-turn is `-J`. -/
@[simp]
theorem symm_apply (J : OrthogonalComplexStructure V) (v : V) :
    J.toLinearIsometryEquiv.symm v = -J v := by
  apply J.toLinearIsometryEquiv.injective
  simp [J.sq_apply]

/-- Equivalently, `J` is skew-adjoint over the real inner product. -/
theorem inner_map_left_eq_neg (J : OrthogonalComplexStructure V) (x y : V) :
    ⟪J x, y⟫_ℝ = -⟪x, J y⟫_ℝ := by
  have h := J.toLinearIsometryEquiv.inner_map_map x (J y)
  rw [J.sq_apply, inner_neg_right] at h
  linarith

end OrthogonalComplexStructure

end

end VanAubelExtensions
