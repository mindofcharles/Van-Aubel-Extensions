/-
Copyright (c) 2026 mindofcharles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mindofcharles
-/

import VanAubelExtensions.Basic

/-!
# Even-dimensional realizations

Part of the formalization of `paper/van-aubel-complex-structure-identity.md`.
-/

namespace VanAubelExtensions

noncomputable section

open scoped InnerProductSpace

section Dimension

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A finite-dimensional real vector space carrying a linear complex
structure has even dimension.  Orthogonality is not needed for this direction. -/
theorem finrank_even_of_complexStructure (J : V →ₗ[ℝ] V)
    (hJ_sq : ∀ v, J (J v) = -v) : Even (Module.finrank ℝ V) := by
  have hcomp : J.comp J = -(LinearMap.id : V →ₗ[ℝ] V) := by
    ext v
    simp [hJ_sq]
  have hdet : (LinearMap.det J) ^ 2 = (-1 : ℝ) ^ Module.finrank ℝ V := by
    calc
      (LinearMap.det J) ^ 2 = LinearMap.det (J.comp J) := by
        rw [LinearMap.det_comp]
        ring
      _ = LinearMap.det (-(LinearMap.id : V →ₗ[ℝ] V)) := by rw [hcomp]
      _ = (-1 : ℝ) ^ Module.finrank ℝ V := by
        simpa only [neg_one_smul, LinearMap.det_id, mul_one] using
          (LinearMap.det_smul (M := V) (-1 : ℝ) (LinearMap.id : V →ₗ[ℝ] V))
  by_contra hnot
  have hodd : Odd (Module.finrank ℝ V) := Nat.not_even_iff_odd.mp hnot
  rw [hodd.neg_one_pow] at hdet
  nlinarith [sq_nonneg (LinearMap.det J)]

/-- Swap the two coordinates inside each of `n` two-dimensional blocks. -/
def evenIndexFlip (n : ℕ) : (Fin n × Fin 2) ≃ (Fin n × Fin 2) :=
  Equiv.prodCongr (Equiv.refl (Fin n)) (Equiv.swap 0 1)

/-- Negate the first coordinate in each two-dimensional block. -/
def evenCoordinateSign {n : ℕ} (i : Fin n × Fin 2) : ℝ ≃ₗᵢ[ℝ] ℝ :=
  if i.2 = 0 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ

/-- The standard blockwise quarter-turn on `ℝ^(2n)`, indexed as `n` pairs. -/
def standardEvenJEquiv (n : ℕ) :
    EuclideanSpace ℝ (Fin n × Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n × Fin 2) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (evenIndexFlip n)).trans
    (LinearIsometryEquiv.piLpCongrRight 2 fun i => evenCoordinateSign i)

@[simp]
theorem standardEvenJEquiv_apply_zero (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) (i : Fin n) :
    standardEvenJEquiv n x (i, 0) = -x (i, 1) := by
  simp [standardEvenJEquiv, evenIndexFlip, evenCoordinateSign]

@[simp]
theorem standardEvenJEquiv_apply_one (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) (i : Fin n) :
    standardEvenJEquiv n x (i, 1) = x (i, 0) := by
  simp [standardEvenJEquiv, evenIndexFlip, evenCoordinateSign]

/-- The standard blockwise quarter-turn is an orthogonal complex structure. -/
def standardEvenComplexStructure (n : ℕ) :
    OrthogonalComplexStructure (EuclideanSpace ℝ (Fin n × Fin 2)) where
  toLinearIsometryEquiv := standardEvenJEquiv n
  sq_apply x := by
    ext ⟨i, j⟩
    fin_cases j <;> simp

end Dimension

section EvenDimensionalExistence

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Every even-dimensional real inner-product space admits an orthogonal
complex structure. -/
theorem exists_orthogonalComplexStructure_of_even
    (hEven : Even (Module.finrank ℝ V)) : Nonempty (OrthogonalComplexStructure V) := by
  rcases hEven with ⟨n, hn⟩
  have hcard : Fintype.card (Fin (Module.finrank ℝ V)) =
      Fintype.card (Fin n × Fin 2) := by
    simp [hn, Nat.mul_two]
  let indexEquiv : Fin (Module.finrank ℝ V) ≃ Fin n × Fin 2 :=
    Fintype.equivOfCardEq hcard
  let basis : OrthonormalBasis (Fin n × Fin 2) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex indexEquiv
  exact ⟨OrthogonalComplexStructure.transport basis.repr (standardEvenComplexStructure n)⟩

/-- In finite dimensions, admitting an orthogonal complex structure is
equivalent to having even real dimension. -/
theorem nonempty_orthogonalComplexStructure_iff_even :
    Nonempty (OrthogonalComplexStructure V) ↔ Even (Module.finrank ℝ V) := by
  constructor
  · rintro ⟨J⟩
    exact finrank_even_of_complexStructure J.toLinearMap J.sq_apply
  · exact exists_orthogonalComplexStructure_of_even

end EvenDimensionalExistence

end

end VanAubelExtensions
