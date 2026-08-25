/-
Copyright (c) 2026 mindofcharles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mindofcharles
-/

import VanAubelExtensions.CenterIdentity

/-!
# Complex-affine naturality and coefficient transfer

Formal counterpart of the algebraic naturality and coefficient-transfer results
in `paper/van-aubel-complex-affine-naturality-and-transfer.md`.
-/

namespace VanAubelExtensions

noncomputable section

open scoped InnerProductSpace

section ComplexAffineTransfer

variable {V₁ : Type*} [AddCommGroup V₁] [Module ℝ V₁]

/-- The complex scalar action induced by a real-linear operator `J`.  When
`J² = -I`, this is the usual action `(a + bi)v = av + bJv`. -/
def complexScalarAction (J : V₁ →ₗ[ℝ] V₁) (z : ℂ) (v : V₁) : V₁ :=
  z.re • v + z.im • J v

@[simp]
theorem complexScalarAction_zero (J : V₁ →ₗ[ℝ] V₁) (v : V₁) :
    complexScalarAction J 0 v = 0 := by simp [complexScalarAction]

@[simp]
theorem complexScalarAction_one (J : V₁ →ₗ[ℝ] V₁) (v : V₁) :
    complexScalarAction J 1 v = v := by simp [complexScalarAction]

@[simp]
theorem complexScalarAction_zero_vector (J : V₁ →ₗ[ℝ] V₁) (z : ℂ) :
    complexScalarAction J z 0 = 0 := by simp [complexScalarAction]

@[simp]
theorem complexScalarAction_I (J : V₁ →ₗ[ℝ] V₁) (v : V₁) :
    complexScalarAction J Complex.I v = J v := by simp [complexScalarAction]

theorem complexScalarAction_add_scalar (J : V₁ →ₗ[ℝ] V₁)
    (z w : ℂ) (v : V₁) :
    complexScalarAction J (z + w) v =
      complexScalarAction J z v + complexScalarAction J w v := by
  simp only [complexScalarAction, Complex.add_re, Complex.add_im, add_smul]
  module

theorem complexScalarAction_sub_scalar (J : V₁ →ₗ[ℝ] V₁)
    (z w : ℂ) (v : V₁) :
    complexScalarAction J (z - w) v =
      complexScalarAction J z v - complexScalarAction J w v := by
  simp only [complexScalarAction, Complex.sub_re, Complex.sub_im, sub_smul]
  module

theorem complexScalarAction_add_vector (J : V₁ →ₗ[ℝ] V₁)
    (z : ℂ) (v w : V₁) :
    complexScalarAction J z (v + w) =
      complexScalarAction J z v + complexScalarAction J z w := by
  simp only [complexScalarAction, smul_add, map_add]
  module

theorem complexScalarAction_sum_scalar {I : Type*} [Fintype I]
    (J : V₁ →ₗ[ℝ] V₁) (z : I → ℂ) (v : V₁) :
    complexScalarAction J (∑ i, z i) v =
      ∑ i, complexScalarAction J (z i) v := by
  simp only [complexScalarAction, Complex.re_sum, Complex.im_sum,
    Finset.sum_add_distrib, Finset.sum_smul]

theorem complexScalarAction_sum_vector {I : Type*} [Fintype I]
    (J : V₁ →ₗ[ℝ] V₁) (z : ℂ) (v : I → V₁) :
    complexScalarAction J z (∑ i, v i) =
      ∑ i, complexScalarAction J z (v i) := by
  simp only [complexScalarAction, Finset.smul_sum, map_sum,
    Finset.sum_add_distrib]

theorem complexScalarAction_mul (J : V₁ →ₗ[ℝ] V₁)
    (hJ_sq : ∀ v, J (J v) = -v) (z w : ℂ) (v : V₁) :
    complexScalarAction J (z * w) v =
      complexScalarAction J z (complexScalarAction J w v) := by
  simp only [complexScalarAction, Complex.mul_re, Complex.mul_im, sub_smul, add_smul,
    map_add, map_smul]
  rw [hJ_sq v]
  module

/-- The coefficient `αε = (1 + εi)/2`. -/
def centerCoefficient (ε : ℝ) : ℂ :=
  ⟨(2 : ℝ)⁻¹, (2 : ℝ)⁻¹ * ε⟩

theorem centerCoefficient_eq (ε : ℝ) :
    centerCoefficient ε = ((1 : ℂ) + (ε : ℂ) * Complex.I) / 2 := by
  apply Complex.ext
  · simp [centerCoefficient]
  · simp [centerCoefficient]
    ring

/-- The center formula in the complex-affine two-coefficient normal form. -/
theorem squareCenter_eq_complexAffineCombination
    (J : V₁ →ₗ[ℝ] V₁) (ε : ℝ) (X Y : V₁) :
    squareCenter J ε X Y =
      complexScalarAction J (1 - centerCoefficient ε) X +
        complexScalarAction J (centerCoefficient ε) Y := by
  simp only [squareCenter, complexScalarAction, centerCoefficient, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im, map_sub]
  module

/-- In an affine space the same formula is `X + αε(Y-X)`, so no origin is
chosen. -/
theorem affineSquareCenter_eq_complexCoefficient
    {E₁ : Type*} [AddTorsor V₁ E₁] (J : V₁ →ₗ[ℝ] V₁)
    (ε : ℝ) (X Y : E₁) :
    affineSquareCenter J ε X Y =
      complexScalarAction J (centerCoefficient ε) (Y -ᵥ X) +ᵥ X := by
  simp only [affineSquareCenter, complexScalarAction, centerCoefficient]
  rw [vadd_right_cancel_iff]
  module

/-- Complex scalar expressions commute with an intertwining real-linear map. -/
theorem complexScalarAction_natural
    {W₁ : Type*} [AddCommGroup W₁] [Module ℝ W₁]
    (J : V₁ →ₗ[ℝ] V₁) (K : W₁ →ₗ[ℝ] W₁) (T : V₁ →ₗ[ℝ] W₁)
    (hTJ : ∀ v, T (J v) = K (T v)) (z : ℂ) (v : V₁) :
    T (complexScalarAction J z v) = complexScalarAction K z (T v) := by
  simp only [complexScalarAction, map_add, map_smul, hTJ]

/-- Naturality of square centers under arbitrary complex-affine maps.  No
injectivity, surjectivity, or metric hypothesis is used. -/
theorem affineSquareCenter_natural
    {W₁ E₁ F₁ : Type*} [AddCommGroup W₁] [Module ℝ W₁]
    [AddTorsor V₁ E₁] [AddTorsor W₁ F₁]
    (J : V₁ →ₗ[ℝ] V₁) (K : W₁ →ₗ[ℝ] W₁) (f : E₁ →ᵃ[ℝ] F₁)
    (hTJ : ∀ v, f.linear (J v) = K (f.linear v)) (ε : ℝ) (X Y : E₁) :
    f (affineSquareCenter J ε X Y) = affineSquareCenter K ε (f X) (f Y) := by
  simp only [affineSquareCenter, f.map_vadd]
  rw [vadd_right_cancel_iff]
  rw [map_smul, map_add, map_smul, hTJ, f.linearMap_vsub]

/-- The four vertices of the parallelogram determined by a directed edge and
a linear complex structure.  Orthogonality is not assumed. -/
@[ext]
structure AffineEdgeParallelogram (E : Type*) where
  first : E
  second : E
  third : E
  fourth : E

def AffineEdgeParallelogram.map {E F : Type*}
    (f : E → F) (s : AffineEdgeParallelogram E) : AffineEdgeParallelogram F :=
  ⟨f s.first, f s.second, f s.third, f s.fourth⟩

def affineEdgeParallelogram {E₁ : Type*} [AddTorsor V₁ E₁]
    (J : V₁ →ₗ[ℝ] V₁) (ε : ℝ) (X Y : E₁) :
    AffineEdgeParallelogram E₁ :=
  ⟨X, Y, ε • J (Y -ᵥ X) +ᵥ Y, ε • J (Y -ᵥ X) +ᵥ X⟩

def degenerateAffineEdgeParallelogram {E₁ : Type*} (X : E₁) :
    AffineEdgeParallelogram E₁ :=
  ⟨X, X, X, X⟩

/-- Complex-affine maps carry the entire edge parallelogram to the
corresponding target parallelogram, without any metric hypothesis. -/
theorem affineEdgeParallelogram_natural
    {W₁ E₁ F₁ : Type*} [AddCommGroup W₁] [Module ℝ W₁]
    [AddTorsor V₁ E₁] [AddTorsor W₁ F₁]
    (J : V₁ →ₗ[ℝ] V₁) (K : W₁ →ₗ[ℝ] W₁) (f : E₁ →ᵃ[ℝ] F₁)
    (hTJ : ∀ v, f.linear (J v) = K (f.linear v))
    (ε : ℝ) (X Y : E₁) :
    (affineEdgeParallelogram J ε X Y).map f =
      affineEdgeParallelogram K ε (f X) (f Y) := by
  ext <;> simp only [AffineEdgeParallelogram.map, affineEdgeParallelogram]
  all_goals rw [f.map_vadd, map_smul, hTJ, f.linearMap_vsub]

/-- If the edge direction is killed, its transported parallelogram collapses
to one point. -/
theorem affineEdgeParallelogram_natural_degenerate
    {W₁ E₁ F₁ : Type*} [AddCommGroup W₁] [Module ℝ W₁]
    [AddTorsor V₁ E₁] [AddTorsor W₁ F₁]
    (J : V₁ →ₗ[ℝ] V₁) (K : W₁ →ₗ[ℝ] W₁) (f : E₁ →ᵃ[ℝ] F₁)
    (hTJ : ∀ v, f.linear (J v) = K (f.linear v))
    (ε : ℝ) (X Y : E₁) (hzero : f.linear (Y -ᵥ X) = 0) :
    (affineEdgeParallelogram J ε X Y).map f =
      degenerateAffineEdgeParallelogram (f X) := by
  rw [affineEdgeParallelogram_natural J K f hTJ]
  have hXY : f Y = f X := by
    rw [← vsub_eq_zero_iff_eq, ← f.linearMap_vsub]
    exact hzero
  ext <;> simp [affineEdgeParallelogram,
    degenerateAffineEdgeParallelogram, hXY]

/-- Naturality simultaneously transports the two opposite-center vectors in
the Van Aubel identity. -/
theorem affineVanAubelCenterDifferences_natural
    {W₁ E₁ F₁ : Type*} [AddCommGroup W₁] [Module ℝ W₁]
    [AddTorsor V₁ E₁] [AddTorsor W₁ F₁]
    (J : V₁ →ₗ[ℝ] V₁) (K : W₁ →ₗ[ℝ] W₁) (f : E₁ →ᵃ[ℝ] F₁)
    (hTJ : ∀ v, f.linear (J v) = K (f.linear v)) (ε : ℝ) (A B C D : E₁) :
    f.linear (affineSquareCenter J ε C D -ᵥ affineSquareCenter J ε A B) =
        affineSquareCenter K ε (f C) (f D) -ᵥ affineSquareCenter K ε (f A) (f B) ∧
      f.linear (affineSquareCenter J ε D A -ᵥ affineSquareCenter J ε B C) =
        affineSquareCenter K ε (f D) (f A) -ᵥ affineSquareCenter K ε (f B) (f C) := by
  constructor
  · rw [f.linearMap_vsub, affineSquareCenter_natural J K f hTJ,
      affineSquareCenter_natural J K f hTJ]
  · rw [f.linearMap_vsub, affineSquareCenter_natural J K f hTJ,
      affineSquareCenter_natural J K f hTJ]

/-- Direct pointwise naturality of the full Van Aubel identity.  This theorem
does not assume that the affine map is injective or surjective. -/
theorem affineVanAubelIdentity_natural
    {W₁ E₁ F₁ : Type*} [AddCommGroup W₁] [Module ℝ W₁]
    [AddTorsor V₁ E₁] [AddTorsor W₁ F₁]
    (J : V₁ →ₗ[ℝ] V₁) (K : W₁ →ₗ[ℝ] W₁) (f : E₁ →ᵃ[ℝ] F₁)
    (hTJ : ∀ v, f.linear (J v) = K (f.linear v)) (ε : ℝ) (A B C D : E₁)
    (hsource :
      affineSquareCenter J ε C D -ᵥ affineSquareCenter J ε A B =
        ε • J (affineSquareCenter J ε D A -ᵥ affineSquareCenter J ε B C)) :
    affineSquareCenter K ε (f C) (f D) -ᵥ affineSquareCenter K ε (f A) (f B) =
      ε • K (affineSquareCenter K ε (f D) (f A) -ᵥ
        affineSquareCenter K ε (f B) (f C)) := by
  obtain ⟨hRP, hSQ⟩ :=
    affineVanAubelCenterDifferences_natural J K f hTJ ε A B C D
  calc
    affineSquareCenter K ε (f C) (f D) -ᵥ affineSquareCenter K ε (f A) (f B) =
        f.linear (affineSquareCenter J ε C D -ᵥ
          affineSquareCenter J ε A B) := hRP.symm
    _ = f.linear
        (ε • J (affineSquareCenter J ε D A -ᵥ affineSquareCenter J ε B C)) := by
          rw [hsource]
    _ = ε • K (f.linear
        (affineSquareCenter J ε D A -ᵥ affineSquareCenter J ε B C)) := by
          rw [map_smul, hTJ]
    _ = ε • K (affineSquareCenter K ε (f D) (f A) -ᵥ
        affineSquareCenter K ε (f B) (f C)) := by rw [hSQ]

/-- A finite complex-coefficient normal form for vector-valued expressions. -/
def complexLinearCombination {I : Type*} [Fintype I]
    (J : V₁ →ₗ[ℝ] V₁) (c : I → ℂ) (x : I → V₁) : V₁ :=
  ∑ i, complexScalarAction J (c i) (x i)

/-- Coefficients summing to one make the normal form translation-equivariant,
which is the vector-space content of being an affine combination. -/
theorem complexLinearCombination_translate {I : Type*} [Fintype I]
    (J : V₁ →ₗ[ℝ] V₁) (c : I → ℂ) (x : I → V₁) (t : V₁)
    (hc : ∑ i, c i = 1) :
    complexLinearCombination J c (fun i => x i + t) =
      complexLinearCombination J c x + t := by
  calc
    complexLinearCombination J c (fun i => x i + t) =
        ∑ i, (complexScalarAction J (c i) (x i) + complexScalarAction J (c i) t) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [complexScalarAction_add_vector]
    _ = complexLinearCombination J c x + ∑ i, complexScalarAction J (c i) t := by
      rw [Finset.sum_add_distrib]
      rfl
    _ = complexLinearCombination J c x + complexScalarAction J (∑ i, c i) t := by
      congr 1
      simp only [complexScalarAction, Complex.re_sum, Complex.im_sum, Finset.sum_add_distrib,
        Finset.sum_smul]
    _ = complexLinearCombination J c x + t := by rw [hc, complexScalarAction_one]

/-- The translation law without imposing a coefficient-sum condition. -/
theorem complexLinearCombination_translate_general {I : Type*} [Fintype I]
    (J : V₁ →ₗ[ℝ] V₁) (c : I → ℂ) (x : I → V₁) (t : V₁) :
    complexLinearCombination J c (fun i => x i + t) =
      complexLinearCombination J c x + complexScalarAction J (∑ i, c i) t := by
  calc
    complexLinearCombination J c (fun i => x i + t) =
        ∑ i, (complexScalarAction J (c i) (x i) +
          complexScalarAction J (c i) t) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [complexScalarAction_add_vector]
    _ = complexLinearCombination J c x +
        ∑ i, complexScalarAction J (c i) t := by
      rw [Finset.sum_add_distrib]
      rfl
    _ = complexLinearCombination J c x +
        complexScalarAction J (∑ i, c i) t := by
      rw [complexScalarAction_sum_scalar]

/-- Coefficient sum zero is the origin-independence condition for a
vector-valued difference of affine point terms. -/
theorem complexLinearCombination_translate_of_sum_eq_zero
    {I : Type*} [Fintype I]
    (J : V₁ →ₗ[ℝ] V₁) (c : I → ℂ) (x : I → V₁) (t : V₁)
    (hc : ∑ i, c i = 0) :
    complexLinearCombination J c (fun i => x i + t) =
      complexLinearCombination J c x := by
  rw [complexLinearCombination_translate_general, hc,
    complexScalarAction_zero, add_zero]

/-- Syntax of terms generated recursively from point variables by fixed
finite complex-affine combinations. -/
inductive ComplexAffineTerm (I : Type*) where
  | var (i : I) : ComplexAffineTerm I
  | combine (q : ℕ) (coeff : Fin q → ℂ)
      (coeff_sum : ∑ r, coeff r = 1)
      (term : Fin q → ComplexAffineTerm I) : ComplexAffineTerm I

namespace ComplexAffineTerm

/-- The coefficient vector obtained by flattening a recursive affine term. -/
def normalCoefficients {I : Type*} [Fintype I] [DecidableEq I] :
    ComplexAffineTerm I → I → ℂ
  | .var i => fun j => if j = i then 1 else 0
  | .combine q coeff _ term => fun j =>
      ∑ r : Fin q, coeff r * normalCoefficients (term r) j

/-- Recursive evaluation in vector coordinates. -/
def evalVector {I : Type*}
    (J : V₁ →ₗ[ℝ] V₁) : ComplexAffineTerm I → (I → V₁) → V₁
  | .var i, x => x i
  | .combine q coeff _ term, x =>
      ∑ r : Fin q, complexScalarAction J (coeff r) (evalVector J (term r) x)

/-- Every recursively generated affine term has coefficients summing to one. -/
theorem normalCoefficients_sum {I : Type*} [Fintype I] [DecidableEq I]
    (t : ComplexAffineTerm I) :
    ∑ i, normalCoefficients t i = 1 := by
  induction t with
  | var i => simp [normalCoefficients]
  | combine q coeff hcoeff term ih =>
      simp only [normalCoefficients]
      calc
        ∑ i, ∑ r : Fin q, coeff r * normalCoefficients (term r) i =
            ∑ r : Fin q, ∑ i, coeff r * normalCoefficients (term r) i :=
          Finset.sum_comm
        _ = ∑ r : Fin q, coeff r * (∑ i, normalCoefficients (term r) i) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.mul_sum]
        _ = ∑ r : Fin q, coeff r * 1 := by
          apply Finset.sum_congr rfl
          intro r _
          rw [ih r]
        _ = 1 := by simpa using hcoeff

/-- Structural normal-form theorem: recursive evaluation is exactly the
flattened complex coefficient combination. -/
theorem evalVector_eq_normalForm {I : Type*} [Fintype I] [DecidableEq I]
    (J : V₁ →ₗ[ℝ] V₁) (hJ_sq : ∀ v, J (J v) = -v)
    (t : ComplexAffineTerm I) (x : I → V₁) :
    evalVector J t x = complexLinearCombination J (normalCoefficients t) x := by
  induction t with
  | var i =>
      classical
      simp only [evalVector, complexLinearCombination, normalCoefficients]
      symm
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji]
      · simp
  | combine q coeff hcoeff term ih =>
      classical
      simp only [evalVector, ih, complexLinearCombination, normalCoefficients]
      calc
        ∑ r : Fin q,
            complexScalarAction J (coeff r)
              (∑ i, complexScalarAction J (normalCoefficients (term r) i) (x i)) =
            ∑ r : Fin q, ∑ i,
              complexScalarAction J (coeff r)
                (complexScalarAction J (normalCoefficients (term r) i) (x i)) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [complexScalarAction_sum_vector]
        _ = ∑ r : Fin q, ∑ i,
              complexScalarAction J
                (coeff r * normalCoefficients (term r) i) (x i) := by
          apply Finset.sum_congr rfl
          intro r _
          apply Finset.sum_congr rfl
          intro i _
          rw [complexScalarAction_mul J hJ_sq]
        _ = ∑ i, ∑ r : Fin q,
              complexScalarAction J
                (coeff r * normalCoefficients (term r) i) (x i) :=
          Finset.sum_comm
        _ = ∑ i, complexScalarAction J
              (∑ r : Fin q, coeff r * normalCoefficients (term r) i) (x i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [complexScalarAction_sum_scalar]

/-- Intrinsic affine evaluation of a recursive term, expressed relative to a
temporary origin.  The next theorem proves that this origin is immaterial. -/
def evalAffine {I E₁ : Type*} [Fintype I] [DecidableEq I]
    [AddTorsor V₁ E₁] (J : V₁ →ₗ[ℝ] V₁)
    (t : ComplexAffineTerm I) (x : I → E₁) (O : E₁) : E₁ :=
  complexLinearCombination J (normalCoefficients t) (fun i => x i -ᵥ O) +ᵥ O

/-- The affine evaluation does not depend on the temporary origin. -/
theorem evalAffine_origin_independent {I E₁ : Type*}
    [Fintype I] [DecidableEq I] [AddTorsor V₁ E₁]
    (J : V₁ →ₗ[ℝ] V₁) (t : ComplexAffineTerm I) (x : I → E₁) (O O' : E₁) :
    evalAffine J t x O = evalAffine J t x O' := by
  rw [evalAffine, evalAffine]
  have hcoords : (fun i => x i -ᵥ O') =
      fun i => (x i -ᵥ O) + (O -ᵥ O') := by
    funext i
    exact (vsub_add_vsub_cancel (x i) O O').symm
  rw [hcoords, complexLinearCombination_translate J _ _ _
    (normalCoefficients_sum t)]
  rw [← vadd_vadd, vsub_vadd]

/-- Equal normal coefficient vectors give equal evaluations in every complex
affine space. -/
theorem evalAffine_eq_of_normalCoefficients_eq
    {I E₁ : Type*} [Fintype I] [DecidableEq I] [AddTorsor V₁ E₁]
    (J : V₁ →ₗ[ℝ] V₁) {t s : ComplexAffineTerm I}
    (hcoeff : normalCoefficients t = normalCoefficients s)
    (x : I → E₁) (O : E₁) :
    evalAffine J t x O = evalAffine J s x O := by
  simp only [evalAffine, hcoeff]

/-- Intrinsic affine evaluation agrees with recursive evaluation in the
coordinates based at any chosen origin. -/
theorem evalAffine_eq_evalVector_vadd
    {I E₁ : Type*} [Fintype I] [DecidableEq I] [AddTorsor V₁ E₁]
    (J : V₁ →ₗ[ℝ] V₁) (hJ_sq : ∀ v, J (J v) = -v)
    (t : ComplexAffineTerm I) (x : I → E₁) (O : E₁) :
    evalAffine J t x O = evalVector J t (fun i => x i -ᵥ O) +ᵥ O := by
  rw [evalAffine, evalVector_eq_normalForm J hJ_sq]

end ComplexAffineTerm

/-- On a nonzero complex-structure space, a complex coefficient is determined
by its action on one nonzero vector. -/
theorem complexScalarAction_eq_zero_iff [Nontrivial V₁]
    (J : V₁ →ₗ[ℝ] V₁) (hJ_sq : ∀ v, J (J v) = -v)
    {z : ℂ} {v : V₁} (hv : v ≠ 0) :
    complexScalarAction J z v = 0 ↔ z = 0 := by
  constructor
  · intro hzero
    have hJzero : z.re • J v - z.im • v = 0 := by
      have h' := congrArg J hzero
      simp only [complexScalarAction, map_add, map_smul, map_zero] at h'
      rw [hJ_sq v] at h'
      simpa only [smul_neg, sub_eq_add_neg] using h'
    have hsq : (z.re ^ 2 + z.im ^ 2) • v = 0 := by
      have hzero' : z.re • v + z.im • J v = 0 := by
        simpa only [complexScalarAction] using hzero
      calc
        (z.re ^ 2 + z.im ^ 2) • v =
            z.re • (z.re • v + z.im • J v) -
              z.im • (z.re • J v - z.im • v) := by module
        _ = z.re • 0 - z.im • 0 := by
          rw [hzero', hJzero]
        _ = 0 := by module
    have hcoeff : z.re ^ 2 + z.im ^ 2 = 0 :=
      (smul_eq_zero.mp hsq).resolve_right hv
    have hre : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    have him : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    apply Complex.ext <;> simp [hre, him]
  · rintro rfl
    exact complexScalarAction_zero J v

/-- Universal equality of finite normal forms forces equality of their
coefficient vectors. -/
theorem complexLinearCombination_coefficients_unique
    {I : Type*} [Fintype I] [Nontrivial V₁]
    (J : V₁ →ₗ[ℝ] V₁) (hJ_sq : ∀ v, J (J v) = -v)
    (c d : I → ℂ)
    (h : ∀ x : I → V₁, complexLinearCombination J c x = complexLinearCombination J d x) :
    c = d := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : V₁)
  funext i
  let x : I → V₁ := fun j => if j = i then v else 0
  have hcollapse (a : I → ℂ) :
      complexLinearCombination J a x = complexScalarAction J (a i) v := by
    simp only [complexLinearCombination]
    calc
      ∑ j, complexScalarAction J (a j) (x j) =
          ∑ j, if j = i then complexScalarAction J (a i) v else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hji : j = i
        · subst j
          simp [x]
        · simp [x, hji]
      _ = complexScalarAction J (a i) v := by simp
  have hi := h x
  have haction : complexScalarAction J (c i) v = complexScalarAction J (d i) v := by
    rw [hcollapse c, hcollapse d] at hi
    exact hi
  have hzero : complexScalarAction J (c i - d i) v = 0 := by
    rw [complexScalarAction_sub_scalar, haction]
    module
  exact sub_eq_zero.mp ((complexScalarAction_eq_zero_iff J hJ_sq hv).mp hzero)

/-- Multiplication by `i` on the complex affine line, viewed as a real-linear
complex structure. -/
def complexLineJ : ℂ →ₗ[ℝ] ℂ where
  toFun z := Complex.I * z
  map_add' x y := by simp [mul_add]
  map_smul' r z := by
    simp
    ring

theorem complexLineJ_sq : ∀ z, complexLineJ (complexLineJ z) = -z := by
  intro z
  change Complex.I * (Complex.I * z) = -z
  rw [← mul_assoc, Complex.I_mul_I]
  simp

/-- Precise dimension-free transfer: if two coefficient normal forms agree
universally on the complex line, they agree in every nonzero real vector space
carrying a complex structure. -/
theorem complexCoefficientIdentity_transfer
    {I : Type*} [Fintype I] [Nontrivial V₁]
    (J : V₁ →ₗ[ℝ] V₁) (_hJ_sq : ∀ v, J (J v) = -v)
    (c d : I → ℂ)
    (hline : ∀ x : I → ℂ,
      complexLinearCombination complexLineJ c x = complexLinearCombination complexLineJ d x) :
    ∀ x : I → V₁, complexLinearCombination J c x = complexLinearCombination J d x := by
  have hcoeff := complexLinearCombination_coefficients_unique complexLineJ complexLineJ_sq c d hline
  rw [hcoeff]
  intro x
  rfl

namespace ComplexAffineTerm

/-- Two recursive terms agree universally on the complex affine line exactly
when their normal coefficient vectors agree. -/
theorem evalVector_complexLine_iff_normalCoefficients_eq
    {I : Type*} [Fintype I] [DecidableEq I]
    (t s : ComplexAffineTerm I) :
    (∀ x : I → ℂ, evalVector complexLineJ t x = evalVector complexLineJ s x) ↔
      normalCoefficients t = normalCoefficients s := by
  constructor
  · intro h
    apply complexLinearCombination_coefficients_unique
      complexLineJ complexLineJ_sq
    intro x
    rw [← evalVector_eq_normalForm complexLineJ complexLineJ_sq t x,
      ← evalVector_eq_normalForm complexLineJ complexLineJ_sq s x]
    exact h x
  · intro h x
    rw [evalVector_eq_normalForm complexLineJ complexLineJ_sq,
      evalVector_eq_normalForm complexLineJ complexLineJ_sq, h]

/-- Point-valued version of the preceding uniqueness theorem, viewing `ℂ`
as its own affine line and using zero only as a temporary origin. -/
theorem evalAffine_complexLine_iff_normalCoefficients_eq
    {I : Type*} [Fintype I] [DecidableEq I]
    (t s : ComplexAffineTerm I) :
    (∀ x : I → ℂ,
      evalAffine complexLineJ t x 0 = evalAffine complexLineJ s x 0) ↔
      normalCoefficients t = normalCoefficients s := by
  constructor
  · intro h
    apply complexLinearCombination_coefficients_unique
      complexLineJ complexLineJ_sq
    intro x
    have hx := h x
    simpa [evalAffine] using hx
  · intro h x
    exact evalAffine_eq_of_normalCoefficients_eq complexLineJ h x 0

/-- Universal recursive affine-term transfer from the complex line to every
real vector space carrying a complex structure. -/
theorem evalVector_transfer_from_complexLine
    {I : Type*} [Finite I]
    (t s : ComplexAffineTerm I)
    (hline : ∀ x : I → ℂ,
      evalVector complexLineJ t x = evalVector complexLineJ s x)
    (J : V₁ →ₗ[ℝ] V₁) (hJ_sq : ∀ v, J (J v) = -v)
    (x : I → V₁) :
    evalVector J t x = evalVector J s x := by
  classical
  let _ := Fintype.ofFinite I
  have hcoeff :=
    (evalVector_complexLine_iff_normalCoefficients_eq t s).mp hline
  rw [evalVector_eq_normalForm J hJ_sq,
    evalVector_eq_normalForm J hJ_sq, hcoeff]

/-- Point-valued affine version of universal transfer.  No map between the
source and target affine spaces is involved. -/
theorem evalAffine_transfer_from_complexLine
    {I E₁ : Type*} [Fintype I] [DecidableEq I] [AddTorsor V₁ E₁]
    (t s : ComplexAffineTerm I)
    (hline : ∀ x : I → ℂ,
      evalVector complexLineJ t x = evalVector complexLineJ s x)
    (J : V₁ →ₗ[ℝ] V₁) (x : I → E₁) (O : E₁) :
    evalAffine J t x O = evalAffine J s x O := by
  exact evalAffine_eq_of_normalCoefficients_eq J
    ((evalVector_complexLine_iff_normalCoefficients_eq t s).mp hline) x O

/-- Universal point-valued transfer stated exactly with the complex affine
line as the test space. -/
theorem evalAffine_transfer_from_affineComplexLine
    {I E₁ : Type*} [Fintype I] [DecidableEq I] [AddTorsor V₁ E₁]
    (t s : ComplexAffineTerm I)
    (hline : ∀ x : I → ℂ,
      evalAffine complexLineJ t x 0 = evalAffine complexLineJ s x 0)
    (J : V₁ →ₗ[ℝ] V₁) (x : I → E₁) (O : E₁) :
    evalAffine J t x O = evalAffine J s x O := by
  exact evalAffine_eq_of_normalCoefficients_eq J
    ((evalAffine_complexLine_iff_normalCoefficients_eq t s).mp hline) x O

end ComplexAffineTerm

/-- The coefficient vector of the left side `R - P` of the Van Aubel
identity, ordered by the variables `(A,B,C,D)`. -/
def vanAubelLeftCoefficients (ε : ℝ) : Fin 4 → ℂ :=
  ![-(1 - centerCoefficient ε), -centerCoefficient ε,
    1 - centerCoefficient ε, centerCoefficient ε]

/-- The coefficient vector of `ε i (S - Q)`, in the same variable order. -/
def vanAubelRightCoefficients (ε : ℝ) : Fin 4 → ℂ :=
  ![(ε : ℂ) * Complex.I * centerCoefficient ε,
    -((ε : ℂ) * Complex.I * (1 - centerCoefficient ε)),
    -((ε : ℂ) * Complex.I * centerCoefficient ε),
    (ε : ℂ) * Complex.I * (1 - centerCoefficient ε)]

/-- The Van Aubel relation is literally equality of two fixed complex
coefficient vectors. -/
theorem vanAubel_coefficients_eq (ε : ℝ) (hε_sq : ε ^ 2 = 1) :
    vanAubelLeftCoefficients ε = vanAubelRightCoefficients ε := by
  rcases sq_eq_one_iff.mp hε_sq with rfl | rfl
  all_goals
    funext i
    fin_cases i <;>
      apply Complex.ext <;>
      norm_num [vanAubelLeftCoefficients, vanAubelRightCoefficients,
        centerCoefficient]

/-- For a nonzero vector, `u` and `Ju` are real-linearly independent for
every complex structure; no metric or orthogonality hypothesis is needed. -/
theorem self_and_complexStructure_image_linearIndependent
    (J : V₁ →ₗ[ℝ] V₁) (hJ_sq : ∀ v, J (J v) = -v)
    {u : V₁} (hu : u ≠ 0) :
    LinearIndependent ℝ ![u, J u] := by
  have hJinj : Function.Injective J := by
    intro x y hxy
    have hxy' := congrArg J hxy
    rw [hJ_sq x, hJ_sq y] at hxy'
    exact neg_injective hxy'
  have hJu : J u ≠ 0 := by
    intro hzero
    apply hu
    apply hJinj
    simpa using hzero
  rw [linearIndependent_fin2]
  refine ⟨hJu, ?_⟩
  intro a ha
  have ha' : a • J u = u := by simpa using ha
  have hJa := congrArg J ha'
  simp only [map_smul] at hJa
  rw [hJ_sq u] at hJa
  have hau : a • u = -J u := by
    calc
      a • u = -(a • (-u)) := by module
      _ = -J u := by rw [hJa]
  have hzero : (a ^ 2 + 1) • u = 0 := by
    calc
      (a ^ 2 + 1) • u = a • (a • u) + u := by module
      _ = a • (-J u) + u := by rw [hau]
      _ = -(a • J u) + u := by module
      _ = -u + u := by rw [ha']
      _ = 0 := by module
  have hcoeff : a ^ 2 + 1 ≠ 0 := by nlinarith [sq_nonneg a]
  exact hu ((smul_eq_zero.mp hzero).resolve_left hcoeff)

end ComplexAffineTransfer

end

end VanAubelExtensions
