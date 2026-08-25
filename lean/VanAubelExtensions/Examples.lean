/-
Copyright (c) 2026 mindofcharles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mindofcharles
-/

import VanAubelExtensions.Dimension
import VanAubelExtensions.Rigidity
import VanAubelExtensions.SquareGeometry

/-!
# Higher-dimensional examples and exceptional families

Formal examples supporting
`paper/van-aubel-complex-structure-identity.md` and
`paper/van-aubel-edge-operator-realizations-and-rigidity.md`.
-/

namespace VanAubelExtensions

noncomputable section

open scoped InnerProductSpace

section HigherDimensionalPhenomena

/- An abstract affine inner-product space carries no left/right or “outside”
predicate for an edge.  Accordingly, `squareOnEdge` takes `J` as explicit
additional data; `J` selects the plane spanned by `u` and `J u`. -/

/-- In every positive block dimension, the standard complex structure and its
negative are distinct.  Thus the Euclidean metric alone does not select a
quarter-turn in dimensions greater than two (or even in dimension two without
an orientation). -/
theorem standardEvenComplexStructure_ne_neg (n : ℕ) (hn : 0 < n) :
    standardEvenComplexStructure n ≠ (standardEvenComplexStructure n).neg := by
  intro h
  let i : Fin n := ⟨0, hn⟩
  let x : EuclideanSpace ℝ (Fin n × Fin 2) := EuclideanSpace.single (i, 0) 1
  have hx := congrArg
    (fun J : OrthogonalComplexStructure (EuclideanSpace ℝ (Fin n × Fin 2)) => J x (i, 1)) h
  norm_num [OrthogonalComplexStructure.neg, standardEvenComplexStructure, x] at hx

/-- First affine line in a concrete four-dimensional Euclidean example. -/
def skewLineOne (t : ℝ) : EuclideanSpace ℝ (Fin 4) := !₂[t, 0, 0, 0]

/-- Second affine line in the same example.  Its third coordinate is fixed at
one, so it cannot meet `skewLineOne`. -/
def skewLineTwo (s : ℝ) : EuclideanSpace ℝ (Fin 4) := !₂[0, s, 1, 0]

def skewDirectionOne : EuclideanSpace ℝ (Fin 4) := !₂[1, 0, 0, 0]

def skewDirectionTwo : EuclideanSpace ℝ (Fin 4) := !₂[0, 1, 0, 0]

theorem skewLineOne_direction (t : ℝ) :
    skewLineOne (t + 1) - skewLineOne t = skewDirectionOne := by
  ext i
  fin_cases i <;> simp [skewLineOne, skewDirectionOne]

theorem skewLineTwo_direction (s : ℝ) :
    skewLineTwo (s + 1) - skewLineTwo s = skewDirectionTwo := by
  ext i
  fin_cases i <;> simp [skewLineTwo, skewDirectionTwo]

/-- The two direction vectors in the example are orthogonal. -/
theorem skewDirections_inner_eq_zero :
    ⟪skewDirectionOne, skewDirectionTwo⟫_ℝ = 0 := by
  simp [skewDirectionOne, skewDirectionTwo, PiLp.inner_apply, Fin.sum_univ_succ]

/-- Nevertheless, the two affine lines are disjoint. -/
theorem skewLines_disjoint : ¬ ∃ t s : ℝ, skewLineOne t = skewLineTwo s := by
  rintro ⟨t, s, h⟩
  have hcoord := congrArg (fun x : EuclideanSpace ℝ (Fin 4) => x 2) h
  change (0 : ℝ) = 1 at hcoord
  norm_num at hcoord

end HigherDimensionalPhenomena

section MetricTransportCounterexamples

/-- The nonorthogonal complex structure
`Jₐ(x,y)=(-a y,a⁻¹x)` on the Euclidean plane. -/
def anisotropicPlaneJ (a : ℝ) :
    EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun x := !₂[-a * x 1, a⁻¹ * x 0]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [mul_add]
  map_smul' r x := by
    ext i
    fin_cases i <;> simp [mul_left_comm]

theorem anisotropicPlaneJ_sq (a : ℝ) (ha : a ≠ 0) :
    IsLinearComplexStructure (anisotropicPlaneJ a) := by
  intro x
  ext i
  fin_cases i <;> simp [anisotropicPlaneJ, ha]

def planeDiagonal : EuclideanSpace ℝ (Fin 2) := !₂[1, 1]

def planeFirstBasis : EuclideanSpace ℝ (Fin 2) := !₂[1, 0]

/-- The explicit inner-product defect of `Jₐ`. -/
theorem anisotropicPlaneJ_diagonal_inner (a : ℝ) :
    ⟪planeDiagonal, anisotropicPlaneJ a planeDiagonal⟫_ℝ = -a + a⁻¹ := by
  simp [planeDiagonal, anisotropicPlaneJ, PiLp.inner_apply,
    Fin.sum_univ_succ]

theorem anisotropicPlaneJ_two_not_orthogonal :
    ⟪planeDiagonal, anisotropicPlaneJ 2 planeDiagonal⟫_ℝ ≠ 0 := by
  rw [anisotropicPlaneJ_diagonal_inner]
  norm_num

/-- `J₂` also fails to preserve the length of the first basis vector. -/
theorem anisotropicPlaneJ_two_not_norm_preserving :
    ‖anisotropicPlaneJ 2 planeFirstBasis‖ ≠ ‖planeFirstBasis‖ := by
  intro hnorm
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at hnorm
  norm_num [planeFirstBasis, anisotropicPlaneJ, Fin.sum_univ_succ] at hnorm

/-- The standard quarter-turn is orthogonal, stated directly as preservation
of every real inner product. -/
theorem standardPlaneJ_inner_map_map (x y : EuclideanSpace ℝ (Fin 2)) :
    ⟪anisotropicPlaneJ 1 x, anisotropicPlaneJ 1 y⟫_ℝ = ⟪x, y⟫_ℝ := by
  simp [anisotropicPlaneJ, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

/-- Stretch the first real coordinate. -/
def stretchPlaneFirst (a : ℝ) :
    EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun x := !₂[a * x 0, x 1]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [mul_add]
  map_smul' r x := by
    ext i
    fin_cases i <;> simp [mul_left_comm]

/-- Conjugating the standard orthogonal quarter-turn by a coordinate stretch
produces the nonorthogonal target structure `Jₐ`. -/
theorem stretchPlaneFirst_intertwines (a : ℝ) (ha : a ≠ 0)
    (x : EuclideanSpace ℝ (Fin 2)) :
    stretchPlaneFirst a (anisotropicPlaneJ 1 x) =
      anisotropicPlaneJ a (stretchPlaneFirst a x) := by
  ext i
  fin_cases i <;> simp [stretchPlaneFirst, anisotropicPlaneJ, ha]

/-- A single packaged counterexample: the source structure preserves every
inner product, the intertwining relation holds, but the target structure is
not orthogonal. -/
theorem source_orthogonal_target_nonorthogonal :
    (∀ x y : EuclideanSpace ℝ (Fin 2),
      ⟪anisotropicPlaneJ 1 x, anisotropicPlaneJ 1 y⟫_ℝ = ⟪x, y⟫_ℝ) ∧
    (∀ x : EuclideanSpace ℝ (Fin 2),
      stretchPlaneFirst 2 (anisotropicPlaneJ 1 x) =
        anisotropicPlaneJ 2 (stretchPlaneFirst 2 x)) ∧
    ⟪planeDiagonal, anisotropicPlaneJ 2 planeDiagonal⟫_ℝ ≠ 0 :=
  ⟨standardPlaneJ_inner_map_map,
    stretchPlaneFirst_intertwines 2 (by norm_num),
    anisotropicPlaneJ_two_not_orthogonal⟩

/-- Real scaling on the complex line. -/
def complexLineScaling (r : ℝ) : ℂ →ₗ[ℝ] ℂ :=
  r • LinearMap.id

/-- Scaling commutes with multiplication by `i`, so it is complex-linear. -/
theorem complexLineScaling_intertwines (r : ℝ) (z : ℂ) :
    complexLineScaling r (complexLineJ z) =
      complexLineJ (complexLineScaling r z) := by
  simp [complexLineScaling, complexLineJ]
  ring

/-- The complex-linear map `z ↦ 2z` doubles every norm exactly. -/
@[simp]
theorem complexLineScaling_two_norm (z : ℂ) :
    ‖complexLineScaling 2 z‖ = 2 * ‖z‖ := by
  norm_num [complexLineScaling, norm_smul]

/-- The complex-linear map `z ↦ 2z` doubles a nonzero length and therefore
is not an isometry, despite transporting the algebraic construction. -/
theorem complexLineScaling_two_not_norm_preserving :
    ¬ ∀ z : ℂ, ‖complexLineScaling 2 z‖ = ‖z‖ := by
  intro h
  have hunit := h 1
  rw [complexLineScaling_two_norm] at hunit
  norm_num at hunit

end MetricTransportCounterexamples

section ExceptionalNonorthogonalFamily

/-- The exceptional example lives in real dimension four. -/
theorem exceptional_space_finrank : Module.finrank ℝ (ℂ × ℂ) = 4 := by
  rw [Module.finrank_prod, Complex.finrank_real_complex]

/-- The standard complex structure on `ℂ × ℂ`, viewed as a real vector
space. -/
def exceptionalK : (ℂ × ℂ) →ₗ[ℝ] (ℂ × ℂ) where
  toFun z := (Complex.I * z.1, Complex.I * z.2)
  map_add' x y := by
    ext <;> simp [mul_add]
  map_smul' r z := by
    ext <;> simp [mul_comm, mul_left_comm]

/-- A nonzero square-zero, complex-antilinear perturbation on `ℂ × ℂ`. -/
def exceptionalN : (ℂ × ℂ) →ₗ[ℝ] (ℂ × ℂ) where
  toFun z := (star z.2, 0)
  map_add' x y := by
    ext <;> simp
  map_smul' r z := by
    ext <;> simp

@[simp]
theorem exceptionalK_apply (z : ℂ × ℂ) :
    exceptionalK z = (Complex.I * z.1, Complex.I * z.2) := rfl

@[simp]
theorem exceptionalN_apply (z : ℂ × ℂ) :
    exceptionalN z = (star z.2, 0) := rfl

theorem exceptionalK_sq : IsLinearComplexStructure exceptionalK := by
  intro z
  ext <;> simp only [exceptionalK_apply, Prod.fst_neg, Prod.snd_neg]
  all_goals rw [← mul_assoc, Complex.I_mul_I]
  all_goals simp

theorem exceptionalN_sq (z : ℂ × ℂ) : exceptionalN (exceptionalN z) = 0 := by
  simp [exceptionalN]

theorem exceptional_anticommutes (z : ℂ × ℂ) :
    exceptionalK (exceptionalN z) + exceptionalN (exceptionalK z) = 0 := by
  ext <;> simp [exceptionalK, exceptionalN]

theorem exceptionalN_ne_zero : exceptionalN ≠ 0 := by
  intro h
  have hz := LinearMap.congr_fun h (0, 1)
  norm_num [exceptionalN] at hz

/-- The second independent perturbation `KN`. -/
def exceptionalKN : (ℂ × ℂ) →ₗ[ℝ] (ℂ × ℂ) :=
  exceptionalK.comp exceptionalN

@[simp]
theorem exceptionalKN_apply (z : ℂ × ℂ) :
    exceptionalKN z = (Complex.I * star z.2, 0) := by
  simp [exceptionalKN, exceptionalK, exceptionalN]

/-- Real linear combinations of `N` and `KN`. -/
def exceptionalPerturbation (a b : ℝ) : (ℂ × ℂ) →ₗ[ℝ] (ℂ × ℂ) :=
  a • exceptionalN + b • exceptionalKN

/-- The two perturbations `N` and `KN` are real-linearly independent, in the
strong coordinate form needed below. -/
theorem exceptionalPerturbation_pair_injective :
    Function.Injective
      (fun p : ℝ × ℝ => exceptionalPerturbation p.1 p.2) := by
  intro p q hpq
  have hv := LinearMap.congr_fun hpq ((0 : ℂ), (1 : ℂ))
  have hc := congrArg Prod.fst hv
  have hc' : (p.1 : ℂ) + (p.2 : ℂ) * Complex.I =
      (q.1 : ℂ) + (q.2 : ℂ) * Complex.I := by
    simpa [exceptionalPerturbation, exceptionalKN, exceptionalK,
      exceptionalN, LinearMap.comp_apply] using hc
  have hre := congrArg Complex.re hc'
  have him := congrArg Complex.im hc'
  norm_num at hre him
  exact Prod.ext hre him

/-- In particular, `N` and `KN` are linearly independent as vectors in the
real vector space of endomorphisms. -/
theorem exceptionalN_KN_linearIndependent :
    LinearIndependent ℝ ![exceptionalN, exceptionalKN] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hp : exceptionalPerturbation (c 0) (c 1) =
      exceptionalPerturbation 0 0 := by
    simpa [exceptionalPerturbation, Fin.sum_univ_two] using hc
  have hpair : (c 0, c 1) = ((0 : ℝ), (0 : ℝ)) := by
    apply exceptionalPerturbation_pair_injective
    exact hp
  fin_cases i
  · exact congrArg Prod.fst hpair
  · exact congrArg Prod.snd hpair

/-- The four edge operators of the concrete exceptional realization. -/
def exceptionalEdgeOperator : Fin 4 → (ℂ × ℂ) →ₗ[ℝ] (ℂ × ℂ) :=
  ![exceptionalK - exceptionalKN, exceptionalK + exceptionalN,
    exceptionalK + exceptionalKN, exceptionalK - exceptionalN]

/-- Their coefficient pairs relative to the independent directions
`(N,KN)`. -/
def exceptionalEdgeCoefficient : Fin 4 → ℝ × ℝ :=
  ![(0, -1), (1, 0), (0, 1), (-1, 0)]

theorem exceptionalEdgeCoefficient_injective :
    Function.Injective exceptionalEdgeCoefficient := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [exceptionalEdgeCoefficient] <;>
    norm_num at hij

theorem exceptionalEdgeOperator_eq_base_add_perturbation (i : Fin 4) :
    exceptionalEdgeOperator i = exceptionalK +
      exceptionalPerturbation (exceptionalEdgeCoefficient i).1
        (exceptionalEdgeCoefficient i).2 := by
  fin_cases i <;>
    simp [exceptionalEdgeOperator, exceptionalEdgeCoefficient,
      exceptionalPerturbation, exceptionalKN] <;>
    module

/-- All four edge complex structures in the explicit `ℂ²` family are
pairwise distinct. -/
theorem exceptionalEdgeOperator_injective :
    Function.Injective exceptionalEdgeOperator := by
  intro i j hij
  apply exceptionalEdgeCoefficient_injective
  apply exceptionalPerturbation_pair_injective
  apply add_left_cancel (a := exceptionalK)
  rw [← exceptionalEdgeOperator_eq_base_add_perturbation i,
    ← exceptionalEdgeOperator_eq_base_add_perturbation j]
  exact hij

/-- The exceptional second edge operator is not norm-preserving for the
standard product norm, so this family is genuinely nonorthogonal. -/
theorem exceptional_second_not_norm_preserving :
    ¬ ∀ z : ℂ × ℂ, ‖(exceptionalK + exceptionalN) z‖ = ‖z‖ := by
  intro h
  have hz := h (-Complex.I, 1)
  norm_num [exceptionalK, exceptionalN] at hz

/-- Squared standard Hermitian norm on `ℂ²`.  This is recorded explicitly
because the generic product norm instance on `ℂ × ℂ` is the max norm. -/
def complexPairHermitianNormSq (z : ℂ × ℂ) : ℝ :=
  Complex.normSq z.1 + Complex.normSq z.2

/-- The paper's exact metric computation:
`(K+N)(0,1)=(1,i)`, with squared Hermitian norms `2` and `1`. -/
theorem exceptional_second_hermitianNormSq_example :
    complexPairHermitianNormSq ((exceptionalK + exceptionalN) (0, 1)) = 2 ∧
      complexPairHermitianNormSq (0, 1) = 1 := by
  norm_num [complexPairHermitianNormSq, exceptionalK, exceptionalN,
    Complex.normSq_apply]

theorem exceptional_second_not_hermitianNormSq_preserving :
    ¬ ∀ z : ℂ × ℂ,
      complexPairHermitianNormSq ((exceptionalK + exceptionalN) z) =
        complexPairHermitianNormSq z := by
  intro h
  have hz := h (0, 1)
  norm_num [complexPairHermitianNormSq, exceptionalK, exceptionalN,
    Complex.normSq_apply] at hz

/-- A concrete four-real-dimensional exceptional family: all four edge maps
are complex structures and satisfy the universal identity, although the
second edge map differs from the target map. -/
theorem exists_nontrivial_exceptional_operator_family :
    ∃ L₁ L₂ L₃ L₄ : (ℂ × ℂ) →ₗ[ℝ] (ℂ × ℂ),
      UniversalOperatorIdentity exceptionalK L₁ L₂ L₃ L₄ ∧
      IsLinearComplexStructure L₁ ∧ IsLinearComplexStructure L₂ ∧
      IsLinearComplexStructure L₃ ∧ IsLinearComplexStructure L₄ ∧
      L₂ ≠ exceptionalK := by
  refine ⟨exceptionalK - exceptionalK.comp exceptionalN,
    exceptionalK + exceptionalN, exceptionalK + exceptionalK.comp exceptionalN,
    exceptionalK - exceptionalN, ?_, ?_⟩
  · exact universalOperatorIdentity_of_parametrization exceptionalK exceptionalN exceptionalK_sq
  · have hall := (parametrized_all_complexStructures_iff exceptionalK exceptionalN
        exceptionalK_sq).mpr ⟨exceptionalN_sq, exceptional_anticommutes⟩
    refine ⟨hall.1, hall.2.1, hall.2.2.1, hall.2.2.2, ?_⟩
    intro h
    apply exceptionalN_ne_zero
    have hz : exceptionalK + exceptionalN = exceptionalK + 0 := by
      simpa using h
    exact add_left_cancel hz

/-- A model of complex dimension `n + 2`: the explicit exceptional `ℂ²`
block together with `n` unused complex coordinates. -/
abbrev HigherExceptionalSpace (n : ℕ) :=
  (ℂ × ℂ) × (Fin n → ℂ)

theorem higherExceptionalSpace_finrank (n : ℕ) :
    Module.finrank ℝ (HigherExceptionalSpace n) = 2 * (n + 2) := by
  rw [Module.finrank_prod, exceptional_space_finrank,
    Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex]
  omega

/-- Standard multiplication by `i` on every coordinate of the higher
exceptional space. -/
def higherExceptionalK (n : ℕ) :
    HigherExceptionalSpace n →ₗ[ℝ] HigherExceptionalSpace n where
  toFun z := (exceptionalK z.1, fun i => Complex.I * z.2 i)
  map_add' x y := by
    ext <;> simp [mul_add]
  map_smul' r z := by
    ext <;> simp [mul_comm, mul_left_comm]

/-- Extend the square-zero perturbation by zero on all extra coordinates. -/
def higherExceptionalN (n : ℕ) :
    HigherExceptionalSpace n →ₗ[ℝ] HigherExceptionalSpace n where
  toFun z := (exceptionalN z.1, 0)
  map_add' x y := by
    ext <;> simp
  map_smul' r z := by
    ext <;> simp

@[simp]
theorem higherExceptionalK_apply (n : ℕ) (z : HigherExceptionalSpace n) :
    higherExceptionalK n z =
      (exceptionalK z.1, fun i => Complex.I * z.2 i) := rfl

@[simp]
theorem higherExceptionalN_apply (n : ℕ) (z : HigherExceptionalSpace n) :
    higherExceptionalN n z = (exceptionalN z.1, 0) := rfl

theorem higherExceptionalK_sq (n : ℕ) :
    IsLinearComplexStructure (higherExceptionalK n) := by
  intro z
  apply Prod.ext
  · change exceptionalK (exceptionalK z.1) = -z.1
    exact exceptionalK_sq z.1
  · funext i
    change Complex.I * (Complex.I * z.2 i) = -z.2 i
    rw [← mul_assoc, Complex.I_mul_I]
    simp

theorem higherExceptionalN_sq (n : ℕ) (z : HigherExceptionalSpace n) :
    higherExceptionalN n (higherExceptionalN n z) = 0 := by
  ext <;> simp

theorem higherExceptional_anticommutes (n : ℕ) (z : HigherExceptionalSpace n) :
    higherExceptionalK n (higherExceptionalN n z) +
      higherExceptionalN n (higherExceptionalK n z) = 0 := by
  ext <;> simp

def higherExceptionalKN (n : ℕ) :
    HigherExceptionalSpace n →ₗ[ℝ] HigherExceptionalSpace n :=
  (higherExceptionalK n).comp (higherExceptionalN n)

def higherExceptionalPerturbation (n : ℕ) (a b : ℝ) :
    HigherExceptionalSpace n →ₗ[ℝ] HigherExceptionalSpace n :=
  a • higherExceptionalN n + b • higherExceptionalKN n

/-- Squared standard Hermitian norm on the coordinate model
`ℂ² × ℂⁿ`. -/
def higherHermitianNormSq (n : ℕ) (z : HigherExceptionalSpace n) : ℝ :=
  complexPairHermitianNormSq z.1 + ∑ i, Complex.normSq (z.2 i)

theorem higherExceptionalPerturbation_pair_injective (n : ℕ) :
    Function.Injective
      (fun p : ℝ × ℝ => higherExceptionalPerturbation n p.1 p.2) := by
  intro p q hpq
  have hv := LinearMap.congr_fun hpq
    ((((0 : ℂ), (1 : ℂ))), (0 : Fin n → ℂ))
  have hfirst := congrArg Prod.fst hv
  have hc : (p.1 : ℂ) + (p.2 : ℂ) * Complex.I =
      (q.1 : ℂ) + (q.2 : ℂ) * Complex.I := by
    simpa [higherExceptionalPerturbation, higherExceptionalKN,
      exceptionalKN] using congrArg Prod.fst hfirst
  have hre := congrArg Complex.re hc
  have him := congrArg Complex.im hc
  norm_num at hre him
  exact Prod.ext hre him

/-- The four pairwise-distinct edge complex structures in every complex
dimension `n + 2`. -/
def higherExceptionalEdgeOperator (n : ℕ) :
    Fin 4 → HigherExceptionalSpace n →ₗ[ℝ] HigherExceptionalSpace n :=
  ![higherExceptionalK n - higherExceptionalKN n,
    higherExceptionalK n + higherExceptionalN n,
    higherExceptionalK n + higherExceptionalKN n,
    higherExceptionalK n - higherExceptionalN n]

theorem higherExceptionalEdgeOperator_eq_base_add_perturbation
    (n : ℕ) (i : Fin 4) :
    higherExceptionalEdgeOperator n i = higherExceptionalK n +
      higherExceptionalPerturbation n (exceptionalEdgeCoefficient i).1
        (exceptionalEdgeCoefficient i).2 := by
  fin_cases i <;>
    simp [higherExceptionalEdgeOperator, exceptionalEdgeCoefficient,
      higherExceptionalPerturbation, higherExceptionalKN] <;>
    module

theorem higherExceptionalEdgeOperator_injective (n : ℕ) :
    Function.Injective (higherExceptionalEdgeOperator n) := by
  intro i j hij
  apply exceptionalEdgeCoefficient_injective
  apply higherExceptionalPerturbation_pair_injective n
  apply add_left_cancel (a := higherExceptionalK n)
  rw [← higherExceptionalEdgeOperator_eq_base_add_perturbation n i,
    ← higherExceptionalEdgeOperator_eq_base_add_perturbation n j]
  exact hij

theorem higherExceptionalEdgeOperator_all_complexStructures
    (n : ℕ) (i : Fin 4) :
    IsLinearComplexStructure (higherExceptionalEdgeOperator n i) := by
  have hall := (parametrized_all_complexStructures_iff
    (higherExceptionalK n) (higherExceptionalN n)
    (higherExceptionalK_sq n)).mpr
      ⟨higherExceptionalN_sq n, higherExceptional_anticommutes n⟩
  fin_cases i
  · exact hall.1
  · exact hall.2.1
  · exact hall.2.2.1
  · exact hall.2.2.2

theorem higherExceptionalEdgeOperator_universalIdentity (n : ℕ) :
    UniversalOperatorIdentity (higherExceptionalK n)
      (higherExceptionalEdgeOperator n 0)
      (higherExceptionalEdgeOperator n 1)
      (higherExceptionalEdgeOperator n 2)
      (higherExceptionalEdgeOperator n 3) := by
  simpa [higherExceptionalEdgeOperator, higherExceptionalKN] using
    (universalOperatorIdentity_of_parametrization
      (higherExceptionalK n) (higherExceptionalN n)
      (higherExceptionalK_sq n))

/-- The second edge operator remains non-isometric after adjoining any number
of unused complex coordinates. -/
theorem higherExceptional_second_not_norm_preserving (n : ℕ) :
    ¬ ∀ z : HigherExceptionalSpace n,
      ‖higherExceptionalEdgeOperator n 1 z‖ = ‖z‖ := by
  intro h
  have hz := h (((-Complex.I, 1) : ℂ × ℂ), (0 : Fin n → ℂ))
  norm_num [higherExceptionalEdgeOperator, higherExceptionalK,
    higherExceptionalN] at hz
  change max 2 ‖(0 : Fin n → ℂ)‖ = 1 at hz
  rw [norm_zero] at hz
  norm_num at hz

theorem higherExceptional_second_not_hermitianNormSq_preserving (n : ℕ) :
    ¬ ∀ z : HigherExceptionalSpace n,
      higherHermitianNormSq n (higherExceptionalEdgeOperator n 1 z) =
        higherHermitianNormSq n z := by
  intro h
  have hz := h ((((0 : ℂ), (1 : ℂ))), (0 : Fin n → ℂ))
  norm_num [higherHermitianNormSq, complexPairHermitianNormSq,
    higherExceptionalEdgeOperator, higherExceptionalK, higherExceptionalN,
    Complex.normSq_apply] at hz

/-- Nonorthogonal non-rigidity occurs in every finite complex dimension at
least two (parameterized here as `n + 2`), and the four edge maps can be
chosen pairwise distinct. -/
theorem exceptional_family_in_every_complex_dimension_ge_two (n : ℕ) :
    Function.Injective (higherExceptionalEdgeOperator n) ∧
      (∀ i, IsLinearComplexStructure (higherExceptionalEdgeOperator n i)) ∧
      UniversalOperatorIdentity (higherExceptionalK n)
        (higherExceptionalEdgeOperator n 0)
        (higherExceptionalEdgeOperator n 1)
        (higherExceptionalEdgeOperator n 2)
        (higherExceptionalEdgeOperator n 3) ∧
      ¬ ∀ z : HigherExceptionalSpace n,
        higherHermitianNormSq n (higherExceptionalEdgeOperator n 1 z) =
          higherHermitianNormSq n z :=
  ⟨higherExceptionalEdgeOperator_injective n,
    higherExceptionalEdgeOperator_all_complexStructures n,
    higherExceptionalEdgeOperator_universalIdentity n,
    higherExceptional_second_not_hermitianNormSq_preserving n⟩

end ExceptionalNonorthogonalFamily

end

end VanAubelExtensions
