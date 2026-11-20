/-
Copyright (c) 2026 mindofcharles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mindofcharles
-/

import VanAubelExtensions.ExceptionalMetric
import VanAubelExtensions.ShearNorm

/-!
# Exact real norms of exceptional edge operators

The unitary adapted basis reduces the norm estimate to the sharp scalar
shear bound. An active block gives equality, and the zero parameter is
handled separately on a nonzero Hermitian space.
-/

namespace VanAubelExtensions

noncomputable section

open Module
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {N : AntilinearMap V}

namespace ExceptionalUnitaryNormalForm

variable (F : ExceptionalUnitaryNormalForm N)

def maxCoefficient : ℝ :=
  (Finset.univ.sup fun i => (⟨F.coefficient i, (F.positive i).le⟩ : NNReal) : NNReal)

theorem maxCoefficient_nonneg : 0 ≤ F.maxCoefficient := NNReal.coe_nonneg _

theorem coefficient_le_max (i : Fin F.r) : F.coefficient i ≤ F.maxCoefficient := by
  exact_mod_cast (Finset.le_sup (f := fun j =>
    (⟨F.coefficient j, (F.positive j).le⟩ : NNReal)) (Finset.mem_univ i))

theorem exists_maxCoefficient (hr : 0 < F.r) :
    ∃ i : Fin F.r, F.coefficient i = F.maxCoefficient := by
  have hne : (Finset.univ : Finset (Fin F.r)).Nonempty :=
    ⟨⟨0, hr⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ hne
    (fun j => (⟨F.coefficient j, (F.positive j).le⟩ : NNReal))
  exact ⟨i, congrArg (fun x : NNReal => (x : ℝ)) hi.symm⟩

theorem apply_eq_sum (x : V) :
    N x = ∑ i : Fin F.r, (star (F.basis.repr x (.inr i)) * (F.coefficient i : ℂ)) •
      F.basis (.inl (.inl i)) := by
  calc
    N x = N (∑ j, F.basis.repr x j • F.basis j) := congrArg N (F.basis.sum_repr x).symm
    _ = _ := by
      simp only [map_sum, map_add, Fintype.sum_sum_type, map_smulₛₗ, F.apply_u, F.apply_w,
        F.apply_v, smul_zero, Finset.sum_const_zero, zero_add, smul_smul, starRingEnd_apply]

theorem coordinate_apply_u (x : V) (i : Fin F.r) :
    F.basis.repr (N x) (.inl (.inl i)) =
      (F.coefficient i : ℂ) * star (F.basis.repr x (.inr i)) := by
  rw [OrthonormalBasis.repr_apply_apply, F.apply_eq_sum, inner_sum]
  simp [inner_smul_right, F.basis.inner_eq_ite, mul_comm]

theorem coordinate_apply_w (x : V) (i : Fin F.s) :
    F.basis.repr (N x) (.inl (.inr i)) = 0 := by
  rw [OrthonormalBasis.repr_apply_apply, F.apply_eq_sum, inner_sum]
  simp [inner_smul_right, F.basis.inner_eq_ite]

theorem coordinate_apply_v (x : V) (i : Fin F.r) :
    F.basis.repr (N x) (.inr i) = 0 := by
  rw [OrthonormalBasis.repr_apply_apply, F.apply_eq_sum, inner_sum]
  simp [inner_smul_right, F.basis.inner_eq_ite]

theorem norm_sq_coordinates (x : V) :
    ‖x‖ ^ 2 =
      (∑ i : Fin F.r, ‖F.basis.repr x (.inl (.inl i))‖ ^ 2) +
      (∑ i : Fin F.s, ‖F.basis.repr x (.inl (.inr i))‖ ^ 2) +
      (∑ i : Fin F.r, ‖F.basis.repr x (.inr i)‖ ^ 2) := by
  rw [← F.basis.repr.norm_map x, EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type,
    Fintype.sum_sum_type]

theorem norm_shear_sq (c : ℂ) (x : V) :
    ‖x + c • N x‖ ^ 2 =
      (∑ i : Fin F.r,
        (‖F.basis.repr x (.inl (.inl i)) + c * (F.coefficient i : ℂ) *
          star (F.basis.repr x (.inr i))‖ ^ 2 + ‖F.basis.repr x (.inr i)‖ ^ 2)) +
      (∑ i : Fin F.s, ‖F.basis.repr x (.inl (.inr i))‖ ^ 2) := by
  rw [F.norm_sq_coordinates]
  simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply,
    F.coordinate_apply_u, F.coordinate_apply_w, F.coordinate_apply_v, smul_eq_mul,
    mul_zero, add_zero, Finset.sum_add_distrib]
  simp only [mul_assoc]
  abel

theorem norm_shear_le (c : ℂ) (hc : ‖c‖ = 1) (x : V) :
    ‖x + c • N x‖ ≤ shearNorm F.maxCoefficient * ‖x‖ := by
  have hq := one_le_shearNorm F.maxCoefficient_nonneg
  have hq0 := shearNorm_pos F.maxCoefficient_nonneg
  have hsum :
      (∑ i : Fin F.r,
        (‖F.basis.repr x (.inl (.inl i)) + c * (F.coefficient i : ℂ) *
          star (F.basis.repr x (.inr i))‖ ^ 2 + ‖F.basis.repr x (.inr i)‖ ^ 2)) ≤
      shearNorm F.maxCoefficient ^ 2 *
        (∑ i : Fin F.r,
          (‖F.basis.repr x (.inl (.inl i))‖ ^ 2 + ‖F.basis.repr x (.inr i)‖ ^ 2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    refine (complex_shear_bound (F.positive i).le c _ _ hc).trans ?_
    have hm := shearNorm_mono (F.positive i).le (F.coefficient_le_max i)
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (shearNorm_pos (F.positive i).le).le hq0.le).mpr hm)
      (by positivity)
  have hw : (∑ i : Fin F.s, ‖F.basis.repr x (.inl (.inr i))‖ ^ 2) ≤
      shearNorm F.maxCoefficient ^ 2 *
        (∑ i : Fin F.s, ‖F.basis.repr x (.inl (.inr i))‖ ^ 2) := by
    have hq2 : 1 ≤ shearNorm F.maxCoefficient ^ 2 := by nlinarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hq2
      (show 0 ≤ ∑ i : Fin F.s, ‖F.basis.repr x (.inl (.inr i))‖ ^ 2 by positivity)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hq0.le (norm_nonneg x))).mp
  rw [mul_pow, F.norm_shear_sq, F.norm_sq_coordinates]
  simp only [Finset.sum_add_distrib] at hsum ⊢
  nlinarith

theorem norm_active_pair (i : Fin F.r) (a b : ℂ) :
    ‖a • F.basis (.inl (.inl i)) + b • F.basis (.inr i)‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  simp only [pow_two]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)]
  · simp [norm_smul]
  · simp [inner_smul_left, inner_smul_right, F.basis.inner_eq_ite]

end ExceptionalUnitaryNormalForm

variable [FiniteDimensional ℂ V]

/-- The real-linear shear associated with a phase and an antilinear parameter. -/
def AntilinearMap.shearContinuous (N : AntilinearMap V) (c : ℂ) : V →L[ℝ] V :=
  ((LinearMap.id : V →ₗ[ℝ] V) + (c • N).realMap).toContinuousLinearMap

@[simp] theorem AntilinearMap.shearContinuous_apply (N : AntilinearMap V) (c : ℂ) (x : V) :
    N.shearContinuous c x = x + c • N x := rfl

namespace ExceptionalUnitaryNormalForm

variable (F : ExceptionalUnitaryNormalForm N)

theorem shearNorm_le_opNorm (c : ℂ) (hc : ‖c‖ = 1) (i : Fin F.r) :
    shearNorm (F.coefficient i) ≤ ‖N.shearContinuous c‖ := by
  let q := shearNorm (F.coefficient i)
  have hq : 0 < q := shearNorm_pos (F.positive i).le
  have hrel : 1 + q * F.coefficient i = q ^ 2 := by
    have h := shearNorm_quadratic (F.coefficient i)
    dsimp [q]
    nlinarith
  have hrelC : (1 : ℂ) + (q : ℂ) * (F.coefficient i : ℂ) = (q : ℂ) ^ 2 := by
    exact_mod_cast hrel
  let x := c • F.basis (.inl (.inl i)) + (q : ℂ) • F.basis (.inr i)
  have hNx : N x = ((q : ℂ) * (F.coefficient i : ℂ)) • F.basis (.inl (.inl i)) := by
    simp only [x, map_add, map_smulₛₗ, F.apply_u, F.apply_v, smul_zero, zero_add, smul_smul]
    rw [show (starRingEnd ℂ) (q : ℂ) = (q : ℂ) from Complex.conj_ofReal q]
  have hSx : N.shearContinuous c x =
      (c * (q : ℂ) ^ 2) • F.basis (.inl (.inl i)) + (q : ℂ) • F.basis (.inr i) := by
    rw [AntilinearMap.shearContinuous_apply, hNx, ← hrelC]
    dsimp [x]
    module
  have hx : ‖x‖ ^ 2 = 1 + q ^ 2 := by
    rw [F.norm_active_pair]
    simp [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  have hS : ‖N.shearContinuous c x‖ ^ 2 = q ^ 2 * (1 + q ^ 2) := by
    rw [hSx, F.norm_active_pair, norm_mul, norm_pow, hc, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
    ring
  have hxpos : 0 < ‖x‖ := by
    have h := sq_pos_of_pos hq
    nlinarith [norm_nonneg x]
  have hratio : ‖N.shearContinuous c x‖ = q * ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hq.le (norm_nonneg x))).mp
    rw [hS, mul_pow, hx]
  apply (mul_le_mul_iff_of_pos_right hxpos).mp
  rw [← hratio]
  exact (N.shearContinuous c).le_opNorm x

/-- Exact real operator norm of every unit-phase exceptional shear. -/
theorem norm_shearContinuous [Nontrivial V] (c : ℂ) (hc : ‖c‖ = 1) :
    ‖N.shearContinuous c‖ = shearNorm F.maxCoefficient := by
  apply le_antisymm
  · exact (N.shearContinuous c).opNorm_le_bound
      (shearNorm_pos F.maxCoefficient_nonneg).le (F.norm_shear_le c hc)
  · by_cases hr : F.r = 0
    · have : IsEmpty (Fin F.r) := ⟨fun i => by have hi := i.isLt; omega⟩
      have hmax : F.maxCoefficient = 0 := by
        have hs : (Finset.univ.sup (fun i =>
            (⟨F.coefficient i, (F.positive i).le⟩ : NNReal))) ≤ (0 : NNReal) :=
          Finset.sup_le (fun i _ => isEmptyElim i)
        exact congrArg (fun t : NNReal => (t : ℝ)) (le_antisymm hs bot_le)
      have hN : N = 0 := by
        ext x
        simpa only [Finset.univ_eq_empty, Finset.sum_empty, LinearMap.zero_apply]
          using F.apply_eq_sum x
      have hS : N.shearContinuous c = ContinuousLinearMap.id ℝ V := by
        ext x
        simp [hN]
      rw [hmax, shearNorm_zero, hS]
      simp
    · obtain ⟨i, hi⟩ := F.exists_maxCoefficient (Nat.pos_of_ne_zero hr)
      rw [← hi]
      exact F.shearNorm_le_opNorm c hc i

end ExceptionalUnitaryNormalForm

/-- The standard target complex structure of a Hermitian space, as a real map. -/
def hermitianQuarterTurn : V →ₗ[ℝ] V :=
  (Complex.I • (LinearMap.id : V →ₗ[ℂ] V)).restrictScalars ℝ

def exceptionalEdgeReal (N : AntilinearMap V) : Fin 4 → V →ₗ[ℝ] V :=
  ![hermitianQuarterTurn - hermitianQuarterTurn.comp N.realMap,
    hermitianQuarterTurn + N.realMap,
    hermitianQuarterTurn + hermitianQuarterTurn.comp N.realMap,
    hermitianQuarterTurn - N.realMap]

def exceptionalEdgePhase : Fin 4 → ℂ := ![-1, -Complex.I, 1, Complex.I]

theorem exceptionalEdgePhase_norm (k : Fin 4) : ‖exceptionalEdgePhase k‖ = 1 := by
  fin_cases k <;> simp [exceptionalEdgePhase, Matrix.cons_val_two, Matrix.cons_val_three]

omit [FiniteDimensional ℂ V] in
theorem exceptionalEdgeReal_factor (N : AntilinearMap V) (k : Fin 4) (x : V) :
    exceptionalEdgeReal N k x = Complex.I • (x + exceptionalEdgePhase k • N x) := by
  fin_cases k
  · change Complex.I • x - Complex.I • N x = Complex.I • (x + (-1 : ℂ) • N x)
    simp [smul_add, sub_eq_add_neg]
  · change Complex.I • x + N x = Complex.I • (x + (-Complex.I) • N x)
    simp [smul_add, smul_smul]
  · change Complex.I • x + Complex.I • N x = Complex.I • (x + (1 : ℂ) • N x)
    simp [smul_add]
  · change Complex.I • x - N x = Complex.I • (x + Complex.I • N x)
    simp [smul_add, smul_smul, sub_eq_add_neg]

/-- The four exceptional edge operators have the same exact real operator norm. -/
theorem exceptionalEdgeReal_norm [Nontrivial V] (F : ExceptionalUnitaryNormalForm N)
    (k : Fin 4) :
    ‖(exceptionalEdgeReal N k).toContinuousLinearMap‖ = shearNorm F.maxCoefficient := by
  have hpoint (x : V) : ‖exceptionalEdgeReal N k x‖ =
      ‖N.shearContinuous (exceptionalEdgePhase k) x‖ := by
    rw [exceptionalEdgeReal_factor, norm_smul, Complex.norm_I, one_mul,
      AntilinearMap.shearContinuous_apply]
  have heq : ‖(exceptionalEdgeReal N k).toContinuousLinearMap‖ =
      ‖N.shearContinuous (exceptionalEdgePhase k)‖ := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro x
      change ‖exceptionalEdgeReal N k x‖ ≤
        ‖N.shearContinuous (exceptionalEdgePhase k)‖ * ‖x‖
      rw [hpoint]
      exact (N.shearContinuous (exceptionalEdgePhase k)).le_opNorm x
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro x
      rw [← hpoint]
      exact ((exceptionalEdgeReal N k).toContinuousLinearMap).le_opNorm x
  rw [heq, F.norm_shearContinuous _ (exceptionalEdgePhase_norm k)]

omit [FiniteDimensional ℂ V] in
theorem exceptionalEdgeReal_active_norm_sq (F : ExceptionalUnitaryNormalForm N)
    (k : Fin 4) (i : Fin F.r) :
    ‖exceptionalEdgeReal N k (F.basis (.inr i))‖ ^ 2 = 1 + F.coefficient i ^ 2 := by
  rw [exceptionalEdgeReal_factor, norm_smul, Complex.norm_I, one_mul, F.apply_v, smul_smul]
  rw [add_comm (F.basis (.inr i))]
  have h := F.norm_active_pair i (exceptionalEdgePhase k * (F.coefficient i : ℂ)) 1
  simp only [one_smul] at h
  rw [h, norm_mul, exceptionalEdgePhase_norm, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (F.positive i), norm_one, one_pow]
  ring

end

end VanAubelExtensions
