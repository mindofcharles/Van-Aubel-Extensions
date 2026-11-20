/-
Copyright (c) 2026 mindofcharles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mindofcharles
-/

import VanAubelExtensions.Rigidity
import VanAubelExtensions.ComplexAffineTransfer

/-!
# The complex module induced by a real complex structure

A type wrapper keeps the induced scalar action local to the chosen operator.
The underlying real vector space and the existing real-linear theorem interfaces
are preserved by the coordinate identification.
-/

namespace VanAubelExtensions

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private theorem action_real_smul (J : V →ₗ[ℝ] V) (r : ℝ) (z : ℂ) (v : V) :
    complexScalarAction J (r • z) v = r • complexScalarAction J z v := by
  simp only [complexScalarAction, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im, smul_add, smul_smul, add_zero]

private theorem action_comm_real (J : V →ₗ[ℝ] V) (r : ℝ) (z : ℂ) (v : V) :
    r • complexScalarAction J z v = complexScalarAction J z (r • v) := by
  simp only [complexScalarAction, map_smul, smul_add, smul_smul]
  module

private theorem action_anticommuting (J N : V →ₗ[ℝ] V)
    (hN : ∀ v, J (N v) + N (J v) = 0) (z : ℂ) (v : V) :
    N (complexScalarAction J z v) = complexScalarAction J (star z) (N v) := by
  have hanti : N (J v) = -J (N v) :=
    eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using hN v)
  simp only [complexScalarAction, map_add, map_smul, Complex.star_def,
    Complex.conj_re, Complex.conj_im, hanti]
  module

/-- A copy of the real space carrying the complex action induced by `J`. -/
def ComplexStructureSpace (J : V →ₗ[ℝ] V) (_hJ : IsLinearComplexStructure J) := V

namespace ComplexStructureSpace

variable (J : V →ₗ[ℝ] V) (hJ : IsLinearComplexStructure J)

instance : AddCommGroup (ComplexStructureSpace J hJ) := inferInstanceAs (AddCommGroup V)

instance : Module ℝ (ComplexStructureSpace J hJ) := inferInstanceAs (Module ℝ V)

instance : Module ℂ (ComplexStructureSpace J hJ) where
  smul z v := complexScalarAction J z v
  one_smul := complexScalarAction_one J
  mul_smul := complexScalarAction_mul J hJ
  smul_zero := complexScalarAction_zero_vector J
  smul_add := complexScalarAction_add_vector J
  add_smul := complexScalarAction_add_scalar J
  zero_smul := complexScalarAction_zero J

instance : IsScalarTower ℝ ℂ (ComplexStructureSpace J hJ) where
  smul_assoc := action_real_smul J

instance : SMulCommClass ℝ ℂ (ComplexStructureSpace J hJ) where
  smul_comm := action_comm_real J

instance [FiniteDimensional ℝ V] : FiniteDimensional ℝ (ComplexStructureSpace J hJ) :=
  inferInstanceAs (FiniteDimensional ℝ V)

instance [FiniteDimensional ℝ V] : FiniteDimensional ℂ (ComplexStructureSpace J hJ) :=
  Module.Finite.of_restrictScalars_finite ℝ ℂ (ComplexStructureSpace J hJ)

/-- Multiplication by `i` is precisely the prescribed real operator. -/
@[simp] theorem I_smul (v : ComplexStructureSpace J hJ) : Complex.I • v = J v := by
  exact complexScalarAction_I J v

/-- Anticommutation is exactly semilinearity for complex conjugation. -/
def antilinearMap (N : V →ₗ[ℝ] V) (hN : ∀ v, J (N v) + N (J v) = 0) :
    ComplexStructureSpace J hJ →ₛₗ[starRingEnd ℂ] ComplexStructureSpace J hJ where
  toFun := N
  map_add' := N.map_add
  map_smul' := action_anticommuting J N hN

@[simp] theorem antilinearMap_apply (N : V →ₗ[ℝ] V)
    (hN : ∀ v, J (N v) + N (J v) = 0) (v : ComplexStructureSpace J hJ) :
    antilinearMap J hJ N hN v = N v := rfl

end ComplexStructureSpace

end

end VanAubelExtensions
