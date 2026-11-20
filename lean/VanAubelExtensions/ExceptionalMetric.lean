/-
Copyright (c) 2026 mindofcharles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mindofcharles
-/

import VanAubelExtensions.ExceptionalNormalForms
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Hermitian normal forms and metric distortion of exceptional operators
-/

namespace VanAubelExtensions

noncomputable section

open Module
open scoped InnerProductSpace

section ConjugateSpace

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private theorem conjugate_mul_smul (a b : ℂ) (v : V) :
    star (a * b) • v = star a • star b • v := by
  simp only [star_mul, smul_smul, mul_comm]

private theorem conjugate_one_smul (v : V) : star (1 : ℂ) • v = v := by simp
private theorem conjugate_smul_zero (c : ℂ) : star c • (0 : V) = 0 := smul_zero _
private theorem conjugate_smul_add (c : ℂ) (v w : V) :
    star c • (v + w) = star c • v + star c • w := smul_add _ _ _
private theorem conjugate_add_smul (c d : ℂ) (v : V) :
    star (c + d) • v = star c • v + star d • v := by rw [star_add, add_smul]
private theorem conjugate_zero_smul (v : V) : star (0 : ℂ) • v = 0 := by simp

private def conjugateSmul (c : ℂ) (v : V) : V := star c • v

/-- The conjugate complex vector space. -/
def ConjugateSpace (V : Type*) := V

def conjugate (v : V) : ConjugateSpace V := v

def unconjugate (v : ConjugateSpace V) : V := v

instance : AddCommGroup (ConjugateSpace V) := inferInstanceAs (AddCommGroup V)

instance : Module ℂ (ConjugateSpace V) where
  smul := conjugateSmul (V := V)
  one_smul := conjugate_one_smul (V := V)
  mul_smul := conjugate_mul_smul (V := V)
  smul_zero := conjugate_smul_zero (V := V)
  smul_add := conjugate_smul_add (V := V)
  add_smul := conjugate_add_smul (V := V)
  zero_smul := conjugate_zero_smul (V := V)

instance [FiniteDimensional ℂ V] : FiniteDimensional ℂ (ConjugateSpace V) := by
  let C := basisConjugation (Module.finBasis ℂ V)
  let f : V →ₗ[ℂ] ConjugateSpace V :=
    { toFun := C
      map_add' := C.map_add
      map_smul' c v := C.map_smulₛₗ c v }
  exact Module.Finite.of_surjective f C.surjective

theorem finrank_conjugateSpace [FiniteDimensional ℂ V] :
    finrank ℂ (ConjugateSpace V) = finrank ℂ V := by
  let C := basisConjugation (Module.finBasis ℂ V)
  let f : V →ₗ[ℂ] ConjugateSpace V :=
    { toFun := C
      map_add' := C.map_add
      map_smul' c v := C.map_smulₛₗ c v }
  exact (LinearEquiv.ofBijective f C.bijective).finrank_eq.symm

end ConjugateSpace

section ConjugateMetric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

private theorem conjugate_norm_smul (c : ℂ) (v : V) :
    ‖star c • v‖ ≤ ‖c‖ * ‖v‖ := by rw [norm_smul, norm_star]

instance : NormedAddCommGroup (ConjugateSpace V) := inferInstanceAs (NormedAddCommGroup V)

instance : NormedSpace ℂ (ConjugateSpace V) where
  norm_smul_le := conjugate_norm_smul (V := V)

private def conjugateInner (x y : V) : ℂ := star ⟪x, y⟫_ℂ

private theorem conjugate_inner_norm_sq (x : V) : ‖x‖ ^ 2 = (conjugateInner x x).re := by
  simp only [conjugateInner, Complex.star_def, Complex.conj_re]
  exact norm_sq_eq_re_inner (𝕜 := ℂ) x

private theorem conjugate_inner_symm (x y : V) :
    star (conjugateInner y x) = conjugateInner x y := by
  simp only [conjugateInner, star_star]
  exact (inner_conj_symm y x).symm

private theorem conjugate_inner_add (x y z : V) :
    conjugateInner (x + y) z = conjugateInner x z + conjugateInner y z := by
  simp only [conjugateInner, inner_add_left, star_add]

private theorem conjugate_inner_smul (x y : V) (c : ℂ) :
    conjugateInner (star c • x) y = star c * conjugateInner x y := by
  simp only [conjugateInner, inner_smul_left, starRingEnd_apply, star_star, star_mul, mul_comm]

instance : InnerProductSpace ℂ (ConjugateSpace V) where
  inner := conjugateInner (V := V)
  norm_sq_eq_re_inner := conjugate_inner_norm_sq (V := V)
  conj_inner_symm := conjugate_inner_symm (V := V)
  add_left := conjugate_inner_add (V := V)
  smul_left := conjugate_inner_smul (V := V)

theorem conjugateSpace_inner (x y : ConjugateSpace V) :
    @inner ℂ (ConjugateSpace V) _ x y = star (@inner ℂ V _ x y) := rfl

/-- An orthonormal basis of the conjugate space is also an orthonormal basis
of the underlying original space, with the same vectors. -/
def unconjugateOrthonormalBasis [FiniteDimensional ℂ V] {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (ConjugateSpace V)) : OrthonormalBasis (Fin n) ℂ V := by
  classical
  let v : Fin n → V := fun i => b i
  have hon : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    have h := congrArg star (b.inner_eq_ite i j)
    rw [conjugateSpace_inner, star_star] at h
    by_cases hij : i = j
    · simpa only [if_pos hij, star_one] using h
    · simpa only [if_neg hij, star_zero] using h
  have hd : Fintype.card (Fin n) = finrank ℂ V := by
    rw [← finrank_conjugateSpace (V := V)]
    exact (finrank_eq_card_basis b.toBasis).symm
  exact OrthonormalBasis.mk hon (hon.linearIndependent.span_eq_top_of_card_eq_finrank' hd).ge

@[simp] theorem unconjugateOrthonormalBasis_apply [FiniteDimensional ℂ V] {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (ConjugateSpace V)) (i : Fin n) :
    unconjugateOrthonormalBasis b i = (b i : V) := by
  unfold unconjugateOrthonormalBasis
  exact congrFun (OrthonormalBasis.coe_mk _ _) i

private theorem conjugate_antilin_smul (N : AntilinearMap V) (c : ℂ) (v : V) :
    N (star c • v) = c • N v := by
  rw [N.map_smulₛₗ]
  exact congrArg (fun z : ℂ => z • N v) (star_star c)

/-- An antilinear map is linear on the conjugate domain. -/
def AntilinearMap.linearized (N : AntilinearMap V) : ConjugateSpace V →ₗ[ℂ] V where
  toFun := N
  map_add' := N.map_add
  map_smul' := conjugate_antilin_smul N

@[simp] theorem AntilinearMap.linearized_apply (N : AntilinearMap V) (v : ConjugateSpace V) :
    N.linearized v = N v := rfl

end ConjugateMetric

section SingularBases

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

/-- A bijective map has singular bases with strictly positive coefficients. -/
theorem linearMap_exists_singularBases (B : E →ₗ[ℂ] F) (hB : Function.Bijective B) :
    ∃ σ : Fin (finrank ℂ E) → ℝ,
      ∃ v : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E,
      ∃ u : OrthonormalBasis (Fin (finrank ℂ E)) ℂ F,
        (∀ i, 0 < σ i) ∧ ∀ i, B (v i) = (σ i : ℂ) • u i := by
  classical
  let hT := B.isSymmetric_adjoint_comp_self
  let v := hT.eigenvectorBasis rfl
  let eigenvalue := hT.eigenvalues rfl
  have hinner (i j : Fin (finrank ℂ E)) :
      ⟪B (v i), B (v j)⟫_ℂ = (eigenvalue j : ℂ) * (if i = j then 1 else 0) := by
    rw [← B.adjoint_inner_right, show B.adjoint (B (v j)) = (eigenvalue j : ℂ) • v j from
      hT.apply_eigenvectorBasis rfl j, inner_smul_right, v.inner_eq_ite]
  have heigenPos (i : Fin (finrank ℂ E)) : 0 < eigenvalue i := by
    have heq : ‖B (v i)‖ ^ 2 = eigenvalue i := by
      have h := congrArg Complex.re (hinner i i)
      simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using h
    have hne : B (v i) ≠ 0 := by
      intro h
      have hz : v i = 0 := hB.injective (by simpa only [map_zero] using h)
      have hn := v.norm_eq_one i
      rw [hz, norm_zero] at hn
      norm_num at hn
    rw [← heq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hne)
  let σ := fun i => Real.sqrt (eigenvalue i)
  have hσ (i) : 0 < σ i := Real.sqrt_pos.mpr (heigenPos i)
  have hσsq (i) : σ i ^ 2 = eigenvalue i := Real.sq_sqrt (heigenPos i).le
  let u := fun i => ((σ i : ℂ)⁻¹) • B (v i)
  have hon : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [u, inner_smul_left, inner_smul_right, hinner]
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl, mul_one, ← hσsq]
      have hne : (σ i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hσ i).ne'
      have hstar : (starRingEnd ℂ) ((σ i : ℂ)⁻¹) = (σ i : ℂ)⁻¹ := by
        rw [map_inv₀]
        exact congrArg Inv.inv (Complex.conj_ofReal (σ i))
      rw [hstar]
      push_cast
      field_simp
    · simp [hij]
  have hd : Fintype.card (Fin (finrank ℂ E)) = finrank ℂ F := by
    simpa only [Fintype.card_fin] using (LinearEquiv.ofBijective B hB).finrank_eq
  let ub := OrthonormalBasis.mk hon
    (hon.linearIndependent.span_eq_top_of_card_eq_finrank' hd).ge
  refine ⟨σ, v, ub, hσ, ?_⟩
  intro i
  simp only [ub, OrthonormalBasis.coe_mk]
  change B (v i) = (σ i : ℂ) • (((σ i : ℂ)⁻¹) • B (v i))
  rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (hσ i).ne'), one_smul]

end SingularBases

section UnitaryNormalForms

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

private theorem decomposition_left (P : Submodule ℂ V) (p : P) :
    P.orthogonalDecomposition.symm (WithLp.toLp 2 (p, 0)) = (p : V) := by
  exact (Submodule.orthogonalDecomposition_symm_apply P _).trans (by simp)

private theorem decomposition_right (P : Submodule ℂ V) (p : Pᗮ) :
    P.orthogonalDecomposition.symm (WithLp.toLp 2 (0, p)) = (p : V) := by
  exact (Submodule.orthogonalDecomposition_symm_apply P _).trans (by simp)

/-- An orthonormal adapted basis, with positive block coefficients. -/
structure ExceptionalUnitaryNormalForm (N : AntilinearMap V) where
  r : ℕ
  s : ℕ
  coefficient : Fin r → ℝ
  basis : OrthonormalBasis ((Fin r ⊕ Fin s) ⊕ Fin r) ℂ V
  positive : ∀ i, 0 < coefficient i
  rank_eq : r = finrank ℂ N.range
  dimension_eq : finrank ℂ V = 2 * r + s
  apply_u : ∀ i, N (basis (.inl (.inl i))) = 0
  apply_w : ∀ i, N (basis (.inl (.inr i))) = 0
  apply_v : ∀ i, N (basis (.inr i)) =
    (coefficient i : ℂ) • basis (.inl (.inl i))

/-- Existence of the full unitary singular-value normal form. -/
theorem AntilinearMap.exists_unitaryNormalForm (N : AntilinearMap V)
    (hN : ∀ v, N (N v) = 0) : Nonempty (ExceptionalUnitaryNormalForm N) := by
  classical
  let M := N.kerᗮ
  let B : ConjugateSpace M →ₗ[ℂ] N.range :=
    { toFun x := ⟨N (unconjugate (V := M) x : V), ⟨(unconjugate (V := M) x : V), rfl⟩⟩
      map_add' x y := by apply Subtype.ext; exact map_add N _ _
      map_smul' c x := by
        apply Subtype.ext
        change N (star c • (unconjugate (V := M) x : V)) = c • N (unconjugate (V := M) x : V)
        rw [N.map_smulₛₗ]
        exact congrArg (fun z : ℂ => z • N (unconjugate (V := M) x : V)) (star_star c) }
  have hB : Function.Bijective B := by
    constructor
    · intro x y hxy
      have hxy' : N (unconjugate (V := M) x : V) =
          N (unconjugate (V := M) y : V) := congrArg Subtype.val hxy
      have hk : (unconjugate (V := M) x : V) - (unconjugate (V := M) y : V) ∈ N.ker := by
        change N ((unconjugate (V := M) x : V) - (unconjugate (V := M) y : V)) = 0
        rw [map_sub, hxy', sub_self]
      have hm : (unconjugate (V := M) x : V) - (unconjugate (V := M) y : V) ∈ M :=
        M.sub_mem (unconjugate (V := M) x).property (unconjugate (V := M) y).property
      have hz : (unconjugate (V := M) x : V) - (unconjugate (V := M) y : V) ∈
          (⊥ : Submodule ℂ V) := by
        rw [← N.ker.inf_orthogonal_eq_bot]
        exact ⟨hk, hm⟩
      change (unconjugate (V := M) x : V) - (unconjugate (V := M) y : V) = 0 at hz
      exact Subtype.ext (sub_eq_zero.mp hz)
    · intro u
      obtain ⟨v, hv⟩ := u.property
      let eK := N.ker.prodEquivOfIsCompl M N.ker.isCompl_orthogonal
      refine ⟨conjugate (eK.symm v).2, ?_⟩
      apply Subtype.ext
      change N ((eK.symm v).2 : V) = u
      have hd := congrArg N (eK.apply_symm_apply v)
      change N (((eK.symm v).1 : V) + ((eK.symm v).2 : V)) = N v at hd
      rw [map_add, show N ((eK.symm v).1 : V) = 0 from (eK.symm v).1.property,
        zero_add] at hd
      exact hd.trans hv
  obtain ⟨σ, vc, u, hσ, hBu⟩ := linearMap_exists_singularBases B hB
  let vm := unconjugateOrthonormalBasis vc
  let U := N.range.comap N.ker.subtype
  let eU : N.range ≃ₗᵢ[ℂ] U :=
    { toFun u := ⟨⟨u, N.range_le_ker hN u.property⟩, u.property⟩
      invFun u := ⟨u.1, u.property⟩
      left_inv u := rfl
      right_inv u := rfl
      map_add' u v := rfl
      map_smul' c u := rfl
      norm_map' u := rfl }
  let w := stdOrthonormalBasis ℂ Uᗮ
  let bk := ((u.map eU).prod w).map U.orthogonalDecomposition.symm
  let b := (bk.prod vm).map N.ker.orthogonalDecomposition.symm
  have hu (i) : b (.inl (.inl i)) = (u i : V) := by
    calc
      b (.inl (.inl i)) = (bk (.inl i) : V) := by
        simp only [b, OrthonormalBasis.map_apply, OrthonormalBasis.prod_apply,
          Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply]
        exact decomposition_left N.ker _
      _ = (u i : V) := by
        simp only [bk, OrthonormalBasis.map_apply, OrthonormalBasis.prod_apply,
          Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply, OrthonormalBasis.map_apply]
        change ((U.orthogonalDecomposition.symm (WithLp.toLp 2 (eU (u i), 0))) : V) = _
        rw [decomposition_left]
        rfl
  have hw (i) : b (.inl (.inr i)) = ((bk (.inr i) : N.ker) : V) := by
    simp only [b, OrthonormalBasis.map_apply, OrthonormalBasis.prod_apply,
      Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply]
    exact decomposition_left N.ker _
  have hv (i) : b (.inr i) = (unconjugate (V := M) (vc i) : V) := by
    simp only [b, OrthonormalBasis.map_apply, OrthonormalBasis.prod_apply,
      Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply]
    exact (decomposition_right N.ker _).trans
      (by simp only [vm, unconjugateOrthonormalBasis_apply]; rfl)
  refine ⟨{
    r := finrank ℂ (ConjugateSpace M)
    s := finrank ℂ Uᗮ
    coefficient := σ
    basis := b
    positive := hσ
    rank_eq := (LinearEquiv.ofBijective B hB).finrank_eq
    dimension_eq := ?_
    apply_u := ?_
    apply_w := ?_
    apply_v := ?_ }⟩
  · have hd := finrank_eq_card_basis b.toBasis
    simp only [Fintype.card_sum, Fintype.card_fin] at hd
    omega
  · intro i
    rw [hu]
    exact N.range_le_ker hN (u i).property
  · intro i
    rw [hw]
    exact (bk (.inr i)).property
  · intro i
    rw [hv, hu]
    exact congrArg Subtype.val (hBu i)

end UnitaryNormalForms

end

end VanAubelExtensions
