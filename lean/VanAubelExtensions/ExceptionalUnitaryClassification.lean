/-
Copyright (c) 2026 mindofcharles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mindofcharles
-/

import VanAubelExtensions.ExceptionalMetric
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Logic.Equiv.Basic

/-!
# Classification of exceptional parameters under unitary conjugacy

The positive Gram spectrum identifies the adapted-basis coefficients as a
unique multiset. Matching those coefficients constructs a unitary intertwiner.
-/

namespace VanAubelExtensions

noncomputable section

open Module Polynomial
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

/-- The Gram map of an antilinear map, expressed on the original complex
space by conjugating both domain and codomain of its linearized Gram map. -/
def AntilinearMap.gram (N : AntilinearMap V) : V →ₗ[ℂ] V := by
  let A := N.linearized.adjoint.comp N.linearized
  refine {
    toFun := fun v => unconjugate (A (conjugate v))
    map_add' := ?_
    map_smul' := ?_ }
  · intro x y
    exact congrArg unconjugate (A.map_add (conjugate x) (conjugate y))
  · intro c v
    have h := congrArg unconjugate (A.map_smul (star c) (conjugate v))
    change unconjugate (A (conjugate (star (star c) • v))) =
      star (star c) • unconjugate (A (conjugate v)) at h
    simpa only [star_star, RingHom.id_apply] using h

theorem AntilinearMap.gram_inner (N : AntilinearMap V) (x y : V) :
    ⟪x, N.gram y⟫_ℂ = ⟪N y, N x⟫_ℂ := by
  have h := N.linearized.adjoint_inner_right (conjugate x) (N y)
  change star ⟪x, N.gram y⟫_ℂ = ⟪N x, N y⟫_ℂ at h
  have hs := congrArg star h
  rw [star_star] at hs
  exact hs.trans (inner_conj_symm (N y) (N x))

/-- The multiset of positive singular values, extracted from the Gram spectrum. -/
def AntilinearMap.positiveSingularValues (N : AntilinearMap V) : Multiset ℝ := by
  classical
  exact (N.gram.charpoly.roots.map (fun z => Real.sqrt z.re)).filter (fun t => 0 < t)

namespace ExceptionalUnitaryNormalForm

variable {N : AntilinearMap V} (F : ExceptionalUnitaryNormalForm N)

def coefficientValues : Multiset ℝ := (Finset.univ : Finset (Fin F.r)).val.map F.coefficient

def gramDiagonal : ((Fin F.r ⊕ Fin F.s) ⊕ Fin F.r) → ℂ :=
  Sum.elim (fun _ => 0) (fun i => (F.coefficient i : ℂ) ^ 2)

theorem gram_basis (j : (Fin F.r ⊕ Fin F.s) ⊕ Fin F.r) :
    N.gram (F.basis j) = F.gramDiagonal j • F.basis j := by
  apply InnerProductSpace.ext_inner_left_basis F.basis.toBasis
  intro i
  rw [F.basis.coe_toBasis, N.gram_inner, inner_smul_right]
  rcases i with (i | i) | i <;> rcases j with (j | j) | j <;>
    simp only [gramDiagonal, Sum.elim_inl, Sum.elim_inr, F.apply_u, F.apply_w, F.apply_v,
      inner_zero_left, inner_zero_right, F.basis.inner_eq_ite,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, mul_ite, mul_one, mul_zero,
      if_false, ite_self]
  by_cases h : i = j
  · subst j
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos (F.positive i), ← Complex.ofReal_pow]
  · rw [if_neg h]
    change ⟪(F.coefficient j : ℂ) • F.basis (.inl (.inl j)),
      (F.coefficient i : ℂ) • F.basis (.inl (.inl i))⟫_ℂ = 0
    rw [inner_smul_left, inner_smul_right, F.basis.inner_eq_zero (by simpa using Ne.symm h)]
    simp

theorem gram_toMatrix :
    LinearMap.toMatrix F.basis.toBasis F.basis.toBasis N.gram =
      Matrix.diagonal F.gramDiagonal := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change F.basis.toBasis.repr (N.gram (F.basis j)) i = _
  rw [F.gram_basis]
  by_cases hij : i = j
  · subst j; simp
  · simp [hij]

theorem gram_charpoly : N.gram.charpoly =
    ∏ i : (Fin F.r ⊕ Fin F.s) ⊕ Fin F.r, (X - C (F.gramDiagonal i)) := by
  rw [← N.gram.charpoly_toMatrix F.basis.toBasis, F.gram_toMatrix, Matrix.charpoly_diagonal]

theorem gram_roots : N.gram.charpoly.roots =
    (Finset.univ : Finset ((Fin F.r ⊕ Fin F.s) ⊕ Fin F.r)).val.map F.gramDiagonal := by
  rw [F.gram_charpoly, Polynomial.roots_prod]
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  · exact Finset.prod_ne_zero_iff.mpr (fun _ _ => X_sub_C_ne_zero _)

theorem positiveSingularValues_eq : N.positiveSingularValues = F.coefficientValues := by
  classical
  rw [AntilinearMap.positiveSingularValues, F.gram_roots]
  rw [Multiset.map_map]
  change ((Finset.univ : Finset ((Fin F.r ⊕ Fin F.s) ⊕ Fin F.r)).val.map
    (fun i => Real.sqrt (F.gramDiagonal i).re)).filter (fun t => 0 < t) = _
  rw [← Finset.univ_disjSum_univ]
  simp only [Finset.val_disjSum, Multiset.disjSum, Multiset.map_add,
    Multiset.map_map, Multiset.filter_add, Function.comp_def, gramDiagonal,
    Sum.elim_inl, Sum.elim_inr]
  simp only [Complex.zero_re, Real.sqrt_zero]
  simp only [Multiset.filter_map]
  have hzero : (fun _ : Fin F.r ⊕ Fin F.s => (0 : ℝ) < 0) = fun _ => False := by
    funext i
    simp
  simp only [Function.comp_def, hzero, Multiset.filter_false, Multiset.map_zero, zero_add]
  have hsqrt (i : Fin F.r) : Real.sqrt (((F.coefficient i : ℂ) ^ 2).re) = F.coefficient i := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re, Real.sqrt_sq (F.positive i).le]
  simp only [hsqrt]
  change ((Finset.univ : Finset (Fin F.r)).val.filter
    (fun i => 0 < F.coefficient i)).map F.coefficient = _
  rw [Multiset.filter_eq_self.mpr (fun i _ => F.positive i)]
  rfl

/-- The positive block coefficients are unique as a multiset. -/
theorem coefficientValues_unique (G : ExceptionalUnitaryNormalForm N) :
    F.coefficientValues = G.coefficientValues :=
  F.positiveSingularValues_eq.symm.trans G.positiveSingularValues_eq

/-- Transport of an adapted orthonormal basis along a unitary intertwiner. -/
def mapUnitary (M : AntilinearMap V) (hN : ∀ v, N (N v) = 0)
    (hM : ∀ v, M (M v) = 0) (G : V ≃ₗᵢ[ℂ] V) (hG : ∀ v, M (G v) = G (N v)) :
    ExceptionalUnitaryNormalForm M where
  r := F.r
  s := F.s
  coefficient := F.coefficient
  basis := F.basis.map G
  positive := F.positive
  rank_eq := F.rank_eq.trans
    ((AntilinearMap.conjugate_iff_rank_eq N M hN hM).mp ⟨G.toLinearEquiv, hG⟩)
  dimension_eq := F.dimension_eq
  apply_u i := by simp only [OrthonormalBasis.map_apply, hG, F.apply_u, map_zero]
  apply_w i := by simp only [OrthonormalBasis.map_apply, hG, F.apply_w, map_zero]
  apply_v i := by simp only [OrthonormalBasis.map_apply, hG, F.apply_v, map_smul]

end ExceptionalUnitaryNormalForm

/-- Equal finite value multisets can be matched by an index equivalence. -/
private theorem equiv_of_value_multiset_eq {α β γ : Type*} [Fintype α] [Fintype β]
    (f : α → γ) (g : β → γ)
    (h : (Finset.univ : Finset α).val.map f = (Finset.univ : Finset β).val.map g) :
    ∃ e : α ≃ β, ∀ a, g (e a) = f a := by
  classical
  have hc (c : γ) : Fintype.card {a // f a = c} = Fintype.card {b // g b = c} := by
    have hh := congrArg (Multiset.count c) h
    simp only [Fintype.card_subtype]
    change ((Finset.univ : Finset α).val.filter (fun a => f a = c)).card =
      ((Finset.univ : Finset β).val.filter (fun b => g b = c)).card
    simpa only [Multiset.count_map, eq_comm] using hh
  let e := fun c => Fintype.equivOfCardEq (hc c)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

/-- The positive singular-value multiset classifies square-zero antilinear
maps under complex-linear unitary conjugacy. -/
theorem AntilinearMap.unitary_conjugate_iff (N M : AntilinearMap V)
    (hN : ∀ v, N (N v) = 0) (hM : ∀ v, M (M v) = 0) :
    (∃ G : V ≃ₗᵢ[ℂ] V, ∀ v, M (G v) = G (N v)) ↔
      N.positiveSingularValues = M.positiveSingularValues := by
  classical
  constructor
  · rintro ⟨G, hG⟩
    obtain ⟨F⟩ := N.exists_unitaryNormalForm hN
    let F' := F.mapUnitary M hN hM G hG
    rw [F.positiveSingularValues_eq, F'.positiveSingularValues_eq]
    rfl
  · intro hvalues
    obtain ⟨F⟩ := N.exists_unitaryNormalForm hN
    obtain ⟨F'⟩ := M.exists_unitaryNormalForm hM
    have hcoeff : F.coefficientValues = F'.coefficientValues :=
      F.positiveSingularValues_eq.symm.trans (hvalues.trans F'.positiveSingularValues_eq)
    obtain ⟨ec, hec⟩ := equiv_of_value_multiset_eq F.coefficient F'.coefficient hcoeff
    have hr : F.r = F'.r := by
      simpa only [Fintype.card_fin] using Fintype.card_congr ec
    have hs : F.s = F'.s := by
      have hd := F.dimension_eq
      have hd' := F'.dimension_eq
      omega
    let ew : Fin F.s ≃ Fin F'.s := Fintype.equivOfCardEq (by simpa using hs)
    let ei := (Equiv.sumCongr ec ew).sumCongr ec
    let G := F.basis.equiv F'.basis ei
    refine ⟨G, ?_⟩
    have hmaps : M.comp G.toLinearEquiv.toLinearMap = G.toLinearEquiv.toLinearMap.comp N := by
      apply F.basis.toBasis.ext
      intro i
      change M (G (F.basis i)) = G (N (F.basis i))
      rcases i with (i | i) | i
      · simp [G, ei, F.apply_u, F'.apply_u]
      · simp [G, ei, F.apply_w, F'.apply_w]
      · rw [F.apply_v, G.map_smul]
        simp [G, ei, F'.apply_v, hec]
    intro v
    exact LinearMap.congr_fun hmaps v

end

end VanAubelExtensions
