/-
Copyright (c) 2026 mindofcharles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mindofcharles
-/

import VanAubelExtensions.ComplexAffineTransfer
import VanAubelExtensions.ComplexStructureSpace
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Square-zero complex-antilinear maps

Complex-antilinear maps are bundled as semilinear maps over complex conjugation.
The real-linear bridge preserves the existing edge-operator interfaces.
-/

namespace VanAubelExtensions

noncomputable section

open Module

section ComplexAntilinear

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

abbrev AntilinearMap (V : Type*) [AddCommGroup V] [Module ℂ V] :=
  V →ₛₗ[starRingEnd ℂ] V

/-- The underlying real-linear map of a complex-antilinear map. -/
def AntilinearMap.realMap (N : AntilinearMap V) : V →ₗ[ℝ] V where
  toFun := N
  map_add' := N.map_add
  map_smul' c v := by
    change N ((c : ℂ) • v) = (c : ℂ) • N v
    rw [N.map_smulₛₗ]
    exact congrArg (fun z : ℂ => z • N v) (Complex.conj_ofReal c)

@[simp] theorem AntilinearMap.realMap_apply (N : AntilinearMap V) (v : V) :
    N.realMap v = N v := rfl

theorem AntilinearMap.range_le_ker (N : AntilinearMap V)
    (hN : ∀ v, N (N v) = 0) : N.range ≤ N.ker := by
  rintro v ⟨x, rfl⟩
  exact hN x

/-- Rank-nullity for antilinear maps, obtained through their underlying real maps. -/
theorem AntilinearMap.finrank_range_add_finrank_ker [FiniteDimensional ℂ V]
    (N : AntilinearMap V) :
    Module.finrank ℂ N.range + Module.finrank ℂ N.ker = Module.finrank ℂ V := by
  have hr : N.realMap.range = N.range.restrictScalars ℝ := by ext v; rfl
  have hk : N.realMap.ker = N.ker.restrictScalars ℝ := by ext v; rfl
  have h := N.realMap.finrank_range_add_finrank_ker
  rw [hr, hk] at h
  change Module.finrank ℝ N.range + Module.finrank ℝ N.ker = Module.finrank ℝ V at h
  rw [finrank_real_of_complex N.range, finrank_real_of_complex N.ker,
    finrank_real_of_complex V] at h
  omega

/-- The sharp rank restriction for the exceptional parameter. -/
theorem AntilinearMap.rank_bound [FiniteDimensional ℂ V]
    (N : AntilinearMap V) (hN : ∀ v, N (N v) = 0) :
    2 * Module.finrank ℂ N.range ≤ Module.finrank ℂ V := by
  have hle := Submodule.finrank_mono (N.range_le_ker hN)
  have heq := N.finrank_range_add_finrank_ker
  omega

/-- Conjugation of the coordinate vector, without choosing a real form on `V`. -/
def coordinateConjugation (n : ℕ) :
    (Fin n → ℂ) ≃ₛₗ[starRingEnd ℂ] (Fin n → ℂ) where
  toFun x i := star (x i)
  invFun x i := star (x i)
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_add' x y := by ext i; exact map_add (starRingEnd ℂ) (x i) (y i)
  map_smul' c x := by ext i; exact map_mul (starRingEnd ℂ) c (x i)

@[simp] theorem coordinateConjugation_apply (n : ℕ) (x : Fin n → ℂ) (i : Fin n) :
    coordinateConjugation n x i = star (x i) := rfl

/-- The conjugation determined by a specified complex basis. -/
def basisConjugation {n : ℕ} (b : Basis (Fin n) ℂ V) : V ≃ₛₗ[starRingEnd ℂ] V :=
  b.equivFun.trans ((coordinateConjugation n).trans b.equivFun.symm)

theorem basisConjugation_coordinates {n : ℕ} (b : Basis (Fin n) ℂ V) (x : V) :
    b.equivFun (basisConjugation b x) = coordinateConjugation n (b.equivFun x) := by
  change b.equivFun (b.equivFun.symm (coordinateConjugation n (b.equivFun x))) = _
  exact b.equivFun.apply_symm_apply _

@[simp] theorem basisConjugation_basis {n : ℕ} (b : Basis (Fin n) ℂ V) (i : Fin n) :
    basisConjugation b (b i) = b i := by
  apply b.equivFun.injective
  rw [basisConjugation_coordinates]
  ext j
  simp only [coordinateConjugation_apply, Basis.equivFun_self]
  split_ifs <;> simp

@[simp] theorem basisConjugation_involutive {n : ℕ} (b : Basis (Fin n) ℂ V) (x : V) :
    basisConjugation b (basisConjugation b x) = x := by
  apply b.equivFun.injective
  rw [basisConjugation_coordinates, basisConjugation_coordinates]
  ext i
  simp only [coordinateConjugation_apply, star_star]

/-- A complex-linear lift of a basis of the image. Its composite with `N` is
the basis conjugation, rather than the identity. -/
theorem AntilinearMap.exists_linearLift [FiniteDimensional ℂ V]
    (N : AntilinearMap V) :
    ∃ R : N.range →ₗ[ℂ] V,
      ∀ q, N (R q) = (basisConjugation (Module.finBasis ℂ N.range) q : V) := by
  let b := Module.finBasis ℂ N.range
  choose v hv using fun i => (b i).property
  let R : N.range →ₗ[ℂ] V := b.constr ℂ v
  refine ⟨R, ?_⟩
  have heq : N.comp R = N.range.subtype.comp (basisConjugation b).toLinearMap := by
    apply b.ext
    intro i
    simp [R, hv]
  intro q
  exact LinearMap.congr_fun heq q

/-- A coordinate model consists of two rank-sized blocks and a zero block. -/
abbrev ExceptionalModel (r s : ℕ) := ((Fin r → ℂ) × (Fin s → ℂ)) × (Fin r → ℂ)

def exceptionalModelMap (r s : ℕ) : AntilinearMap (ExceptionalModel r s) where
  toFun x := ((coordinateConjugation r x.2, 0), 0)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

@[simp] theorem exceptionalModelMap_apply (r s : ℕ) (x : ExceptionalModel r s) :
    exceptionalModelMap r s x = ((coordinateConjugation r x.2, 0), 0) := rfl

@[simp] theorem exceptionalModelMap_sq (r s : ℕ) (x : ExceptionalModel r s) :
    exceptionalModelMap r s (exceptionalModelMap r s x) = 0 := by
  ext <;> simp [exceptionalModelMap]

/-- Every square-zero antilinear map has the rank normal form. -/
theorem AntilinearMap.exists_rank_normalForm [FiniteDimensional ℂ V]
    (N : AntilinearMap V) (hN : ∀ v, N (N v) = 0) :
    ∃ r s : ℕ, ∃ e : ExceptionalModel r s ≃ₗ[ℂ] V,
      r = Module.finrank ℂ N.range ∧ Module.finrank ℂ V = 2 * r + s ∧
        ∀ x, N (e x) = e (exceptionalModelMap r s x) := by
  classical
  let U := N.range.comap N.ker.subtype
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl U
  let eK := U.prodEquivOfIsCompl W hW
  let eU : N.range ≃ₗ[ℂ] U :=
    { toFun u := ⟨⟨u, N.range_le_ker hN u.property⟩, u.property⟩
      invFun u := ⟨u.1, u.property⟩
      left_inv u := rfl
      right_inv u := rfl
      map_add' u v := rfl
      map_smul' c u := rfl }
  obtain ⟨R, hR⟩ := N.exists_linearLift
  let b := Module.finBasis ℂ N.range
  let C := basisConjugation b
  have hC (u : N.range) : C (C u) = u := basisConjugation_involutive b u
  have hEK (u : N.range) : (eK (eU u, 0) : V) = u := by
    simp [eK, eU, Submodule.coe_prodEquivOfIsCompl']
  let T : ((N.range × W) × N.range) →ₗ[ℂ] V :=
    (N.ker.subtype.comp (eK.toLinearMap.comp
      (eU.toLinearMap.prodMap (LinearMap.id : W →ₗ[ℂ] W)))).coprod R
  have hNT (x : (N.range × W) × N.range) : N (T x) = (C x.2 : V) := by
    change N ((eK (eU x.1.1, x.1.2) : V) + R x.2) = _
    rw [map_add, show N (eK (eU x.1.1, x.1.2) : V) = 0 from
      (eK (eU x.1.1, x.1.2)).property, zero_add, hR]
  have hTzero (x : (N.range × W) × N.range) (hx : T x = 0) : x = 0 := by
    have hCx : C x.2 = 0 := by
      apply Subtype.ext
      change (C x.2 : V) = 0
      rw [← hNT x, hx, map_zero]
    have hq : x.2 = 0 := C.injective (by simpa using hCx)
    have hp : eK (eU x.1.1, x.1.2) = 0 := by
      apply Subtype.ext
      simpa [T, hq] using hx
    have hp' : (eU x.1.1, x.1.2) = 0 := eK.injective (by simpa using hp)
    have hu : x.1.1 = 0 := eU.injective (by simpa using congrArg Prod.fst hp')
    have hw : x.1.2 = 0 := congrArg Prod.snd hp'
    exact Prod.ext (Prod.ext hu hw) hq
  have hTinj : Function.Injective T := by
    intro x y hxy
    exact sub_eq_zero.mp (hTzero (x - y) (by rw [map_sub, hxy, sub_self]))
  have hTsurj : Function.Surjective T := by
    intro v
    let q : N.range := C ⟨N v, ⟨v, rfl⟩⟩
    have hq : N (R q) = N v := by
      rw [hR]
      exact congrArg Subtype.val (hC ⟨N v, ⟨v, rfl⟩⟩)
    let k : N.ker := ⟨v - R q, by change N (v - R q) = 0; rw [map_sub, hq, sub_self]⟩
    let z := eK.symm k
    refine ⟨((eU.symm z.1, z.2), q), ?_⟩
    change (eK (eU (eU.symm z.1), z.2) : V) + R q = v
    rw [eU.apply_symm_apply]
    change (eK (eK.symm k) : V) + R q = v
    rw [eK.apply_symm_apply]
    change (v - R q) + R q = v
    module
  let eT := LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩
  let bw := Module.finBasis ℂ W
  let coordinates := (b.equivFun.symm.prodCongr bw.equivFun.symm).prodCongr b.equivFun.symm
  let e := coordinates.trans eT
  refine ⟨Module.finrank ℂ N.range, Module.finrank ℂ W, e, rfl, ?_, ?_⟩
  · have hd := e.finrank_eq
    simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin] at hd
    omega
  · intro x
    change N (T (coordinates x)) = T (coordinates (exceptionalModelMap _ _ x))
    rw [hNT]
    simp only [coordinates, LinearEquiv.prodCongr_apply, exceptionalModelMap_apply, map_zero]
    change (C (b.equivFun.symm x.2) : V) =
      (eK (eU (b.equivFun.symm (coordinateConjugation _ x.2)), 0) : V) + R 0
    rw [map_zero, add_zero, hEK]
    apply congrArg Subtype.val
    apply b.equivFun.injective
    change b.equivFun (basisConjugation b (b.equivFun.symm x.2)) = _
    rw [basisConjugation_coordinates]
    simp only [b.equivFun.apply_symm_apply]

/-- Complex-linear conjugacy is classified exactly by the complex rank. -/
theorem AntilinearMap.conjugate_iff_rank_eq [FiniteDimensional ℂ V]
    (N M : AntilinearMap V) (hN : ∀ v, N (N v) = 0) (hM : ∀ v, M (M v) = 0) :
    (∃ G : V ≃ₗ[ℂ] V, ∀ v, M (G v) = G (N v)) ↔
      Module.finrank ℂ N.range = Module.finrank ℂ M.range := by
  constructor
  · rintro ⟨G, hG⟩
    have hrange : N.range.map G.toLinearMap = M.range := by
      ext v
      constructor
      · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
        exact ⟨G x, hG x⟩
      · rintro ⟨x, rfl⟩
        refine ⟨N (G.symm x), ⟨G.symm x, rfl⟩, ?_⟩
        change G (N (G.symm x)) = M x
        rw [← hG, G.apply_symm_apply]
    rw [← hrange, G.finrank_map_eq]
  · intro hrank
    obtain ⟨r, s, e, hr, hd, he⟩ := N.exists_rank_normalForm hN
    obtain ⟨r', s', e', hr', hd', he'⟩ := M.exists_rank_normalForm hM
    have hrr : r' = r := hr'.trans (hrank.symm.trans hr.symm)
    cases hrr
    have hss : s' = s := by omega
    cases hss
    refine ⟨e.symm.trans e', ?_⟩
    intro v
    obtain ⟨x, rfl⟩ := e.surjective v
    change M (e' (e.symm (e x))) = e' (e.symm (N (e x)))
    rw [e.symm_apply_apply, he, he', e.symm_apply_apply]

/-- Each admissible block rank is realized by the explicit coordinate model. -/
theorem exceptionalModelMap_rank (r s : ℕ) :
    Module.finrank ℂ (exceptionalModelMap r s).range = r := by
  let f : (Fin r → ℂ) →ₗ[ℂ] ExceptionalModel r s :=
    { toFun u := ((u, 0), 0)
      map_add' u v := by simp
      map_smul' c u := by simp }
  have hf : Function.Injective f := by
    intro u v huv
    exact congrArg (fun x : ExceptionalModel r s => x.1.1) huv
  have hrange : (exceptionalModelMap r s).range = f.range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨coordinateConjugation r y.2, rfl⟩
    · rintro ⟨u, rfl⟩
      refine ⟨((0, 0), coordinateConjugation r u), ?_⟩
      ext i <;> simp [exceptionalModelMap, f]
  rw [hrange, LinearMap.finrank_range_of_inj hf]
  simp

/-- Every rank allowed by the bound occurs on every complex space of that dimension. -/
theorem exists_squareZero_antilinear_of_rank [FiniteDimensional ℂ V]
    (r : ℕ) (hr : 2 * r ≤ Module.finrank ℂ V) :
    ∃ N : AntilinearMap V, (∀ v, N (N v) = 0) ∧ Module.finrank ℂ N.range = r := by
  classical
  let s := Module.finrank ℂ V - 2 * r
  have hd : Module.finrank ℂ (ExceptionalModel r s) = Module.finrank ℂ V := by
    simp only [ExceptionalModel, Module.finrank_prod, Module.finrank_pi, Fintype.card_fin]
    dsimp [s]
    omega
  let e : ExceptionalModel r s ≃ₗ[ℂ] V := LinearEquiv.ofFinrankEq (ExceptionalModel r s) V hd
  let N : AntilinearMap V := e.toLinearMap.comp ((exceptionalModelMap r s).comp e.symm.toLinearMap)
  have hN (v : V) : N v = e (exceptionalModelMap r s (e.symm v)) := rfl
  refine ⟨N, ?_, ?_⟩
  · intro v
    simp only [hN, e.symm_apply_apply, exceptionalModelMap_sq, map_zero]
  · have hrange : (exceptionalModelMap r s).range.map e.toLinearMap = N.range := by
      ext v
      constructor
      · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
        refine ⟨e x, ?_⟩
        change N (e x) = e (exceptionalModelMap r s x)
        rw [hN, e.symm_apply_apply]
      · rintro ⟨x, rfl⟩
        exact ⟨exceptionalModelMap r s (e.symm x), ⟨e.symm x, rfl⟩, rfl⟩
    rw [← hrange, e.finrank_map_eq, exceptionalModelMap_rank]

end ComplexAntilinear

section RealComplexStructureBridge

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- The rank normal form applies to the original real edge-operator parameter. -/
theorem real_exceptional_rank_normalForm
    (K N : V →ₗ[ℝ] V) (hK : IsLinearComplexStructure K)
    (hNN : ∀ v, N (N v) = 0) (hanti : ∀ v, K (N v) + N (K v) = 0) :
    ∃ r s : ℕ, ∃ e : ExceptionalModel r s ≃ₗ[ℂ] ComplexStructureSpace K hK,
      r = Module.finrank ℂ (ComplexStructureSpace.antilinearMap K hK N hanti).range ∧
      Module.finrank ℂ (ComplexStructureSpace K hK) = 2 * r + s ∧
      ∀ x, N (e x) = e (exceptionalModelMap r s x) := by
  exact AntilinearMap.exists_rank_normalForm
    (ComplexStructureSpace.antilinearMap K hK N hanti) hNN

end RealComplexStructureBridge

end

end VanAubelExtensions
