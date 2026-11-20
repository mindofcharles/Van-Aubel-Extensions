/-
Copyright (c) 2026 mindofcharles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mindofcharles
-/

import VanAubelExtensions.OperatorDefect
import VanAubelExtensions.ComplexStructureSpace

/-!
# Mixed-sign identities and their linear loci

Edges and mismatch bits are indexed by `Fin 4`, starting at zero.
The single uniform defect formula is connected to the actual four centers;
the sixteen-row criterion and the dimension computations follow from it.
-/

namespace VanAubelExtensions

noncomputable section

/-- A Boolean mismatch bit as a real scalar. -/
def mismatchBit (b : Bool) : ℝ := if b then 1 else 0

/-- The sign on an edge, relative to the prescribed target sign. -/
def mismatchEdgeSign (δ : ℝ) (b : Bool) : ℝ := δ * (1 - 2 * mismatchBit b)

def mismatchOfSign (δ ε : ℝ) : Bool := decide (ε ≠ δ)

theorem mismatchOfSign_bit (δ ε : ℝ) (hδ : δ ^ 2 = 1) (hε : ε ^ 2 = 1) :
    mismatchBit (mismatchOfSign δ ε) = (1 - δ * ε) / 2 := by
  rcases sq_eq_one_iff.mp hδ with rfl | rfl <;>
    rcases sq_eq_one_iff.mp hε with rfl | rfl <;>
    norm_num [mismatchBit, mismatchOfSign]

theorem mismatchOfSign_recover (δ ε : ℝ) (hδ : δ ^ 2 = 1) (hε : ε ^ 2 = 1) :
    mismatchEdgeSign δ (mismatchOfSign δ ε) = ε := by
  rcases sq_eq_one_iff.mp hδ with rfl | rfl <;>
    rcases sq_eq_one_iff.mp hε with rfl | rfl <;>
    norm_num [mismatchEdgeSign, mismatchBit, mismatchOfSign]

section RealDefects

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def cyclicEdges (A B C D : V) : Fin 4 → V := ![B - A, C - B, D - C, A - D]

def mismatchVector (J : V →ₗ[ℝ] V) (δ : ℝ) (t : Fin 4 → Bool)
    (u : Fin 4 → V) : V :=
  mismatchBit (t 1) • u 1 - mismatchBit (t 3) • u 3 +
    δ • J (mismatchBit (t 0) • u 0 - mismatchBit (t 2) • u 2)

/-- Exact defect formula for the four independently chosen edge signs. -/
theorem operatorDefect_mixedSigns
    (J : V →ₗ[ℝ] V) (hJ : IsLinearComplexStructure J)
    (δ : ℝ) (hδ : δ ^ 2 = 1) (t : Fin 4 → Bool) (A B C D : V) :
    operatorDefect (δ • J)
      (mismatchEdgeSign δ (t 0) • J) (mismatchEdgeSign δ (t 1) • J)
      (mismatchEdgeSign δ (t 2) • J) (mismatchEdgeSign δ (t 3) • J) A B C D =
      mismatchVector J δ t (cyclicEdges A B C D) := by
  have hJsq : ∀ v, J (J v) = -v := hJ
  rcases sq_eq_one_iff.mp hδ with rfl | rfl <;>
    simp only [operatorDefect, operatorCenter, mismatchVector, cyclicEdges,
      mismatchEdgeSign, LinearMap.smul_apply, map_sub, map_add, map_smul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      hJsq] <;> module

/-- The complete sixteen-row table, with edges numbered from zero. -/
def mismatchCondition (J : V →ₗ[ℝ] V) (δ : ℝ) (t : Fin 4 → Bool)
    (u : Fin 4 → V) : Prop :=
  match t 0, t 1, t 2, t 3 with
  | false, false, false, false => True
  | true, false, false, false => u 0 = 0
  | false, true, false, false => u 1 = 0
  | false, false, true, false => u 2 = 0
  | false, false, false, true => u 3 = 0
  | true, true, false, false => u 1 = -(δ • J (u 0))
  | false, true, true, false => u 1 = δ • J (u 2)
  | false, false, true, true => u 3 = -(δ • J (u 2))
  | true, false, false, true => u 3 = δ • J (u 0)
  | true, false, true, false => u 0 = u 2
  | false, true, false, true => u 1 = u 3
  | true, true, true, false => u 1 + δ • J (u 0 - u 2) = 0
  | false, true, true, true => u 1 - u 3 - δ • J (u 2) = 0
  | true, false, true, true => -u 3 + δ • J (u 0 - u 2) = 0
  | true, true, false, true => u 1 - u 3 + δ • J (u 0) = 0
  | true, true, true, true => u 1 - u 3 + δ • J (u 0 - u 2) = 0

/-- Every row of the finite table is equivalent to the uniform equation. -/
theorem mismatchVector_eq_zero_iff
    (J : V →ₗ[ℝ] V) (hJ : IsLinearComplexStructure J)
    (δ : ℝ) (hδ : δ ^ 2 = 1) (t : Fin 4 → Bool) (u : Fin 4 → V) :
    mismatchVector J δ t u = 0 ↔ mismatchCondition J δ t u := by
  change ∀ v, J (J v) = -v at hJ
  have hδne : δ ≠ 0 := by intro h; simp [h] at hδ
  have hJzero (v : V) : J v = 0 ↔ v = 0 := by
    constructor
    · intro h
      have hh := congrArg J h
      simpa [hJ v] using hh
    · rintro rfl; exact map_zero J
  have hJinj : Function.Injective J := by
    intro x y h
    have hh := congrArg J h
    simpa only [hJ, neg_inj] using hh
  cases h0 : t 0 <;> cases h1 : t 1 <;> cases h2 : t 2 <;> cases h3 : t 3 <;>
    simp [mismatchVector, mismatchCondition, h0, h1, h2, h3, mismatchBit,
      hδne, hJzero, hJinj.eq_iff, add_eq_zero_iff_eq_neg,
      sub_eq_add_neg, smul_neg, neg_eq_iff_eq_neg]

/-- The sixteen conditions classify the actual center identity. -/
theorem mixedSigns_centerIdentity_iff
    (J : V →ₗ[ℝ] V) (hJ : IsLinearComplexStructure J)
    (δ : ℝ) (hδ : δ ^ 2 = 1) (t : Fin 4 → Bool) (A B C D : V) :
    operatorCenter (mismatchEdgeSign δ (t 2) • J) C D -
        operatorCenter (mismatchEdgeSign δ (t 0) • J) A B =
      (δ • J) (operatorCenter (mismatchEdgeSign δ (t 3) • J) D A -
        operatorCenter (mismatchEdgeSign δ (t 1) • J) B C) ↔
      mismatchCondition J δ t (cyclicEdges A B C D) := by
  rw [← sub_eq_zero]
  change operatorDefect _ _ _ _ _ A B C D = 0 ↔ _
  rw [operatorDefect_mixedSigns J hJ δ hδ, mismatchVector_eq_zero_iff J hJ δ hδ]

end RealDefects

section AffineMixedSigns

variable {V E : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V E]

theorem affineOperatorDefect_mixedSigns
    (J : V →ₗ[ℝ] V) (hJ : IsLinearComplexStructure J)
    (δ : ℝ) (hδ : δ ^ 2 = 1) (t : Fin 4 → Bool) (A B C D : E) :
    affineOperatorDefect (δ • J)
      (mismatchEdgeSign δ (t 0) • J) (mismatchEdgeSign δ (t 1) • J)
      (mismatchEdgeSign δ (t 2) • J) (mismatchEdgeSign δ (t 3) • J) A B C D =
      mismatchVector J δ t ![B -ᵥ A, C -ᵥ B, D -ᵥ C, A -ᵥ D] := by
  rw [affineOperatorDefect_eq_coordinates _ _ _ _ _ A,
    operatorDefect_mixedSigns J hJ δ hδ]
  congr 1
  funext i
  fin_cases i <;> simp [cyclicEdges, Matrix.cons_val_two, Matrix.cons_val_three,
    vsub_sub_vsub_cancel_right]

end AffineMixedSigns

section ComplexLoci

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def complexIReal : V →ₗ[ℝ] V :=
  (Complex.I • (LinearMap.id : V →ₗ[ℂ] V)).restrictScalars ℝ

theorem complexIReal_sq : IsLinearComplexStructure (complexIReal (V := V)) := by
  intro v
  change Complex.I • (Complex.I • v) = -v
  simp [smul_smul]

/-- The three independent edge vectors, with the fourth determined by closure. -/
def mismatchLocusMap (δ : ℝ) (t : Fin 4 → Bool) : (Fin 3 → V) →ₗ[ℂ] V where
  toFun u :=
    ((mismatchBit (t 3) : ℂ) + (δ * mismatchBit (t 0) : ℝ) * Complex.I) • u 0 +
    ((mismatchBit (t 1) + mismatchBit (t 3) : ℝ) : ℂ) • u 1 +
    ((mismatchBit (t 3) : ℂ) - (δ * mismatchBit (t 2) : ℝ) * Complex.I) • u 2
  map_add' u v := by simp only [Pi.add_apply, smul_add]; module
  map_smul' c u := by simp only [Pi.smul_apply, RingHom.id_apply]; module

/-- The linear locus map is the defect of the quadrilateral with these
three successive edges and initial vertex zero. -/
theorem mismatchLocusMap_eq_operatorDefect (δ : ℝ) (hδ : δ ^ 2 = 1)
    (t : Fin 4 → Bool) (u : Fin 3 → V) :
    mismatchLocusMap δ t u =
      operatorDefect (δ • complexIReal)
        (mismatchEdgeSign δ (t 0) • complexIReal)
        (mismatchEdgeSign δ (t 1) • complexIReal)
        (mismatchEdgeSign δ (t 2) • complexIReal)
        (mismatchEdgeSign δ (t 3) • complexIReal)
        0 (u 0) (u 0 + u 1) (u 0 + u 1 + u 2) := by
  rw [operatorDefect_mixedSigns complexIReal complexIReal_sq δ hδ]
  simp only [mismatchVector, cyclicEdges, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    complexIReal, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply]
  change
    ((mismatchBit (t 3) : ℂ) + (δ * mismatchBit (t 0) : ℝ) * Complex.I) • u 0 +
      ((mismatchBit (t 1) + mismatchBit (t 3) : ℝ) : ℂ) • u 1 +
      ((mismatchBit (t 3) : ℂ) - (δ * mismatchBit (t 2) : ℝ) * Complex.I) • u 2 =
    (mismatchBit (t 1) : ℂ) • ((u 0 + u 1) - u 0) -
      (mismatchBit (t 3) : ℂ) • (0 - (u 0 + u 1 + u 2)) +
      (δ : ℂ) • (Complex.I • ((mismatchBit (t 0) : ℂ) • (u 0 - 0) -
        (mismatchBit (t 2) : ℂ) • ((u 0 + u 1 + u 2) - (u 0 + u 1))))
  push_cast
  module

theorem mismatchLocusMap_surjective (δ : ℝ) (hδ : δ ^ 2 = 1)
    (t : Fin 4 → Bool) (ht : ∃ i, t i = true) :
    Function.Surjective (mismatchLocusMap (V := V) δ t) := by
  intro v
  rcases sq_eq_one_iff.mp hδ with rfl | rfl <;>
    cases h0 : t 0 <;> cases h1 : t 1 <;> cases h2 : t 2 <;> cases h3 : t 3
  all_goals first
    | solve
      | obtain ⟨i, hi⟩ := ht
        fin_cases i <;> simp_all
    | solve
      | refine ⟨![0, v, 0], ?_⟩
        norm_num [mismatchLocusMap, mismatchBit, h0, h1, h2, h3, Matrix.cons_val_two]
    | solve
      | refine ⟨![0, (2 : ℂ)⁻¹ • v, 0], ?_⟩
        norm_num [mismatchLocusMap, mismatchBit, h0, h1, h2, h3, smul_smul, Matrix.cons_val_two]
    | solve
      | refine ⟨![(-Complex.I) • v, 0, 0], ?_⟩
        norm_num [mismatchLocusMap, mismatchBit, h0, h1, h2, h3, smul_smul, Matrix.cons_val_two]
    | solve
      | refine ⟨![Complex.I • v, 0, 0], ?_⟩
        norm_num [mismatchLocusMap, mismatchBit, h0, h1, h2, h3, smul_smul, Matrix.cons_val_two]
    | solve
      | refine ⟨![0, 0, (-Complex.I) • v], ?_⟩
        norm_num [mismatchLocusMap, mismatchBit, h0, h1, h2, h3, smul_smul, Matrix.cons_val_two]
    | solve
      | refine ⟨![0, 0, Complex.I • v], ?_⟩
        norm_num [mismatchLocusMap, mismatchBit, h0, h1, h2, h3, smul_smul, Matrix.cons_val_two]

/-- Every nonempty mismatch locus has complex dimension twice that of `V`. -/
theorem mismatchLocus_finrank [FiniteDimensional ℂ V]
    (δ : ℝ) (hδ : δ ^ 2 = 1) (t : Fin 4 → Bool) (ht : ∃ i, t i = true) :
    Module.finrank ℂ (mismatchLocusMap (V := V) δ t).ker = 2 * Module.finrank ℂ V := by
  have hdim := (mismatchLocusMap (V := V) δ t).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (mismatchLocusMap_surjective δ hδ t ht),
    finrank_top, Module.finrank_pi_fintype] at hdim
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hdim
  omega

def independentEdgeMap : (Fin 4 → V) →ₗ[ℂ] (Fin 3 → V) where
  toFun p := ![p 1 - p 0, p 2 - p 1, p 3 - p 2]
  map_add' p q := by
    ext i
    fin_cases i <;> simp [Matrix.cons_val_two] <;> module
  map_smul' c p := by
    ext i
    fin_cases i <;> simp [Matrix.cons_val_two, smul_sub]

theorem independentEdgeMap_surjective : Function.Surjective (independentEdgeMap (V := V)) := by
  intro u
  refine ⟨![0, u 0, u 0 + u 1, u 0 + u 1 + u 2], ?_⟩
  ext i
  fin_cases i <;> simp [independentEdgeMap, Matrix.cons_val_two, Matrix.cons_val_three]

def mismatchPointLocusMap (δ : ℝ) (t : Fin 4 → Bool) : (Fin 4 → V) →ₗ[ℂ] V :=
  (mismatchLocusMap δ t).comp independentEdgeMap

theorem mismatchPointLocusMap_eq_operatorDefect (δ : ℝ) (hδ : δ ^ 2 = 1)
    (t : Fin 4 → Bool) (p : Fin 4 → V) :
    mismatchPointLocusMap δ t p =
      operatorDefect (δ • complexIReal)
        (mismatchEdgeSign δ (t 0) • complexIReal)
        (mismatchEdgeSign δ (t 1) • complexIReal)
        (mismatchEdgeSign δ (t 2) • complexIReal)
        (mismatchEdgeSign δ (t 3) • complexIReal) (p 0) (p 1) (p 2) (p 3) := by
  rw [mismatchPointLocusMap, LinearMap.comp_apply,
    mismatchLocusMap_eq_operatorDefect δ hδ t]
  change operatorDefect _ _ _ _ _ 0 (p 1 - p 0)
    ((p 1 - p 0) + (p 2 - p 1))
    ((p 1 - p 0) + (p 2 - p 1) + (p 3 - p 2)) = _
  have h2 : (p 1 - p 0) + (p 2 - p 1) = p 2 - p 0 := by module
  have h3 : (p 1 - p 0) + (p 2 - p 1) + (p 3 - p 2) = p 3 - p 0 := by module
  rw [h3, h2]
  simpa only [sub_self] using operatorDefect_sub_origin
    (δ • complexIReal) (mismatchEdgeSign δ (t 0) • complexIReal)
    (mismatchEdgeSign δ (t 1) • complexIReal) (mismatchEdgeSign δ (t 2) • complexIReal)
    (mismatchEdgeSign δ (t 3) • complexIReal) (p 0) (p 0) (p 1) (p 2) (p 3)

theorem mismatchPointLocusMap_surjective (δ : ℝ) (hδ : δ ^ 2 = 1)
    (t : Fin 4 → Bool) (ht : ∃ i, t i = true) :
    Function.Surjective (mismatchPointLocusMap (V := V) δ t) :=
  (mismatchLocusMap_surjective δ hδ t ht).comp independentEdgeMap_surjective

theorem mismatchPointLocus_finrank [FiniteDimensional ℂ V]
    (δ : ℝ) (hδ : δ ^ 2 = 1) (t : Fin 4 → Bool) (ht : ∃ i, t i = true) :
    Module.finrank ℂ (mismatchPointLocusMap (V := V) δ t).ker = 3 * Module.finrank ℂ V := by
  have hdim := (mismatchPointLocusMap (V := V) δ t).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (mismatchPointLocusMap_surjective δ hδ t ht),
    finrank_top, Module.finrank_pi_fintype] at hdim
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hdim
  omega

theorem mismatchLocus_real_finrank [FiniteDimensional ℂ V]
    (δ : ℝ) (hδ : δ ^ 2 = 1) (t : Fin 4 → Bool) (ht : ∃ i, t i = true) :
    Module.finrank ℝ (mismatchLocusMap (V := V) δ t).ker =
      4 * Module.finrank ℂ V := by
  rw [finrank_real_of_complex, mismatchLocus_finrank δ hδ t ht]
  omega

theorem mismatchLocus_real_codimension [FiniteDimensional ℂ V]
    (δ : ℝ) (hδ : δ ^ 2 = 1) (t : Fin 4 → Bool) (ht : ∃ i, t i = true) :
    Module.finrank ℝ (Fin 3 → V) -
      Module.finrank ℝ (mismatchLocusMap (V := V) δ t).ker = 2 * Module.finrank ℂ V := by
  rw [finrank_real_of_complex, mismatchLocus_real_finrank δ hδ t ht,
    Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  omega

end ComplexLoci

end

end VanAubelExtensions
