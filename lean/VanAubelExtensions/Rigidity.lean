/-
Copyright (c) 2026 mindofcharles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mindofcharles
-/

import VanAubelExtensions.Basic

/-!
# Universal operator classification and rigidity

Formal counterpart of
`paper/van-aubel-edge-operator-realizations-and-rigidity.md`.
-/

namespace VanAubelExtensions

noncomputable section

open scoped InnerProductSpace

section GeneralOperatorIdentity

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def operatorCenter (L : V →ₗ[ℝ] V) (X Y : V) : V :=
  (2 : ℝ)⁻¹ • (X + Y + L (Y - X))

def UniversalOperatorIdentity
    (K L₁ L₂ L₃ L₄ : V →ₗ[ℝ] V) : Prop :=
  ∀ A B C D,
    operatorCenter L₃ C D - operatorCenter L₁ A B =
      K (operatorCenter L₄ D A - operatorCenter L₂ B C)

theorem universalOperatorIdentity_of_parametrization
    (K N : V →ₗ[ℝ] V) (hK_sq : ∀ v, K (K v) = -v) :
    UniversalOperatorIdentity K
      (K - K.comp N) (K + N) (K + K.comp N) (K - N) := by
  intro A B C D
  simp only [operatorCenter, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.comp_apply, map_sub, map_add, map_smul, hK_sq]
  module

theorem universalOperatorIdentity_parametrization
    (K L₁ L₂ L₃ L₄ : V →ₗ[ℝ] V) (hK_sq : ∀ v, K (K v) = -v)
    (h : UniversalOperatorIdentity K L₁ L₂ L₃ L₄) :
    ∃! N : V →ₗ[ℝ] V,
      L₁ = K - K.comp N ∧ L₂ = K + N ∧
        L₃ = K + K.comp N ∧ L₄ = K - N := by
  let N := L₂ - K
  have hA (v : V) : -v + L₁ v = K v + K (L₄ v) := by
    have hv := congrArg (fun x : V => (2 : ℝ) • x) (h v 0 0 0)
    simp only [operatorCenter, map_zero, map_neg, map_smul, map_add, zero_add, add_zero,
      sub_zero, zero_sub, smul_zero] at hv
    calc
      -v + L₁ v = L₁ v + -v := by module
      _ = K v + K (L₄ v) := by simpa [smul_smul] using hv
  have hB (v : V) : -v - L₁ v = -K v + K (L₂ v) := by
    have hv := congrArg (fun x : V => (2 : ℝ) • x) (h 0 v 0 0)
    simp only [operatorCenter, map_zero, map_neg, map_smul, map_add, zero_add, add_zero,
      sub_zero, zero_sub, smul_zero] at hv
    calc
      -v - L₁ v = -L₁ v + -v := by module
      _ = K (L₂ v) + -K v := by simpa [smul_smul] using hv
      _ = -K v + K (L₂ v) := by module
  have hC (v : V) : L₃ v - v = K v + K (L₂ v) := by
    have hv := congrArg (fun x : V => (2 : ℝ) • x) (h 0 0 v 0)
    simp only [operatorCenter, map_zero, map_neg, map_smul, map_add, zero_add, add_zero,
      sub_zero, zero_sub, smul_zero] at hv
    have hv' : v - L₃ v = -K (L₂ v) - K v := by
      calc
        v - L₃ v = v + -L₃ v := by module
        _ = -K (L₂ v) + -K v := by simpa [smul_smul] using hv
        _ = -K (L₂ v) - K v := by module
    calc
      L₃ v - v = -(v - L₃ v) := by module
      _ = -(-K (L₂ v) - K v) := by rw [hv']
      _ = K v + K (L₂ v) := by module
  have hK_injective : Function.Injective K := by
    intro x y hxy
    have hxy' := congrArg K hxy
    simp only [hK_sq] at hxy'
    exact neg_injective hxy'
  have hsum (v : V) : L₂ v + L₄ v = (2 : ℝ) • K v := by
    have hKL₂ : K (L₂ v) = -v - L₁ v + K v := by
      calc
        K (L₂ v) = (-K v + K (L₂ v)) + K v := by module
        _ = (-v - L₁ v) + K v := by rw [← hB v]
    have hKL₄ : K (L₄ v) = -v + L₁ v - K v := by
      calc
        K (L₄ v) = (K v + K (L₄ v)) - K v := by module
        _ = (-v + L₁ v) - K v := by rw [← hA v]
    have hk : K (L₂ v + L₄ v) = -(2 : ℝ) • v := by
      calc
        K (L₂ v + L₄ v) = K (L₂ v) + K (L₄ v) := map_add K _ _
        _ = (-v - L₁ v + K v) + (-v + L₁ v - K v) := by rw [hKL₂, hKL₄]
        _ = -(2 : ℝ) • v := by module
    apply hK_injective
    calc
      K (L₂ v + L₄ v) = -(2 : ℝ) • v := hk
      _ = K ((2 : ℝ) • K v) := by rw [map_smul, hK_sq]; module
  have hL₄ : L₄ = K - N := by
    ext v
    dsimp [N]
    calc
      L₄ v = (L₂ v + L₄ v) - L₂ v := by module
      _ = (2 : ℝ) • K v - L₂ v := by rw [hsum v]
      _ = K v - (L₂ v - K v) := by module
  have hL₁ : L₁ = K - K.comp N := by
    ext v
    dsimp [N]
    simp only [map_sub]
    rw [hK_sq]
    calc
      L₁ v = -(-v - L₁ v) - v := by module
      _ = -(-K v + K (L₂ v)) - v := by rw [hB v]
      _ = K v - (K (L₂ v) - -v) := by module
  have hL₃ : L₃ = K + K.comp N := by
    ext v
    dsimp [N]
    simp only [map_sub]
    rw [hK_sq]
    calc
      L₃ v = (L₃ v - v) + v := by module
      _ = (K v + K (L₂ v)) + v := by rw [hC v]
      _ = K v + (K (L₂ v) - -v) := by module
  refine ⟨N, ⟨hL₁, ?_, hL₃, hL₄⟩, ?_⟩
  · ext v
    simp [N]
  · intro N' hN'
    rcases hN' with ⟨_, hL₂', _, _⟩
    apply LinearMap.ext
    intro v
    dsimp [N]
    calc
      N' v = (K + N') v - K v := by simp
      _ = L₂ v - K v := by rw [← hL₂']

theorem universalOperatorIdentity_iff_parametrized
    (K L₁ L₂ L₃ L₄ : V →ₗ[ℝ] V) (hK_sq : ∀ v, K (K v) = -v) :
    UniversalOperatorIdentity K L₁ L₂ L₃ L₄ ↔
      ∃ N : V →ₗ[ℝ] V,
        L₁ = K - K.comp N ∧ L₂ = K + N ∧
          L₃ = K + K.comp N ∧ L₄ = K - N := by
  constructor
  · intro h
    exact (universalOperatorIdentity_parametrization K L₁ L₂ L₃ L₄ hK_sq h).exists
  · rintro ⟨N, rfl, rfl, rfl, rfl⟩
    exact universalOperatorIdentity_of_parametrization K N hK_sq

/-- A real-linear complex structure, without any metric assumptions. -/
def IsLinearComplexStructure (L : V →ₗ[ℝ] V) : Prop :=
  ∀ v, L (L v) = -v

/-- The two perturbations `K + N` and `K - N` are both complex structures
exactly when `N` is square-zero and anticommutes with `K`. -/
theorem add_sub_are_complexStructures_iff
    (K N : V →ₗ[ℝ] V) (hK_sq : IsLinearComplexStructure K) :
    (IsLinearComplexStructure (K + N) ∧ IsLinearComplexStructure (K - N)) ↔
      (∀ v, N (N v) = 0) ∧ (∀ v, K (N v) + N (K v) = 0) := by
  constructor
  · rintro ⟨hplus, hminus⟩
    have hp (v : V) : K (N v) + N (K v) + N (N v) = 0 := by
      calc
        K (N v) + N (K v) + N (N v) = (K + N) ((K + N) v) + v := by
          simp only [LinearMap.add_apply, map_add]
          rw [hK_sq v]
          module
        _ = -v + v := by rw [hplus v]
        _ = 0 := by module
    have hm (v : V) : -K (N v) - N (K v) + N (N v) = 0 := by
      calc
        -K (N v) - N (K v) + N (N v) = (K - N) ((K - N) v) + v := by
          simp only [LinearMap.sub_apply, map_sub]
          rw [hK_sq v]
          module
        _ = -v + v := by rw [hminus v]
        _ = 0 := by module
    have hNN (v : V) : N (N v) = 0 := by
      have htwo : (2 : ℝ) • N (N v) = 0 := by
        calc
          (2 : ℝ) • N (N v) =
              (K (N v) + N (K v) + N (N v)) +
                (-K (N v) - N (K v) + N (N v)) := by module
          _ = 0 + 0 := by rw [hp v, hm v]
          _ = 0 := by module
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    refine ⟨hNN, ?_⟩
    intro v
    calc
      K (N v) + N (K v) = K (N v) + N (K v) + N (N v) := by rw [hNN]; module
      _ = 0 := hp v
  · rintro ⟨hNN, hanti⟩
    constructor
    · intro v
      calc
        (K + N) ((K + N) v) =
            -v + (K (N v) + N (K v)) + N (N v) := by
          simp only [LinearMap.add_apply, map_add]
          rw [hK_sq v]
          module
        _ = -v := by rw [hanti v, hNN v]; module
    · intro v
      calc
        (K - N) ((K - N) v) =
            -v - (K (N v) + N (K v)) + N (N v) := by
          simp only [LinearMap.sub_apply, map_sub]
          rw [hK_sq v]
          module
        _ = -v := by rw [hanti v, hNN v]; module

/-- Complete classification when every edge operator in the universal
identity is itself a complex structure. -/
theorem parametrized_all_complexStructures_iff
    (K N : V →ₗ[ℝ] V) (hK_sq : IsLinearComplexStructure K) :
    (IsLinearComplexStructure (K - K.comp N) ∧
        IsLinearComplexStructure (K + N) ∧
        IsLinearComplexStructure (K + K.comp N) ∧
        IsLinearComplexStructure (K - N)) ↔
      (∀ v, N (N v) = 0) ∧ (∀ v, K (N v) + N (K v) = 0) := by
  constructor
  · rintro ⟨_, hplus, _, hminus⟩
    exact (add_sub_are_complexStructures_iff K N hK_sq).mp ⟨hplus, hminus⟩
  · intro hN
    have hbase := (add_sub_are_complexStructures_iff K N hK_sq).mpr hN
    rcases hN with ⟨hNN, hanti⟩
    have hNKN (v : V) : N (K (N v)) = 0 := by
      have h := hanti (N v)
      rw [hNN] at h
      simpa using h
    have hKNK (v : V) : K (N (K v)) = N v := by
      have h := hanti (K v)
      have hz : K (N (K v)) - N v = 0 := by
        rw [hK_sq v, map_neg] at h
        simpa only [sub_eq_add_neg] using h
      exact sub_eq_zero.mp hz
    have hcomp_sq (v : V) : (K.comp N) ((K.comp N) v) = 0 := by
      simp [LinearMap.comp_apply, hNKN]
    have hcomp_anti (v : V) :
        K ((K.comp N) v) + (K.comp N) (K v) = 0 := by
      simp only [LinearMap.comp_apply]
      rw [hK_sq (N v), hKNK v]
      module
    have hcomp := (add_sub_are_complexStructures_iff K (K.comp N) hK_sq).mpr
      ⟨hcomp_sq, hcomp_anti⟩
    exact ⟨hcomp.2, hbase.1, hcomp.1, hbase.2⟩

end GeneralOperatorIdentity

section AffineOperatorIdentity

variable {V E : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V E]

/-- The center associated with a real-linear edge operator, defined without
choosing an origin in the affine space. -/
def affineOperatorCenter (L : V →ₗ[ℝ] V) (X Y : E) : E :=
  (2 : ℝ)⁻¹ • ((Y -ᵥ X) + L (Y -ᵥ X)) +ᵥ X

/-- Coordinates of an affine operator center relative to an arbitrary origin. -/
theorem affineOperatorCenter_vsub (L : V →ₗ[ℝ] V) (O X Y : E) :
    affineOperatorCenter L X Y -ᵥ O =
      operatorCenter L (X -ᵥ O) (Y -ᵥ O) := by
  simp only [affineOperatorCenter, vadd_vsub_assoc, operatorCenter]
  rw [← vsub_sub_vsub_cancel_right Y X O]
  module

/-- The universal edge-operator identity stated intrinsically in an affine
space. -/
def AffineUniversalOperatorIdentity
    (K L₁ L₂ L₃ L₄ : V →ₗ[ℝ] V) : Prop :=
  ∀ A B C D : E,
    affineOperatorCenter L₃ C D -ᵥ affineOperatorCenter L₁ A B =
      K (affineOperatorCenter L₄ D A -ᵥ affineOperatorCenter L₂ B C)

/-- Choosing any origin identifies the intrinsic affine identity with its
vector-coordinate version. -/
theorem affineUniversalOperatorIdentity_iff [Nonempty E]
    (K L₁ L₂ L₃ L₄ : V →ₗ[ℝ] V) :
    AffineUniversalOperatorIdentity (E := E) K L₁ L₂ L₃ L₄ ↔
      UniversalOperatorIdentity K L₁ L₂ L₃ L₄ := by
  let O : E := Classical.choice (inferInstance : Nonempty E)
  constructor
  · intro h A B C D
    have h' := h (A +ᵥ O) (B +ᵥ O) (C +ᵥ O) (D +ᵥ O)
    rw [← vsub_sub_vsub_cancel_right
      (affineOperatorCenter L₃ (C +ᵥ O) (D +ᵥ O))
      (affineOperatorCenter L₁ (A +ᵥ O) (B +ᵥ O)) O] at h'
    rw [← vsub_sub_vsub_cancel_right
      (affineOperatorCenter L₄ (D +ᵥ O) (A +ᵥ O))
      (affineOperatorCenter L₂ (B +ᵥ O) (C +ᵥ O)) O] at h'
    simpa only [affineOperatorCenter_vsub, vadd_vsub] using h'
  · intro h A B C D
    rw [← vsub_sub_vsub_cancel_right
      (affineOperatorCenter L₃ C D) (affineOperatorCenter L₁ A B) O]
    rw [← vsub_sub_vsub_cancel_right
      (affineOperatorCenter L₄ D A) (affineOperatorCenter L₂ B C) O]
    simp only [affineOperatorCenter_vsub]
    exact h (A -ᵥ O) (B -ᵥ O) (C -ᵥ O) (D -ᵥ O)

/-- Complete affine-space classification of universal edge-operator
realizations. -/
theorem affineUniversalOperatorIdentity_iff_parametrized [Nonempty E]
    (K L₁ L₂ L₃ L₄ : V →ₗ[ℝ] V) (hK_sq : ∀ v, K (K v) = -v) :
    AffineUniversalOperatorIdentity (E := E) K L₁ L₂ L₃ L₄ ↔
      ∃ N : V →ₗ[ℝ] V,
        L₁ = K - K.comp N ∧ L₂ = K + N ∧
          L₃ = K + K.comp N ∧ L₄ = K - N := by
  rw [affineUniversalOperatorIdentity_iff]
  exact universalOperatorIdentity_iff_parametrized K L₁ L₂ L₃ L₄ hK_sq

/-- The affine classification parameter is unique. -/
theorem affineUniversalOperatorIdentity_parametrization [Nonempty E]
    (K L₁ L₂ L₃ L₄ : V →ₗ[ℝ] V) (hK_sq : ∀ v, K (K v) = -v)
    (h : AffineUniversalOperatorIdentity (E := E) K L₁ L₂ L₃ L₄) :
    ∃! N : V →ₗ[ℝ] V,
      L₁ = K - K.comp N ∧ L₂ = K + N ∧
        L₃ = K + K.comp N ∧ L₄ = K - N :=
  universalOperatorIdentity_parametrization K L₁ L₂ L₃ L₄ hK_sq
    ((affineUniversalOperatorIdentity_iff K L₁ L₂ L₃ L₄).mp h)

end AffineOperatorIdentity

section DimensionTwoRigidity

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A square-zero real-linear map anticommuting with a complex structure
vanishes in real dimension two.  This is the sharp low-dimensional rigidity
input and uses no inner product. -/
theorem squareZero_anticommuting_eq_zero_of_finrank_two
    (hdim : Module.finrank ℝ V = 2)
    (K N : V →ₗ[ℝ] V) (hK_sq : IsLinearComplexStructure K)
    (hNN : ∀ v, N (N v) = 0)
    (hanti : ∀ v, K (N v) + N (K v) = 0) :
    N = 0 := by
  by_contra hN
  have hex : ∃ v : V, N v ≠ 0 := by
    apply Classical.byContradiction
    intro h
    apply hN
    ext v
    by_contra hv
    exact h ⟨v, hv⟩
  obtain ⟨v, hv⟩ := hex
  let w := N v
  have hw : w ≠ 0 := hv
  have hKw : K w ≠ 0 := by
    intro hz
    have hz' := congrArg K hz
    rw [hK_sq w, map_zero] at hz'
    exact hw (neg_eq_zero.mp hz')
  have hli : LinearIndependent ℝ ![w, K w] := by
    rw [linearIndependent_fin2]
    refine ⟨hKw, ?_⟩
    intro a ha
    have ha' : a • K w = w := by simpa using ha
    have hKa := congrArg K ha'
    simp only [map_smul] at hKa
    rw [hK_sq w] at hKa
    have haw : a • w = -K w := by
      calc
        a • w = -(a • (-w)) := by module
        _ = -K w := by rw [hKa]
    have hzero : (a ^ 2 + 1) • w = 0 := by
      calc
        (a ^ 2 + 1) • w = a • (a • w) + w := by module
        _ = a • (-K w) + w := by rw [haw]
        _ = -(a • K w) + w := by module
        _ = -w + w := by rw [ha']
        _ = 0 := by module
    have hcoeff : a ^ 2 + 1 ≠ 0 := by nlinarith [sq_nonneg a]
    exact hw ((smul_eq_zero.mp hzero).resolve_left hcoeff)
  have hspan : Submodule.span ℝ (Set.range ![w, K w]) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank
    simp [hdim]
  have hwker : w ∈ N.ker := by
    change N w = 0
    exact hNN v
  have hKwker : K w ∈ N.ker := by
    change N (K w) = 0
    have h := hanti w
    rw [show N w = 0 from hNN v, map_zero, zero_add] at h
    exact h
  have hle : Submodule.span ℝ (Set.range ![w, K w]) ≤ N.ker := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact hwker
    · exact hKwker
  have hker : N.ker = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact hle
  exact hN ((LinearMap.ker_eq_top).mp hker)

/-- Every universal realization by four complex structures is trivial in
real dimension two, even without orthogonality. -/
theorem universalOperatorIdentity_rigidity_of_finrank_two
    (hdim : Module.finrank ℝ V = 2)
    (K L₁ L₂ L₃ L₄ : V →ₗ[ℝ] V)
    (hK_sq : IsLinearComplexStructure K)
    (hL₁_sq : IsLinearComplexStructure L₁)
    (hL₂_sq : IsLinearComplexStructure L₂)
    (hL₃_sq : IsLinearComplexStructure L₃)
    (hL₄_sq : IsLinearComplexStructure L₄)
    (h : UniversalOperatorIdentity K L₁ L₂ L₃ L₄) :
    L₁ = K ∧ L₂ = K ∧ L₃ = K ∧ L₄ = K := by
  obtain ⟨N, hL₁, hL₂, hL₃, hL₄⟩ :=
    (universalOperatorIdentity_parametrization K L₁ L₂ L₃ L₄ hK_sq h).exists
  have hall :
      IsLinearComplexStructure (K - K.comp N) ∧
        IsLinearComplexStructure (K + N) ∧
        IsLinearComplexStructure (K + K.comp N) ∧
        IsLinearComplexStructure (K - N) := by
    rw [← hL₁, ← hL₂, ← hL₃, ← hL₄]
    exact ⟨hL₁_sq, hL₂_sq, hL₃_sq, hL₄_sq⟩
  obtain ⟨hNN, hanti⟩ :=
    (parametrized_all_complexStructures_iff K N hK_sq).mp hall
  have hN := squareZero_anticommuting_eq_zero_of_finrank_two
    hdim K N hK_sq hNN hanti
  subst N
  simpa using And.intro hL₁ (And.intro hL₂ (And.intro hL₃ hL₄))

/-- Intrinsic affine-space form of dimension-two rigidity. -/
theorem affineUniversalOperatorIdentity_rigidity_of_finrank_two
    {E : Type*} [AddTorsor V E] [Nonempty E]
    (hdim : Module.finrank ℝ V = 2)
    (K L₁ L₂ L₃ L₄ : V →ₗ[ℝ] V)
    (hK_sq : IsLinearComplexStructure K)
    (hL₁_sq : IsLinearComplexStructure L₁)
    (hL₂_sq : IsLinearComplexStructure L₂)
    (hL₃_sq : IsLinearComplexStructure L₃)
    (hL₄_sq : IsLinearComplexStructure L₄)
    (h : AffineUniversalOperatorIdentity (E := E) K L₁ L₂ L₃ L₄) :
    L₁ = K ∧ L₂ = K ∧ L₃ = K ∧ L₄ = K :=
  universalOperatorIdentity_rigidity_of_finrank_two hdim K L₁ L₂ L₃ L₄
    hK_sq hL₁_sq hL₂_sq hL₃_sq hL₄_sq
    ((affineUniversalOperatorIdentity_iff K L₁ L₂ L₃ L₄).mp h)

end DimensionTwoRigidity

section OperatorRigidity

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- If all four edge complex structures are orthogonal, the universal
four-operator identity is rigid: every edge operator is the target operator. -/
theorem orthogonalOperatorIdentity_rigidity
    (K L₁ L₂ L₃ L₄ : OrthogonalComplexStructure W)
    (h : UniversalOperatorIdentity K.toLinearMap L₁.toLinearMap L₂.toLinearMap
      L₃.toLinearMap L₄.toLinearMap) :
    L₁.toLinearMap = K.toLinearMap ∧ L₂.toLinearMap = K.toLinearMap ∧
      L₃.toLinearMap = K.toLinearMap ∧ L₄.toLinearMap = K.toLinearMap := by
  obtain ⟨N, hL₁, hL₂, hL₃, hL₄⟩ :=
    (universalOperatorIdentity_parametrization K.toLinearMap L₁.toLinearMap
      L₂.toLinearMap L₃.toLinearMap L₄.toLinearMap K.sq_apply h).exists
  have hN : N = 0 := by
    ext v
    have hplus : ‖K v + N v‖ = ‖v‖ := by
      change ‖(K.toLinearMap + N) v‖ = ‖v‖
      rw [← hL₂]
      exact L₂.norm_map v
    have hminus : ‖K v - N v‖ = ‖v‖ := by
      change ‖(K.toLinearMap - N) v‖ = ‖v‖
      rw [← hL₄]
      exact L₄.norm_map v
    have hpara := parallelogram_law_with_norm ℝ (K v) (N v)
    rw [hplus, hminus, K.norm_map] at hpara
    have hnorm : ‖N v‖ = 0 := by
      nlinarith [sq_nonneg ‖N v‖, norm_nonneg (N v)]
    exact norm_eq_zero.mp hnorm
  subst N
  have hcomp_zero : K.toLinearMap.comp (0 : W →ₗ[ℝ] W) = 0 := by
    ext v
    simp
  rw [hcomp_zero] at hL₁ hL₃
  exact ⟨hL₁.trans (sub_zero _), hL₂.trans (add_zero _),
    hL₃.trans (add_zero _), hL₄.trans (sub_zero _)⟩

end OperatorRigidity

section SignRigidity

variable {U : Type*} [AddCommGroup U] [Module ℝ U] [Nontrivial U]

/-- On a nonzero real vector space, independent signs on the four edges cannot
satisfy the target signed Van Aubel identity universally: all signs must agree
with the target sign. -/
theorem universalOperatorIdentity_sign_rigidity
    (J : U →ₗ[ℝ] U) (hJ_sq : ∀ v, J (J v) = -v)
    (δ ε₁ ε₂ ε₃ ε₄ : ℝ)
    (hδ : δ ^ 2 = 1) (_hε₁ : ε₁ ^ 2 = 1) (hε₂ : ε₂ ^ 2 = 1)
    (_hε₃ : ε₃ ^ 2 = 1) (hε₄ : ε₄ ^ 2 = 1)
    (h : UniversalOperatorIdentity (δ • J) (ε₁ • J) (ε₂ • J) (ε₃ • J) (ε₄ • J)) :
    ε₁ = δ ∧ ε₂ = δ ∧ ε₃ = δ ∧ ε₄ = δ := by
  have hK_sq : ∀ v, (δ • J) ((δ • J) v) = -v := by
    rcases sq_eq_one_iff.mp hδ with rfl | rfl <;>
      simp [hJ_sq]
  obtain ⟨N, hL₁, hL₂, hL₃, hL₄⟩ :=
    (universalOperatorIdentity_parametrization (δ • J) (ε₁ • J) (ε₂ • J)
      (ε₃ • J) (ε₄ • J) hK_sq h).exists
  obtain ⟨v, hv⟩ := exists_ne (0 : U)
  have hJv : J v ≠ 0 := by
    intro hz
    have hz' := congrArg J hz
    rw [hJ_sq v, map_zero] at hz'
    exact hv (neg_eq_zero.mp hz')
  have hNv : N v = (ε₂ - δ) • J v := by
    have heq := LinearMap.congr_fun hL₂ v
    simp only [LinearMap.smul_apply, LinearMap.add_apply] at heq
    calc
      N v = (δ • J v + N v) - δ • J v := by module
      _ = ε₂ • J v - δ • J v := by rw [← heq]
      _ = (ε₂ - δ) • J v := by module
  have hsignVector : ε₄ • J v = (2 * δ - ε₂) • J v := by
    have heq := LinearMap.congr_fun hL₄ v
    simp only [LinearMap.smul_apply, LinearMap.sub_apply] at heq
    calc
      ε₄ • J v = δ • J v - N v := heq
      _ = δ • J v - (ε₂ - δ) • J v := by rw [hNv]
      _ = (2 * δ - ε₂) • J v := by module
  have hsign : ε₄ = 2 * δ - ε₂ :=
    smul_left_injective ℝ hJv hsignVector
  have hε₂δ : ε₂ = δ := by
    rcases sq_eq_one_iff.mp hδ with rfl | rfl <;>
      rcases sq_eq_one_iff.mp hε₂ with rfl | rfl
    · rfl
    · norm_num at hsign
      nlinarith [hε₄]
    · norm_num at hsign
      nlinarith [hε₄]
    · rfl
  have hNzero : N = 0 := by
    have hmaps : (δ • J) + N = (δ • J) + 0 := by
      simpa [hε₂δ] using hL₂.symm
    exact add_left_cancel hmaps
  subst N
  have hcomp_zero : (δ • J).comp (0 : U →ₗ[ℝ] U) = 0 := by
    ext w
    simp
  rw [hcomp_zero] at hL₁ hL₃
  have hmap₁ : ε₁ • J = δ • J := hL₁.trans (sub_zero _)
  have hmap₃ : ε₃ • J = δ • J := hL₃.trans (add_zero _)
  have hmap₄ : ε₄ • J = δ • J := hL₄.trans (sub_zero _)
  have scalar_eq_of_map_eq {a b : ℝ} (hab : a • J = b • J) : a = b := by
    apply smul_left_injective ℝ hJv
    simpa only [LinearMap.smul_apply] using LinearMap.congr_fun hab v
  exact ⟨scalar_eq_of_map_eq hmap₁, hε₂δ,
    scalar_eq_of_map_eq hmap₃, scalar_eq_of_map_eq hmap₄⟩

/-- Full if-and-only-if form of independent-sign rigidity. -/
theorem universalOperatorIdentity_sign_iff
    (J : U →ₗ[ℝ] U) (hJ_sq : ∀ v, J (J v) = -v)
    (δ ε₁ ε₂ ε₃ ε₄ : ℝ)
    (hδ : δ ^ 2 = 1) (hε₁ : ε₁ ^ 2 = 1) (hε₂ : ε₂ ^ 2 = 1)
    (hε₃ : ε₃ ^ 2 = 1) (hε₄ : ε₄ ^ 2 = 1) :
    UniversalOperatorIdentity (δ • J) (ε₁ • J) (ε₂ • J) (ε₃ • J) (ε₄ • J) ↔
      ε₁ = δ ∧ ε₂ = δ ∧ ε₃ = δ ∧ ε₄ = δ := by
  constructor
  · intro h
    exact universalOperatorIdentity_sign_rigidity J hJ_sq δ ε₁ ε₂ ε₃ ε₄
      hδ hε₁ hε₂ hε₃ hε₄ h
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    subst ε₁
    subst ε₂
    subst ε₃
    subst ε₄
    have hK_sq : ∀ v, (δ • J) ((δ • J) v) = -v := by
      rcases sq_eq_one_iff.mp hδ with rfl | rfl <;>
        simp [hJ_sq]
    simpa using universalOperatorIdentity_of_parametrization
      (δ • J) (0 : U →ₗ[ℝ] U) hK_sq

end SignRigidity

end

end VanAubelExtensions
