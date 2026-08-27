/-
Copyright (c) 2026 mindofcharles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mindofcharles
-/

import VanAubelExtensions.ComplexAffineTransfer

/-!
# Square geometry and metric consequences

Part of the formalization of `paper/van-aubel-complex-structure-identity.md`.
-/

namespace VanAubelExtensions

noncomputable section

open scoped InnerProductSpace

section SquareConstruction

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [AddTorsor V E]

/-- Four ordered vertices used by the edge construction.  The structure stores
the vertices; the square properties follow separately from orthogonality of
`J` and the condition `ε² = 1`. -/
@[ext]
structure EdgeSquare (E : Type*) where
  first : E
  second : E
  third : E
  fourth : E

/-- Apply a function to all four vertices of an edge square. -/
def EdgeSquare.map {E F : Type*} (f : E → F) (s : EdgeSquare E) : EdgeSquare F :=
  ⟨f s.first, f s.second, f s.third, f s.fourth⟩

@[simp]
theorem EdgeSquare.map_first {E F : Type*} (f : E → F) (s : EdgeSquare E) :
    (s.map f).first = f s.first := rfl

@[simp]
theorem EdgeSquare.map_second {E F : Type*} (f : E → F) (s : EdgeSquare E) :
    (s.map f).second = f s.second := rfl

@[simp]
theorem EdgeSquare.map_third {E F : Type*} (f : E → F) (s : EdgeSquare E) :
    (s.map f).third = f s.third := rfl

@[simp]
theorem EdgeSquare.map_fourth {E F : Type*} (f : E → F) (s : EdgeSquare E) :
    (s.map f).fourth = f s.fourth := rfl

/-- The edge parallelogram determined by `ε J` on `X ⟶ Y`.  If `ε² = 1`, the
orthogonality of `J` makes it a square, including the degenerate case `X = Y`. -/
def squareOnEdge (J : OrthogonalComplexStructure V) (ε : ℝ) (X Y : E) : EdgeSquare E where
  first := X
  second := Y
  third := ε • J (Y -ᵥ X) +ᵥ Y
  fourth := ε • J (Y -ᵥ X) +ᵥ X

/-- The zero-size square at a point. -/
def degenerateSquare (X : E) : EdgeSquare E := ⟨X, X, X, X⟩

/-- The two-dimensional direction space selected by an edge and `J`. -/
def squareDirectionPlane (J : OrthogonalComplexStructure V) (ε : ℝ) (X Y : E) :
    Submodule ℝ V :=
  Submodule.span ℝ (Set.range ![Y -ᵥ X, ε • J (Y -ᵥ X)])

@[simp]
theorem squareOnEdge_first (J : OrthogonalComplexStructure V) (ε : ℝ) (X Y : E) :
    (squareOnEdge J ε X Y).first = X := rfl

@[simp]
theorem squareOnEdge_second (J : OrthogonalComplexStructure V) (ε : ℝ) (X Y : E) :
    (squareOnEdge J ε X Y).second = Y := rfl

@[simp]
theorem squareOnEdge_third_vsub_second (J : OrthogonalComplexStructure V)
    (ε : ℝ) (X Y : E) :
    (squareOnEdge J ε X Y).third -ᵥ (squareOnEdge J ε X Y).second =
      ε • J (Y -ᵥ X) := by
  simp [squareOnEdge]

@[simp]
theorem squareOnEdge_fourth_vsub_first (J : OrthogonalComplexStructure V)
    (ε : ℝ) (X Y : E) :
    (squareOnEdge J ε X Y).fourth -ᵥ (squareOnEdge J ε X Y).first =
      ε • J (Y -ᵥ X) := by
  simp [squareOnEdge]

@[simp]
theorem squareOnEdge_third_vsub_fourth (J : OrthogonalComplexStructure V)
    (ε : ℝ) (X Y : E) :
    (squareOnEdge J ε X Y).third -ᵥ (squareOnEdge J ε X Y).fourth = Y -ᵥ X := by
  simp [squareOnEdge]

/-- The two adjacent side vectors have equal length. -/
theorem squareOnEdge_adjacent_norm_eq (J : OrthogonalComplexStructure V)
    (ε : ℝ) (hε_sq : ε ^ 2 = 1) (X Y : E) :
    ‖(squareOnEdge J ε X Y).third -ᵥ (squareOnEdge J ε X Y).second‖ = ‖Y -ᵥ X‖ := by
  rw [squareOnEdge_third_vsub_second, norm_smul, J.norm_map]
  rcases sq_eq_one_iff.mp hε_sq with rfl | rfl <;> simp

/-- The two adjacent side vectors are orthogonal. -/
theorem squareOnEdge_adjacent_inner_eq_zero (J : OrthogonalComplexStructure V)
    (ε : ℝ) (X Y : E) :
    ⟪Y -ᵥ X, (squareOnEdge J ε X Y).third -ᵥ
      (squareOnEdge J ε X Y).second⟫_ℝ = 0 := by
  rw [squareOnEdge_third_vsub_second, real_inner_smul_right, real_inner_comm]
  rw [J.inner_map_self_eq_zero]
  simp

/-- For a nonzero edge, its direction and the rotated direction are linearly
independent.  Hence the square lies in a genuine two-dimensional direction
plane. -/
theorem squareDirections_linearIndependent (J : OrthogonalComplexStructure V)
    (ε : ℝ) (hε_sq : ε ^ 2 = 1) {u : V} (hu : u ≠ 0) :
    LinearIndependent ℝ ![u, ε • J u] := by
  apply linearIndependent_of_ne_zero_of_inner_eq_zero
  · intro i
    fin_cases i
    · simpa using hu
    · exact smul_ne_zero (by nlinarith [hε_sq]) (J.map_ne_zero hu)
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [real_inner_smul_left, real_inner_smul_right, J.inner_map_self_eq_zero,
        J.inner_self_map_eq_zero]

/-- The direction plane of a nondegenerate edge-square has dimension two. -/
theorem squareDirectionPlane_finrank_eq_two (J : OrthogonalComplexStructure V)
    (ε : ℝ) (hε_sq : ε ^ 2 = 1) {u : V} (hu : u ≠ 0) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range ![u, ε • J u])) = 2 := by
  rw [finrank_span_eq_card (squareDirections_linearIndependent J ε hε_sq hu)]
  simp

/-- Every vertex of the constructed square lies in the affine translate of
its direction plane through `X`. -/
theorem squareOnEdge_vertices_mem_directionPlane (J : OrthogonalComplexStructure V)
    (ε : ℝ) (X Y : E) :
    (squareOnEdge J ε X Y).first -ᵥ X ∈ squareDirectionPlane J ε X Y ∧
      (squareOnEdge J ε X Y).second -ᵥ X ∈ squareDirectionPlane J ε X Y ∧
      (squareOnEdge J ε X Y).third -ᵥ X ∈ squareDirectionPlane J ε X Y ∧
      (squareOnEdge J ε X Y).fourth -ᵥ X ∈ squareDirectionPlane J ε X Y := by
  let u := Y -ᵥ X
  let v := ε • J u
  have hu : u ∈ squareDirectionPlane J ε X Y := by
    apply Submodule.subset_span
    exact ⟨0, by simp [u]⟩
  have hv : v ∈ squareDirectionPlane J ε X Y := by
    apply Submodule.subset_span
    exact ⟨1, by simp [u, v]⟩
  constructor
  · simp [squareOnEdge]
  constructor
  · simpa [u] using hu
  constructor
  · simpa [squareOnEdge, vadd_vsub_assoc, u, v, add_comm] using
      (squareDirectionPlane J ε X Y).add_mem hv hu
  · simpa [squareOnEdge, u, v] using hv

/-- A zero-length edge produces four coincident vertices. -/
theorem squareOnEdge_zero (J : OrthogonalComplexStructure V) (ε : ℝ) (X : E) :
    squareOnEdge J ε X X = degenerateSquare X := by
  ext <;> simp [squareOnEdge, degenerateSquare]

/-- A complex-affine map carries the four vertices of the constructed
`J`-edge configuration to the corresponding `K`-configuration.  Under the
signed square hypotheses, the target square may be degenerate. -/
theorem squareOnEdge_natural
    {W F : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [AddTorsor W F]
    (J : OrthogonalComplexStructure V) (K : OrthogonalComplexStructure W)
    (f : E →ᵃ[ℝ] F)
    (hTJ : ∀ v, f.linear (J v) = K (f.linear v))
    (ε : ℝ) (X Y : E) :
    (squareOnEdge J ε X Y).map f = squareOnEdge K ε (f X) (f Y) := by
  ext <;> simp only [EdgeSquare.map, squareOnEdge]
  all_goals rw [f.map_vadd, map_smul, hTJ, f.linearMap_vsub]

/-- If the linear part kills the edge direction, the transported square
collapses to one point. -/
theorem squareOnEdge_natural_degenerate_of_linear_vsub_eq_zero
    {W F : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [AddTorsor W F]
    (J : OrthogonalComplexStructure V) (K : OrthogonalComplexStructure W)
    (f : E →ᵃ[ℝ] F)
    (hTJ : ∀ v, f.linear (J v) = K (f.linear v))
    (ε : ℝ) (X Y : E) (hzero : f.linear (Y -ᵥ X) = 0) :
    (squareOnEdge J ε X Y).map f = degenerateSquare (f X) := by
  rw [squareOnEdge_natural J K f hTJ]
  have hXY : f Y = f X := by
    rw [← vsub_eq_zero_iff_eq]
    rw [← f.linearMap_vsub]
    exact hzero
  rw [hXY, squareOnEdge_zero]

/-- If the transported edge direction is nonzero, the target square lies in
a genuine two-dimensional `K`-direction plane. -/
theorem squareOnEdge_natural_directionPlane_finrank_eq_two
    {W F : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [AddTorsor W F]
    (K : OrthogonalComplexStructure W) (f : E →ᵃ[ℝ] F)
    (ε : ℝ) (hε_sq : ε ^ 2 = 1) (X Y : E)
    (hnonzero : f.linear (Y -ᵥ X) ≠ 0) :
    Module.finrank ℝ
      (squareDirectionPlane K ε (f X) (f Y)) = 2 := by
  apply squareDirectionPlane_finrank_eq_two K ε hε_sq
  rw [← f.linearMap_vsub]
  exact hnonzero

/-- The center formula is the midpoint of the first and third vertices. -/
theorem affineSquareCenter_eq_diagonalMidpoint (J : OrthogonalComplexStructure V)
    (ε : ℝ) (X Y : E) :
    affineSquareCenter J.toLinearMap ε X Y =
      (2 : ℝ)⁻¹ • ((squareOnEdge J ε X Y).third -ᵥ X) +ᵥ X := by
  simp only [affineSquareCenter, squareOnEdge, vadd_vsub_assoc]
  rw [vadd_right_cancel_iff]
  change (2 : ℝ)⁻¹ • ((Y -ᵥ X) + ε • J (Y -ᵥ X)) =
    (2 : ℝ)⁻¹ • (ε • J (Y -ᵥ X) + (Y -ᵥ X))
  module

end SquareConstruction

section MetricConsequences

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [AddTorsor V E]

/-- An orthogonal complex structure sends every vector to an orthogonal
vector. -/
theorem inner_map_self_eq_zero (J : V →ₗᵢ[ℝ] V) (hJ_sq : ∀ v, J (J v) = -v)
    (v : V) : ⟪J v, v⟫_ℝ = 0 := by
  have hneg : ⟪J v, v⟫_ℝ = -⟪J v, v⟫_ℝ := by
    calc
      ⟪J v, v⟫_ℝ = ⟪J v, -J (J v)⟫_ℝ := by rw [hJ_sq]; simp
      _ = -⟪J v, J (J v)⟫_ℝ := by simp
      _ = -⟪v, J v⟫_ℝ := by rw [J.inner_map_map]
      _ = -⟪J v, v⟫_ℝ := by rw [real_inner_comm]
  linarith

/-- The opposite-center vectors have equal norms. -/
theorem oppositeCentersNormEq (J : V →ₗᵢ[ℝ] V) (hJ_sq : ∀ v, J (J v) = -v)
    (ε : ℝ) (hε_sq : ε ^ 2 = 1) (A B C D : E) :
    ‖affineSquareCenter J.toLinearMap ε C D -ᵥ affineSquareCenter J.toLinearMap ε A B‖ =
      ‖affineSquareCenter J.toLinearMap ε D A -ᵥ affineSquareCenter J.toLinearMap ε B C‖ := by
  rw [affineVanAubelIdentity J.toLinearMap hJ_sq ε hε_sq]
  rcases sq_eq_one_iff.mp hε_sq with rfl | rfl <;> simp

/-- The opposite-center vectors are orthogonal. -/
theorem oppositeCentersInnerEqZero (J : V →ₗᵢ[ℝ] V)
    (hJ_sq : ∀ v, J (J v) = -v) (ε : ℝ) (hε_sq : ε ^ 2 = 1)
    (A B C D : E) :
    ⟪affineSquareCenter J.toLinearMap ε C D -ᵥ affineSquareCenter J.toLinearMap ε A B,
      affineSquareCenter J.toLinearMap ε D A -ᵥ affineSquareCenter J.toLinearMap ε B C⟫_ℝ = 0 := by
  rw [affineVanAubelIdentity J.toLinearMap hJ_sq ε hε_sq]
  rw [real_inner_smul_left]
  change ε * ⟪J _, _⟫_ℝ = 0
  rw [inner_map_self_eq_zero J hJ_sq]
  simp

/-- The two opposite-center vectors vanish simultaneously. -/
theorem oppositeCenters_eq_zero_iff (J : V →ₗᵢ[ℝ] V)
    (hJ_sq : ∀ v, J (J v) = -v) (ε : ℝ) (hε_sq : ε ^ 2 = 1)
    (A B C D : E) :
    affineSquareCenter J.toLinearMap ε C D -ᵥ affineSquareCenter J.toLinearMap ε A B = 0 ↔
      affineSquareCenter J.toLinearMap ε D A -ᵥ affineSquareCenter J.toLinearMap ε B C = 0 := by
  constructor
  · intro hpr
    apply norm_eq_zero.mp
    rw [← oppositeCentersNormEq J hJ_sq ε hε_sq A B C D, hpr, norm_zero]
  · intro hqs
    apply norm_eq_zero.mp
    rw [oppositeCentersNormEq J hJ_sq ε hε_sq A B C D, hqs, norm_zero]

/-- The three conclusions of Van Aubel's theorem, packaged together. -/
structure VanAubelConclusion (J : OrthogonalComplexStructure V) (ε : ℝ)
    (P Q R S : E) : Prop where
  identity : R -ᵥ P = ε • J (S -ᵥ Q)
  equal_norms : ‖R -ᵥ P‖ = ‖S -ᵥ Q‖
  orthogonal : ⟪R -ᵥ P, S -ᵥ Q⟫_ℝ = 0

/-- Full Van Aubel theorem in a real Hermitian affine space. -/
theorem vanAubelTheorem (J : OrthogonalComplexStructure V)
    (ε : ℝ) (hε_sq : ε ^ 2 = 1) (A B C D : E) :
    VanAubelConclusion J ε
      (affineSquareCenter J.toLinearMap ε A B)
      (affineSquareCenter J.toLinearMap ε B C)
      (affineSquareCenter J.toLinearMap ε C D)
      (affineSquareCenter J.toLinearMap ε D A) := by
  constructor
  · exact affineVanAubelIdentity J.toLinearMap J.sq_apply ε hε_sq A B C D
  · exact oppositeCentersNormEq J.toLinearIsometry J.sq_apply ε hε_sq A B C D
  · exact oppositeCentersInnerEqZero J.toLinearIsometry J.sq_apply ε hε_sq A B C D

end MetricConsequences

section MetricTransport

variable {V W E F : Type*}
  [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [AddTorsor V E] [AddTorsor W F]

/-- Pointwise algebraic naturality, followed by orthogonality of the target
complex structure, re-realizes equal length and perpendicularity in the
target.  It does not compare either target length with a source length. -/
theorem affineVanAubelIdentity_natural_target_metric
    (J : V →ₗ[ℝ] V) (K : OrthogonalComplexStructure W)
    (f : E →ᵃ[ℝ] F)
    (hTJ : ∀ v, f.linear (J v) = K (f.linear v))
    (ε : ℝ) (hε_sq : ε ^ 2 = 1) (A B C D : E)
    (hsource :
      affineSquareCenter J ε C D -ᵥ affineSquareCenter J ε A B =
        ε • J (affineSquareCenter J ε D A -ᵥ affineSquareCenter J ε B C)) :
    let u := affineSquareCenter K.toLinearMap ε (f C) (f D) -ᵥ
      affineSquareCenter K.toLinearMap ε (f A) (f B)
    let v := affineSquareCenter K.toLinearMap ε (f D) (f A) -ᵥ
      affineSquareCenter K.toLinearMap ε (f B) (f C)
    ‖u‖ = ‖v‖ ∧ ⟪u, v⟫_ℝ = 0 := by
  dsimp only
  have hrel := affineVanAubelIdentity_natural J K.toLinearMap f hTJ ε A B C D hsource
  constructor
  · rw [hrel, norm_smul]
    change ‖ε‖ * ‖K _‖ = ‖_‖
    rw [K.norm_map]
    rcases sq_eq_one_iff.mp hε_sq with rfl | rfl <;> simp
  · rw [hrel, real_inner_smul_left]
    change ε * ⟪K _, _⟫_ℝ = 0
    rw [K.inner_map_self_eq_zero]
    simp

end MetricTransport

section IsometricTransport

variable {V W E F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- An affine map preserves all pairwise distances exactly when its linear
part preserves the norm of every displacement vector. -/
theorem affineMap_preserves_dist_iff_linear_preserves_norm
    [PseudoMetricSpace E] [NormedAddTorsor V E]
    [PseudoMetricSpace F] [NormedAddTorsor W F] [Nonempty E]
    (f : E →ᵃ[ℝ] F) :
    (∀ X Y : E, dist (f X) (f Y) = dist X Y) ↔
      ∀ v : V, ‖f.linear v‖ = ‖v‖ := by
  constructor
  · intro h v
    let O : E := Classical.choice (inferInstance : Nonempty E)
    calc
      ‖f.linear v‖ = ‖f (v +ᵥ O) -ᵥ f O‖ := by
        rw [← f.linearMap_vsub, vadd_vsub]
      _ = dist (f (v +ᵥ O)) (f O) := (dist_eq_norm_vsub W _ _).symm
      _ = dist (v +ᵥ O) O := h _ _
      _ = ‖(v +ᵥ O) -ᵥ O‖ := dist_eq_norm_vsub V _ _
      _ = ‖v‖ := by rw [vadd_vsub]
  · intro h X Y
    calc
      dist (f X) (f Y) = ‖f X -ᵥ f Y‖ := dist_eq_norm_vsub W _ _
      _ = ‖f.linear (X -ᵥ Y)‖ := by rw [f.linearMap_vsub]
      _ = ‖X -ᵥ Y‖ := h _
      _ = dist X Y := (dist_eq_norm_vsub V _ _).symm

/-- If the linear part is represented by a linear isometry, the affine map
preserves all pairwise distances. -/
theorem affineMap_dist_eq_of_linearIsometry
    [PseudoMetricSpace E] [NormedAddTorsor V E]
    [PseudoMetricSpace F] [NormedAddTorsor W F]
    (f : E →ᵃ[ℝ] F) (T : V →ₗᵢ[ℝ] W)
    (hlinear : f.linear = T.toLinearMap) (X Y : E) :
    dist (f X) (f Y) = dist X Y := by
  calc
    dist (f X) (f Y) = ‖f X -ᵥ f Y‖ := dist_eq_norm_vsub W _ _
    _ = ‖f.linear (X -ᵥ Y)‖ := by rw [f.linearMap_vsub]
    _ = ‖X -ᵥ Y‖ := by
      rw [hlinear]
      change ‖T (X -ᵥ Y)‖ = ‖X -ᵥ Y‖
      exact T.norm_map _
    _ = dist X Y := (dist_eq_norm_vsub V _ _).symm

/-- Real polarization: a real-linear norm-preserving map preserves every
inner product. -/
theorem linearMap_inner_map_map_of_norm_map
    (T : V →ₗ[ℝ] W) (hnorm : ∀ v, ‖T v‖ = ‖v‖) (x y : V) :
    ⟪T x, T y⟫_ℝ = ⟪x, y⟫_ℝ := by
  rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    hnorm x, hnorm y]
  rw [← map_sub, hnorm (x - y)]

/-- Consequently, the norm criterion for an affine isometric embedding also
preserves all inner products of displacement vectors. -/
theorem affineMap_displacement_inner_eq_of_linear_norm_map
    [AddTorsor V E] [AddTorsor W F]
    (f : E →ᵃ[ℝ] F) (hnorm : ∀ v, ‖f.linear v‖ = ‖v‖)
    (X Y Z : E) :
    ⟪f X -ᵥ f Y, f Z -ᵥ f Y⟫_ℝ = ⟪X -ᵥ Y, Z -ᵥ Y⟫_ℝ := by
  rw [← f.linearMap_vsub, ← f.linearMap_vsub]
  exact linearMap_inner_map_map_of_norm_map f.linear hnorm _ _

/-- The same linear-isometry hypothesis preserves inner products of all
displacement vectors. -/
theorem affineMap_displacement_inner_eq_of_linearIsometry
    [AddTorsor V E] [AddTorsor W F]
    (f : E →ᵃ[ℝ] F) (T : V →ₗᵢ[ℝ] W)
    (hlinear : f.linear = T.toLinearMap) (X Y Z : E) :
    ⟪f X -ᵥ f Y, f Z -ᵥ f Y⟫_ℝ = ⟪X -ᵥ Y, Z -ᵥ Y⟫_ℝ := by
  rw [← f.linearMap_vsub, ← f.linearMap_vsub, hlinear]
  change ⟪T (X -ᵥ Y), T (Z -ᵥ Y)⟫_ℝ = ⟪X -ᵥ Y, Z -ᵥ Y⟫_ℝ
  exact T.inner_map_map _ _

/-- A surjective complex-linear isometric embedding upgrades to a
complex-linear real isometric equivalence (the real-complex-structure form of
a unitary isomorphism). -/
theorem complexLinearIsometryEquiv_of_surjective
    (J : V →ₗ[ℝ] V) (K : W →ₗ[ℝ] W) (T : V →ₗᵢ[ℝ] W)
    (hTJ : ∀ v, T (J v) = K (T v)) (hsurj : Function.Surjective T) :
    ∃ U : V ≃ₗᵢ[ℝ] W,
      (∀ v, U v = T v) ∧ (∀ v, U (J v) = K (U v)) := by
  let U := LinearIsometryEquiv.ofSurjective T hsurj
  refine ⟨U, ?_, ?_⟩
  · intro v
    rfl
  · intro v
    exact hTJ v

end IsometricTransport

section OrientedPlane

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)]

/-- In an oriented Euclidean plane, the canonical positive quarter-turn is an
orthogonal complex structure. -/
def orientedPlaneComplexStructure (o : Orientation ℝ V (Fin 2)) :
    OrthogonalComplexStructure V where
  toLinearIsometryEquiv := o.rightAngleRotation
  sq_apply := o.rightAngleRotation_rightAngleRotation

/-- The affine theorem specialized to the classical oriented Euclidean plane. -/
theorem classicalVanAubelIdentity {E : Type*} [AddTorsor V E]
    (o : Orientation ℝ V (Fin 2)) (ε : ℝ) (hε_sq : ε ^ 2 = 1)
    (A B C D : E) :
    affineSquareCenter (orientedPlaneComplexStructure o).toLinearMap ε C D -ᵥ
        affineSquareCenter (orientedPlaneComplexStructure o).toLinearMap ε A B =
      ε • orientedPlaneComplexStructure o
        (affineSquareCenter (orientedPlaneComplexStructure o).toLinearMap ε D A -ᵥ
          affineSquareCenter (orientedPlaneComplexStructure o).toLinearMap ε B C) :=
  affineVanAubelIdentity (orientedPlaneComplexStructure o).toLinearMap
    (orientedPlaneComplexStructure o).sq_apply ε hε_sq A B C D

end OrientedPlane

end

end VanAubelExtensions
