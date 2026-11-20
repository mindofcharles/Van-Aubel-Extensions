/-
Copyright (c) 2026 mindofcharles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mindofcharles
-/

import VanAubelExtensions.MixedSigns
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Measure-zero mixed-sign loci

Surjectivity makes every nonempty mismatch kernel a proper real subspace.
It therefore has zero additive Haar measure, as does every measure absolutely
continuous with respect to that measure.
-/

namespace VanAubelExtensions

noncomputable section

open MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] [Nontrivial V]
  [MeasurableSpace (Fin 4 → V)] [BorelSpace (Fin 4 → V)]

/-- A nonempty mismatch locus has zero Lebesgue (additive Haar) measure. -/
theorem mismatchPointLocus_haar_zero (δ : ℝ) (hδ : δ ^ 2 = 1)
    (t : Fin 4 → Bool) (ht : ∃ i, t i = true)
    (μ : Measure (Fin 4 → V)) [Measure.IsAddHaarMeasure μ] :
    μ {p | mismatchPointLocusMap δ t p = 0} = 0 := by
  let f := mismatchPointLocusMap (V := V) δ t
  have hsurj : Function.Surjective f := mismatchPointLocusMap_surjective δ hδ t ht
  have hk : f.ker ≠ ⊤ := by
    intro h
    have hf : f = 0 := LinearMap.ker_eq_top.mp h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨p, hp⟩ := hsurj v
    have hz : (0 : V) = v := by simpa only [hf, LinearMap.zero_apply] using hp
    exact hv hz.symm
  have hr : f.ker.restrictScalars ℝ ≠ ⊤ := by
    intro h
    apply hk
    apply Submodule.eq_top_iff'.mpr
    intro p
    have hp : p ∈ f.ker.restrictScalars ℝ := by rw [h]; trivial
    exact hp
  change μ (f.ker.restrictScalars ℝ : Set (Fin 4 → V)) = 0
  exact Measure.addHaar_submodule μ _ hr

/-- Every measure absolutely continuous with respect to Lebesgue measure
assigns probability (or mass) zero to a fixed nonempty mismatch locus. -/
theorem mismatchPointLocus_absolutelyContinuous_zero (δ : ℝ) (hδ : δ ^ 2 = 1)
    (t : Fin 4 → Bool) (ht : ∃ i, t i = true)
    (μ ν : Measure (Fin 4 → V)) [Measure.IsAddHaarMeasure μ] (hν : ν ≪ μ) :
    ν {p | mismatchPointLocusMap δ t p = 0} = 0 :=
  hν (mismatchPointLocus_haar_zero δ hδ t ht μ)

end

end VanAubelExtensions
