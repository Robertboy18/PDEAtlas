/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.Radon.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Continuity of hyperplane integrals

Schwartz decay controls the integrand on every orthogonal fiber by one
integrable function of the fiber coordinate. The bound is uniform in the
remaining coordinates because orthogonal projection decreases the norm.
Dominated convergence then gives continuity of the fiber integrals.

This removes the almost-everywhere qualification in the `L¹` definition:
each fiber integral exists, and the marginal is continuous everywhere.
The same argument applies to real or Banach-valued Schwartz functions and
to orthogonal subspaces of any dimension.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [MeasurableSpace E] [BorelSpace E] in
private theorem norm_orthogonal_component_le (K : Submodule ℝ E) (x : K) (y : Kᗮ) :
    ‖y‖ ≤ ‖(x : E) + (y : E)‖ := by
  calc
    ‖y‖ ≤ ‖WithLp.toLp 2 (x, y)‖ := by
      simpa using WithLp.norm_snd_le K (WithLp.toLp 2 (x, y))
    _ = ‖K.orthogonalDecomposition.symm (WithLp.toLp 2 (x, y))‖ :=
      (K.orthogonalDecomposition.symm.norm_map _).symm
    _ = _ := by simp [Submodule.orthogonalDecomposition_symm_apply]

/-- One integrable function bounds a Schwartz function along every fiber
orthogonal to `K`, uniformly in the base point in `K`. -/
theorem exists_integrable_bound_add_orthogonal (f : 𝓢(E, F)) (K : Submodule ℝ E) :
    ∃ b : Kᗮ → ℝ, Integrable b ∧
      ∀ (x : K) (y : Kᗮ), ‖f ((x : E) + (y : E))‖ ≤ b y := by
  let l := (volume : Measure Kᗮ).integrablePower
  refine ⟨fun y ↦ 2 ^ l * (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ l 0 f) *
    (1 + ‖y‖) ^ (-(l : ℝ)),
    ((volume : Measure Kᗮ).integrable_pow_neg_integrablePower).const_mul _, ?_⟩
  intro x y
  have hdecay : ‖y‖ ^ (0 + l) * ‖f ((x : E) + (y : E))‖ ≤
      SchwartzMap.seminorm ℝ l 0 f := by
    calc
      _ ≤ ‖(x : E) + (y : E)‖ ^ l * ‖f ((x : E) + (y : E))‖ := by
        simp only [zero_add]
        gcongr
        exact norm_orthogonal_component_le K x y
      _ ≤ _ := norm_pow_mul_le_seminorm ℝ f l _
  simpa only [pow_zero, one_mul] using
    pow_mul_le_of_le_of_pow_mul_le (norm_nonneg y)
      (norm_nonneg (f ((x : E) + (y : E))))
      (norm_le_seminorm ℝ f _) hdecay

/-- Every individual orthogonal fiber of a Schwartz function is integrable. -/
theorem integrable_add_orthogonal (f : 𝓢(E, F)) (K : Submodule ℝ E) (x : K) :
    Integrable (fun y : Kᗮ ↦ f ((x : E) + (y : E))) := by
  obtain ⟨b, hb, hbound⟩ := f.exists_integrable_bound_add_orthogonal K
  exact hb.mono'
    (f.continuous.comp (continuous_const.add continuous_subtype_val)).aestronglyMeasurable
    (Filter.Eventually.of_forall (hbound x))

/-- Integrating out an orthogonal subspace preserves continuity of a
Schwartz function. The fiber integral is taken at every point, not almost everywhere. -/
theorem continuous_orthogonalMarginal (f : 𝓢(E, F)) (K : Submodule ℝ E) :
    Continuous (PDE.Analysis.Fourier.orthogonalMarginal K f) := by
  obtain ⟨b, hb, hbound⟩ := f.exists_integrable_bound_add_orthogonal K
  apply continuous_of_dominated (bound := b)
  · intro x
    exact (f.continuous.comp (continuous_const.add continuous_subtype_val)).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall (hbound x)
  · exact hb
  · exact Filter.Eventually.of_forall
      (fun y ↦ f.continuous.comp (continuous_subtype_val.add continuous_const))

/-- The hyperplane integral of a Schwartz function varies continuously with
the signed displacement, for each fixed unit normal. -/
theorem continuous_radonTransform (f : 𝓢(E, F)) {θ : E} (hθ : ‖θ‖ = 1) :
    Continuous (PDE.Analysis.Fourier.radonTransform f θ) := by
  let A : ℝ ≃ₗᵢ[ℝ] ℝ ∙ θ := LinearIsometryEquiv.toSpanUnitSingleton θ hθ
  exact (f.continuous_orthogonalMarginal (ℝ ∙ θ)).comp A.continuous

end SchwartzMap
