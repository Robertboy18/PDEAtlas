/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.FiniteProduct.Vector
public import PDE.Spaces.Sobolev.Calculus.Composition.FiniteProduct.Linear
public import PDE.Analysis.InnerProductSpace.Calculus.Normalization

/-!
# Weak derivatives of sphere-valued Sobolev maps

A map into the unit sphere has tangent weak derivatives. We obtain this from
the Sobolev chain rule for a smooth cutoff of normalization: composing with
that map leaves the field unchanged, while its derivative removes the radial
component. Uniqueness of weak derivatives then forces that component to vanish.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.FiniteProductComposition

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology InnerProductSpace Sobolev

variable {n m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}
  [IsFiniteMeasure (domainMeasure n Ω)]

/-- The weak derivative columns of a unit-length Sobolev map are orthogonal to
its value almost everywhere. No smoothness of the field is assumed. -/
theorem inner_values_derivatives_eq_zero_ae_of_norm_eq_one
    (hΩ : IsOpen Ω) (E : Extension.GraphSpace.Operator n 1 p Ω) (hp : p ≠ ∞)
    (U : Fin m → W^{1,p}(Ω))
    (hunit : ∀ᵐ x ∂domainMeasure n Ω, ‖values U x‖ = 1) (i : Fin n) :
    ∀ᵐ x ∂domainMeasure n Ω, ⟪values U x, derivatives U i x⟫_ℝ = 0 := by
  obtain ⟨G, hG, _, heq, C, hC⟩ :=
    NormedSpace.exists_contDiff_compactSupport_eqOn_normalize
      (E := ℝ^m) (a := 1 / 2) (b := 2) (by norm_num) (by norm_num)
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by simp)
  have hbound : ∀ z, ‖fderiv ℝ G z‖ ≤ (‖C‖₊ : ℝ) :=
    fun z ↦ (hC z).trans (le_abs_self C)
  let V := vectorCompositionOnOfExtension hΩ E hp hG1 hbound U
  have hvalues : values V =ᵐ[domainMeasure n Ω] values U := by
    filter_upwards [vectorCompositionOnOfExtension_values_ae hΩ E hp hG1 hbound U,
      hunit] with x hx hu
    rw [hx, heq _ (by rw [hu]; norm_num) (by rw [hu]; norm_num)]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one hu
  have hVU : V = U := eq_of_values_ae_eq hΩ hvalues
  have hd := vectorCompositionOnOfExtension_derivatives_ae hΩ E hp hG1 hbound U i
  change derivatives V i =ᵐ[domainMeasure n Ω] _ at hd
  rw [hVU] at hd
  filter_upwards [hd, hunit] with x hx hu
  have hnear : ∀ᶠ z in 𝓝 (values U x), 1 / 2 < ‖z‖ ∧ ‖z‖ < 2 :=
    continuous_norm.continuousAt.eventually (Ioo_mem_nhds
      (by norm_num [hu]) (by norm_num [hu]))
  have hgerm : G =ᶠ[𝓝 (values U x)] NormedSpace.normalize :=
    hnear.mono fun z hz ↦ heq z hz.1.le hz.2.le
  rw [hgerm.fderiv_eq,
    NormedSpace.fderiv_normalize_apply_of_norm_eq_one hu] at hx
  have hinner := congrArg (fun v ↦ ⟪values U x, v⟫_ℝ) hx
  simpa [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu]
    using hinner

end SobolevSpace.GraphSpace.FiniteProductComposition
