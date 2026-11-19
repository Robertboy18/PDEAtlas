/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Area.PairedRescaling
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.PairedKernel

/-!
# Uniform bounds for paired gradients in an actual C¹ boundary chart

The forward chart is Lipschitz on its bounded boundary piece. Its inverse
parametrization therefore has a quantitative lower bound on distances. Together
with the bounded actual surface Jacobian and normal separation, this produces
an integrable dimension-plus-one majorant after rescaling.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open Set PDE.Analysis PotentialTheory Boundary.Geometry.SurfaceMeasure
open scoped Gradient

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The forward chart controls parameter distances by actual physical boundary distances. -/
theorem exists_chartBoundaryParametrization_lower_bound (i : Fin hΩ.N) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ a ∈ chartBoundaryParameterDomain (Ω := Ω) i,
      ∀ b ∈ chartBoundaryParameterDomain (Ω := Ω) i,
        ‖a - b‖ ≤ L * ‖chartBoundaryParametrization (Ω := Ω) i a -
          chartBoundaryParametrization (Ω := Ω) i b‖ := by
  obtain ⟨K, hK⟩ := exists_chart_lipschitzOnWith_boundary_piece (Ω := Ω) i
  refine ⟨max 1 (K : ℝ), le_max_left _ _, ?_⟩
  intro a ha b hb
  have hPa : chartBoundaryParametrization (Ω := Ω) i a ∈
      (hΩ.chart i).source ∩ frontier Ω := by
    rw [← image_chartBoundaryParametrization i]
    exact mem_image_of_mem _ ha
  have hPb : chartBoundaryParametrization (Ω := Ω) i b ∈
      (hΩ.chart i).source ∩ frontier Ω := by
    rw [← image_chartBoundaryParametrization i]
    exact mem_image_of_mem _ hb
  have hdist := hK.dist_le_mul _ hPa _ hPb
  have hea : hΩ.chart i (chartBoundaryParametrization (Ω := Ω) i a) =
      flatEmbedding a := (hΩ.chart i).right_inv ha
  have heb : hΩ.chart i (chartBoundaryParametrization (Ω := Ω) i b) =
      flatEmbedding b := (hΩ.chart i).right_inv hb
  rw [hea, heb, (isometry_flatEmbedding (n := m)).dist_eq] at hdist
  simp only [dist_eq_norm] at hdist
  exact hdist.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-- The actual Jacobian is uniformly bounded on each bounded chart parameter domain. -/
theorem exists_chartBoundaryJacobian_bound (i : Fin hΩ.N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ b ∈ chartBoundaryParameterDomain (Ω := Ω) i,
      ‖chartBoundaryJacobian (Ω := Ω) i b‖ ≤ M := by
  have hbounded : Bornology.IsBounded (chartBoundaryParameterDomain (Ω := Ω) i) :=
    (isometry_flatEmbedding (n := m)).antilipschitzWith.isBounded_preimage
      (hΩ.chart_target_bounded i)
  obtain ⟨M, hM⟩ := hbounded.isCompact_closure.exists_bound_of_continuousOn
    (continuous_chartBoundaryJacobian (Ω := Ω) i).continuousOn
  exact ⟨max 0 M, le_max_left _ _, fun b hb ↦
    (hM b (subset_closure hb)).trans (le_max_right _ _)⟩

/-- Actual chart geometry and normal separation give a uniform integrable rescaled majorant. -/
theorem exists_chartBoundary_paired_gradient_rescale_bound (hm : 1 ≤ m)
    (i : Fin hΩ.N) {a : ℝ^m} (ha : a ∈ chartBoundaryParameterDomain (Ω := Ω) i)
    (x : frontier Ω) (hx : chartBoundaryParametrization (Ω := Ω) i a = (x : ℝ^(m + 1))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∀ v : ℝ^m,
      a + t • v ∈ chartBoundaryParameterDomain (Ω := Ω) i →
      ‖chartBoundaryJacobian (Ω := Ω) i (a + t • v) •
        (t ^ m • (∇ (fundamentalSolution (m + 1))
            ((x : ℝ^(m + 1)) - t • outwardUnitNormal (Ω := Ω) x -
              chartBoundaryParametrization i (a + t • v)) -
          ∇ (fundamentalSolution (m + 1))
            ((x : ℝ^(m + 1)) + t • outwardUnitNormal (Ω := Ω) x -
              chartBoundaryParametrization i (a + t • v))))‖ ≤
        C * ((1 + ‖v‖) ^ (m + 1))⁻¹ := by
  obtain ⟨L, hL, hLip⟩ := exists_chartBoundaryParametrization_lower_bound (Ω := Ω) i
  obtain ⟨M, hM, hJac⟩ := exists_chartBoundaryJacobian_bound (Ω := Ω) i
  obtain ⟨δ, hδ, hpaired⟩ := exists_paired_gradient_fundamentalSolution_bound
    (Ω := Ω) (by omega : 2 ≤ m + 1) x
  let A : ℝ := 2 ^ (m + 2) * (((m + 1 : ℕ) : ℝ) + 1) / unitSphereArea (m + 1)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (by positivity) (unitSphereArea_pos (n := m + 1)).le
  refine ⟨M * A * L ^ (m + 1), by positivity, δ, hδ, ?_⟩
  intro t ht htδ v hv
  let y := chartBoundaryParametrization (Ω := Ω) i (a + t • v)
  have hy : y ∈ frontier Ω := by
    have hi : y ∈ (hΩ.chart i).source ∩ frontier Ω := by
      rw [← image_chartBoundaryParametrization i]
      exact mem_image_of_mem _ hv
    exact hi.2
  have hkernel : ‖∇ (fundamentalSolution (m + 1))
        ((x : ℝ^(m + 1)) - t • outwardUnitNormal (Ω := Ω) x - y) -
      ∇ (fundamentalSolution (m + 1))
        ((x : ℝ^(m + 1)) + t • outwardUnitNormal (Ω := Ω) x - y)‖ ≤
      A * t / (t + ‖(x : ℝ^(m + 1)) - y‖) ^ (m + 1) :=
    hpaired t ht htδ y hy
  have hdist : t * ‖v‖ ≤ L * ‖(x : ℝ^(m + 1)) - y‖ := by
    have h := hLip a ha (a + t • v) hv
    rw [hx] at h
    simpa only [y, sub_add_cancel_left, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht] using h
  have hden : t * (1 + ‖v‖) ≤ L * (t + ‖(x : ℝ^(m + 1)) - y‖) := by
    have htL := mul_le_mul_of_nonneg_right hL ht.le
    nlinarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ t * (1 + ‖v‖)) hden (m + 1)
  simp only [mul_pow] at hpow
  have hratio : t ^ (m + 1) / (t + ‖(x : ℝ^(m + 1)) - y‖) ^ (m + 1) ≤
      L ^ (m + 1) / (1 + ‖v‖) ^ (m + 1) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    exact hpow
  calc
    _ = ‖chartBoundaryJacobian (Ω := Ω) i (a + t • v)‖ * t ^ m *
        ‖∇ (fundamentalSolution (m + 1))
            ((x : ℝ^(m + 1)) - t • outwardUnitNormal (Ω := Ω) x - y) -
          ∇ (fundamentalSolution (m + 1))
            ((x : ℝ^(m + 1)) + t • outwardUnitNormal (Ω := Ω) x - y)‖ := by
      simp only [y, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg ht.le m), mul_assoc]
    _ ≤ M * t ^ m * (A * t / (t + ‖(x : ℝ^(m + 1)) - y‖) ^ (m + 1)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (hJac _ hv) (pow_nonneg ht.le m))
        hkernel (norm_nonneg _) (mul_nonneg hM (pow_nonneg ht.le m))
    _ = M * A * (t ^ (m + 1) / (t + ‖(x : ℝ^(m + 1)) - y‖) ^ (m + 1)) := by
      rw [pow_succ]
      ring
    _ ≤ M * A * (L ^ (m + 1) / (1 + ‖v‖) ^ (m + 1)) :=
      mul_le_mul_of_nonneg_left hratio (mul_nonneg hM hA)
    _ = (M * A * L ^ (m + 1)) * ((1 + ‖v‖) ^ (m + 1))⁻¹ := by ring

end SobolevSpace.Trace.C1
