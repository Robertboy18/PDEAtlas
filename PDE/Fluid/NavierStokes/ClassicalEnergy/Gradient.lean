/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Energy
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.SpaceTime
import PDE.Fluid.NavierStokes.LocalEnergy.Testing

/-!
# The gradient field of classical velocity slices

`sliceGradient u` is the spatial gradient field whose value at a point of positive time is the
matrix of coordinate derivatives of the velocity slice through that point; it vanishes at
nonpositive times. When every positive-time slice is continuously differentiable it is the weak
spatial derivative of the velocity on each such slice, its slices are square integrable when the
derivative of the slice is, and it agrees with the classical spacetime gradient wherever the
velocity is differentiable. Its squared Frobenius norm is at most `n` times the squared operator
norm of the slice derivative.
-/

@[expose] public noncomputable section

namespace NavierStokes

open EuclideanSpace MeasureTheory IncompressibleFlow PDE PDE.Common

set_option linter.missingDocs true

variable {n : ℕ}

/-- The gradient field of the velocity slices: at positive time `z 0`, entry `(i, j)` is the
coordinate derivative `∂ⱼ` of `x ↦ uᵢ(z 0, x)` at the spatial part of `z`; zero otherwise. -/
def sliceGradient (u : ℝ^(n + 1) → ℝ^n) : SpatialGradientField n :=
  fun z ↦ if 0 < z 0 then
    WithLp.toLp 2 fun ij ↦ (∂[ij.2] (fun x ↦ u (timeSpaceCons (z 0) x) ij.1)) (spatialPart z)
  else 0

/-- At positive time the slice gradient is the matrix of slice derivatives. -/
theorem sliceGradient_timeSpaceCons_apply (u : ℝ^(n + 1) → ℝ^n) {t : ℝ} (ht : 0 < t)
    (x : ℝ^n) (i j : Fin n) :
    sliceGradient u (timeSpaceCons t x) (i, j) =
      (∂[j] (fun y ↦ u (timeSpaceCons t y) i)) x := by
  simp [sliceGradient, ht, PiLp.toLp_apply]

/-- The slice gradient vanishes at nonpositive times. -/
theorem sliceGradient_of_nonpos (u : ℝ^(n + 1) → ℝ^n) {z : ℝ^(n + 1)} (hz : z 0 ≤ 0) :
    sliceGradient u z = 0 := by
  simp [sliceGradient, not_lt.mpr hz]

/-- Where the velocity is differentiable at positive time, the slice gradient is the classical
spatial gradient. -/
theorem sliceGradient_eq_spatialVelocityGradient {u : ℝ^(n + 1) → ℝ^n} {z : ℝ^(n + 1)}
    (hz : 0 < z 0) (hu : DifferentiableAt ℝ u z) :
    sliceGradient u z = spatialVelocityGradient n u z := by
  ext ⟨i, j⟩
  rw [← timeSpaceCons_spatialPart z] at hu ⊢
  rw [sliceGradient_timeSpaceCons_apply u (by simpa using hz), spatialVelocityGradient_apply]
  exact partialDeriv_timeSpaceCons_spatial j (fun y ↦ u y i) (z 0) (spatialPart z)
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp _ hu)

/-- On the open slab, the slice gradient of a `C²` velocity is continuous. -/
theorem continuousAt_sliceGradient {u : ℝ^(n + 1) → ℝ^n} {T : ℝ}
    (hu : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 2 u z) {z : ℝ^(n + 1)}
    (hz : z ∈ finiteTimeDomain n T) : ContinuousAt (sliceGradient u) z := by
  have heq : spatialVelocityGradient n u =ᶠ[nhds z] sliceGradient u := by
    filter_upwards [(isOpen_finiteTimeDomain n T).mem_nhds hz] with y hy
    exact (sliceGradient_eq_spatialVelocityGradient hy.1
      ((hu y hy).differentiableAt (by norm_num))).symm
  exact (continuousAt_spatialVelocityGradient (hu z hz)).congr heq

/-- A continuously differentiable velocity slice has the slice gradient as its weak spatial
derivative. -/
theorem hasWeakDerivativeOn_sliceGradient {u : ℝ^(n + 1) → ℝ^n} {t : ℝ} (ht : 0 < t)
    (hC : ContDiff ℝ 1 (velocitySlice u t)) (i j : Fin n) :
    SobolevSpace.HasWeakDerivativeOn (n := n) Set.univ [j]
      (fun x ↦ u (timeSpaceCons t x) i) (fun x ↦ sliceGradient u (timeSpaceCons t x) (i, j)) := by
  have hf (x : ℝ^n) (_ : x ∈ Set.univ) :
      ContDiffAt ℝ 1 (fun x ↦ u (timeSpaceCons t x) i) x :=
    ((contDiffAt_piLp 2).mp hC.contDiffAt i)
  have h := SobolevSpace.hasWeakDerivativeOn_of_contDiffAt_one isOpen_univ hf j
  convert h using 1
  funext x
  exact sliceGradient_timeSpaceCons_apply u ht x i j

/-- The squared norm of the slice gradient is at most `n` times the squared operator norm of the
slice derivative. -/
theorem norm_sliceGradient_sq_le {u : ℝ^(n + 1) → ℝ^n} {t : ℝ} (ht : 0 < t) {x : ℝ^n}
    (hd : DifferentiableAt ℝ (velocitySlice u t) x) :
    ‖sliceGradient u (timeSpaceCons t x)‖ ^ 2 ≤ n * ‖fderiv ℝ (velocitySlice u t) x‖ ^ 2 := by
  have hentry (i j : Fin n) : sliceGradient u (timeSpaceCons t x) (i, j) =
      fderiv ℝ (velocitySlice u t) x (EuclideanSpace.single j 1) i := by
    rw [sliceGradient_timeSpaceCons_apply u ht]
    exact (partialDeriv_apply j i hd).symm
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [hentry]
  calc ∑ j : Fin n, ∑ i : Fin n, fderiv ℝ (velocitySlice u t) x (EuclideanSpace.single j 1) i ^ 2
      = ∑ j : Fin n, ‖fderiv ℝ (velocitySlice u t) x (EuclideanSpace.single j 1)‖ ^ 2 := by
        simp [EuclideanSpace.real_norm_sq_eq]
    _ ≤ ∑ _j : Fin n, ‖fderiv ℝ (velocitySlice u t) x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have h := (fderiv ℝ (velocitySlice u t) x).le_opNorm (EuclideanSpace.single j 1)
        rw [EuclideanSpace.orthonormal_single.1 j, mul_one] at h
        exact pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = n * ‖fderiv ℝ (velocitySlice u t) x‖ ^ 2 := by simp

/-- The norm of the slice gradient is at most `√n` times the operator norm of the slice
derivative. -/
theorem norm_sliceGradient_le {u : ℝ^(n + 1) → ℝ^n} {t : ℝ} (ht : 0 < t) {x : ℝ^n}
    (hd : DifferentiableAt ℝ (velocitySlice u t) x) :
    ‖sliceGradient u (timeSpaceCons t x)‖ ≤ √n * ‖fderiv ℝ (velocitySlice u t) x‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (sliceGradient u (timeSpaceCons t x))),
    ← Real.sqrt_sq (norm_nonneg (fderiv ℝ (velocitySlice u t) x)), ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt (norm_sliceGradient_sq_le ht hd)

/-- A continuously differentiable slice is continuous in the slice gradient. -/
theorem continuous_spatialGradientSlice_sliceGradient {u : ℝ^(n + 1) → ℝ^n} {t : ℝ}
    (ht : 0 < t) (hC : ContDiff ℝ 1 (velocitySlice u t)) :
    Continuous (spatialGradientSlice (sliceGradient u) t) := by
  have heq : spatialGradientSlice (sliceGradient u) t =
      fun x ↦ WithLp.toLp 2 fun ij : Fin n × Fin n ↦
        (∂[ij.2] (fun y ↦ u (timeSpaceCons t y) ij.1)) x := by
    funext x
    ext ⟨i, j⟩
    simp [spatialGradientSlice, sliceGradient_timeSpaceCons_apply u ht]
  rw [heq]
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro ij
  exact ((contDiff_piLp 2).mp hC ij.1).continuous_partialDeriv ij.2

/-- The slice gradient of a continuously differentiable slice with square-integrable derivative is
square integrable. -/
theorem memLp_spatialGradientSlice_sliceGradient {u : ℝ^(n + 1) → ℝ^n} {t : ℝ} (ht : 0 < t)
    (hC : ContDiff ℝ 1 (velocitySlice u t))
    (hD : MemLp (fderiv ℝ (velocitySlice u t)) 2 volume) :
    MemLp (spatialGradientSlice (sliceGradient u) t) 2 volume :=
  hD.of_le_mul (continuous_spatialGradientSlice_sliceGradient ht hC).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦
      norm_sliceGradient_le ht (hC.differentiable (by norm_num) x))

end NavierStokes
