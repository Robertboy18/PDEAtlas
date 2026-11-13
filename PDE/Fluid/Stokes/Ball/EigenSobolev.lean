/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.EigenExpansion
public import PDE.Fluid.NavierStokes.Nonuniqueness.Symmetry.Averaging
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Sector eigenvectors in `H¹` of the ball

`eigen_mem_closure_modes_H1` restates `eigen_mem_closure_modes` for an element `u` of
`H¹(B(0, R))³` whose value lies in the sector `odd` and which satisfies the eigenvalue equation
against every divergence-free element of `H¹` in the same sector: the restriction of a smooth
divergence-free sector field to the ball is such an element, with its classical gradient. If
moreover the value of `u` is `L²`-orthogonal to `ballModes R μ odd`, it vanishes
(`eq_zero_of_inner_ballModes`).

The sector sign `sectorSign` is the character `NavierStokes.Symmetry.parity` of the
axisymmetry group, and the rotation average `axisAverage` of the axisymmetric representatives
is `NavierStokes.Symmetry.rotationAverage`.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.CoordinateSystems SobolevSpace.GraphSpace
open PDE (partialDeriv divergence)
open scoped RealInnerProductSpace ContDiff Sobolev

namespace PDE.Fluid.Stokes.Ball

/-- The sector sign is the parity character of the axisymmetry group. -/
theorem sectorSign_eq_parity (odd : Bool) : sectorSign odd = NavierStokes.Symmetry.parity odd := by
  cases odd <;> rfl

/-- The rotation average of the axisymmetric representatives is the rotation average of the
axisymmetry group. -/
theorem axisAverage_eq_rotationAverage (u : ℝ^3 → ℝ^3) :
    axisAverage u = NavierStokes.Symmetry.rotationAverage u := by
  funext x
  set g : ℝ → ℝ^3 := fun φ ↦ axisRotation φ (u (axisRotation (-φ) x)) with hg
  have hper : Function.Periodic g (2 * Real.pi) := by
    intro φ
    simp only [hg, axisRotation_add_two_pi, neg_add]
    rw [show -φ + -(2 * Real.pi) = (-φ - 2 * Real.pi) by ring,
      ← axisRotation_add_two_pi (-φ - 2 * Real.pi)]
    ring_nf
  have h1 : ∫ θ in (0 : ℝ)..2 * Real.pi, axisRotation (-θ) (u (axisRotation θ x)) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, g θ := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 2 * Real.pi) g
    simp only [neg_zero] at h
    have h' : ∫ θ in (0 : ℝ)..2 * Real.pi, g (-θ) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, axisRotation (-θ) (u (axisRotation θ x)) := by
      refine intervalIntegral.integral_congr fun θ _ ↦ ?_
      simp only [hg, neg_neg]
    rw [← h', h]
    have := hper.intervalIntegral_add_eq (-(2 * Real.pi)) 0
    simpa using this
  have h2 : NavierStokes.Symmetry.rotationAverage u x =
      (2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, g θ := by
    have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) g
      (show (2 * Real.pi) ≠ 0 by positivity)
    simp only [mul_zero, mul_one] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    simp only [NavierStokes.Symmetry.act_false, axialRotation_symm, axialRotation_apply, hg]
  rw [axisAverage, h1, h2]

/-- The sector condition for a value on the ball: almost everywhere invariance under the
rotations about the axis and parity `sectorSign odd` under the equatorial reflection. -/
def InSector (R : ℝ) (odd : Bool) (U : ℝ^3 → ℝ^3) : Prop :=
  (∀ θ, ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
      U (axisRotation θ x) = axisRotation θ (U x)) ∧
    ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
      U (equatorialReflection x) = sectorSign odd • equatorialReflection (U x)

/-- The flattened classical gradient `k ↦ ∂ⱼ vᵢ` of a field, `k = (i, j)`. -/
def flatGrad (v : ℝ^3 → ℝ^3) (x : ℝ^3) : ℝ^(3 * 3) :=
  WithLp.toLp 2 fun k ↦ ∂[(finProdFinEquiv.symm k).2] (fun y ↦ v y (finProdFinEquiv.symm k).1) x

/-- A smooth field restricts to an element of `H¹(B)³` whose gradient is the classical one. -/
theorem exists_H1_of_contDiff {R : ℝ} {v : ℝ^3 → ℝ^3} (hv : ContDiff ℝ ∞ v) :
    ∃ V : Fin 3 → H¹(Metric.ball (0 : ℝ^3) R),
      (vectorWkpValueCLM V : ℝ^3 → ℝ^3) =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) R)] v ∧
      ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)), ∀ i j,
        ∇ V x (finProdFinEquiv (i, j)) = ∂[j] (fun y ↦ v y i) x := by
  have hvi (i : Fin 3) : ContDiff ℝ ∞ (fun y ↦ v y i) := (contDiff_piLp_apply 2).comp hv
  have hgc : Continuous (flatGrad v) := by
    unfold flatGrad
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k ↦
      ((hvi _).partialDeriv _).continuous)
  have hf : MemLp v 2 (SobolevSpace.domainMeasure 3 (Metric.ball (0 : ℝ^3) R)) :=
    memLp_ball_of_continuous hv.continuous
  have hg : MemLp (flatGrad v) 2 (SobolevSpace.domainMeasure 3 (Metric.ball (0 : ℝ^3) R)) :=
    memLp_ball_of_continuous hgc
  have hgij (i j : Fin 3) (x : ℝ^3) :
      flatGrad v x (finProdFinEquiv (i, j)) = ∂[j] (fun y ↦ v y i) x := by
    simp [flatGrad]
  obtain ⟨V, hV1, hV2⟩ := exists_vectorWkp_of_weakGradient (hf.toLp v) (hg.toLp _)
    fun i j ↦ by
      refine (hasWeakDerivativeOn_ball_of_contDiff (R := R) hv i j).congr_ae ?_ ?_
      · filter_upwards [hf.coeFn_toLp] with x hx
        rw [hx]
      · filter_upwards [hg.coeFn_toLp] with x hx
        rw [hx, hgij]
  refine ⟨V, hV1.trans hf.coeFn_toLp, ?_⟩
  filter_upwards [hV2, hg.coeFn_toLp] with x h1 h2 i j
  rw [h1, h2, hgij]

/-- Pointwise sector symmetry passes to an almost everywhere equal value. -/
theorem inSector_of_ae_eq {R : ℝ} {odd : Bool} {U v : ℝ^3 → ℝ^3}
    (hUv : U =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) R)] v)
    (hveq : IsEquivariantUnderAxisRotation v)
    (hvpar : ∀ x, v (equatorialReflection x) = sectorSign odd • equatorialReflection (v x)) :
    InSector R odd U := by
  refine ⟨fun θ ↦ ?_, ?_⟩
  · have hc := (measurePreserving_axisRotation_ball R θ).quasiMeasurePreserving.ae_eq_comp hUv
    filter_upwards [hc, hUv] with x h1 h2
    simp only [Function.comp_apply] at h1
    rw [h1, h2, hveq]
  · have hc := (measurePreserving_equatorialReflection_ball R).quasiMeasurePreserving.ae_eq_comp
      hUv
    filter_upwards [hc, hUv] with x h1 h2
    simp only [Function.comp_apply] at h1
    rw [h1, h2, hvpar]

/-- **Sector eigenvectors in `H¹` lie in the closed span of the modes.** An element `u` of
`H¹(B(0, R))³` with divergence zero, value in the sector `odd`, and the eigenvalue equation
`∫ ∇u : ∇v = μ ∫ ⟪u, v⟫` against every divergence-free element `v` of `H¹` in the sector has its
value in the closed span of `ballModes R μ odd`. -/
theorem eigen_mem_closure_modes_H1 {R μ : ℝ} (hR : 0 < R) (odd : Bool)
    (u : Fin 3 → H¹(Metric.ball (0 : ℝ^3) R))
    (hdiv : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
      ∑ i, ∇ u x (finProdFinEquiv (i, i)) = 0)
    (hsec : InSector R odd (vectorWkpValueCLM u))
    (heigH1 : ∀ v : Fin 3 → H¹(Metric.ball (0 : ℝ^3) R),
      (∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
        ∑ i, ∇ v x (finProdFinEquiv (i, i)) = 0) →
      InSector R odd (vectorWkpValueCLM v) →
      ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
          ∇ u x (finProdFinEquiv (i, j)) * ∇ v x (finProdFinEquiv (i, j)) =
        μ * ∫ x in Metric.ball (0 : ℝ^3) R, ⟪vectorWkpValueCLM u x, vectorWkpValueCLM v x⟫) :
    vectorWkpValueCLM u ∈ (Submodule.span ℝ (ballModes R μ odd)).topologicalClosure := by
  have hu : MemLp (vectorWkpValueCLM u : ℝ^3 → ℝ^3) 2
      (volume.restrict (Metric.ball (0 : ℝ^3) R)) := Lp.memLp (vectorWkpValueCLM u)
  have hDu (i j : Fin 3) : MemLp (fun x ↦ ∇ u x (finProdFinEquiv (i, j))) 2
      (volume.restrict (Metric.ball (0 : ℝ^3) R)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (finProdFinEquiv (i, j))).comp_memLp'
      (Lp.memLp (vectorWkpGradientCLM u))
  have h := eigen_mem_closure_modes (μ := μ) hR odd hu hDu
    (fun i j ↦ hasWeakDerivativeOn_vectorWkpGradientCLM u i j) hdiv hsec.1 hsec.2 ?_
  · rwa [Lp.toLp_coeFn] at h
  intro v hv hdivv hveq hvpar
  obtain ⟨V, hV1, hV2⟩ := exists_H1_of_contDiff (R := R) hv
  have hVdiv : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
      ∑ i, ∇ V x (finProdFinEquiv (i, i)) = 0 := by
    filter_upwards [hV2] with x hx
    simp only [hx]
    simpa [divergence] using hdivv x
  have h1 := heigH1 V hVdiv (inSector_of_ae_eq hV1 hveq hvpar)
  have e1 : ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
      ∇ u x (finProdFinEquiv (i, j)) * ∇ V x (finProdFinEquiv (i, j)) =
      ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
        ∇ u x (finProdFinEquiv (i, j)) * ∂[j] (fun y ↦ v y i) x := by
    refine integral_congr_ae ?_
    filter_upwards [hV2] with x hx
    simp only [hx]
  have e2 : ∫ x in Metric.ball (0 : ℝ^3) R, ⟪vectorWkpValueCLM u x, vectorWkpValueCLM V x⟫ =
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪vectorWkpValueCLM u x, v x⟫ := by
    refine integral_congr_ae ?_
    filter_upwards [hV1] with x hx
    rw [hx]
  rw [e1, e2] at h1
  exact h1

/-- **Orthogonality to the modes.** A sector eigenvector of `H¹` whose value is
`L²`-orthogonal to every element of `ballModes R μ odd` has zero value. -/
theorem eq_zero_of_inner_ballModes {R μ : ℝ} (hR : 0 < R) (odd : Bool)
    (u : Fin 3 → H¹(Metric.ball (0 : ℝ^3) R))
    (hdiv : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
      ∑ i, ∇ u x (finProdFinEquiv (i, i)) = 0)
    (hsec : InSector R odd (vectorWkpValueCLM u))
    (heigH1 : ∀ v : Fin 3 → H¹(Metric.ball (0 : ℝ^3) R),
      (∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
        ∑ i, ∇ v x (finProdFinEquiv (i, i)) = 0) →
      InSector R odd (vectorWkpValueCLM v) →
      ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
          ∇ u x (finProdFinEquiv (i, j)) * ∇ v x (finProdFinEquiv (i, j)) =
        μ * ∫ x in Metric.ball (0 : ℝ^3) R, ⟪vectorWkpValueCLM u x, vectorWkpValueCLM v x⟫)
    (horth : ∀ f ∈ ballModes R μ odd, ⟪f, vectorWkpValueCLM u⟫ = 0) :
    vectorWkpValueCLM u = 0 := by
  set U := vectorWkpValueCLM u
  have hmem := eigen_mem_closure_modes_H1 hR odd u hdiv hsec heigH1
  have hspan : ∀ f ∈ Submodule.span ℝ (ballModes R μ odd), ⟪f, U⟫ = 0 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf => exact horth f hf
    | zero => simp
    | add f g _ _ hf hg => rw [inner_add_left, hf, hg, add_zero]
    | smul c f _ hf => rw [real_inner_smul_left, hf, mul_zero]
  have hclosed : IsClosed {f : Lp (ℝ^3) 2 (volume.restrict (Metric.ball (0 : ℝ^3) R)) |
      ⟪f, U⟫ = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hcl : ((Submodule.span ℝ (ballModes R μ odd)).topologicalClosure :
      Set (Lp (ℝ^3) 2 (volume.restrict (Metric.ball (0 : ℝ^3) R)))) ⊆
      {f | ⟪f, U⟫ = 0} := by
    rw [Submodule.topologicalClosure_coe]
    exact closure_minimal (fun f hf ↦ hspan f hf) hclosed
  have hUU : ⟪U, U⟫ = 0 := hcl hmem
  exact inner_self_eq_zero.mp hUU

end PDE.Fluid.Stokes.Ball
