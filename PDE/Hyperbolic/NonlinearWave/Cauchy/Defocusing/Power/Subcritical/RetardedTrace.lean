/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.ConeFlux
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder
public import PDE.Spaces.Sobolev.Variational.Spaces.H1
import PDE.Spaces.Sobolev.Calculus.Product.LipschitzCoefficient
import Mathlib.Analysis.Calculus.Rademacher

/-!
# The retarded Sobolev trace

The pullback of a C¹ spacetime field to a backward light cone is Lipschitz on bounded balls. Its
vertex is harmless for H¹ membership. The weak gradient is the spatial gradient minus the time
derivative times the outward radial normal.

The trace is the function `u*` of (15) in Evans, §12.3.2, and the gradient formula is the identity
`Du* = Du - ν uₜ` that the proof of Theorem 3 of §12.3.3 uses between (21) and (22).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.2, equation (15); §12.3.3, proof of Theorem 3,
  equations (21)-(22).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory Metric PDE PDE.Common PDE.Analysis
open SobolevSpace SobolevSpace.GraphSpace WaveEquation
open scoped ENNReal Sobolev RealInnerProductSpace Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- The spacetime field restricted to a backward cone, including its vertex. -/
def retardedTrace (u : ℝ^4 → ℝ) (c : ℝ^3) (T : ℝ) : ℝ^3 → ℝ :=
  u ∘ backwardConeGraph c T

/-- The tangential gradient of the retarded trace. The normal is totalized at
its single exceptional point, the vertex. -/
def retardedGradient (u : ℝ^4 → ℝ) (c : ℝ^3) (T : ℝ) (x : ℝ^3) : ℝ^3 :=
  classicalWaveSpatialGradient u (backwardConeGraph c T x) -
    (∂[0] u) (backwardConeGraph c T x) • NormedSpace.normalize (x - c)

/-- Compactness upgrades the local Lipschitz property of the cone trace. -/
theorem exists_lipschitzOnWith_retardedTrace {u : ℝ^4 → ℝ}
    (hu : ContDiff ℝ 1 u) (c : ℝ^3) (T R : ℝ) :
    ∃ K, LipschitzOnWith K (retardedTrace u c T) (ball c R) := by
  obtain ⟨L, hL⟩ := exists_lipschitzWith_backwardConeGraph c T
  have hloc := hu.locallyLipschitz.comp hL.locallyLipschitz
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall c R) hloc.locallyLipschitzOn
  exact ⟨K, hK.mono ball_subset_closedBall⟩

/-- Away from the vertex, the ordinary partial derivatives give the null
combination of the spacetime derivatives. -/
theorem partialDeriv_retardedTrace {u : ℝ^4 → ℝ} (hu : ContDiff ℝ 1 u)
    (c : ℝ^3) (T : ℝ) {x : ℝ^3} (hx : x ≠ c) (i : Fin 3) :
    (∂[i] (retardedTrace u c T)) x = retardedGradient u c T x i := by
  have hd := (hu.differentiable one_ne_zero _).hasFDerivAt.comp x
    (hasFDerivAt_backwardConeGraph c T hx)
  rw [partialDeriv, retardedTrace, hd.fderiv, ContinuousLinearMap.comp_apply,
    coneGraphDifferential_apply, fderiv_apply_eq_sum_partialDeriv_mul]
  simp only [Fin.sum_univ_succ, timeSpaceCons_zero, timeSpaceCons_succ,
    EuclideanSpace.inner_single_right, retardedGradient,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, classicalWaveSpatialGradient_apply]
  fin_cases i <;> simp [mul_comm, sub_eq_add_neg, add_comm]

/-- Every finite ball carries the retarded H¹ trace, with its weak
spatial gradient identified almost everywhere. -/
theorem exists_h1_retardedTrace {u : ℝ^4 → ℝ} (hu : ContDiff ℝ 1 u) (c : ℝ^3) (T R : ℝ) :
    ∃ U : H¹(ball c R), baseRepresentative U =ᵐ[domainMeasure 3 (ball c R)] retardedTrace u c T ∧
      (∇ U : ℝ^3 → ℝ^3) =ᵐ[domainMeasure 3 (ball c R)] retardedGradient u c T := by
  let μ := domainMeasure 3 (ball c R)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_retardedTrace hu c T R
  obtain ⟨g, hg, heq⟩ := hK.extend_real
  obtain ⟨B, hB⟩ := (hg.isBounded_image (isBounded_ball (x := c) (r := R))).exists_norm_le
  have hmem : MemLp g 2 μ := by
    apply (memLp_top_of_bound hg.continuous.aestronglyMeasurable B ?_).mono_exponent le_top
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hB (g x) (mem_image_of_mem g hx)
  have hder (i : Fin 3) : MemLp (lipschitzWeakCoord g i) 2 μ :=
    ((hg.memLp_lineDeriv (μ := (volume : Measure (ℝ^3)))
      (EuclideanSpace.single i (1 : ℝ))).mono_measure Measure.restrict_le_self).mono_exponent le_top
  have hw (i : Fin 3) : HasWeakDerivativeOn (ball c R) [i] g (lipschitzWeakCoord g i) :=
    (hg.hasWeakDerivativeOn_lipschitzWeakCoord i).mono measurableSet_ball (subset_univ _)
  obtain ⟨U, hU, hDU⟩ := exists_of_weakDerivative_coordinates (hmem.toLp g)
    (fun i ↦ (hder i).toLp (lipschitzWeakCoord g i)) (fun i ↦
      (hw i).congr_ae hmem.coeFn_toLp.symm (hder i).coeFn_toLp.symm)
  refine ⟨U, ?_, ?_⟩
  · change (U.val (baseIndex 3 1) : ℝ^3 → ℝ) =ᵐ[μ] _
    rw [hU]
    filter_upwards [hmem.coeFn_toLp, ae_restrict_mem measurableSet_ball] with x hx hxR
    exact hx.trans (heq hxR).symm
  have hcoords : ∀ᵐ x ∂μ, ∀ i : Fin 3,
      U.val (singleDerivIndex 3 i) x = lipschitzWeakCoord g i x := by
    refine ae_all_iff.mpr fun i ↦ ?_
    rw [hDU i]
    exact (hder i).coeFn_toLp
  have hne : ∀ᵐ x ∂μ, x ≠ c := ae_restrict_of_ae (show ∀ᵐ x ∂(volume : Measure (ℝ^3)), x ≠ c from
      by
        rw [ae_iff]
        simp)
  filter_upwards [wkpGradientCLM_apply_ae U, hcoords,
    ae_restrict_mem measurableSet_ball, hne] with x hx hd hxR hxc
  refine PiLp.ext fun i ↦ ?_
  rw [hx i, hd i]
  have hevent : g =ᶠ[𝓝 x] retardedTrace u c T :=
    Filter.Eventually.mono (isOpen_ball.mem_nhds hxR) fun y hy ↦ (heq hy).symm
  change lineDeriv ℝ g x (EuclideanSpace.single i (1 : ℝ)) = _
  rw [hevent.lineDeriv_eq]
  have hdiff := (hu.differentiable one_ne_zero _).comp x
    (hasFDerivAt_backwardConeGraph c T hxc).differentiableAt
  change lineDeriv ℝ (u ∘ backwardConeGraph c T) x _ = _
  rw [hdiff.lineDeriv_eq_fderiv]
  exact partialDeriv_retardedTrace hu c T hxc i

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
