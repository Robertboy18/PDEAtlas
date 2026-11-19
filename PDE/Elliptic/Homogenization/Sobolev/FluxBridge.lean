/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.Sobolev.Interval
public import PDE.Elliptic.Variational.DivergenceForm

/-!
# The interval flux equation as a weak divergence-form equation

A `C¹` scalar solution with differentiable flux and zero endpoints gives an
`H¹₀` field satisfying `IsWeakDivergenceSolution`, by integration by parts against
weak derivatives. The coefficient itself need only be continuous.
-/

@[expose] public noncomputable section

open Set MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal

namespace PDE.Elliptic.Homogenization

/-- A differentiable classical flux gives the weak divergence solution predicate. -/
theorem exists_weakSolution_of_flux {b f u : ℝ → ℝ} (hb : Continuous b)
    (hf : Continuous f) (hu : ContDiff ℝ 1 u) (hzero : u 0 = 0) (hone : u 1 = 0)
    (hflux : ∀ x, HasDerivAt (fun y ↦ b y * deriv u y) (-f x) x) :
    ∃ U : H¹₀(unitInterval),
      (baseCoordCLM U : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 unitInterval] (fun x ↦ u (x 0)) ∧
      (∀ i, (derivCoordCLM i U : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 unitInterval]
        (fun x ↦ deriv u (x 0))) ∧
      IsWeakDivergenceSolution (fun _ _ ↦ continuousLiftLp hb ∞) (continuousLiftLp hf 2) U := by
  obtain ⟨U, hU, hdU⟩ := exists_H10_of_endpoints hu hzero hone
  refine ⟨U, hU, hdU, isOpen_unitInterval, fun φ ↦ ?_⟩
  let q : ℝ → ℝ := fun y ↦ b y * deriv u y
  have hq : ContDiff ℝ 1 q := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun x ↦ (hflux x).differentiableAt, ?_⟩
    have he : deriv q = fun x ↦ -f x := funext fun x ↦ (hflux x).deriv
    rw [he]
    exact hf.neg
  have hweak := hasWeakDerivativeOn_of_contDiffAt_one isOpen_unitInterval
    (fun x _ ↦ (hq.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).contDiff).contDiffAt)
    (0 : Fin 1)
  change HasWeakDerivativeOn unitInterval [0] (fun x : ℝ^1 ↦ q (x 0))
    (∂[0] (fun x : ℝ^1 ↦ q (x 0))) at hweak
  have h := hweak.integral_identity φ.1 φ.2
  have hdq (x : ℝ^1) : (∂[0] (fun y : ℝ^1 ↦ q (y 0))) x = -f (x 0) := by
    rw [partialDeriv_lift (hq.differentiable one_ne_zero), (hflux (x 0)).deriv]
  simp only [Fin.sum_univ_one]
  calc
    _ = ∫ x, q (x 0) * (∂[0] φ.1.toFun) x ∂domainMeasure 1 unitInterval := by
      apply integral_congr_ae
      filter_upwards [continuousLiftLp_ae hb ∞, hdU 0] with x hb' hu'
      rw [hb', hu']
    _ = ∫ x, f (x 0) * φ.1.toFun x ∂domainMeasure 1 unitInterval := by
      simpa only [iteratedPartialDeriv, List.length_singleton, pow_one, neg_one_mul,
        hdq, neg_mul, integral_neg, neg_neg, one_mul] using h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [continuousLiftLp_ae hf 2] with x hx
      rw [hx]

end PDE.Elliptic.Homogenization
