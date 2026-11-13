/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightedPaths
public import PDE.Analysis.Evolution.ODE.Linear.Green.Unstable
public import PDE.Analysis.Calculus.Primitive.ExponentialBound

/-!
# Green operators on exponentially weighted paths

The convergent Green integrals define bounded linear operators on the space of
bounded continuous functions representing paths of growth `e^{η|t|}`. For
`0 ≤ η < a`, `stableGreen` is the past integral
`e^{-a t} ∫_{-∞}^t e^{a s} f(s) ds`, the solution of `u' + a u = f` of that growth,
with norm at most `1/(a - η)`. `unstableGreen` is its time reversal, the future
integral solving `u' - a u = f`, with the same bound. For `η > 0`, `centerGreen` is
the primitive `∫₀ᵗ f`, with norm at most `1/η`.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {η a : ℝ}

/-- The stable Green operator in the exponential weight `η`. -/
def stableGreen (hη : 0 ≤ η) (ha : η < a) :
    (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) := by
  let I (u : ℝ →ᵇ E) : C(ℝ, E) :=
    ⟨pastExponentialIntegral a (exponentialLift η u),
      continuous_iff_continuousAt.mpr fun t ↦
        (hasDerivAt_pastExponentialIntegral hη ha (norm_nonneg u)
          (exponentialLift η u).continuous (norm_exponentialLift_le η u) t).continuousAt⟩
  have hI (u : ℝ →ᵇ E) (t : ℝ) :
      ‖I u t‖ ≤ Real.exp (η * |t|) * (‖u‖ / (a - η)) :=
    norm_pastExponentialIntegral_le hη ha (norm_nonneg u) (norm_exponentialLift_le η u) t
  have hi (u : ℝ →ᵇ E) (t : ℝ) :
      IntegrableOn (fun s ↦ Real.exp (a * s) • exponentialLift η u s) (Iic t) :=
    integrableOn_exp_smul_Iic hη ha (norm_nonneg u) (exponentialLift η u).continuous
      (norm_exponentialLift_le η u) t
  let T : (ℝ →ᵇ E) →ₗ[ℝ] (ℝ →ᵇ E) :=
    { toFun u := ofExponentialBound η (I u) (‖u‖ / (a - η)) (hI u)
      map_add' u v := by
        ext t
        change Real.exp (-(η * |t|)) •
            (Real.exp (-(a * t)) • ∫ s in Iic t,
              Real.exp (a * s) • (Real.exp (η * |s|) • (u s + v s))) =
          Real.exp (-(η * |t|)) •
            (Real.exp (-(a * t)) • ∫ s in Iic t,
              Real.exp (a * s) • (Real.exp (η * |s|) • u s)) +
          Real.exp (-(η * |t|)) •
            (Real.exp (-(a * t)) • ∫ s in Iic t,
              Real.exp (a * s) • (Real.exp (η * |s|) • v s))
        simp_rw [smul_add]
        have hadd := integral_add (hi u t) (hi v t)
        change (∫ s in Iic t,
            Real.exp (a * s) • (Real.exp (η * |s|) • u s) +
              Real.exp (a * s) • (Real.exp (η * |s|) • v s)) = _ at hadd
        rw [hadd]
        simp only [smul_add]
        rfl
      map_smul' c u := by
        ext t
        change Real.exp (-(η * |t|)) •
            (Real.exp (-(a * t)) • ∫ s in Iic t,
              Real.exp (a * s) • (Real.exp (η * |s|) • (c • u s))) =
          c • (Real.exp (-(η * |t|)) •
            (Real.exp (-(a * t)) • ∫ s in Iic t,
              Real.exp (a * s) • (Real.exp (η * |s|) • u s)))
        have heq : (fun s ↦ Real.exp (a * s) • (Real.exp (η * |s|) • (c • u s))) =
            fun s ↦ c • (Real.exp (a * s) • (Real.exp (η * |s|) • u s)) := by
          funext s
          rw [smul_comm (Real.exp (η * |s|)) c, smul_comm (Real.exp (a * s)) c]
        rw [heq]
        rw [integral_smul]
        rw [smul_comm (Real.exp (-(a * t))) c, smul_comm (Real.exp (-(η * |t|))) c] }
  exact T.mkContinuous (1 / (a - η)) fun u ↦ by
    change ‖ofExponentialBound η (I u) (‖u‖ / (a - η)) (hI u)‖ ≤
      1 / (a - η) * ‖u‖
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using
      norm_ofExponentialBound_le η (I u) (div_nonneg (norm_nonneg u) (sub_pos.mpr ha).le)
        (hI u)

/-- The stable operator's decoded path is its past integral. -/
@[simp] theorem exponentialLift_stableGreen (hη : 0 ≤ η) (ha : η < a)
    (u : ℝ →ᵇ E) (t : ℝ) :
    exponentialLift η (stableGreen hη ha u) t =
      pastExponentialIntegral a (exponentialLift η u) t := by
  change Real.exp (η * |t|) • (Real.exp (-(η * |t|)) •
    pastExponentialIntegral a (exponentialLift η u) t) = _
  rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

/-- The stable operator norm is bounded by the reciprocal spectral gap. -/
theorem norm_stableGreen_le (hη : 0 ≤ η) (ha : η < a) :
    ‖stableGreen (E := E) hη ha‖ ≤ 1 / (a - η) := by
  unfold stableGreen
  apply LinearMap.mkContinuous_norm_le
  exact one_div_nonneg.mpr (sub_pos.mpr ha).le

/-- The unstable Green operator is the negative time reversal of the stable
operator. -/
def unstableGreen (hη : 0 ≤ η) (ha : η < a) :
    (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) := by
  let R := compContinuousCLM E ℝ (⟨Neg.neg, continuous_neg⟩ : C(ℝ, ℝ))
  exact -((R.comp (stableGreen hη ha)).comp R)

/-- The unstable operator decodes to the future integral. -/
@[simp] theorem exponentialLift_unstableGreen (hη : 0 ≤ η) (ha : η < a)
    (u : ℝ →ᵇ E) (t : ℝ) :
    exponentialLift η (unstableGreen hη ha u) t =
      futureExponentialIntegral a (exponentialLift η u) t := by
  let R := compContinuousCLM E ℝ (⟨Neg.neg, continuous_neg⟩ : C(ℝ, ℝ))
  have heq : (fun s ↦ exponentialLift η u (-s)) =
      exponentialLift η (R u) := by
    funext s
    simp [exponentialLift, R]
  change Real.exp (η * |t|) • (-(stableGreen hη ha (R u) (-t))) = _
  rw [smul_neg, ← abs_neg t]
  change -(exponentialLift η (stableGreen hη ha (R u)) (-t)) = _
  rw [exponentialLift_stableGreen]
  simp only [futureExponentialIntegral, heq]

/-- Time reversal preserves the stable Green norm estimate. -/
theorem norm_unstableGreen_le (hη : 0 ≤ η) (ha : η < a) :
    ‖unstableGreen (E := E) hη ha‖ ≤ 1 / (a - η) := by
  let R := compContinuousCLM E ℝ (⟨Neg.neg, continuous_neg⟩ : C(ℝ, ℝ))
  have hR : ‖R‖ ≤ 1 := norm_compContinuousCLM_le_one _
  change ‖-((R.comp (stableGreen hη ha)).comp R)‖ ≤ _
  rw [norm_neg]
  calc
    ‖(R.comp (stableGreen hη ha)).comp R‖ ≤
        (‖R‖ * ‖stableGreen (E := E) hη ha‖) * ‖R‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg R))
    _ ≤ (1 * (1 / (a - η))) * 1 :=
      mul_le_mul (mul_le_mul hR (norm_stableGreen_le hη ha)
        (norm_nonneg _) zero_le_one) hR (norm_nonneg _) (by positivity)
    _ = 1 / (a - η) := by rw [one_mul, mul_one]

/-- The center Green operator is the primitive with value zero at time zero. -/
def centerGreen (hη : 0 < η) : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) := by
  let I (u : ℝ →ᵇ E) : C(ℝ, E) :=
    ⟨fun t ↦ ∫ s in (0 : ℝ)..t, exponentialLift η u s,
      continuous_iff_continuousAt.mpr fun t ↦
        (intervalIntegral.integral_hasDerivAt_right
          ((exponentialLift η u).continuous.intervalIntegrable 0 t)
          (exponentialLift η u).continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
          (exponentialLift η u).continuous.continuousAt).continuousAt⟩
  have hI (u : ℝ →ᵇ E) (t : ℝ) :
      ‖I u t‖ ≤ Real.exp (η * |t|) * (‖u‖ / η) :=
    norm_integral_zero_to_le_of_exponential_bound hη (norm_nonneg u)
      (norm_exponentialLift_le η u) t
  let T : (ℝ →ᵇ E) →ₗ[ℝ] (ℝ →ᵇ E) :=
    { toFun u := ofExponentialBound η (I u) (‖u‖ / η) (hI u)
      map_add' u v := by
        ext t
        change Real.exp (-(η * |t|)) •
            (∫ s in (0 : ℝ)..t, Real.exp (η * |s|) • (u s + v s)) =
          Real.exp (-(η * |t|)) • (∫ s in (0 : ℝ)..t, Real.exp (η * |s|) • u s) +
            Real.exp (-(η * |t|)) • (∫ s in (0 : ℝ)..t, Real.exp (η * |s|) • v s)
        simp_rw [smul_add]
        have hadd := intervalIntegral.integral_add
          ((exponentialLift η u).continuous.intervalIntegrable (μ := volume) 0 t)
          ((exponentialLift η v).continuous.intervalIntegrable (μ := volume) 0 t)
        change (∫ s in (0 : ℝ)..t, Real.exp (η * |s|) • u s +
          Real.exp (η * |s|) • v s) = _ at hadd
        rw [hadd, smul_add]
        rfl
      map_smul' c u := by
        ext t
        change Real.exp (-(η * |t|)) •
            (∫ s in (0 : ℝ)..t, Real.exp (η * |s|) • (c • u s)) =
          c • (Real.exp (-(η * |t|)) •
            (∫ s in (0 : ℝ)..t, Real.exp (η * |s|) • u s))
        simp_rw [smul_comm (Real.exp (η * |(_ : ℝ)|)) c]
        rw [intervalIntegral.integral_smul, smul_comm] }
  exact T.mkContinuous (1 / η) fun u ↦ by
    change ‖ofExponentialBound η (I u) (‖u‖ / η) (hI u)‖ ≤ 1 / η * ‖u‖
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using
      norm_ofExponentialBound_le η (I u) (div_nonneg (norm_nonneg u) hη.le) (hI u)

/-- The center operator decodes to its oriented primitive. -/
@[simp] theorem exponentialLift_centerGreen (hη : 0 < η) (u : ℝ →ᵇ E) (t : ℝ) :
    exponentialLift η (centerGreen hη u) t =
      ∫ s in (0 : ℝ)..t, exponentialLift η u s := by
  change Real.exp (η * |t|) • (Real.exp (-(η * |t|)) •
    (∫ s in (0 : ℝ)..t, exponentialLift η u s)) = _
  rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

/-- The center primitive has norm at most the reciprocal exponential weight. -/
theorem norm_centerGreen_le (hη : 0 < η) :
    ‖centerGreen (E := E) hη‖ ≤ 1 / η := by
  unfold centerGreen
  apply LinearMap.mkContinuous_norm_le
  exact one_div_nonneg.mpr hη.le

end PDE.Analysis.Evolution
