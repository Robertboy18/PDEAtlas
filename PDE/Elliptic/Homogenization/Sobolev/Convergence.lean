/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.WeakCompactness.Identification
public import PDE.Elliptic.Homogenization.Convergence
public import PDE.Elliptic.Homogenization.Sobolev.Solutions

/-!
# Weak Sobolev convergence and strong corrected-gradient convergence

The uniform error estimate for the explicit interval solutions transfers to the
value coordinates of their `H¹₀` representatives. Thus the variational
solutions converge strongly in `L²`, with order-`|ε|` error. Uniform ellipticity and
the Poincaré inequality give a uniform `H¹₀` bound; injectivity of the value
coordinate then identifies the weak Sobolev limit. The cell correction also gives
strong `L²` convergence of the corrected gradient error, with order-`|ε|` rate.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal Topology
namespace PDE.Elliptic.Homogenization.PeriodicMedium

/-- The value coordinates of the weak solutions have an order-`|ε|` error bound. -/
theorem exists_sobolevSolution_L2_error_bound (a : PeriodicMedium) {f : ℝ → ℝ}
    (hf : Continuous f) :
    ∃ C > 0, ∃ ε₀ > 0, ∀ ε : ℝ, ε ≠ 0 → |ε| ≤ ε₀ →
      ‖baseCoordCLM (a.sobolevSolution hf ε) -
        baseCoordCLM (a.homogenizedSobolevSolution hf)‖ ≤ C * |ε| := by
  let := isFiniteMeasure_domainMeasure_of_isBounded isBounded_unitInterval
  obtain ⟨C, hC, ε₀, hε₀, hbound⟩ := a.exists_solution_error_bound hf
  let K : ℝ := (measureUnivNNReal (domainMeasure 1 unitInterval) : ℝ) ^
    (2 : ℝ≥0∞).toReal⁻¹
  have hK : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  refine ⟨(K + 1) * C, mul_pos (by positivity) hC, ε₀, hε₀, fun ε hε hs ↦ ?_⟩
  have hb : ‖baseCoordCLM (a.sobolevSolution hf ε) -
      baseCoordCLM (a.homogenizedSobolevSolution hf)‖ ≤ K * (C * |ε|) := by
    apply Lp.norm_le_of_ae_bound (mul_nonneg hC.le (abs_nonneg ε))
    filter_upwards [Lp.coeFn_sub (baseCoordCLM (a.sobolevSolution hf ε))
      (baseCoordCLM (a.homogenizedSobolevSolution hf)),
      a.sobolevSolution_base_ae hf ε, a.homogenizedSobolevSolution_base_ae hf,
      ae_restrict_mem isOpen_unitInterval.measurableSet] with x hx hu hv hxΩ
    rw [hx, Pi.sub_apply, hu, hv, Real.norm_eq_abs]
    exact hbound ε hε hs (x 0) ⟨hxΩ.1.le, hxΩ.2.le⟩
  calc
    _ ≤ K * (C * |ε|) := hb
    _ ≤ (K + 1) * (C * |ε|) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (mul_nonneg hC.le (abs_nonneg ε))
    _ = _ := by ring

/-- The canonical weak solutions converge strongly in their `L²` value coordinates. -/
theorem tendsto_sobolevSolution_L2 (a : PeriodicMedium) {f : ℝ → ℝ} (hf : Continuous f) :
    Tendsto (fun ε ↦ baseCoordCLM (a.sobolevSolution hf ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (baseCoordCLM (a.homogenizedSobolevSolution hf))) := by
  obtain ⟨C, hC, ε₀, hε₀, hb⟩ := a.exists_sobolevSolution_L2_error_bound hf
  rw [Metric.tendsto_nhds]
  intro η hη
  have ht : Tendsto (fun ε : ℝ ↦ |ε|) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hm : 0 < min ε₀ (η / C) := lt_min hε₀ (div_pos hη hC)
  filter_upwards [self_mem_nhdsWithin, ht.eventually (gt_mem_nhds hm)] with ε hε hs
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (hb ε (ne_of_gt hε) (lt_of_lt_of_le hs (min_le_left _ _)).le)
  have h := (lt_div_iff₀ hC).mp (lt_of_lt_of_le hs (min_le_right _ _))
  simpa only [mul_comm] using h

/-- Ellipticity and the zero-boundary Poincaré inequality bound the entire solution family
in the Sobolev norm, uniformly in the microscopic scale. -/
theorem exists_sobolevSolution_norm_bound (a : PeriodicMedium) {f : ℝ → ℝ}
    (hf : Continuous f) :
    ∃ M : ℝ, ∀ ε : ℝ, ‖a.sobolevSolution hf ε‖ ≤ M := by
  obtain ⟨α, hα, hEll⟩ := a.exists_aeUniformlyElliptic_matrixCoefficient
  obtain ⟨c, hc, hdir⟩ := dirichletForm_isCoercive zero_lt_one isBounded_unitInterval
  let ell := loadFunctional (continuousLiftLp hf 2)
  refine ⟨‖ell‖ / (α * c), fun ε ↦ ?_⟩
  apply PDE.Analysis.Variational.norm_le_dual_norm_div_of_pairing ell (α * c)
    (mul_pos hα hc)
  have heq := (isWeakSolution_iff_isWeakDivergenceSolution isOpen_unitInterval
    (a.matrixCoefficient ε) (continuousLiftLp hf 2) (a.sobolevSolution hf ε)).2
      (a.sobolevSolution_isWeakDivergenceSolution hf ε)
  calc
    _ = α * (c * ‖a.sobolevSolution hf ε‖ * ‖a.sobolevSolution hf ε‖) := by ring
    _ ≤ α * dirichletForm (a.sobolevSolution hf ε) (a.sobolevSolution hf ε) :=
      mul_le_mul_of_nonneg_left (hdir _) hα.le
    _ ≤ variableCoeffForm (multiplicationCoefficientOperator (a.matrixCoefficient ε))
        (a.sobolevSolution hf ε) (a.sobolevSolution hf ε) :=
      (integratedElliptic_multiplication_of_ae (a.matrixCoefficient ε) (hEll ε)).2 _
    _ = ell (a.sobolevSolution hf ε) := heq _

/-- The zero-Dirichlet weak solutions converge weakly in `H¹₀`. -/
theorem tendsto_sobolevSolution_weak (a : PeriodicMedium) {f : ℝ → ℝ}
    (hf : Continuous f) :
    Tendsto (fun ε ↦ toWeakSpace ℝ H¹₀(unitInterval) (a.sobolevSolution hf ε))
      (𝓝[>] (0 : ℝ))
      (𝓝 (toWeakSpace ℝ H¹₀(unitInterval) (a.homogenizedSobolevSolution hf))) := by
  obtain ⟨M, hM⟩ := a.exists_sobolevSolution_norm_bound hf
  apply PDE.Analysis.WeakCompactness.tendsto_of_injective_map
    baseCoordCLM (baseCoordCLM_injective isOpen_unitInterval)
    (a.sobolevSolution hf) (a.homogenizedSobolevSolution hf)
    (isBounded_iff_forall_norm_le.mpr ⟨M, by rintro _ ⟨ε, rfl⟩; exact hM ε⟩)
  exact ((toWeakSpaceCLM ℝ _).continuous.tendsto _).comp (a.tendsto_sobolevSolution_L2 hf)

/-- The first-order cell correction of the effective gradient, as an `L²` field. -/
def correctedSobolevGradient (a : PeriodicMedium) {f : ℝ → ℝ}
    (hf : Continuous f) (ε : ℝ) : DerivLp 1 2 unitInterval :=
  continuousLiftLp
    (((a.contDiff_corrector.continuous_deriv_one.comp
      (continuous_id.div_const ε)).const_add 1).mul
      (a.contDiff_homogenizedSolution hf).continuous_deriv_one) 2

/-- The correction uses the derivative coordinate of the canonical effective solution. -/
theorem correctedSobolevGradient_ae (a : PeriodicMedium) {f : ℝ → ℝ}
    (hf : Continuous f) (ε : ℝ) (i : Fin 1) :
    (a.correctedSobolevGradient hf ε : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 unitInterval]
      fun x ↦ (1 + deriv a.corrector (x 0 / ε)) *
        (derivCoordCLM i (a.homogenizedSobolevSolution hf) : ℝ^1 → ℝ) x := by
  filter_upwards [continuousLiftLp_ae
    (((a.contDiff_corrector.continuous_deriv_one.comp
      (continuous_id.div_const ε)).const_add 1).mul
      (a.contDiff_homogenizedSolution hf).continuous_deriv_one) 2,
    a.homogenizedSobolevSolution_deriv_ae hf i] with x hx hu
  rw [hu]
  exact hx

/-- Subtracting the cell-corrected effective gradient gives an order-`|ε|` `L²` error. -/
theorem exists_sobolevSolution_gradient_error_bound (a : PeriodicMedium) {f : ℝ → ℝ}
    (hf : Continuous f) :
    ∃ C > 0, ∃ ε₀ > 0, ∀ ε : ℝ, ε ≠ 0 → |ε| ≤ ε₀ → ∀ i : Fin 1,
      ‖derivCoordCLM i (a.sobolevSolution hf ε) -
        a.correctedSobolevGradient hf ε‖ ≤ C * |ε| := by
  let := isFiniteMeasure_domainMeasure_of_isBounded isBounded_unitInterval
  obtain ⟨C, hC, ε₀, hε₀, hbound⟩ := a.exists_gradient_corrector_error_bound hf
  let K : ℝ := (measureUnivNNReal (domainMeasure 1 unitInterval) : ℝ) ^
    (2 : ℝ≥0∞).toReal⁻¹
  have hK : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  refine ⟨(K + 1) * C, mul_pos (by positivity) hC, ε₀, hε₀, fun ε hε hs i ↦ ?_⟩
  have hb : ‖derivCoordCLM i (a.sobolevSolution hf ε) -
      a.correctedSobolevGradient hf ε‖ ≤ K * (C * |ε|) := by
    apply Lp.norm_le_of_ae_bound (mul_nonneg hC.le (abs_nonneg ε))
    filter_upwards [Lp.coeFn_sub (derivCoordCLM i (a.sobolevSolution hf ε))
      (a.correctedSobolevGradient hf ε), a.sobolevSolution_deriv_ae hf ε i,
      a.correctedSobolevGradient_ae hf ε i, a.homogenizedSobolevSolution_deriv_ae hf i,
      ae_restrict_mem isOpen_unitInterval.measurableSet] with x hx hu hc hv hxΩ
    rw [hx, Pi.sub_apply, hu, hc, hv, Real.norm_eq_abs]
    exact hbound ε hε hs (x 0) ⟨hxΩ.1.le, hxΩ.2.le⟩
  calc
    _ ≤ K * (C * |ε|) := hb
    _ ≤ (K + 1) * (C * |ε|) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (mul_nonneg hC.le (abs_nonneg ε))
    _ = _ := by ring

/-- The corrected weak gradient error tends strongly to zero in `L²`. -/
theorem tendsto_sobolevSolution_gradient_error (a : PeriodicMedium) {f : ℝ → ℝ}
    (hf : Continuous f) (i : Fin 1) :
    Tendsto (fun ε ↦ derivCoordCLM i (a.sobolevSolution hf ε) -
      a.correctedSobolevGradient hf ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, hC, ε₀, hε₀, hb⟩ := a.exists_sobolevSolution_gradient_error_bound hf
  rw [Metric.tendsto_nhds]
  intro η hη
  have ht : Tendsto (fun ε : ℝ ↦ |ε|) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hm : 0 < min ε₀ (η / C) := lt_min hε₀ (div_pos hη hC)
  filter_upwards [self_mem_nhdsWithin, ht.eventually (gt_mem_nhds hm)] with ε hε hs
  rw [dist_zero_right]
  apply lt_of_le_of_lt (hb ε (ne_of_gt hε) (lt_of_lt_of_le hs (min_le_left _ _)).le i)
  have h := (lt_div_iff₀ hC).mp (lt_of_lt_of_le hs (min_le_right _ _))
  simpa only [mul_comm] using h

end PDE.Elliptic.Homogenization.PeriodicMedium
