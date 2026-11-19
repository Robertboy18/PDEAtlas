/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.RegularizedHessian
import CAS.ExactTactic
import PDE.FDeriv.Calculus

/-!
# Polar truncations of the Newtonian Hessian

Vanishing of a compactly supported source at the pole removes one power of
the Hessian singularity. Dominated convergence identifies its classical
pairing, while Green identities and polar coordinates identify spherical
truncations for general test functions.
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

open MeasureTheory Filter LineDeriv TopologicalSpace SobolevSpace
open scoped Distributions ENNReal Topology
open PDE.Analysis

namespace PotentialTheory

/-- For a compact C¹ source that vanishes at the pole, regularized Hessians
converge to the absolutely integrable classical pairing. The cancellation
removes one power of the singularity, leaving the local majorant `|X|⁻⁴`. -/
theorem fiveDimensionalGammaRegularized_hessian_pairing_tendsto_of_zero
    (i j : Fin 5) (g : ℝ^5 → ℝ) (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (hg0 : g 0 = 0) :
    Integrable (fun X : ℝ^5 ↦
      iteratedPartialDeriv (n := 5) [j, i] (fundamentalSolution 5) X * g X) ∧
      Tendsto (fun n : ℕ ↦ ∫ X : ℝ^5,
        iteratedPartialDeriv (n := 5) [j, i]
          (fiveDimensionalGammaRegularized ((n + 1 : ℝ)⁻¹)) X * g X)
        atTop (𝓝 (∫ X : ℝ^5,
          iteratedPartialDeriv (n := 5) [j, i] (fundamentalSolution 5) X * g X)) := by
  let ε : ℕ → ℝ := fun n ↦ ((n + 1 : ℝ)⁻¹)
  let F : ℕ → ℝ^5 → ℝ := fun n X ↦
    iteratedPartialDeriv (n := 5) [j, i] (fiveDimensionalGammaRegularized (ε n)) X * g X
  let f : ℝ^5 → ℝ := fun X ↦
    iteratedPartialDeriv (n := 5) [j, i] (fundamentalSolution 5) X * g X
  obtain ⟨C, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by simp)
  obtain ⟨R, -, hgzero⟩ := hgc.exists_pos_le_norm
  let K : ℝ := 18 / (8 * Real.pi ^ 2) * C
  have hK : 0 ≤ K := by simp only [K]; positivity
  let bound : ℝ^5 → ℝ := (Metric.ball 0 R).indicator fun X ↦ K * ‖X‖ ^ (-4 : ℝ)
  have hεpos (n : ℕ) : 0 < ε n := inv_pos.2 n.cast_add_one_pos
  have hεlim : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨by simpa [ε, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ), .of_forall hεpos⟩
  have hFmeas (n : ℕ) : AEStronglyMeasurable (F n) volume :=
    ((PDE.contDiff_iteratedPartialDeriv_of_le (k := 2)
      ((fiveDimensionalGammaRegularized_contDiff _ (hεpos n).ne').of_le (by simp)) [j, i]
        (by simp)).continuous.mul hg.continuous).aestronglyMeasurable
  have hlim : ∀ᵐ X ∂volume, Tendsto (fun n ↦ F n X) atTop (𝓝 (f X)) := by
    filter_upwards [(Set.countable_singleton (0 : ℝ^5)).ae_notMem volume] with X hX
    exact ((fiveDimensionalGammaRegularized_hessian_tendsto i j X hX).comp hεlim).mul_const (g X)
  have hboundInt : Integrable bound volume := by
    refine (integrable_indicator_iff measurableSet_ball).2 <|
      integrableOn_ball_of_norm_le_rpow (C := K) (by norm_num)
        (by norm_num : (4 : ℝ) < Module.finrank ℝ ℝ^5) (.of_forall fun X ↦ ?_)
        (measurable_const.mul (measurable_norm.pow_const (-4 : ℝ))).aestronglyMeasurable
    rw [Real.norm_of_nonneg (by positivity)]
  have hbound (n : ℕ) : ∀ᵐ X ∂volume, ‖F n X‖ ≤ bound X := by
    filter_upwards [(Set.countable_singleton (0 : ℝ^5)).ae_notMem volume] with X hX
    by_cases hXR : X ∈ Metric.ball (0 : ℝ^5) R
    · have hH := fiveDimensionalGammaRegularized_hessian_bound (ε n) (hεpos n).ne' i j X hX
      have hgX : |g X| ≤ C * ‖X‖ := by simpa [hg0] using hLip.norm_sub_le X 0
      simp only [F, bound, Set.indicator_of_mem hXR, Real.norm_eq_abs, abs_mul]
      calc _ ≤ 18 / (8 * Real.pi ^ 2) * ‖X‖ ^ (-5 : ℝ) * (C * ‖X‖) := by gcongr
        _ = K * ‖X‖ ^ (-4 : ℝ) := by
          have := norm_pos_iff.2 hX
          simp only [K]
          cas
    · simp [F, bound, hXR, hgzero X (by simpa using hXR)]
  have hfbound : ∀ᵐ X ∂volume, ‖f X‖ ≤ bound X := by
    filter_upwards [hlim, ae_all_iff.2 hbound] with X hlimX hboundX
    exact le_of_tendsto hlimX.norm (.of_forall hboundX)
  exact ⟨hboundInt.mono' (aestronglyMeasurable_of_tendsto_ae atTop hFmeas hlim) hfbound,
    tendsto_integral_of_dominated_convergence bound hFmeas hboundInt hbound hlim⟩

/-- If the test function vanishes at the pole, the classical Hessian kernel is
absolutely integrable and no local Dirac correction remains.  The proof uses
the uniform regularized-Hessian estimate and the locally integrable majorant
`‖X‖⁻⁴` in five dimensions.
-/
theorem fundamentalSolution_five_distributionalHessian_eq_classical_of_zero
    (i j : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ))
    (hφ0 : φ.toFun 0 = 0) :
    Integrable (fun X : ℝ^5 ↦
      iteratedPartialDeriv (n := 5) [j, i] (fundamentalSolution 5) X *
        φ.toFun X) ∧
      (∫ X : ℝ^5,
          (fundamentalSolution 5) X *
            iteratedPartialDeriv (n := 5) [i, j] φ.toFun X) =
        ∫ X : ℝ^5,
          iteratedPartialDeriv (n := 5) [j, i] (fundamentalSolution 5) X *
            φ.toFun X := by
  obtain ⟨hint, hlim⟩ :=
    fiveDimensionalGammaRegularized_hessian_pairing_tendsto_of_zero i j φ.toFun
      (φ.contDiff.of_le (by simp)) φ.hasCompactSupport hφ0
  refine ⟨hint, ?_⟩
  exact tendsto_nhds_unique
    (fiveDimensionalGammaRegularized_distributionalHessian_tendsto i j φ) hlim

/-- Pointwise Green identity for the two scalar flux components used in the
punctured-domain Hessian calculation.  It holds at every point away from the
Newtonian pole.
-/
theorem fundamentalSolution_five_greenIdentity_pointwise
    (i j : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ))
    (X : ℝ^5) (hX : X ≠ 0) :
    (∂[i] (fun Y ↦ (fundamentalSolution 5) Y *
        (∂[j] φ.toFun) Y)) X -
      (∂[j] (fun Y ↦
        (∂[i] (fundamentalSolution 5)) Y * φ.toFun Y)) X =
      (fundamentalSolution 5) X *
          iteratedPartialDeriv (n := 5) [i, j] φ.toFun X -
        iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X *
          φ.toFun X := by
  have hΓ : ContDiffAt ℝ 2 (fundamentalSolution 5) X :=
    (contDiffAt_fundamentalSolution 5 X hX).of_le (WithTop.coe_le_coe.mpr le_top)
  have hφ : ContDiffAt ℝ 2 φ.toFun X := φ.contDiff.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [PDE.partialDeriv_mul (hΓ.differentiableAt (by norm_num))
      ((PDE.contDiffAt_partialDeriv 1 hφ j).differentiableAt (by norm_num)),
    PDE.partialDeriv_mul ((PDE.contDiffAt_partialDeriv 1 hΓ i).differentiableAt (by norm_num))
      (hφ.differentiableAt (by norm_num))]
  simp only [iteratedPartialDeriv]
  rw [PDE.partialDeriv_partialDeriv_comm_at j i hΓ]
  ring

/-- At every fixed positive inner radius, the classical Hessian kernel paired
with a test function is absolutely integrable on the punctured region.
-/
theorem fundamentalSolution_five_classicalHessian_integrableOn
    (ε : ℝ) (hε : 0 < ε) (i j : Fin 5)
    (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    IntegrableOn (fun X : ℝ^5 ↦
      iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X *
        φ.toFun X) {X | ε < ‖X‖} := by
  have hK : IsCompact (tsupport φ.toFun ∩ {X : ℝ^5 | ε / 2 ≤ ‖X‖}) :=
    φ.hasCompactSupport.inter_right (isClosed_le continuous_const continuous_norm)
  refine IntegrableOn.of_forall_sdiff_eq_zero (ContinuousOn.integrableOn_compact hK fun X hX ↦ ?_)
    (measurableSet_lt measurable_const measurable_norm) fun X hX ↦ ?_
  · have hΓ : ContDiffAt ℝ 2 (fundamentalSolution 5) X :=
      (contDiffAt_fundamentalSolution 5 X (norm_pos_iff.1 ((half_pos hε).trans_le hX.2))).of_le
        (WithTop.coe_le_coe.mpr le_top)
    exact ((PDE.contDiffAt_partialDeriv 0 (PDE.contDiffAt_partialDeriv 1 hΓ j) i).continuousAt.mul
      φ.continuous.continuousAt).continuousWithinAt
  · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hX.2 ⟨h, (half_le_self hε.le).trans hX.1.le⟩,
      mul_zero]

/-- Polar coordinates identify each fixed spherical truncation of the
classical Hessian with the radial-angular principal-value expression.
-/
theorem fundamentalSolution_five_classicalHessian_polar
    (ε : ℝ) (hε : 0 < ε) (i j : Fin 5)
    (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    (∫ X in {X : ℝ^5 | ε < ‖X‖},
      iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X *
        φ.toFun X) =
      ∫ r in Set.Ioi ε, r⁻¹ *
        ∫ ω : Metric.sphere (0 : ℝ^5) 1,
          ((15 / (8 * Real.pi ^ 2)) *
              (ω : ℝ^5) i *
              (ω : ℝ^5) j -
            (3 / (8 * Real.pi ^ 2)) * (if i = j then 1 else 0)) *
            φ.toFun (r • (ω : ℝ^5))
          ∂(volume : Measure ℝ^5).toSphere := by
  let radial : ℝ → ℝ := fun r ↦ r⁻¹ *
    ∫ ω : Metric.sphere (0 : ℝ^5) 1,
      ((15 / (8 * Real.pi ^ 2)) * (ω : ℝ^5) i * (ω : ℝ^5) j -
        (3 / (8 * Real.pi ^ 2)) * (if i = j then 1 else 0)) * φ.toFun (r • (ω : ℝ^5))
      ∂(volume : Measure ℝ^5).toSphere
  have hS : MeasurableSet {X : ℝ^5 | ε < ‖X‖} := measurableSet_lt measurable_const measurable_norm
  calc _ = ∫ r in Set.Ioi 0, (Set.Ioi ε).indicator radial r := by
        rw [← integral_indicator hS, PDE.Analysis.integral_polar_addHaar_iterated _ _
          ((integrable_indicator_iff hS).2
            (fundamentalSolution_five_classicalHessian_integrableOn ε hε i j φ))]
        refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ ?_
        have hnorm (ω : Metric.sphere (0 : ℝ^5) 1) : ‖r • (ω : ℝ^5)‖ = r := by
          simp [norm_smul, abs_of_pos hr]
        by_cases hεr : ε < r
        · rw [Set.indicator_of_mem (s := Set.Ioi ε) hεr]
          simp only [radial, smul_eq_mul]
          rw [← integral_const_mul, ← integral_const_mul]
          refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
          have hω : r • (ω : ℝ^5) ≠ 0 := norm_ne_zero_iff.1 (by rw [hnorm]; exact hr.ne')
          have hmem : r • (ω : ℝ^5) ∈ {X : ℝ^5 | ε < ‖X‖} := by simpa [hnorm] using hεr
          dsimp only
          rw [Set.indicator_of_mem hmem, fundamentalSolution_five_iteratedPartialDeriv_two j i _ hω,
            hnorm]
          simp only [PiLp.smul_apply, smul_eq_mul, finrank_euclideanSpace_fin, @eq_comm _ j i]
          rw [show (-7 : ℝ) = -(7 : ℕ) by norm_num, show (-5 : ℝ) = -(5 : ℕ) by norm_num,
            Real.rpow_neg hr.le, Real.rpow_neg hr.le, Real.rpow_natCast, Real.rpow_natCast]
          field_simp
        · simp [hnorm, hεr]
    _ = _ := by
      rw [setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi, sup_eq_right.2 hε.le]

/-- The classical Hessian kernel is measurable, including its assigned value at
zero. Away from zero this follows from its explicit radial formula. -/
theorem measurable_fundamentalSolution_five_hessian (i j : Fin 5) :
    Measurable (iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5)) := by
  apply measurable_of_continuousOn_compl_singleton (0 : ℝ^5)
  have hp (a : ℝ) : ContinuousOn (fun X : ℝ^5 ↦ ‖X‖ ^ a) {0}ᶜ :=
    continuous_norm.continuousOn.rpow_const fun X hX ↦
      Or.inl (norm_ne_zero_iff.mpr (by simpa only [Set.mem_compl_iff,
        Set.mem_singleton_iff] using hX))
  have hj : Continuous (fun X : ℝ^5 ↦ X j) := by fun_prop
  have hi : Continuous (fun X : ℝ^5 ↦ X i) := by fun_prop
  have hformula : ContinuousOn (fun X : ℝ^5 ↦
      (15 / (8 * Real.pi ^ 2)) * X j * X i * ‖X‖ ^ (-7 : ℝ) -
        (3 / (8 * Real.pi ^ 2)) * (if j = i then 1 else 0) * ‖X‖ ^ (-5 : ℝ)) {0}ᶜ :=
    (((continuousOn_const.mul hj.continuousOn).mul hi.continuousOn).mul
      (hp (-7))).sub (continuousOn_const.mul (hp (-5)))
  apply hformula.congr
  intro X hX
  exact fundamentalSolution_five_iteratedPartialDeriv_two j i X (by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hX)

end PotentialTheory
