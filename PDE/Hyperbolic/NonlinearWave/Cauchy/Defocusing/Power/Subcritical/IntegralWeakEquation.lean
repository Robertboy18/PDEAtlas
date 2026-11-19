/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RetardedPairing
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.TestedKernel
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import PDE.FDeriv.Laplacian.Congruence
import PDE.FDeriv.Laplacian.Continuity
import CAS.ExactTactic

/-!
# The weak wave equation of the physical retarded field

Compact spatial testing moves both time derivatives onto the smooth wave
kernel. A continuous forcing satisfies the tested wave equation without derivatives
of the forcing. Finite propagation first permits a compact spatial cutoff on a neighborhood of the
evaluation time.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology unitInterval Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- The compact spatial pairing of the Duhamel field is an oriented integral
in physical source time, with the spherical average acting on the test. -/
theorem integral_oddDuhamelSolution_mul_eq_interval {F : ℝ × ℝ^3 → ℝ} (hF : Continuous F)
    {φ : ℝ^3 → ℝ} (hφ : Continuous φ) (hφs : HasCompactSupport φ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : ℝ^3, oddDuhamelSolution 0 (fun z : ℝ^4 ↦ F (timeSpaceContinuousLinearEquiv 3 z))
      (timeSpaceCons t x) * φ x) = ∫ s in (0 : ℝ)..t, (t - s) * ∫ x : ℝ^3,
      F (s, x) * unitSphereAverage 3 φ x (t - s) := by
  let g : ℝ → ℝ := fun s ↦ (t - s) *
    ∫ x : ℝ^3, F (s, x) * unitSphereAverage 3 φ x (t - s)
  have hscale : t * (∫ s in (0 : ℝ)..1, g (t * s)) = ∫ s in (0 : ℝ)..t, g s := by
    simpa only [smul_eq_mul, mul_zero, mul_one] using
      intervalIntegral.smul_integral_comp_mul_left g t (a := 0) (b := 1)
  rw [integral_oddDuhamelSolution_mul_eq hF hφ hφs ht]
  change t ^ 2 * (∫ s : I, (1 - (s : ℝ)) *
    ∫ x : ℝ^3, F (t * (s : ℝ), x) *
      unitSphereAverage 3 φ x (t * (1 - (s : ℝ)))) = ∫ s in (0 : ℝ)..t, g s
  rw [← hscale, integral_unitInterval (fun s : ℝ ↦ (1 - s) *
    ∫ x : ℝ^3, F (t * s, x) * unitSphereAverage 3 φ x (t * (1 - s))),
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  have hage : t - t * s = t * (1 - s) := by cas
  simp only [g, hage]
  cas

/-- A continuous forcing with uniformly compact spatial support gives an
Duhamel field satisfying the wave equation after every compact C²
spatial test. -/
theorem hasDerivAt_deriv_integral_oddDuhamelSolution_mul_of_uniform_support {F : ℝ × ℝ^3 → ℝ}
    (hF : Continuous F) {S : Set (ℝ^3)} (hS : IsCompact S) (hFs : ∀ s x, x ∉ S → F (s, x) = 0)
    {φ : ℝ^3 → ℝ} (hφ : ContDiff ℝ 2 φ) (hφs : HasCompactSupport φ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deriv (fun b ↦ ∫ x : ℝ^3,
      oddDuhamelSolution 0 (fun z : ℝ^4 ↦ F (timeSpaceContinuousLinearEquiv 3 z))
        (timeSpaceCons b x) * φ x))
      ((∫ x : ℝ^3, F (t, x) * φ x) +
        ∫ x : ℝ^3,
          oddDuhamelSolution 0 (fun z : ℝ^4 ↦ F (timeSpaceContinuousLinearEquiv 3 z))
            (timeSpaceCons t x) * laplacian φ x) t := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let μ : Measure S := (volume : Measure (ℝ^3)).comap Subtype.val
  let : IsFiniteMeasureOnCompacts μ :=
    MeasureTheory.IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
      (MeasurableEmbedding.subtype_coe hS.measurableSet)
  have hsub (s : ℝ) (q : ℝ^3 → ℝ) :
      (∫ y : S, F (s, y) * q y ∂μ) = ∫ x : ℝ^3, F (s, x) * q x := by
    change (∫ y : S, F (s, y) * q y ∂Measure.comap Subtype.val volume) = _
    rw [integral_subtype_comap hS.measurableSet (fun x : ℝ^3 ↦ F (s, x) * q x)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [hFs s x hx, zero_mul]
  let J : (ℝ^3 → ℝ) → ℝ → ℝ := fun ψ b ↦ ∫ s in (0 : ℝ)..b,
    ∫ y : S, F (s, y) * ((b - s) * unitSphereAverage 3 ψ y (b - s)) ∂μ
  have hpair {ψ : ℝ^3 → ℝ} (hψ : Continuous ψ) (hψs : HasCompactSupport ψ)
      {b : ℝ} (hb : 0 ≤ b) :
      (∫ x : ℝ^3,
        oddDuhamelSolution 0 (fun z : ℝ^4 ↦ F (timeSpaceContinuousLinearEquiv 3 z))
          (timeSpaceCons b x) * ψ x) = J ψ b := by
    rw [integral_oddDuhamelSolution_mul_eq_interval hF hψ hψs hb]
    apply intervalIntegral.integral_congr
    intro s _
    change (b - s) * (∫ x : ℝ^3, F (s, x) * unitSphereAverage 3 ψ x (b - s)) =
      ∫ y : S, F (s, y) * ((b - s) * unitSphereAverage 3 ψ y (b - s)) ∂μ
    rw [hsub s (fun x ↦ (b - s) * unitSphereAverage 3 ψ x (b - s))]
    simp_rw [mul_left_comm (F (s, _)) (b - s)]
    rw [integral_const_mul]
  have hnear : (fun b ↦ ∫ x : ℝ^3,
      oddDuhamelSolution 0 (fun z : ℝ^4 ↦ F (timeSpaceContinuousLinearEquiv 3 z))
        (timeSpaceCons b x) * φ x) =ᶠ[𝓝 t] J φ := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with b hb
    exact hpair hφ.continuous hφs hb.le
  have he := hasDerivAt_deriv_retarded_spherical_pairing (μ := μ)
    (c := fun p : ℝ × S ↦ F (p.1, p.2))
    (hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    continuous_subtype_val hφ ht
  change HasDerivAt (deriv (J φ)) _ t at he
  rw [hsub] at he
  rw [hpair hφ.continuous_coordinate_laplacian hφs.coordinate_laplacian ht.le]
  exact he.congr_of_eventuallyEq hnear.deriv


private theorem unitSphereAverage_eq_zero_outside {φ : ℝ^3 → ℝ} {R : ℝ}
    (hφ : ∀ x, R ≤ ‖x‖ → φ x = 0) {x : ℝ^3} {r : ℝ} (hx : R + |r| < ‖x‖) :
    unitSphereAverage 3 φ x r = 0 := by
  have hz (ω : Metric.sphere (0 : ℝ^3) 1) : φ (x + r • (ω : ℝ^3)) = 0 := by
    apply hφ
    have hn : ‖r • (ω : ℝ^3)‖ = |r| := by
      rw [norm_smul, Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp ω.property, mul_one]
    have hb := norm_sub_norm_le x (-r • (ω : ℝ^3))
    simp only [neg_smul, norm_neg, sub_neg_eq_add, hn] at hb
    linarith
  simp only [unitSphereAverage, hz, integral_zero, zero_div]

private theorem integral_oddDuhamelSolution_mul_eq_of_spatial_agreement {F G : ℝ × ℝ^3 → ℝ}
    (hF : Continuous F) (hG : Continuous G) {φ : ℝ^3 → ℝ} (hφ : Continuous φ)
    (hφs : HasCompactSupport φ) {R T : ℝ} (hφzero : ∀ x, R ≤ ‖x‖ → φ x = 0)
    (hFG : ∀ s ∈ Icc 0 T, ∀ x, ‖x‖ ≤ R + T → F (s, x) = G (s, x)) {b : ℝ} (hb : b ∈ Icc 0 T) :
    (∫ x : ℝ^3,
      oddDuhamelSolution 0 (fun z : ℝ^4 ↦ F (timeSpaceContinuousLinearEquiv 3 z))
        (timeSpaceCons b x) * φ x) =
      ∫ x : ℝ^3,
        oddDuhamelSolution 0 (fun z : ℝ^4 ↦ G (timeSpaceContinuousLinearEquiv 3 z))
          (timeSpaceCons b x) * φ x := by
  rw [integral_oddDuhamelSolution_mul_eq_interval hF hφ hφs hb.1,
    integral_oddDuhamelSolution_mul_eq_interval hG hφ hφs hb.1]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc 0 b := by simpa only [uIcc_of_le hb.1] using hs
  change (b - s) * (∫ x : ℝ^3, F (s, x) * unitSphereAverage 3 φ x (b - s)) =
    (b - s) * (∫ x : ℝ^3, G (s, x) * unitSphereAverage 3 φ x (b - s))
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : ‖x‖ ≤ R + T
  · rw [hFG s ⟨hs'.1, hs'.2.trans hb.2⟩ x hx]
  · have hz := unitSphereAverage_eq_zero_outside hφzero
      (x := x) (r := b - s) (by
        rw [abs_of_nonneg (sub_nonneg.mpr hs'.2)]
        have hlarge := lt_of_not_ge hx
        linarith [hs'.1, hb.2])
    rw [hz, mul_zero, mul_zero]

/-- The retarded field of any continuous forcing satisfies the wave
identity after compact C² spatial testing. Finite propagation permits a compact
spatial cutoff of the source before taking the two time derivatives. -/
theorem hasDerivAt_deriv_integral_oddDuhamelSolution_mul {F : ℝ × ℝ^3 → ℝ} (hF : Continuous F)
    {φ : ℝ^3 → ℝ} (hφ : ContDiff ℝ 2 φ) (hφs : HasCompactSupport φ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deriv (fun b ↦ ∫ x : ℝ^3,
      oddDuhamelSolution 0 (fun z : ℝ^4 ↦ F (timeSpaceContinuousLinearEquiv 3 z))
        (timeSpaceCons b x) * φ x))
      ((∫ x : ℝ^3, F (t, x) * φ x) +
        ∫ x : ℝ^3,
          oddDuhamelSolution 0 (fun z : ℝ^4 ↦ F (timeSpaceContinuousLinearEquiv 3 z))
            (timeSpaceCons t x) * laplacian φ x) t := by
  obtain ⟨R, hRpos, hR⟩ := hφs.exists_pos_le_norm
  obtain ⟨Q, hQpos, hQ⟩ := hφs.coordinate_laplacian.exists_pos_le_norm
  let A := max R Q
  let T := t + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have hA : 0 < A := hRpos.trans_le (le_max_left R Q)
  let χ : ContDiffBump (0 : ℝ^3) :=
    { rIn := A + T
      rOut := A + T + 1
      rIn_pos := add_pos hA hT
      rIn_lt_rOut := lt_add_one (A + T) }
  let G : ℝ × ℝ^3 → ℝ := fun p ↦ χ p.2 * F p
  have hG : Continuous G := (χ.continuous.comp continuous_snd).mul hF
  have hagree (s : ℝ) (_hs : s ∈ Icc 0 T) (x : ℝ^3) (hx : ‖x‖ ≤ A + T) :
      F (s, x) = G (s, x) := by
    have hc : x ∈ Metric.closedBall (0 : ℝ^3) χ.rIn := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    simp only [G, χ.one_of_mem_closedBall hc, one_mul]
  have hφzero (x : ℝ^3) (hx : A ≤ ‖x‖) : φ x = 0 := hR x ((le_max_left R Q).trans hx)
  have hΔzero (x : ℝ^3) (hx : A ≤ ‖x‖) : laplacian φ x = 0 :=
    hQ x ((le_max_right R Q).trans hx)
  have hnear : (fun b ↦ ∫ x : ℝ^3,
      oddDuhamelSolution 0 (fun z : ℝ^4 ↦ F (timeSpaceContinuousLinearEquiv 3 z))
        (timeSpaceCons b x) * φ x) =ᶠ[𝓝 t]
      (fun b ↦ ∫ x : ℝ^3,
        oddDuhamelSolution 0 (fun z : ℝ^4 ↦ G (timeSpaceContinuousLinearEquiv 3 z))
          (timeSpaceCons b x) * φ x) := by
    filter_upwards [Ioo_mem_nhds ht (lt_add_one t)] with b hb
    exact integral_oddDuhamelSolution_mul_eq_of_spatial_agreement hF hG hφ.continuous
      hφs hφzero hagree ⟨hb.1.le, hb.2.le⟩
  have he := hasDerivAt_deriv_integral_oddDuhamelSolution_mul_of_uniform_support hG
    χ.hasCompactSupport.isCompact (fun s x hx ↦ by
      dsimp [G]
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]) hφ hφs ht
  apply (he.congr_deriv ?_).congr_of_eventuallyEq hnear.deriv
  congr 1
  · apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : ‖x‖ ≤ A + T
    · rw [hagree t ⟨ht.le, le_add_of_nonneg_right zero_le_one⟩ x hx]
    · rw [hφzero x (by have := lt_of_not_ge hx; linarith [hT]), mul_zero, mul_zero]
  · exact (integral_oddDuhamelSolution_mul_eq_of_spatial_agreement hF hG
      hφ.continuous_coordinate_laplacian hφs.coordinate_laplacian hΔzero hagree
      ⟨ht.le, le_add_of_nonneg_right zero_le_one⟩).symm

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
