/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianHessianTail
import CAS.ExactTactic

/-!
# Local cancellation for the Newtonian Hessian

Subtracting the source value at the pole gains one power of distance. A local
Lipschitz bound therefore makes the centered Hessian integral absolutely
convergent, with an explicit bound proportional to the ball radius.

The uncentered kernel has zero integral on each concentric annulus. Its
spherical principal value is consequently the centered integral. The diagonal
source correction remains separate from this principal value.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Filter
open scoped Topology

namespace PotentialTheory

/-- The radial majorant for the centered five-dimensional Hessian has mass
`(8π² / 3) R` on a ball of radius `R`. -/
theorem integral_ball_norm_rpow_neg_four_five
    (R : ℝ) (hR : 0 < R) :
    (∫ X in Metric.ball (0 : ℝ^5) R, ‖X‖ ^ (-4 : ℝ)) =
      (8 * Real.pi ^ 2 / 3) * R := by
  let f : ℝ → ℝ := (Set.Iio R).indicator (fun r ↦ r ^ (-4 : ℝ))
  have hpolar := integral_fun_norm_addHaar (E := ℝ^5) (volume : Measure (ℝ^5)) f
  have hleft : (∫ X : ℝ^5, f ‖X‖) =
      ∫ X in Metric.ball (0 : ℝ^5) R, ‖X‖ ^ (-4 : ℝ) := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with X
    simp only [f, Set.indicator, Set.mem_Iio, Metric.mem_ball, dist_zero_right]
  have hrad :
      (∫ r in Set.Ioi (0 : ℝ),
        r ^ (Module.finrank ℝ (ℝ^5) - 1) • f r) = R := by
    calc
      _ = ∫ r in Set.Ioi (0 : ℝ), (Set.Iio R).indicator (fun _ ↦ (1 : ℝ)) r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        have hrpos : 0 < r := hr
        have hp : r ^ (4 : ℕ) * r ^ (-4 : ℝ) = 1 := by
          simpa only [Real.rpow_ofNat, show (4 : ℝ) + -4 = 0 by norm_num,
            Real.rpow_zero] using (Real.rpow_add hrpos 4 (-4)).symm
        by_cases hrR : r < R
        · simpa only [f, Set.indicator_of_mem (s := Set.Iio R) hrR,
            finrank_euclideanSpace_fin, smul_eq_mul] using hp
        · simp [f, hrR]
      _ = ∫ _r in Set.Ioo (0 : ℝ) R, (1 : ℝ) := by
        rw [setIntegral_indicator measurableSet_Iio]
        rfl
      _ = R := by
        simp [MeasureTheory.measureReal_def, hR.le]
  have hvol :
      (volume : Measure (ℝ^5)).real (Metric.ball (0 : ℝ^5) 1) =
        8 * Real.pi ^ 2 / 15 := by
    simpa only [PDE.Analysis.ballVolume, MeasureTheory.measureReal_def,
      one_pow, mul_one, PDE.Analysis.unitBallVolume_five] using
      PDE.Analysis.ballVolume_eq_unitBallVolume_mul_pow 5 1 zero_le_one
  rw [hleft, hrad, hvol] at hpolar
  calc
    _ = (Module.finrank ℝ (ℝ^5)) • (8 * Real.pi ^ 2 / 15) • R := hpolar
    _ = _ := by simp only [finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul]; cas

/-- A local Lipschitz bound at the pole makes the centered classical Hessian
integrable. No absolute integrability of the uncentered kernel is asserted. -/
theorem integrableOn_and_norm_integral_fundamentalSolution_five_hessian_sub
    (i j : Fin 5) (f : ℝ^5 → ℝ) (hf : Measurable f)
    (R L : ℝ) (hR : 0 < R) (hL : 0 ≤ L)
    (hlip : ∀ X ∈ Metric.ball (0 : ℝ^5) R, |f X - f 0| ≤ L * ‖X‖) :
    IntegrableOn (fun X : ℝ^5 ↦
      iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X *
        (f X - f 0)) (Metric.ball 0 R) ∧
      ‖∫ X in Metric.ball (0 : ℝ^5) R,
        iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X *
          (f X - f 0)‖ ≤ 6 * L * R := by
  let F : ℝ^5 → ℝ := fun X ↦
    iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X * (f X - f 0)
  let C : ℝ := (18 / (8 * Real.pi ^ 2)) * L
  let B : ℝ^5 → ℝ := fun X ↦ C * ‖X‖ ^ (-4 : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBmeas : Measurable B := measurable_const.mul (measurable_norm.pow_const _)
  have hB : IntegrableOn B (Metric.ball (0 : ℝ^5) R) := by
    apply integrableOn_ball_of_norm_le_rpow (C := C) (α := (4 : ℝ))
      (by norm_num) (by norm_num)
    · filter_upwards [] with X
      simp only [B, Real.norm_eq_abs, abs_mul, abs_of_nonneg hC,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg X) (-4)), le_refl]
    · exact hBmeas.aestronglyMeasurable
  have hFmeas : Measurable F :=
    (measurable_fundamentalSolution_five_hessian i j).mul (hf.sub measurable_const)
  have hbound : ∀ᵐ X ∂volume.restrict (Metric.ball (0 : ℝ^5) R), ‖F X‖ ≤ B X := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae ((Set.countable_singleton (0 : ℝ^5)).ae_notMem volume)] with X hXR hX
    have hX0 : X ≠ 0 := by simpa only [Set.mem_singleton_iff] using hX
    have hpos : 0 < ‖X‖ := norm_pos_iff.mpr hX0
    have hp : ‖X‖ ^ (-5 : ℝ) * ‖X‖ = ‖X‖ ^ (-4 : ℝ) := by
      simpa only [Real.rpow_one, show (-5 : ℝ) + 1 = -4 by norm_num] using
        (Real.rpow_add hpos (-5) 1).symm
    calc
      ‖F X‖ =
          |iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X| *
            |f X - f 0| := by simp only [F, norm_mul, Real.norm_eq_abs]
      _ ≤ ((18 / (8 * Real.pi ^ 2)) * ‖X‖ ^ (-5 : ℝ)) * (L * ‖X‖) :=
        mul_le_mul (abs_fundamentalSolution_five_hessian_le i j X hX0)
          (hlip X hXR) (abs_nonneg _) (by positivity)
      _ = B X := by dsimp [B, C]; rw [mul_mul_mul_comm, hp]
  have hF : IntegrableOn F (Metric.ball (0 : ℝ^5) R) :=
    hB.mono' hFmeas.aestronglyMeasurable.restrict hbound
  refine ⟨hF, ?_⟩
  calc
    ‖∫ X in Metric.ball (0 : ℝ^5) R, F X‖ ≤
        ∫ X in Metric.ball (0 : ℝ^5) R, ‖F X‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ X in Metric.ball (0 : ℝ^5) R, B X :=
      integral_mono_ae hF.norm hB hbound
    _ = C * ((8 * Real.pi ^ 2 / 3) * R) := by
      rw [show B = fun X : ℝ^5 ↦ C * ‖X‖ ^ (-4 : ℝ) from rfl,
        integral_const_mul, integral_ball_norm_rpow_neg_four_five R hR]
    _ = 6 * L * R := by dsimp [C]; cas

/-- Every positive spherical truncation of the constant-source Hessian has
zero mass. The truncated kernel is integrable, so the zero comes from
cancellation in an absolutely convergent integral. -/
theorem integrableOn_and_integral_fundamentalSolution_five_hessian_annulus
    (i j : Fin 5) (R ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5))
      (Metric.ball (0 : ℝ^5) R ∩ {X : ℝ^5 | ε < ‖X‖}) ∧
      (∫ X in Metric.ball (0 : ℝ^5) R ∩ {X : ℝ^5 | ε < ‖X‖},
        iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X) = 0 := by
  let S := Metric.ball (0 : ℝ^5) R ∩ {X : ℝ^5 | ε < ‖X‖}
  let K := iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5)
  have hS : MeasurableSet S :=
    measurableSet_ball.inter (measurableSet_lt measurable_const measurable_norm)
  have hK : IntegrableOn K S := by
    refine ((integrableOn_const (C := (18 / (8 * Real.pi ^ 2)) * ε ^ (-5 : ℝ))
      (s := Metric.ball (0 : ℝ^5) R)).mono_set Set.inter_subset_left).mono'
      (measurable_fundamentalSolution_five_hessian i j).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem hS] with X hX
    have hnorm : 0 < ‖X‖ := hε.trans hX.2
    rw [Real.norm_eq_abs]
    exact (abs_fundamentalSolution_five_hessian_le i j X (norm_pos_iff.1 hnorm)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hε hX.2.le (by norm_num))
        (by positivity))
  refine ⟨hK, ?_⟩
  change (∫ X in S, K X) = 0
  rw [← integral_indicator hS, PDE.Analysis.integral_polar_addHaar_iterated _ _
    ((integrable_indicator_iff hS).2 hK)]
  refine setIntegral_eq_zero_of_forall_eq_zero fun r (hr : 0 < r) ↦ smul_eq_zero_of_right _ ?_
  have hrnorm (ω : Metric.sphere (0 : ℝ^5) 1) : ‖r • (ω : ℝ^5)‖ = r := by
    simp [norm_smul, abs_of_pos hr]
  by_cases hmem : r < R ∧ ε < r
  · calc _ = r ^ (-5 : ℝ) * ∫ ω : Metric.sphere (0 : ℝ^5) 1,
            ((15 / (8 * Real.pi ^ 2)) * (ω : ℝ^5) j * (ω : ℝ^5) i -
              (3 / (8 * Real.pi ^ 2)) * (if j = i then 1 else 0))
            ∂(volume : Measure (ℝ^5)).toSphere := by
          rw [← integral_const_mul]
          refine integral_congr_ae (.of_forall fun ω ↦ ?_)
          have hrω : r • (ω : ℝ^5) ∈ S := by
            simpa only [S, Set.mem_inter_iff, Metric.mem_ball, dist_zero_right,
              Set.mem_ofPred_eq, hrnorm ω] using hmem
          dsimp only
          rw [Set.indicator_of_mem hrω]
          dsimp only [K]
          rw [fundamentalSolution_five_iteratedPartialDeriv_two j i _
            (norm_ne_zero_iff.mp (by rw [hrnorm ω]; exact hr.ne')), hrnorm ω,
            show r ^ (-5 : ℝ) = r ^ (-7 : ℝ) * r ^ 2 by
              rw [← Real.rpow_two, ← Real.rpow_add hr]; norm_num]
          simp only [PiLp.smul_apply, smul_eq_mul]
          ring
      _ = 0 := by rw [fiveDimensionalHessianAngularMean_zero j i, mul_zero]
  · refine integral_eq_zero_of_ae (.of_forall fun ω ↦ Set.indicator_of_notMem ?_ _)
    simpa only [S, Set.mem_inter_iff, Metric.mem_ball, dist_zero_right,
      Set.mem_ofPred_eq, hrnorm ω] using hmem

/-- Local subtraction preserves every positive truncation, and the resulting
integrable remainder gives the spherical principal-value limit. Only a local
Lipschitz estimate and measurability of the source are needed. -/
theorem fundamentalSolution_five_hessian_near_principalValue_tendsto
    (i j : Fin 5) (f : ℝ^5 → ℝ) (hf : Measurable f)
    (R L : ℝ) (hR : 0 < R) (hL : 0 ≤ L)
    (hlip : ∀ X ∈ Metric.ball (0 : ℝ^5) R, |f X - f 0| ≤ L * ‖X‖) :
    (∀ ε : ℝ, 0 < ε →
      IntegrableOn (fun X : ℝ^5 ↦
        iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X * f X)
        (Metric.ball 0 R ∩ {X : ℝ^5 | ε < ‖X‖})) ∧
      Tendsto (fun ε : ℝ ↦
        ∫ X in Metric.ball (0 : ℝ^5) R ∩ {X : ℝ^5 | ε < ‖X‖},
          iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X * f X)
        (𝓝[>] 0)
        (𝓝 (∫ X in Metric.ball (0 : ℝ^5) R,
          iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X *
            (f X - f 0))) := by
  let K := iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5)
  let F : ℝ^5 → ℝ := fun X ↦ K X * (f X - f 0)
  have hF : IntegrableOn F (Metric.ball (0 : ℝ^5) R) :=
    (integrableOn_and_norm_integral_fundamentalSolution_five_hessian_sub
      i j f hf R L hR hL hlip).1
  have htrunc (ε : ℝ) (hε : 0 < ε) :
      IntegrableOn (fun X : ℝ^5 ↦ K X * f X)
        (Metric.ball 0 R ∩ {X : ℝ^5 | ε < ‖X‖}) ∧
        (∫ X in Metric.ball (0 : ℝ^5) R ∩ {X : ℝ^5 | ε < ‖X‖}, K X * f X) =
          ∫ X in Metric.ball (0 : ℝ^5) R ∩ {X : ℝ^5 | ε < ‖X‖}, F X := by
    have hann := integrableOn_and_integral_fundamentalSolution_five_hessian_annulus i j R ε hε
    have hc : IntegrableOn F
        (Metric.ball (0 : ℝ^5) R ∩ {X : ℝ^5 | ε < ‖X‖}) :=
      hF.mono_set Set.inter_subset_left
    have hconst := hann.1.mul_const (f 0)
    rw [show (fun X : ℝ^5 ↦ K X * f X) = fun X ↦ F X + K X * f 0 from
      funext fun X ↦ by simp only [F]; ring]
    refine ⟨hc.add hconst, ?_⟩
    rw [integral_add hc hconst, integral_mul_const]
    change _ + (∫ X in Metric.ball (0 : ℝ^5) R ∩ {X : ℝ^5 | ε < ‖X‖},
      iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X) * f 0 = _
    rw [hann.2, zero_mul, add_zero]
  refine ⟨fun ε hε ↦ (htrunc ε hε).1, ?_⟩
  have hlim : Tendsto (fun ε : ℝ ↦
      ∫ X in Metric.ball (0 : ℝ^5) R, {X : ℝ^5 | ε < ‖X‖}.indicator F X)
      (𝓝[>] 0) (𝓝 (∫ X in Metric.ball (0 : ℝ^5) R, F X)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun X ↦ ‖F X‖)
      (.of_forall fun ε ↦ hF.aestronglyMeasurable.indicator
        (measurableSet_lt measurable_const measurable_norm))
      (.of_forall fun ε ↦ .of_forall fun X ↦ norm_indicator_le_norm_self F X) hF.norm ?_
    filter_upwards [ae_restrict_of_ae
      ((Set.countable_singleton (0 : ℝ^5)).ae_notMem volume)] with X (hX : X ≠ 0)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (norm_pos_iff.2 hX)] with ε hε
    exact (Set.indicator_of_mem (s := {Y : ℝ^5 | ε < ‖Y‖}) hε.2 F).symm
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [setIntegral_indicator (measurableSet_lt measurable_const measurable_norm)]
  exact (htrunc ε hε).2.symm

/-- The near principal value together with the distributional diagonal
correction has an explicit local bound. Identification with the potential
Hessian comes from the convolution theorem. -/
theorem norm_fundamentalSolution_five_hessian_near_corrected_le
    (i j : Fin 5) (f : ℝ^5 → ℝ) (hf : Measurable f)
    (R L : ℝ) (hR : 0 < R) (hL : 0 ≤ L)
    (hlip : ∀ X ∈ Metric.ball (0 : ℝ^5) R, |f X - f 0| ≤ L * ‖X‖) :
    ‖(∫ X in Metric.ball (0 : ℝ^5) R,
        iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X *
          (f X - f 0)) - (if i = j then f 0 / 5 else 0)‖ ≤
      6 * L * R + (if i = j then |f 0| / 5 else 0) := by
  have hbound := (integrableOn_and_norm_integral_fundamentalSolution_five_hessian_sub
    i j f hf R L hR hL hlip).2
  refine (norm_sub_le _ _).trans ?_
  apply add_le_add hbound
  by_cases hij : i = j <;> simp [hij, norm_div, Real.norm_eq_abs]


/-- A bound on the source's first derivative controls the centered
near Hessian contribution at `X`, including the diagonal source correction.
The mean value theorem supplies the required cancellation estimate. -/
theorem norm_fundamentalSolution_five_hessian_near_corrected_le_of_fderiv_bound
    (i j : Fin 5) (f : ℝ^5 → ℝ) (hf : Measurable f)
    (X : ℝ^5) (R L : ℝ) (hR : 0 < R) (hL : 0 ≤ L)
    (hdiff : ∀ Y ∈ Metric.ball X R, DifferentiableAt ℝ f Y)
    (hbound : ∀ Y ∈ Metric.ball X R, ‖fderiv ℝ f Y‖ ≤ L) :
    ‖(∫ H in Metric.ball (0 : ℝ^5) R,
        iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) H *
          (f (X - H) - f X)) - (if i = j then f X / 5 else 0)‖ ≤
      6 * L * R + (if i = j then |f X| / 5 else 0) := by
  have hcenter : X ∈ Metric.ball X R := Metric.mem_ball_self hR
  have hlip : ∀ H ∈ Metric.ball (0 : ℝ^5) R,
      |f (X - H) - f (X - 0)| ≤ L * ‖H‖ := by
    intro H hH
    have hnorm : ‖(X - H) - X‖ = ‖H‖ := by
      rw [show (X - H) - X = -H by abel, norm_neg]
    have hmem : X - H ∈ Metric.ball X R := by
      rw [Metric.mem_ball, dist_eq_norm, hnorm]
      simpa only [Metric.mem_ball, dist_zero_right] using hH
    simpa only [sub_zero, Real.norm_eq_abs, hnorm] using
      (convex_ball X R).norm_image_sub_le_of_norm_fderiv_le
        hdiff hbound hcenter hmem
  simpa only [sub_zero] using
    norm_fundamentalSolution_five_hessian_near_corrected_le i j (fun H ↦ f (X - H))
      (hf.comp (measurable_const.sub measurable_id)) R L hR hL hlip

end PotentialTheory
