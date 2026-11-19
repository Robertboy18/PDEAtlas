/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.SphericalPairing
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RetardedSplit

/-!
# Compact spatial testing of the retarded field

The physical Duhamel field of a continuous source pairs with every continuous
compact spatial test by transferring spherical averaging to that test. The
source requires neither spatial integrability nor a derivative. This supplies
the integral identity needed before differentiating the tested wave equation.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open scoped unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- Compact spatial testing of the Duhamel field puts every spherical
average on the test. The identity is valid for any continuous source. -/
theorem integral_oddDuhamelSolution_mul_eq {F : ℝ × ℝ^3 → ℝ} (hF : Continuous F) {φ : ℝ^3 → ℝ}
    (hφ : Continuous φ) (hφs : HasCompactSupport φ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : ℝ^3,
      oddDuhamelSolution 0 (fun z : ℝ^4 ↦ F (timeSpaceContinuousLinearEquiv 3 z))
        (timeSpaceCons t x) * φ x) =
      t ^ 2 * ∫ s : I, (1 - (s : ℝ)) *
        ∫ x : ℝ^3, F (t * (s : ℝ), x) *
          unitSphereAverage 3 φ x (t * (1 - (s : ℝ))) := by
  let A : I → ℝ^3 → ℝ := fun s x ↦ (1 - (s : ℝ)) *
    unitSphereAverage 3 (fun y ↦ F (t * (s : ℝ), y)) x (t * (1 - (s : ℝ)))
  have hA : Continuous A.uncurry := by
    have hc := continuous_integral_of_compact (μ := (volume : Measure (ℝ^3)).toSphere)
      (g := fun (q : I × ℝ^3) (ω : Direction) ↦
        F (t * (q.1 : ℝ), q.2 + (t * (1 - (q.1 : ℝ))) • (ω : ℝ^3)))
      (hF.comp (by fun_prop))
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul (hc.div_const _)
  have hi : Integrable (fun q : I × ℝ^3 ↦ A q.1 q.2 * φ q.2)
      ((volume : Measure I).prod volume) := by
    apply Continuous.integrable_of_hasCompactSupport (hA.mul (hφ.comp continuous_snd))
    refine HasCompactSupport.intro (isCompact_univ.prod hφs.isCompact) fun q hq ↦ ?_
    have hx : q.2 ∉ tsupport φ := by
      simpa only [mem_prod, mem_univ, true_and] using hq
    change A q.1 q.2 * φ q.2 = 0
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hformula (x : ℝ^3) :
      oddDuhamelSolution 0 (fun z : ℝ^4 ↦ F (timeSpaceContinuousLinearEquiv 3 z))
        (timeSpaceCons t x) = t ^ 2 * ∫ s : I, A s x := by
    rw [oddDuhamelSolution_zero_eq_normalized _ x ht]
    simp only [A, unitSphereAverage, mul_smul,
      timeSpaceContinuousLinearEquiv_apply, PDE.time, timeSpaceCons_zero, spatialPart_timeSpaceCons]
  calc
    _ = t ^ 2 * ∫ x : ℝ^3, ∫ s : I, A s x * φ x := by
      simp_rw [hformula, mul_assoc, ← integral_mul_const]
      rw [integral_const_mul]
    _ = t ^ 2 * ∫ s : I, ∫ x : ℝ^3, A s x * φ x := by
      congr 1
      exact integral_integral_swap (f := fun (x : ℝ^3) (s : I) ↦ A s x * φ x) hi.swap
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with s
      simp only [A, mul_assoc, integral_const_mul]
      congr 1
      exact integral_unitSphereAverage_mul_eq (F := fun y ↦ F (t * (s : ℝ), y))
        (hF.comp (continuous_const.prodMk continuous_id)) hφ hφs _

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
