/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Topology.TietzeExtension
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralGlobalExistence
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Nodal.Retarded
import CAS.ExactTactic

/-!
# The nodal moment of a quadratic integral wave

The Duhamel measure, ray and weight define the nodal moment. Interior second derivatives
together with an exact early zero patch force it to vanish.
-/

@[expose] public noncomputable section

section

open Set Filter MeasureTheory BoundedContinuousFunction PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open scoped Topology unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

/-- The compact time and angular parameters in the normalized retarded integral. -/
abbrev NodalParameter := I × Direction

/-- The ordinary normalized-time measure and Kirchhoff angular measure. -/
def nodalMeasure : Measure NodalParameter :=
  (volume : Measure I).prod ((volume : Measure (ℝ^3)).toSphere)

instance : IsFiniteMeasure nodalMeasure := by unfold nodalMeasure; infer_instance

/-- The affine ray from an initial center into the retarded cone. -/
def nodalRay : NodalParameter →ᵇ ℝ^4 :=
  mkOfCompact ⟨fun z ↦ (timeSpaceContinuousLinearEquiv 3).symm
    ((z.1 : ℝ), (1 - (z.1 : ℝ)) • (z.2 : ℝ^3)),
    (timeSpaceContinuousLinearEquiv 3).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          (continuous_subtype_val.comp continuous_snd)))⟩

/-- The radius factor divided by the area of the unit sphere. -/
def nodalWeight : NodalParameter →ᵇ ℝ :=
  mkOfCompact ⟨fun z ↦ (1 - (z.1 : ℝ)) / unitSphereArea 3,
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).div_const _⟩

/-- The ray uses the same coordinates as the physical retarded potential. -/
theorem nodalRay_affine (c : ℝ^3) (t : ℝ) (z : NodalParameter) :
    timeSpaceCons 0 c + t • nodalRay z =
      timeSpaceCons (t * (z.1 : ℝ)) (c + t • ((1 - (z.1 : ℝ)) • (z.2 : ℝ^3))) := by
  apply (timeSpaceContinuousLinearEquiv 3).injective
  simp only [map_add, map_smul, nodalRay, mkOfCompact_apply, ContinuousMap.coe_mk,
    ContinuousLinearEquiv.apply_symm_apply, timeSpaceContinuousLinearEquiv_apply,
    PDE.time, timeSpaceCons_zero, spatialPart_timeSpaceCons]
  ext <;> simp

/-- The physical signed-power retarded integral equals the compact product average. -/
theorem oddDuhamel_signedPower_eq_nodalAverage {p t : ℝ} (hp : 1 ≤ p) (ht : 0 ≤ t)
    {u : ℝ^4 → ℝ} (hu : ContinuousOn u {x | 0 ≤ x 0}) (c : ℝ^3) :
    oddDuhamelSolution 0 (fun z ↦ -Real.signedPower p (u z)) (timeSpaceCons t c) =
      -(t ^ 2 * ∫ z, nodalWeight z *
        Real.signedPower p (u (timeSpaceCons 0 c + t • nodalRay z)) ∂nodalMeasure) := by
  have hpath : Continuous (fun z : NodalParameter ↦ timeSpaceCons 0 c + t • nodalRay z) :=
    continuous_const.add (nodalRay.continuous.const_smul t)
  have hmem (z : NodalParameter) :
      timeSpaceCons 0 c + t • nodalRay z ∈ {x | 0 ≤ x 0} := by
    rw [nodalRay_affine]
    exact mul_nonneg ht z.1.property.1
  let f : NodalParameter →ᵇ ℝ := mkOfCompact
    ⟨fun z ↦ nodalWeight z * Real.signedPower p
        (u (timeSpaceCons 0 c + t • nodalRay z)),
      nodalWeight.continuous.mul ((Real.contDiff_one_signedPower hp).continuous.comp
        (hu.comp_continuous hpath hmem))⟩
  have hi : Integrable (fun z ↦ nodalWeight z *
      Real.signedPower p (u (timeSpaceCons 0 c + t • nodalRay z))) nodalMeasure :=
    f.integrable nodalMeasure
  rw [oddDuhamelSolution_zero_eq_normalized _ _ ht, nodalMeasure, integral_prod _ hi, ← mul_neg,
    ← integral_neg]
  congr 2 with s
  simp only [nodalRay_affine, nodalWeight, mkOfCompact_apply, ContinuousMap.coe_mk]
  rw [integral_neg, integral_const_mul]
  generalize (∫ ω : Direction, Real.signedPower p
    (u (timeSpaceCons (t * (s : ℝ)) (c + t • ((1 - (s : ℝ)) • (ω : ℝ^3)))))
      ∂((volume : Measure (ℝ^3)).toSphere)) = J
  cas

/-- The moment detected by the symmetric source-derivative increment. -/
def nodalMoment (p : ℝ) (u : ℝ^4 → ℝ) (c : ℝ^3) (T : ℝ) : ℝ :=
  ∫ z, if u (timeSpaceCons 0 c + T • nodalRay z) = 0 then
    |deriv (fun t : ℝ ↦ u (timeSpaceCons 0 c + (T + t) • nodalRay z)) 0| ^ (p - 1) *
      (nodalWeight z *
        deriv (fun t : ℝ ↦ u (timeSpaceCons 0 c + (T + t) • nodalRay z)) 0)
    else 0 ∂nodalMeasure

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

end

section

open Set Filter MeasureTheory BoundedContinuousFunction PDE.Analysis PDE.Common WaveEquation
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

/-- An incoming zero patch and interior C² regularity force the unit nodal moment to vanish. -/
theorem nodalMoment_eq_zero_of_interior_integral_identity {p δ : ℝ}
    (hp : 1 < p) (hp₂ : p ≤ 2) {g h : ℝ^3 → ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) {u : ℝ × ℝ^3 → ℝ}
    (hu₁ : ContDiffOn ℝ 1 u {q | |q.1| < 3})
    (hu : ContDiffOn ℝ 2 (u ∘ timeSpaceContinuousLinearEquiv 3)
      {x | 0 < x 0 ∧ x 0 < 2})
    (hδ : 0 < δ)
    (hpatch : ∀ t ∈ Ioo (0 : ℝ) δ, ∀ x : ℝ^3, t + ‖x‖ = 1 → u (t, x) = 0)
    (heq : ∀ q : ℝ × ℝ^3, q.1 ∈ Icc 0 2 →
      u q = cauchyFreeField g h q + oddDuhamelSolution 0
        (fun z : ℝ^4 ↦ -Real.signedPower p (u (timeSpaceContinuousLinearEquiv 3 z)))
        (timeSpaceCons q.1 q.2)) :
    nodalMoment p (u ∘ timeSpaceContinuousLinearEquiv 3) 0 1 = 0 := by
  have hcont := hu₁.continuousOn
  have hzero_initial (θ : ℝ^3) (hθ : ‖θ‖ = 1) : u (0, θ) = 0 := by
    have hc : ContinuousAt (fun t : ℝ ↦ u (t, (1 - t) • θ)) 0 := by
      apply (hcont.continuousAt
        ((isOpen_lt continuous_fst.abs continuous_const).mem_nhds
          (by norm_num : |(0 : ℝ)| < 3))).comp
      fun_prop
    have heq : (fun t : ℝ ↦ u (t, (1 - t) • θ)) =ᶠ[𝓝[>] 0] (fun _ ↦ 0) := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (lt_min hδ zero_lt_one)).filter_mono nhdsWithin_le_nhds]
        with t ht hsmall
      apply hpatch t ⟨ht, hsmall.trans_le (min_le_left _ _)⟩
      have ht1 : t < 1 := hsmall.trans_le (min_le_right _ _)
      rw [norm_smul, Real.norm_of_nonneg (by linarith : 0 ≤ 1 - t), hθ, mul_one]
      exact add_sub_cancel _ _
    have hz : Tendsto (fun t : ℝ ↦ u (t, (1 - t) • θ)) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' heq.symm
    simpa only [sub_zero, one_smul] using
      tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hz
  let U : ℝ^4 → ℝ := u ∘ timeSpaceContinuousLinearEquiv 3
  let s : Set (ℝ^4) := {x | x 0 ∈ Icc (0 : ℝ) 2}
  have hs : IsClosed s := isClosed_Icc.preimage (EuclideanSpace.proj 0).continuous
  have hUs : ContinuousOn U s :=
    hcont.comp (timeSpaceContinuousLinearEquiv 3).continuous.continuousOn fun x hx ↦
      (abs_of_nonneg hx.1).trans_lt (hx.2.trans_lt (by norm_num))
  let f : C(s, ℝ) := ⟨fun x ↦ U x, continuousOn_iff_continuous_domRestrict.mp hUs⟩
  obtain ⟨G, hG⟩ := f.exists_restrict_eq hs
  have hGU {x : ℝ^4} (hx : x ∈ s) : G x = U x :=
    congrArg (fun a : C(s, ℝ) ↦ a ⟨x, hx⟩) hG
  have hdu {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) (c : ℝ^3) :
      oddDuhamelSolution 0 (fun z ↦ -Real.signedPower p (U z)) (timeSpaceCons t c) =
        oddDuhamelSolution 0 (fun z ↦ -Real.signedPower p (G z)) (timeSpaceCons t c) := by
    rw [oddDuhamelSolution_zero_eq_normalized _ _ ht.1,
      oddDuhamelSolution_zero_eq_normalized _ _ ht.1]
    congr 2 with a
    congr 3 with ω
    rw [hGU]
    change t * (a : ℝ) ∈ Icc (0 : ℝ) 2
    exact ⟨mul_nonneg ht.1 a.property.1,
      (mul_le_of_le_one_right ht.1 a.property.2).trans ht.2⟩
  let e : ℝ^4 := timeSpaceCons 1 (0 : ℝ^3)
  have hvertex (t : ℝ) : timeSpaceCons 0 (0 : ℝ^3) + t • e = timeSpaceCons t 0 := by
    apply (timeSpaceContinuousLinearEquiv 3).injective
    simp [e, map_add, map_smul, timeSpaceContinuousLinearEquiv_apply, PDE.time]
  have hu₁' : ContDiffOn ℝ 1 U {x | -3 < x 0 ∧ x 0 < 3} :=
    hu₁.comp (timeSpaceContinuousLinearEquiv 3).contDiff.contDiffOn fun x hx ↦ abs_lt.mpr hx
  have hzero (z : NodalParameter) (hz : nodalRay z 0 ≤ δ / 2) :
      U (timeSpaceCons 0 (0 : ℝ^3) + nodalRay z) = 0 := by
    have hzδ : (z.1 : ℝ) ≤ δ / 2 := by
      simpa only [nodalRay, mkOfCompact_apply, ContinuousMap.coe_mk,
        timeSpaceContinuousLinearEquiv_symm_apply, timeSpaceCons_zero] using hz
    have hθ : ‖(z.2 : ℝ^3)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using z.2.property
    have hpoint : timeSpaceContinuousLinearEquiv 3
        (timeSpaceCons 0 (0 : ℝ^3) + nodalRay z) =
          ((z.1 : ℝ), (1 - (z.1 : ℝ)) • (z.2 : ℝ^3)) := by
      simp [nodalRay, map_add, timeSpaceContinuousLinearEquiv_apply, PDE.time]
    change u _ = 0
    rw [hpoint]
    by_cases ht : (z.1 : ℝ) = 0
    · simpa only [ht, sub_zero, one_smul] using hzero_initial _ hθ
    · apply hpatch _ ⟨lt_of_le_of_ne z.1.property.1 (Ne.symm ht), by linarith⟩
      rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr z.1.property.2), hθ, mul_one]
      exact add_sub_cancel _ _
  have hm := nodal_moment_eq_zero_of_interior_retarded_identity nodalMeasure hp hp₂
    (half_pos hδ) (timeSpaceCons 0 0) e (by simp) (by simp [e]) nodalRay
    (fun z ↦ by simp [nodalRay, timeSpaceContinuousLinearEquiv_symm_apply])
    nodalWeight hu₁' hu hzero (contDiff_two_kirchhoffFormula hg hh)
  change nodalMoment p U 0 1 = 0
  unfold nodalMoment
  simp only [one_smul]
  apply hm
  filter_upwards [Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) < 2)] with t ht
  rw [hvertex]
  have heq' : U (timeSpaceCons t 0) =
      spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons t 0) +
      oddDuhamelSolution 0 (fun z ↦ -Real.signedPower p (U z)) (timeSpaceCons t 0) := by
    simpa only [U, Function.comp_def, timeSpaceContinuousLinearEquiv_apply, PDE.time,
      timeSpaceCons_zero, spatialPart_timeSpaceCons, cauchyFreeField] using
        heq (t, 0) ⟨ht.1.le, ht.2.le⟩
  change U (timeSpaceCons t 0) = _
  rw [heq', hdu ⟨ht.1.le, ht.2.le⟩,
    oddDuhamel_signedPower_eq_nodalAverage hp.le ht.1.le G.continuous.continuousOn]
  rw [sub_eq_add_neg]
  congr 4 with z
  rw [hGU]
  rw [nodalRay_affine]
  change t * (z.1 : ℝ) ∈ Icc (0 : ℝ) 2
  exact ⟨mul_nonneg ht.1.le z.1.property.1,
    (mul_le_of_le_one_right ht.1.le z.1.property.2).trans ht.2.le⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

end
