/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Kirchhoff
public import PDE.Hyperbolic.Models.Wave.OddDimensions
import CAS.ExactTactic

/-!
# Kirchhoff's formula and spherical means

The surface-integral and spherical-mean formulas describe the same function.
Differentiating the radius times the mean produces the displacement and radial
gradient terms in Kirchhoff's integral. This identification lets the representation
results for odd dimensions apply to the surface-integral formula in dimension three.
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace WaveEquation

open MeasureTheory PDE.Analysis

/-- At positive time, Kirchhoff's surface integral is exactly the
three-dimensional spherical-mean representation. Only one derivative of the
displacement and continuity of the velocity data are needed for this identity. -/
theorem kirchhoffFormula_eq_evansOddDimensionalFormula {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 1 g)
    (hh : Continuous h) (x : ℝ^3) (t : Set.Ioi (0 : ℝ)) :
    kirchhoffFormula g h x t = evansOddDimensionalFormula 0 g h x t := by
  let μ := (volume : Measure (ℝ^3)).toSphere
  let p := fun ω : Metric.sphere (0 : ℝ^3) 1 ↦ x + (t : ℝ) • (ω : ℝ^3)
  have hp : Continuous p := by fun_prop
  have hi {f : Metric.sphere (0 : ℝ^3) 1 → ℝ} (hf : Continuous f) : Integrable f μ :=
    hf.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (fun _ _ ↦ Set.mem_univ _))
  have hgint : Integrable (fun ω ↦ g (p ω)) μ := hi (hg.continuous.comp hp)
  have hhint : Integrable (fun ω ↦ h (p ω)) μ := hi (hh.comp hp)
  have hdcont : Continuous (fun ω : Metric.sphere (0 : ℝ^3) 1 ↦ fderiv ℝ g (p ω) (ω : ℝ^3)) :=
    (hg.continuous_fderiv_apply (by norm_num)).comp (hp.prodMk continuous_subtype_val)
  have hdint := hi hdcont
  have hradial (ω : Metric.sphere (0 : ℝ^3) 1) : ∑ i, ∇ g (p ω) i * (p ω i - x i) =
        (t : ℝ) * fderiv ℝ g (p ω) (ω : ℝ^3) := by
    rw [PDE.fderiv_apply_eq_sum_partialDeriv_mul]
    simp only [PDE.gradient_apply_eq_partialDeriv, p, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, add_sub_cancel_left, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  have hderiv : deriv (fun r ↦ r * unitSphereAverage 3 g x r) (t : ℝ) = unitSphereAverage 3 g x t +
          (t : ℝ) * ((∫ ω, fderiv ℝ g (p ω) (ω : ℝ^3) ∂μ) / unitSphereArea 3) := by
    simpa only [one_mul, id_eq] using ((hasDerivAt_id (t : ℝ)).fun_mul
        (hasDerivAt_unitSphereAverage g x t hg)).deriv
  rw [evansOddDimensionalFormula_zero, hderiv]
  simp only [kirchhoffFormula, abs_of_pos t.property,
    t.property.ne', ↓reduceDIte, sphereIntegral, unitSphereAverage,
    unitSphereArea_three, Nat.reduceSub]
  change (1 / (4 * Real.pi * (t : ℝ) ^ 2)) * ((t : ℝ) ^ 2 * ∫ ω, (t : ℝ) * h (p ω) + g (p ω) +
        ∑ i, ∇ g (p ω) i * (p ω i - x i) ∂μ) = ((∫ ω, g (p ω) ∂μ) / (4 * Real.pi)) +
      (t : ℝ) * ((∫ ω, fderiv ℝ g (p ω) (ω : ℝ^3) ∂μ) / (4 * Real.pi)) +
      (t : ℝ) * ((∫ ω, h (p ω) ∂μ) / (4 * Real.pi))
  simp_rw [hradial]
  rw [integral_add ((hhint.const_mul _).fun_add hgint) (hdint.const_mul _),
    integral_add (hhint.const_mul _) hgint, integral_const_mul, integral_const_mul]
  have ht : (t : ℝ) ≠ 0 := t.property.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  cas

/-- The total Kirchhoff candidate agrees with the signed-radius formula,
including time zero. This removes the apparent singularity of the surface
normalization and permits ordinary two-sided differentiation at the initial slice. -/
theorem kirchhoffFormula_eq_sphericalMean {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 1 g) (hh : Continuous h)
    (x : ℝ^3) (t : ℝ) :
    kirchhoffFormula g h x t =
      deriv (fun r ↦ r * unitSphereAverage 3 g x r) t + t * unitSphereAverage 3 h x t := by
  have hpos {v : ℝ^3 → ℝ} (hv : Continuous v) {s : ℝ} (hs : 0 < s) : kirchhoffFormula g v x s =
        deriv (fun r ↦ r * unitSphereAverage 3 g x r) s +
          s * unitSphereAverage 3 v x s := by
    simpa only [evansOddDimensionalFormula_zero] using
      kirchhoffFormula_eq_evansOddDimensionalFormula hg hv x ⟨s, hs⟩
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · let P := fun r ↦ r * unitSphereAverage 3 g x r
    have hodd : Function.Odd P := by
      simpa only [oddSphericalProfile_zero] using oddSphericalProfile_odd 0 g x
    have heven : deriv P (-t) = deriv P t := even_deriv_of_odd hodd t
    calc
      kirchhoffFormula g h x t = kirchhoffFormula g (-h) x (-t) := by
        simp only [kirchhoffFormula, abs_neg, Pi.neg_apply, neg_mul, mul_neg, neg_neg]
      _ = deriv P (-t) + (-t) * unitSphereAverage 3 (-h) x (-t) := hpos hh.neg (neg_pos.mpr ht)
      _ = deriv P t + t * unitSphereAverage 3 h x t := by
        rw [heven, unitSphereAverage_neg_radius]
        simp [unitSphereAverage, integral_neg, neg_div]
  · have hd := ((hasDerivAt_id (0 : ℝ)).fun_mul (hasDerivAt_unitSphereAverage g x 0 hg)).deriv
    simpa [kirchhoffFormula, unitSphereAverage_zero] using hd.symm
  · exact hpos hh ht

end WaveEquation
