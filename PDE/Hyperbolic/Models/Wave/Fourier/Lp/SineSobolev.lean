/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module
public import PDE.Hyperbolic.Models.Wave.Fourier.Lp.SineWeakGradient
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.Weak

/-!
# Uniform Sobolev bounds for physical sine evolution

The weak gradient bound and the quantitative weak Sobolev inequality
control the real part of physical sine evolution by its velocity L2 norm.
The estimate is uniform in time and applies to every finite critical Sobolev
exponent in arbitrary Euclidean dimension.
-/

@[expose] public section

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal

namespace WaveEquation.Fourier

/-- The physical sine evolution has a uniform homogeneous Sobolev bound.
Only the velocity L2 norm occurs, for every finite critical exponent. -/
theorem eLpNorm_re_sineEvolution_le {n : ℕ} {q : NNReal} (hn : 0 < n)
    (hq : (q : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (n : ℝ)⁻¹) (t : ℝ) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    eLpNorm (fun x ↦ (sineEvolution t u x).re) q volume ≤
      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^n)) 2 : ℝ≥0∞) * n * ‖u‖ₑ := by
  classical
  choose v hv hnorm using fun i : Fin n ↦ exists_weakDerivative_sineEvolution_norm_le i t u
  have hb (i : Fin n) : eLpNorm (fun x ↦ (v i x).re) 2 volume ≤ ‖u‖ₑ := by
    calc
      _ ≤ eLpNorm (v i) 2 volume := eLpNorm_mono_ae ((Lp.memLp (v i)).re.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x ↦ by
          simpa only [Real.norm_eq_abs, RCLike.re_to_complex] using Complex.abs_re_le_norm (v i x))
      _ = ‖v i‖ₑ := (Lp.enorm_def _).symm
      _ ≤ ‖u‖ₑ := by
        simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hnorm i)
  have h := SobolevSpace.Inequalities.eLpNorm_le_sum_eLpNorm_weakDeriv
    (p := (2 : NNReal)) (q := q) (by norm_num) hn hq
    (Lp.memLp (sineEvolution t u)).re (fun i ↦ (Lp.memLp (v i)).re) (fun i ↦ (hv i).1)
  apply h.trans
  calc
    _ ≤ (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^n)) 2 : ℝ≥0∞) *
        ∑ _i : Fin n, ‖u‖ₑ := mul_le_mul_right (Finset.sum_le_sum fun i _ ↦ hb i) _
    _ = _ := by simp [mul_assoc]

end WaveEquation.Fourier
