/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.EvenDimensions.Descent
public import PDE.Analysis.Integration.SphereProjection.Normalization

/-!
# The even-dimensional weighted ball formula

The weighted ball formula is the representation (38) of Evans, §2.4.1(e), which he derives by
the method of descent (33)-(37). The literal moving-ball profile uses the ordinary ball average
and the reciprocal square-root kernel. On positive radii it equals the lifted spherical profile
after the exact double-factorial normalization. Equality on an open interval is propagated
through the radial transform and the outer derivative; no derivative is inferred from equality at
a single radius.

The moving-ball expression is used only at positive time. Its canonical joint
extension through time zero is `evenWaveSolution`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1(e), equations (33)-(38).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- The iterated weighted ball profile in dimension `2k+2`. Its totalized
values away from positive radii do not define the Cauchy extension. -/
def evenBallProfile (k : ℕ) (f : ℝ^(2 * k + 2) → ℝ) (x : ℝ^(2 * k + 2)) : ℝ → ℝ :=
  oddRadialTransform k (fun r ↦ r ^ (2 * k + 2) * ballAverage (2 * k + 2)
    (fun y ↦ f y / Real.sqrt (r ^ 2 - ‖y - x‖ ^ 2)) x r)

/-- The literal even-dimensional formula: the time derivative of the displacement
profile plus the velocity profile, divided by `(2k+2)‼`. -/
def evansEvenDimensionalFormula (k : ℕ) (g h : ℝ^(2 * k + 2) → ℝ)
    (x : ℝ^(2 * k + 2)) (t : Set.Ioi (0 : ℝ)) : ℝ :=
  (deriv (evenBallProfile k g x) t + evenBallProfile k h x t) /
    (Nat.doubleFactorial (2 * k + 2) : ℝ)

/-- The spherical and ball profiles agree on the entire positive-radius interval
with the exact ratio of double factorials. -/
theorem oddSphericalProfile_eq_evenBallProfile (k : ℕ)
    {f : ℝ^(2 * k + 2) → ℝ} (hf : Continuous f) (z : ℝ^(2 * k + 3)) :
    Set.EqOn (oddSphericalProfile k (f ∘ coordinateProjection) z)
      (fun r ↦ ((Nat.doubleFactorial (2 * k + 1) : ℝ) / Nat.doubleFactorial (2 * k + 2)) *
      evenBallProfile k f (coordinateProjection z) r) (Set.Ioi 0) := by
  have : Fact (0 < 2 * k + 2) := ⟨by omega⟩
  have he : Set.EqOn (fun r ↦ r ^ (2 * k + 1) *
        unitSphereAverage (2 * k + 3) (f ∘ coordinateProjection) z r)
      (fun r ↦ ((Nat.doubleFactorial (2 * k + 1) : ℝ) / Nat.doubleFactorial (2 * k + 2)) *
          (r ^ (2 * k + 2) * ballAverage (2 * k + 2)
            (fun y ↦ f y / Real.sqrt (r ^ 2 - ‖y - coordinateProjection z‖ ^ 2))
            (coordinateProjection z) r)) (Set.Ioi 0) := by
    intro r hr
    have h := pow_mul_unitSphereAverage_coordinateProjection hf z hr
    rw [two_mul_unitBallVolume_div_unitSphereArea_even k] at h
    simpa only [show 2 * k + 2 - 1 = 2 * k + 1 by omega] using h
  simpa only [oddSphericalProfile, evenBallProfile, oddRadialTransform_const_mul] using
    oddRadialTransform_congr_Ioi k he

/-- The descended classical field is Evans's formula (38) at every positive time.
Only the lower orders needed for this identification are assumed here. -/
theorem evenWaveSolution_eq_evansEvenDimensionalFormula (k : ℕ) {g h : ℝ^(2 * k + 2) → ℝ}
    (hg : ContDiff ℝ (k + 1) g) (hh : Continuous h) (x : ℝ^(2 * k + 2)) (t : Set.Ioi (0 : ℝ)) :
    evenWaveSolution k g h (timeSpaceCons t x) = evansEvenDimensionalFormula k g h x t := by
  have hgprofile := oddSphericalProfile_eq_evenBallProfile k hg.continuous (coordinateInclusion x)
  have hhprofile := oddSphericalProfile_eq_evenBallProfile k hh (coordinateInclusion x)
  have hgderiv := hgprofile.deriv isOpen_Ioi t.property
  simp only [coordinateProjection_coordinateInclusion, deriv_const_mul_field] at hgderiv
  have hγ : (Nat.doubleFactorial (2 * k + 1) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.doubleFactorial_pos _).ne'
  rw [evenWaveSolution_timeSpaceCons,
    oddWaveSolution_eq_evansOddDimensionalFormula k (hg.comp coordinateProjection.contDiff)]
  unfold evansOddDimensionalFormula evansEvenDimensionalFormula
  rw [hgderiv, hhprofile t.property, coordinateProjection_coordinateInclusion]
  field_simp

end WaveEquation
