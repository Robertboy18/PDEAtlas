/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.ConeProfile.Integrability
public import PDE.Hyperbolic.NonlinearWave.Morawetz.ConeFlux
public import PDE.Analysis.Integration.Cone.Transport
import CAS.ExactTactic

/-!
# The exact completed-square identity for the cone current

The scaling current pulled back to the cone equals half the outer square trace
minus the weighted radial square in dimension three. Integrability follows from
the finite cone densities, with no regularity or limit at the tip.

This is the formula (10) of the proof of Evans, §12.4, Theorem 2, obtained as in Evans through the
pullback `u*(y) = u(y, T - |y|)` of (12) and the identity (13).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, proof of Theorem 2, equations (10)-(13).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set Filter PDE PDE.Common PDE.Analysis NormedSpace
open scoped RealInnerProductSpace

namespace WaveEquation

/-- The angular scaling-current flux pulled back to a backward cone. -/
def coneProfileScalingFlux {n : ℕ} (V : ℝ → ℝ) (a T : ℝ) (c : ℝ^n)
    (u : ℝ^(n + 1) → ℝ) (x : ℝ^n) : ℝ :=
  coneCurrentNormalFlux (scalingCurrentDensity V a (timeSpaceCons T c) u)
    (fun p ↦ WithLp.toLp 2 (fun i ↦ scalingCurrentFlux V a (timeSpaceCons T c) u i p))
    (timeSpaceCons (T - ‖x - c‖) x, normalize (x - c))

/-- Away from the tip the current is the radial quadratic term and its amplitude cross term.
The potential cancels; no field equation is used. -/
theorem coneProfileScalingFlux_eq {n : ℕ} (V : ℝ → ℝ) (a T : ℝ) (c : ℝ^n)
    (u : ℝ^(n + 1) → ℝ) {x : ℝ^n} (hx : x ≠ c) :
    coneProfileScalingFlux V a T c u x = -‖x - c‖ * ⟪coneProfileGradient T c u x, normalize (x -
      c)⟫ ^ 2 - a * coneProfile T c u x * ⟪coneProfileGradient T c u x, normalize (x - c)⟫ := by
  let p := timeSpaceCons (T - ‖x - c‖) x
  let ν := normalize (x - c)
  have hν : ∑ i : Fin n, ν i ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, norm_normalize (sub_ne_zero.mpr hx), one_pow]
  have hc := scalingCurrent_normalFlux (V := V) a (timeSpaceCons T c) u
    (p := p) (r := ‖x - c‖) (ν := ν)
    (by simp [p]) (fun i ↦ by
      simpa only [p, timeSpaceCons_succ, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] using
        (congrArg (fun z : ℝ^n ↦ z i) (norm_smul_normalize (x - c))).symm) hν
  have hd : ⟪coneProfileGradient T c u x, ν⟫ =
      (∑ i : Fin n, ν i * (∂[i.succ] u) p) - (∂[0] u) p := by
    change (∑ i : Fin n, ν i * ((∂[i.succ] u) p - (∂[0] u) p * ν i)) = _
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    congr 1
    calc
      (∑ i : Fin n, ν i * ((∂[0] u) p * ν i)) = (∂[0] u) p * ∑ i : Fin n, ν i ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        ring
      _ = _ := by rw [hν, mul_one]
  have hflux : coneProfileScalingFlux V a T c u x =
      -‖x - c‖ * ((∂[0] u) p - ∑ i : Fin n, ν i * (∂[i.succ] u) p) ^ 2 +
        a * coneProfile T c u x * ((∂[0] u) p - ∑ i : Fin n, ν i * (∂[i.succ] u) p) := by
    simpa only [coneProfileScalingFlux, coneCurrentNormalFlux, coneProfile,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      WithLp.ofLp_toLp, mul_comm] using hc
  have hq : (∂[0] u) p - ∑ i : Fin n, ν i * (∂[i.succ] u) p =
      -⟪coneProfileGradient T c u x, ν⟫ := by linarith
  rw [hflux, hq]
  change -‖x - c‖ * (-⟪coneProfileGradient T c u x, ν⟫) ^ 2 +
    a * coneProfile T c u x * (-⟪coneProfileGradient T c u x, ν⟫) = _
  ring

namespace ConeProfile

private theorem square_expansion {ρ : ℝ} (hρ : ρ ≠ 0) (w d : ℝ) :
    ρ * (d + w / ρ) ^ 2 = ρ * d ^ 2 + 2 * (w * d) + w ^ 2 / ρ := by
  cas using hρ

/-- The exact cone-current identity `A = boundary/2 - weighted square` in dimension three.
Finite densities supply H¹ membership and every integrability assertion used here.
This is the pulled-back current identity; conversion to Hausdorff cone measure is separate. -/
theorem integral_scalingFlux_eq_boundary_sub_square (V : ℝ → ℝ) {T r : ℝ} {c : ℝ^3} {u : ℝ^4 → ℝ}
    (hr : 0 < r)
    (hu : ∀ x ∈ closedBall c r, x ≠ c → ContDiffAt ℝ 1 u (timeSpaceCons (T - ‖x - c‖) x))
    (hgradient : IntegrableOn (fun x ↦ ‖coneProfileGradient T c u x‖ ^ 2) (ball c r))
    (hpotential : IntegrableOn (fun x ↦ coneProfile T c u x ^ 6) (ball c r)) :
    (∫ x in ball c r, coneProfileScalingFlux V 1 T c u x) =
      (1 / 2 : ℝ) * sphereIntegral 3 (fun x ↦ coneProfile T c u x ^ 2) c r -
        ∫ x in ball c r, ‖x - c‖ *
          (⟪coneProfileGradient T c u x, normalize (x - c)⟫ +
            coneProfile T c u x / ‖x - c‖) ^ 2 := by
  let w := coneProfile T c u
  let d := fun x ↦ ⟪coneProfileGradient T c u x, normalize (x - c)⟫
  obtain ⟨hD, hcross, hweight⟩ := integrable_radial_terms (by omega : 3 ≤ 3) hr
    (fun x hx hne ↦ hu x (ball_subset_closedBall hx) hne) hgradient hpotential
  change IntegrableOn (fun x ↦ ‖x - c‖ * d x ^ 2) (ball c r) at hD
  change IntegrableOn (fun x ↦ w x * d x) (ball c r) at hcross
  change IntegrableOn (fun x ↦ w x ^ 2 / ‖x - c‖) (ball c r) at hweight
  have hsum : IntegrableOn (fun x ↦ ‖x - c‖ * d x ^ 2 + 2 * (w x * d x))
      (ball c r) := by
    simpa only [Pi.add_apply, IntegrableOn] using! hD.add (hcross.const_mul 2)
  have ha : (∫ x in ball c r, coneProfileScalingFlux V 1 T c u x) =
      -(∫ x in ball c r, ‖x - c‖ * d x ^ 2) - ∫ x in ball c r, w x * d x := by
    calc
      _ = ∫ x in ball c r, -(‖x - c‖ * d x ^ 2) - w x * d x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (volume.ae_ne c)] with x hx
        simp only [coneProfileScalingFlux_eq V 1 T c u hx, one_mul, neg_mul, w, d]
      _ = _ := by rw [integral_sub (f := fun x ↦ -(‖x - c‖ * d x ^ 2)) hD.neg hcross, integral_neg]
  have hs : (∫ x in ball c r, ‖x - c‖ * (d x + w x / ‖x - c‖) ^ 2) =
      (∫ x in ball c r, ‖x - c‖ * d x ^ 2) +
        2 * (∫ x in ball c r, w x * d x) + ∫ x in ball c r, w x ^ 2 / ‖x - c‖ := by
    calc
      _ = ∫ x in ball c r, (‖x - c‖ * d x ^ 2 + 2 * (w x * d x)) + w x ^ 2 / ‖x - c‖ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (volume.ae_ne c)] with x hx
        exact square_expansion (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)) (w x) (d x)
      _ = _ := by
        rw [integral_add hsum hweight, integral_add hD (hcross.const_mul 2), integral_const_mul]
  have hboundary := radial_square_flux_three hr hu hgradient hpotential
  change (∫ x in ball c r, coneProfileScalingFlux V 1 T c u x) =
    (1 / 2 : ℝ) * sphereIntegral 3 (fun x ↦ w x ^ 2) c r -
      ∫ x in ball c r, ‖x - c‖ * (d x + w x / ‖x - c‖) ^ 2
  rw [ha, hs]
  change (∫ x in ball c r, w x ^ 2 / ‖x - c‖) + (∫ x in ball c r, w x * d x) =
    (1 / 2 : ℝ) * sphereIntegral 3 (fun x ↦ w x ^ 2) c r at hboundary
  linarith

end ConeProfile
end WaveEquation
