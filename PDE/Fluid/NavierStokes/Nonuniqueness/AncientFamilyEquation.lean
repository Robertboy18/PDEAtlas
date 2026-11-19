/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.AncientFamily

/-!
# The decoded equation of the ancient correction

A fixed point `u = b c + G (N u)` of the ancient equation (`AncientFamily`) decodes at every
`τ ≤ 0` to (2.15) of Hou, Wang and Yang:

`U(τ) = e^{μτ} c e + ∫_{-∞}^τ Ks(τ - σ) N(σ) dσ - ∫_τ^0 Ku(σ - τ) N(σ) dσ`,

with `N(σ) = F(σ) + L_far(σ) U(σ) - (U(σ)·∇)U(σ)` (`correctionForcing`), the cutoff forcing and
coefficient at order two and the unprojected convection. The kernels apply the Leray
projection: the unstable kernel takes values in the divergence-free range of `P`, and the stable
kernel is `(1 - P) S(r) Π`, where the gain `S(r)` preserves divergence-free fields. So the
decoded ancient correction is divergence-free at every `τ ≤ 0`.

## Main results

* `correctionForcing`, `ancientLift_ancientForcing`.
* `ancientLift_eq_of_fixedPoint`, `ancientLift_ancientCorrection`: the decoded equation (2.15).
* `leraySobolev_ancientLift_ancientCorrection`: `Π U_cor(τ) = U_cor(τ)` for `τ ≤ 0`.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 2.2, (2.11), p. 12, and
  (2.15), p. 13.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open PDE.Analysis.Evolution NavierStokes.SobolevConvection NavierStokes.Selfsimilar
open scoped ENNReal BoundedContinuousFunction

namespace NavierStokes.Selfsimilar.ProfileDichotomy

variable {b : Fin 3 → DerivLp 3 ∞ Set.univ} {c : Fin 3 → Fin 3 → DerivLp 3 ∞ Set.univ}
  {hk2 : ProfileCoefficientBounds 2 b c} {hk3 : ProfileCoefficientBounds 3 b c}
  (d : ProfileDichotomy b c hk2 hk3)

/-- At positive lags the stable kernel takes values in divergence-free fields. -/
theorem leraySobolev_Ks {r : ℝ} (hr : 0 < r) (x : VectorH 3 2) :
    leraySobolev 3 3 (d.Ks r x) = d.Ks r x := by
  rw [d.Ks_apply, map_sub, d.leraySobolev_P,
    leraySobolev_profileGain _ hr (leraySobolev_idempotent x)]

/-- The unstable kernel takes values in divergence-free fields. -/
theorem leraySobolev_Ku (r : ℝ) (x : VectorH 3 2) :
    leraySobolev 3 3 (d.Ku r x) = d.Ku r x := by
  rw [← d.P_Ku, d.leraySobolev_P]

end NavierStokes.Selfsimilar.ProfileDichotomy

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

variable (D : UnstableProfile)

/-- The forcing `F(σ) + L_far(σ) v(σ) - (v(σ)·∇)v(σ)` of (2.11) along a path `v` in vector `H³`,
with the cutoff forcing and coefficient at order two and the unprojected convection; the kernels
of the dichotomy apply the Leray projection. -/
def correctionForcing (R : ℝ) (v : ℝ → VectorH 3 3) (σ : ℝ) : VectorH 3 2 :=
  cutoffForcing D R 2 σ + cutoffCoefficient D R 2 σ (v σ) - convection (v σ) (v σ)

variable {D} {R s : ℝ}

/-- At nonpositive times the decoded ancient forcing of a path is the forcing of (2.11) along the
decoded path. -/
theorem ancientLift_ancientForcing (u : Iic (0 : ℝ) →ᵇ VectorH 3 3) {σ : ℝ} (hσ : σ ≤ 0) :
    ancientLift (2 * D.dichotomy.η) (ancientForcing D R u) σ =
      correctionForcing D R (ancientLift D.dichotomy.η u) σ := by
  rw [ancientForcing, ancientLift_fullPathForcing,
    ancientLift_cutoffForcingPath D D.dichotomy.η_le hσ,
    ancientLift_cutoffCoefficientPath D D.dichotomy.η_le hσ, correctionForcing,
    neg_apply, neg_apply, sub_eq_add_neg]

/-- A continuous linear map fixing the integrand on a measurable set fixes the integral. -/
private theorem map_setIntegral_of_forall_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (L : E →L[ℝ] E) {f : ℝ → E} {S : Set ℝ} (hS : MeasurableSet S)
    (hf : ∀ x ∈ S, L (f x) = f x) : L (∫ x in S, f x) = ∫ x in S, f x := by
  by_cases hint : IntegrableOn f S
  · rw [← L.integral_comp_comm hint]
    exact setIntegral_congr_fun hS hf
  · rw [integral_undef hint, map_zero]

/-- **The decoded ancient equation (2.15).** A fixed point of the ancient equation with
homogeneous part `b c` decodes, at every `τ ≤ 0`, to the homogeneous unstable solution
`e^{μτ} c e` plus the past integral of the stable kernel minus the future integral of the
unstable kernel against the forcing of (2.11). -/
theorem ancientLift_eq_of_fixedPoint {c : ℝ} {u : Iic (0 : ℝ) →ᵇ VectorH 3 3}
    (hu : u = D.dichotomy.b c + D.ancientGreen (ancientForcing D R u)) {τ : ℝ} (hτ : τ ≤ 0) :
    ancientLift D.dichotomy.η u τ = Real.exp (D.dichotomy.μ * τ) • (c • D.dichotomy.e) +
      (ancientDuhamel D.dichotomy.Ks (correctionForcing D R (ancientLift D.dichotomy.η u)) τ -
        backwardDuhamel D.dichotomy.Ku (correctionForcing D R (ancientLift D.dichotomy.η u)) 0
          τ) := by
  rw [ancientLift_mixed_fixedPoint_of_joint _ _ _ _ _ _ _ _ _ _ _ hu hτ,
    D.dichotomy.ancientLift_b c τ hτ]
  congr 2
  · unfold ancientDuhamel
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
    rw [ancientLift_ancientForcing u (by linarith [mem_Ioi.mp hr])]
  · unfold backwardDuhamel
    refine intervalIntegral.integral_congr fun σ hσ ↦ ?_
    rw [uIcc_of_le hτ] at hσ
    rw [ancientLift_ancientForcing u hσ.2]

/-- The decoded ancient correction solves (2.15) with unstable terminal coordinate `s c₀ e`. -/
theorem ancientLift_ancientCorrection (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    {τ : ℝ} (hτ : τ ≤ 0) :
    ancientLift D.dichotomy.η (ancientCorrection D R s) τ =
      Real.exp (D.dichotomy.μ * τ) • ((s * D.ancientAmplitude) • D.dichotomy.e) +
        (ancientDuhamel D.dichotomy.Ks
            (correctionForcing D R (ancientLift D.dichotomy.η (ancientCorrection D R s))) τ -
          backwardDuhamel D.dichotomy.Ku
            (correctionForcing D R (ancientLift D.dichotomy.η (ancientCorrection D R s))) 0 τ) :=
  ancientLift_eq_of_fixedPoint (ancientCorrection_spec hR hs).2 hτ

/-- The decoded ancient correction is divergence-free at every `τ ≤ 0`. -/
theorem leraySobolev_ancientLift_ancientCorrection (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) {τ : ℝ} (hτ : τ ≤ 0) :
    leraySobolev 3 3 (ancientLift D.dichotomy.η (ancientCorrection D R s) τ) =
      ancientLift D.dichotomy.η (ancientCorrection D R s) τ := by
  rw [ancientLift_ancientCorrection hR hs hτ, map_add, map_sub, map_smul, map_smul,
    D.dichotomy.leraySobolev_e]
  congr 2
  · exact map_setIntegral_of_forall_eq _ measurableSet_Ioi fun r hr ↦
      D.dichotomy.leraySobolev_Ks hr _
  · unfold backwardDuhamel
    rw [intervalIntegral.integral_of_le hτ]
    exact map_setIntegral_of_forall_eq _ measurableSet_Ioc fun σ _ ↦
      D.dichotomy.leraySobolev_Ku _ _

end NavierStokes.Nonuniqueness
