/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Middle
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.FastLogCosh
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Gated.Bounds
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Gated.GenuineNonlinearity
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Cutoff

/-!
# A smooth globally hyperbolic gated flux

The fast law `kδ(s) = 2s + δ log(cosh s)`, the scalar gate cutoff `C`, and the
middle clock `g` define the flux

`F(x,y,z) = (-kδ(x) + b(y)z, g(y) + C(-y)φ(z) + C(y)φ(x), kδ(z) - b(-y)x)`.

For `0 < δ < 1/4`, every smooth feedback `φ` valued in `[-4, 1]` and every
smooth gate `b` with topological support in `(205, e)` give a globally smooth,
strictly hyperbolic flux with three genuinely nonlinear characteristic families. The middle speed
has absolute value at most `361/4000`, and both adjacent speed gaps exceed
`5/4`. The cutoff and clock curvatures combine into nonnegative pulse terms
with weights `1-φ` and `4+φ`, together with a strictly positive density term.
-/

@[expose] public noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile

open Set PDE.Analysis PDE.Analysis.ClockDensity
open scoped ContDiff

/-- The gated flux with the fast log-cosh law, scalar cutoff, and middle clock fixed. -/
def concreteGatedFlux (δ : ℝ) (φ b : ℝ → ℝ) : ℝ^3 → ℝ^3 :=
  GatedFlux.flux (fastLogCosh δ) MiddleClock.g cutoff φ b

/-- Smooth feedback and gate functions give a globally smooth concrete flux. -/
theorem contDiff_concreteGatedFlux (δ : ℝ) {φ b : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (concreteGatedFlux δ φ b) :=
  GatedFlux.contDiff_flux (contDiff_fastLogCosh δ) MiddleClock.contDiff_g contDiff_cutoff hφ hb

/-- The concrete scalar laws give global strict hyperbolicity and genuine nonlinearity
for every ordered characteristic family, with arbitrary smooth signed gate coefficients. -/
theorem concreteGatedFlux_smooth_strictlyHyperbolic_genuinelyNonlinear {δ e : ℝ} {φ b : ℝ → ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 1 / 4) (hφ : ContDiff ℝ ∞ φ) (hφrange : ∀ s, -4 ≤ φ s ∧ φ s ≤ 1)
    (hb : ContDiff ℝ ∞ b) (hsupport : tsupport b ⊆ Ioo (205 : ℝ) e) :
    ContDiff ℝ ∞ (concreteGatedFlux δ φ b) ∧ IsStrictlyHyperbolicOn (concreteGatedFlux δ φ b) univ ∧
      ∀ i : Fin 3, IsGenuinelyNonlinearFamily (concreteGatedFlux δ φ b) i := by
  have hk : ContDiff ℝ 2 (fastLogCosh δ) :=
    (contDiff_fastLogCosh δ).of_le (by simp)
  have hg : ContDiff ℝ 2 MiddleClock.g := MiddleClock.contDiff_g.of_le (by simp)
  have hC : ContDiff ℝ 2 cutoff := contDiff_cutoff.of_le (by simp)
  have hφ' : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hb' : Differentiable ℝ b := hb.differentiable (by simp)
  have hleft : ∀ s : ℝ, s ≤ 100 → cutoff s = 1 := fun _ hs ↦ cutoff_of_le hs
  have hright : ∀ s : ℝ, 205 ≤ s → cutoff s = 0 := fun _ hs ↦ cutoff_of_ge hs
  have hCslope (s : ℝ) : -(1 / 100 : ℝ) ≤ deriv cutoff s ∧ deriv cutoff s ≤ 0 :=
    ⟨by simpa only [neg_div] using neg_one_div_le_deriv_cutoff s, deriv_cutoff_nonpos s⟩
  have hδabs : |δ| < 1 / 4 := by simpa only [abs_of_pos hδ] using hδsmall
  have hkslope : ∀ s, 7 / 4 < deriv (fastLogCosh δ) s := seven_fourths_lt_deriv_fastLogCosh hδabs
  have hlow (q : ℝ^3) :
      -deriv (fastLogCosh δ) (q 0) < GatedFlux.middleSpeed MiddleClock.g cutoff φ q := by
    have hgap := GatedFlux.five_fourths_lt_left_gap (a := 100) (by norm_num)
      hleft MiddleClock.abs_deriv_g_le hCslope hφrange hkslope q
    linarith
  have hhigh (q : ℝ^3) :
      GatedFlux.middleSpeed MiddleClock.g cutoff φ q < deriv (fastLogCosh δ) (q 2) := by
    have hgap := GatedFlux.five_fourths_lt_right_gap (a := 100) (by norm_num)
      hleft MiddleClock.abs_deriv_g_le hCslope hφrange hkslope q
    linarith
  have hg2 (y : ℝ) : deriv (deriv MiddleClock.g) y =
      (qMinus y + 4 * qPlus y + qMinus (-y) + 4 * qPlus (-y)) / 100 +
        (1 / 1000000 : ℝ) * rho0 (y / 100) := by
    simpa only [MiddleClock.curvature] using MiddleClock.deriv_deriv_g y
  have hmiddle (q : ℝ^3) : 0 < GatedFlux.middleCurvature MiddleClock.g cutoff φ q :=
    GatedFlux.middleCurvature_pos deriv_deriv_cutoff hg2
      qMinus_nonneg qPlus_nonneg rho0_pos hφrange q
  refine ⟨contDiff_concreteGatedFlux δ hφ hb, ?_, fun i ↦ ?_⟩
  · exact GatedFlux.isStrictlyHyperbolicOn_univ (a := 100) (d := 205) (e := e)
      (hk.differentiable (by simp)) (hg.differentiable (by simp))
      (hC.differentiable (by simp)) hφ' hb' (by norm_num) (by norm_num)
      hleft hright hsupport hlow hhigh
  · exact GatedFlux.isGenuinelyNonlinearFamily (a := 100) (d := 205) (e := e)
      hk hg hC hφ' hb' (by norm_num) (by norm_num) hleft hright hsupport hlow hhigh
      (deriv_deriv_fastLogCosh_pos hδ) hmiddle i

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
