/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonlinearity.LebesgueConvection
public import PDE.Fluid.NavierStokes.Nonuniqueness.Localization
public import PDE.Fluid.NavierStokes.Nonuniqueness.ProfileCoefficients
public import PDE.Parabolic.Heat.WholeSpace.GaussianFlowDilation
import PDE.Analysis.Calculus.Homogeneous

/-!
# The cutoff field and its coefficient and forcing paths

Let `U` be an unstable profile with far field `u_in(x) = ‖x‖⁻¹ A(x)`, and let
`u_in = u_loc + w` be the localization at radius `R`. The cutoff field is the heat flow
`u_cut(t) = -e^{tΔ} w` of the remainder, in similarity variables `t = e^τ`, `x = e^{τ/2} ξ`:

`U_cut(τ, ξ) = -e^{τ/2} (e^{e^τ Δ} w)(e^{τ/2} ξ) = -(G₁ * w_τ)(ξ)`,
`w_τ(x) = e^{τ/2} w(e^{τ/2} x)`.

For `r ≥ 4` the cutoff field is a continuous path in `W^{k,r}` (`cutoffSobolev`) with
`‖U_cut(τ)‖_{W^{k,r}} ≤ C_k (e^{τ/2} / R)^{1/4}`, which is (2.10) of Hou, Wang and Yang with `p = 4`
(`norm_cutoffSobolev_le_rpow`).

The correction `U_cor = U - Ũ - U_cut` solves (2.11) with the linear coefficient
`L_far(τ) v = -Π(U_cut(τ)·∇v + v·∇U_cut(τ))` and the forcing
`F(τ) = -Π(U_cut·∇U_cut + Ũ·∇U_cut + U_cut·∇Ũ)`. At every order `k`, `L_far(τ)` maps vector
`H^{k+1}` to vector `H^k` and `F(τ)` lies in vector `H^k`; both depend continuously on `τ`, and
(2.13) bounds them by a constant times `(e^{τ/2}/R)^{1/4}`, the forcing for `R ≥ 1` and `τ ≤ 0`. As
bounded continuous paths on `τ ≤ 0` in the exponential weights `η` and `2η` they are
`cutoffCoefficientPathOfOrder` and `cutoffForcingPathOfOrder`, and at the order `H³ → H²` of the
ancient fixed point `cutoffCoefficientPath` and `cutoffForcingPath`. For `η ≤ 1/16` they decode to
`L_far(τ)` and `F(τ)` and have norms at most a constant times `R^{-1/4}`, the forcing for `R ≥ 1`;
for `η > 1/16` the paths are zero, so the fixed point is set up with `η ≤ 1/16`.

## Main results

* `cutoffField`, `cutoffField_eq_conv`, `cutoffField_eq_remainder`.
* `cutoffSobolev`, `continuous_cutoffSobolev`, `norm_cutoffSobolev_le`,
  `norm_cutoffSobolev_le_rpow`, `baseRepresentative_cutoffSobolev`.
* `cutoffCoefficient`, `profileConvection_cutoffSobolev_base_ae`,
  `norm_cutoffCoefficient_le_rpow`; `cutoffForcing`, `cutoffConvection_base_ae`,
  `norm_cutoffForcing_le_rpow`.
* `cutoffCoefficientPath`, `ancientLift_cutoffCoefficientPath`,
  `norm_cutoffCoefficientPath_le`; `cutoffForcingPath`, `ancientLift_cutoffForcingPath`,
  `norm_cutoffForcingPath_le`; at every order `cutoffCoefficientPathOfOrder` and
  `cutoffForcingPathOfOrder`.

## How it works

We write the cutoff field as the time-one heat flow of the rescaled remainder,
`U_cut(τ) = -(G₁ * w_τ)` with `w_τ(x) = e^{τ/2} w(e^{τ/2} x)`, by the parabolic scaling of the heat
flow (`cutoffField_eq_conv`); by the scaling of the localization, `w_τ` is the remainder at radius
`e^{-τ/2} R` (`cutoffField_eq_remainder`). Since `w ∈ L⁴` and `G₁` smooths `L⁴` into every
`W^{k,r}`, `r ≥ 4`, the path is continuous (`continuous_cutoffSobolev`): dilations are only strongly
continuous on `L⁴`, but they act on the datum before the smoothing. Young's inequality and
`‖w_τ‖_{L⁴} = e^{τ/8} ‖w‖_{L⁴}` give `‖U_cut(τ)‖_{W^{k,r}} ≤ C_k e^{τ/8} ‖w‖_{L⁴}`
(`norm_cutoffSobolev_le`), and `‖w‖_{L⁴} = C R^{-1/4}` turns this into (2.10). The coefficient bound
is the bound of `profileTransport` with `U_cut` in `W^{k+1,∞}` (`norm_cutoffCoefficient_le_rpow`);
the forcing goes through the `L⁴` convection `lebesgueConvection`, since `U_cut` and `Ũ` are in `L⁴`
but not in `L²`, and the quadratic term `U_cut·∇U_cut`, of order `ρ²` for `ρ = (e^{τ/2}/R)^{1/4}`,
is at most of order `ρ` because `ρ ≤ 1` for `R ≥ 1` and `τ ≤ 0` (`norm_cutoffForcing_le_rpow`). On
`τ ≤ 0` both decay like `e^{τ/8}` (`norm_cutoffCoefficient_le`, `norm_cutoffForcing_le`), which is
at most `e^{ητ}` and `e^{2ητ}` for `η ≤ 1/16` (`norm_cutoffCoefficient_le_exp`,
`norm_cutoffForcing_le_exp`), and this makes them bounded continuous paths in the two weights.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 2.2, construction of the
  cutoff and (2.8)-(2.13), p. 12.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace HeatEquation.WholeSpace
open PDE.Analysis.Evolution NavierStokes.SobolevConvection IncompressibleFlow
open scoped ENNReal Sobolev BoundedContinuousFunction

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

namespace UnstableProfile

variable (D : UnstableProfile)

/-- The far field `‖x‖⁻¹ A(x)` of an unstable profile is homogeneous of degree `-1`. -/
theorem farField_smul (x : ℝ^3) {c : ℝ} (hc : 0 < c) :
    ‖c • x‖⁻¹ • D.A (c • x) = c⁻¹ • (‖x‖⁻¹ • D.A x) :=
  PDE.inv_norm_smul_apply_smul_of_homogeneous D.A_homogeneous x hc

/-- The far field `‖x‖⁻¹ A(x)` of an unstable profile is smooth away from the origin. -/
theorem contDiffAt_farField {x : ℝ^3} (hx : x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y ↦ ‖y‖⁻¹ • D.A y) x :=
  PDE.contDiffAt_inv_norm_smul hx (D.A_contDiffAt x hx)

/-- The localization remainder of the far field lies in `L⁴` at every radius. -/
theorem memLp_four_localizationRemainder (R : ℝ) :
    MemLp (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) 4 volume :=
  memLp_localizationRemainder (fun x _ hc ↦ D.farField_smul x hc)
    (fun _ hx ↦ D.contDiffAt_farField hx) (by norm_num) (by simp)

/-- The `L⁴` norm of the localization remainder of the far field is
`localizationConstant (‖·‖⁻¹ • A) * R^{-1/4}`. -/
theorem toReal_eLpNorm_localizationRemainder {R : ℝ} (hR : 0 < R) :
    (eLpNorm (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) 4 volume).toReal =
      localizationConstant (fun x ↦ ‖x‖⁻¹ • D.A x) * R ^ (-(1 / 4 : ℝ)) := by
  rw [eLpNorm_localizationRemainder_four hR (fun x _ hc ↦ D.farField_smul x hc)
    (fun _ hx ↦ D.contDiffAt_farField hx), ENNReal.toReal_ofReal]
  exact mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg hR.le _)

end UnstableProfile

variable (D : UnstableProfile) (R : ℝ)

/-! ### The cutoff field -/

/-- The cutoff field `U_cut(τ, ξ) = -e^{τ/2} (e^{e^τ Δ} w)(e^{τ/2} ξ)` in similarity variables,
the heat flow `u_cut(t) = -e^{tΔ} w` of the localization remainder `w` at radius `R` of the far
field `‖x‖⁻¹ A(x)`. -/
def cutoffField (τ : ℝ) (ξ : ℝ^3) : ℝ^3 :=
  -(Real.exp (τ / 2) • gaussianFlow (Real.exp τ)
    (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) (Real.exp (τ / 2) • ξ))

/-- The cutoff field is minus the time-one heat flow of the rescaled remainder:
`U_cut(τ) = -(G₁ * w_τ)` with `w_τ(x) = e^{τ/2} w(e^{τ/2} x)`. -/
theorem cutoffField_eq_conv (τ : ℝ) :
    cutoffField D R τ = -gaussianFlow 1 (fun x ↦ Real.exp (τ / 2) •
      localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R (Real.exp (τ / 2) • x)) := by
  funext ξ
  have hscale := gaussianFlow_scaling (Real.exp_pos (τ / 2)) 1
    (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) ξ
  rw [mul_one, sq, ← Real.exp_add, add_halves] at hscale
  rw [cutoffField, hscale, Pi.neg_apply,
    gaussianFlow_const_smul 1 (Real.exp (τ / 2))
      (fun x ↦ localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R (Real.exp (τ / 2) • x))]
  rfl

/-- The rescaled remainder is the remainder at the radius `e^{-τ/2} R`, so
`U_cut(τ) = -(G₁ * w_{e^{-τ/2} R})`. -/
theorem cutoffField_eq_remainder {R : ℝ} (hR : 0 < R) (τ : ℝ) :
    cutoffField D R τ = -gaussianFlow 1
      (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) (Real.exp (-(τ / 2)) * R)) := by
  rw [cutoffField_eq_conv, Real.exp_neg]
  congr 2
  funext x
  exact localizationRemainder_smul_apply hR (fun x _ hc ↦ D.farField_smul x hc)
    (Real.exp_pos _) x

/-- The cutoff field is the time-one heat flow of the rescaled negative remainder. -/
theorem cutoffField_eq_gaussianFlow_neg (τ : ℝ) :
    cutoffField D R τ = gaussianFlow 1 (fun x ↦ Real.exp (τ / 2) •
      (-localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) (Real.exp (τ / 2) • x)) := by
  rw [cutoffField_eq_conv]
  have h := gaussianFlow_const_smul 1 (-1 : ℝ) (fun x ↦ Real.exp (τ / 2) •
    localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R (Real.exp (τ / 2) • x))
  rw [neg_one_smul] at h
  rw [← h]
  congr 1
  funext x
  simp only [Pi.neg_apply, smul_neg, neg_one_smul]

/-- The cutoff field is smooth. -/
theorem contDiff_cutoffField (τ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (cutoffField D R τ) := by
  rw [cutoffField_eq_gaussianFlow_neg]
  exact contDiff_gaussianFlow_one_dilate (D.memLp_four_localizationRemainder R).neg
    (by norm_num) τ

/-- The components of the cutoff field `U_cut(τ)` as elements of `W^{k,r}(ℝ³)`, `4 ≤ r ≤ ∞`. -/
def cutoffSobolev (k : ℕ) {r : ℝ≥0∞} (hr : 4 ≤ r) (τ : ℝ) : Fin 3 → W^{k,r}(ℝ^3) :=
  gaussianFlowOneDilateWkp (-localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R)
    (D.memLp_four_localizationRemainder R).neg (by norm_num) hr k τ

variable {R}

/-- The cutoff field is a continuous path in `W^{k,r}(ℝ³)` for every `k` and `4 ≤ r ≤ ∞`. -/
theorem continuous_cutoffSobolev (k : ℕ) {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 4 ≤ r) :
    Continuous (cutoffSobolev D R k hr) :=
  continuous_gaussianFlowOneDilateWkp (-localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R)
    (D.memLp_four_localizationRemainder R).neg (by norm_num) (by norm_num) hr k

/-- The base representatives of `cutoffSobolev` are the components of the cutoff field. -/
theorem baseRepresentative_cutoffSobolev (k : ℕ) {r : ℝ≥0∞} (hr : 4 ≤ r) (τ : ℝ) (i : Fin 3) :
    baseRepresentative (cutoffSobolev D R k hr τ i) =ᵐ[volume]
      fun x ↦ cutoffField D R τ x i := by
  rw [cutoffField_eq_gaussianFlow_neg]
  exact baseRepresentative_gaussianFlowOneDilateWkp _ _ _ hr k τ i

/-- The weak partial derivative `∂ⱼ` of the `i`-th component of `cutoffSobolev` is the
classical one almost everywhere. -/
theorem baseRepresentative_partialDerivCLM_cutoffSobolev (k : ℕ) {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hr : 4 ≤ r) (τ : ℝ) (i j : Fin 3) :
    baseRepresentative (partialDerivCLM j (cutoffSobolev D R (k + 1) hr τ i)) =ᵐ[volume]
      fun x ↦ fderiv ℝ (cutoffField D R τ) x (EuclideanSpace.single j 1) i := by
  rw [cutoffField_eq_gaussianFlow_neg]
  exact baseRepresentative_partialDerivCLM_vectorWkpOfContDiff _
    (contDiff_gaussianFlow_one_dilate (D.memLp_four_localizationRemainder R).neg (by norm_num) τ)
    (fun m _ ↦ memLp_iteratedFDeriv_gaussianFlow_one_dilate
      (D.memLp_four_localizationRemainder R).neg (by norm_num) hr τ m) i j

/-- The constant `∑_a ‖D^{|a|} G₁‖_{Lᵠ}` of the smoothing bound for the cutoff field in
`W^{k,r}`, with `q` the Young exponent of `4` and `r`. -/
def cutoffSobolevConstant (k : ℕ) (r : ℝ≥0∞) : ℝ :=
  ∑ a : DerivIndex 3 k, (eLpNorm (iteratedFDeriv ℝ a.toList.length
    (HeatEquation.heatKernelSchwartz 3)) (ENNReal.youngExponent 4 r) volume).toReal

theorem cutoffSobolevConstant_nonneg (k : ℕ) (r : ℝ≥0∞) : 0 ≤ cutoffSobolevConstant k r :=
  Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg

/-- The smoothing bound `‖U_cut(τ)‖_{W^{k,r}} ≤ C_k e^{τ/8} ‖w‖_{L⁴}`. -/
theorem norm_cutoffSobolev_le (k : ℕ) {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 4 ≤ r) (τ : ℝ) :
    ‖cutoffSobolev D R k hr τ‖ ≤ cutoffSobolevConstant k r * Real.exp (τ / 8) *
      (eLpNorm (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) 4 volume).toReal := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (cutoffSobolevConstant_nonneg k r)
    (Real.exp_pos _).le) ENNReal.toReal_nonneg)).mpr fun i ↦ ?_
  have h := norm_gaussianFlowOneDilateWkp_le
    (-localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R)
    (D.memLp_four_localizationRemainder R).neg (by norm_num) hr k τ i
  rw [eLpNorm_neg] at h
  have hexp : τ / 2 * (1 - ((3 : ℕ) : ℝ) * (4 : ℝ≥0∞)⁻¹.toReal) = τ / 8 := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    push_cast
    ring
  rw [hexp] at h
  exact h

/-- The smoothing bound (2.10), `‖U_cut(τ)‖_{W^{k,r}} ≤ C_k (e^{τ/2} / R)^{1/4}`, with `C_k`
independent of `τ` and `R`. -/
theorem norm_cutoffSobolev_le_rpow (k : ℕ) {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 4 ≤ r)
    (hR : 0 < R) (τ : ℝ) :
    ‖cutoffSobolev D R k hr τ‖ ≤ cutoffSobolevConstant k r *
      localizationConstant (fun x ↦ ‖x‖⁻¹ • D.A x) * (Real.exp (τ / 2) / R) ^ (1 / 4 : ℝ) := by
  refine (norm_cutoffSobolev_le D k hr τ).trans (le_of_eq ?_)
  rw [D.toReal_eLpNorm_localizationRemainder hR, Real.div_rpow (Real.exp_pos _).le hR.le,
    ← Real.exp_mul, Real.rpow_neg hR.le, div_eq_mul_inv]
  ring_nf

/-! ### The linear coefficient -/

variable (R)

/-- The linear coefficient `L_far(τ) v = -Π(U_cut(τ)·∇v + v·∇U_cut(τ))` of the correction
equation, from vector `H^{k+1}` to vector `H^k`. -/
def cutoffCoefficient (k : ℕ) (τ : ℝ) : VectorH 3 (k + 1) →L[ℝ] VectorH 3 k :=
  profileTransport k (cutoffSobolev D R (k + 1) le_top τ)

/-- The linear coefficient is the Leray projection of the unprojected transport. -/
theorem cutoffCoefficient_apply (k : ℕ) (τ : ℝ) (v : VectorH 3 (k + 1)) :
    cutoffCoefficient D R k τ v =
      -leraySobolev 3 k (profileConvection k (cutoffSobolev D R (k + 1) le_top τ) v) :=
  rfl

/-- The linear coefficient takes values in solenoidal fields. -/
theorem leraySobolev_cutoffCoefficient (k : ℕ) (τ : ℝ) (v : VectorH 3 (k + 1)) :
    leraySobolev 3 k (cutoffCoefficient D R k τ v) = cutoffCoefficient D R k τ v :=
  leraySobolev_profileTransport k _ v

/-- The components of the unprojected transport in the linear coefficient are
`∑ᵢ (U_cut,ᵢ ∂ᵢvⱼ + ∂ᵢU_cut,ⱼ vᵢ)` almost everywhere. -/
theorem profileConvection_cutoffSobolev_base_ae (k : ℕ) (τ : ℝ) (v : VectorH 3 (k + 1))
    (j : Fin 3) :
    baseRepresentative (profileConvection k (cutoffSobolev D R (k + 1) le_top τ) v j)
      =ᵐ[volume] fun x ↦ ∑ i : Fin 3,
        (cutoffField D R τ x i * baseRepresentative (partialDerivCLM i (v j)) x +
          fderiv ℝ (cutoffField D R τ) x (EuclideanSpace.single i 1) j *
            baseRepresentative (v i) x) := by
  filter_upwards [profileConvection_base_ae k (cutoffSobolev D R (k + 1) le_top τ) v j,
    ae_all_iff.mpr fun i ↦ baseRepresentative_cutoffSobolev D (k + 1) le_top τ i,
    ae_all_iff.mpr fun i ↦ baseRepresentative_partialDerivCLM_cutoffSobolev D k le_top τ j i]
    with x hx h0 h1
  rw [hx]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [h0 i, h1 i]

/-- The linear coefficient depends continuously on `τ` in the operator norm. -/
theorem continuous_cutoffCoefficient (k : ℕ) : Continuous (cutoffCoefficient D R k) :=
  (continuous_profileTransport k).comp (continuous_cutoffSobolev D (k + 1) le_top)

/-- The bound `2 · 3² · wkTopMultiplierNormBound 3 k · C_{k+1} ‖w‖_{L⁴}` of the linear
coefficient, with `C_{k+1} = cutoffSobolevConstant (k + 1) ∞`. -/
def cutoffCoefficientBound (k : ℕ) : ℝ :=
  profileTransportBound 3 k * cutoffSobolevConstant (k + 1) ⊤ *
    (eLpNorm (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) 4 volume).toReal

theorem cutoffCoefficientBound_nonneg (k : ℕ) : 0 ≤ cutoffCoefficientBound D R k :=
  mul_nonneg (mul_nonneg (profileTransportBound_nonneg 3 k)
    (cutoffSobolevConstant_nonneg (k + 1) ⊤)) ENNReal.toReal_nonneg

/-- The linear coefficient decays like `e^{τ/8}`. -/
theorem norm_cutoffCoefficient_le (k : ℕ) (τ : ℝ) :
    ‖cutoffCoefficient D R k τ‖ ≤ cutoffCoefficientBound D R k * Real.exp (τ / 8) := by
  refine (norm_profileTransport_le k _).trans ?_
  calc
    _ ≤ profileTransportBound 3 k * (cutoffSobolevConstant (k + 1) ⊤ * Real.exp (τ / 8) *
        (eLpNorm (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) 4 volume).toReal) :=
      mul_le_mul_of_nonneg_left (norm_cutoffSobolev_le D (k + 1) le_top τ)
        (profileTransportBound_nonneg 3 k)
    _ = _ := by unfold cutoffCoefficientBound; ring

/-- For `η ≤ 1/8` and `τ ≤ 0` the linear coefficient is at most `e^{ητ}` times its bound. -/
theorem norm_cutoffCoefficient_le_exp (k : ℕ) {η τ : ℝ} (hη : η ≤ 1 / 8) (hτ : τ ≤ 0) :
    ‖cutoffCoefficient D R k τ‖ ≤ Real.exp (η * τ) * cutoffCoefficientBound D R k := by
  refine (norm_cutoffCoefficient_le D R k τ).trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith))
    (cutoffCoefficientBound_nonneg D R k)

/-- The constant `2 · 3² · wkTopMultiplierNormBound 3 k · C_{k+1} · localizationConstant` of the
linear coefficient. -/
def cutoffCoefficientConstant (k : ℕ) : ℝ :=
  profileTransportBound 3 k * cutoffSobolevConstant (k + 1) ⊤ *
    localizationConstant (fun x ↦ ‖x‖⁻¹ • D.A x)

theorem cutoffCoefficientConstant_nonneg (k : ℕ) : 0 ≤ cutoffCoefficientConstant D k := by
  have := profileTransportBound_nonneg 3 k
  have := cutoffSobolevConstant_nonneg (k + 1) ⊤
  have : 0 ≤ localizationConstant (fun x ↦ ‖x‖⁻¹ • D.A x) := ENNReal.toReal_nonneg
  unfold cutoffCoefficientConstant
  positivity

variable {R}

/-- The first bound of (2.13): `‖L_far(τ)‖ ≤ C (e^{τ/2} / R)^{1/4}`. -/
theorem norm_cutoffCoefficient_le_rpow (k : ℕ) (hR : 0 < R) (τ : ℝ) :
    ‖cutoffCoefficient D R k τ‖ ≤
      cutoffCoefficientConstant D k * (Real.exp (τ / 2) / R) ^ (1 / 4 : ℝ) := by
  refine (norm_profileTransport_le k _).trans ?_
  calc
    _ ≤ profileTransportBound 3 k * (cutoffSobolevConstant (k + 1) ⊤ *
        localizationConstant (fun x ↦ ‖x‖⁻¹ • D.A x) * (Real.exp (τ / 2) / R) ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (norm_cutoffSobolev_le_rpow D (k + 1) le_top hR τ)
        (profileTransportBound_nonneg 3 k)
    _ = _ := by unfold cutoffCoefficientConstant; ring

variable (R)

/-- The linear coefficient `H^{k+1} → H^k` as a bounded continuous path on `τ ≤ 0` in the
exponential weight `η`: for `η ≤ 1/16` its value at `τ` is `e^{-ητ} L_far(τ)`, so it decodes to
`L_far(τ)`. For `η > 1/16` the path is zero (`cutoffCoefficientPathOfOrder_of_lt`), as is the
forcing path, so the ancient fixed point is set up with `η ≤ 1/16`. -/
def cutoffCoefficientPathOfOrder (k : ℕ) (η : ℝ) :
    Iic (0 : ℝ) →ᵇ (VectorH 3 (k + 1) →L[ℝ] VectorH 3 k) :=
  if hη : η ≤ 1 / 16 then
    ofAncientBound η ⟨cutoffCoefficient D R k, continuous_cutoffCoefficient D R k⟩
      (cutoffCoefficientBound D R k)
      fun _ ht ↦ norm_cutoffCoefficient_le_exp D R k (hη.trans (by norm_num)) ht
  else 0

/-- The coefficient path `H³ → H²` of the ancient fixed point, the case `k = 2` of
`cutoffCoefficientPathOfOrder`. -/
def cutoffCoefficientPath (η : ℝ) : Iic (0 : ℝ) →ᵇ (VectorH 3 3 →L[ℝ] VectorH 3 2) :=
  cutoffCoefficientPathOfOrder D R 2 η

variable {R}

/-- Above the weight `1/16` the coefficient path is zero. -/
theorem cutoffCoefficientPathOfOrder_of_lt (k : ℕ) {η : ℝ} (hη : 1 / 16 < η) :
    cutoffCoefficientPathOfOrder D R k η = 0 := by
  rw [cutoffCoefficientPathOfOrder, dite_eq_right (not_le.mpr hη)]

/-- The coefficient path decodes to the linear coefficient
`L_far(τ) = -Π(U_cut(τ)·∇ · + (·)·∇U_cut(τ))` at every `τ ≤ 0`. -/
theorem ancientLift_cutoffCoefficientPathOfOrder (k : ℕ) {η : ℝ} (hη : η ≤ 1 / 16) {τ : ℝ}
    (hτ : τ ≤ 0) :
    ancientLift η (cutoffCoefficientPathOfOrder D R k η) τ = cutoffCoefficient D R k τ := by
  rw [cutoffCoefficientPathOfOrder, dite_eq_left hη]
  exact ancientLift_ofAncientBound _ _ _ _ hτ

/-- The coefficient path is of size `R^{-1/4}`, uniformly in the weight `η ≤ 1/16`. -/
theorem norm_cutoffCoefficientPathOfOrder_le (k : ℕ) {η : ℝ} (hη : η ≤ 1 / 16) (hR : 0 < R) :
    ‖cutoffCoefficientPathOfOrder D R k η‖ ≤
      cutoffCoefficientConstant D k * R ^ (-(1 / 4 : ℝ)) := by
  rw [cutoffCoefficientPathOfOrder, dite_eq_left hη]
  refine (norm_ofAncientBound_le _ _ (cutoffCoefficientBound_nonneg D R k) _).trans
    (le_of_eq ?_)
  rw [cutoffCoefficientBound, D.toReal_eLpNorm_localizationRemainder hR,
    cutoffCoefficientConstant]
  ring

/-- Above the weight `1/16` the coefficient path `H³ → H²` is zero. -/
theorem cutoffCoefficientPath_of_lt {η : ℝ} (hη : 1 / 16 < η) :
    cutoffCoefficientPath D R η = 0 :=
  cutoffCoefficientPathOfOrder_of_lt D 2 hη

/-- The coefficient path `H³ → H²` decodes to the linear coefficient at every `τ ≤ 0`. -/
theorem ancientLift_cutoffCoefficientPath {η : ℝ} (hη : η ≤ 1 / 16) {τ : ℝ} (hτ : τ ≤ 0) :
    ancientLift η (cutoffCoefficientPath D R η) τ = cutoffCoefficient D R 2 τ :=
  ancientLift_cutoffCoefficientPathOfOrder D 2 hη hτ

/-- Applied to a field `v`, the decoded coefficient path is `-Π(U_cut(τ)·∇v + v·∇U_cut(τ))`;
the components of the unprojected transport are given by
`profileConvection_cutoffSobolev_base_ae`. -/
theorem ancientLift_cutoffCoefficientPath_apply {η : ℝ} (hη : η ≤ 1 / 16) {τ : ℝ} (hτ : τ ≤ 0)
    (v : VectorH 3 3) :
    ancientLift η (cutoffCoefficientPath D R η) τ v =
      -leraySobolev 3 2 (profileConvection 2 (cutoffSobolev D R 3 le_top τ) v) := by
  rw [ancientLift_cutoffCoefficientPath D hη hτ, cutoffCoefficient_apply]

/-- The coefficient path `H³ → H²` is of size `R^{-1/4}`, uniformly in the weight
`η ≤ 1/16`. -/
theorem norm_cutoffCoefficientPath_le {η : ℝ} (hη : η ≤ 1 / 16) (hR : 0 < R) :
    ‖cutoffCoefficientPath D R η‖ ≤ cutoffCoefficientConstant D 2 * R ^ (-(1 / 4 : ℝ)) :=
  norm_cutoffCoefficientPathOfOrder_le D 2 hη hR

/-! ### The forcing -/

variable (R)

/-- The unprojected forcing `U_cut·∇U_cut + Ũ·∇U_cut + U_cut·∇Ũ` in vector `H^k`, from the `L⁴`
convection of the cutoff field and the profile. -/
def cutoffConvection (k : ℕ) (τ : ℝ) : VectorH 3 k :=
  lebesgueConvection k (cutoffSobolev D R k le_rfl τ) (cutoffSobolev D R (k + 1) le_rfl τ) +
    lebesgueConvection k (D.velocityWkFour k) (cutoffSobolev D R (k + 1) le_rfl τ) +
    lebesgueConvection k (cutoffSobolev D R k le_rfl τ) (D.velocityWkFour (k + 1))

/-- The forcing `F(τ) = -Π(U_cut·∇U_cut + Ũ·∇U_cut + U_cut·∇Ũ)` of the correction equation, in
vector `H^k`. -/
def cutoffForcing (k : ℕ) (τ : ℝ) : VectorH 3 k :=
  -leraySobolev 3 k (cutoffConvection D R k τ)

/-- The forcing is solenoidal. -/
theorem leraySobolev_cutoffForcing (k : ℕ) (τ : ℝ) :
    leraySobolev 3 k (cutoffForcing D R k τ) = cutoffForcing D R k τ := by
  rw [cutoffForcing, map_neg, leraySobolev_idempotent]

/-- The components of the unprojected forcing are
`∑ᵢ (U_cut,ᵢ ∂ᵢU_cut,ⱼ + Ũᵢ ∂ᵢU_cut,ⱼ + U_cut,ᵢ ∂ᵢŨⱼ)` almost everywhere. -/
theorem cutoffConvection_base_ae (k : ℕ) (τ : ℝ) (j : Fin 3) :
    baseRepresentative (cutoffConvection D R k τ j) =ᵐ[volume] fun x ↦ ∑ i : Fin 3,
      (cutoffField D R τ x i *
          fderiv ℝ (cutoffField D R τ) x (EuclideanSpace.single i 1) j +
        D.U x i * fderiv ℝ (cutoffField D R τ) x (EuclideanSpace.single i 1) j +
        cutoffField D R τ x i * fderiv ℝ D.U x (EuclideanSpace.single i 1) j) := by
  have hadd₁ := baseRepresentative_add_ae
    (lebesgueConvection k (cutoffSobolev D R k le_rfl τ) (cutoffSobolev D R (k + 1) le_rfl τ) j +
      lebesgueConvection k (D.velocityWkFour k) (cutoffSobolev D R (k + 1) le_rfl τ) j)
    (lebesgueConvection k (cutoffSobolev D R k le_rfl τ) (D.velocityWkFour (k + 1)) j)
  have hadd₂ := baseRepresentative_add_ae
    (lebesgueConvection k (cutoffSobolev D R k le_rfl τ) (cutoffSobolev D R (k + 1) le_rfl τ) j)
    (lebesgueConvection k (D.velocityWkFour k) (cutoffSobolev D R (k + 1) le_rfl τ) j)
  simp only [domainMeasure, Measure.restrict_univ] at hadd₁ hadd₂
  filter_upwards [hadd₁, hadd₂,
    lebesgueConvection_base_ae k (cutoffSobolev D R k le_rfl τ)
      (cutoffSobolev D R (k + 1) le_rfl τ) j,
    lebesgueConvection_base_ae k (D.velocityWkFour k) (cutoffSobolev D R (k + 1) le_rfl τ) j,
    lebesgueConvection_base_ae k (cutoffSobolev D R k le_rfl τ) (D.velocityWkFour (k + 1)) j,
    ae_all_iff.mpr fun i ↦ baseRepresentative_cutoffSobolev D k le_rfl τ i,
    ae_all_iff.mpr fun i ↦ baseRepresentative_partialDerivCLM_cutoffSobolev D k le_rfl τ j i,
    ae_all_iff.mpr fun i ↦ baseRepresentative_vectorWkpOfContDiff (k := k) (p := 4) D.U
      D.contDiff_U (fun m _ ↦ D.derivatives_memLp_four m) i,
    ae_all_iff.mpr fun i ↦ baseRepresentative_partialDerivCLM_vectorWkpOfContDiff (k := k)
      (p := 4) D.U D.contDiff_U (fun m _ ↦ D.derivatives_memLp_four m) j i]
    with x h₁ h₂ hc₁ hc₂ hc₃ hU hdU hV hdV
  change baseRepresentative ((lebesgueConvection k (cutoffSobolev D R k le_rfl τ)
    (cutoffSobolev D R (k + 1) le_rfl τ) j + lebesgueConvection k (D.velocityWkFour k)
      (cutoffSobolev D R (k + 1) le_rfl τ) j) +
    lebesgueConvection k (cutoffSobolev D R k le_rfl τ) (D.velocityWkFour (k + 1)) j) x = _
  rw [h₁, h₂, hc₁, hc₂, hc₃, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hU i, hdU i, ← hV i, ← hdV i]
  rfl

/-- The unprojected forcing depends continuously on `τ`. -/
theorem continuous_cutoffConvection (k : ℕ) : Continuous (cutoffConvection D R k) := by
  have h₁ : Continuous (cutoffSobolev D R k (le_rfl : (4 : ℝ≥0∞) ≤ 4)) :=
    continuous_cutoffSobolev D k le_rfl
  have h₂ : Continuous (cutoffSobolev D R (k + 1) (le_rfl : (4 : ℝ≥0∞) ≤ 4)) :=
    continuous_cutoffSobolev D (k + 1) le_rfl
  have hL := (lebesgueConvection (n := 3) k).continuous
  unfold cutoffConvection
  exact (((hL.comp h₁).clm_apply h₂).add ((hL.comp continuous_const).clm_apply h₂)).add
    ((hL.comp h₁).clm_apply continuous_const)

/-- The forcing depends continuously on `τ`. -/
theorem continuous_cutoffForcing (k : ℕ) : Continuous (cutoffForcing D R k) := by
  unfold cutoffForcing
  exact ((leraySobolev 3 k).continuous.comp (continuous_cutoffConvection D R k)).neg

/-- The unprojected forcing is bounded by the norms of the cutoff field and of the profile in
`W^{k,4}` and `W^{k+1,4}`. -/
theorem norm_cutoffConvection_le (k : ℕ) (τ : ℝ) :
    ‖cutoffConvection D R k τ‖ ≤ (3 : ℝ) ^ 2 * holderProductBound 3 k *
      (‖cutoffSobolev D R k (le_rfl : (4 : ℝ≥0∞) ≤ 4) τ‖ *
          ‖cutoffSobolev D R (k + 1) (le_rfl : (4 : ℝ≥0∞) ≤ 4) τ‖ +
        ‖D.velocityWkFour k‖ * ‖cutoffSobolev D R (k + 1) (le_rfl : (4 : ℝ≥0∞) ≤ 4) τ‖ +
        ‖cutoffSobolev D R k (le_rfl : (4 : ℝ≥0∞) ≤ 4) τ‖ * ‖D.velocityWkFour (k + 1)‖) := by
  have h₁ := norm_lebesgueConvection_le k (cutoffSobolev D R k le_rfl τ)
    (cutoffSobolev D R (k + 1) le_rfl τ)
  have h₂ := norm_lebesgueConvection_le k (D.velocityWkFour k)
    (cutoffSobolev D R (k + 1) le_rfl τ)
  have h₃ := norm_lebesgueConvection_le k (cutoffSobolev D R k le_rfl τ)
    (D.velocityWkFour (k + 1))
  push_cast at h₁ h₂ h₃
  refine (norm_add₃_le).trans ?_
  calc
    _ ≤ _ := add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by ring

/-- The bound `3² · holderProductBound 3 k · (C_k C_{k+1} ‖w‖²_{L⁴} +
(‖Ũ‖_{W^{k,4}} C_{k+1} + C_k ‖Ũ‖_{W^{k+1,4}}) ‖w‖_{L⁴})` of the forcing on `τ ≤ 0`, with
`C_k = cutoffSobolevConstant k 4`. -/
def cutoffForcingBound (k : ℕ) : ℝ :=
  (3 : ℝ) ^ 2 * holderProductBound 3 k *
    (cutoffSobolevConstant k 4 * cutoffSobolevConstant (k + 1) 4 *
        (eLpNorm (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) 4 volume).toReal ^ 2 +
      (‖D.velocityWkFour k‖ * cutoffSobolevConstant (k + 1) 4 +
          cutoffSobolevConstant k 4 * ‖D.velocityWkFour (k + 1)‖) *
        (eLpNorm (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) 4 volume).toReal)

theorem cutoffForcingBound_nonneg (k : ℕ) : 0 ≤ cutoffForcingBound D R k := by
  have := cutoffSobolevConstant_nonneg k 4
  have := cutoffSobolevConstant_nonneg (k + 1) 4
  have := holderProductBound_nonneg 3 k
  unfold cutoffForcingBound
  positivity

variable {R}

/-- On `τ ≤ 0` the forcing decays like `e^{τ/8}`. -/
theorem norm_cutoffForcing_le (k : ℕ) {τ : ℝ} (hτ : τ ≤ 0) :
    ‖cutoffForcing D R k τ‖ ≤ cutoffForcingBound D R k * Real.exp (τ / 8) := by
  set W := (eLpNorm (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) 4 volume).toReal
  set K₁ := cutoffSobolevConstant k 4
  set K₂ := cutoffSobolevConstant (k + 1) 4
  set H := holderProductBound 3 k
  set s := Real.exp (τ / 8)
  have hW : 0 ≤ W := ENNReal.toReal_nonneg
  have hK₁ : 0 ≤ K₁ := cutoffSobolevConstant_nonneg k 4
  have hK₂ : 0 ≤ K₂ := cutoffSobolevConstant_nonneg (k + 1) 4
  have hH : 0 ≤ H := holderProductBound_nonneg 3 k
  have hs : 0 ≤ s := (Real.exp_pos _).le
  have hs1 : s ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hU₁ := norm_nonneg (D.velocityWkFour k)
  have hU₂ := norm_nonneg (D.velocityWkFour (k + 1))
  have ha₁ : ‖cutoffSobolev D R k (le_rfl : (4 : ℝ≥0∞) ≤ 4) τ‖ ≤ K₁ * s * W :=
    norm_cutoffSobolev_le D k le_rfl τ
  have ha₂ : ‖cutoffSobolev D R (k + 1) (le_rfl : (4 : ℝ≥0∞) ≤ 4) τ‖ ≤ K₂ * s * W :=
    norm_cutoffSobolev_le D (k + 1) le_rfl τ
  rw [cutoffForcing, norm_neg]
  calc
    _ ≤ ‖cutoffConvection D R k τ‖ := norm_leraySobolev_le _
    _ ≤ (3 : ℝ) ^ 2 * H * (K₁ * s * W * (K₂ * s * W) + ‖D.velocityWkFour k‖ * (K₂ * s * W) +
        K₁ * s * W * ‖D.velocityWkFour (k + 1)‖) := by
      refine (norm_cutoffConvection_le D R k τ).trans ?_
      gcongr
    _ = (3 : ℝ) ^ 2 * H * (K₁ * K₂ * W ^ 2 * s +
        (‖D.velocityWkFour k‖ * K₂ + K₁ * ‖D.velocityWkFour (k + 1)‖) * W) * s := by ring
    _ ≤ (3 : ℝ) ^ 2 * H * (K₁ * K₂ * W ^ 2 * 1 +
        (‖D.velocityWkFour k‖ * K₂ + K₁ * ‖D.velocityWkFour (k + 1)‖) * W) * s := by
      gcongr
    _ = cutoffForcingBound D R k * s := by unfold cutoffForcingBound; ring

/-- For `η ≤ 1/16` and `τ ≤ 0` the forcing is at most `e^{2ητ}` times its bound. -/
theorem norm_cutoffForcing_le_exp (k : ℕ) {η τ : ℝ} (hη : η ≤ 1 / 16) (hτ : τ ≤ 0) :
    ‖cutoffForcing D R k τ‖ ≤ Real.exp (2 * η * τ) * cutoffForcingBound D R k := by
  refine (norm_cutoffForcing_le D k hτ).trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith))
    (cutoffForcingBound_nonneg D R k)

/-- The constant `3² · holderProductBound 3 k · (C_k C_{k+1} C_A² + (‖Ũ‖_{W^{k,4}} C_{k+1} +
C_k ‖Ũ‖_{W^{k+1,4}}) C_A)` of the forcing, with `C_A = localizationConstant (‖·‖⁻¹ • A)`. -/
def cutoffForcingConstant (k : ℕ) : ℝ :=
  (3 : ℝ) ^ 2 * holderProductBound 3 k *
    (cutoffSobolevConstant k 4 * cutoffSobolevConstant (k + 1) 4 *
        localizationConstant (fun x ↦ ‖x‖⁻¹ • D.A x) ^ 2 +
      (‖D.velocityWkFour k‖ * cutoffSobolevConstant (k + 1) 4 +
          cutoffSobolevConstant k 4 * ‖D.velocityWkFour (k + 1)‖) *
        localizationConstant (fun x ↦ ‖x‖⁻¹ • D.A x))

theorem cutoffForcingConstant_nonneg (k : ℕ) : 0 ≤ cutoffForcingConstant D k := by
  have := holderProductBound_nonneg 3 k
  have := cutoffSobolevConstant_nonneg k 4
  have := cutoffSobolevConstant_nonneg (k + 1) 4
  have := norm_nonneg (D.velocityWkFour k)
  have := norm_nonneg (D.velocityWkFour (k + 1))
  have : 0 ≤ localizationConstant (fun x ↦ ‖x‖⁻¹ • D.A x) := ENNReal.toReal_nonneg
  unfold cutoffForcingConstant
  positivity

/-- The third bound of (2.13): for `R ≥ 1` and `τ ≤ 0`,
`‖F(τ)‖ ≤ C (e^{τ/2} / R)^{1/4}`. -/
theorem norm_cutoffForcing_le_rpow (k : ℕ) (hR : 1 ≤ R) {τ : ℝ} (hτ : τ ≤ 0) :
    ‖cutoffForcing D R k τ‖ ≤
      cutoffForcingConstant D k * (Real.exp (τ / 2) / R) ^ (1 / 4 : ℝ) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  set C := localizationConstant (fun x ↦ ‖x‖⁻¹ • D.A x)
  set K₁ := cutoffSobolevConstant k 4
  set K₂ := cutoffSobolevConstant (k + 1) 4
  set H := holderProductBound 3 k
  set ρ := (Real.exp (τ / 2) / R) ^ (1 / 4 : ℝ)
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hK₁ : 0 ≤ K₁ := cutoffSobolevConstant_nonneg k 4
  have hK₂ : 0 ≤ K₂ := cutoffSobolevConstant_nonneg (k + 1) 4
  have hH : 0 ≤ H := holderProductBound_nonneg 3 k
  have hρ : 0 ≤ ρ := Real.rpow_nonneg (div_nonneg (Real.exp_pos _).le hR0.le) _
  have hρ1 : ρ ≤ 1 := by
    refine Real.rpow_le_one (div_nonneg (Real.exp_pos _).le hR0.le) ?_ (by norm_num)
    rw [div_le_one hR0]
    exact (Real.exp_le_one_iff.mpr (by linarith)).trans hR
  have hU₁ := norm_nonneg (D.velocityWkFour k)
  have hU₂ := norm_nonneg (D.velocityWkFour (k + 1))
  have ha₁ : ‖cutoffSobolev D R k (le_rfl : (4 : ℝ≥0∞) ≤ 4) τ‖ ≤ K₁ * C * ρ :=
    norm_cutoffSobolev_le_rpow D k le_rfl hR0 τ
  have ha₂ : ‖cutoffSobolev D R (k + 1) (le_rfl : (4 : ℝ≥0∞) ≤ 4) τ‖ ≤ K₂ * C * ρ :=
    norm_cutoffSobolev_le_rpow D (k + 1) le_rfl hR0 τ
  rw [cutoffForcing, norm_neg]
  calc
    _ ≤ ‖cutoffConvection D R k τ‖ := norm_leraySobolev_le _
    _ ≤ (3 : ℝ) ^ 2 * H * (K₁ * C * ρ * (K₂ * C * ρ) + ‖D.velocityWkFour k‖ * (K₂ * C * ρ) +
        K₁ * C * ρ * ‖D.velocityWkFour (k + 1)‖) := by
      refine (norm_cutoffConvection_le D R k τ).trans ?_
      gcongr
    _ = (3 : ℝ) ^ 2 * H * (K₁ * K₂ * C ^ 2 * ρ +
        (‖D.velocityWkFour k‖ * K₂ + K₁ * ‖D.velocityWkFour (k + 1)‖) * C) * ρ := by ring
    _ ≤ (3 : ℝ) ^ 2 * H * (K₁ * K₂ * C ^ 2 * 1 +
        (‖D.velocityWkFour k‖ * K₂ + K₁ * ‖D.velocityWkFour (k + 1)‖) * C) * ρ := by
      gcongr
    _ = cutoffForcingConstant D k * ρ := by unfold cutoffForcingConstant; ring

variable (R)

/-- The forcing in vector `H^k` as a bounded continuous path on `τ ≤ 0` in the exponential
weight `2η`: for `η ≤ 1/16` its value at `τ` is `e^{-2ητ} F(τ)`, so it decodes to `F(τ)`. For
`η > 1/16` the path is zero (`cutoffForcingPathOfOrder_of_lt`), as is the coefficient path, so
the ancient fixed point is set up with `η ≤ 1/16`. -/
def cutoffForcingPathOfOrder (k : ℕ) (η : ℝ) : Iic (0 : ℝ) →ᵇ VectorH 3 k :=
  if hη : η ≤ 1 / 16 then
    ofAncientBound (2 * η) ⟨cutoffForcing D R k, continuous_cutoffForcing D R k⟩
      (cutoffForcingBound D R k) fun _ ht ↦ norm_cutoffForcing_le_exp D k hη ht
  else 0

/-- The forcing path in vector `H²` of the ancient fixed point, the case `k = 2` of
`cutoffForcingPathOfOrder`. -/
def cutoffForcingPath (η : ℝ) : Iic (0 : ℝ) →ᵇ VectorH 3 2 :=
  cutoffForcingPathOfOrder D R 2 η

variable {R}

/-- Above the weight `1/16` the forcing path is zero. -/
theorem cutoffForcingPathOfOrder_of_lt (k : ℕ) {η : ℝ} (hη : 1 / 16 < η) :
    cutoffForcingPathOfOrder D R k η = 0 := by
  rw [cutoffForcingPathOfOrder, dite_eq_right (not_le.mpr hη)]

/-- The forcing path decodes, in weight `2η`, to the forcing
`F(τ) = -Π(U_cut·∇U_cut + Ũ·∇U_cut + U_cut·∇Ũ)` at every `τ ≤ 0`; the components of the
unprojected forcing are given by `cutoffConvection_base_ae`. -/
theorem ancientLift_cutoffForcingPathOfOrder (k : ℕ) {η : ℝ} (hη : η ≤ 1 / 16) {τ : ℝ}
    (hτ : τ ≤ 0) :
    ancientLift (2 * η) (cutoffForcingPathOfOrder D R k η) τ = cutoffForcing D R k τ := by
  rw [cutoffForcingPathOfOrder, dite_eq_left hη]
  exact ancientLift_ofAncientBound _ _ _ _ hτ

/-- The forcing path is of size `R^{-1/4}` for `R ≥ 1`, uniformly in the weight `η ≤ 1/16`. -/
theorem norm_cutoffForcingPathOfOrder_le (k : ℕ) {η : ℝ} (hη : η ≤ 1 / 16) (hR : 1 ≤ R) :
    ‖cutoffForcingPathOfOrder D R k η‖ ≤ cutoffForcingConstant D k * R ^ (-(1 / 4 : ℝ)) := by
  rw [cutoffForcingPathOfOrder, dite_eq_left hη]
  refine (norm_ofAncientBound_le _ _ (cutoffForcingBound_nonneg D R k) _).trans ?_
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  set ρ := R ^ (-(1 / 4 : ℝ))
  set C := localizationConstant (fun x ↦ ‖x‖⁻¹ • D.A x)
  have hρ : 0 ≤ ρ := Real.rpow_nonneg hR0.le _
  have hρ1 : ρ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR (by norm_num)
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have := cutoffSobolevConstant_nonneg k 4
  have := cutoffSobolevConstant_nonneg (k + 1) 4
  have := holderProductBound_nonneg 3 k
  have hU₁ := norm_nonneg (D.velocityWkFour k)
  have hU₂ := norm_nonneg (D.velocityWkFour (k + 1))
  rw [cutoffForcingBound, D.toReal_eLpNorm_localizationRemainder hR0, cutoffForcingConstant]
  have hρ2 : (C * ρ) ^ 2 ≤ C ^ 2 * ρ := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg C)
  calc
    _ ≤ (3 : ℝ) ^ 2 * holderProductBound 3 k *
        (cutoffSobolevConstant k 4 * cutoffSobolevConstant (k + 1) 4 * (C ^ 2 * ρ) +
          (‖D.velocityWkFour k‖ * cutoffSobolevConstant (k + 1) 4 +
              cutoffSobolevConstant k 4 * ‖D.velocityWkFour (k + 1)‖) * (C * ρ)) := by
      gcongr
    _ = _ := by ring

/-- Above the weight `1/16` the forcing path in vector `H²` is zero. -/
theorem cutoffForcingPath_of_lt {η : ℝ} (hη : 1 / 16 < η) : cutoffForcingPath D R η = 0 :=
  cutoffForcingPathOfOrder_of_lt D 2 hη

/-- The forcing path in vector `H²` decodes, in weight `2η`, to the forcing at every
`τ ≤ 0`. -/
theorem ancientLift_cutoffForcingPath {η : ℝ} (hη : η ≤ 1 / 16) {τ : ℝ} (hτ : τ ≤ 0) :
    ancientLift (2 * η) (cutoffForcingPath D R η) τ = cutoffForcing D R 2 τ :=
  ancientLift_cutoffForcingPathOfOrder D 2 hη hτ

/-- The forcing path in vector `H²` is of size `R^{-1/4}` for `R ≥ 1`, uniformly in the weight
`η ≤ 1/16`. -/
theorem norm_cutoffForcingPath_le {η : ℝ} (hη : η ≤ 1 / 16) (hR : 1 ≤ R) :
    ‖cutoffForcingPath D R η‖ ≤ cutoffForcingConstant D 2 * R ^ (-(1 / 4 : ℝ)) :=
  norm_cutoffForcingPathOfOrder_le D 2 hη hR

end NavierStokes.Nonuniqueness
