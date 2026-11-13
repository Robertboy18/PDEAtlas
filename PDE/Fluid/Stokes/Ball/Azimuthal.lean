/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.Separation
public import PDE.Analysis.Calculus.EuclideanBall.NormalCutoff
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Azimuthal coefficients of weak Neumann-Stokes eigenfunctions

The azimuthal test fields `v = G(‖x‖²) ψ₀(x)`, with `ψ₀ = mode R .azimuthal l 0` the swirl
field `x × ∇h_l` up to the factor `g_l(0)`, are smooth, divergence free, equivariant and of
parity `(-1)^{l+1}`. Their radial derivative `∑ⱼ xⱼ ∂ⱼ v = (2 ‖x‖² G' + l G)(‖x‖²) ψ₀` vanishes
on the sphere `‖x‖ = R` when `2 R² G'(R²) + l G(R²) = 0`. For such `G` the integration by parts
of `PDE.Analysis.integral_sum_mul_partialDeriv_add_mul_eq_zero` against `T = ∇v` turns the weak
eigenvalue equation `∫ ∇u : ∇v = μ ∫ ⟪u, v⟫` into `∫ ⟪u, Δv + μ v⟫ = 0`, with no boundary term.
-/

@[expose] public noncomputable section

open MeasureTheory Set Real MvPolynomial
open PDE (partialDeriv laplacian divergence)
open PDE.Analysis.SpecialFunctions PDE.CoordinateSystems PDE.CoordinateSystems.Spherical
open scoped RealInnerProductSpace ContDiff

namespace PDE.Fluid.Stokes.Ball

/-- The azimuthal test field `G(‖x‖²) ψ₀(x)` of degree `l`, where `ψ₀ = mode R .azimuthal l 0`. -/
def azimuthalTest (R : ℝ) (l : ℕ) (G : ℝ → ℝ) (x : ℝ^3) : ℝ^3 :=
  G (‖x‖ ^ 2) • mode R .azimuthal l 0 x

private theorem mode_azimuthal_zero_apply (R : ℝ) (l : ℕ) (y : ℝ^3) (i : Fin 3) :
    mode R .azimuthal l 0 y i = reducedSphericalBesselJSq l 0 *
      eval y.ofLp (swirlPolynomial (zonalSolidHarmonicPolynomial l) i) := by
  simp [mode, azimuthalModeField_apply, besselRadial, besselFactor]

private theorem azimuthalTest_apply_eq (R : ℝ) (l : ℕ) (G : ℝ → ℝ) (i : Fin 3) :
    (fun y ↦ azimuthalTest R l G y i) = fun y ↦
      (fun s ↦ G s * reducedSphericalBesselJSq l 0) (‖y‖ ^ 2) *
        eval y.ofLp (swirlPolynomial (zonalSolidHarmonicPolynomial l) i) := by
  funext y
  simp only [azimuthalTest, PiLp.smul_apply, smul_eq_mul, mode_azimuthal_zero_apply]
  ring

/-- The azimuthal test fields are smooth. -/
theorem contDiff_azimuthalTest (R : ℝ) (l : ℕ) {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (azimuthalTest R l G) :=
  (hG.comp (contDiff_norm_sq ℝ)).smul (mode_contDiff R .azimuthal l 0)

/-- The azimuthal test fields are divergence free. -/
theorem divergence_azimuthalTest (R : ℝ) (l : ℕ) {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (x : ℝ^3) : divergence (azimuthalTest R l G) x = 0 := by
  have hF : Differentiable ℝ fun s ↦ G s * reducedSphericalBesselJSq l 0 :=
    (hG.differentiable (by simp)).mul_const _
  simp only [divergence]
  have h (i : Fin 3) : ∂[i] (fun y ↦ azimuthalTest R l G y i) x =
      2 * x i * deriv (fun s ↦ G s * reducedSphericalBesselJSq l 0) (‖x‖ ^ 2) *
        eval x.ofLp (swirlPolynomial (zonalSolidHarmonicPolynomial l) i) +
      (G (‖x‖ ^ 2) * reducedSphericalBesselJSq l 0) *
        eval x.ofLp (pderiv i (swirlPolynomial (zonalSolidHarmonicPolynomial l) i)) := by
    rw [azimuthalTest_apply_eq, partialDeriv_radial_mul_eval hF]
  set P := zonalSolidHarmonicPolynomial l
  have hX := congrArg (eval x.ofLp) (sum_X_mul_swirlPolynomial P)
  have hP := congrArg (eval x.ofLp) (sum_pderiv_swirlPolynomial P)
  simp only [map_sum, eval_mul, eval_X, map_zero] at hX hP
  rw [Finset.sum_congr rfl fun i _ ↦ h i, Finset.sum_add_distrib]
  have h1 : ∑ i, 2 * x i * deriv (fun s ↦ G s * reducedSphericalBesselJSq l 0) (‖x‖ ^ 2) *
      eval x.ofLp (swirlPolynomial P i) =
      2 * deriv (fun s ↦ G s * reducedSphericalBesselJSq l 0) (‖x‖ ^ 2) *
        ∑ i, x.ofLp i * eval x.ofLp (swirlPolynomial P i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [show x.ofLp i = x i from rfl]
    ring
  rw [h1, hX, ← Finset.mul_sum, hP]
  ring

/-- The azimuthal test fields commute with the rotations about the axis. -/
theorem azimuthalTest_axisRotation (R : ℝ) (l : ℕ) (G : ℝ → ℝ) :
    IsEquivariantUnderAxisRotation (azimuthalTest R l G) := by
  intro φ x
  have hn : ‖axisRotation φ x‖ = ‖x‖ := (axialRotation φ).norm_map x
  simp only [azimuthalTest, hn, mode_axisRotation]
  rw [← axialRotation_apply, ← axialRotation_apply, map_smul]

/-- The azimuthal test fields have the parity `(-1)^{l+1}` of the azimuthal modes. -/
theorem azimuthalTest_equatorialReflection (R : ℝ) (l : ℕ) (G : ℝ → ℝ) (x : ℝ^3) :
    azimuthalTest R l G (equatorialReflection x) =
      modeParity .azimuthal l • equatorialReflection (azimuthalTest R l G x) := by
  have hn : ‖equatorialReflection x‖ = ‖x‖ := equatorialReflection.norm_map x
  simp only [azimuthalTest, hn, mode_equatorialReflection, map_smul, smul_comm (G _)]

/-- The radial derivative of an azimuthal test field:
`∑ⱼ xⱼ ∂ⱼ vᵢ = (2 ‖x‖² G'(‖x‖²) + l G(‖x‖²)) ψ₀ᵢ`. -/
theorem sum_partialDeriv_azimuthalTest_mul (R : ℝ) (l : ℕ) {G : ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) (x : ℝ^3) (i : Fin 3) :
    ∑ j, ∂[j] (fun y ↦ azimuthalTest R l G y i) x * x j =
      (2 * ‖x‖ ^ 2 * deriv G (‖x‖ ^ 2) + l * G (‖x‖ ^ 2)) * mode R .azimuthal l 0 x i := by
  have hF : Differentiable ℝ fun s ↦ G s * reducedSphericalBesselJSq l 0 :=
    (hG.differentiable (by simp)).mul_const _
  have hd : deriv (fun s ↦ G s * reducedSphericalBesselJSq l 0) (‖x‖ ^ 2) =
      deriv G (‖x‖ ^ 2) * reducedSphericalBesselJSq l 0 :=
    ((hG.differentiable (by simp) _).hasDerivAt.mul_const _).deriv
  rw [azimuthalTest_apply_eq, sum_partialDeriv_radial_mul_eval_mul hF
    (sum_X_mul_pderiv_swirlPolynomial (euler_zonalSolidHarmonicPolynomial l) i), hd,
    mode_azimuthal_zero_apply]
  ring

/-- **The Neumann identity for azimuthal tests.** Let `u` have integrable components and weak
derivatives `Du i j = ∂ⱼ uᵢ` on the ball, and satisfy the weak eigenvalue equation of
eigenvalue `μ` against every smooth divergence-free equivariant field of parity `ε`. If the
azimuthal modes of degree `l` have parity `ε` and `2 R² G'(R²) + l G(R²) = 0`, then
`∫_B ⟪u, (4 ‖x‖² G'' + (4l + 6) G' + μ G)(‖x‖²) ψ₀⟫ = 0`. -/
theorem integral_inner_azimuthal_eq_zero_of_weak_eigen {R μ ε : ℝ} (hR : 0 < R) {l : ℕ}
    (hpar : modeParity .azimuthal l = ε) {u : ℝ^3 → ℝ^3} {Du : Fin 3 → Fin 3 → ℝ^3 → ℝ}
    (hu : ∀ i, IntegrableOn (fun x ↦ u x i) (Metric.ball (0 : ℝ^3) R))
    (hDu : ∀ i j, IntegrableOn (Du i j) (Metric.ball (0 : ℝ^3) R))
    (hweak : ∀ i j, SobolevSpace.HasWeakDerivativeOn (Metric.ball (0 : ℝ^3) R) [j]
      (fun x ↦ u x i) (Du i j))
    (heig : ∀ v : ℝ^3 → ℝ^3, ContDiff ℝ ∞ v → (∀ x, divergence v x = 0) →
      IsEquivariantUnderAxisRotation v →
      (∀ x, v (equatorialReflection x) = ε • equatorialReflection (v x)) →
      ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j, Du i j x * ∂[j] (fun y ↦ v y i) x =
        μ * ∫ x in Metric.ball (0 : ℝ^3) R, ⟪u x, v x⟫)
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (hGR : 2 * R ^ 2 * deriv G (R ^ 2) + l * G (R ^ 2) = 0) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ⟪u x, (4 * ‖x‖ ^ 2 * deriv (deriv G) (‖x‖ ^ 2) +
      (4 * l + 6) * deriv G (‖x‖ ^ 2) + μ * G (‖x‖ ^ 2)) • mode R .azimuthal l 0 x⟫ = 0 := by
  set B := Metric.ball (0 : ℝ^3) R
  set v := azimuthalTest R l G with hv
  have hvC : ContDiff ℝ ∞ v := contDiff_azimuthalTest R l hG
  have hvi (i : Fin 3) : ContDiff ℝ ∞ (fun y ↦ v y i) := (contDiff_piLp_apply 2).comp hvC
  set T : Fin 3 → Fin 3 → ℝ^3 → ℝ := fun i j ↦ ∂[j] (fun y ↦ v y i) with hT
  have hTC : ∀ i j, ContDiff ℝ ∞ (T i j) := fun i j ↦ (hvi i).partialDeriv j
  have hTn : ∀ x : ℝ^3, ‖x‖ = R → ∀ i, ∑ j, T i j x * x j = 0 := fun x hx i ↦ by
    simp only [hT, hv, sum_partialDeriv_azimuthalTest_mul R l hG x i, hx, hGR, zero_mul]
  have htool := PDE.Analysis.integral_sum_mul_partialDeriv_add_mul_eq_zero hR hTC hTn
    (v := fun i x ↦ u x i) hu hDu hweak
  have hlap (x : ℝ^3) (i : Fin 3) : ∑ j, ∂[j] (T i j) x =
      (4 * ‖x‖ ^ 2 * deriv (deriv G) (‖x‖ ^ 2) + (4 * l + 6) * deriv G (‖x‖ ^ 2)) *
        mode R .azimuthal l 0 x i := by
    simpa only [hT, hv, azimuthalTest, PiLp.smul_apply, smul_eq_mul, laplacian] using
      laplacian_mul_mode_azimuthal_zero (hG.of_le (by simp)) R l x i
  have hmul : ∀ {g : ℝ^3 → ℝ}, Continuous g → ∀ {f : ℝ^3 → ℝ}, IntegrableOn f B →
      Integrable (fun x ↦ f x * g x) (volume.restrict B) := fun hg _ hf ↦
    hf.mul_continuousOn_of_subset hg.continuousOn measurableSet_ball
      (isCompact_closedBall 0 R) Metric.ball_subset_closedBall
  have hcK : Continuous fun x : ℝ^3 ↦ 4 * ‖x‖ ^ 2 * deriv (deriv G) (‖x‖ ^ 2) +
      (4 * l + 6) * deriv G (‖x‖ ^ 2) := by
    have h2 := (hG.iterate_deriv 2).continuous
    have h1 := (hG.iterate_deriv 1).continuous
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
      Function.id_comp] at h1 h2
    fun_prop
  have hI1 : Integrable (fun x ↦ ∑ i, u x i * ((4 * ‖x‖ ^ 2 * deriv (deriv G) (‖x‖ ^ 2) +
      (4 * l + 6) * deriv G (‖x‖ ^ 2)) * mode R .azimuthal l 0 x i)) (volume.restrict B) :=
    integrable_finsetSum _ fun i _ ↦ hmul (hcK.mul
      ((contDiff_piLp_apply 2).comp (mode_contDiff R .azimuthal l 0)).continuous) (hu i)
  have hI2 : Integrable (fun x ↦ ∑ i, ∑ j, Du i j x * T i j x) (volume.restrict B) :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      hmul (hTC i j).continuous (hDu i j)
  have hsplit : ∫ x in B, ∑ i, ∑ j, (u x i * ∂[j] (T i j) x + Du i j x * T i j x) =
      (∫ x in B, ∑ i, u x i * ((4 * ‖x‖ ^ 2 * deriv (deriv G) (‖x‖ ^ 2) +
        (4 * l + 6) * deriv G (‖x‖ ^ 2)) * mode R .azimuthal l 0 x i)) +
      ∫ x in B, ∑ i, ∑ j, Du i j x * T i j x := by
    rw [← integral_add hI1 hI2]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hlap]
  have hE := heig v hvC (divergence_azimuthalTest R l hG) (azimuthalTest_axisRotation R l G)
    (fun x ↦ hpar ▸ azimuthalTest_equatorialReflection R l G x)
  rw [hsplit] at htool
  change _ + ∫ x in B, ∑ i, ∑ j, Du i j x * ∂[j] (fun y ↦ v y i) x = 0 at htool
  rw [hE] at htool
  have hI3 : Integrable (fun x ↦ ⟪u x, v x⟫) (volume.restrict B) := by
    simp only [EuclideanSpace.real_inner_eq_sum]
    exact integrable_finsetSum _ fun i _ ↦ hmul (hvi i).continuous (hu i)
  calc ∫ x in B, ⟪u x, (4 * ‖x‖ ^ 2 * deriv (deriv G) (‖x‖ ^ 2) +
        (4 * l + 6) * deriv G (‖x‖ ^ 2) + μ * G (‖x‖ ^ 2)) • mode R .azimuthal l 0 x⟫
      = (∫ x in B, ∑ i, u x i * ((4 * ‖x‖ ^ 2 * deriv (deriv G) (‖x‖ ^ 2) +
          (4 * l + 6) * deriv G (‖x‖ ^ 2)) * mode R .azimuthal l 0 x i)) +
        μ * ∫ x in B, ⟪u x, v x⟫ := by
        rw [← integral_const_mul, ← integral_add hI1 (hI3.const_mul μ)]
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        simp only [hv, azimuthalTest, EuclideanSpace.real_inner_eq_sum, PiLp.smul_apply,
          smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        ring
    _ = 0 := htool

/-- The one-dimensional form of the azimuthal pairing: for an equivariant field `W` integrable
on the ball, `∫_B ⟪W, K(‖x‖²) ψ₀⟫ = 0` if and only if
`∫₀^R r^{l+2} K(r²) c(r) dr = 0`, where `c` is the azimuthal meridian coefficient of `W`. -/
theorem setIntegral_inner_azimuthal_zero_eq_zero_iff {R : ℝ} {W : ℝ^3 → ℝ^3}
    (hW : IsEquivariantUnderAxisRotation W) (hWint : IntegrableOn W (Metric.ball (0 : ℝ^3) R))
    {K : ℝ → ℝ} (hK : Continuous K) (l : ℕ) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ⟪W x, K (‖x‖ ^ 2) • mode R .azimuthal l 0 x⟫ = 0 ↔
      ∫ r in Ioo 0 R, r ^ (l + 2) * K (r ^ 2) * meridianCoefficient W l 2 r = 0 := by
  rw [setIntegral_inner_azimuthal hW hWint hK l 0]
  have hI : ∫ r in Ioo 0 R, K (r ^ 2) * azimuthalProfile R l 0 r * r ^ 2 *
      meridianCoefficient W l 2 r = reducedSphericalBesselJ l 0 *
        ∫ r in Ioo 0 R, r ^ (l + 2) * K (r ^ 2) * meridianCoefficient W l 2 r := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun r _ ↦ ?_
    simp only [azimuthalProfile_zero]
    ring
  rw [hI]
  have hg : reducedSphericalBesselJ l 0 ≠ 0 := (reducedSphericalBesselJ_zero_pos l).ne'
  have h2π : 2 * π ≠ 0 := by positivity
  constructor
  · intro h
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left h2π)).resolve_left hg
  · intro h
    rw [h, mul_zero, mul_zero]

/-- The azimuthal boundary function in the squared argument:
`boundaryFunction .azimuthal l α = l G_l(α²) - α² G_{l+1}(α²)`. -/
theorem boundaryFunction_azimuthal_eq_sq (l : ℕ) (α : ℝ) :
    boundaryFunction .azimuthal l α = l * reducedSphericalBesselJSq l (α ^ 2) -
      α ^ 2 * reducedSphericalBesselJSq (l + 1) (α ^ 2) := by
  simp only [boundaryFunction, reducedSphericalBesselJ_eq_sq]

/-- **Azimuthal coefficients of weak eigenfunctions.** Let `u` satisfy the weak Neumann-Stokes
eigenvalue equation with eigenvalue `μ` against the smooth divergence-free equivariant fields
of parity `ε`, the parity of the azimuthal modes of degree `l ≥ 1`, and let `w` be a measurable
equivariant field equal to `u` almost everywhere on the ball. Then the azimuthal meridian
coefficient of `w` is almost everywhere `A r^l G_l(μ r²)` on `(0, R)`, the radial profile of the
azimuthal modes, and `A = 0` unless `μ > 0` and `√μ R` is a root of the azimuthal boundary
function: the interior tests give the radial equation, and the Neumann test
`G(s) = 1 - l (s - R²) / (2R²)`, whose field has vanishing radial derivative on the sphere,
gives `A φ'(R) = 0`, while `R φ'(R) = R^l (l G_l(μR²) - μR² G_{l+1}(μR²))` is positive for
`μ ≤ 0`. -/
theorem meridianCoefficient_azimuthal_of_weak_eigen {R μ ε : ℝ} (hR : 0 < R)
    {l : ℕ} (hl : 1 ≤ l) (hpar : modeParity .azimuthal l = ε) {u : ℝ^3 → ℝ^3}
    {Du : Fin 3 → Fin 3 → ℝ^3 → ℝ}
    (hu : ∀ i, IntegrableOn (fun x ↦ u x i) (Metric.ball (0 : ℝ^3) R))
    (hDu : ∀ i j, IntegrableOn (Du i j) (Metric.ball (0 : ℝ^3) R))
    (hweak : ∀ i j, SobolevSpace.HasWeakDerivativeOn (Metric.ball (0 : ℝ^3) R) [j]
      (fun x ↦ u x i) (Du i j))
    (heig : ∀ v : ℝ^3 → ℝ^3, ContDiff ℝ ∞ v → (∀ x, divergence v x = 0) →
      IsEquivariantUnderAxisRotation v →
      (∀ x, v (equatorialReflection x) = ε • equatorialReflection (v x)) →
      ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j, Du i j x * ∂[j] (fun y ↦ v y i) x =
        μ * ∫ x in Metric.ball (0 : ℝ^3) R, ⟪u x, v x⟫)
    {w : ℝ^3 → ℝ^3} (hwm : Measurable w) (hw : IsEquivariantUnderAxisRotation w)
    (hwint : IntegrableOn w (Metric.ball (0 : ℝ^3) R))
    (huw : u =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) R)] w) :
    ∃ A : ℝ, meridianCoefficient w l 2 =ᵐ[volume.restrict (Ioo 0 R)]
        (fun r ↦ A * radialSolution l μ r) ∧
      (A = 0 ∨ (0 < μ ∧ boundaryFunction .azimuthal l (√μ * R) = 0)) := by
  have hswap (Φ : ℝ^3 → ℝ^3) : ∫ x in Metric.ball (0 : ℝ^3) R, ⟪u x, Φ x⟫ =
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪w x, Φ x⟫ :=
    integral_congr_ae (by filter_upwards [huw] with x hx; rw [hx])
  have hNeu := fun {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
      (hGR : 2 * R ^ 2 * deriv G (R ^ 2) + l * G (R ^ 2) = 0) ↦
    integral_inner_azimuthal_eq_zero_of_weak_eigen hR hpar hu hDu hweak heig hG hGR
  obtain ⟨A, hA⟩ := meridianCoefficient_azimuthal_ae_eq hR hwm hw hwint
    fun F hF hcs hsupp _ ↦ by
      have hR2 : R ^ 2 ∉ tsupport F := fun h ↦ lt_irrefl _ (hsupp h)
      have hF0 : F (R ^ 2) = 0 := image_eq_zero_of_notMem_tsupport hR2
      have hF1 : deriv F (R ^ 2) = 0 :=
        image_eq_zero_of_notMem_tsupport fun h ↦ hR2 (tsupport_deriv_subset h)
      exact (hswap _).symm.trans (hNeu hF (by rw [hF0, hF1]; ring))
  refine ⟨A, hA, ?_⟩
  -- the Neumann test
  set G : ℝ → ℝ := fun s ↦ 1 - l / (2 * R ^ 2) * (s - R ^ 2) with hGdef
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR.ne'
  have hGd : ∀ s, HasDerivAt G (-(l / (2 * R ^ 2))) s := fun s ↦
    ((((hasDerivAt_id' s).sub_const (R ^ 2)).const_mul (l / (2 * R ^ 2))).const_sub 1).congr_deriv
      (by ring)
  have hGd1 : deriv G = fun _ ↦ -(l / (2 * R ^ 2)) := funext fun s ↦ (hGd s).deriv
  have hGC : ContDiff ℝ ∞ G := by simp only [hGdef]; fun_prop
  have hGR : 2 * R ^ 2 * deriv G (R ^ 2) + l * G (R ^ 2) = 0 := by
    rw [hGd1]
    simp only [hGdef, sub_self, mul_zero, sub_zero, mul_one]
    field_simp
    ring
  set K : ℝ → ℝ := fun s ↦ 4 * s * deriv (deriv G) s + (4 * l + 6) * deriv G s + μ * G s
    with hKdef
  have hK : Continuous K := by
    simp only [hKdef, hGdef]
    fun_prop
  have h := (hswap _).symm.trans (hNeu hGC hGR)
  have h1 := (setIntegral_inner_azimuthal_zero_eq_zero_iff hw hwint hK l).mp h
  have h2 : ∫ r in Ioo 0 R, r ^ (l + 2) * K (r ^ 2) * meridianCoefficient w l 2 r =
      A * ∫ r in Ioo 0 R, r ^ (l + 2) * (4 * r ^ 2 * deriv (deriv G) (r ^ 2) +
        (4 * l + 6) * deriv G (r ^ 2) + μ * G (r ^ 2)) * radialSolution l μ r := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hA] with r hr
    rw [hr, hKdef]
    ring
  rw [h2, integral_radial_mul_radialSolution l μ hR.le hGC] at h1
  have hφ' : deriv (fun s ↦ s ^ l * G (s ^ 2)) R = 0 := by
    have h := mul_deriv_pow_mul_comp_sq (hGC.differentiable (by simp)) l R
    rw [show (l : ℝ) * G (R ^ 2) + 2 * R ^ 2 * deriv G (R ^ 2) = 0 by linarith [hGR],
      mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hR.ne'
  have hG1 : G (R ^ 2) = 1 := by simp [hGdef]
  rw [hφ', hG1] at h1
  refine (mul_eq_zero.mp h1).imp id fun h3 ↦ ?_
  · have h4 : deriv (radialSolution l μ) R = 0 := by
      have h5 : R ^ 2 * R ^ l * deriv (radialSolution l μ) R = 0 := by
        linear_combination -h3
      exact (mul_eq_zero.mp h5).resolve_left (by positivity)
    have h6 := mul_deriv_radialSolution l μ R
    rw [h4, mul_zero] at h6
    have h7 : (l : ℝ) * reducedSphericalBesselJSq l (μ * R ^ 2) -
        μ * R ^ 2 * reducedSphericalBesselJSq (l + 1) (μ * R ^ 2) = 0 :=
      (mul_eq_zero.mp h6.symm).resolve_left (pow_ne_zero _ hR.ne')
    have hμ : 0 < μ := by
      by_contra hμ
      replace hμ := not_lt.mp hμ
      have ht : μ * R ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hμ (sq_nonneg R)
      have hp1 := reducedSphericalBesselJSq_pos_of_nonpos l ht
      have hp2 := reducedSphericalBesselJSq_pos_of_nonpos (l + 1) ht
      have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
      nlinarith
    exact ⟨hμ, by rwa [boundaryFunction_azimuthal_eq_sq, mul_pow, Real.sq_sqrt hμ.le]⟩

end PDE.Fluid.Stokes.Ball
