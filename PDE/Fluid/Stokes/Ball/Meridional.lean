/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.Separation
public import PDE.Analysis.Calculus.EuclideanBall.NormalCutoff
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Meridional test fields on the ball

With `h = h_l` the zonal solid harmonic of degree `l`, the meridional fields
`v = A(‖x‖²) h(x) x + B(‖x‖²) ∇h(x)` for smooth radial factors `A`, `B` contain the meridional
modes and the gradients `∇(P(‖x‖²) h) = v(2P', P)`. Their divergence is
`(2 s A' + (l + 3) A + 2 l B')(‖x‖²) h`, their Laplacian is the meridional field with factors
`K_{l+1}[A]` and `2A + K_{l-1}[B]`, where `K_c[F] = 4 s F'' + (4c + 6) F'`, and their radial
derivative `∑ⱼ xⱼ ∂ⱼ v` is the meridional field with factors `2 s A' + (l + 1) A` and
`2 s B' + (l - 1) B`. On a meridian, `v(point r θ 0) = (r^{l+1} A + l r^{l-1} B)(r²) Y_l +
r^{l-1} B(r²) X_l`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Real MvPolynomial
open PDE (partialDeriv laplacian divergence)
open EuclideanLaplacian
open PDE.Analysis.SpecialFunctions PDE.CoordinateSystems PDE.CoordinateSystems.Spherical
open scoped RealInnerProductSpace ContDiff

namespace PDE.Fluid.Stokes.Ball

/-- The meridional field `A(‖x‖²) h_l(x) x + B(‖x‖²) ∇h_l(x)` of degree `l`. -/
def meridionalTest (l : ℕ) (A B : ℝ → ℝ) : ℝ^3 → ℝ^3 :=
  meridionalField (zonalSolidHarmonicPolynomial l) A B

/-- The components of a meridional field. -/
theorem meridionalTest_apply (l : ℕ) (A B : ℝ → ℝ) (x : ℝ^3) (i : Fin 3) :
    meridionalTest l A B x i =
      A (‖x‖ ^ 2) * eval x.ofLp (zonalSolidHarmonicPolynomial l * X i) +
        B (‖x‖ ^ 2) * eval x.ofLp (pderiv i (zonalSolidHarmonicPolynomial l)) :=
  rfl

/-- The operator `K_c[F](s) = 4 s F''(s) + (4c + 6) F'(s)`, the radial part of the Laplacian on
`F(‖x‖²) q(x)` for a harmonic polynomial `q` homogeneous of degree `c`. -/
def radialLaplacian (c : ℝ) (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  4 * s * deriv (deriv F) s + (4 * c + 6) * deriv F s

/-- The meridional fields are smooth. -/
theorem contDiff_meridionalTest (l : ℕ) {A B : ℝ → ℝ} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (meridionalTest l A B) :=
  contDiff_meridionalField _ hA hB

/-- The divergence of a meridional field: `(2 s A' + (l + 3) A + 2 l B')(‖x‖²) h(x)`. -/
theorem divergence_meridionalTest (l : ℕ) {A B : ℝ → ℝ} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) (x : ℝ^3) :
    divergence (meridionalTest l A B) x =
      (2 * ‖x‖ ^ 2 * deriv A (‖x‖ ^ 2) + (l + 3) * A (‖x‖ ^ 2) + 2 * l * deriv B (‖x‖ ^ 2)) *
        eval x.ofLp (zonalSolidHarmonicPolynomial l) := by
  set P := zonalSolidHarmonicPolynomial l with hP
  have hA1 : Differentiable ℝ A := hA.differentiable (by simp)
  have hB1 : Differentiable ℝ B := hB.differentiable (by simp)
  have hcomp (i : Fin 3) : ∂[i] (fun y ↦ meridionalTest l A B y i) x =
      2 * x i * deriv A (‖x‖ ^ 2) * eval x.ofLp (P * X i) +
        A (‖x‖ ^ 2) * eval x.ofLp (pderiv i (P * X i)) +
      (2 * x i * deriv B (‖x‖ ^ 2) * eval x.ofLp (pderiv i P) +
        B (‖x‖ ^ 2) * eval x.ofLp (pderiv i (pderiv i P))) := by
    simp only [meridionalTest_apply]
    rw [partialDeriv_add ((contDiff_radial_mul_eval (Q := _) (hA.of_le (by simp))).differentiable
        one_ne_zero x)
      ((contDiff_radial_mul_eval (Q := _) (hB.of_le (by simp))).differentiable one_ne_zero x),
      partialDeriv_radial_mul_eval hA1, partialDeriv_radial_mul_eval hB1]
  unfold divergence
  rw [Finset.sum_congr rfl fun i _ ↦ hcomp i]
  have e1 := congrArg (eval x.ofLp) (sum_pderiv_mul_X (euler_zonalSolidHarmonicPolynomial l))
  have e2 := congrArg (eval x.ofLp) (euler_zonalSolidHarmonicPolynomial l)
  have e3 := congrArg (eval x.ofLp) (polynomialLaplacian_zonalSolidHarmonicPolynomial l)
  rw [polynomialLaplacian] at e3
  have e4 : ∑ i, x i * eval x.ofLp (P * X i) = ‖x‖ ^ 2 * eval x.ofLp P := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [map_mul, eval_X]
    ring
  simp only [map_sum, map_mul, eval_X, eval_C, map_zero] at e1 e2 e3
  simp only [Fin.sum_univ_three] at e1 e2 e3 e4 ⊢
  linear_combination 2 * deriv A (‖x‖ ^ 2) * e4 + A (‖x‖ ^ 2) * e1 +
    2 * deriv B (‖x‖ ^ 2) * e2 + B (‖x‖ ^ 2) * e3

/-- The Laplacian of a meridional field is the meridional field with factors `K_{l+1}[A]` and
`2A + K_{l-1}[B]`. -/
theorem laplacian_meridionalTest (l : ℕ) {A B : ℝ → ℝ} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) (x : ℝ^3) (i : Fin 3) :
    laplacian (fun y ↦ meridionalTest l A B y i) x =
      meridionalTest l (radialLaplacian ((l : ℝ) + 1) A)
        (fun s ↦ 2 * A s + radialLaplacian ((l : ℝ) - 1) B s) x i := by
  set P := zonalSolidHarmonicPolynomial l with hP
  have hL := polynomialLaplacian_zonalSolidHarmonicPolynomial l
  have hfun : (fun y ↦ meridionalTest l A B y i) = fun y ↦
      A (‖y‖ ^ 2) * eval y.ofLp (P * X i) + B (‖y‖ ^ 2) * eval y.ofLp (pderiv i P) := rfl
  have h2 : ContDiffAt ℝ 2 (fun y : ℝ^3 ↦ A (‖y‖ ^ 2) * eval y.ofLp (P * X i)) x :=
    (contDiff_radial_mul_eval (Q := _) (hA.of_le (by simp))).contDiffAt
  have h2' : ContDiffAt ℝ 2 (fun y : ℝ^3 ↦ B (‖y‖ ^ 2) * eval y.ofLp (pderiv i P)) x :=
    (contDiff_radial_mul_eval (Q := _) (hB.of_le (by simp))).contDiffAt
  rw [hfun, laplacian_add _ _ x h2 h2',
    laplacian_radial_mul_eval (hA.of_le (by simp))
      (sum_X_mul_pderiv_mul_X (euler_zonalSolidHarmonicPolynomial l) i),
    laplacian_radial_mul_eval (hB.of_le (by simp))
      (sum_X_mul_pderiv_pderiv (euler_zonalSolidHarmonicPolynomial l) i),
    polynomialLaplacian_mul_X hL i, polynomialLaplacian_pderiv_eq_zero hL i, meridionalTest_apply]
  have htwo : eval x.ofLp (2 * pderiv i P) = 2 * eval x.ofLp (pderiv i P) := by
    rw [map_mul, map_ofNat]
  rw [htwo, map_zero, mul_zero, add_zero]
  simp only [radialLaplacian]
  ring

/-- The radial derivative of a meridional field: `∑ⱼ xⱼ ∂ⱼ v` is the meridional field with
factors `2 s A' + (l + 1) A` and `2 s B' + (l - 1) B`. -/
theorem sum_partialDeriv_meridionalTest_mul (l : ℕ) {A B : ℝ → ℝ} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) (x : ℝ^3) (i : Fin 3) :
    ∑ j, ∂[j] (fun y ↦ meridionalTest l A B y i) x * x j =
      meridionalTest l (fun s ↦ 2 * s * deriv A s + ((l : ℝ) + 1) * A s)
        (fun s ↦ 2 * s * deriv B s + ((l : ℝ) - 1) * B s) x i := by
  set P := zonalSolidHarmonicPolynomial l with hP
  have hA1 : Differentiable ℝ A := hA.differentiable (by simp)
  have hB1 : Differentiable ℝ B := hB.differentiable (by simp)
  have hsplit (j : Fin 3) : ∂[j] (fun y ↦ meridionalTest l A B y i) x =
      ∂[j] (fun y : ℝ^3 ↦ A (‖y‖ ^ 2) * eval y.ofLp (P * X i)) x +
        ∂[j] (fun y : ℝ^3 ↦ B (‖y‖ ^ 2) * eval y.ofLp (pderiv i P)) x := by
    simp only [meridionalTest_apply]
    exact partialDeriv_add ((contDiff_radial_mul_eval (Q := _) (hA.of_le (by simp))).differentiable
        one_ne_zero x)
      ((contDiff_radial_mul_eval (Q := _) (hB.of_le (by simp))).differentiable one_ne_zero x)
  simp only [hsplit, add_mul, Finset.sum_add_distrib]
  rw [sum_partialDeriv_radial_mul_eval_mul hA1
      (sum_X_mul_pderiv_mul_X (euler_zonalSolidHarmonicPolynomial l) i),
    sum_partialDeriv_radial_mul_eval_mul hB1
      (sum_X_mul_pderiv_pderiv (euler_zonalSolidHarmonicPolynomial l) i),
    meridionalTest_apply]
  ring

/-- The vector form `v = A(‖x‖²) h(x) x + B(‖x‖²) ∇h(x)`. -/
theorem meridionalTest_eq (l : ℕ) (A B : ℝ → ℝ) (x : ℝ^3) :
    meridionalTest l A B x =
      (A (‖x‖ ^ 2) * eval x.ofLp (zonalSolidHarmonicPolynomial l)) • x +
        B (‖x‖ ^ 2) • polynomialGradient (zonalSolidHarmonicPolynomial l) x := by
  ext i
  simp only [meridionalTest_apply, map_mul, eval_X, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, polynomialGradient]
  ring

/-- The meridional fields commute with the rotations about the axis. -/
theorem meridionalTest_axisRotation (l : ℕ) (A B : ℝ → ℝ) :
    IsEquivariantUnderAxisRotation (meridionalTest l A B) := by
  intro φ x
  have hnorm : ‖axisRotation φ x‖ = ‖x‖ := (axialRotation φ).norm_map x
  rw [meridionalTest_eq, meridionalTest_eq, hnorm,
    eval_zonalSolidHarmonicPolynomial_axisRotation,
    polynomialGradient_zonalSolidHarmonicPolynomial_axisRotation, ← axialRotation_apply,
    ← axialRotation_apply, ← axialRotation_apply, map_add, map_smul, map_smul]

/-- The meridional fields of degree `l` have the parity `(-1)^l` of the meridional modes. -/
theorem meridionalTest_equatorialReflection (l : ℕ) (A B : ℝ → ℝ) (x : ℝ^3) :
    meridionalTest l A B (equatorialReflection x) =
      modeParity .meridional l • equatorialReflection (meridionalTest l A B x) := by
  have hnorm : ‖equatorialReflection x‖ = ‖x‖ := equatorialReflection.norm_map x
  rw [meridionalTest_eq, meridionalTest_eq, hnorm,
    eval_zonalSolidHarmonicPolynomial_equatorialReflection,
    polynomialGradient_zonalSolidHarmonicPolynomial_equatorialReflection, modeParity,
    map_add, map_smul, map_smul, smul_add, smul_smul, smul_smul, smul_smul]
  congr 1
  · congr 1
    ring
  · rw [mul_comm]

/-- On the meridian of azimuth zero,
`v(point r θ 0) = (r^{l+1} A(r²) + l r^{l-1} B(r²)) Y_l(θ) + r^{l-1} B(r²) X_l(θ)`. -/
theorem meridionalTest_point (l : ℕ) (A B : ℝ → ℝ) (r θ : ℝ) :
    meridionalTest l A B (point r θ 0) =
      (r ^ (l + 1) * A (r ^ 2) + l * r ^ (l - 1) * B (r ^ 2)) • vectorHarmonic l 0 θ +
        (r ^ (l - 1) * B (r ^ 2)) • vectorHarmonic l 1 θ := by
  rw [meridionalTest_eq, norm_point_sq, eval_zonalSolidHarmonicPolynomial_point,
    polynomialGradient_zonalSolidHarmonicPolynomial_point]
  simp only [vectorHarmonic, vectorHarmonicProfile, frame, point]
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.isValue, ↓reduceIte,
    show (1 : Fin 3) ≠ 0 by decide, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Gradients of `P(‖x‖²) h(x)` are meridional fields: `∇(P h) = v(2P', P)`. -/
theorem partialDeriv_radial_mul_zonal (l : ℕ) {P : ℝ → ℝ} (hP : Differentiable ℝ P)
    (x : ℝ^3) (i : Fin 3) :
    ∂[i] (fun y : ℝ^3 ↦ P (‖y‖ ^ 2) * eval y.ofLp (zonalSolidHarmonicPolynomial l)) x =
      meridionalTest l (fun s ↦ 2 * deriv P s) P x i := by
  rw [partialDeriv_radial_mul_eval hP, meridionalTest_apply, map_mul, eval_X]
  rw [show x.ofLp i = x i from rfl]
  ring

/-- **The Neumann identity for meridional tests.** Let `u` have integrable components and
weak derivatives on the ball, be weakly divergence free and satisfy the weak eigenvalue
equation of eigenvalue `μ` against the smooth divergence-free equivariant fields of parity
`ε`, the parity of the meridional modes of degree `l`. Let `v = v(A, B)` be divergence free
(`2 s A' + (l + 3) A + 2 l B' = 0`) and let the pressure `p = P(‖x‖²) h(x)` make its traction
`(∇v - p) x` vanish on the sphere: `2 R² A'(R²) + (l + 1) A(R²) = P(R²)` and
`2 R² B'(R²) + (l - 1) B(R²) = 0`. Then `∫_B ⟪u, Δv - ∇p + μ v⟫ = 0`. -/
theorem integral_inner_meridional_eq_zero_of_weak_eigen {R μ ε : ℝ} (hR : 0 < R) {l : ℕ}
    (hpar : modeParity .meridional l = ε) {u : ℝ^3 → ℝ^3} {Du : Fin 3 → Fin 3 → ℝ^3 → ℝ}
    (hu : ∀ i, IntegrableOn (fun x ↦ u x i) (Metric.ball (0 : ℝ^3) R))
    (hDu : ∀ i j, IntegrableOn (Du i j) (Metric.ball (0 : ℝ^3) R))
    (hweak : ∀ i j, SobolevSpace.HasWeakDerivativeOn (Metric.ball (0 : ℝ^3) R) [j]
      (fun x ↦ u x i) (Du i j))
    (hdiv : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)), ∑ i, Du i i x = 0)
    (heig : ∀ v : ℝ^3 → ℝ^3, ContDiff ℝ ∞ v → (∀ x, divergence v x = 0) →
      IsEquivariantUnderAxisRotation v →
      (∀ x, v (equatorialReflection x) = ε • equatorialReflection (v x)) →
      ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j, Du i j x * ∂[j] (fun y ↦ v y i) x =
        μ * ∫ x in Metric.ball (0 : ℝ^3) R, ⟪u x, v x⟫)
    {A B P : ℝ → ℝ} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (hP : ContDiff ℝ ∞ P)
    (hfree : ∀ s, 2 * s * deriv A s + ((l : ℝ) + 3) * A s + 2 * l * deriv B s = 0)
    (hbc1 : 2 * R ^ 2 * deriv A (R ^ 2) + ((l : ℝ) + 1) * A (R ^ 2) = P (R ^ 2))
    (hbc2 : 2 * R ^ 2 * deriv B (R ^ 2) + ((l : ℝ) - 1) * B (R ^ 2) = 0) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ⟪u x, meridionalTest l
      (fun s ↦ radialLaplacian ((l : ℝ) + 1) A s - 2 * deriv P s + μ * A s)
      (fun s ↦ 2 * A s + radialLaplacian ((l : ℝ) - 1) B s - P s + μ * B s) x⟫ = 0 := by
  set B₀ := Metric.ball (0 : ℝ^3) R
  set h := zonalSolidHarmonicPolynomial l with hh
  set v := meridionalTest l A B with hv
  set p : ℝ^3 → ℝ := fun y ↦ P (‖y‖ ^ 2) * eval y.ofLp h with hp
  have hvC : ContDiff ℝ ∞ v := contDiff_meridionalTest l hA hB
  have hvi (i : Fin 3) : ContDiff ℝ ∞ (fun y ↦ v y i) := (contDiff_piLp_apply 2).comp hvC
  have hpC : ContDiff ℝ ∞ p := contDiff_radial_mul_eval hP
  set T : Fin 3 → Fin 3 → ℝ^3 → ℝ := fun i j y ↦
    ∂[j] (fun z ↦ v z i) y - (if i = j then 1 else 0) * p y with hT
  have hTC : ∀ i j, ContDiff ℝ ∞ (T i j) := fun i j ↦
    ((hvi i).partialDeriv j).sub (contDiff_const.mul hpC)
  have hdT : ∀ i j x, ∂[j] (T i j) x =
      ∂[j] (fun y ↦ ∂[j] (fun z ↦ v z i) y) x - (if i = j then 1 else 0) * ∂[j] p x := by
    intro i j x
    simp only [hT]
    rw [partialDeriv_sub (((hvi i).partialDeriv j).differentiable (by simp) x)
      ((contDiff_const.mul hpC).differentiable (by simp) x), partialDeriv_mul
      (differentiableAt_const _) (hpC.differentiable (by simp) x), partialDeriv_const, zero_mul,
      zero_add]
  have hdivT (x : ℝ^3) (i : Fin 3) : ∑ j, ∂[j] (T i j) x =
      meridionalTest l (fun s ↦ radialLaplacian ((l : ℝ) + 1) A s - 2 * deriv P s)
        (fun s ↦ 2 * A s + radialLaplacian ((l : ℝ) - 1) B s - P s) x i := by
    simp only [hdT, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    have hlap := laplacian_meridionalTest l hA hB x i
    simp only [laplacian] at hlap
    rw [hlap, hp, partialDeriv_radial_mul_zonal l (hP.differentiable (by simp)) x i]
    simp only [meridionalTest_apply]
    ring
  have hTn : ∀ x : ℝ^3, ‖x‖ = R → ∀ i, ∑ j, T i j x * x j = 0 := by
    intro x hx i
    simp only [hT, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [hv, sum_partialDeriv_meridionalTest_mul l hA hB x i, meridionalTest_apply, hp]
    simp only [hx]
    have hxi : eval x.ofLp h * x i = eval x.ofLp (h * X i) := by
      rw [map_mul, eval_X]
    linear_combination (eval x.ofLp (h * X i)) * hbc1 +
      (eval x.ofLp (pderiv i h)) * hbc2 - P (R ^ 2) * hxi
  have htool := PDE.Analysis.integral_sum_mul_partialDeriv_add_mul_eq_zero hR hTC hTn
    (v := fun i x ↦ u x i) hu hDu hweak
  have hmul : ∀ {g : ℝ^3 → ℝ}, Continuous g → ∀ {f : ℝ^3 → ℝ}, IntegrableOn f B₀ →
      Integrable (fun x ↦ f x * g x) (volume.restrict B₀) := fun hg _ hf ↦
    hf.mul_continuousOn_of_subset hg.continuousOn measurableSet_ball
      (isCompact_closedBall 0 R) Metric.ball_subset_closedBall
  set W₁ := meridionalTest l (fun s ↦ radialLaplacian ((l : ℝ) + 1) A s - 2 * deriv P s)
    (fun s ↦ 2 * A s + radialLaplacian ((l : ℝ) - 1) B s - P s) with hW₁
  have hW₁C : Continuous W₁ := by
    have hA1 := (contDiff_infty_iff_deriv.1 hA).2
    have hA2 := (contDiff_infty_iff_deriv.1 hA1).2
    have hB1 := (contDiff_infty_iff_deriv.1 hB).2
    have hB2 := (contDiff_infty_iff_deriv.1 hB1).2
    have hP1 := (contDiff_infty_iff_deriv.1 hP).2
    exact (contDiff_meridionalTest l (by unfold radialLaplacian; fun_prop)
      (by unfold radialLaplacian; fun_prop)).continuous
  have hI1 : Integrable (fun x ↦ ∑ i, u x i * W₁ x i) (volume.restrict B₀) :=
    integrable_finsetSum _ fun i _ ↦ hmul ((continuous_apply i).comp
      ((PiLp.continuous_ofLp 2 _).comp hW₁C)) (hu i)
  have hI2 : Integrable (fun x ↦ ∑ i, ∑ j, Du i j x * T i j x) (volume.restrict B₀) :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      hmul (hTC i j).continuous (hDu i j)
  have hsplit : ∫ x in B₀, ∑ i, ∑ j, (u x i * ∂[j] (T i j) x + Du i j x * T i j x) =
      (∫ x in B₀, ∑ i, u x i * W₁ x i) + ∫ x in B₀, ∑ i, ∑ j, Du i j x * T i j x := by
    rw [← integral_add hI1 hI2]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hdivT, hW₁]
  have hpres : ∫ x in B₀, ∑ i, ∑ j, Du i j x * T i j x =
      ∫ x in B₀, ∑ i, ∑ j, Du i j x * ∂[j] (fun y ↦ v y i) x := by
    refine integral_congr_ae ?_
    filter_upwards [hdiv] with x hx
    simp only [hT, mul_sub, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.sum_mul, hx, sub_zero]
  have hfree' (x : ℝ^3) : divergence v x = 0 := by
    rw [hv, divergence_meridionalTest l hA hB x, hfree, zero_mul]
  have hE := heig v hvC hfree' (meridionalTest_axisRotation l A B)
    (fun x ↦ hpar ▸ meridionalTest_equatorialReflection l A B x)
  rw [hsplit, hpres, hE] at htool
  have hI3 : Integrable (fun x ↦ ⟪u x, v x⟫) (volume.restrict B₀) := by
    simp only [EuclideanSpace.real_inner_eq_sum]
    exact integrable_finsetSum _ fun i _ ↦ hmul (hvi i).continuous (hu i)
  calc ∫ x in B₀, ⟪u x, meridionalTest l
        (fun s ↦ radialLaplacian ((l : ℝ) + 1) A s - 2 * deriv P s + μ * A s)
        (fun s ↦ 2 * A s + radialLaplacian ((l : ℝ) - 1) B s - P s + μ * B s) x⟫
      = (∫ x in B₀, ∑ i, u x i * W₁ x i) + μ * ∫ x in B₀, ⟪u x, v x⟫ := by
        rw [← integral_const_mul, ← integral_add hI1 (hI3.const_mul μ)]
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        simp only [hv, hW₁, EuclideanSpace.real_inner_eq_sum, meridionalTest_apply,
          Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        ring
    _ = 0 := htool

/-- The meridional fields with continuous factors are continuous. -/
theorem continuous_meridionalTest (l : ℕ) {A B : ℝ → ℝ} (hA : Continuous A)
    (hB : Continuous B) : Continuous (meridionalTest l A B) := by
  refine PiLp.continuous_toLp 2 _ |>.comp (continuous_pi fun i ↦ ?_)
  have hc1 : Continuous fun x : ℝ^3 ↦ eval x.ofLp (zonalSolidHarmonicPolynomial l * X i) :=
    (contDiff_eval_ofLp _ (k := 0)).continuous
  have hc2 : Continuous fun x : ℝ^3 ↦
      eval x.ofLp (pderiv i (zonalSolidHarmonicPolynomial l)) :=
    (contDiff_eval_ofLp _ (k := 0)).continuous
  fun_prop

/-- **The meridional pairing in polar form.** For a measurable equivariant field `W`
integrable on the ball and continuous factors `A`, `B`,
`∫_B ⟪W, v(A, B)⟫ = 2π ∫₀^R r² ((r^{l+1} A(r²) + l r^{l-1} B(r²)) a(r) + r^{l-1} B(r²) b(r)) dr`,
where `a` and `b` are the meridian coefficients of `W` on `Y_l` and `X_l`. -/
theorem setIntegral_inner_meridionalTest {R : ℝ} {W : ℝ^3 → ℝ^3} (hWm : Measurable W)
    (hW : IsEquivariantUnderAxisRotation W) (hWint : IntegrableOn W (Metric.ball (0 : ℝ^3) R))
    (l : ℕ) {A B : ℝ → ℝ} (hA : Continuous A) (hB : Continuous B) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ⟪W x, meridionalTest l A B x⟫ =
      2 * π * ∫ r in Ioo 0 R, r ^ 2 *
        ((r ^ (l + 1) * A (r ^ 2) + l * r ^ (l - 1) * B (r ^ 2)) * meridianCoefficient W l 0 r +
          r ^ (l - 1) * B (r ^ 2) * meridianCoefficient W l 1 r) := by
  set f : ℝ^3 → ℝ := fun x ↦ ⟪W x, meridionalTest l A B x⟫ with hf
  have hrot : IsInvariantUnderAxisRotation f := by
    intro φ x
    simp only [hf]
    rw [hW, meridionalTest_axisRotation, inner_axisRotation_axisRotation]
  have hcont := continuous_meridionalTest l hA hB
  have hint : IntegrableOn f (Metric.ball (0 : ℝ^3) R) := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℝ^3) R).exists_bound_of_continuousOn
      hcont.continuousOn
    refine Integrable.mono' (hWint.norm.mul_const M)
      (hWint.aestronglyMeasurable.inner hcont.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact (norm_inner_le_norm _ _).trans (by gcongr; exact hM x (Metric.ball_subset_closedBall hx))
  rw [setIntegral_ball_of_axisymmetric hrot hint]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_integrableOn_meridian hWm hW hWint l 0,
    ae_integrableOn_meridian hWm hW hWint l 1] with r h0 h1
  have h0' := (intervalIntegrable_iff_integrableOn_Ioo_of_le pi_pos.le).mpr h0
  have h1' := (intervalIntegrable_iff_integrableOn_Ioo_of_le pi_pos.le).mpr h1
  rw [meridianCoefficient, meridianCoefficient, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      (h0'.const_mul _) (h1'.const_mul _), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ ↦ ?_
  simp only [hf, meridionalTest_point, inner_add_right, real_inner_smul_right]
  ring

/-- The factor `2 l F'` of `h_l x` in the curl test field `curl(F(‖x‖²)(x × ∇h_l))`. -/
abbrev curlFactorA (l : ℕ) (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  2 * l * deriv F s

/-- The factor `-(2 s F' + (l + 1) F)` of `∇h_l` in the curl test field. -/
abbrev curlFactorB (l : ℕ) (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  -(2 * s * deriv F s + ((l : ℝ) + 1) * F s)

/-- The radial Helmholtz operator `4 s F'' + (4l + 6) F' + μ F` on the factors of degree `l`. -/
abbrev radialHelmholtz (l : ℕ) (μ : ℝ) (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  4 * s * deriv (deriv F) s + (4 * l + 6) * deriv F s + μ * F s

/-- **Curl tests.** For smooth `F`, the factors `A = 2l F'` and `B = -(2 s F' + (l + 1) F)`
(the meridional field `curl(F(‖x‖²)(x × ∇h_l))`) give a divergence-free field, and
`Δ v(A, B) + μ v(A, B)` is the curl test of `K = 4 s F'' + (4l + 6) F' + μ F`. -/
theorem curlTest_identities {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (l : ℕ) (μ s : ℝ) :
    (2 * s * deriv (curlFactorA l F) s + ((l : ℝ) + 3) * curlFactorA l F s +
        2 * l * deriv (curlFactorB l F) s = 0) ∧
      (radialLaplacian ((l : ℝ) + 1) (curlFactorA l F) s + μ * curlFactorA l F s =
        2 * l * deriv (radialHelmholtz l μ F) s) ∧
      (2 * curlFactorA l F s + radialLaplacian ((l : ℝ) - 1) (curlFactorB l F) s +
          μ * curlFactorB l F s =
        -(2 * s * deriv (radialHelmholtz l μ F) s + ((l : ℝ) + 1) * radialHelmholtz l μ F s)) := by
  set A := curlFactorA l F with hAdef
  set B := curlFactorB l F with hBdef
  set K := radialHelmholtz l μ F with hKdef
  have hF1 (t : ℝ) : HasDerivAt F (deriv F t) t := (hF.differentiable (by simp) t).hasDerivAt
  have hD1 : ContDiff ℝ ∞ (deriv F) := hF.iterate_deriv 1
  have hD2 : ContDiff ℝ ∞ (deriv (deriv F)) := by
    simpa [Function.iterate_succ] using hF.iterate_deriv 2
  have hF2 (t : ℝ) : HasDerivAt (deriv F) (deriv (deriv F) t) t :=
    (hD1.differentiable (by simp) t).hasDerivAt
  have hF3 (t : ℝ) : HasDerivAt (deriv (deriv F)) (deriv (deriv (deriv F)) t) t :=
    (hD2.differentiable (by simp) t).hasDerivAt
  have hid (t : ℝ) : HasDerivAt (fun t : ℝ ↦ t) 1 t := hasDerivAt_id' t
  have hA1 (t : ℝ) : HasDerivAt A (2 * l * deriv (deriv F) t) t := (hF2 t).const_mul _
  have hA2 (t : ℝ) : HasDerivAt (deriv A) (2 * l * deriv (deriv (deriv F)) t) t := by
    rw [show deriv A = _ from funext fun t ↦ (hA1 t).deriv]
    exact (hF3 t).const_mul _
  have hB1 (t : ℝ) : HasDerivAt B (-(2 * deriv F t + 2 * t * deriv (deriv F) t +
      ((l : ℝ) + 1) * deriv F t)) t :=
    ((((hid t).const_mul 2).mul (hF2 t)).add ((hF1 t).const_mul ((l : ℝ) + 1))).neg.congr_deriv
      (by ring)
  have hB2 (t : ℝ) : HasDerivAt (deriv B) (-(2 * deriv (deriv F) t + 2 * deriv (deriv F) t +
      2 * t * deriv (deriv (deriv F)) t + ((l : ℝ) + 1) * deriv (deriv F) t)) t := by
    rw [show deriv B = _ from funext fun t ↦ (hB1 t).deriv]
    exact ((((hF2 t).const_mul 2).add (((hid t).const_mul 2).mul (hF3 t))).add
      ((hF2 t).const_mul ((l : ℝ) + 1))).neg.congr_deriv (by ring)
  have hK1 (t : ℝ) : HasDerivAt K (4 * deriv (deriv F) t + 4 * t * deriv (deriv (deriv F)) t +
      (4 * l + 6) * deriv (deriv F) t + μ * deriv F t) t :=
    ((((hid t).const_mul 4).mul (hF3 t)).add ((hF2 t).const_mul (4 * (l : ℝ) + 6))).add
      ((hF1 t).const_mul μ) |>.congr_deriv (by ring)
  rw [(hA1 s).deriv, (hB1 s).deriv, (hK1 s).deriv]
  simp only [radialLaplacian, (hA2 s).deriv, (hB2 s).deriv, (hA1 s).deriv, (hB1 s).deriv]
  simp only [hAdef, hBdef, hKdef, curlFactorA, curlFactorB, radialHelmholtz]
  refine ⟨by ring, by ring, by ring⟩

end PDE.Fluid.Stokes.Ball
