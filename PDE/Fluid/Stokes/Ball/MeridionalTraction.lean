/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.MeridionalSolution
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalToWeak

/-!
# The boundary condition of the meridional family

For smooth `A`, `B`, `P` let `w = v(A, B)`, `p = P(‖x‖²) h_l` and let
`τ = v(E_{l+1} A - P, E_{l-1} B)` with `E_c F = 2 s F' + c F` (`radialEuler`), so that
`τ = (∇w) x - p x` is the pseudo-traction of `w` on spheres. Every weakly differentiable field
satisfies a Green identity with this traction on the ball of radius `R`
(`integral_meridional_traction`). If the meridional coefficients of a weak eigenfunction are those
of a smooth classical eigenfunction `Z = v(A, B)` with pressure `P(‖x‖²) h_l`, then `Z` has zero
traction on the sphere, `E_{l+1} A(R²) = P(R²)` and `E_{l-1} B(R²) = 0`
(`traction_eq_zero_of_weak_eigen`).

## How it works

The matrix field `T = ∇w - p I - R⁻² τ ⊗ x` has vanishing normal component on the sphere `‖x‖ = R`,
so the integration by parts of `PDE.Analysis.integral_sum_mul_partialDeriv_add_mul_eq_zero` against
`T` leaves no boundary term, and this is the Green identity. For the traction theorem we first show
that the Euler field of the weak derivatives has the meridional coefficients of `E Z`, so that
against meridional test fields the weak eigenfunction and its Euler field pair as `Z` and `E Z` do.
We apply the Green identity to the weak eigenfunction, to `Z` and to a divergence-free meridional
test field `v(A', B')`; with the two eigenvalue equations the volume terms cancel and leave the
boundary pairing of `integral_inner_euler_add_eq`, one linear relation between the boundary values
at `R` of the radial and polar profiles of the test and of the traction. The tests `v(0, 1)` and
`v(c₀, s)` with `c₀ = -2l/(l + 3)` are divergence free with independent boundary values, so both
components of the traction vanish.
-/

@[expose] public noncomputable section

open MeasureTheory Set Real MvPolynomial Filter
open PDE (partialDeriv laplacian divergence)
open PDE.Analysis.SpecialFunctions PDE.CoordinateSystems PDE.CoordinateSystems.Spherical
open scoped RealInnerProductSpace ContDiff Topology

namespace PDE.Fluid.Stokes.Ball

/-- The Euler operator `2 s F'(s) + c F(s)` on the radial factors of meridional fields:
`∑ⱼ xⱼ ∂ⱼ v(A, B) = v(E_{l+1} A, E_{l-1} B)`. -/
def radialEuler (c : ℝ) (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  2 * s * deriv F s + c * F s

/-- The Euler operator preserves smoothness. -/
theorem contDiff_radialEuler (c : ℝ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (radialEuler c F) :=
  ((contDiff_const.mul contDiff_id).mul (hF.iterate_deriv 1)).add (contDiff_const.mul hF)

/-- The radial factor `K_{l+1} A - 2 P' - R⁻² E_{l+4}(E_{l+1} A - P)` of
`Δw - ∇p - R⁻² (E τ + 3 τ)` for `w = v(A, B)`, `p = P(‖x‖²) h_l` and the traction field
`τ = v(E_{l+1} A - P, E_{l-1} B)`. -/
def tractionRadial (l : ℕ) (R : ℝ) (A P : ℝ → ℝ) (s : ℝ) : ℝ :=
  radialLaplacian ((l : ℝ) + 1) A s - 2 * deriv P s -
    radialEuler ((l : ℝ) + 4) (fun t ↦ radialEuler ((l : ℝ) + 1) A t - P t) s / R ^ 2

/-- The polar factor `2 A + K_{l-1} B - P - R⁻² E_{l+2}(E_{l-1} B)` of
`Δw - ∇p - R⁻² (E τ + 3 τ)`. -/
def tractionPolar (l : ℕ) (R : ℝ) (A B P : ℝ → ℝ) (s : ℝ) : ℝ :=
  2 * A s + radialLaplacian ((l : ℝ) - 1) B s - P s -
    radialEuler ((l : ℝ) + 2) (radialEuler ((l : ℝ) - 1) B) s / R ^ 2

private theorem continuous_radialLaplacian (c : ℝ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    Continuous (radialLaplacian c F) := by
  have h2 : Continuous (deriv (deriv F)) := by
    have := (hF.iterate_deriv 2).continuous
    simpa [Function.iterate_succ] using this
  have h1 : Continuous (deriv F) := (hF.iterate_deriv 1).continuous
  unfold radialLaplacian
  fun_prop

/-- The radial factor of the traction identity is continuous. -/
theorem continuous_tractionRadial (l : ℕ) (R : ℝ) {A P : ℝ → ℝ} (hA : ContDiff ℝ ∞ A)
    (hP : ContDiff ℝ ∞ P) : Continuous (tractionRadial l R A P) := by
  have h1 := continuous_radialLaplacian ((l : ℝ) + 1) hA
  have h2 : Continuous (deriv P) := (hP.iterate_deriv 1).continuous
  have h3 := (contDiff_radialEuler ((l : ℝ) + 4)
    ((contDiff_radialEuler ((l : ℝ) + 1) hA).sub hP)).continuous
  unfold tractionRadial
  fun_prop

/-- The polar factor of the traction identity is continuous. -/
theorem continuous_tractionPolar (l : ℕ) (R : ℝ) {A B P : ℝ → ℝ} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) (hP : ContDiff ℝ ∞ P) : Continuous (tractionPolar l R A B P) := by
  have h1 := continuous_radialLaplacian ((l : ℝ) - 1) hB
  have h3 := (contDiff_radialEuler ((l : ℝ) + 2)
    (contDiff_radialEuler ((l : ℝ) - 1) hB)).continuous
  have := hA.continuous
  have := hP.continuous
  unfold tractionPolar
  fun_prop

/-- **Green identity with the traction.** For `v` with integrable components and weak
derivatives `Dv` on the ball and smooth `A`, `B`, `P`, let `w = v(A, B)`, `p = P(‖x‖²) h_l` and
`τ = v(E_{l+1} A - P, E_{l-1} B)`, so that `τ = (∇w) x - p x`. The integration by parts
against `T = ∇w - p I - R⁻² τ ⊗ x`, whose normal component vanishes on the sphere, gives
`∫ ⟪v, Δw - ∇p - R⁻² (E τ + 3 τ)⟫ + ∫ Dv : ∇w - ∫ (tr Dv) p - R⁻² ∫ ⟪E v, τ⟫ = 0`. -/
theorem integral_meridional_traction {R : ℝ} (hR : 0 < R) (l : ℕ) {v : ℝ^3 → ℝ^3}
    {Dv : Fin 3 → Fin 3 → ℝ^3 → ℝ}
    (hv : ∀ i, IntegrableOn (fun x ↦ v x i) (Metric.ball (0 : ℝ^3) R))
    (hDv : ∀ i j, IntegrableOn (Dv i j) (Metric.ball (0 : ℝ^3) R))
    (hweak : ∀ i j, SobolevSpace.HasWeakDerivativeOn (Metric.ball (0 : ℝ^3) R) [j]
      (fun x ↦ v x i) (Dv i j))
    {A B P : ℝ → ℝ} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (hP : ContDiff ℝ ∞ P) :
    (∫ x in Metric.ball (0 : ℝ^3) R, ⟪v x, meridionalTest l
        (tractionRadial l R A P) (tractionPolar l R A B P) x⟫) +
      (∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
        Dv i j x * ∂[j] (fun y ↦ meridionalTest l A B y i) x) -
      (∫ x in Metric.ball (0 : ℝ^3) R,
        (∑ i, Dv i i x) * (P (‖x‖ ^ 2) * eval x.ofLp (zonalSolidHarmonicPolynomial l))) -
      (∫ x in Metric.ball (0 : ℝ^3) R, ⟪eulerField Dv x, meridionalTest l
        (fun t ↦ radialEuler ((l : ℝ) + 1) A t - P t) (radialEuler ((l : ℝ) - 1) B) x⟫) / R ^ 2
      = 0 := by
  set B₀ := Metric.ball (0 : ℝ^3) R
  set h := zonalSolidHarmonicPolynomial l with hh
  set τA : ℝ → ℝ := fun t ↦ radialEuler ((l : ℝ) + 1) A t - P t with hτA
  set τB : ℝ → ℝ := radialEuler ((l : ℝ) - 1) B with hτB
  have hτAC : ContDiff ℝ ∞ τA := (contDiff_radialEuler _ hA).sub hP
  have hτBC : ContDiff ℝ ∞ τB := contDiff_radialEuler _ hB
  set w := meridionalTest l A B with hw
  set τ := meridionalTest l τA τB with hτ
  set p : ℝ^3 → ℝ := fun y ↦ P (‖y‖ ^ 2) * eval y.ofLp h with hp
  have hwC : ContDiff ℝ ∞ w := contDiff_meridionalTest l hA hB
  have hτC : ContDiff ℝ ∞ τ := contDiff_meridionalTest l hτAC hτBC
  have hwi (i : Fin 3) : ContDiff ℝ ∞ (fun y ↦ w y i) := (contDiff_piLp_apply 2).comp hwC
  have hτi (i : Fin 3) : ContDiff ℝ ∞ (fun y ↦ τ y i) := (contDiff_piLp_apply 2).comp hτC
  have hpC : ContDiff ℝ ∞ p := contDiff_radial_mul_eval hP
  have hcoord (j : Fin 3) : ContDiff ℝ ∞ (fun y : ℝ^3 ↦ y j) := contDiff_piLp_apply 2
  set T : Fin 3 → Fin 3 → ℝ^3 → ℝ := fun i j y ↦
    ∂[j] (fun z ↦ w z i) y - (if i = j then 1 else 0) * p y - (R ^ 2)⁻¹ * (τ y i * y j)
    with hT
  have hTeq : ∀ i j, T i j = fun y ↦
      ∂[j] (fun z ↦ w z i) y - (if i = j then 1 else 0) * p y - (R ^ 2)⁻¹ * (τ y i * y j) :=
    fun _ _ ↦ rfl
  have hTC : ∀ i j, ContDiff ℝ ∞ (T i j) := fun i j ↦ by
    rw [hTeq]
    exact (((hwi i).partialDeriv j).sub (contDiff_const.mul hpC)).sub
      (contDiff_const.mul ((hτi i).mul (hcoord j)))
  -- the pointwise identities
  have hpX (x : ℝ^3) (i : Fin 3) : p x * x i = meridionalTest l P (fun _ ↦ 0) x i := by
    simp only [hp, meridionalTest_apply, map_mul, eval_X, zero_mul, add_zero]
    rw [show x.ofLp i = x i from rfl]
    ring
  have hEw (x : ℝ^3) (i : Fin 3) : ∑ j, ∂[j] (fun y ↦ w y i) x * x j =
      meridionalTest l (radialEuler ((l : ℝ) + 1) A) (radialEuler ((l : ℝ) - 1) B) x i :=
    sum_partialDeriv_meridionalTest_mul l hA hB x i
  have hEτ (x : ℝ^3) (i : Fin 3) : ∑ j, ∂[j] (fun y ↦ τ y i) x * x j =
      meridionalTest l (radialEuler ((l : ℝ) + 1) τA) (radialEuler ((l : ℝ) - 1) τB) x i :=
    sum_partialDeriv_meridionalTest_mul l hτAC hτBC x i
  have hnorm (x : ℝ^3) : ∑ j, x j * x j = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [sq]
  have hTn : ∀ x : ℝ^3, ‖x‖ = R → ∀ i, ∑ j, T i j x * x j = 0 := by
    intro x hx i
    have hR2 : (R ^ 2)⁻¹ * ‖x‖ ^ 2 = 1 := by rw [hx]; field_simp
    have hsum : ∑ j, T i j x * x j = ∑ j, ∂[j] (fun y ↦ w y i) x * x j - p x * x i -
        (R ^ 2)⁻¹ * τ x i * ∑ j, x j * x j := by
      simp only [hT, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    rw [hsum, hEw, hpX, hnorm, mul_assoc, mul_comm (τ x i), ← mul_assoc, hR2, one_mul]
    simp only [hτ, hτA, hτB, meridionalTest_apply]
    ring
  have htool := PDE.Analysis.integral_sum_mul_partialDeriv_add_mul_eq_zero hR hTC hTn
    (v := fun i x ↦ v x i) hv hDv hweak
  -- the divergence of `T`
  have hdT (x : ℝ^3) (i : Fin 3) : ∑ j, ∂[j] (T i j) x =
      meridionalTest l (tractionRadial l R A P) (tractionPolar l R A B P) x i := by
    have hj (j : Fin 3) : ∂[j] (T i j) x = ∂[j] (fun y ↦ ∂[j] (fun z ↦ w z i) y) x -
        (if i = j then 1 else 0) * ∂[j] p x -
          (R ^ 2)⁻¹ * (∂[j] (fun y ↦ τ y i) x * x j + τ x i * (if j = j then 1 else 0)) := by
      have h₁ : DifferentiableAt ℝ (∂[j] (fun z ↦ w z i)) x :=
        ((hwi i).partialDeriv j).differentiable (by simp) x
      have h₂ : DifferentiableAt ℝ (fun y ↦ (if i = j then (1 : ℝ) else 0) * p y) x :=
        (contDiff_const.mul hpC).differentiable (by simp) x
      have h₃ : DifferentiableAt ℝ (fun y ↦ (R ^ 2)⁻¹ * (τ y i * y j)) x :=
        (contDiff_const.mul ((hτi i).mul (hcoord j))).differentiable (by simp) x
      have h₄ : DifferentiableAt ℝ (fun y ↦ τ y i * y j) x :=
        ((hτi i).mul (hcoord j)).differentiable (by simp) x
      rw [hTeq, partialDeriv_sub (f := fun y ↦ ∂[j] (fun z ↦ w z i) y -
        (if i = j then (1 : ℝ) else 0) * p y) (h₁.sub h₂) h₃, partialDeriv_sub h₁ h₂,
        partialDeriv_mul (differentiableAt_const _) (hpC.differentiable (by simp) x),
        partialDeriv_mul (differentiableAt_const _) h₄,
        partialDeriv_mul ((hτi i).differentiable (by simp) x)
          ((hcoord j).differentiable (by simp) x), partialDeriv_coord,
        partialDeriv_const, partialDeriv_const, zero_mul, zero_add, zero_mul, zero_add]
    simp only [hj, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, ← Finset.mul_sum, Finset.sum_add_distrib, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hlap := laplacian_meridionalTest l hA hB x i
    simp only [laplacian] at hlap
    rw [hlap, hp, partialDeriv_radial_mul_zonal l (hP.differentiable (by simp)) x i, hEτ]
    simp only [meridionalTest_apply, radialEuler, hτ, tractionRadial, tractionPolar, hτA, hτB]
    push_cast
    ring
  have hmul : ∀ {g : ℝ^3 → ℝ}, Continuous g → ∀ {f : ℝ^3 → ℝ}, IntegrableOn f B₀ →
      Integrable (fun x ↦ f x * g x) (volume.restrict B₀) := fun hg _ hf ↦
    hf.mul_continuousOn_of_subset hg.continuousOn measurableSet_ball
      (isCompact_closedBall 0 R) Metric.ball_subset_closedBall
  set W₁ := meridionalTest l (tractionRadial l R A P) (tractionPolar l R A B P) with hW₁
  have hW₁C : Continuous W₁ := continuous_meridionalTest l (continuous_tractionRadial l R hA hP)
    (continuous_tractionPolar l R hA hB hP)
  have hI1 : Integrable (fun x ↦ ∑ i, v x i * W₁ x i) (volume.restrict B₀) :=
    integrable_finsetSum _ fun i _ ↦ hmul ((continuous_apply i).comp
      ((PiLp.continuous_ofLp 2 _).comp hW₁C)) (hv i)
  have hI2 : Integrable (fun x ↦ ∑ i, ∑ j, Dv i j x * T i j x) (volume.restrict B₀) :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      hmul (hTC i j).continuous (hDv i j)
  have hsplit : ∫ x in B₀, ∑ i, ∑ j, (v x i * ∂[j] (T i j) x + Dv i j x * T i j x) =
      (∫ x in B₀, ∑ i, v x i * W₁ x i) + ∫ x in B₀, ∑ i, ∑ j, Dv i j x * T i j x := by
    rw [← integral_add hI1 hI2]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hdT, hW₁]
  have hJ1 : Integrable (fun x ↦ ∑ i, ∑ j, Dv i j x * ∂[j] (fun y ↦ w y i) x)
      (volume.restrict B₀) :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      hmul ((hwi i).partialDeriv j).continuous (hDv i j)
  have hJ2 : Integrable (fun x ↦ (∑ i, Dv i i x) * p x) (volume.restrict B₀) :=
    hmul hpC.continuous (integrable_finsetSum _ fun i _ ↦ hDv i i)
  have hJ3 : Integrable (fun x ↦ ⟪eulerField Dv x, τ x⟫) (volume.restrict B₀) := by
    simp only [eulerField, EuclideanSpace.real_inner_eq_sum, Finset.sum_mul]
    exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      (hmul ((hcoord j).continuous.mul (hτi i).continuous) (hDv i j)).congr
        (ae_of_all _ fun x ↦ by simp only [Pi.mul_apply]; ring)
  have hDT : ∫ x in B₀, ∑ i, ∑ j, Dv i j x * T i j x =
      (∫ x in B₀, ∑ i, ∑ j, Dv i j x * ∂[j] (fun y ↦ w y i) x) -
        (∫ x in B₀, (∑ i, Dv i i x) * p x) -
        (∫ x in B₀, ⟪eulerField Dv x, τ x⟫) / R ^ 2 := by
    have hJ12 : Integrable (fun x ↦ (∑ i, ∑ j, Dv i j x * ∂[j] (fun y ↦ w y i) x) -
        (∑ i, Dv i i x) * p x) (volume.restrict B₀) := hJ1.sub hJ2
    have hJ3' : Integrable (fun x ↦ (R ^ 2)⁻¹ * ⟪eulerField Dv x, τ x⟫) (volume.restrict B₀) :=
      hJ3.const_mul _
    rw [div_eq_inv_mul, ← integral_const_mul, ← integral_sub hJ1 hJ2, ← integral_sub hJ12 hJ3']
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [hT, eulerField, EuclideanSpace.real_inner_eq_sum, mul_sub,
      Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    have hsum : ∑ i, ∑ j, Dv i j x * ((if i = j then (1 : ℝ) else 0) * p x) =
        ∑ i, Dv i i x * p x := by
      simp [mul_ite]
    rw [hsum]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [hsplit, hDT] at htool
  have hinner : ∫ x in B₀, ∑ i, v x i * W₁ x i = ∫ x in B₀, ⟪v x, W₁ x⟫ :=
    integral_congr_ae (ae_of_all _ fun x ↦ by simp only [EuclideanSpace.real_inner_eq_sum])
  rw [hinner] at htool
  linarith

private theorem differentiable_pow_mul_comp_sq (n : ℕ) {F : ℝ → ℝ} (hF : Differentiable ℝ F) :
    Differentiable ℝ fun s : ℝ ↦ s ^ n * F (s ^ 2) :=
  (differentiable_pow n).mul (hF.comp (differentiable_pow 2))

/-- The radial profile is smooth. -/
theorem contDiff_radialProfile (l : ℕ) {A B : ℝ → ℝ} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (radialProfile l A B) :=
  ((contDiff_id.pow _).mul (hA.comp (contDiff_id.pow 2))).add
    ((contDiff_const.mul (contDiff_id.pow _)).mul (hB.comp (contDiff_id.pow 2)))

/-- The polar profile is smooth. -/
theorem contDiff_polarProfile (l : ℕ) {B : ℝ → ℝ} (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (polarProfile l B) :=
  (contDiff_id.pow _).mul (hB.comp (contDiff_id.pow 2))

/-- The Euler derivative of the radial profile: `r ρ'(r)` is the radial profile of
`v(E_{l+1} A, E_{l-1} B)`. -/
theorem mul_deriv_radialProfile {l : ℕ} (hl : 1 ≤ l) {A B : ℝ → ℝ} (hA : Differentiable ℝ A)
    (hB : Differentiable ℝ B) (r : ℝ) :
    r * deriv (radialProfile l A B) r =
      radialProfile l (radialEuler ((l : ℝ) + 1) A) (radialEuler ((l : ℝ) - 1) B) r := by
  have hfun : radialProfile l A B = (fun s ↦ s ^ (l + 1) * A (s ^ 2)) +
      fun s ↦ (l : ℝ) * (s ^ (l - 1) * B (s ^ 2)) := by
    funext s
    simp only [radialProfile, Pi.add_apply]
    ring
  have hd1 : HasDerivAt (fun s ↦ s ^ (l + 1) * A (s ^ 2))
      (deriv (fun s ↦ s ^ (l + 1) * A (s ^ 2)) r) r :=
    (differentiable_pow_mul_comp_sq (l + 1) hA r).hasDerivAt
  have hd2 : HasDerivAt (fun s ↦ s ^ (l - 1) * B (s ^ 2))
      (deriv (fun s ↦ s ^ (l - 1) * B (s ^ 2)) r) r :=
    (differentiable_pow_mul_comp_sq (l - 1) hB r).hasDerivAt
  have h := hd1.add (hd2.const_mul (l : ℝ))
  rw [hfun, h.deriv, mul_add, mul_left_comm, mul_deriv_pow_mul_comp_sq hA,
    mul_deriv_pow_mul_comp_sq hB]
  simp only [radialProfile, radialEuler]
  rw [Nat.cast_sub hl]
  push_cast
  ring

/-- The Euler derivative of the polar profile: `r τ'(r)` is the polar profile of
`v(·, E_{l-1} B)`. -/
theorem mul_deriv_polarProfile {l : ℕ} (hl : 1 ≤ l) {B : ℝ → ℝ} (hB : Differentiable ℝ B)
    (r : ℝ) :
    r * deriv (polarProfile l B) r = polarProfile l (radialEuler ((l : ℝ) - 1) B) r := by
  have hfun : polarProfile l B = fun s ↦ s ^ (l - 1) * B (s ^ 2) := rfl
  rw [hfun, mul_deriv_pow_mul_comp_sq hB]
  simp only [polarProfile, radialEuler]
  rw [Nat.cast_sub hl]
  push_cast
  ring

/-- Meridional fields with continuous factors are integrable on the ball. -/
theorem integrableOn_meridionalTest (R : ℝ) (l : ℕ) {A B : ℝ → ℝ} (hA : Continuous A)
    (hB : Continuous B) : IntegrableOn (meridionalTest l A B) (Metric.ball (0 : ℝ^3) R) :=
  ((continuous_meridionalTest l hA hB).continuousOn.integrableOn_compact
    (isCompact_closedBall 0 R)).mono_set Metric.ball_subset_closedBall

/-- The ball integral of the pairing of two meridional fields of degree `l`:
`2π ∫₀^R r² (‖Y_l‖² ρ ρ' + ‖X_l‖² τ τ') dr`. -/
theorem setIntegral_inner_meridionalTest_meridionalTest (R : ℝ) (l : ℕ) {A B A' B' : ℝ → ℝ}
    (hA : Continuous A) (hB : Continuous B) (hA' : Continuous A') (hB' : Continuous B') :
    ∫ x in Metric.ball (0 : ℝ^3) R, ⟪meridionalTest l A B x, meridionalTest l A' B' x⟫ =
      2 * π * ∫ r in Ioo 0 R, r ^ 2 *
        (vectorHarmonicNormSq l 0 * radialProfile l A B r * radialProfile l A' B' r +
          vectorHarmonicNormSq l 1 * polarProfile l B r * polarProfile l B' r) := by
  rw [setIntegral_inner_meridionalTest (continuous_meridionalTest l hA hB).measurable
    (meridionalTest_axisRotation l A B) (integrableOn_meridionalTest R l hA hB) l hA' hB']
  congr 1
  refine integral_congr_ae (ae_of_all _ fun r ↦ ?_)
  simp only [meridianCoefficient_meridionalTest_zero, meridianCoefficient_meridionalTest_one,
    radialProfile, polarProfile]
  ring

/-- **The boundary pairing.** For meridional fields `w = v(A, B)` and `τ = v(A', B')` of degree
`l ≥ 1`, `∫_B ⟪w, E τ + 3 τ⟫ + ⟪E w, τ⟫ = 2π R³ (‖Y_l‖² ρ_w(R) ρ_τ(R) + ‖X_l‖² τ_w(R) τ_τ(R))`,
the integral over the ball of the divergence of `⟪w, τ⟫ x`. -/
theorem integral_inner_euler_add_eq {R : ℝ} (hR : 0 < R) {l : ℕ} (hl : 1 ≤ l)
    {A B A' B' : ℝ → ℝ} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (hA' : ContDiff ℝ ∞ A')
    (hB' : ContDiff ℝ ∞ B') :
    (∫ x in Metric.ball (0 : ℝ^3) R, ⟪meridionalTest l A B x, meridionalTest l
        (radialEuler ((l : ℝ) + 4) A') (radialEuler ((l : ℝ) + 2) B') x⟫) +
      (∫ x in Metric.ball (0 : ℝ^3) R, ⟪meridionalTest l (radialEuler ((l : ℝ) + 1) A)
        (radialEuler ((l : ℝ) - 1) B) x, meridionalTest l A' B' x⟫) =
      2 * π * R ^ 3 * (vectorHarmonicNormSq l 0 * radialProfile l A B R *
        radialProfile l A' B' R + vectorHarmonicNormSq l 1 * polarProfile l B R *
          polarProfile l B' R) := by
  set N0 := vectorHarmonicNormSq l 0
  set N1 := vectorHarmonicNormSq l 1
  have hE (c : ℝ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) : Continuous (radialEuler c F) :=
    (contDiff_radialEuler c hF).continuous
  rw [setIntegral_inner_meridionalTest_meridionalTest R l hA.continuous hB.continuous
      (hE _ hA') (hE _ hB'),
    setIntegral_inner_meridionalTest_meridionalTest R l (hE _ hA) (hE _ hB) hA'.continuous
      hB'.continuous, ← mul_add]
  have hdA := hA.differentiable (by simp)
  have hdB := hB.differentiable (by simp)
  have hdA' := hA'.differentiable (by simp)
  have hdB' := hB'.differentiable (by simp)
  set ρ := radialProfile l A B
  set ρ' := radialProfile l A' B'
  set σ := polarProfile l B
  set σ' := polarProfile l B'
  have hρC : ContDiff ℝ ∞ ρ := contDiff_radialProfile l hA hB
  have hρ'C : ContDiff ℝ ∞ ρ' := contDiff_radialProfile l hA' hB'
  have hσC : ContDiff ℝ ∞ σ := contDiff_polarProfile l hB
  have hσ'C : ContDiff ℝ ∞ σ' := contDiff_polarProfile l hB'
  have := hρC.continuous
  have := hρ'C.continuous
  have := hσC.continuous
  have := hσ'C.continuous
  -- the profiles of `E τ + 3 τ`
  have h4 (r : ℝ) : radialProfile l (radialEuler ((l : ℝ) + 4) A')
      (radialEuler ((l : ℝ) + 2) B') r = r * deriv ρ' r + 3 * ρ' r := by
    rw [mul_deriv_radialProfile hl hdA' hdB']
    simp only [radialProfile, radialEuler, ρ']
    ring
  have h2 (r : ℝ) : polarProfile l (radialEuler ((l : ℝ) + 2) B') r =
      r * deriv σ' r + 3 * σ' r := by
    rw [mul_deriv_polarProfile hl hdB']
    simp only [polarProfile, radialEuler, σ']
    ring
  set F : ℝ → ℝ := fun r ↦ r ^ 3 * (N0 * ρ r * ρ' r + N1 * σ r * σ' r) with hF
  set F' : ℝ → ℝ := fun r ↦ 3 * r ^ 2 * (N0 * ρ r * ρ' r + N1 * σ r * σ' r) +
    r ^ 3 * (N0 * (deriv ρ r * ρ' r + ρ r * deriv ρ' r) +
      N1 * (deriv σ r * σ' r + σ r * deriv σ' r)) with hF'
  have hd (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (r : ℝ) : HasDerivAt f (deriv f r) r :=
    (hf.differentiable (by simp) r).hasDerivAt
  have hFd (r : ℝ) : HasDerivAt F (F' r) r := by
    have h := (hasDerivAt_pow 3 r).mul ((((hd ρ hρC r).mul (hd ρ' hρ'C r)).const_mul N0).add
      (((hd σ hσC r).mul (hd σ' hσ'C r)).const_mul N1))
    convert h using 1
    · funext r
      simp only [hF, Pi.mul_apply, Pi.add_apply]
      ring
    · simp only [hF', Pi.mul_apply, Pi.add_apply]
      push_cast
      ring
  have hF'c : Continuous F' := by
    have c1 := hρC.continuous_deriv (by simp)
    have c2 := hρ'C.continuous_deriv (by simp)
    have c3 := hσC.continuous_deriv (by simp)
    have c4 := hσ'C.continuous_deriv (by simp)
    simp only [hF']
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := R)
    (fun r _ ↦ hFd r) (hF'c.intervalIntegrable _ _)
  rw [intervalIntegral.integral_of_le hR.le, integral_Ioc_eq_integral_Ioo] at hFTC
  have hint : ∫ r in Ioo 0 R, (r ^ 2 * (N0 * ρ r * radialProfile l (radialEuler ((l : ℝ) + 4) A')
      (radialEuler ((l : ℝ) + 2) B') r + N1 * σ r *
        polarProfile l (radialEuler ((l : ℝ) + 2) B') r) +
      r ^ 2 * (N0 * radialProfile l (radialEuler ((l : ℝ) + 1) A) (radialEuler ((l : ℝ) - 1) B) r *
        ρ' r + N1 * polarProfile l (radialEuler ((l : ℝ) - 1) B) r * σ' r)) =
      ∫ r in Ioo 0 R, F' r := by
    refine integral_congr_ae (ae_of_all _ fun r ↦ ?_)
    dsimp only
    rw [h4, h2, ← mul_deriv_radialProfile hl hdA hdB, ← mul_deriv_polarProfile hl hdB]
    simp only [hF']
    ring
  have hI1 : IntegrableOn (fun r ↦ r ^ 2 * (N0 * ρ r * radialProfile l
      (radialEuler ((l : ℝ) + 4) A') (radialEuler ((l : ℝ) + 2) B') r +
        N1 * σ r * polarProfile l (radialEuler ((l : ℝ) + 2) B') r)) (Ioo 0 R) := by
    have c1 := (contDiff_radialProfile l (contDiff_radialEuler ((l : ℝ) + 4) hA')
      (contDiff_radialEuler ((l : ℝ) + 2) hB')).continuous
    have c2 := (contDiff_polarProfile l (contDiff_radialEuler ((l : ℝ) + 2) hB')).continuous
    exact Continuous.integrableOn_Icc (a := 0) (b := R) (by fun_prop) |>.mono_set
      Ioo_subset_Icc_self
  have hI2 : IntegrableOn (fun r ↦ r ^ 2 * (N0 * radialProfile l (radialEuler ((l : ℝ) + 1) A)
      (radialEuler ((l : ℝ) - 1) B) r * ρ' r + N1 * polarProfile l
        (radialEuler ((l : ℝ) - 1) B) r * σ' r)) (Ioo 0 R) := by
    have c1 := (contDiff_radialProfile l (contDiff_radialEuler ((l : ℝ) + 1) hA)
      (contDiff_radialEuler ((l : ℝ) - 1) hB)).continuous
    have c2 := (contDiff_polarProfile l (contDiff_radialEuler ((l : ℝ) - 1) hB)).continuous
    exact Continuous.integrableOn_Icc (a := 0) (b := R) (by fun_prop) |>.mono_set
      Ioo_subset_Icc_self
  rw [← integral_add hI1 hI2, hint, hFTC]
  simp only [hF]
  ring


/-- The Euler field of the classical derivatives of `v(A, B)` is `v(E_{l+1} A, E_{l-1} B)`. -/
theorem eulerField_meridionalTest (l : ℕ) {A B : ℝ → ℝ} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) :
    eulerField (fun i j ↦ ∂[j] (fun y ↦ meridionalTest l A B y i)) =
      meridionalTest l (radialEuler ((l : ℝ) + 1) A) (radialEuler ((l : ℝ) - 1) B) := by
  funext x
  ext i
  change _ = meridionalTest l (fun s ↦ 2 * s * deriv A s + ((l : ℝ) + 1) * A s)
    (fun s ↦ 2 * s * deriv B s + ((l : ℝ) - 1) * B s) x i
  rw [← sum_partialDeriv_meridionalTest_mul l hA hB x i]
  simp only [eulerField]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

/-- A smooth field has its classical partial derivatives as weak derivatives on the ball. -/
theorem hasWeakDerivativeOn_ball_of_contDiff {R : ℝ} {f : ℝ^3 → ℝ^3} (hf : ContDiff ℝ ∞ f)
    (i j : Fin 3) : SobolevSpace.HasWeakDerivativeOn (Metric.ball (0 : ℝ^3) R) [j]
      (fun x ↦ f x i) (∂[j] (fun y ↦ f y i)) :=
  SobolevSpace.hasWeakDerivativeOn_of_contDiffAt_one Metric.isOpen_ball
    (fun x _ ↦ (((contDiff_piLp_apply 2).comp hf).of_le (by simp)).contDiffAt) j

/-- **The traction of a meridional block vanishes.** Let `u` be a weak eigenfunction of
meridional parity with equivariant representative `w`, `e` an equivariant field with the
pairings of the Euler field, and `l ≥ 1`. Let `Z = v(A, B)` be divergence free and solve
`ΔZ - ∇(P h_l) = -μ Z` with pressure `P(‖x‖²) h_l`. If the meridian coefficients of `w` on `Y_l`
and `X_l` are almost everywhere those of `Z`, then the traction of `Z` vanishes on the sphere:
`E_{l+1} A (R²) = P(R²)` and `E_{l-1} B (R²) = 0`. -/
theorem traction_eq_zero_of_weak_eigen {R μ ε : ℝ} (hR : 0 < R) {l : ℕ} (hl : 1 ≤ l)
    (hpar : modeParity .meridional l = ε) {u : ℝ^3 → ℝ^3} {Du : Fin 3 → Fin 3 → ℝ^3 → ℝ}
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
    (huw : u =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) R)] w)
    {e : ℝ^3 → ℝ^3} (hem : Measurable e) (he : IsEquivariantUnderAxisRotation e)
    (heint : IntegrableOn e (Metric.ball (0 : ℝ^3) R))
    (hepair : ∀ Φ : ℝ^3 → ℝ^3, Continuous Φ → IsEquivariantUnderAxisRotation Φ →
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪e x, Φ x⟫ =
        ∫ x in Metric.ball (0 : ℝ^3) R, ⟪eulerField Du x, Φ x⟫)
    {A B P : ℝ → ℝ} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (hP : ContDiff ℝ ∞ P)
    (hfree : ∀ s, 2 * s * deriv A s + ((l : ℝ) + 3) * A s + 2 * l * deriv B s = 0)
    (heq1 : ∀ s, radialLaplacian ((l : ℝ) + 1) A s - 2 * deriv P s = -(μ * A s))
    (heq2 : ∀ s, 2 * A s + radialLaplacian ((l : ℝ) - 1) B s - P s = -(μ * B s))
    (ha : meridianCoefficient w l 0 =ᵐ[volume.restrict (Ioo 0 R)]
      meridianCoefficient (meridionalTest l A B) l 0)
    (hb : meridianCoefficient w l 1 =ᵐ[volume.restrict (Ioo 0 R)]
      meridianCoefficient (meridionalTest l A B) l 1) :
    radialEuler ((l : ℝ) + 1) A (R ^ 2) - P (R ^ 2) = 0 ∧
      radialEuler ((l : ℝ) - 1) B (R ^ 2) = 0 := by
  have hN0 : 0 < vectorHarmonicNormSq l 0 := vectorHarmonicNormSq_zero_pos l
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hN1 : 0 < vectorHarmonicNormSq l 1 := by rw [vectorHarmonicNormSq_one]; positivity
  have hZC : ContDiff ℝ ∞ (meridionalTest l A B) := contDiff_meridionalTest l hA hB
  have hEA := contDiff_radialEuler ((l : ℝ) + 1) hA
  have hEB := contDiff_radialEuler ((l : ℝ) - 1) hB
  have hdA := hA.differentiable (by simp)
  have hdB := hB.differentiable (by simp)
  have hball {E : Type} [NormedAddCommGroup E] {f : ℝ^3 → E} (hf : Continuous f) :
      IntegrableOn f (Metric.ball (0 : ℝ^3) R) :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set
      Metric.ball_subset_closedBall
  -- the Euler coefficients are those of `E Z`
  have he0 : meridianCoefficient e l 0 =ᵐ[volume.restrict (Ioo 0 R)] meridianCoefficient
      (meridionalTest l (radialEuler ((l : ℝ) + 1) A) (radialEuler ((l : ℝ) - 1) B)) l 0 := by
    have hg : meridianCoefficient (meridionalTest l A B) l 0 =
        fun r ↦ vectorHarmonicNormSq l 0 * radialProfile l A B r :=
      funext (meridianCoefficient_meridionalTest_zero l A B)
    filter_upwards [ae_eq_mul_deriv_of_weak hR
      (locallyIntegrableOn_meridianCoefficient hem he heint l 0)
      (hg ▸ (contDiff_const.mul (contDiff_radialProfile l hA hB)).of_le (by simp)) ha
      fun φ hφ hcs hs ↦ integral_mul_meridianCoefficient_radial_mul_deriv hR l hu hDu
        hweak hwm hw hwint huw hem he heint hepair hφ hcs hs] with r hr
    rw [hr, hg, meridianCoefficient_meridionalTest_zero,
      deriv_const_mul _ ((contDiff_radialProfile l hA hB).differentiable (by simp) r),
      mul_left_comm, mul_deriv_radialProfile hl hdA hdB]
  have he1 : meridianCoefficient e l 1 =ᵐ[volume.restrict (Ioo 0 R)] meridianCoefficient
      (meridionalTest l (radialEuler ((l : ℝ) + 1) A) (radialEuler ((l : ℝ) - 1) B)) l 1 := by
    have hg : meridianCoefficient (meridionalTest l A B) l 1 =
        fun r ↦ vectorHarmonicNormSq l 1 * polarProfile l B r :=
      funext (meridianCoefficient_meridionalTest_one l A B)
    filter_upwards [ae_eq_mul_deriv_of_weak hR
      (locallyIntegrableOn_meridianCoefficient hem he heint l 1)
      (hg ▸ (contDiff_const.mul (contDiff_polarProfile l hB)).of_le (by simp)) hb
      fun φ hφ hcs hs ↦ integral_mul_meridianCoefficient_polar_mul_deriv hR hl hu hDu
        hweak hwm hw hwint huw hem he heint hepair hφ hcs hs] with r hr
    rw [hr, hg, meridianCoefficient_meridionalTest_one,
      deriv_const_mul _ ((contDiff_polarProfile l hB).differentiable (by simp) r),
      mul_left_comm, mul_deriv_polarProfile hl hdB]
  -- swapping `w`, `e` for `Z`, `E Z` against meridional fields of degree `l`
  have hswap {W W' : ℝ^3 → ℝ^3} (hWm : Measurable W) (hW : IsEquivariantUnderAxisRotation W)
      (hWint : IntegrableOn W (Metric.ball (0 : ℝ^3) R)) (hW'm : Measurable W')
      (hW' : IsEquivariantUnderAxisRotation W')
      (hW'int : IntegrableOn W' (Metric.ball (0 : ℝ^3) R))
      (h0 : meridianCoefficient W l 0 =ᵐ[volume.restrict (Ioo 0 R)] meridianCoefficient W' l 0)
      (h1 : meridianCoefficient W l 1 =ᵐ[volume.restrict (Ioo 0 R)] meridianCoefficient W' l 1)
      {A₁ B₁ : ℝ → ℝ} (hA₁ : Continuous A₁) (hB₁ : Continuous B₁) :
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪W x, meridionalTest l A₁ B₁ x⟫ =
        ∫ x in Metric.ball (0 : ℝ^3) R, ⟪W' x, meridionalTest l A₁ B₁ x⟫ := by
    rw [setIntegral_inner_meridionalTest hWm hW hWint l hA₁ hB₁,
      setIntegral_inner_meridionalTest hW'm hW' hW'int l hA₁ hB₁]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [h0, h1] with r hr0 hr1
    rw [hr0, hr1]
  have hswapw {A₁ B₁ : ℝ → ℝ} (hA₁ : Continuous A₁) (hB₁ : Continuous B₁) :
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪u x, meridionalTest l A₁ B₁ x⟫ =
        ∫ x in Metric.ball (0 : ℝ^3) R, ⟪meridionalTest l A B x, meridionalTest l A₁ B₁ x⟫ := by
    rw [← hswap hwm hw hwint hZC.continuous.measurable (meridionalTest_axisRotation l A B)
      (hball hZC.continuous) ha hb hA₁ hB₁]
    exact integral_congr_ae (by filter_upwards [huw] with x hx; rw [hx])
  have hswape {A₁ B₁ : ℝ → ℝ} (hA₁ : Continuous A₁) (hB₁ : Continuous B₁) :
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪eulerField Du x, meridionalTest l A₁ B₁ x⟫ =
        ∫ x in Metric.ball (0 : ℝ^3) R, ⟪meridionalTest l (radialEuler ((l : ℝ) + 1) A)
          (radialEuler ((l : ℝ) - 1) B) x, meridionalTest l A₁ B₁ x⟫ := by
    rw [← hepair _ (continuous_meridionalTest l hA₁ hB₁) (meridionalTest_axisRotation l A₁ B₁)]
    exact hswap hem he heint (contDiff_meridionalTest l hEA hEB).continuous.measurable
      (meridionalTest_axisRotation l _ _) (hball (contDiff_meridionalTest l hEA hEB).continuous)
      he0 he1 hA₁ hB₁
  -- the boundary pairing of every divergence-free test with the traction of `Z`
  have hτAC : ContDiff ℝ ∞ (fun t ↦ radialEuler ((l : ℝ) + 1) A t - P t) := hEA.sub hP
  have hbdry : ∀ {A' B' : ℝ → ℝ}, ContDiff ℝ ∞ A' → ContDiff ℝ ∞ B' →
      (∀ s, 2 * s * deriv A' s + ((l : ℝ) + 3) * A' s + 2 * l * deriv B' s = 0) →
      vectorHarmonicNormSq l 0 * radialProfile l A' B' R *
          radialProfile l (fun t ↦ radialEuler ((l : ℝ) + 1) A t - P t)
            (radialEuler ((l : ℝ) - 1) B) R +
        vectorHarmonicNormSq l 1 * polarProfile l B' R *
          polarProfile l (radialEuler ((l : ℝ) - 1) B) R = 0 := by
    intro A' B' hA' hB' hfree'
    have hw'C : ContDiff ℝ ∞ (meridionalTest l A' B') := contDiff_meridionalTest l hA' hB'
    have hw'i (i : Fin 3) : ContDiff ℝ ∞ (fun y ↦ meridionalTest l A' B' y i) :=
      (contDiff_piLp_apply 2).comp hw'C
    have hZi (i : Fin 3) : ContDiff ℝ ∞ (fun y ↦ meridionalTest l A B y i) :=
      (contDiff_piLp_apply 2).comp hZC
    have hP0 : ContDiff ℝ ∞ (fun _ : ℝ ↦ (0 : ℝ)) := contDiff_const
    have hdivw' (x : ℝ^3) : ∑ i, ∂[i] (fun y ↦ meridionalTest l A' B' y i) x = 0 :=
      (divergence_meridionalTest l hA' hB' x).trans (by rw [hfree', zero_mul])
    -- Green identity for `u`, `Z` and the test
    have hGu := integral_meridional_traction hR l hu hDu hweak hA' hB' hP0
    have hGZ := integral_meridional_traction hR l
      (fun i ↦ hball (hZi i).continuous) (fun i j ↦ hball ((hZi i).partialDeriv j).continuous)
      (fun i j ↦ hasWeakDerivativeOn_ball_of_contDiff hZC i j) hA' hB' hP0
    have hGw := integral_meridional_traction hR l
      (fun i ↦ hball (hw'i i).continuous) (fun i j ↦ hball ((hw'i i).partialDeriv j).continuous)
      (fun i j ↦ hasWeakDerivativeOn_ball_of_contDiff hw'C i j) hA hB hP
    have hE := heig (meridionalTest l A' B') hw'C hdivw'
      (meridionalTest_axisRotation l A' B')
      (fun x ↦ hpar ▸ meridionalTest_equatorialReflection l A' B' x)
    simp only [zero_mul, mul_zero, integral_zero, sub_zero] at hGu hGZ
    rw [eulerField_meridionalTest l hA hB] at hGZ
    rw [eulerField_meridionalTest l hA' hB'] at hGw
    rw [hE, hswapw (continuous_tractionRadial l R hA' hP0)
      (continuous_tractionPolar l R hA' hB' hP0), hswapw hA'.continuous hB'.continuous,
      hswape (contDiff_radialEuler _ hA').continuous (contDiff_radialEuler _ hB').continuous] at hGu
    -- the pressure term of the test vanishes, and the gradient pairings agree
    have hp0 : ∫ x in Metric.ball (0 : ℝ^3) R, (∑ i, ∂[i] (fun y ↦ meridionalTest l A' B' y i) x) *
        (P (‖x‖ ^ 2) * eval x.ofLp (zonalSolidHarmonicPolynomial l)) = 0 := by
      simp [hdivw']
    -- the eigen-equation of `Z` in the Green identity of the test
    have hΦ : ∀ x, meridionalTest l (tractionRadial l R A P) (tractionPolar l R A B P) x =
        (-μ) • meridionalTest l A B x - (R ^ 2)⁻¹ • meridionalTest l
          (radialEuler ((l : ℝ) + 4) (fun t ↦ radialEuler ((l : ℝ) + 1) A t - P t))
          (radialEuler ((l : ℝ) + 2) (radialEuler ((l : ℝ) - 1) B)) x := by
      intro x
      ext i
      simp only [meridionalTest_apply, tractionRadial, tractionPolar, PiLp.sub_apply,
        PiLp.smul_apply, smul_eq_mul]
      have h1 := heq1 (‖x‖ ^ 2)
      have h2 := heq2 (‖x‖ ^ 2)
      rw [div_eq_inv_mul, div_eq_inv_mul]
      linear_combination (eval x.ofLp (zonalSolidHarmonicPolynomial l * X i)) * h1 +
        (eval x.ofLp (pderiv i (zonalSolidHarmonicPolynomial l))) * h2
    have hc1 : Continuous fun x ↦ ⟪meridionalTest l A' B' x, meridionalTest l A B x⟫ :=
      hw'C.continuous.inner hZC.continuous
    have hc2 : Continuous fun x ↦ ⟪meridionalTest l A' B' x, meridionalTest l
        (radialEuler ((l : ℝ) + 4) (fun t ↦ radialEuler ((l : ℝ) + 1) A t - P t))
        (radialEuler ((l : ℝ) + 2) (radialEuler ((l : ℝ) - 1) B)) x⟫ :=
      hw'C.continuous.inner (contDiff_meridionalTest l (contDiff_radialEuler _ hτAC)
        (contDiff_radialEuler _ hEB)).continuous
    have hG1 : ∫ x in Metric.ball (0 : ℝ^3) R, ⟪meridionalTest l A' B' x,
        meridionalTest l (tractionRadial l R A P) (tractionPolar l R A B P) x⟫ =
        -μ * (∫ x in Metric.ball (0 : ℝ^3) R, ⟪meridionalTest l A' B' x, meridionalTest l A B x⟫) -
          (∫ x in Metric.ball (0 : ℝ^3) R, ⟪meridionalTest l A' B' x, meridionalTest l
            (radialEuler ((l : ℝ) + 4) (fun t ↦ radialEuler ((l : ℝ) + 1) A t - P t))
            (radialEuler ((l : ℝ) + 2) (radialEuler ((l : ℝ) - 1) B)) x⟫) / R ^ 2 := by
      rw [div_eq_inv_mul, ← integral_const_mul, ← integral_const_mul,
        ← integral_sub ((hball hc1).const_mul _) ((hball hc2).const_mul _)]
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      simp only [hΦ, inner_sub_right, real_inner_smul_right]
    have hJ : ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
        ∂[j] (fun y ↦ meridionalTest l A' B' y i) x * ∂[j] (fun y ↦ meridionalTest l A B y i) x =
        ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
        ∂[j] (fun y ↦ meridionalTest l A B y i) x * ∂[j] (fun y ↦ meridionalTest l A' B' y i) x :=
      integral_congr_ae (ae_of_all _ fun x ↦ Finset.sum_congr rfl fun i _ ↦
        Finset.sum_congr rfl fun j _ ↦ mul_comm _ _)
    rw [hG1, hp0, hJ] at hGw
    simp only [real_inner_comm (meridionalTest l A B _) (meridionalTest l A' B' _)] at hGw
    have hsum := integral_inner_euler_add_eq hR hl hA' hB' hτAC hEB
    have hkey : (∫ x in Metric.ball (0 : ℝ^3) R, ⟪meridionalTest l A' B' x, meridionalTest l
        (radialEuler ((l : ℝ) + 4) (fun t ↦ radialEuler ((l : ℝ) + 1) A t - P t))
        (radialEuler ((l : ℝ) + 2) (radialEuler ((l : ℝ) - 1) B)) x⟫) +
        (∫ x in Metric.ball (0 : ℝ^3) R, ⟪meridionalTest l (radialEuler ((l : ℝ) + 1) A')
          (radialEuler ((l : ℝ) - 1) B') x, meridionalTest l
          (fun t ↦ radialEuler ((l : ℝ) + 1) A t - P t) (radialEuler ((l : ℝ) - 1) B) x⟫) = 0 := by
      have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR.ne'
      field_simp at hGu hGZ hGw
      linear_combination -hGw + hGZ - hGu
    rw [hkey] at hsum
    exact (mul_eq_zero.mp hsum.symm).resolve_left (by positivity)
  -- two tests with independent traces
  have h1 := hbdry (A' := fun _ ↦ 0) (B' := fun _ ↦ 1) contDiff_const contDiff_const
    (fun s ↦ by simp)
  set c₀ : ℝ := -(2 * l) / ((l : ℝ) + 3) with hc₀
  have hc₀ne : c₀ ≠ 0 := div_ne_zero (by linarith) (by linarith)
  have h2 := hbdry (A' := fun _ ↦ c₀) (B' := fun s ↦ s) contDiff_const contDiff_id
    (fun s ↦ by
      simp only [deriv_const', mul_zero, zero_add, deriv_id'', mul_one, hc₀]
      field_simp
      ring)
  set X := radialProfile l (fun t ↦ radialEuler ((l : ℝ) + 1) A t - P t)
    (radialEuler ((l : ℝ) - 1) B) R with hX
  set Y := polarProfile l (radialEuler ((l : ℝ) - 1) B) R with hY
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  simp only [radialProfile, polarProfile, Nat.add_sub_cancel, mul_zero, zero_add,
    mul_one] at h1 h2
  have hRm : 0 < R ^ m := pow_pos hR m
  have hX0 : X = 0 := (mul_eq_zero.mp (by linear_combination h2 - R ^ 2 * h1 :
    vectorHarmonicNormSq (m + 1) 0 * c₀ * R ^ (m + 2) * X = 0)).resolve_left
      (mul_ne_zero (mul_ne_zero hN0.ne' hc₀ne) (by positivity))
  rw [hX0, mul_zero, zero_add] at h1
  have hY0 : Y = 0 := (mul_eq_zero.mp h1).resolve_left (mul_ne_zero hN1.ne' hRm.ne')
  simp only [hY, polarProfile, Nat.add_sub_cancel] at hY0
  have hB0 := (mul_eq_zero.mp hY0).resolve_left hRm.ne'
  simp only [hX, radialProfile, Nat.add_sub_cancel, hB0, mul_zero, add_zero] at hX0
  exact ⟨(mul_eq_zero.mp hX0).resolve_left (pow_pos hR _).ne', hB0⟩

end PDE.Fluid.Stokes.Ball
