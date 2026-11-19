/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Module.Normalize
public import PDE.Analysis.Integration.EuclideanBall
public import PDE.FDeriv.Operators
import PDE.Analysis.Calculus.EuclideanBall
import PDE.EnergyMethods.Dirichlet.Basic

/-!
# Green identities on Euclidean balls

We derive Green's first and second identities on positive-radius Euclidean balls from
the ball divergence theorem. The boundary term uses the outward unit normal
`normalize (x - c)`.

The smoothness assumptions are global, which avoids any calculus on manifolds with boundary.

## Main results

* `ballOutwardNormalDerivative`: the normal derivative `∂v/∂ν = ∇v · (x - c)/‖x - c‖` on the
  sphere, extended by `0` at the center.
* `greens_first_identity_ball`: `∫_B u Δv = -∫_B ∇u · ∇v + ∫_{∂B} u ∂v/∂ν` for `u ∈ C¹`,
  `v ∈ C²`.
* `greens_second_identity_ball`: `∫_B (u Δv - v Δu) = ∫_{∂B} (u ∂v/∂ν - v ∂u/∂ν)` for
  `u, v ∈ C²`.

Both identities are obtained by applying the divergence theorem on the ball to the vector
fields `u ∇v` and `u ∇v - v ∇u`. They are Green's formulas (ii) and (iii) of Evans,
Appendix C.2, Theorem 3, on a ball, with `u` only `C¹` in the first.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix C.2, Theorem 1 (Gauss–Green theorem) and
  Theorem 3 (Green's formulas), pp. 711-712.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

open PDE (laplacian)

namespace Energy

open MeasureTheory
open PDE.Analysis

variable {n : ℕ}

/-- Outward normal derivative on a sphere centered at `c`, extended by zero at `c`. -/
noncomputable def ballOutwardNormalDerivative
    (c : ℝ^n) (v : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  ∑ i : Fin n,
    (∂[i] v) x * (NormedSpace.normalize (x - c)) i

/-- The coordinate definition of the spherical normal derivative is the
Euclidean inner product of the gradient with the outward radial direction.

Both sides are total at the center because `NormedSpace.normalize 0 = 0`. -/
theorem ballOutwardNormalDerivative_eq_inner_gradient
    (c : ℝ^n) (v : ℝ^n → ℝ) (x : ℝ^n) :
    ballOutwardNormalDerivative c v x =
      inner ℝ (∇ v x) (NormedSpace.normalize (x - c)) := by
  rw [inner_gradient_left]
  exact
    (PDE.fderiv_apply_eq_sum_partialDeriv_mul
      v x (NormedSpace.normalize (x - c))).symm

private theorem continuous_partialDeriv
    {f : ℝ^n → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin n) :
    Continuous (fun x ↦ (∂[i] f) x) :=
  (PDE.contDiff_partialDeriv_of_succ (m := 0) (i := i) hf).continuous

private theorem continuous_laplacian
    {f : ℝ^n → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (laplacian f) := by
  unfold laplacian
  apply continuous_finsetSum
  intro i _
  exact continuous_partialDeriv
    (PDE.contDiff_partialDeriv_of_succ (m := 1) (i := i) hf) i

private theorem continuous_gradientPairing
    {u v : ℝ^n → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    Continuous
      (fun x ↦ ∑ i : Fin n, (∂[i] u) x * (∂[i] v) x) := by
  apply continuous_finsetSum
  intro i _
  exact (continuous_partialDeriv hu i).mul (continuous_partialDeriv hv i)

private theorem integrableOn_ball_of_continuous
    {f : ℝ^n → ℝ} (hf : Continuous f) (c : ℝ^n) (r : ℝ) :
    IntegrableOn f (Metric.ball c r) volume :=
  (hf.continuousOn.integrableOn_compact
    (isCompact_closedBall c r)).mono_set Metric.ball_subset_closedBall

/-- Green's first identity on a positive-radius Euclidean ball. -/
theorem greens_first_identity_ball
    [Fact (0 < n)]
    (c : ℝ^n) {r : ℝ} (hr : 0 < r)
    {u v : ℝ^n → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v) :
    ballIntegral n (fun x ↦ u x * laplacian v x) c r =
      -ballIntegral n
          (fun x ↦ ∑ i : Fin n,
            (∂[i] u) x * (∂[i] v) x)
          c r +
        sphereIntegral n
          (fun x ↦ u x * ballOutwardNormalDerivative c v x)
          c r := by
  let F : Fin n → ℝ^n → ℝ :=
    fun i x ↦ u x * (∂[i] v) x
  have hF : ∀ i, ContDiff ℝ 1 (F i) := by
    intro i
    exact hu.mul (PDE.contDiff_partialDeriv_of_succ (m := 1) (i := i) hv)
  have hGauss :=
    ballIntegral_divergence_eq_sphereIntegral_normal_flux F hF c hr
  have hdiv :
      (fun x ↦ ∑ i : Fin n, (∂[i] (F i)) x) =
        fun x ↦
          (∑ i : Fin n, (∂[i] u) x * (∂[i] v) x) +
            u x * laplacian v x := by
    funext x
    have huDiff : DifferentiableAt ℝ u x :=
      (hu.differentiable (by norm_num)).differentiableAt
    have hvDiff :
        ∀ i, DifferentiableAt ℝ (fun y ↦ (∂[i] v) y) x := by
      intro i
      exact
        ((PDE.contDiff_partialDeriv_of_succ (m := 1) (i := i) hv).differentiable
          (by norm_num)).differentiableAt
    change ∇·
      (fun y ↦ WithLp.toLp 2 fun i ↦ u y * (∂[i] v) y) x = _
    exact divergence_of_u_grad_v (n := n) (u := u) (v := v) huDiff hvDiff
  have hflux :
      (fun x ↦
        ∑ i : Fin n, F i x * (NormedSpace.normalize (x - c)) i) =
        fun x ↦ u x * ballOutwardNormalDerivative c v x := by
    funext x
    simp only [F, ballOutwardNormalDerivative, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdiv, hflux] at hGauss
  have hGrad :
      IntegrableOn
        (fun x ↦ ∑ i : Fin n,
          (∂[i] u) x * (∂[i] v) x)
        (Metric.ball c r) volume :=
    integrableOn_ball_of_continuous
      (continuous_gradientPairing hu (hv.of_le (by norm_num))) c r
  have hLap :
      IntegrableOn (fun x ↦ u x * laplacian v x)
        (Metric.ball c r) volume :=
    integrableOn_ball_of_continuous
      (hu.continuous.mul (continuous_laplacian hv)) c r
  unfold ballIntegral at hGauss ⊢
  rw [integral_add hGrad hLap] at hGauss
  linarith

/-- Green's second identity on a positive-radius Euclidean ball. -/
theorem greens_second_identity_ball
    [Fact (0 < n)]
    (c : ℝ^n) {r : ℝ} (hr : 0 < r)
    {u v : ℝ^n → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    ballIntegral n
        (fun x ↦ u x * laplacian v x - v x * laplacian u x)
        c r =
      sphereIntegral n
        (fun x ↦
          u x * ballOutwardNormalDerivative c v x -
            v x * ballOutwardNormalDerivative c u x)
        c r := by
  let F : Fin n → ℝ^n → ℝ :=
    fun i x ↦
      u x * (∂[i] v) x - v x * (∂[i] u) x
  have hF : ∀ i, ContDiff ℝ 1 (F i) := by
    intro i
    exact
      ((hu.of_le (by norm_num)).mul
        (PDE.contDiff_partialDeriv_of_succ (m := 1) (i := i) hv)).sub
      ((hv.of_le (by norm_num)).mul
        (PDE.contDiff_partialDeriv_of_succ (m := 1) (i := i) hu))
  have hGauss :=
    ballIntegral_divergence_eq_sphereIntegral_normal_flux F hF c hr
  have hdiv :
      (fun x ↦ ∑ i : Fin n, (∂[i] (F i)) x) =
        fun x ↦ u x * laplacian v x - v x * laplacian u x := by
    funext x
    have huDiff : DifferentiableAt ℝ u x :=
      (hu.differentiable (by norm_num)).differentiableAt
    have hvDiff : DifferentiableAt ℝ v x :=
      (hv.differentiable (by norm_num)).differentiableAt
    have hDu :
        ∀ i, DifferentiableAt ℝ (fun y ↦ (∂[i] u) y) x := by
      intro i
      exact
        ((PDE.contDiff_partialDeriv_of_succ (m := 1) (i := i) hu).differentiable
          (by norm_num)).differentiableAt
    have hDv :
        ∀ i, DifferentiableAt ℝ (fun y ↦ (∂[i] v) y) x := by
      intro i
      exact
        ((PDE.contDiff_partialDeriv_of_succ (m := 1) (i := i) hv).differentiable
          (by norm_num)).differentiableAt
    change ∇·
      (fun y ↦ WithLp.toLp 2 fun i ↦
        u y * (∂[i] v) y - v y * (∂[i] u) y) x = _
    exact
      divergence_u_grad_v_sub_v_grad_u (n := n) (u := u) (v := v)
        huDiff hvDiff hDu hDv
  have hflux :
      (fun x ↦
        ∑ i : Fin n, F i x * (NormedSpace.normalize (x - c)) i) =
        fun x ↦
          u x * ballOutwardNormalDerivative c v x -
            v x * ballOutwardNormalDerivative c u x := by
    funext x
    simp only [F, ballOutwardNormalDerivative, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [hdiv, hflux] using hGauss

end Energy
