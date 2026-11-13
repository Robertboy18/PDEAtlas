/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.Operators
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import PDE.FDeriv.Calculus

/-!
# Pressure recovery in incompressible flow

The pressure Poisson residual `pressurePoissonResidual` is obtained by taking the spatial
divergence of the Euler momentum equation.

For an incompressible velocity field, the time-derivative term has zero
spatial divergence. The differentiated momentum balance therefore gives the pressure Poisson
equation

```text
-Δp = div((u · ∇)u) - div f.
```

One recovery theorem takes the differentiated momentum balance and the
vanishing time-divergence term as explicit hypotheses. A second derives that
balance from a momentum equation holding throughout a neighborhood, under
the `C²` regularity needed to differentiate it. The vector-Laplacian results
also show that viscosity contributes no pressure source for a locally
incompressible `C³` velocity, so the same Poisson equation governs the
Navier–Stokes pressure.

Everything here is pointwise: each theorem is a statement at one spacetime
point `x`, with regularity and the momentum equation assumed on a neighborhood
of `x` where differentiation requires it.

## Main results

* `spatialDivergence_spatialVectorLaplacian_eq_spatialLaplacian_spatialDivergence`:
  `div Δu = Δ div u` for a componentwise `C³` velocity, so the viscous term is
  divergence free wherever `u` is locally incompressible.
* `spatialDivergence_timeDerivative_eq_zero_of_eventually_divergenceFreeAt`:
  `div ∂ₜu = 0` for a `C²` velocity that is incompressible near the point.
* `divergence_balance_of_eventually_momentum_eq`: the spatial divergence of a
  momentum equation valid on a neighborhood.
* `pressurePoissonResidual_eq_zero_of_eventually_momentum_eq`: the pressure
  Poisson equation from a locally valid Euler momentum equation together with
  local incompressibility.
* `pressurePoissonResidual_eq_zero_of_eventually_momentum_eq_add`: the same
  conclusion when a differentiable divergence-free term (such as `ν Δu`) is
  added to the force.

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 1, for the pressure Poisson
  equation obtained from the divergence of the momentum equation.
  <https://doi.org/10.1017/CBO9780511613203>
* A. J. Chorin and J. E. Marsden, *A Mathematical Introduction to Fluid Mechanics*, Texts in Applied
  Mathematics, Springer, 1993, Chapter 1 (The Equations of Motion), for the Euler and Navier–Stokes
  momentum equations.
  <https://doi.org/10.1007/978-1-4612-0883-9>
-/

@[expose] public section

open PDE (partialDeriv spatialGradient)

namespace IncompressibleFlow

open EuclideanSpace
open scoped Topology

set_option linter.missingDocs true

noncomputable section

/-- The spatial divergence of the pressure gradient is the spatial
Laplacian. -/
theorem spatialDivergence_spatialGradient_eq_spatialLaplacian (n : ℕ)
    (p : ℝ^(n + 1) → ℝ) (x : ℝ^(n + 1)) :
  spatialDivergence n (spatialGradient p) x =
      spatialLaplacian n p x := by
  simp only [spatialDivergence_apply, PDE.spatialGradient_apply,
    spatialLaplacian_apply]

/-- Every component of the spatial vector Laplacian of a componentwise `C³`
velocity is differentiable. -/
theorem spatialVectorLaplacian_component_differentiableAt
    (n : ℕ) (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1))
    (hu : ∀ i : Fin n, ContDiffAt ℝ 3 (fun y ↦ u y i) x)
    (i : Fin n) :
    DifferentiableAt ℝ (fun y ↦ spatialVectorLaplacian n u y i) x := by
  simp only [spatialVectorLaplacian_apply, spatialLaplacian_apply]
  apply DifferentiableAt.fun_sum
  intro j _hj
  exact
    (PDE.contDiffAt_partialDeriv (m := 1)
      (PDE.contDiffAt_partialDeriv (m := 2) (hu i) j.succ)
      j.succ).differentiableAt (by norm_num)

/-- For a componentwise `C³` velocity field, spatial divergence commutes
with the spatial vector Laplacian. -/
theorem spatialDivergence_spatialVectorLaplacian_eq_spatialLaplacian_spatialDivergence
    (n : ℕ) (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1))
    (hu : ∀ i : Fin n, ContDiffAt ℝ 3 (fun y ↦ u y i) x) :
    spatialDivergence n (spatialVectorLaplacian n u) x =
      spatialLaplacian n (spatialDivergence n u) x := by
  have hu2 : ∀ᶠ y in 𝓝 x, ∀ i, ContDiffAt ℝ 2 (fun z ↦ u z i) y :=
    ((contDiffAt_piLp (p := (2 : ENNReal))).2 hu).eventually (by norm_num) |>.mono
      fun y hy i ↦ (((contDiffAt_piLp (p := (2 : ENNReal))).1 hy) i).of_le (by norm_num)
  have hd2 (i j k : Fin n) : DifferentiableAt ℝ
      (fun y ↦ (∂[k.succ] (fun z ↦ (∂[j.succ] (fun w ↦ u w i)) z)) y) x :=
    (PDE.contDiffAt_partialDeriv (m := 1) (PDE.contDiffAt_partialDeriv (m := 2) (hu i) j.succ)
      k.succ).differentiableAt (by norm_num)
  -- `∂ⱼ div u = ∑ᵢ ∂ⱼ ∂ᵢ uᵢ` near `x`, and third derivatives commute at `x`
  have hdivNear (j : Fin n) : (fun y ↦ (∂[j.succ] (spatialDivergence n u)) y) =ᶠ[𝓝 x]
      fun y ↦ ∑ i, (∂[j.succ] (fun z ↦ (∂[i.succ] (fun w ↦ u w i)) z)) y := by
    filter_upwards [hu2] with y hy
    rw [funext (spatialDivergence_apply n u)]
    exact PDE.partialDeriv_sum _ (fun i _ ↦
      (PDE.contDiffAt_partialDeriv (m := 1) (hy i) i.succ).differentiableAt (by norm_num)) _
  have hcomm (i j : Fin n) :
      (∂[i.succ] (fun y ↦ (∂[j.succ] (fun z ↦ (∂[j.succ] (fun w ↦ u w i)) z)) y)) x =
        (∂[j.succ] (fun y ↦ (∂[j.succ] (fun z ↦ (∂[i.succ] (fun w ↦ u w i)) z)) y)) x :=
    (PDE.partialDeriv_partialDeriv_comm_at i.succ j.succ
      (PDE.contDiffAt_partialDeriv (m := 2) (hu i) j.succ)).trans
      (PDE.partialDeriv_congr_nhds j.succ
        (hu2.mono fun y hy ↦ PDE.partialDeriv_partialDeriv_comm_at i.succ j.succ (hy i)))
  simp only [spatialDivergence_apply, spatialVectorLaplacian_apply, spatialLaplacian_apply]
  rw [Finset.sum_congr rfl fun i _ ↦ PDE.partialDeriv_sum _ (fun j _ ↦ hd2 i j j) _,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [PDE.partialDeriv_congr_nhds j.succ (hdivNear j),
    PDE.partialDeriv_sum _ (fun i _ ↦ hd2 i i j) _]
  exact Finset.sum_congr rfl fun i _ ↦ hcomm i j

/-- A componentwise `C³` velocity that is incompressible near `x` has a
spatial vector Laplacian with zero spatial divergence at `x`. -/
theorem spatialDivergence_spatialVectorLaplacian_eq_zero_of_eventually_divergenceFreeAt
    (n : ℕ) (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1))
    (hu : ∀ i : Fin n, ContDiffAt ℝ 3 (fun y ↦ u y i) x)
    (hdiv : ∀ᶠ y in 𝓝 x, DivergenceFreeAt u y) :
    spatialDivergence n (spatialVectorLaplacian n u) x = 0 := by
  have hdivFunction : spatialDivergence n u =ᶠ[𝓝 x] fun _ ↦ 0 := hdiv.mono fun y hy ↦ hy
  rw [spatialDivergence_spatialVectorLaplacian_eq_spatialLaplacian_spatialDivergence n u x hu,
    spatialLaplacian_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [PDE.partialDeriv_second_congr_nhds i.succ hdivFunction]
  simp

/-- A globally incompressible componentwise `C³` velocity has a spatial
vector Laplacian with zero spatial divergence. -/
theorem spatialDivergence_spatialVectorLaplacian_eq_zero_of_divergenceFree
    (n : ℕ) (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1))
    (hu : ∀ i : Fin n, ContDiffAt ℝ 3 (fun y ↦ u y i) x)
    (hdiv : DivergenceFree u) :
    spatialDivergence n (spatialVectorLaplacian n u) x = 0 :=
  spatialDivergence_spatialVectorLaplacian_eq_zero_of_eventually_divergenceFreeAt n u x hu
    (.of_forall fun y ↦ hdiv.at y)

/-- For a `C²` velocity that is incompressible near `x`, the spatial
divergence of its time derivative vanishes at `x`. -/
theorem spatialDivergence_timeDerivative_eq_zero_of_eventually_divergenceFreeAt
    (n : ℕ) (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1))
    (hu : ∀ i : Fin n, ContDiffAt ℝ 2 (fun y ↦ u y i) x)
    (hdiv : ∀ᶠ y in 𝓝 x, DivergenceFreeAt u y) :
    spatialDivergence n (timeDerivative n u) x = 0 := by
  have hcomm (i : Fin n) : (∂[i.succ] (fun y ↦ (∂[0] (fun z ↦ u z i)) y)) x =
      (∂[0] (fun y ↦ (∂[i.succ] (fun z ↦ u z i)) y)) x :=
    PDE.partialDeriv_partialDeriv_comm_at i.succ 0 (hu i)
  have hdivFunction : (fun y ↦ ∑ i : Fin n, (∂[i.succ] (fun z ↦ u z i)) y) =ᶠ[𝓝 x]
      fun _ ↦ 0 := hdiv.mono fun y hy ↦ hy
  rw [spatialDivergence_apply]
  simp_rw [timeDerivative_apply, hcomm]
  rw [← PDE.partialDeriv_sum _ (fun i _ ↦
      (PDE.contDiffAt_partialDeriv (m := 1) (hu i) i.succ).differentiableAt (by norm_num)),
    PDE.partialDeriv_congr_nhds 0 hdivFunction]
  simp

/-- A globally divergence-free `C²` velocity has a time derivative with zero
spatial divergence. -/
theorem spatialDivergence_timeDerivative_eq_zero_of_divergenceFree
    (n : ℕ) (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1))
    (hu : ∀ i : Fin n, ContDiffAt ℝ 2 (fun y ↦ u y i) x)
    (hdiv : DivergenceFree u) :
    spatialDivergence n (timeDerivative n u) x = 0 :=
  spatialDivergence_timeDerivative_eq_zero_of_eventually_divergenceFreeAt n u x hu
    (.of_forall fun y ↦ hdiv.at y)

/-- Source in the pressure Poisson equation
`div((u · ∇)u) - div f`. -/
def pressurePoissonSource (n : ℕ) (u : ℝ^(n + 1) → ℝ^n)
    (f : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) : ℝ :=
  spatialDivergence n (convectiveDerivative n u u) x -
    spatialDivergence n f x

/-- Pressure Poisson residual `-Δp - div((u · ∇)u) + div f`. -/
def pressurePoissonResidual (n : ℕ) (u : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) → ℝ) (f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) : ℝ :=
  -spatialLaplacian n p x - pressurePoissonSource n u f x

/-- A momentum equation with an additional differentiable vector term on its
right-hand side may be differentiated spatially near `x`.

The conclusion keeps the divergence of that distinguished term on the left.
This form applies directly to viscosity without requiring an independent
regularity hypothesis on the forcing: the local equation itself identifies
the force with a differentiable expression near `x`. -/
theorem divergence_balance_of_eventually_momentum_eq_add
    (n : ℕ) (u : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) → ℝ)
    (g f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1))
    (hu : ∀ i : Fin n, ContDiffAt ℝ 2 (fun y ↦ u y i) x)
    (hp : ContDiffAt ℝ 2 p x)
    (hg : ∀ i : Fin n, DifferentiableAt ℝ (fun y ↦ g y i) x)
    (hmomentum : ∀ᶠ y in 𝓝 x,
      timeDerivative n u y + convectiveDerivative n u u y +
          spatialGradient p y =
        g y + f y) :
    spatialDivergence n (timeDerivative n u) x +
          spatialDivergence n (convectiveDerivative n u u) x +
          spatialLaplacian n p x -
          spatialDivergence n g x =
      spatialDivergence n f x := by
  have hcomponent (i : Fin n) :
      (∂[i.succ] (fun y ↦ timeDerivative n u y i)) x +
          (∂[i.succ] (fun y ↦ convectiveDerivative n u u y i)) x +
          (∂[i.succ] (fun y ↦ spatialGradient p y i)) x -
          (∂[i.succ] (fun y ↦ g y i)) x =
        (∂[i.succ] (fun y ↦ f y i)) x := by
    have ha : DifferentiableAt ℝ (fun y ↦ timeDerivative n u y i) x := by
      simpa only [timeDerivative_apply] using
        (PDE.contDiffAt_partialDeriv (m := 1) (hu i) 0).differentiableAt (by norm_num)
    have hb : DifferentiableAt ℝ (fun y ↦ convectiveDerivative n u u y i) x := by
      simp only [convectiveDerivative_apply]
      exact DifferentiableAt.fun_sum fun j _ ↦ ((hu j).differentiableAt (by norm_num)).mul
        ((PDE.contDiffAt_partialDeriv (m := 1) (hu i) j.succ).differentiableAt (by norm_num))
    have hc : DifferentiableAt ℝ (fun y ↦ spatialGradient p y i) x := by
      simpa only [PDE.spatialGradient_apply] using
        (PDE.contDiffAt_partialDeriv (m := 1) hp i.succ).differentiableAt (by norm_num)
    rw [← PDE.partialDeriv_add ha hb, ← PDE.partialDeriv_add (ha.fun_add hb) hc,
      ← PDE.partialDeriv_sub ((ha.fun_add hb).fun_add hc) (hg i)]
    refine PDE.partialDeriv_congr_nhds i.succ (hmomentum.mono fun y hy ↦ ?_)
    have hyi := congrArg (· i) hy
    simp only [PiLp.add_apply] at hyi
    linarith
  rw [← spatialDivergence_spatialGradient_eq_spatialLaplacian n p x]
  simp_rw [spatialDivergence_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ hcomponent i

/-- A momentum equation valid near `x` may be differentiated spatially when
velocity and pressure are `C²` germs. The local equation itself identifies
the force with the differentiable left-hand side near `x`. -/
theorem divergence_balance_of_eventually_momentum_eq
    (n : ℕ) (u : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) → ℝ) (f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1))
    (hu : ∀ i : Fin n, ContDiffAt ℝ 2 (fun y ↦ u y i) x)
    (hp : ContDiffAt ℝ 2 p x)
    (hmomentum : ∀ᶠ y in 𝓝 x,
      timeDerivative n u y + convectiveDerivative n u u y +
          spatialGradient p y =
        f y) :
    spatialDivergence n (timeDerivative n u) x +
          spatialDivergence n (convectiveDerivative n u u) x +
          spatialLaplacian n p x =
      spatialDivergence n f x := by
  have hbalance :=
    divergence_balance_of_eventually_momentum_eq_add n u p
      (fun _ : ℝ^(n + 1) ↦ (0 : ℝ^n)) f x hu hp
      (fun _ ↦ differentiableAt_const (c := (0 : ℝ)))
      (by
        filter_upwards [hmomentum] with y hy
        simpa using hy)
  simpa [spatialDivergence_apply] using hbalance

/-- A zero pressure residual is exactly the pressure Poisson equation. -/
theorem pressurePoissonResidual_eq_zero_iff (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (f : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) :
    pressurePoissonResidual n u p f x = 0 ↔
      -spatialLaplacian n p x = pressurePoissonSource n u f x :=
  sub_eq_zero

/--
The differentiated Euler momentum balance yields the pressure Poisson
equation once the spatial divergence of `∂ₜu` is known to vanish.

The first hypothesis is the divergence of
`∂ₜu + (u · ∇)u + ∇p = f`. Keeping it explicit avoids differentiating a
pointwise equality without the regularity and neighborhood hypotheses that
such a step requires.
-/
theorem pressurePoissonResidual_eq_zero_of_divergence_balance
    (n : ℕ) (u : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) → ℝ) (f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1))
    (hbalance :
      spatialDivergence n (timeDerivative n u) x +
          spatialDivergence n (convectiveDerivative n u u) x +
          spatialLaplacian n p x =
        spatialDivergence n f x)
    (htime :
      spatialDivergence n (timeDerivative n u) x = 0) :
    pressurePoissonResidual n u p f x = 0 := by
  unfold pressurePoissonResidual pressurePoissonSource
  linarith

/-- The differentiated Euler momentum balance and local incompressibility
imply the pressure Poisson equation. -/
theorem pressurePoissonResidual_eq_zero_of_divergence_balance_of_eventually_divergenceFreeAt
    (n : ℕ) (u : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) → ℝ) (f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1))
    (hu : ∀ i : Fin n, ContDiffAt ℝ 2 (fun y ↦ u y i) x)
    (hdiv : ∀ᶠ y in 𝓝 x, DivergenceFreeAt u y)
    (hbalance :
      spatialDivergence n (timeDerivative n u) x +
          spatialDivergence n (convectiveDerivative n u u) x +
          spatialLaplacian n p x =
        spatialDivergence n f x) :
    pressurePoissonResidual n u p f x = 0 :=
  pressurePoissonResidual_eq_zero_of_divergence_balance n u p f x hbalance
    (spatialDivergence_timeDerivative_eq_zero_of_eventually_divergenceFreeAt n u x hu hdiv)

/-- A locally valid momentum equation with a differentiable,
divergence-free term added to the force has the same pressure Poisson
equation as the corresponding Euler momentum equation. -/
theorem pressurePoissonResidual_eq_zero_of_eventually_momentum_eq_add
    (n : ℕ) (u : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) → ℝ)
    (g f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1))
    (hu : ∀ i : Fin n, ContDiffAt ℝ 2 (fun y ↦ u y i) x)
    (hp : ContDiffAt ℝ 2 p x)
    (hg : ∀ i : Fin n, DifferentiableAt ℝ (fun y ↦ g y i) x)
    (hdivg : spatialDivergence n g x = 0)
    (hdivu : ∀ᶠ y in 𝓝 x, DivergenceFreeAt u y)
    (hmomentum : ∀ᶠ y in 𝓝 x,
      timeDerivative n u y + convectiveDerivative n u u y +
          spatialGradient p y =
        g y + f y) :
    pressurePoissonResidual n u p f x = 0 := by
  apply
    pressurePoissonResidual_eq_zero_of_divergence_balance_of_eventually_divergenceFreeAt
      n u p f x hu hdivu
  have hbalance :=
    divergence_balance_of_eventually_momentum_eq_add
      n u p g f x hu hp hg hmomentum
  linarith

/-- A locally valid, sufficiently regular Euler momentum equation together
with local incompressibility implies the pressure Poisson equation. -/
theorem pressurePoissonResidual_eq_zero_of_eventually_momentum_eq
    (n : ℕ) (u : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) → ℝ) (f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1))
    (hu : ∀ i : Fin n, ContDiffAt ℝ 2 (fun y ↦ u y i) x)
    (hp : ContDiffAt ℝ 2 p x)
    (hdiv : ∀ᶠ y in 𝓝 x, DivergenceFreeAt u y)
    (hmomentum : ∀ᶠ y in 𝓝 x,
      timeDerivative n u y + convectiveDerivative n u u y +
          spatialGradient p y =
        f y) :
    pressurePoissonResidual n u p f x = 0 := by
  apply
    pressurePoissonResidual_eq_zero_of_divergence_balance_of_eventually_divergenceFreeAt
      n u p f x hu hdiv
  exact divergence_balance_of_eventually_momentum_eq n u p f x hu hp hmomentum

end

end IncompressibleFlow
