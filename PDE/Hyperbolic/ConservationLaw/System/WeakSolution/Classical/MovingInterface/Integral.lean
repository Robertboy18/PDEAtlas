/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Weak
public import PDE.Hyperbolic.ConservationLaw.Scalar.Shock.Interface
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import PDE.Hyperbolic.ConservationLaw.Scalar.Shock.Jump

/-!
# The vector weak integral across a moving interface

Join two globally C¹ fields along an arbitrary C¹ graph `x = s(t)` using
`Set.piecewise`, assigning the left field on the graph. The classical equations
are required only on the open side where each field is used. The vector weak
integral is the graph integral of `s'(t) • [u] - [flux(u)]`, with right-minus-left
jumps. Local integrability and the one-sided traces are derived.

The proof applies the scalar moving-graph divergence formula to each
coordinate of the state and its flux.

The computation is (16)-(17) of Evans, §11.1.1, the vector form of (8)-(9) in §3.4.1(a).
Evans writes jumps left minus right, `[[u]] = u_l - u_r`. Once the unit normal and arc length
of the graph are written in terms of `s'(t)`, his interface coefficient `[[F(u)]] - σ[[u]]` is
`jump` in right-minus-left form.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1.1, equations (12)-(17); §3.4.1(a), equations (8)-(9).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace PDE.Common
open scoped Distributions Topology

attribute [local instance] Classical.propDecidable

namespace PDE.Hyperbolic.ConservationLaw.System.MovingInterface

open Scalar.Shock (interface rightRegion)

variable {m : ℕ} {flux : ℝ^m → ℝ^m} {s : ℝ → ℝ} {uL uR : ℝ^2 → ℝ^m}

/-- The left branch evaluated on the graph is the spatial left trace. -/
theorem tendsto_piecewise_left (hL : Continuous uL) (t : ℝ) :
    Tendsto (fun x ↦ (rightRegion s).piecewise uR uL !₂[t, x]) (𝓝[<] s t)
      (𝓝 (uL (interface s t))) := by
  have hc : Continuous (fun x ↦ uL !₂[t, x]) := by fun_prop
  apply Tendsto.congr' _ hc.continuousAt.continuousWithinAt
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp [Set.piecewise, rightRegion, not_lt.mpr hx.le]

/-- The right branch evaluated on the graph is the spatial right trace. -/
theorem tendsto_piecewise_right (hR : Continuous uR) (t : ℝ) :
    Tendsto (fun x ↦ (rightRegion s).piecewise uR uL !₂[t, x]) (𝓝[>] s t)
      (𝓝 (uR (interface s t))) := by
  have hc : Continuous (fun x ↦ uR !₂[t, x]) := by fun_prop
  apply Tendsto.congr' _ hc.continuousAt.continuousWithinAt
  filter_upwards [self_mem_nhdsWithin] with x hx
  change s t < x at hx
  simp [Set.piecewise, rightRegion, hx]

/-- Joining locally integrable vector fields along a continuous graph preserves
local integrability. -/
theorem locallyIntegrable_piecewise (hs : Continuous s)
    (hL : LocallyIntegrable uL) (hR : LocallyIntegrable uR) :
    LocallyIntegrable ((rightRegion s).piecewise uR uL) := by
  have heq : (rightRegion s).piecewise uR uL =
      fun p ↦ uL p + (rightRegion s).indicator (fun q ↦ uR q - uL q) p := by
    funext p
    by_cases hp : p ∈ rightRegion s <;> simp [hp]
  rw [heq]
  exact hL.add ((hR.sub hL).indicator (Scalar.Shock.isOpen_rightRegion hs).measurableSet)

/-- A continuous flux of the joined continuous branches is locally integrable. -/
theorem locallyIntegrable_flux_piecewise (hflux : Continuous flux) (hs : Continuous s)
    (hL : Continuous uL) (hR : Continuous uR) :
    LocallyIntegrable (fun p ↦ flux ((rightRegion s).piecewise uR uL p)) := by
  have heq : (fun p ↦ flux ((rightRegion s).piecewise uR uL p)) =
      (rightRegion s).piecewise (flux ∘ uR) (flux ∘ uL) := by
    funext p
    by_cases hp : p ∈ rightRegion s <;> simp [hp]
  rw [heq]
  exact locallyIntegrable_piecewise hs (hflux.comp hL).locallyIntegrable
    (hflux.comp hR).locallyIntegrable

/-- The vector coefficient of the singular interface contribution, with
right-minus-left jumps. Its sign matches the system weak integral. -/
def jump (flux : ℝ^m → ℝ^m) (s : ℝ → ℝ) (uL uR : ℝ^2 → ℝ^m) (t : ℝ) : ℝ^m :=
  deriv s t • (uR (interface s t) - uL (interface s t)) -
    (flux (uR (interface s t)) - flux (uL (interface s t)))

/-- The jump coefficient is continuous for continuous branches and a C¹ graph. -/
theorem continuous_jump (hflux : Continuous flux) (hs : ContDiff ℝ 1 s)
    (hL : Continuous uL) (hR : Continuous uR) :
    Continuous (jump flux s uL uR) := by
  have hc := Scalar.Shock.continuous_interface hs.continuous
  exact (hs.continuous_deriv_one.smul ((hR.comp hc).sub (hL.comp hc))).sub
    ((hflux.comp (hR.comp hc)).sub (hflux.comp (hL.comp hc)))

/-- Vanishing of the interface coefficient is precisely the
Rankine–Hugoniot condition at the traces and graph velocity. -/
theorem jump_eq_zero_iff {t : ℝ} :
    jump flux s uL uR t = 0 ↔
      RankineHugoniot flux (uL (interface s t)) (uR (interface s t)) (deriv s t) :=
  sub_eq_zero.trans eq_comm

/-- A compactly supported test makes the vector interface contribution integrable. -/
theorem integrable_smul_jump (hflux : Continuous flux) (hs : ContDiff ℝ 1 s) (hL : Continuous uL)
    (hR : Continuous uR) (φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) :
    Integrable (fun t ↦ φ (interface s t) • jump flux s uL uR t) :=
  ((φ.continuous.comp (Scalar.Shock.continuous_interface hs.continuous)).smul
    (continuous_jump hflux hs hL hR)).integrable_of_hasCompactSupport
      (Scalar.Shock.hasCompactSupport_interface_comp φ.hasCompactSupport s).smul_right

/-- The weak integral of the joined vector field is exactly the tested jump
when the branches satisfy the conservation law on their respective open sides. -/
theorem integral_weakIntegrand_piecewise (hflux : ContDiff ℝ 1 flux) (hs : ContDiff ℝ 1 s)
    (hL : ContDiff ℝ 1 uL) (hR : ContDiff ℝ 1 uR)
    (hPL : ∀ p, p 1 < s (p 0) → fluxResidual flux uL p = 0)
    (hPR : ∀ p, s (p 0) < p 1 → fluxResidual flux uR p = 0) (φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) :
    (∫ p, weakIntegrand flux ((rightRegion s).piecewise uR uL) φ p) =
      ∫ t, φ (interface s t) • jump flux s uL uR t := by
  have hi := integrable_weakIntegrand
    ((locallyIntegrable_piecewise hs.continuous hL.continuous.locallyIntegrable
      hR.continuous.locallyIntegrable).locallyIntegrableOn univ)
    ((locallyIntegrable_flux_piecewise hflux.continuous hs.continuous
      hL.continuous hR.continuous).locallyIntegrableOn univ) φ
  have hj := integrable_smul_jump hflux.continuous hs hL.continuous hR.continuous φ
  refine PiLp.ext fun i ↦ ?_
  rw [eval_integral_piLp (fun j ↦ hi.eval_piLp j) i, eval_integral_piLp (fun j ↦ hj.eval_piLp j) i]
  have hbulk {u : ℝ^2 → ℝ^m} (hu : ContDiff ℝ 1 u) {p : ℝ^2} (hp : fluxResidual flux u p = 0) :
      (∂[0] (fun q ↦ u q i)) p + (∂[1] (fun q ↦ flux (u q) i)) p = 0 := by
    simpa [fluxResidual, partialDeriv_apply 0 i (hu.differentiable_one p),
      partialDeriv_apply 1 i ((hflux.comp hu).differentiable_one p)] using
      congrArg (fun v : ℝ^m ↦ v i) hp
  have hcoord {u : ℝ^2 → ℝ^m} (hu : ContDiff ℝ 1 u) :
      ContDiff ℝ 1 (fun p ↦ u p i) := by fun_prop
  have hscalar := Scalar.Shock.integral_profile_divergence_of_bulk_eq_zero hs
    (hcoord hL) (hcoord hR) (hcoord (hflux.comp hL)) (hcoord (hflux.comp hR))
    (fun p hp ↦ hbulk hL (hPL p hp)) (fun p hp ↦ hbulk hR (hPR p hp)) φ
  convert hscalar using 1
  · apply integral_congr_ae
    filter_upwards [] with p
    by_cases hp : s (p 0) < p 1 <;>
      simp [weakIntegrand, rightRegion, Set.piecewise, Scalar.Shock.profile, hp, mul_comm]
  · apply integral_congr_ae
    filter_upwards [] with t
    simp [jump, mul_comm]

end PDE.Hyperbolic.ConservationLaw.System.MovingInterface
