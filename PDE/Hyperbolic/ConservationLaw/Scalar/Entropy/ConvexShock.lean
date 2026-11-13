/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.ConvexShock
public import PDE.Hyperbolic.ConservationLaw.Scalar.PlanarShock
import Mathlib.Analysis.Convex.Deriv
import CAS.ExactTactic

/-!
# Convex entropy inequalities for scalar shocks

For a convex scalar flux, a decreasing Rankine–Hugoniot jump satisfies every
smooth convex entropy inequality. Only convexity on the interval between the
two states is needed.

The mean value theorem gives an intermediate state `k` with `f'(k) = speed`.
The function

`q(r) - speed * η(r) - η'(k) * (f(r) - speed * r)`

has derivative `(η'(r) - η'(k)) * (f'(r) - f'(k)) ≥ 0`, since both derivatives
are monotone. Rankine–Hugoniot cancels its last term between the endpoints,
leaving precisely the entropy jump inequality. The planar-shock weak formula
then gives the distributional inequality.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.1, equations (12) and (17); §11.4.2, Example 1; §11.4.3,
  equations (36)-(38).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.Scalar

open PDE.Common Set TopologicalSpace

/-- A decreasing Rankine–Hugoniot jump for a differentiable convex flux
dissipates every smooth entropy convex between the two states.

Flux differentiability and both convexity assumptions are local to the
closed state interval. Equal states are allowed and give equality. -/
theorem RankineHugoniot.entropy_jump_le_of_convex {flux : ℝ → ℝ} {uL uR speed : ℝ}
    (hRH : RankineHugoniot flux uL uR speed) (hLR : uR ≤ uL) (hflux : ConvexOn ℝ (Icc uR uL) flux)
    (hdiff : ∀ r ∈ Icc uR uL, DifferentiableAt ℝ flux r) (E : EntropyPair (fun r ↦ deriv flux r))
    (hη : ConvexOn ℝ (Icc uR uL) E.η) :
    E.q uR - E.q uL ≤ speed * (E.η uR - E.η uL) := by
  obtain hLR | rfl := hLR.lt_or_eq
  · have hfluxCont : ContinuousOn flux (Icc uR uL) :=
      fun r hr ↦ (hdiff r hr).continuousAt.continuousWithinAt
    obtain ⟨k, hk, hkSlope⟩ := exists_deriv_eq_slope' flux hLR hfluxCont
      (fun r hr ↦ (hdiff r (Ioo_subset_Icc_self hr)).differentiableWithinAt)
    have hkSpeed : deriv flux k = speed := by
      rw [hkSlope, ← rankineHugoniotSpeed_eq_slope]
      exact ((rankineHugoniot_iff_speed_eq hLR.ne).mp hRH).symm
    have hkClosed : k ∈ Icc uR uL := Ioo_subset_Icc_self hk
    have hfluxMono := hflux.monotoneOn_deriv hdiff
    have hηMono := hη.monotoneOn_deriv
      (fun r _ ↦ E.eta_contDiff.contDiffAt.differentiableAt_one (x := r))
    let g : ℝ → ℝ := fun r ↦ E.q r - speed * E.η r - deriv E.η k * (flux r - speed * r)
    have hg' (r : ℝ) (hr : r ∈ Icc uR uL) :
        HasDerivAt g ((deriv E.η r - deriv E.η k) * (deriv flux r - speed)) r := by
      convert (E.entropyFlux_contDiff.contDiffAt.differentiableAt_one.hasDerivAt.sub
          (E.eta_contDiff.contDiffAt.differentiableAt_one.hasDerivAt.const_mul speed)).sub
          (((hdiff r hr).hasDerivAt.sub ((hasDerivAt_id r).const_mul speed)).const_mul
            (deriv E.η k)) using 1 <;> try rfl
      rw [E.hq r]
      cas
    have hgMono : MonotoneOn g (Icc uR uL) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc uR uL)
        (fun r hr ↦ (hg' r hr).continuousAt.continuousWithinAt)
        (fun r hr ↦ (hg' r (interior_subset hr)).hasDerivWithinAt) ?_
      intro r hr
      have hrClosed : r ∈ Icc uR uL := interior_subset hr
      rw [← hkSpeed]
      obtain hrk | hkr := le_total r k
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hηMono hrClosed hkClosed hrk))
          (sub_nonpos.mpr (hfluxMono hrClosed hkClosed hrk))
      · exact mul_nonneg (sub_nonneg.mpr (hηMono hkClosed hrClosed hkr))
          (sub_nonneg.mpr (hfluxMono hkClosed hrClosed hkr))
    have hends := hgMono (left_mem_Icc.mpr hLR.le) (right_mem_Icc.mpr hLR.le) hLR.le
    have hfluxJump : flux uR - speed * uR = flux uL - speed * uL := by
      dsimp [RankineHugoniot] at hRH
      nlinarith [hRH]
    dsimp [g] at hends
    rw [hfluxJump] at hends
    linarith
  · simp

/-- A decreasing shock for a convex flux satisfies the distributional
inequality for any smooth entropy convex on its state interval. -/
theorem RankineHugoniot.satisfiesEntropyInequalityFor_planarShock_of_convex {flux : ℝ → ℝ}
    {uL uR speed : ℝ} (hRH : RankineHugoniot flux uL uR speed) (hLR : uR ≤ uL)
    (hflux : ConvexOn ℝ (Icc uR uL) flux) (hdiff : ∀ r ∈ Icc uR uL, DifferentiableAt ℝ flux r)
    (E : EntropyPair (fun r ↦ deriv flux r)) (hη : ConvexOn ℝ (Icc uR uL) E.η) :
    SatisfiesEntropyInequalityFor (⊤ : Opens ℝ^2) (planarShock uL uR speed) E :=
  satisfiesEntropyInequalityFor_planarShock_iff.mpr
    (hRH.entropy_jump_le_of_convex hLR hflux hdiff E hη)

/-- A decreasing Rankine–Hugoniot shock for a `C¹` flux convex between its
states is a weak solution satisfying every smooth convex entropy inequality. -/
theorem RankineHugoniot.isEntropyWeakSolution_planarShock_of_convex {flux : ℝ → ℝ} {uL uR speed : ℝ}
    (hRH : RankineHugoniot flux uL uR speed) (hLR : uR ≤ uL) (hflux : ConvexOn ℝ (Icc uR uL) flux)
    (hreg : ContDiff ℝ 1 flux) :
    IsEntropyWeakSolution flux (⊤ : Opens ℝ^2) (planarShock uL uR speed) := by
  refine ⟨hRH.isWeakSolution_planarShock, fun E hη ↦ ?_⟩
  exact hRH.satisfiesEntropyInequalityFor_planarShock_of_convex hLR hflux
    (fun r _ ↦ hreg.contDiffAt.differentiableAt_one (x := r)) E
    (hη.subset (subset_univ _) (convex_Icc uR uL))

end PDE.Hyperbolic.ConservationLaw.Scalar
