/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.ConservationLaw.Viscosity.GaussianTransport.Profile
public import PDE.Hyperbolic.ConservationLaw.System.VanishingViscosity.Limit

/-!
# Common-data vanishing viscosity for the transported Gaussian

The vanishing-viscosity criterion with common initial data,
`entropySolution_of_vanishingViscosity_commonData`, applies to linear transport with
any real speed `c` as a one-component system. It gives the initial weak equation and
every convex entropy inequality for the transported Gaussian
(`isEntropyWeakSolution_limit`).
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common PDE.Hyperbolic.ConservationLaw
open scoped Topology

namespace PDE.Examples.ConservationLaw.GaussianTransport

/-- Scalar values as the one-component Euclidean state. -/
def embed : ℝ →L[ℝ] ℝ^1 :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single 0 1)

/-- The full linear transport flux. -/
def flux (c : ℝ) (z : ℝ^1) : ℝ^1 := c • z

/-- The viscous state. -/
def viscous (c ε : ℝ) : ℝ^2 → ℝ^1 := embed ∘ scalar c ε

/-- The initial datum is independent of both viscosity and transport speed. -/
def datum (x : ℝ) : ℝ^1 := embed (Real.exp (-x ^ 2))

/-- The inviscid Gaussian translated with speed `c`. -/
def limit (c : ℝ) (p : ℝ^2) : ℝ^1 :=
  embed (Real.exp (-((p 1 - c * p 0) ^ 2)))

/-- The viscous state is bounded by `1` for `t ≥ 0`. -/
theorem norm_viscous_le {ε : ℝ} (hε : 0 ≤ ε) (c : ℝ) {p : ℝ^2} (hp : 0 ≤ p 0) :
    ‖viscous c ε p‖ ≤ 1 := by
  simpa [viscous, embed, norm_smul] using norm_scalar_le hε c hp

/-- The viscous state solves the viscous transport system for `t ≥ 0`. -/
theorem viscous_equation {ε : ℝ} (hε : 0 ≤ ε) (c : ℝ) {p : ℝ^2} (hp : 0 ≤ p 0) :
    System.fluxResidual (flux c) (viscous c ε) p =
      ε • (∂[1] (∂[1] (viscous c ε))) p := by
  have hs := denominator_pos hε hp
  have hu : ContDiffAt ℝ 2 (scalar c ε) p := (contDiffAt_scalar c ε p hs).of_le (by simp)
  have hd := hu.differentiableAt (by norm_num)
  change (∂[0] (embed ∘ scalar c ε)) p +
    (∂[1] (fun q ↦ c • (embed ∘ scalar c ε) q)) p =
      ε • (∂[1] (∂[1] (embed ∘ scalar c ε))) p
  rw [partialDeriv_const_smul, embed.partialDeriv_comp 0 hd,
    embed.partialDeriv_comp 1 hd, embed.secondPartialDeriv_comp 1 1 hu,
    ← map_smul, ← map_add, ← map_smul]
  exact congrArg embed (scalar_equation c ε p hs)

/-- The transported Gaussian is an entropy weak solution of the initial-value problem for
linear transport. -/
theorem isEntropyWeakSolution_limit (c : ℝ) :
    IsWeakInitialValueSolution (flux c) datum (limit c) ∧
      System.IsEntropyWeakSolution (flux c) forwardHalfSpace (limit c) := by
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hc (ε : ℝ) (hε : 0 ≤ ε) (p : ℝ^2) (hp : 0 ≤ p 0) :
      ContDiffAt ℝ (⊤ : ℕ∞) (viscous c ε) p :=
    embed.contDiff.contDiffAt.comp p (contDiffAt_scalar c ε p (denominator_pos hε hp))
  have h := System.entropySolution_of_vanishingViscosity_commonData
    (u := viscous c) (v := limit c) (ε := id) (M := 1) (g := datum)
    (by unfold flux; fun_prop) (hpos.mono fun _ hε ↦ hε.le) nhdsWithin_le_nhds
    (hpos.mono fun ε hε p hp ↦
      ((hc ε hε.le p hp.le).of_le (by simp)).contDiffWithinAt)
    (hpos.mono fun ε hε p hp ↦ (hc ε hε.le p hp).continuousAt.continuousWithinAt)
    (hpos.mono fun ε hε p hp ↦ viscous_equation hε.le c hp.le)
    (hpos.mono fun ε hε ↦ by
      filter_upwards [ae_restrict_mem forwardHalfSpace.isOpen.measurableSet] with p hp
      exact norm_viscous_le hε.le c hp.le)
    (Eventually.of_forall fun ε x ↦ by
      change embed (scalar c ε !₂[0, x]) = _
      rw [scalar_initial]
      rfl)
    (Eventually.of_forall fun p ↦
      (embed.continuous.tendsto _).comp (tendsto_scalar c p))
  exact h.2.2

/-- The common datum is nonzero at the origin. -/
theorem datum_origin : datum 0 = EuclideanSpace.single 0 1 := by
  simp [datum, embed]

end PDE.Examples.ConservationLaw.GaussianTransport
