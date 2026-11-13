/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.FirstIntegral
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Reduction.VectorField
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Lifting a scalar connection to the physical profile

The graph's differential invariance turns a scalar orbit into an
orbit of the integrated vector equation. Its two state limits follow by
continuity of the same graph. The first integral then supplies the
second-order viscous equation and both zero-velocity limits.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw.System

/-- Lift a connection of the reduced scalar field through its graph.
The range condition concerns precisely the part of the graph where its
derived differential invariance holds. -/
theorem isViscousProfile_profileGraph_of_scalar {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hflux : Differentiable ℝ flux) (q uR : ℝ^m) (e : ℝ^m ≃L[ℝ] (Fin m → ℝ)) (k : Fin m)
    {φ : (Option (Fin m) → ℝ) → (Option (Fin m) → ℝ)} (hφ : ContDiff ℝ 2 φ) (speed μ a b : ℝ)
    (I : Set ℝ)
    (hinvariant : ∀ s ∈ I, fderiv ℝ (profileGraph q e k φ) (s, μ)
      (reducedProfileField flux q e k φ (s, μ), 0) =
      flux (profileGraph q e k φ (s, μ)) - flux q - speed • (profileGraph q e k φ (s, μ) - q))
    (ha : profileGraph q e k φ (a, μ) = q) (hb : profileGraph q e k φ (b, μ) = uR)
    (hRH : RankineHugoniot flux q uR speed) {x : ℝ → ℝ} (hx : ContDiff ℝ 2 x) (hxI : ∀ t, x t ∈ I)
    (hode : ∀ t, HasDerivAt x (reducedProfileField flux q e k φ (x t, μ)) t)
    (hleft : Tendsto x atBot (𝓝 a)) (hright : Tendsto x atTop (𝓝 b)) :
    IsViscousProfile flux q uR speed (fun t ↦ profileGraph q e k φ (x t, μ)) := by
  have hgraph := contDiff_profileGraph q e k hφ
  apply isViscousProfile_of_first_order hflux (hgraph.comp (hx.prodMk contDiff_const)) _ _ _ hRH
  · intro t
    have hd := (hgraph.differentiable (by norm_num) (x t, μ)).hasFDerivAt.comp_hasDerivAt t
      ((hode t).prodMk (hasDerivAt_const t μ))
    simpa only [Function.comp_def, hinvariant (x t) (hxI t)] using hd
  · simpa only [ha] using hgraph.continuous.continuousAt.tendsto.comp
      (hleft.prodMk_nhds (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ μ) atBot (𝓝 μ)))
  · simpa only [hb] using hgraph.continuous.continuousAt.tendsto.comp
      (hright.prodMk_nhds (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ μ) atTop (𝓝 μ)))

end PDE.Hyperbolic.ConservationLaw.System
