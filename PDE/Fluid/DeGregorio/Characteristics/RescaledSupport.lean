/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.DynamicRescaling
public import PDE.Hyperbolic.Transport.Support
import PDE.Fluid.DeGregorio.Characteristics.Local

/-!
# Fixed support for the rescaled De Gregorio transport equation

At `a = 1` the transport velocity is `U(x,t) + cl(t) x`, and the stretching
coefficient is `cw(t) + U_x(x,t)`. A jointly `C¹` velocity makes the latter
coefficient continuous. With continuous rates, a uniform global spatial Lipschitz
bound for the transport velocity, and zero transport velocity at `±L`, support initially
in `[-L,L]` remains there on the whole finite time interval.

The proof constructs backward characteristics by Picard iteration and proves that
they do not cross the stationary boundaries, using uniqueness for the characteristic ODE.
-/

@[expose] public section

noncomputable section

open Set

namespace DeGregorio

/-- The rescaled transport equation preserves support in `[-L,L]` throughout
a finite time interval. Global spatial Lipschitz control permits linear growth of
the transport velocity and does not restrict the interval length. -/
theorem rescaled_vorticity_support_subset
    {fields : Fields} {cl cw : ℝ → ℝ} {t₀ T L : ℝ}
    (hu : ContDiff ℝ 1 (Function.uncurry fields.velocity))
    (hcl : Continuous cl) (hcw : Continuous cw)
    (K : NNReal)
    (hK : ∀ t ∈ Icc t₀ T,
      LipschitzWith K (fun x ↦ fields.velocity x t + cl t * x))
    (hleft : ∀ t ∈ Icc t₀ T, fields.velocity (-L) t + cl t * (-L) = 0)
    (hright : ∀ t ∈ Icc t₀ T, fields.velocity L t + cl t * L = 0)
    (hregularity : HasClassicalRegularityOn fields (Icc t₀ T))
    (htransport : SatisfiesRescaledTransportEquationOn 1 fields cl cw (Icc t₀ T))
    (hinitial : Function.support (fun x ↦ fields.vorticity x t₀) ⊆ Icc (-L) L) :
    ∀ t ∈ Icc t₀ T,
      Function.support (fun x ↦ fields.vorticity x t) ⊆ Icc (-L) L := by
  apply TransportEquation.transport_support_subset_Icc
    (b := fun x t ↦ fields.velocity x t + cl t * x)
    (c := fun x t ↦ cw t + deriv (fun y ↦ fields.velocity y t) x)
    (hu.continuous.add ((hcl.comp continuous_snd).mul continuous_fst))
    ((hcw.comp continuous_snd).add (continuous_spatial_deriv_of_contDiff hu))
    K hK hleft hright
    (fun _ _ ht ↦ hregularity.vorticity_differentiableAt ht) _ hinitial
  intro x t ht
  simpa only [SatisfiesRescaledTransportEquationOn, one_mul, add_comm] using
    htransport (x := x) ht

end DeGregorio
