/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev
public import PDE.Fluid.DeGregorio.Characteristics.SupportEvolution

/-!
# Rescaled support preservation from vorticity Sobolev bounds

The concrete Biot–Savart relation converts a uniform bound on the input
`L²` norms of `ω` and `ω_x` into the global velocity-gradient bound needed for
backward characteristic construction. The support theorem then gives
preservation of `[-L,L]` when the rescaled transport field vanishes at both endpoints.

Vorticity is assumed compactly supported and `C²` on every time slice so that
the classical Hilbert derivative commutation applies. The uniform Sobolev bound and
the regular coupled evolution are hypotheses.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace DeGregorio

/-- Uniform vorticity `H¹` bounds imply the global velocity-gradient
bound through the concrete Biot–Savart relation. -/
theorem SatisfiesBiotSavartOn.nnnorm_spatial_deriv_le_of_vorticity_norm_bound
    {fields : Fields} {times : Set ℝ}
    (hbiot : SatisfiesBiotSavartOn fields times)
    (hu : ContDiff ℝ 1 (Function.uncurry fields.velocity))
    (homega : ∀ t ∈ times, ContDiff ℝ 2 (fun x ↦ fields.vorticity x t))
    (hsupp : ∀ t ∈ times, HasCompactSupport (fun x ↦ fields.vorticity x t))
    (M : NNReal)
    (hH1 : ∀ t ∈ times,
      (eLpNorm (fun x ↦ fields.vorticity x t) 2 volume).toReal +
        (eLpNorm (deriv (fun x ↦ fields.vorticity x t)) 2 volume).toReal ≤ M) :
    ∀ x t, t ∈ times → ‖deriv (fun y ↦ fields.velocity y t) x‖₊ ≤ M := by
  intro x t ht
  have hslice : ContDiff ℝ 1 (fun y ↦ fields.velocity y t) :=
    hu.comp (contDiff_id.prodMk contDiff_const)
  apply NNReal.coe_le_coe.mp
  simpa only [coe_nnnorm] using ((hbiot ht).norm_le_eLpNorm_add_deriv
    (hslice.continuous_deriv le_rfl) (homega t ht) (hsupp t ht) x).trans (hH1 t ht)

/-- Rescaled vorticity stays in `[-L,L]` under a uniform bound
`‖ω‖₂ + ‖ω_x‖₂ ≤ M`. The bound on `U_x` comes from the Biot–Savart relation. -/
theorem rescaled_vorticity_support_subset_of_vorticity_norm_bound
    {fields : Fields} {cl cw : ℝ → ℝ} {t₀ T L : ℝ}
    (hu : ContDiff ℝ 1 (Function.uncurry fields.velocity))
    (hcl : Continuous cl) (hcw : Continuous cw)
    (homega : ∀ t ∈ Icc t₀ T, ContDiff ℝ 2 (fun x ↦ fields.vorticity x t))
    (hsupp : ∀ t ∈ Icc t₀ T, HasCompactSupport (fun x ↦ fields.vorticity x t))
    (M : NNReal)
    (hH1 : ∀ t ∈ Icc t₀ T,
      (eLpNorm (fun x ↦ fields.vorticity x t) 2 volume).toReal +
        (eLpNorm (deriv (fun x ↦ fields.vorticity x t)) 2 volume).toReal ≤ M)
    (hbiot : SatisfiesBiotSavartOn fields (Icc t₀ T))
    (hleft : ∀ t ∈ Icc t₀ T, fields.velocity (-L) t + cl t * (-L) = 0)
    (hright : ∀ t ∈ Icc t₀ T, fields.velocity L t + cl t * L = 0)
    (hregularity : HasClassicalRegularityOn fields (Icc t₀ T))
    (htransport : SatisfiesRescaledTransportEquationOn 1 fields cl cw (Icc t₀ T))
    (hinitial : Function.support (fun x ↦ fields.vorticity x t₀) ⊆ Icc (-L) L) :
    ∀ t ∈ Icc t₀ T,
      Function.support (fun x ↦ fields.vorticity x t) ⊆ Icc (-L) L :=
  rescaled_vorticity_support_subset_of_deriv_bound hu hcl hcw M
    (hbiot.nnnorm_spatial_deriv_le_of_vorticity_norm_bound hu homega hsupp M hH1)
    hleft hright hregularity htransport hinitial

end DeGregorio
