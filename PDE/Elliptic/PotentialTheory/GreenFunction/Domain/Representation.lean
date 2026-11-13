/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Kernel
public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.NewtonRepresentation

/-!
# Green representation from a classical harmonic corrector

For `u` of class `C²` up to the boundary of a bounded open domain with C¹ graph boundary and a
harmonic corrector `φ` with boundary values `Φ(y - x)`, `representation_of_corrector` proves
`u(x) = -∫ u ∂G/∂ν dS - ∫ G Δu` for the Green kernel `G = greenKernel x φ`, with both integrands
integrable. This is Evans's formula (28) in §2.2.4(a); Theorem 12 follows by substituting the data
of problem (29) (`dirichlet_representation`). The corrector is explicit data, with classical
regularity up to the boundary sufficient for its normal trace; correctors are constructed in
`Domain.Corrector`.

As in Evans, we add Green's second identity for `u` and the corrector
(`SobolevSpace.Boundary.Flux.green_second_identity_of_contDiffUpToBoundary`), his (27), to the
Newton representation `newton_representation`, his (25). Harmonicity of the corrector removes its
volume term, and its boundary values cancel the normal derivative of `u`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(a), the representation formula (25), the corrector
  problem (26), (27), the definition of Green's function for the region `U` and (28), p. 34.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public noncomputable section

open PDE (laplacian)

namespace PotentialTheory.GreenFunction.Domain

open Filter Set MeasureTheory SobolevSpace SobolevSpace.Boundary
open SobolevSpace.Boundary.Flux SobolevSpace.Trace.C1 Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : C1ExtensionAtlas (m + 1) Ω]

/-- A classical harmonic corrector yields the signed Green representation.
Its existence and closure regularity are explicit hypotheses, while the pole
identity, boundary cancellation, and all integrability are conclusions. -/
theorem representation_of_corrector
    (hn : 2 ≤ m + 1) (hgraph : HasC1GraphBoundary Ω)
    {u φ : ℝ^(m + 1) → ℝ} (hu : ContDiffUpToBoundary 2 u Ω)
    (hcu : ContinuousOn u (closure Ω)) {x : ℝ^(m + 1)} (hx : x ∈ Ω)
    (hφ : ContDiffUpToBoundary 2 φ Ω) (hcφ : ContinuousOn φ (closure Ω))
    (hhar : ∀ y ∈ Ω, laplacian φ y = 0)
    (hboundary : EqOn φ (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω)) :
    IntegrableOn (fun y ↦ greenKernel x φ y * laplacian u y) Ω ∧
      Integrable (fun y ↦ u y * normalFlux (Ω := Ω)
        (greenKernelGradient x (hφ.of_le (show 1 ≤ 2 by omega))) y) (surfaceMeasure Ω) ∧
      u x = -(∫ y, u y * normalFlux (Ω := Ω)
        (greenKernelGradient x (hφ.of_le (show 1 ≤ 2 by omega))) y ∂surfaceMeasure Ω) -
        ∫ y in Ω, greenKernel x φ y * laplacian u y := by
  let K := fun y ↦ fundamentalSolution (m + 1) (y - x)
  let Du := (hu.of_le (show 1 ≤ 2 by omega)).completedGradient
  let Dφ := (hφ.of_le (show 1 ≤ 2 by omega)).completedGradient
  let DG := fun y ↦ ∇ K y - Dφ y
  let BN := fun y ↦ K y * normalFlux (Ω := Ω) Du y -
    u y * normalFlux (Ω := Ω) (∇ K) y
  let BC := fun y ↦ u y * normalFlux (Ω := Ω) Dφ y -
    φ y * normalFlux (Ω := Ω) Du y
  obtain ⟨hni, hnbi, hne⟩ := newton_representation hn hgraph hu hcu hx
  obtain ⟨hci, hcbi, hce⟩ :=
    green_second_identity_of_contDiffUpToBoundary hgraph hu hcu hφ hcφ
  have hvolc : (fun y ↦ u y * laplacian φ y - φ y * laplacian u y)
      =ᵐ[volume.restrict Ω] fun y ↦ -(φ y * laplacian u y) := by
    filter_upwards [ae_restrict_mem hΩ.isOpen.measurableSet] with y hy
    rw [hhar y hy, mul_zero, zero_sub]
  have hφi : IntegrableOn (fun y ↦ φ y * laplacian u y) Ω :=
    integrable_fun_neg_iff.mp (hci.congr hvolc)
  have hvolg : (fun y ↦ K y * laplacian u y - φ y * laplacian u y)
      =ᵐ[volume.restrict Ω] fun y ↦ (K y - φ y) * laplacian u y :=
    Eventually.of_forall fun _ ↦ (sub_mul _ _ _).symm
  have hgi : IntegrableOn (fun y ↦ (K y - φ y) * laplacian u y) Ω :=
    (hni.sub hφi).congr hvolg
  have hsurface : (fun y ↦ -(BN y + BC y)) =ᵐ[surfaceMeasure Ω]
      fun y ↦ u y * normalFlux (Ω := Ω) DG y := by
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with y hy
    dsimp only [BN, BC, DG]
    simp only [normalFlux_eq_inner _ hy, inner_sub_left, hboundary hy]
    ring
  have hbi : Integrable (fun y ↦ u y * normalFlux (Ω := Ω) DG y) (surfaceMeasure Ω) :=
    (hnbi.add hcbi).fun_neg.congr hsurface
  refine ⟨hgi, hbi, ?_⟩
  change u x = -(∫ y, u y * normalFlux (Ω := Ω) DG y ∂surfaceMeasure Ω) -
    ∫ y in Ω, (K y - φ y) * laplacian u y
  rw [integral_congr_ae hvolc, integral_neg] at hce
  have hgvol := integral_congr_ae hvolg
  rw [integral_sub hni hφi] at hgvol
  have hgbound := integral_congr_ae hsurface
  rw [integral_neg, integral_add hnbi hcbi] at hgbound
  change -(∫ y in Ω, φ y * laplacian u y) = ∫ y, BC y ∂surfaceMeasure Ω at hce
  change u x = (∫ y, BN y ∂surfaceMeasure Ω) - ∫ y in Ω, K y * laplacian u y at hne
  linarith

end PotentialTheory.GreenFunction.Domain
