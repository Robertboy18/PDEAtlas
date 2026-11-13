/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.WeakRepresentation
public import PDE.Elliptic.Regularity.Boundary.Rellich.WeakNormalSurface

/-!
# Green representation with an L² boundary density

For a weakly harmonic `H¹` corrector `φ` that is continuous on the closure with boundary values
`Φ(y - x)`, `exists_green_representation_with_surfaceDensity_of_corrector` gives one boundary
density `q` in `L²` with `u(x) = ∫ q u dS - ∫ G Δu`, where `G = greenKernel x φ`, for every `u` of
class `C²` up to the boundary and continuous on the closure;
`exists_green_representation_with_surfaceDensity_of_local_graph` also constructs the corrector. The
density represents the negative outward weak normal derivative of `G`, so this is Evans's formula
(28) in §2.2.4(a) with `q` in place of `-∂G/∂ν`, and its boundary term enters with a positive sign.

The construction first subtracts a smooth lifting from the corrector. This
gives a zero-trace H¹ function with L² Laplacian, to which the weak boundary
estimate applies. Agreement of the Sobolev trace with continuous boundary
values then turns the trace pairing into an ordinary surface integral.
No classical boundary gradient of the corrector is assumed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(a), the definition of Green's function for the region
  `U` and the representation formula (28), p. 34.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PotentialTheory.GreenFunction.Domain

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Boundary SobolevSpace.Trace.C1
open SobolevSpace.Boundary.Geometry.SurfaceMeasure
open scoped Sobolev

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [hΩ : C1ExtensionAtlas (m + 1) Ω]

/-- A continuous harmonic H¹ corrector gives one surface L² density for all
classical test functions. Both the boundary and volume integrals are integrable. -/
theorem exists_green_representation_with_surfaceDensity_of_corrector
    (hn : 2 ≤ m + 1) (hgraph : HasC1GraphBoundary Ω)
    {x : ℝ^(m + 1)} (hx : x ∈ Ω)
    (U : H¹(Ω)) {φ : ℝ^(m + 1) → ℝ}
    (hrep : baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] φ)
    (hcφ : ContinuousOn φ (closure Ω))
    (hbφ : EqOn φ (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω))
    (hweak : ∀ t : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) U)
        (derivCoordCLM i t)) = 0) :
    ∃ q : BoundaryL2 (Ω := Ω),
      ∀ (u : ℝ^(m + 1) → ℝ) (hu : ContDiffUpToBoundary 2 u Ω),
        ContinuousOn u (closure Ω) →
        Integrable (fun y ↦ q y * u y) (surfaceMeasure Ω) ∧
        IntegrableOn (fun y ↦ greenKernel x φ y * PDE.laplacian u y) Ω ∧
        u x = (∫ y, q y * u y ∂surfaceMeasure Ω) -
          ∫ y in Ω, greenKernel x φ y * PDE.laplacian u y := by
  obtain ⟨w, f, hwf, hformula⟩ :=
    exists_weakGreen_representation_of_corrector hn hgraph hx U hrep hcφ hbφ hweak
  obtain ⟨q, hq⟩ := exists_surfaceDensity_weakNormalTrace_of_H10 hgraph w f hwf
  obtain ⟨P⟩ := SobolevSpace.Approximation.UpToBoundary.exists_inwardPartition
    hΩ.isOpen hΩ.bounded (hasC1Boundary_of_local_graph hgraph)
  refine ⟨q, ?_⟩
  intro u hu hcu
  let hu₁ := hu.of_le (show 1 ≤ 2 by omega)
  let V : H¹(Ω) := hu₁.toWkpSpaceOn hΩ.isOpen hΩ.bounded 2
  have htrace : (boundaryValue (traceClass V) : ℝ^(m + 1) → ℝ)
      =ᵐ[surfaceMeasure Ω] u := by
    change (trace V : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω] u
    exact trace_eq_ae_of_continuousOn P V hcu
      (hu₁.toWkpSpaceOn_base_ae hΩ.isOpen hΩ.bounded 2)
  have hprod : (fun y ↦ q y * (boundaryValue (traceClass V)) y)
      =ᵐ[surfaceMeasure Ω] fun y ↦ q y * u y :=
    htrace.mono fun y hy ↦ congrArg (q y * ·) hy
  refine ⟨((Lp.memLp q).integrable_mul
    (Lp.memLp (boundaryValue (traceClass V)))).congr hprod, (hformula u hu hcu).1, ?_⟩
  calc
    u x = weakNormalTrace (w : H¹(Ω)) f hwf (traceClass V) -
        ∫ y in Ω, greenKernel x φ y * PDE.laplacian u y := (hformula u hu hcu).2
    _ = (∫ y, q y * u y ∂surfaceMeasure Ω) -
        ∫ y in Ω, greenKernel x φ y * PDE.laplacian u y := by
      rw [hq, integral_congr_ae hprod]

omit hΩ in
/-- Bounded open C¹ graph geometry constructs the corrector and the surface
density in Green's formula. The same density works for every classical test. -/
theorem exists_green_representation_with_surfaceDensity_of_local_graph
    (hn : 2 ≤ m + 1) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω) {x : ℝ^(m + 1)} (hx : x ∈ Ω) :
    letI := hgraph.c1ExtensionAtlas hopen hbounded
    ∃ φ : ℝ^(m + 1) → ℝ,
      LaplacianEquation.IsHarmonicPDE (m + 1) φ Ω ∧
      ContinuousOn φ (closure Ω) ∧
      EqOn φ (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω) ∧
      ∃ q : BoundaryL2 (Ω := Ω),
        ∀ (u : ℝ^(m + 1) → ℝ) (hu : ContDiffUpToBoundary 2 u Ω),
          ContinuousOn u (closure Ω) →
          Integrable (fun y ↦ q y * u y) (surfaceMeasure Ω) ∧
          IntegrableOn (fun y ↦ greenKernel x φ y * PDE.laplacian u y) Ω ∧
          u x = (∫ y, q y * u y ∂surfaceMeasure Ω) -
            ∫ y in Ω, greenKernel x φ y * PDE.laplacian u y := by
  let atlas := hgraph.c1ExtensionAtlas hopen hbounded
  obtain ⟨U, φ, hrep, hh, hc, hb, hw⟩ :=
    exists_harmonic_corrector_of_local_graph hn hopen hbounded hgraph hx
  exact ⟨φ, hh, hc, hb,
    exists_green_representation_with_surfaceDensity_of_corrector
      hn hgraph hx U hrep hc hb hw⟩

end PotentialTheory.GreenFunction.Domain
