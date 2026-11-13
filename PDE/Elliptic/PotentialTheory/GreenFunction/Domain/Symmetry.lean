/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.KernelReciprocity
public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Representation

/-!
# Symmetry of the domain Green function

For poles `x, y` in a bounded open domain with C¹ graph boundary and harmonic correctors `φx`, `φy`
with boundary values `Φ(· - x)`, `Φ(· - y)` and classical regularity up to the boundary,
`symmetry_of_correctors` proves `Φ(y - x) - φx(y) = Φ(x - y) - φy(x)`, that is, `G(x, y) = G(y, x)`.
This is Evans's §2.2.4(a), Theorem 13; the case `x = y` is trivial. No symmetry or limiting boundary
identity is assumed.

## How it works

Evans applies Green's identity to `G(x, ·)` and `G(y, ·)` on `U` minus two small balls, his (31),
and evaluates the limits at the poles. We instead apply `representation_of_corrector` to the
corrector `φy` with pole `x` and to `φx` with pole `y`; both correctors are harmonic, so the volume
terms vanish and `φy(x)`, `φx(y)` become boundary integrals. On the boundary the correctors equal
the kernels, so the difference of the two integrals is the antisymmetric flux of the correctors,
which vanishes by Green's second identity
(`SobolevSpace.Boundary.Flux.green_second_identity_of_contDiffUpToBoundary`), minus the
antisymmetric flux of the kernels, which vanishes by `integral_kernel_cross_normalFlux_eq_zero`.
Evenness of the fundamental solution (`PotentialTheory.fundamentalSolution_eq_of_norm_eq`) turns
`φy(x) = φx(y)` into `G(x, y) = G(y, x)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(a), the definition of Green's function for the region
  `U`, p. 34, and Theorem 13 (Symmetry of Green's function) and its proof, (31), pp. 35-36.
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

/-- Two classical harmonic correctors with the prescribed fundamental-solution
boundary values give symmetric Green values at interior poles. For equal poles the kernel
cross term vanishes identically. -/
theorem symmetry_of_correctors
    (hn : 2 ≤ m + 1) (hgraph : HasC1GraphBoundary Ω)
    {x y : ℝ^(m + 1)} (hx : x ∈ Ω) (hy : y ∈ Ω)
    {φx φy : ℝ^(m + 1) → ℝ}
    (hφx : ContDiffUpToBoundary 2 φx Ω) (hcx : ContinuousOn φx (closure Ω))
    (hφy : ContDiffUpToBoundary 2 φy Ω) (hcy : ContinuousOn φy (closure Ω))
    (hhx : ∀ z ∈ Ω, laplacian φx z = 0)
    (hhy : ∀ z ∈ Ω, laplacian φy z = 0)
    (hbx : EqOn φx (fun z ↦ fundamentalSolution (m + 1) (z - x)) (frontier Ω))
    (hby : EqOn φy (fun z ↦ fundamentalSolution (m + 1) (z - y)) (frontier Ω)) :
    fundamentalSolution (m + 1) (y - x) - φx y =
      fundamentalSolution (m + 1) (x - y) - φy x := by
  let Kx := fun z ↦ fundamentalSolution (m + 1) (z - x)
  let Ky := fun z ↦ fundamentalSolution (m + 1) (z - y)
  let Dx := (hφx.of_le (show 1 ≤ 2 by omega)).completedGradient
  let Dy := (hφy.of_le (show 1 ≤ 2 by omega)).completedGradient
  let Bx := fun z ↦ φy z * normalFlux (Ω := Ω) (fun w ↦ ∇ Kx w - Dx w) z
  let By := fun z ↦ φx z * normalFlux (Ω := Ω) (fun w ↦ ∇ Ky w - Dy w) z
  let BK := fun z ↦ Kx z * normalFlux (Ω := Ω) (∇ Ky) z -
    Ky z * normalFlux (Ω := Ω) (∇ Kx) z
  let BC := fun z ↦ φx z * normalFlux (Ω := Ω) Dy z -
    φy z * normalFlux (Ω := Ω) Dx z
  obtain ⟨_, hix, hex⟩ :=
    representation_of_corrector hn hgraph hφy hcy hx hφx hcx hhx hbx
  obtain ⟨_, hiy, hey⟩ :=
    representation_of_corrector hn hgraph hφx hcx hy hφy hcy hhy hby
  have hxzero : (∫ z in Ω, (Kx z - φx z) * laplacian φy z) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro z hz
    rw [hhy z hz, mul_zero]
  have hyzero : (∫ z in Ω, (Ky z - φy z) * laplacian φx z) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro z hz
    rw [hhx z hz, mul_zero]
  dsimp only [greenKernel] at hex hey
  change Integrable Bx (surfaceMeasure Ω) at hix
  change Integrable By (surfaceMeasure Ω) at hiy
  rw [hxzero, sub_zero] at hex
  rw [hyzero, sub_zero] at hey
  obtain ⟨hki, hke⟩ : Integrable BK (surfaceMeasure Ω) ∧ ∫ z, BK z ∂surfaceMeasure Ω = 0 := by
    by_cases hxy : x = y
    · subst hxy
      have hBK : BK = 0 := funext fun z ↦ sub_self _
      rw [hBK]
      exact ⟨integrable_zero _ _ _, integral_zero _ _⟩
    · exact integral_kernel_cross_normalFlux_eq_zero hn hgraph hx hy hxy
  obtain ⟨_, hci, hce⟩ :=
    green_second_identity_of_contDiffUpToBoundary hgraph hφx hcx hφy hcy
  have hczero : (∫ z in Ω, φx z * laplacian φy z - φy z * laplacian φx z) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro z hz
    rw [hhy z hz, hhx z hz, mul_zero, mul_zero, sub_self]
  rw [hczero] at hce
  have hb : (fun z ↦ Bx z - By z) =ᵐ[surfaceMeasure Ω] fun z ↦ BC z - BK z := by
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with z hz
    dsimp only [Bx, By, BC, BK]
    simp only [normalFlux_eq_inner _ hz, inner_sub_left, hbx hz, hby hz]
    ring
  have hbe := integral_congr_ae hb
  rw [integral_sub hix hiy, integral_sub hci hki, ← hce, hke, sub_self] at hbe
  have heven : Ky x = Kx y := fundamentalSolution_eq_of_norm_eq (norm_sub_rev x y)
  change φy x = -(∫ z, Bx z ∂surfaceMeasure Ω) at hex
  change φx y = -(∫ z, By z ∂surfaceMeasure Ω) at hey
  change Kx y - φx y = Ky x - φy x
  linarith

end PotentialTheory.GreenFunction.Domain
