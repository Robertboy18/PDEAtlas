/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Localization
public import PDE.Elliptic.PotentialTheory.FundamentalSolution.Pole
import PDE.Analysis.Calculus.LocalExtension.Support
import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Linear
import PDE.FDeriv.Laplacian.Congruence

/-!
# The Newton boundary representation on a general domain

For `u` of class `C²` up to the boundary of a bounded open domain with C¹ graph boundary and a pole
`x` in the domain, `newton_representation` proves
`u(x) = ∫ (Φ(y - x) ∂_ν u - u ∂_ν Φ(y - x)) dS - ∫ Φ(y - x) Δu dy`, with both integrands integrable.
This is Evans's formula (25) in §2.2.4(a), from which he derives Green's function. The logarithmic
and Newtonian kernels are both included, and no limiting boundary identity is assumed.

## How it works

Evans applies Green's formula on `U - B(x, ε)`, his (24), and lets `ε → 0` using the calculations in
the proof of §2.2.1(b), Theorem 1. We avoid the shrinking ball. A smooth function `a` with compact
support in `Ω` that equals `u` near `x` (`ContDiffOn.exists_contDiff_tsupport_subset_eventuallyEq`)
carries the pole: by `PotentialTheory.integral_fundamentalSolution_sub_mul_laplacian`,
`∫ Φ(y - x) Δa(y) dy = -u(x)`. The difference `u - a` vanishes near `x`, so Green's formula with the
kernel applies to it (`integral_kernel_mul_laplacian_of_zero_near`), and on the boundary `u - a` and
its gradient agree with those of `u`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.1(b), the proof of Theorem 1 (Solving Poisson's
  equation), pp. 23-25; §2.2.4(a), Green's formula on `V_ε = U - B(x, ε)`, (24), p. 33, and the
  representation formula (25), p. 34.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (laplacian)

namespace PotentialTheory.GreenFunction.Domain

open Filter Set MeasureTheory SobolevSpace SobolevSpace.Boundary
open SobolevSpace.Trace.C1 Geometry.SurfaceMeasure
open scoped Topology Gradient

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : C1ExtensionAtlas (m + 1) Ω]

/-- The Newton boundary representation for classical closure data.
The completed gradient gives the interior normal trace on a C¹ boundary. -/
theorem newton_representation
    (hn : 2 ≤ m + 1) (hgraph : HasC1GraphBoundary Ω)
    {u : ℝ^(m + 1) → ℝ} (hu : ContDiffUpToBoundary 2 u Ω)
    (hc : ContinuousOn u (closure Ω)) {x : ℝ^(m + 1)} (hx : x ∈ Ω) :
    let K := fun y ↦ fundamentalSolution (m + 1) (y - x)
    IntegrableOn (fun y ↦ K y * laplacian u y) Ω ∧
      Integrable (fun y ↦ K y * normalFlux (Ω := Ω)
        (hu.of_le (show 1 ≤ 2 by omega)).completedGradient y -
        u y * normalFlux (Ω := Ω) (∇ K) y) (surfaceMeasure Ω) ∧
      u x = (∫ y, K y * normalFlux (Ω := Ω)
        (hu.of_le (show 1 ≤ 2 by omega)).completedGradient y -
          u y * normalFlux (Ω := Ω) (∇ K) y ∂surfaceMeasure Ω) -
        ∫ y in Ω, K y * laplacian u y := by
  let K := fun y ↦ fundamentalSolution (m + 1) (y - x)
  let hu₁ := hu.of_le (show 1 ≤ 2 by omega)
  let Du := hu₁.completedGradient
  obtain ⟨a, ha, hac, has, hnear⟩ :=
    hu.contDiffOn.exists_contDiff_tsupport_subset_eventuallyEq hΩ.isOpen hx
  have haΩ : ContDiffUpToBoundary 2 a Ω :=
    ContDiffUpToBoundary.of_contDiff ha hΩ.bounded
  let ha₁ := haΩ.of_le (show 1 ≤ 2 by omega)
  let w := fun y ↦ u y - a y
  have hw : ContDiffUpToBoundary 2 w Ω := hu.sub haΩ hΩ.isOpen
  have hwc : ContinuousOn w (closure Ω) := hc.sub ha.continuous.continuousOn
  have hwzero : w =ᶠ[𝓝 x] fun _ ↦ 0 := hnear.mono fun y hy ↦ sub_eq_zero.mpr hy
  obtain ⟨hwi, hwb, hweq⟩ :=
    integral_kernel_mul_laplacian_of_zero_near hgraph hw hwc hx hwzero
  have hagerm {y : ℝ^(m + 1)} (hy : y ∉ Ω) : a =ᶠ[𝓝 y] fun _ ↦ 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hy (has h))
  have haoff {y : ℝ^(m + 1)} (hy : y ∉ Ω) : laplacian a y = 0 := by
    rw [EuclideanLaplacian.laplacian_congr_nhds (hagerm hy), PDE.laplacian_const]
  have hapole : (∫ y in Ω, K y * laplacian a y) = -u x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy ↦ by rw [haoff hy, mul_zero])]
    exact (integral_fundamentalSolution_sub_mul_laplacian hn ha hac x).trans
      (congrArg Neg.neg hnear.eq_of_nhds.symm)
  have hai : IntegrableOn (fun y ↦ K y * laplacian a y) Ω :=
    (integrable_fundamentalSolution_sub_mul_laplacian ha hac x).integrableOn
  have hlap {y : ℝ^(m + 1)} (hy : y ∈ Ω) :
      laplacian w y = laplacian u y - laplacian a y :=
    PDE.laplacian_sub u a y (hu.contDiffOn.contDiffAt (hΩ.isOpen.mem_nhds hy)) ha.contDiffAt
  have hsum : (fun y ↦ K y * laplacian w y + K y * laplacian a y)
      =ᵐ[volume.restrict Ω] fun y ↦ K y * laplacian u y := by
    filter_upwards [ae_restrict_mem hΩ.isOpen.measurableSet] with y hy
    rw [hlap hy]
    ring
  have hui : IntegrableOn (fun y ↦ K y * laplacian u y) Ω :=
    (hwi.add hai).congr hsum
  have hboundary {y : ℝ^(m + 1)} (hy : y ∈ frontier Ω) :
      w y = u y ∧ (hw.of_le (show 1 ≤ 2 by omega)).completedGradient y = Du y := by
    have haz := hagerm (hΩ.isOpen.frontier_eq ▸ hy).2
    refine ⟨by change u y - a y = u y; rw [haz.eq_of_nhds, sub_zero], ?_⟩
    have hsub := hu₁.completedGradient_sub ha₁ hΩ.isOpen (frontier_subset_closure hy)
    change (hw.of_le (show 1 ≤ 2 by omega)).completedGradient y =
      Du y - ha₁.completedGradient y at hsub
    rw [hsub, ha₁.completedGradient_eq_gradient_extension hΩ.isOpen
      (ha.of_le (by norm_num)) (fun _ _ ↦ rfl) (frontier_subset_closure hy),
      haz.gradient_eq]
    simp
  have hsurface : (fun y ↦ K y *
      normalFlux (Ω := Ω) (hw.of_le (show 1 ≤ 2 by omega)).completedGradient y -
        w y * normalFlux (Ω := Ω) (∇ K) y) =ᵐ[surfaceMeasure Ω]
      fun y ↦ K y * normalFlux (Ω := Ω) Du y -
        u y * normalFlux (Ω := Ω) (∇ K) y := by
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with y hy
    simp only [normalFlux_eq_inner _ hy, (hboundary hy).1, (hboundary hy).2]
  refine ⟨hui, hwb.congr hsurface, ?_⟩
  have hvol := integral_congr_ae hsum
  rw [integral_add hwi hai, hapole, hweq, integral_congr_ae hsurface] at hvol
  linarith

end PotentialTheory.GreenFunction.Domain
