/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GreenKernel
public import PDE.Elliptic.Classical.Poisson.FundamentalSolutionConvolution
import PDE.Elliptic.Classical.Poisson.PlanarFundamentalSolution
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability
import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarLogMoment

/-!
# Green potentials on the upper half-space

The half-space Green potential of a source `f` is

`u(x) = ∫_{ℝ^n₊} G(y, x) f(y) dy`,

where `G` is the method-of-images kernel `halfSpaceGreenFunction` of Evans's §2.2.4(b); `u` is the
source term of his representation formula (30) on the half-space. We prove that `u` vanishes on the
boundary hyperplane and that oddness of `f` in a tangential coordinate passes to `u`. In the plane,
every continuous compactly supported source has an integrable Green potential, and at an interior
point where the source is `C²` the potential is `C²` and satisfies `-Δu = f`, with no condition on
the boundary values of the source.

## Main definitions

* `halfSpaceGreenPotential`, `HasIntegrableHalfSpaceGreenPotential`: the potential and the pointwise
  integrability domain of the Green operator.
* `oddHalfSpaceExtension`: the odd extension of a planar source across the boundary, set to zero on
  the boundary.

## Main results

* `halfSpaceGreenPotential_boundary`: `u = 0` on the boundary hyperplane.
* `halfSpaceGreenPotential_coordinateReflection_of_odd`: integrability at one point and tangential
  oddness of `f` imply integrability at the reflected point and the parity identity.
* `hasIntegrableHalfSpaceGreenPotential_of_odd_of_integrable` and its corollaries: an odd planar
  source whose whole-space logarithmic potential converges (in particular a continuous source with
  finite mass and finite logarithmic moment, or a test function) lies in the domain of the Green
  operator.
* `halfSpaceGreenPotential_eq_convolution_of_odd_of_integrable`: for odd planar sources with
  integrable whole-space logarithmic integrand at `x`, the half-space potential equals `Φ * f` at
  `x`.
* `negative_laplacian_halfSpaceGreenPotential_of_odd`: `-Δ (halfSpaceGreenPotential f) = f`
  pointwise for compactly supported `C²` planar sources that are odd across the boundary.
* `hasIntegrableHalfSpaceGreenPotential_of_continuous`: integrability for continuous compact planar
  sources, including those with nonzero boundary values.
* `halfSpaceGreenPotential_local_poisson`: interior `C²` regularity and Poisson inversion at points
  where a continuous compact source is `C²`.

## How it works

Evans proves `-Δ(Φ * f) = f` on the whole space (§2.2.1(b), Theorem 1); for the half-space,
Theorem 14 verifies Poisson's formula, the case `f = 0`. We obtain the source term from the
whole-space theorem. If `f(ỹ) = -f(y)`, the image term `-Φ(x - ỹ) f(y)` integrated over the upper
half-plane equals `Φ(x - y) f(y)` integrated over the lower half-plane, so when the whole-space
logarithmic integrand is integrable at `x` the half-space potential at `x` is `(Φ * f)(x)`, and
`-Δu = f` for compactly supported `C²` odd sources is
`PoissonEquation.negative_laplacian_fundamentalSolutionConvolution_two`. A general continuous
compact source is replaced by `oddHalfSpaceExtension f`. That extension can jump across the
boundary, but it agrees with `f` near an interior point, so the local whole-space result
`PoissonEquation.fundamentalSolution_convolution_local_poisson` gives interior inversion.

## Implementation notes

The definition uses Mathlib's total Bochner integral, which returns `0` on non-integrable
integrands. The analytic identities either assume the required integrability or derive it from the
stated source regularity and tail conditions. In particular, the inversion theorem derives
integrability from its compactly supported `C²` datum. The kernel receives the integration variable
as its source point and `x` as its field point; by `halfSpaceGreenFunction_comm` the opposite
ordering gives the same function.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.1(b), Theorem 1 (Solving Poisson's equation), pp. 23-25;
  §2.2.4(a), Theorem 12 (Representation formula using Green's function), (30), p. 35; §2.2.4(b), the
  definition of Green's function for the half-space and Theorem 14 (Poisson's formula for
  half-space), p. 37.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

noncomputable section

set_option linter.missingDocs true

namespace GreenFunction

open MeasureTheory Set
open SobolevSpace
open scoped Topology Convolution

/-- The method-of-images Green potential of `f` on the upper half-space.

The kernel receives the integration variable as its source point and `x` as
its field point. By `halfSpaceGreenFunction_comm`, this agrees with the
opposite common convention for ordering Green-kernel arguments. -/
def halfSpaceGreenPotential {n : ℕ} [Fact (0 < n)]
    (f : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  ∫ y in HalfSpace.upper n,
    halfSpaceGreenFunction (n := n) y x * f y

/-- The source lies in the pointwise domain of the half-space Green
operator: its Green integrand is Bochner integrable at every evaluation
point. -/
def HasIntegrableHalfSpaceGreenPotential {n : ℕ} [Fact (0 < n)]
    (f : ℝ^n → ℝ) : Prop :=
  ∀ x : ℝ^n, IntegrableOn
    (fun y ↦ halfSpaceGreenFunction (n := n) y x * f y)
    (HalfSpace.upper n)

/-- The half-space Green operator depends only on the source in the open physical domain. -/
theorem halfSpaceGreenPotential_congr
    {n : ℕ} [Fact (0 < n)] {f g : ℝ^n → ℝ} (hfg : EqOn f g (HalfSpace.upper n)) :
    halfSpaceGreenPotential f = halfSpaceGreenPotential g := by
  funext x
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (HalfSpace.measurableSet_upper (n := n))] with y hy
  rw [hfg hy]

/-- A half-space Green potential vanishes on the boundary hyperplane. -/
theorem halfSpaceGreenPotential_boundary
    {n : ℕ} [Fact (0 < n)] (f : ℝ^n → ℝ) {x : ℝ^n}
    (hx : x ∈ HalfSpace.boundary n) :
    halfSpaceGreenPotential f x = 0 := by
  simp [halfSpaceGreenPotential, halfSpaceGreenFunction_boundary (n := n) hx]

/-- If the Green integrand is integrable at `x`, and the source is odd in a
tangential coordinate, then the integrand is integrable at the reflected
point and the Green potential is odd in that coordinate.

The first component of the conclusion records integrability at the reflected
evaluation point; the second is the parity identity itself. -/
theorem halfSpaceGreenPotential_coordinateReflection_of_odd
    {n : ℕ} [Fact (0 < n)] {i : Fin n}
    (hi : i ≠ PDE.Common.lastIndex (n := n))
    (f : ℝ^n → ℝ) (x : ℝ^n)
    (hodd : ∀ y ∈ HalfSpace.upper n,
      f (PDE.Common.coordinateReflection i y) = -f y)
    (hintegrable : IntegrableOn
      (fun y ↦ halfSpaceGreenFunction (n := n) y x * f y)
      (HalfSpace.upper n)) :
    IntegrableOn
        (fun y ↦
          halfSpaceGreenFunction (n := n) y
            (PDE.Common.coordinateReflection i x) * f y)
        (HalfSpace.upper n) ∧
      halfSpaceGreenPotential f (PDE.Common.coordinateReflection i x) =
        -halfSpaceGreenPotential f x := by
  have hmp := HalfSpace.measurePreserving_coordinateReflection_restrict_upper n hi
  have hemb : MeasurableEmbedding (PDE.Common.coordinateReflection i : ℝ^n → ℝ^n) :=
    (PDE.Common.coordinateReflectionLinearIsometryEquiv i).toMeasurableEquiv.measurableEmbedding
  have hcomp : (fun y ↦ halfSpaceGreenFunction (n := n) (PDE.Common.coordinateReflection i y)
        (PDE.Common.coordinateReflection i x) * f (PDE.Common.coordinateReflection i y))
      =ᵐ[volume.restrict (HalfSpace.upper n)]
        fun y ↦ -(halfSpaceGreenFunction (n := n) y x * f y) := by
    filter_upwards [ae_restrict_mem (HalfSpace.measurableSet_upper (n := n))] with y hy
    rw [halfSpaceGreenFunction_coordinateReflection (n := n) hi y x, hodd y hy]
    ring
  refine ⟨(hmp.integrable_comp_emb hemb (g := fun y ↦ halfSpaceGreenFunction (n := n) y
    (PDE.Common.coordinateReflection i x) * f y)).mp ((Integrable.neg hintegrable).congr
      hcomp.symm), ?_⟩
  calc halfSpaceGreenPotential f (PDE.Common.coordinateReflection i x)
      = ∫ y in HalfSpace.upper n, halfSpaceGreenFunction (n := n)
          (PDE.Common.coordinateReflection i y) (PDE.Common.coordinateReflection i x) *
            f (PDE.Common.coordinateReflection i y) := (hmp.integral_comp hemb _).symm
    _ = -halfSpaceGreenPotential f x := by rw [integral_congr_ae hcomp, integral_neg]; rfl

/-! ## Planar Poisson inversion -/

/-- The whole-space convolution integrand is integrable when its right factor
is a compactly supported `C²` function. -/
private theorem integrable_fundamentalSolution_mul_testFunction_sub
    (f : TestFunction (⊤ : TopologicalSpace.Opens (ℝ^2)) ℝ 2)
    (x : ℝ^2) :
    Integrable
      (fun y : ℝ^2 ↦
        PotentialTheory.fundamentalSolution 2 (x - y) * f y) := by
  have hconvolution :=
    f.hasCompactSupport.convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℝ)
      (PotentialTheory.locallyIntegrable_fundamentalSolution 2)
      f.continuous x
  simpa using hconvolution.integrable_swap

/-- If a planar source is odd across the boundary and its whole-space
logarithmic potential is integrable at `x`, then the reflected-image term is
integrable on the upper half-plane. -/
private theorem integrableOn_reflectedFundamentalSolution_mul_of_odd_of_integrable
    (f : ℝ^2 → ℝ)
    (hodd : ∀ y : ℝ^2, f (HalfSpace.reflect 2 y) = -f y)
    (x : ℝ^2)
    (hintegrable : Integrable
      (fun y : ℝ^2 ↦
        PotentialTheory.fundamentalSolution 2 (x - y) * f y)) :
    IntegrableOn
      (fun y : ℝ^2 ↦
        PotentialTheory.fundamentalSolution 2
          (x - HalfSpace.reflect 2 y) * f y)
      (HalfSpace.upper 2) := by
  let H : ℝ^2 → ℝ := fun y ↦ PotentialTheory.fundamentalSolution 2 (x - y) * f y
  have hK : Integrable (H ∘ HalfSpace.reflect 2) (volume.restrict (HalfSpace.upper 2)) := by
    rw [← (HalfSpace.measurePreserving_reflect_restrict_lower 2).integrable_comp_emb
      (HalfSpace.reflectLinearIsometryEquiv 2).toMeasurableEquiv.measurableEmbedding,
      Function.comp_assoc, (HalfSpace.reflect_involutive 2).comp_self, Function.comp_id]
    exact hintegrable.integrableOn
  refine hK.neg.congr (.of_forall fun y ↦ ?_)
  simp only [Pi.neg_apply, Function.comp_apply, H, hodd]
  ring

/-- An odd planar source lies in the integrability domain of the half-space
Green operator whenever its whole-space logarithmic potential is integrable
at every evaluation point.

This is the method-of-images integrability statement needed for noncompact
sources; the tail condition replaces compact support. -/
theorem hasIntegrableHalfSpaceGreenPotential_of_odd_of_integrable
    (f : ℝ^2 → ℝ)
    (hodd : ∀ y : ℝ^2, f (HalfSpace.reflect 2 y) = -f y)
    (hintegrable : ∀ x : ℝ^2, Integrable
      (fun y : ℝ^2 ↦
        PotentialTheory.fundamentalSolution 2 (x - y) * f y)) :
    HasIntegrableHalfSpaceGreenPotential f := by
  intro x
  refine ((hintegrable x).integrableOn.sub
    (integrableOn_reflectedFundamentalSolution_mul_of_odd_of_integrable f hodd x
      (hintegrable x))).congr (.of_forall fun y ↦ ?_)
  simp only [Pi.sub_apply, halfSpaceGreenFunction]
  ring

/-- A continuous normally odd source with finite mass and finite logarithmic
moment lies in the domain of the planar half-space Green operator. -/
theorem hasIntegrableHalfSpaceGreenPotential_of_odd_of_integrable_log_weight
    (f : ℝ^2 → ℝ)
    (hodd : ∀ y : ℝ^2, f (HalfSpace.reflect 2 y) = -f y)
    (hfcontinuous : Continuous f)
    (hf : Integrable f)
    (hflog : Integrable (fun y : ℝ^2 ↦ Real.log (1 + ‖y‖) * f y)) :
    HasIntegrableHalfSpaceGreenPotential f :=
  hasIntegrableHalfSpaceGreenPotential_of_odd_of_integrable f hodd
    (PotentialTheory.integrable_fundamentalSolution_mul_of_integrable_log_weight
      f hfcontinuous hf hflog)

/-- A compactly supported `C²` planar source that is odd across the boundary lies
in the natural integrability domain of the half-space Green operator. -/
theorem hasIntegrableHalfSpaceGreenPotential_of_odd
    (f : TestFunction (⊤ : TopologicalSpace.Opens (ℝ^2)) ℝ 2)
    (hodd : ∀ y : ℝ^2, f (HalfSpace.reflect 2 y) = -f y) :
    HasIntegrableHalfSpaceGreenPotential f := by
  exact hasIntegrableHalfSpaceGreenPotential_of_odd_of_integrable f hodd fun x ↦
    integrable_fundamentalSolution_mul_testFunction_sub f x

/-- For an odd planar source with integrable whole-space logarithmic
potential, the method-of-images potential equals convolution with the planar
fundamental solution. -/
theorem halfSpaceGreenPotential_eq_convolution_of_odd_of_integrable
    (f : ℝ^2 → ℝ)
    (hodd : ∀ y : ℝ^2, f (HalfSpace.reflect 2 y) = -f y)
    (x : ℝ^2)
    (hintegrable : Integrable
      (fun y : ℝ^2 ↦
        PotentialTheory.fundamentalSolution 2 (x - y) * f y)) :
    halfSpaceGreenPotential f x =
      convolution (PotentialTheory.fundamentalSolution 2) f
        (ContinuousLinearMap.mul ℝ ℝ) volume x := by
  let H : ℝ^2 → ℝ := fun y ↦ PotentialTheory.fundamentalSolution 2 (x - y) * f y
  let J : ℝ^2 → ℝ := fun y ↦
    PotentialTheory.fundamentalSolution 2 (x - HalfSpace.reflect 2 y) * f y
  have hH : Integrable H := hintegrable
  have hJ : IntegrableOn J (HalfSpace.upper 2) :=
    integrableOn_reflectedFundamentalSolution_mul_of_odd_of_integrable f hodd x hintegrable
  have hlower : ∫ y in HalfSpace.lower 2, H y = ∫ y in HalfSpace.upper 2, -J y := by
    rw [← (HalfSpace.measurePreserving_reflect_restrict_lower 2).integral_comp
      (HalfSpace.reflectLinearIsometryEquiv 2).toMeasurableEquiv.measurableEmbedding
      fun y ↦ -J y]
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    simp only [H, J, hodd, HalfSpace.reflect_involutive 2 y]
    ring
  calc halfSpaceGreenPotential f x = ∫ y in HalfSpace.upper 2, H y - J y :=
        integral_congr_ae (.of_forall fun y ↦ by simp only [halfSpaceGreenFunction, H, J]; ring)
    _ = ∫ y, H y := by
      rw [integral_sub hH.integrableOn hJ,
        ← integral_add_compl (HalfSpace.measurableSet_upper (n := 2)) hH,
        setIntegral_congr_set (HalfSpace.compl_upper_ae_eq_lower (n := 2)), hlower, integral_neg]
      ring
    _ = _ := by rw [MeasureTheory.convolution_mul_swap]

/-- For a continuous normally odd source with finite mass and finite
logarithmic moment, the method-of-images potential equals whole-space
convolution with the planar fundamental solution. -/
theorem halfSpaceGreenPotential_eq_convolution_of_odd_of_integrable_log_weight
    (f : ℝ^2 → ℝ)
    (hodd : ∀ y : ℝ^2, f (HalfSpace.reflect 2 y) = -f y)
    (hfcontinuous : Continuous f)
    (hf : Integrable f)
    (hflog : Integrable (fun y : ℝ^2 ↦ Real.log (1 + ‖y‖) * f y))
    (x : ℝ^2) :
    halfSpaceGreenPotential f x =
      convolution (PotentialTheory.fundamentalSolution 2) f
        (ContinuousLinearMap.mul ℝ ℝ) volume x :=
  halfSpaceGreenPotential_eq_convolution_of_odd_of_integrable f hodd x
    (PotentialTheory.integrable_fundamentalSolution_mul_of_integrable_log_weight
      f hfcontinuous hf hflog x)

/-- For odd compactly supported `C²` data, the method-of-images potential
equals convolution with the whole-space planar fundamental solution. -/
theorem halfSpaceGreenPotential_eq_fundamentalSolutionConvolution_of_odd
    (f : TestFunction (⊤ : TopologicalSpace.Opens (ℝ^2)) ℝ 2)
    (hodd : ∀ y : ℝ^2, f (HalfSpace.reflect 2 y) = -f y)
    (x : ℝ^2) :
    halfSpaceGreenPotential f x =
      PoissonEquation.fundamentalSolutionConvolution 2 f x := by
  rw [PoissonEquation.fundamentalSolutionConvolution]
  exact halfSpaceGreenPotential_eq_convolution_of_odd_of_integrable
    f hodd x (integrable_fundamentalSolution_mul_testFunction_sub f x)

/-- The planar method-of-images Green potential solves `-Δu = f`
pointwise for every compactly supported `C²` source that is odd across the
boundary. -/
theorem negative_laplacian_halfSpaceGreenPotential_of_odd
    (f : TestFunction (⊤ : TopologicalSpace.Opens (ℝ^2)) ℝ 2)
    (hodd : ∀ y : ℝ^2, f (HalfSpace.reflect 2 y) = -f y)
    (x : ℝ^2) :
    -laplacian (halfSpaceGreenPotential f) x = f x := by
  have hpotential : halfSpaceGreenPotential f =
      PoissonEquation.fundamentalSolutionConvolution 2 f := by
    funext y
    exact halfSpaceGreenPotential_eq_fundamentalSolutionConvolution_of_odd
      f hodd y
  rw [hpotential]
  exact PoissonEquation.negative_laplacian_fundamentalSolutionConvolution_two f x

/-- The odd extension of the upper-half-plane source, set to zero on the boundary.
A nonzero boundary value of the original source can give a jump in this extension. -/
def oddHalfSpaceExtension (f : ℝ^2 → ℝ) : ℝ^2 → ℝ :=
  (HalfSpace.upper 2).indicator f -
    (HalfSpace.lower 2).indicator (fun y ↦ f (HalfSpace.reflect 2 y))

/-- The canonical odd extension agrees with its datum on the open upper half-plane. -/
theorem oddHalfSpaceExtension_eqOn (f : ℝ^2 → ℝ) :
    EqOn (oddHalfSpaceExtension f) f (HalfSpace.upper 2) := by
  intro y hy
  have hyl : y ∉ HalfSpace.lower 2 := by
    intro h
    have hypos : 0 < y (PDE.Common.lastIndex (n := 2)) := hy
    have hyneg : y (PDE.Common.lastIndex (n := 2)) < 0 := h
    linarith
  simp [oddHalfSpaceExtension, hy, hyl]

/-- The canonical odd extension depends only on the values on the open upper half-plane. -/
theorem oddHalfSpaceExtension_congr {f g : ℝ^2 → ℝ} (h : EqOn f g (HalfSpace.upper 2)) :
    oddHalfSpaceExtension f = oddHalfSpaceExtension g := by
  unfold oddHalfSpaceExtension
  rw [Set.indicator_congr h, Set.indicator_congr fun y hy ↦
    h ((HalfSpace.mem_upper_reflect_iff (n := 2) (x := y)).mpr hy)]

/-- Reflection in the horizontal axis reverses the canonical extension's sign. -/
theorem oddHalfSpaceExtension_reflect (f : ℝ^2 → ℝ) (y : ℝ^2) :
    oddHalfSpaceExtension f (HalfSpace.reflect 2 y) = -oddHalfSpaceExtension f y := by
  by_cases hyu : y ∈ HalfSpace.upper 2 <;> by_cases hyl : y ∈ HalfSpace.lower 2 <;>
    simp [oddHalfSpaceExtension, hyu, hyl, HalfSpace.mem_upper_reflect_iff (n := 2),
      HalfSpace.mem_lower_reflect_iff (n := 2), HalfSpace.reflect_involutive 2 y]

/-- A compact upper-half-plane source has a compact canonical odd extension. -/
theorem hasCompactSupport_oddHalfSpaceExtension
    {f : ℝ^2 → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (oddHalfSpaceExtension f) := by
  have hrc : HasCompactSupport (fun y ↦ f (HalfSpace.reflect 2 y)) :=
    hc.comp_homeomorph (HalfSpace.reflectLinearIsometryEquiv 2).toHomeomorph
  have hupper : HasCompactSupport ((HalfSpace.upper 2).indicator f) := by
    apply HasCompactSupport.intro hc.isCompact
    intro y hy
    simp [image_eq_zero_of_notMem_tsupport hy]
  have hlower : HasCompactSupport
      ((HalfSpace.lower 2).indicator (fun y ↦ f (HalfSpace.reflect 2 y))) := by
    apply HasCompactSupport.intro hrc.isCompact
    intro y hy
    simp [image_eq_zero_of_notMem_tsupport hy]
  exact hupper.sub hlower

/-- The jump at the boundary does not prevent local integrability of the odd extension. -/
theorem locallyIntegrable_oddHalfSpaceExtension
    {f : ℝ^2 → ℝ} (hf : Continuous f) :
    LocallyIntegrable (oddHalfSpaceExtension f) volume := by
  have hr := hf.comp (HalfSpace.reflectLinearIsometryEquiv 2).continuous
  exact (hf.locallyIntegrable.indicator (HalfSpace.measurableSet_upper (n := 2))).sub
    (hr.locallyIntegrable.indicator (HalfSpace.isOpen_lower 2).measurableSet)

/-- The planar fundamental-solution integral converges for the canonical odd extension
of a continuous compact source, even when the extension jumps at the boundary. -/
theorem integrable_fundamentalSolution_mul_oddHalfSpaceExtension
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) (z : ℝ^2) :
    Integrable (fun y ↦ PotentialTheory.fundamentalSolution 2 (z - y) *
      oddHalfSpaceExtension f y) := by
  have hr := hf.comp (HalfSpace.reflectLinearIsometryEquiv 2).continuous
  have hrc : HasCompactSupport (fun y ↦ f (HalfSpace.reflect 2 y)) :=
    hc.comp_homeomorph (HalfSpace.reflectLinearIsometryEquiv 2).toHomeomorph
  have hfi : Integrable (fun y ↦ PotentialTheory.fundamentalSolution 2 (z - y) * f y) := by
    simpa using (hc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      (PotentialTheory.locallyIntegrable_fundamentalSolution 2) hf z).integrable_swap
  have hri : Integrable (fun y ↦ PotentialTheory.fundamentalSolution 2 (z - y) *
      f (HalfSpace.reflect 2 y)) := by
    simpa using (hrc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      (PotentialTheory.locallyIntegrable_fundamentalSolution 2) hr z).integrable_swap
  apply ((hfi.indicator (HalfSpace.measurableSet_upper (n := 2))).sub
    (hri.indicator (HalfSpace.isOpen_lower 2).measurableSet)).congr
  filter_upwards with y
  simp only [oddHalfSpaceExtension, Pi.sub_apply, Set.indicator]
  split_ifs <;> ring

private theorem exists_odd_compact_extension
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ F : ℝ^2 → ℝ, LocallyIntegrable F volume ∧ HasCompactSupport F ∧
      (∀ y, F (HalfSpace.reflect 2 y) = -F y) ∧ EqOn F f (HalfSpace.upper 2) ∧
      ∀ z, Integrable (fun y ↦ PotentialTheory.fundamentalSolution 2 (z - y) * F y) :=
  ⟨oddHalfSpaceExtension f, locallyIntegrable_oddHalfSpaceExtension hf,
    hasCompactSupport_oddHalfSpaceExtension hc, oddHalfSpaceExtension_reflect f,
    oddHalfSpaceExtension_eqOn f, integrable_fundamentalSolution_mul_oddHalfSpaceExtension hf hc⟩

/-- Every continuous compact planar source has an integrable half-space Green
potential. Its values on the boundary need not vanish. -/
theorem hasIntegrableHalfSpaceGreenPotential_of_continuous
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    HasIntegrableHalfSpaceGreenPotential f := by
  obtain ⟨F, _, _, hodd, heq, hi⟩ := exists_odd_compact_extension hf hc
  intro x
  apply (hasIntegrableHalfSpaceGreenPotential_of_odd_of_integrable F hodd hi x).congr
  filter_upwards [ae_restrict_mem (HalfSpace.measurableSet_upper (n := 2))] with y hy
  rw [heq hy]

/-- The planar Green potential solves `-Δu = f` at each interior point where
a continuous compact source is `C²`. A nonzero boundary value of `f` is allowed:
its odd extension may jump across the boundary, but is smooth near the point. -/
theorem halfSpaceGreenPotential_local_poisson
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    {x : ℝ^2} (hx : x ∈ HalfSpace.upper 2) (hlocal : ContDiffAt ℝ 2 f x) :
    ContDiffAt ℝ 2 (halfSpaceGreenPotential f) x ∧
      -laplacian (halfSpaceGreenPotential f) x = f x := by
  obtain ⟨F, hF, hFc, hodd, heq, hi⟩ := exists_odd_compact_extension hf hc
  have hgerm : F =ᶠ[nhds x] f := heq.eventuallyEq_of_mem ((HalfSpace.isOpen_upper 2).mem_nhds hx)
  have hpotential : halfSpaceGreenPotential f =
      PotentialTheory.fundamentalSolution 2 ⋆[ContinuousLinearMap.mul ℝ ℝ] F := by
    funext z
    calc
      halfSpaceGreenPotential f z = halfSpaceGreenPotential F z := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (HalfSpace.measurableSet_upper (n := 2))] with y hy
        rw [heq hy]
      _ = (PotentialTheory.fundamentalSolution 2 ⋆[ContinuousLinearMap.mul ℝ ℝ] F) z :=
        halfSpaceGreenPotential_eq_convolution_of_odd_of_integrable F hodd z (hi z)
  rw [hpotential]
  obtain ⟨hreg, hpoisson⟩ := PoissonEquation.fundamentalSolution_convolution_local_poisson
    hF hFc (hlocal.congr_of_eventuallyEq hgerm)
  exact ⟨hreg, hpoisson.trans (heq hx)⟩

end GreenFunction
