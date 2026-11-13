/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Flux.WeakClassical
public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.Existence
public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.Regularization
public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Kernel
public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.NewtonRepresentation
import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.PoissonLoad

/-!
# Green representation using a weak normal derivative

A weakly harmonic `H¹` corrector has a bounded normal functional on the trace space, even when no
classical boundary gradient has been constructed. Subtracting it from the functional of a smooth
regularization of the fundamental pole gives, in `exists_weakGreenNormalTrace_of_corrector`, a
functional `N` on the trace space with `u(x) = -N(u) - ∫ G Δu`, where `G = greenKernel x φ` and `N`
is applied to the trace of `u`, for every `u` of class `C²` up to the boundary and continuous on the
closure. `exists_weakGreen_representation_of_corrector` states the identity with the weak normal
trace of an explicit zero-trace field in place of `-N`, and
`exists_weakGreen_representation_of_local_graph` also constructs the corrector. This is Evans's
formula (28) in §2.2.4(a) with `N` in place of `u ↦ ∫ u ∂G/∂ν dS`.

The functional is chosen before the test function. The proof constructs it
from the corrector and the regularized pole; it is not supplied as a
representation hypothesis. An L² surface density for this functional is constructed in
`Domain.SurfaceRepresentation`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(a), the definition of Green's function for the region
  `U` and the representation formula (28), p. 34.
  <https://doi.org/10.1090/gsm/019>
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace PotentialTheory.GreenFunction.Domain

open Filter MeasureTheory Metric Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Boundary SobolevSpace.Trace.C1
open SobolevSpace.Boundary.Geometry.SurfaceMeasure
open scoped Sobolev Gradient Topology

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [hΩ : C1ExtensionAtlas (m + 1) Ω]

/-- Green representation uses the given regularizer, its zero-trace
corrector difference, and its explicit Poisson load. Keeping these witnesses
allows the same weak normal density to be used in a boundary limit proof. -/
theorem green_representation_of_regularized_corrector
    (hn : 2 ≤ m + 1) (hgraph : HasC1GraphBoundary Ω)
    {x : ℝ^(m + 1)} (hx : x ∈ Ω)
    (U : H¹(Ω)) {φ : ℝ^(m + 1) → ℝ}
    (hrep : baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] φ)
    (hweak : ∀ t : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) U)
        (derivCoordCLM i t)) = 0)
    (A : ℝ^(m + 1) → ℝ) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hAc : HasCompactSupport A) (w : H¹₀(Ω))
    (hw : (w : H¹(Ω)) = U - mkWkpSpaceOnOfContDiff A hA hAc)
    (hreg : ∀ y ∈ frontier Ω,
      A =ᶠ[𝓝 y] fun z ↦ fundamentalSolution (m + 1) (z - x))
    (f : DerivLp (m + 1) 2 Ω)
    (hwf : ∀ t : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i)
        (w : H¹(Ω))) (derivCoordCLM i t)) = -inner ℝ f (baseCoordCLM t))
    (hfF : (f : ℝ^(m + 1) → ℝ) =ᵐ[domainMeasure (m + 1) Ω]
      Ω.indicator (fun y ↦ -PDE.laplacian A y)) :
    ∀ (u : ℝ^(m + 1) → ℝ) (hu : ContDiffUpToBoundary 2 u Ω),
      ContinuousOn u (closure Ω) →
      IntegrableOn (fun y ↦ greenKernel x φ y * PDE.laplacian u y) Ω ∧
      u x = weakNormalTrace (w : H¹(Ω)) f hwf (traceClass
        ((hu.of_le (show 1 ≤ 2 by omega)).toWkpSpaceOn hΩ.isOpen hΩ.bounded 2)) -
          ∫ y in Ω, greenKernel x φ y * PDE.laplacian u y := by
  let hA₂ : ContDiffUpToBoundary 2 A Ω :=
    ContDiffUpToBoundary.of_contDiff (hA.of_le (by norm_num)) hΩ.bounded
  let hA₁ := hA₂.of_le (show 1 ≤ 2 by omega)
  let A₁ : H¹(Ω) := hA₁.toWkpSpaceOn hΩ.isOpen hΩ.bounded 2
  let A₂ : W^{2,2}(Ω) := hA₂.toWkpSpaceOn hΩ.isOpen hΩ.bounded 2
  let K := fun y ↦ fundamentalSolution (m + 1) (y - x)
  have hAeq : mkWkpSpaceOnOfContDiff (k := 1) (p := 2) (Ω := Ω) A hA hAc = A₁ := by
    apply WkpSpaceOn.ext_of_base_ae hΩ.isOpen
    refine Filter.EventuallyEq.trans ?_ (hA₁.toWkpSpaceOn_base_ae hΩ.isOpen hΩ.bounded 2).symm
    simpa only [baseRepresentative, baseIndex_toList, iteratedPartialDeriv] using
      mkWkpSpaceOnOfContDiff_apply_ae (k := 1) (p := 2) (Ω := Ω) A hA hAc (baseIndex (m + 1) 1)
  have htrace : trace U = trace A₁ := sub_eq_zero.1 <| by
    rw [← map_sub, ← hAeq, ← hw]
    exact (trace_eq_zero_iff_mem_H10 _).mpr w.property
  have hnormal {y : ℝ^(m + 1)} (hy : y ∈ frontier Ω) :
      hA₁.completedGradient y = gradient K y := by
    rw [hA₁.completedGradient_eq_gradient_extension hΩ.isOpen
      (hA.of_le (by norm_num)) (fun _ _ ↦ rfl) (frontier_subset_closure hy)]
    exact (hreg y hy).gradient_eq
  let N : HilbertTraceSpace (Ω := Ω) →L[ℝ] ℝ :=
    weakNormalTraceOfH2 A₂ - weakHarmonicNormalTrace U hweak
  have hw' : (w : H¹(Ω)) = U - A₁ := hw.trans (congrArg (U - ·) hAeq)
  have hAlower : lowerOrderCLM (show 1 ≤ 2 by omega) A₂ = A₁ :=
    hA₂.lowerOrder_toWkpSpaceOn hΩ.isOpen hΩ.bounded 2 (show 1 ≤ 2 by omega)
  have hfeq : f = -wkpLaplacianCLM A₂ := by
    apply Lp.ext
    filter_upwards [hfF, Lp.coeFn_neg (wkpLaplacianCLM A₂),
      hA₂.coordinate_laplacian_toWkpSpaceOn_ae hΩ.isOpen hΩ.bounded 2,
      ae_restrict_mem (μ := volume) hΩ.isOpen.measurableSet] with y hfy hneg hΔ hy
    rw [hneg, Pi.neg_apply, hfy, indicator_of_mem hy]
    exact congrArg Neg.neg hΔ.symm
  have hwN : weakNormalTrace (w : H¹(Ω)) f hwf = -N := by
    ext q
    obtain ⟨V, rfl⟩ := (trace (Ω := Ω)).ker.mkQ_surjective q
    change weakNormalTrace (w : H¹(Ω)) f hwf (traceClass V) =
      -(weakNormalTraceOfH2 A₂ (traceClass V) -
        weakHarmonicNormalTrace U hweak (traceClass V))
    rw [weakNormalTrace_traceClass, weakNormalTraceOfH2_traceClass,
      weakHarmonicNormalTrace_traceClass, hAlower, hw', map_sub, inner_sub_left, hfeq,
      inner_neg_left]
    ring
  intro u hu hcu
  let hu₁ := hu.of_le (show 1 ≤ 2 by omega)
  let V : W^{2,2}(Ω) := hu.toWkpSpaceOn hΩ.isOpen hΩ.bounded 2
  let V₁ : H¹(Ω) := hu₁.toWkpSpaceOn hΩ.isOpen hΩ.bounded 2
  let Du := hu₁.completedGradient
  have hprod : (fun y ↦ baseRepresentative U y * wkpLaplacianCLM V y)
      =ᵐ[volume.restrict Ω] fun y ↦ φ y * PDE.laplacian u y := by
    filter_upwards [hu.coordinate_laplacian_toWkpSpaceOn_ae hΩ.isOpen hΩ.bounded 2,
      hrep] with y hy hφy
    change baseRepresentative U y *
      (wkpLaplacianCLM (hu.toWkpSpaceOn hΩ.isOpen hΩ.bounded 2)) y = _
    rw [hy, hφy]
  have hvol :
      inner ℝ (wkpLaplacianCLM V) (wkpBaseCoordinateCLM U) =
        ∫ y in Ω, φ y * PDE.laplacian u y := by
    rw [L2.inner_def]
    refine integral_congr_ae (hprod.mono fun y hy ↦ ?_)
    simp only [RCLike.inner_apply, conj_trivial]
    exact hy
  have hφi : IntegrableOn (fun y ↦ φ y * PDE.laplacian u y) Ω :=
    ((Lp.memLp (wkpBaseCoordinateCLM U)).integrable_mul (Lp.memLp (wkpLaplacianCLM V))).congr hprod
  have hsurfaceA : (fun y ↦ A y * normalFlux (Ω := Ω) Du y)
      =ᵐ[surfaceMeasure Ω] fun y ↦ K y * normalFlux (Ω := Ω) Du y := by
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with y hy
    rw [(hreg y hy).eq_of_nhds]
  have hsurfaceN : (fun y ↦ u y * normalFlux (Ω := Ω) hA₁.completedGradient y)
      =ᵐ[surfaceMeasure Ω] fun y ↦ u y * normalFlux (Ω := Ω) (gradient K) y := by
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with y hy
    simp only [normalFlux_eq_inner _ hy, hnormal hy]
  have hKi : Integrable (fun y ↦ K y * normalFlux (Ω := Ω) Du y) (surfaceMeasure Ω) :=
    (Boundary.Flux.green_first_identity_of_contDiffUpToBoundary hgraph
      hA₁ hA.continuous.continuousOn hu).2.2.1.congr hsurfaceA
  have hNi : Integrable (fun y ↦ u y * normalFlux (Ω := Ω) (gradient K) y)
      (surfaceMeasure Ω) :=
    (Boundary.Flux.green_first_identity_of_contDiffUpToBoundary hgraph
      hu₁ hcu hA₂).2.2.1.congr hsurfaceN
  have hmix :
      (∫ y in Ω, φ y * PDE.laplacian u y) +
          weakHarmonicNormalTrace U hweak (traceClass V₁) =
        ∫ y, K y * normalFlux (Ω := Ω) Du y ∂surfaceMeasure Ω := by
    have h := laplacian_pairing_add_weakHarmonicNormalTrace_eq V U A₁ hweak htrace
    rw [← weakNormalTraceOfH2_traceClass V A₁,
      hu.lowerOrder_toWkpSpaceOn hΩ.isOpen hΩ.bounded 2 (show 1 ≤ 2 by omega),
      hvol] at h
    exact h.trans
      ((weakNormalTraceOfH2_toWkpSpaceOn_traceClass hgraph hu hA₁
        hA.continuous.continuousOn).trans (integral_congr_ae hsurfaceA))
  obtain ⟨hnewi, _, hnew⟩ := newton_representation hn hgraph hu hcu hx
  have hgreen : (fun y ↦ K y * PDE.laplacian u y - φ y * PDE.laplacian u y)
      =ᵐ[volume.restrict Ω] fun y ↦ greenKernel x φ y * PDE.laplacian u y :=
    Eventually.of_forall fun _ ↦ (sub_mul _ _ _).symm
  refine ⟨(hnewi.sub hφi).congr hgreen, ?_⟩
  have hgreenvol := integral_congr_ae hgreen
  rw [integral_sub hnewi hφi] at hgreenvol
  rw [integral_sub hKi hNi] at hnew
  change u x = weakNormalTrace (w : H¹(Ω)) f hwf (traceClass V₁) -
    ∫ y in Ω, greenKernel x φ y * PDE.laplacian u y
  rw [hwN, neg_apply, show N (traceClass V₁) = weakNormalTraceOfH2 A₂ (traceClass V₁) -
    weakHarmonicNormalTrace U hweak (traceClass V₁) from rfl,
    (weakNormalTraceOfH2_toWkpSpaceOn_traceClass hgraph hA₂ hu₁ hcu).trans
      (integral_congr_ae hsurfaceN)]
  linarith

/-- Subtracting a smooth lifting from a harmonic corrector gives zero-trace
H¹ data with L² Laplacian. Its weak normal trace gives Green representation
for every classical test function. This form retains the zero-trace witness
needed by boundary regularity estimates. -/
theorem exists_weakGreen_representation_of_corrector
    (hn : 2 ≤ m + 1) (hgraph : HasC1GraphBoundary Ω)
    {x : ℝ^(m + 1)} (hx : x ∈ Ω)
    (U : H¹(Ω)) {φ : ℝ^(m + 1) → ℝ}
    (hrep : baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] φ)
    (hcφ : ContinuousOn φ (closure Ω))
    (hbφ : EqOn φ (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω))
    (hweak : ∀ t : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) U)
        (derivCoordCLM i t)) = 0) :
    ∃ w : H¹₀(Ω), ∃ f : DerivLp (m + 1) 2 Ω,
      ∃ hwf : ∀ t : H¹₀(Ω),
        (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i)
          (w : H¹(Ω))) (derivCoordCLM i t)) = -inner ℝ f (baseCoordCLM t),
      ∀ (u : ℝ^(m + 1) → ℝ) (hu : ContDiffUpToBoundary 2 u Ω),
        ContinuousOn u (closure Ω) →
        IntegrableOn (fun y ↦ greenKernel x φ y * PDE.laplacian u y) Ω ∧
        u x = weakNormalTrace (w : H¹(Ω)) f hwf (traceClass
          ((hu.of_le (show 1 ≤ 2 by omega)).toWkpSpaceOn hΩ.isOpen hΩ.bounded 2)) -
            ∫ y in Ω, greenKernel x φ y * PDE.laplacian u y := by
  obtain ⟨P⟩ := SobolevSpace.Approximation.UpToBoundary.exists_inwardPartition
    hΩ.isOpen hΩ.bounded
    (hasC1Boundary_of_local_graph hgraph)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ.isOpen x hx
  obtain ⟨A, hA, hAc, w, hw, _, hreg⟩ :=
    exists_regularized_corrector P hΩ.bounded hr hball U hcφ hrep hbφ
  have hboundary {y : ℝ^(m + 1)} (hy : y ∈ frontier Ω) :
      A =ᶠ[𝓝 y] (fun z ↦ fundamentalSolution (m + 1) (z - x)) := by
    apply hreg y (frontier_subset_closure hy)
    by_contra! hnear
    exact (hΩ.isOpen.frontier_eq ▸ hy).2
      (hball (by simpa only [mem_ball, dist_eq_norm] using hnear))
  let : Fact (0 < m + 1) := ⟨by omega⟩
  obtain ⟨_, _, _, f, hfF, hwf⟩ :=
    exists_interior_load_of_regularized_corrector hΩ.isOpen hΩ.bounded hx
      U A hA hAc w hw hweak (fun _ hy ↦ hboundary hy)
  exact ⟨w, f, hwf, green_representation_of_regularized_corrector
    hn hgraph hx U hrep hweak A hA hAc w hw (fun _ hy ↦ hboundary hy) f hwf hfF⟩

/-- A weak harmonic corrector determines one bounded boundary functional that
gives Green representation for every classical test function. No boundary
derivative of the corrector, or density of the functional, is assumed. -/
theorem exists_weakGreenNormalTrace_of_corrector
    (hn : 2 ≤ m + 1) (hgraph : HasC1GraphBoundary Ω)
    {x : ℝ^(m + 1)} (hx : x ∈ Ω)
    (U : H¹(Ω)) {φ : ℝ^(m + 1) → ℝ}
    (hrep : baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] φ)
    (hcφ : ContinuousOn φ (closure Ω))
    (hbφ : EqOn φ (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω))
    (hweak : ∀ t : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) U)
        (derivCoordCLM i t)) = 0) :
    ∃ N : HilbertTraceSpace (Ω := Ω) →L[ℝ] ℝ,
      ∀ (u : ℝ^(m + 1) → ℝ) (hu : ContDiffUpToBoundary 2 u Ω),
        ContinuousOn u (closure Ω) →
        IntegrableOn (fun y ↦ greenKernel x φ y * PDE.laplacian u y) Ω ∧
        u x = -N (traceClass
          ((hu.of_le (show 1 ≤ 2 by omega)).toWkpSpaceOn hΩ.isOpen hΩ.bounded 2)) -
            ∫ y in Ω, greenKernel x φ y * PDE.laplacian u y := by
  obtain ⟨w, f, hwf, hformula⟩ :=
    exists_weakGreen_representation_of_corrector hn hgraph hx U hrep hcφ hbφ hweak
  refine ⟨-weakNormalTrace (w : H¹(Ω)) f hwf, ?_⟩
  intro u hu hcu
  simpa only [neg_apply, neg_neg] using hformula u hu hcu

omit hΩ in
/-- Bounded open C¹ graph geometry constructs both the harmonic corrector and
the bounded boundary functional in the weak Green formula. The same functional
works for all classical test functions at the chosen interior pole. -/
theorem exists_weakGreen_representation_of_local_graph
    (hn : 2 ≤ m + 1) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω) {x : ℝ^(m + 1)} (hx : x ∈ Ω) :
    letI atlas := hgraph.c1ExtensionAtlas hopen hbounded
    ∃ φ : ℝ^(m + 1) → ℝ,
      LaplacianEquation.IsHarmonicPDE (m + 1) φ Ω ∧
      ContinuousOn φ (closure Ω) ∧
      EqOn φ (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω) ∧
      ∃ N : HilbertTraceSpace (Ω := Ω) →L[ℝ] ℝ,
        ∀ (u : ℝ^(m + 1) → ℝ) (hu : ContDiffUpToBoundary 2 u Ω),
          ContinuousOn u (closure Ω) →
          IntegrableOn (fun y ↦ greenKernel x φ y * PDE.laplacian u y) Ω ∧
          u x = -N (traceClass
            ((hu.of_le (show 1 ≤ 2 by omega)).toWkpSpaceOn hopen hbounded 2)) -
              ∫ y in Ω, greenKernel x φ y * PDE.laplacian u y := by
  let atlas := hgraph.c1ExtensionAtlas hopen hbounded
  obtain ⟨U, φ, hrep, hh, hc, hb, hw⟩ :=
    exists_harmonic_corrector_of_local_graph hn hopen hbounded hgraph hx
  exact ⟨φ, hh, hc, hb,
    exists_weakGreenNormalTrace_of_corrector hn hgraph hx U hrep hc hb hw⟩

end PotentialTheory.GreenFunction.Domain
