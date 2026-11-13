/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ContinuousRepresentative
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ZeroTrace
public import PDE.Spaces.Sobolev.Boundary.Flux.Graph.Topology
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Closure
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Operators

/-!
# Admissibility of classical collar tests

The trace of a C¹ representative is its restriction to the boundary. Thus a
C¹ test vanishing on the boundary belongs to H¹₀. Applying this fact to
`φ * (1 - χ(d/t))` proves the cutoff-test admissibility from `χ(0)=1`
and vanishing boundary height on the support of φ. The weak gradient is the
classical gradient of this test; no boundary gradient of the state is used.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Set MeasureTheory
open scoped Sobolev Gradient

namespace SobolevSpace.GraphSpace.Rellich

open Approximation.UpToBoundary Boundary.Geometry.SurfaceMeasure Trace.C1

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
  [H : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- A globally C¹ scalar field vanishing on the boundary has an H¹₀
realization with its classical value and gradient representatives. -/
theorem exists_H10_of_contDiff_boundary_zero
    (P : InwardPartition Ω) {v : ℝ^(m + 1) → ℝ}
    (hv : ContDiff ℝ 1 v) (hzero : ∀ x ∈ frontier Ω, v x = 0) :
    ∃ V : H¹₀(Ω),
      baseRepresentative (V : H¹(Ω)) =ᵐ[domainMeasure (m + 1) Ω] v ∧
      (wkpGradientCLM (V : H¹(Ω)) : ℝ^(m + 1) → ℝ^(m + 1))
        =ᵐ[domainMeasure (m + 1) Ω] ∇ v := by
  let hvb := ContDiffUpToBoundary.of_contDiff hv H.bounded
  let V : H¹(Ω) := hvb.toWkpSpaceOn H.isOpen H.bounded 2
  have hbase : baseRepresentative V =ᵐ[domainMeasure (m + 1) Ω] v := by
    simpa only [baseRepresentative, baseIndex_toList, iteratedPartialDeriv] using
      hvb.toWkpSpaceOn_apply_ae H.isOpen H.bounded 2 (baseIndex (m + 1) 1)
  have htrace : trace V = 0 := by
    apply Lp.ext
    have hclass := trace_eq_ae_of_continuousOn P V hv.continuous.continuousOn hbase
    have hfront : ∀ᵐ x ∂surfaceMeasure Ω, x ∈ frontier Ω := by
      simpa only [surfaceMeasure, Nat.add_sub_cancel] using
        ae_restrict_mem (μ := Measure.euclideanHausdorffMeasure m)
          isClosed_frontier.measurableSet
    filter_upwards [hclass, hfront, Lp.coeFn_zero (E := ℝ) (p := 2)
      (μ := surfaceMeasure Ω)] with x hx hxΩ hz
    exact (hx.trans (hzero x hxΩ)).trans hz.symm
  refine ⟨⟨V, (trace_eq_zero_iff_mem_H10 V).mp htrace⟩, hbase, ?_⟩
  exact hvb.gradient_toWkpSpaceOn_ae H.isOpen H.bounded 2

/-- The complementary collar cutoff is an admissible H¹₀ test. Boundary
height is needed only where the ambient test is nonzero. -/
theorem exists_H10_collarComplement
    (P : InwardPartition Ω) {φ d : ℝ^(m + 1) → ℝ} {χ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hd : ContDiff ℝ 1 d) (hχ : ContDiff ℝ 1 χ)
    (hχ0 : χ 0 = 1)
    (hboundary : ∀ x ∈ frontier Ω, φ x ≠ 0 → d x = 0) (t : ℝ) :
    ∃ V : H¹₀(Ω),
      baseRepresentative (V : H¹(Ω)) =ᵐ[domainMeasure (m + 1) Ω]
        (fun x ↦ φ x * (1 - χ (d x / t))) ∧
      (wkpGradientCLM (V : H¹(Ω)) : ℝ^(m + 1) → ℝ^(m + 1))
        =ᵐ[domainMeasure (m + 1) Ω] ∇ (fun x ↦ φ x * (1 - χ (d x / t))) := by
  apply exists_H10_of_contDiff_boundary_zero P
    (hφ.mul (contDiff_const.sub (hχ.comp (hd.div_const t))))
  intro x hx
  by_cases hφx : φ x = 0
  · simp only [hφx, zero_mul]
  · simp only [Function.comp_apply, hboundary x hx hφx, zero_div, hχ0, sub_self, mul_zero]

/-- A graph chart derives the boundary vanishing condition for the cutoff test
from the support of its ambient factor. The coordinate change may be oblique. -/
theorem exists_H10_graphCollarComplement
    (P : InwardPartition Ω) {U : Set ℝ^(m + 1)} (hU : IsOpen U)
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) {g : ℝ^m → ℝ}
    (hg : ContDiff ℝ 1 g)
    (hside : ∀ x ∈ U, x ∈ Ω ↔ x ∈ Boundary.Flux.Graph.linearEpigraph A g)
    {φ : ℝ^(m + 1) → ℝ} {χ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ U)
    (hχ : ContDiff ℝ 1 χ) (hχ0 : χ 0 = 1) (t : ℝ) :
    ∃ V : H¹₀(Ω),
      baseRepresentative (V : H¹(Ω)) =ᵐ[domainMeasure (m + 1) Ω]
        (fun x ↦ φ x * (1 - χ (Boundary.Flux.Graph.linearGraphHeight A g x / t))) ∧
      (wkpGradientCLM (V : H¹(Ω)) : ℝ^(m + 1) → ℝ^(m + 1))
        =ᵐ[domainMeasure (m + 1) Ω]
          ∇ (fun x ↦ φ x * (1 - χ (Boundary.Flux.Graph.linearGraphHeight A g x / t))) := by
  have hd : ContDiff ℝ 1 (Boundary.Flux.Graph.linearGraphHeight A g) := by
    unfold Boundary.Flux.Graph.linearGraphHeight
    exact ((EuclideanSpace.proj (Fin.last m)).contDiff.comp A.contDiff).sub
      (hg.comp ((ContinuousLinearMap.fst ℝ (ℝ^m) ℝ).contDiff.comp
        (Trace.HalfSpace.tangentialNormalContinuousLinearEquiv.contDiff.comp A.contDiff)))
  apply exists_H10_collarComplement P hφ hd hχ hχ0 _ t
  intro x hx hφx
  exact (Boundary.Flux.Graph.mem_frontier_iff_graphHeight_eq_zero hU A g hg.continuous
    hside (hsupp (subset_tsupport φ (Function.mem_support.mpr hφx)))).mp hx

end SobolevSpace.GraphSpace.Rellich
