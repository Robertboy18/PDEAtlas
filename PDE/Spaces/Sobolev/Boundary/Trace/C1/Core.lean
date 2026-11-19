/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Spaces.Sobolev.Approximation.Density.Restriction
public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
public import PDE.Spaces.Sobolev.Boundary.Geometry.SurfaceMeasure
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Geometry
import PDE.Spaces.Sobolev.Extension.C1.Assembly.Operator

/-!
# Classical core for traces on operational C¹ domains

We embed ambient smooth test functions in `W^{1,p}(Ω)`, prove density for
finite `p`, and realize literal boundary restriction in the
intrinsic surface-measure `Lᵖ` space. The exponent is an `ℝ≥0∞`, so the
Hilbert case `p = 2` and finite real exponents use the same construction.
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace
namespace Trace.C1

open MeasureTheory Set
open scoped ENNReal Sobolev

/-- Restriction of an ambient smooth test function to a domain carrying an
operational `C¹` atlas, as an element of `W^{1,p}(Ω)`. -/
noncomputable def globalTestFunctionToDomainW1pLinear
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Trace.HalfSpace.GlobalTestFunction m →ₗ[ℝ]
      W^{1,p}(Ω) :=
  (GraphSpace.restrictCLM
      (n := m + 1) (k := 1) (p := p)
      hΩ.isOpen.measurableSet (Set.subset_univ _)).toLinearMap.comp
    (GraphSpace.testFunctionToWkpLinear
      (n := m + 1) (k := 1) (p := p) (Ω := Set.univ))

/-- The domain test-function embedding is the classical Sobolev
embedding of the same function on the domain. -/
theorem globalTestFunctionToDomainW1pLinear_eq_mk
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (φ : Trace.HalfSpace.GlobalTestFunction m) :
    globalTestFunctionToDomainW1pLinear
        (m := m) (Ω := Ω) p φ =
      GraphSpace.mkWkpSpaceOnOfContDiff
        (n := m + 1) (k := 1) (p := p) (Ω := Ω)
        (f := φ.1.toFun) φ.1.contDiff φ.1.hasCompactSupport := by
  exact GraphSpace.restrictCLM_mkWkpSpaceOnOfContDiff
    hΩ.isOpen.measurableSet (Set.subset_univ _)
    φ.1.toFun φ.1.contDiff φ.1.hasCompactSupport

/-- Restrictions of ambient smooth test functions are dense in
`W^{1,p}(Ω)` whenever `p < ∞`. -/
theorem denseRange_globalTestFunctionToDomainW1pLinear
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    DenseRange
      (globalTestFunctionToDomainW1pLinear
        (m := m) (Ω := Ω) p) := by
  rw [DenseRange]
  intro u
  rw [mem_closure_iff_seq_limit]
  obtain ⟨f, hf, hcs, hlim⟩ :=
    Extension.C1.approximation_W1pSpaceOn
      (n := m + 1) (p := p) (Ω := Ω)
       hp u
  let φ : ℕ → Trace.HalfSpace.GlobalTestFunction m := fun k ↦
    ⟨_root_.TestFunction.mk
      (f k) (hf k) (hcs k) (Set.subset_univ _), Set.subset_univ _⟩
  refine ⟨fun k ↦
    globalTestFunctionToDomainW1pLinear
      (m := m) (Ω := Ω) p (φ k), ?_, ?_⟩
  · intro k
    exact ⟨φ k, rfl⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hφ_toFun (k : ℕ) : (φ k).1.toFun = f k := by
      funext x
      rfl
    simp_rw [globalTestFunctionToDomainW1pLinear_eq_mk, hφ_toFun]
    exact hlim

/-- The boundary restriction of an ambient smooth test function lies in the
surface-measure `Lᵖ` space, because it is continuous with compact support. -/
theorem globalTestFunctionBoundary_memLp
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ≥0∞) (φ : Trace.HalfSpace.GlobalTestFunction m) :
    MemLp φ.1.toFun p
      (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) := by
  exact φ.1.contDiff.continuous.memLp_of_hasCompactSupport
    φ.1.hasCompactSupport

/-- Literal restriction of an ambient smooth test function to the physical
boundary, represented in intrinsic surface-measure `Lᵖ`. -/
noncomputable def globalTestFunctionBoundaryLpLinear
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ≥0∞) :
    Trace.HalfSpace.GlobalTestFunction m →ₗ[ℝ]
      MeasureTheory.Lp ℝ p
        (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) where
  toFun φ := (globalTestFunctionBoundary_memLp
    (m := m) (Ω := Ω) p φ).toLp φ.1.toFun
  map_add' φ ψ := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x ↦ by simp
  map_smul' c φ := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x ↦ by simp

/-- Almost-everywhere formula for literal boundary restriction. -/
theorem globalTestFunctionBoundaryLpLinear_apply_ae
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ≥0∞) (φ : Trace.HalfSpace.GlobalTestFunction m) :
    (globalTestFunctionBoundaryLpLinear
      (m := m) (Ω := Ω) p φ : ℝ^(m + 1) → ℝ) =ᵐ[
        Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω]
      φ.1.toFun :=
  (globalTestFunctionBoundary_memLp
    (m := m) (Ω := Ω) p φ).coeFn_toLp

end Trace.C1
end SobolevSpace
