/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.C1.Classical
public import PDE.Spaces.Sobolev.Extension.VectorValued.Geometric.Flattening

/-!
# Localized Banach-valued Sobolev functions in boundary charts

Multiply by a boundary partition factor and flatten the resulting Sobolev function into
the upper half-space. The physical base representative is the compact chart expression
used for the classical boundary law. The formula holds on the entire upper half-space,
including beyond the artificial edge of the chart.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.C1

open GraphSpace GeometricExtension

variable {m : ℕ} {Ω : Opens ℝ^(m + 1)}
  [hΩ : Boundary.C1ExtensionAtlas (m + 1) (Ω : Set ℝ^(m + 1))]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Localize by one boundary partition factor and flatten into the upper half-space. -/
def localizedFlatten (i : Fin hΩ.N) :
    W^{1,p}(Ω; F) →L[ℝ]
      W^{1,p}(⟨ℝ^(m + 1)₊, HalfSpace.isOpen_upper (m + 1)⟩; F) :=
  (flattenSobolev (k := 1) (by decide) hΩ.chart_symm_contDiff i).comp
    (compactSmoothMultiplierCLM (hΩ.boundaryCutoff i).toFun
      (hΩ.boundaryCutoff i).contDiff (hΩ.boundaryCutoff i).hasCompactSupport)

/-- The Sobolev chart piece represents the localized classical expression whenever
the physical base has the given ambient representative. -/
theorem localizedFlatten_base_ae (i : Fin hΩ.N) (U : W^{1,p}(Ω; F))
    {f : ℝ^(m + 1) → F}
    (hU : (U.val (baseIndex (m + 1) 1) : ℝ^(m + 1) → F)
      =ᵐ[domainMeasure (m + 1) Ω] f) :
    ((localizedFlatten i U).val (baseIndex (m + 1) 1) : ℝ^(m + 1) → F)
      =ᵐ[domainMeasure (m + 1) ℝ^(m + 1)₊] flattenedClassicalPiece i f := by
  let V := compactSmoothMultiplierCLM (hΩ.boundaryCutoff i).toFun
    (hΩ.boundaryCutoff i).contDiff (hΩ.boundaryCutoff i).hasCompactSupport U
  have hV : (V.val (baseIndex (m + 1) 1) : ℝ^(m + 1) → F)
      =ᵐ[domainMeasure (m + 1) Ω] fun x ↦ (hΩ.boundaryCutoff i).toFun x • f x := by
    filter_upwards [compactSmoothMultiplierCLM_base_ae (hΩ.boundaryCutoff i).toFun
      (hΩ.boundaryCutoff i).contDiff (hΩ.boundaryCutoff i).hasCompactSupport U, hU]
      with x hx hux
    exact hx.trans (congrArg ((hΩ.boundaryCutoff i).toFun x • ·) hux)
  change (coordinateCLM (baseIndex (m + 1) 1)
    (flattenSobolev (k := 1) (by decide) hΩ.chart_symm_contDiff i V) : ℝ^(m + 1) → F)
      =ᵐ[_] _
  have hbase := flattenSobolev_base (k := 1) (by decide) hΩ.chart_symm_contDiff i V
  exact (Filter.EventuallyEq.of_eq
    (congrArg (fun g : Lp F p (domainMeasure (m + 1) ℝ^(m + 1)₊) ↦
      (g : ℝ^(m + 1) → F)) hbase)).trans (flattenLp_ae_eq i _ hV)

end SobolevSpace.VectorValued.Trace.C1
