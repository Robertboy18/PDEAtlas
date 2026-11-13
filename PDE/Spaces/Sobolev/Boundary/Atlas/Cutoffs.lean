/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
public import PDE.DistributionTheory.TestFunction.CompactCutoff -- shake: keep
import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport -- shake: keep

/-!
# Derived cutoffs for operational C¹ domains

The extension operator on a bounded `C¹` domain is assembled from the partition of unity
`ψ₀ + ∑ ψᵢ = 1` of a `C1ExtensionAtlas`. Each local piece is transported to the half-space,
extended by reflection, and pulled back. At three points in this construction one needs a smooth
cutoff which equals `1` on a compact set `K` and is supported in an open set `U ⊇ K`:

* in the source, to relocalize the interior piece inside `Ω` (`interiorSupportCutoff`, with
  `K = tsupport ψ₀` and `U = Ω`);
* in the target of the `i`-th chart, to cut the reflected extension down to a compactly supported
  function inside the chart target (`targetSupportCutoff`, with `K = chartᵢ '' tsupport ψᵢ` and
  `U = (chartᵢ).target`);
* back in the source, to make the pulled-back reflected term compactly supported inside the chart
  source (`pullbackSupportCutoff`, with `K = (chartᵢ).symm '' tsupport ηᵢ` and
  `U = (chartᵢ).source`).

All three come from the smooth Urysohn lemma `TestFunction.exists_eq_one_on_compact`, chosen
once and for all with `Classical.choose`. We name the compact sets, prove they are compact and
lie in the right open sets, and record the support and value-one properties of the resulting
cutoffs, together with the bound `0 ≤ ηᵢ ≤ 1` for the target cutoff. The only analysis is
continuity of charts on compact sets.

## Main declarations

* `interiorSupport`, `interiorSupportCutoff`: the interior partition support and its cutoff.
* `boundarySupport`, `boundarySupportInTarget`, `targetSupportCutoff`, `targetCutoffSupport`:
  the `i`-th boundary support, its chart image, the target cutoff `ηᵢ`, and the support of `ηᵢ`.
* `pullbackSupport`, `pullbackSupportCutoff`: the inverse-chart image of `tsupport ηᵢ` and a
  source cutoff equal to `1` near it.
* `vol_chart_target_ne_top`: bounded chart targets have finite Lebesgue measure.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1 and its proof, pp. 268-271, the extension
  theorem for bounded `C¹` domains.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions

set_option linter.missingDocs true

namespace SobolevSpace

open Set
open scoped ENNReal Topology

namespace Boundary
namespace C1ExtensionAtlas

namespace DerivedCutoffs

open MeasureTheory
open SobolevSpace.HalfSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} [hΩ : C1ExtensionAtlas n Ω]

/-- Every bounded chart target has finite Euclidean volume. -/
theorem vol_chart_target_ne_top (i : Fin hΩ.N) :
    (MeasureTheory.volume : Measure (ℝ^n)) (hΩ.chart i).target ≠ ∞ := by
  have hlt :
      (MeasureTheory.volume : Measure (ℝ^n)) (hΩ.chart i).target < ∞ :=
    (hΩ.chart_target_bounded i).measure_lt_top
      (μ := (MeasureTheory.volume : Measure (ℝ^n)))
  exact hlt.ne

/-- The compact set `tsupport (ψ₀)` attached to the interior partition piece. -/
noncomputable def interiorSupport : Set (ℝ^n) :=
  tsupport hΩ.interiorCutoff.toFun

/-- The support of the interior partition function is compact. -/
theorem isCompact_interiorSupport : IsCompact (interiorSupport (n := n) (Ω := Ω)) := by
  change HasCompactSupport hΩ.interiorCutoff.toFun
  exact hΩ.interiorCutoff.hasCompactSupport

/-- The interior partition support lies inside the domain. -/
theorem interiorSupport_subset_domain : interiorSupport (n := n) (Ω := Ω) ⊆ Ω := by
  simpa [interiorSupport] using hΩ.interiorCutoff_support

/-- A cutoff supported in `Ω`, equal to `1` on `tsupport ψ₀`. -/
noncomputable def interiorSupportCutoff : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
  Classical.choose
    (TestFunction.exists_eq_one_on_compact (n := n)
      (U := Ω)
      (K := interiorSupport (n := n) (Ω := Ω))
      (hU := hΩ.isOpen)
      (hK := isCompact_interiorSupport (n := n) (Ω := Ω))
      (hKU := interiorSupport_subset_domain (n := n) (Ω := Ω)))

/-- The interior support cutoff is supported in the domain. -/
theorem tsupport_interiorSupportCutoff_subset_domain :
    tsupport (interiorSupportCutoff (n := n) (Ω := Ω)).toFun ⊆ Ω :=
by
  classical
  have h :=
      Classical.choose_spec
        (TestFunction.exists_eq_one_on_compact (n := n)
          (U := Ω)
          (K := interiorSupport (n := n) (Ω := Ω))
          (hU := hΩ.isOpen)
          (hK := isCompact_interiorSupport (n := n) (Ω := Ω))
          (hKU := interiorSupport_subset_domain (n := n) (Ω := Ω)))
  simpa [interiorSupportCutoff] using h.1

/-- The interior support cutoff equals one on the interior partition support. -/
theorem interiorSupportCutoff_eq_one_on_interiorSupport :
    ∀ x ∈ interiorSupport (n := n) (Ω := Ω),
      (interiorSupportCutoff (n := n) (Ω := Ω)).toFun x = 1 :=
by
  classical
  have h :=
      Classical.choose_spec
        (TestFunction.exists_eq_one_on_compact (n := n)
          (U := Ω)
          (K := interiorSupport (n := n) (Ω := Ω))
          (hU := hΩ.isOpen)
          (hK := isCompact_interiorSupport (n := n) (Ω := Ω))
          (hKU := interiorSupport_subset_domain (n := n) (Ω := Ω)))
  simpa [interiorSupportCutoff] using h.2.1

/-- The interior support cutoff is identically one near every point of the interior
partition support. -/
theorem interiorSupportCutoff_eq_one_nhds_on_interiorSupport :
    ∀ x ∈ interiorSupport (n := n) (Ω := Ω),
      (interiorSupportCutoff (n := n) (Ω := Ω)).toFun =ᶠ[𝓝 x] 1 :=
by
  classical
  have h :=
      Classical.choose_spec
        (TestFunction.exists_eq_one_on_compact (n := n)
          (U := Ω)
          (K := interiorSupport (n := n) (Ω := Ω))
          (hU := hΩ.isOpen)
          (hK := isCompact_interiorSupport (n := n) (Ω := Ω))
          (hKU := interiorSupport_subset_domain (n := n) (Ω := Ω)))
  simpa [interiorSupportCutoff] using h.2.2.1

/-- The compact support of the `i`-th boundary partition function. -/
noncomputable def boundarySupport (i : Fin hΩ.N) : Set (ℝ^n) :=
  tsupport (hΩ.boundaryCutoff i).toFun

/-- Each boundary partition support is compact. -/
theorem isCompact_boundarySupport (i : Fin hΩ.N) :
    IsCompact (boundarySupport (n := n) (Ω := Ω) i) := by
  change HasCompactSupport (hΩ.boundaryCutoff i).toFun
  exact (hΩ.boundaryCutoff i).hasCompactSupport

/-- The `i`-th boundary partition support lies in the source of its chart. -/
theorem boundarySupport_subset_source (i : Fin hΩ.N) :
    boundarySupport (n := n) (Ω := Ω) i ⊆ (hΩ.chart i).source := by
  intro x hx
  exact hΩ.boundaryCutoff_support i hx

/-- The compact set `chartᵢ '' tsupport(ψᵢ)` in the target coordinates. -/
noncomputable def boundarySupportInTarget (i : Fin hΩ.N) : Set (ℝ^n) :=
  (hΩ.chart i) '' boundarySupport (n := n) (Ω := Ω) i

/-- The chart image of a boundary partition support is compact. -/
theorem isCompact_boundarySupportInTarget (i : Fin hΩ.N) :
    IsCompact (boundarySupportInTarget (n := n) (Ω := Ω) i) := by
  have hK : IsCompact (boundarySupport (n := n) (Ω := Ω) i) :=
    isCompact_boundarySupport (n := n) (Ω := Ω) i
  refine hK.image_of_continuousOn
    ((hΩ.chart i).continuousOn.mono (boundarySupport_subset_source (n := n) (Ω := Ω) i))

/-- The transported boundary support lies in the target of its chart. -/
theorem boundarySupportInTarget_subset_target (i : Fin hΩ.N) :
    boundarySupportInTarget (n := n) (Ω := Ω) i ⊆ (hΩ.chart i).target := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact (hΩ.chart i).map_source (boundarySupport_subset_source (n := n) (Ω := Ω) i hx)

/-- A cutoff `ηᵢ` supported in the chart target, equal to `1` on `chartᵢ '' tsupport(ψᵢ)`. -/
noncomputable def targetSupportCutoff (i : Fin hΩ.N) : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
  Classical.choose
    (TestFunction.exists_eq_one_on_compact (n := n)
      (U := (hΩ.chart i).target)
      (K := boundarySupportInTarget (n := n) (Ω := Ω) i)
      (hU := (hΩ.chart i).open_target)
      (hK := isCompact_boundarySupportInTarget (n := n) (Ω := Ω) i)
      (hKU := boundarySupportInTarget_subset_target (n := n) (Ω := Ω) i))

/-- The target support cutoff is supported in the chart target. -/
theorem tsupport_targetSupportCutoff_subset_target (i : Fin hΩ.N) :
    tsupport (targetSupportCutoff (n := n) (Ω := Ω) i).toFun ⊆ (hΩ.chart i).target :=
  (Classical.choose_spec
      (TestFunction.exists_eq_one_on_compact (n := n)
        (U := (hΩ.chart i).target)
        (K := boundarySupportInTarget (n := n) (Ω := Ω) i)
        (hU := (hΩ.chart i).open_target)
        (hK := isCompact_boundarySupportInTarget (n := n) (Ω := Ω) i)
        (hKU := boundarySupportInTarget_subset_target (n := n) (Ω := Ω) i))).1

/-- The target support cutoff equals one on the transported boundary support. -/
theorem targetSupportCutoff_eq_one_on_boundarySupportInTarget (i : Fin hΩ.N) :
    ∀ y ∈ boundarySupportInTarget (n := n) (Ω := Ω) i,
      (targetSupportCutoff (n := n) (Ω := Ω) i).toFun y = 1 :=
  (Classical.choose_spec
      (TestFunction.exists_eq_one_on_compact (n := n)
        (U := (hΩ.chart i).target)
        (K := boundarySupportInTarget (n := n) (Ω := Ω) i)
        (hU := (hΩ.chart i).open_target)
        (hK := isCompact_boundarySupportInTarget (n := n) (Ω := Ω) i)
        (hKU := boundarySupportInTarget_subset_target (n := n) (Ω := Ω) i))).2.1

/-- The target support cutoff is identically one near every point of the transported
boundary support. -/
theorem targetSupportCutoff_eq_one_nhds_on_boundarySupportInTarget (i : Fin hΩ.N) :
    ∀ y ∈ boundarySupportInTarget (n := n) (Ω := Ω) i,
      (targetSupportCutoff (n := n) (Ω := Ω) i).toFun =ᶠ[𝓝 y] 1 :=
  (Classical.choose_spec
      (TestFunction.exists_eq_one_on_compact (n := n)
        (U := (hΩ.chart i).target)
        (K := boundarySupportInTarget (n := n) (Ω := Ω) i)
        (hU := (hΩ.chart i).open_target)
        (hK := isCompact_boundarySupportInTarget (n := n) (Ω := Ω) i)
        (hKU := boundarySupportInTarget_subset_target (n := n) (Ω := Ω) i))).2.2.1

/-- The canonical target cutoff is a smooth cutoff: its values lie
in the closed unit interval. -/
theorem targetSupportCutoff_mem_Icc (i : Fin hΩ.N) (y : ℝ^n) :
    (targetSupportCutoff (n := n) (Ω := Ω) i).toFun y ∈ Set.Icc (0 : ℝ) 1 :=
  (Classical.choose_spec
      (TestFunction.exists_eq_one_on_compact (n := n)
        (U := (hΩ.chart i).target)
        (K := boundarySupportInTarget (n := n) (Ω := Ω) i)
        (hU := (hΩ.chart i).open_target)
        (hK := isCompact_boundarySupportInTarget (n := n) (Ω := Ω) i)
        (hKU := boundarySupportInTarget_subset_target (n := n) (Ω := Ω) i))).2.2.2 y

/-- Compact target support used after the reflected half-space extension is relocalized. -/
noncomputable def targetCutoffSupport (i : Fin hΩ.N) : Set (ℝ^n) :=
  tsupport (targetSupportCutoff (n := n) (Ω := Ω) i).toFun

/-- The target support cutoff has compact support. -/
theorem isCompact_targetCutoffSupport (i : Fin hΩ.N) :
    IsCompact (targetCutoffSupport (n := n) (Ω := Ω) i) := by
  change HasCompactSupport (targetSupportCutoff (n := n) (Ω := Ω) i).toFun
  exact (targetSupportCutoff (n := n) (Ω := Ω) i).hasCompactSupport

/-- The target support cutoff is supported inside the chart target. -/
theorem targetCutoffSupport_subset_target (i : Fin hΩ.N) :
    targetCutoffSupport (n := n) (Ω := Ω) i ⊆ (hΩ.chart i).target :=
  tsupport_targetSupportCutoff_subset_target (n := n) (Ω := Ω) i

/-- The inverse-chart image of the relocalized reflected support. -/
noncomputable def pullbackSupport (i : Fin hΩ.N) : Set (ℝ^n) :=
  (hΩ.chart i).symm '' targetCutoffSupport (n := n) (Ω := Ω) i

/-- The inverse-chart image of the target cutoff support is compact. -/
theorem isCompact_pullbackSupport (i : Fin hΩ.N) :
    IsCompact (pullbackSupport (n := n) (Ω := Ω) i) := by
  exact (isCompact_targetCutoffSupport (n := n) (Ω := Ω) i).image_of_continuousOn
    ((hΩ.chart i).symm.continuousOn.mono
      (targetCutoffSupport_subset_target (n := n) (Ω := Ω) i))

/-- The pulled-back cutoff support lies inside the chart source. -/
theorem pullbackSupport_subset_source (i : Fin hΩ.N) :
    pullbackSupport (n := n) (Ω := Ω) i ⊆ (hΩ.chart i).source := by
  rintro x ⟨y, hy, rfl⟩
  exact (hΩ.chart i).map_target
    (targetCutoffSupport_subset_target (n := n) (Ω := Ω) i hy)

/-- A source-chart cutoff equal to one near the support of the pulled-back reflected term. -/
noncomputable def pullbackSupportCutoff (i : Fin hΩ.N) : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
  Classical.choose
    (TestFunction.exists_eq_one_on_compact (n := n)
      (U := (hΩ.chart i).source)
      (K := pullbackSupport (n := n) (Ω := Ω) i)
      (hU := (hΩ.chart i).open_source)
      (hK := isCompact_pullbackSupport (n := n) (Ω := Ω) i)
      (hKU := pullbackSupport_subset_source (n := n) (Ω := Ω) i))

/-- The pullback support cutoff is supported in the chart source. -/
theorem tsupport_pullbackSupportCutoff_subset_source (i : Fin hΩ.N) :
    tsupport (pullbackSupportCutoff (n := n) (Ω := Ω) i).toFun ⊆ (hΩ.chart i).source :=
  (Classical.choose_spec
    (TestFunction.exists_eq_one_on_compact (n := n)
      (U := (hΩ.chart i).source)
      (K := pullbackSupport (n := n) (Ω := Ω) i)
      (hU := (hΩ.chart i).open_source)
      (hK := isCompact_pullbackSupport (n := n) (Ω := Ω) i)
      (hKU := pullbackSupport_subset_source (n := n) (Ω := Ω) i))).1

/-- The pullback support cutoff equals one on the pulled-back target support. -/
theorem pullbackSupportCutoff_eq_one_on_pullbackSupport (i : Fin hΩ.N) :
    ∀ x ∈ pullbackSupport (n := n) (Ω := Ω) i,
      (pullbackSupportCutoff (n := n) (Ω := Ω) i).toFun x = 1 :=
  (Classical.choose_spec
    (TestFunction.exists_eq_one_on_compact (n := n)
      (U := (hΩ.chart i).source)
      (K := pullbackSupport (n := n) (Ω := Ω) i)
      (hU := (hΩ.chart i).open_source)
      (hK := isCompact_pullbackSupport (n := n) (Ω := Ω) i)
      (hKU := pullbackSupport_subset_source (n := n) (Ω := Ω) i))).2.1

/-- The pullback support cutoff is identically one near every point of the pulled-back
target support. -/
theorem pullbackSupportCutoff_eq_one_nhds_on_pullbackSupport (i : Fin hΩ.N) :
    ∀ x ∈ pullbackSupport (n := n) (Ω := Ω) i,
      (pullbackSupportCutoff (n := n) (Ω := Ω) i).toFun =ᶠ[nhds x] 1 :=
  (Classical.choose_spec
    (TestFunction.exists_eq_one_on_compact (n := n)
      (U := (hΩ.chart i).source)
      (K := pullbackSupport (n := n) (Ω := Ω) i)
      (hU := (hΩ.chart i).open_source)
      (hK := isCompact_pullbackSupport (n := n) (Ω := Ω) i)
      (hKU := pullbackSupport_subset_source (n := n) (Ω := Ω) i))).2.2.1

end DerivedCutoffs

end C1ExtensionAtlas
end Boundary

end SobolevSpace
