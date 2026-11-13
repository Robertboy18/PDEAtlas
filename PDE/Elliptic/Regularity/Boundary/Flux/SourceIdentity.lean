/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.TestFunctionPullback
public import PDE.Spaces.Sobolev.Calculus.Divergence.Functional

/-!
# Boundary-chart tests for an arbitrary square-integrable flux

A target test pulls back to an `H¹₀` test on the physical
domain. Inserting it into `-div q = f` gives the chart-source identity with
the derivative of the chart. The flux need not be linear in a
gradient, nor does it need weak derivatives of its own.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace PDE.Elliptic.Regularity.Boundary

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- The physical weak equation evaluated on the zero-extended inverse image
of a target test. All derivatives belong to the chart or the smooth test. -/
theorem weakFlux_chartPullback_source_identity
    (hΩ : SobolevSpace.Boundary.C1ExtensionAtlas n Ω) (a : Fin hΩ.N)
    (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω)
    (hweak : ∀ v : H¹₀(Ω),
      (∑ i, ⟪q i, derivCoordCLM i v⟫) = ⟪f, baseCoordCLM v⟫)
    (φ : TestFunctionOn n
      (SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ (Ω := Ω) a).target) :
    let E := SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ (Ω := Ω) a
    (∫ x in E.source, ∑ i : Fin n, q i x *
      (∑ j : Fin n, (∂[j] φ.1.toFun) (E x) *
        ((∂[i] (fun z ↦ E z)) x) j)) =
      ∫ x in E.source, f x * φ.1.toFun (E x) := by
  classical
  let E := SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ (Ω := Ω) a
  obtain ⟨Φ, hbase, hderiv⟩ := TestFunctionPullback.exists_chartTest_pullback hΩ a φ
  have hterm (i : Fin n) : Integrable
      (fun x ↦ q i x * derivCoordCLM i Φ x) (domainMeasure n Ω) := by
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using
      L2.integrable_inner (𝕜 := ℝ) (q i) (derivCoordCLM i Φ)
  have hglobal :
      (∫ x, ∑ i : Fin n, q i x * derivCoordCLM i Φ x ∂domainMeasure n Ω) =
        ∫ x, f x * baseCoordCLM Φ x ∂domainMeasure n Ω := by
    rw [integral_finsetSum Finset.univ (fun i _ ↦ hterm i)]
    simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, mul_comm] using hweak Φ
  have hSΩ : E.source ⊆ Ω := fun _ hx ↦ hx.2
  have hind (g : ℝ^n → ℝ) :
      (∫ x, E.source.indicator g x ∂domainMeasure n Ω) = ∫ x in E.source, g x := by
    rw [integral_indicator E.open_source.measurableSet]
    rw [show (domainMeasure n Ω).restrict E.source = volume.restrict E.source by
      exact Measure.restrict_restrict_of_subset hSΩ]
  have hleft : (fun x ↦ ∑ i : Fin n, q i x * derivCoordCLM i Φ x)
      =ᵐ[domainMeasure n Ω] E.source.indicator (fun x ↦ ∑ i : Fin n, q i x *
        (∑ j : Fin n, (∂[j] φ.1.toFun) (E x) *
          (fderiv ℝ (fun z ↦ E z) x (EuclideanSpace.single i 1)) j)) := by
    filter_upwards [ae_all_iff.mpr hderiv] with x hx
    by_cases hxS : x ∈ E.source
    · rw [indicator_of_mem hxS]
      apply Finset.sum_congr rfl
      intro i _
      rw [show derivCoordCLM i Φ x =
        TestFunctionPullback.pullbackDerivative hΩ a φ i x from hx i]
      unfold TestFunctionPullback.pullbackDerivative
      change q i x * E.source.indicator _ x = _
      rw [indicator_of_mem hxS]
    · rw [indicator_of_notMem hxS]
      apply Finset.sum_eq_zero
      intro i _
      rw [show derivCoordCLM i Φ x =
        TestFunctionPullback.pullbackDerivative hΩ a φ i x from hx i]
      unfold TestFunctionPullback.pullbackDerivative
      change q i x * E.source.indicator _ x = _
      rw [indicator_of_notMem hxS, mul_zero]
  have hright : (fun x ↦ f x * baseCoordCLM Φ x) =ᵐ[domainMeasure n Ω]
      E.source.indicator (fun x ↦ f x * φ.1.toFun (E x)) := by
    filter_upwards [hbase] with x hx
    rw [show baseCoordCLM Φ x = TestFunctionPullback.pullbackBase hΩ a φ x from hx]
    change f x * E.source.indicator (fun z ↦ φ.1.toFun (E z)) x = _
    by_cases hxS : x ∈ E.source <;> simp [hxS]
  rw [integral_congr_ae hleft, integral_congr_ae hright, hind, hind] at hglobal
  exact hglobal

end PDE.Elliptic.Regularity.Boundary
