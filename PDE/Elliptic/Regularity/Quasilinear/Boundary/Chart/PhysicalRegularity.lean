/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.H2.ChartLocalization
public import PDE.Elliptic.Regularity.Quasilinear.Boundary.Chart.LocalRegularity

/-!
# Physical cutoff pieces for a monotone quasilinear equation

A cutoff supported in a C² chart has an `H²` representative. The
normal derivative is recovered in chart coordinates from the weak equation;
odd reflection and a buffered pullback return the representative to the
physical domain. There is no regularity assumption on the weak solution.
-/

@[expose] public noncomputable section

open scoped Sobolev

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal NNReal RealInnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- Every smooth cutoff supported in a C² chart of the physical domain
localizes the weak solution to an `H²(Ω)` field. -/
theorem exists_H2_physicalChartCutoff_of_monotone_weakEquation
    (hΩ : SobolevSpace.Boundary.C1ExtensionAtlas n Ω) (a : Fin hΩ.N)
    (hE : ContDiff ℝ 2 (fun x ↦ hΩ.chart a x))
    (hSymm : ContDiff ℝ 2 (fun y ↦ (hΩ.chart a).symm y))
    (A : ℝ^n → ℝ^n) (hzero : A 0 = 0) {θ : ℝ} (hθ : 0 < θ)
    (hmono : ∀ z w, θ * ‖z - w‖ * ‖z - w‖ ≤ ⟪A z - A w, z - w⟫)
    {C : ℝ≥0} (hLip : LipschitzWith C A)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hψ : tsupport ψ.toFun ⊆ (hΩ.chart a).source)
    : ∃ M : ℝ, 0 ≤ M ∧ ∀ (u : H¹₀(Ω))
    (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω),
    (∀ᵐ x ∂domainMeasure n Ω,
      A (WithLp.toLp 2 (fun i ↦ derivCoordCLM i u x)) =
        WithLp.toLp 2 (fun i ↦ q i x)) →
    (∀ v : H¹₀(Ω),
      (∑ i, ⟪q i, derivCoordCLM i v⟫) = ⟪f, baseCoordCLM v⟫) →
    ∃ W : W^{2,2}(Ω),
      (baseRepresentative W =ᵐ[domainMeasure n Ω]
        fun x ↦ ψ.toFun x * baseCoordCLM u x) ∧ ‖W‖ ≤ M * (‖u‖ + ‖f‖) := by
  have hK : IsCompact ((hΩ.chart a) '' tsupport ψ.toFun) :=
    ψ.hasCompactSupport.image (hΩ.chart_contDiff a).continuous
  have hKt : (hΩ.chart a) '' tsupport ψ.toFun ⊆ (hΩ.chart a).target := by
    rintro y ⟨x, hx, rfl⟩
    exact (hΩ.chart a).map_source (hψ hx)
  obtain ⟨η, hηtarget, hηone, _, hηrange⟩ :=
    TestFunction.exists_eq_one_on_compact (hΩ.chart a).open_target hK hKt
  obtain ⟨C₁, hC₁, hchart⟩ := exists_H2_chartCutoff_of_monotone_weakEquation
    hΩ a hE hSymm A hzero hθ hmono hLip η hηtarget
      (fun y _ ↦ by rw [abs_of_nonneg (hηrange y).1]; exact (hηrange y).2)
  obtain ⟨C₂, hC₂, hphysical⟩ := exists_H2_chartLocalization hΩ a hE ψ η hψ hηone
  refine ⟨C₂ * C₁, mul_nonneg hC₂ hC₁, ?_⟩
  intro u q f hq hweak
  obtain ⟨V, htrace, hbase, hVnorm⟩ := hchart u q f hq hweak
  obtain ⟨W, hW, hWnorm⟩ := hphysical (baseCoordCLM u) V htrace hbase
  exact ⟨W, hW, hWnorm.trans
    ((mul_le_mul_of_nonneg_left hVnorm hC₂).trans_eq (mul_assoc _ _ _).symm)⟩

end PDE.Elliptic.Regularity.Quasilinear
