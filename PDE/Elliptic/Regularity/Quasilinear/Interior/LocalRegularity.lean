/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Boundary.Chart.PhysicalRegularity
import PDE.Spaces.Sobolev.Boundary.Atlas.Operations
import PDE.Spaces.Sobolev.Boundary.Geometry.InteriorChart

/-!
# Interior regularity for a monotone quasilinear equation

Translate the bounded physical domain strictly into the upper half-space.
An interior cutoff then lies inside the target of a smooth chart. The
local chart theorem applies without any boundary contact; its difference
quotient estimates and flux recovery give the interior `H²` representative.
The auxiliary chart has zero partition weight in the original atlas.
-/

@[expose] public noncomputable section

open scoped Sobolev

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal RealInnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- An interior cutoff of a weak solution has an `H²` representative,
derived from strong monotonicity and the `L²` load. -/
theorem exists_H2_interiorCutoff_of_monotone_weakEquation
    (hΩ : SobolevSpace.Boundary.C1ExtensionAtlas n Ω)
    (A : ℝ^n → ℝ^n) (hzero : A 0 = 0) {θ : ℝ} (hθ : 0 < θ)
    (hmono : ∀ z w, θ * ‖z - w‖ * ‖z - w‖ ≤ ⟪A z - A w, z - w⟫)
    {C : ℝ≥0} (hLip : LipschitzWith C A)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ Ω)
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
  obtain ⟨E, hsource, hE, hSymm, hupper, hbounded⟩ :=
    SobolevSpace.Boundary.exists_interior_translation_chart hΩ.isOpen hΩ.bounded
  have hflat (x : ℝ^n) (hx : x ∈ E.source) :
      x ∈ Ω ↔ E x ∈ HalfSpace.upper n :=
    iff_of_true (hsource ▸ hx) (hupper (E.map_source hx))
  let P := hΩ.adjoinChart E (hE.of_le (by norm_num)) (hSymm.of_le (by norm_num))
    hflat hbounded
  have hchart : P.chart (Fin.last hΩ.N) = E := Fin.lastCases_last
  apply exists_H2_physicalChartCutoff_of_monotone_weakEquation P (Fin.last hΩ.N)
    (by rw [hchart]; exact hE.of_le (by norm_num))
    (by rw [hchart]; exact hSymm.of_le (by norm_num))
    A hzero hθ hmono hLip ψ ?_
  rw [hchart, hsource]
  exact hψ

end PDE.Elliptic.Regularity.Quasilinear
