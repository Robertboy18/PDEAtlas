/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Flux.SourceIdentity
public import PDE.Spaces.Sobolev.Calculus.Pullback.Divergence.Piola

/-!
# The weak flux equation in a boundary chart

The physical weak equation transports to the target with its Piola
flux and volume-weighted load. The formula applies to any square-integrable
flux, and therefore to nonlinear fluxes before their weak derivatives have
been recovered.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace PDE.Elliptic.Regularity.Boundary

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.WeakChangeOfVariables
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- Transport of `-div q = f` to the chart target, tested against an ordinary
smooth test. Both the matrix and the determinant are chart derivatives. -/
theorem weakFlux_chartPullback_target_identity
    (hΩ : SobolevSpace.Boundary.C1ExtensionAtlas n Ω) (a : Fin hΩ.N)
    (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω)
    (hweak : ∀ v : H¹₀(Ω),
      (∑ i, ⟪q i, derivCoordCLM i v⟫) = ⟪f, baseCoordCLM v⟫)
    (φ : TestFunctionOn n
      (SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ (Ω := Ω) a).target) :
    let E := SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ (Ω := Ω) a
    (∫ y in E.target,
      ⟪piolaTransform E (fun x ↦ WithLp.toLp 2 (fun i ↦ q i x)) y,
        WithLp.toLp 2 (fun j ↦ (∂[j] φ.1.toFun) y)⟫) =
      ∫ y in E.target,
        (|(fderiv ℝ (fun z ↦ E.symm z) y).det| * f (E.symm y)) * φ.1.toFun y := by
  let E := SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ (Ω := Ω) a
  have hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y) := by
    simpa [E, SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using
      hΩ.chart_symm_contDiff a
  dsimp only
  rw [← integral_source_flux_pairing_eq E hSymm,
    ← integral_source_load_pairing_eq E hSymm]
  simp only [inner_adjoint_eq_sum_coordinates]
  exact weakFlux_chartPullback_source_identity hΩ a q f hweak φ

end PDE.Elliptic.Regularity.Boundary
