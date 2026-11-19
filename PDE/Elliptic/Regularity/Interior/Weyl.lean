/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Weyl.LocalRepresentative
import PDE.Elliptic.Regularity.Interior.Weyl.Gluing

/-!
# Weyl regularity for locally integrable distributional solutions

On an arbitrary open subset of positive-dimensional Euclidean space, a locally integrable
distributional solution of Laplace's equation has a classical harmonic representative.
The equality is almost everywhere: changing the original function at isolated points does not
change the conclusion. The interior smoothness theorem applies to the representative.
-/

@[expose] public section

open PDE (laplacian)

open MeasureTheory TopologicalSpace
open scoped Distributions

namespace LaplacianEquation

/-- Weyl's lemma for scalar `L¹_loc` data on an arbitrary open Euclidean domain.
Distributional harmonicity is tested against compactly supported smooth test functions.
No continuity, boundary regularity, or global integrability of the data is assumed. -/
theorem exists_isHarmonicPDE_ae_eq_of_integral_laplacian_eq_zero
    {n : ℕ} [Fact (0 < n)] {Ω : Opens (ℝ^n)} {u : ℝ^n → ℝ}
    (hu : LocallyIntegrableOn u Ω volume)
    (hweak : ∀ φ : 𝓓(Ω, ℝ), (∫ y, u y * laplacian (φ : ℝ^n → ℝ) y) = 0) :
    ∃ h : ℝ^n → ℝ, IsHarmonicPDE n h Ω ∧ u =ᵐ[volume.restrict Ω] h := by
  apply exists_isHarmonicPDE_ae_eq_of_locally
  intro x hx
  obtain ⟨R, hR, hRΩ, v, hv, huv⟩ :=
    exists_isHarmonicPDE_ae_eq_on_ball_of_integral_laplacian_eq_zero hu hweak hx
  exact ⟨Metric.ball x R, Metric.isOpen_ball, Metric.mem_ball_self hR, hRΩ, v, hv, huv⟩

end LaplacianEquation
