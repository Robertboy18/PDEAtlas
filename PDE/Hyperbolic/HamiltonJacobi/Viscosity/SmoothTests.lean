/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.QuadraticBarrier
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.JetOperator
public import PDE.Analysis.Calculus.SmoothContact

/-!
# Smooth tests and local C¹ viscosity tests

For a continuous Hamiltonian in finite-dimensional space, an upper
semicontinuous subsolution tested against functions smooth on its open domain
satisfies the local `C¹` test predicate. The lower semicontinuous
supersolution statement is analogous. Thus the two test conventions give
the same subsolutions and supersolutions in these classes.

The converse is immediate by restricting the tests. The other
direction uses nearby smooth contacts and continuity in both position and
momentum. It does not replace a `C¹` contact by an exact smooth contact with
the same jet; the contact lemma only needs differentiability of
the original test at its contact point.

These are local equivalences on an arbitrary open spacetime set; initial values and bounds at
spatial infinity enter comparison separately.
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi

open Set
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E]

/-- For upper semicontinuous functions on an open set, smooth
upper tests suffice for the local `C¹` subsolution predicate when the
Hamiltonian is jointly continuous in momentum and position. -/
theorem isSpatialViscositySubsolution_iff_smooth_tests {H : E → E → ℝ} {U : Set (E × ℝ)}
    {u : E × ℝ → ℝ} (hU : IsOpen U) (hu : UpperSemicontinuousOn u U)
    (hH : Continuous (fun q : E × E ↦ H q.1 q.2)) :
    IsSpatialViscositySubsolution H U u ↔ ∀ z ∈ U, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ U →
      IsLocalMaxOn (fun y ↦ u y - φ y) U z →
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1 ≤ 0 := by
  constructor
  · exact fun h z hz φ hφ hmax ↦ h.2 z hz φ ((hφ.contDiffAt (hU.mem_nhds hz)).of_le (by simp)) hmax
  · intro htest
    refine ⟨hU, fun z hz φ hφ hmax ↦ ?_⟩
    have hd := hφ.differentiableAt_one
    have h := PDE.Analysis.le_zero_of_contDiff_upper_contacts
      (Q := quadraticSize (E := E)) contDiff_quadraticSize
      (by simp [quadraticSize]) norm_sq_le_quadraticSize
      (B := 4) norm_fderiv_quadraticSize_le hU hu hz
      hd.hasFDerivAt hmax (continuous_spatialJetOperator hH).continuousAt
      (fun y hy ψ hψ hcontact ↦ by
        rw [spatialJetOperator_fderiv ((hψ.differentiable (by simp)) y)]
        exact htest y hy ψ hψ.contDiffOn hcontact)
    simpa only [spatialJetOperator_fderiv hd] using h

/-- For lower semicontinuous functions on an open set, smooth
lower tests suffice for the local `C¹` supersolution predicate when the
Hamiltonian is jointly continuous in momentum and position. -/
theorem isSpatialViscositySupersolution_iff_smooth_tests {H : E → E → ℝ} {U : Set (E × ℝ)}
    {u : E × ℝ → ℝ} (hU : IsOpen U) (hu : LowerSemicontinuousOn u U)
    (hH : Continuous (fun q : E × E ↦ H q.1 q.2)) :
    IsSpatialViscositySupersolution H U u ↔ ∀ z ∈ U, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ U →
      IsLocalMinOn (fun y ↦ u y - φ y) U z → 0 ≤
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1 := by
  constructor
  · exact fun h z hz φ hφ hmin ↦ h.2 z hz φ ((hφ.contDiffAt (hU.mem_nhds hz)).of_le (by simp)) hmin
  · intro htest
    refine ⟨hU, fun z hz φ hφ hmin ↦ ?_⟩
    have hd := hφ.differentiableAt_one
    have h := PDE.Analysis.zero_le_of_contDiff_lower_contacts
      (Q := quadraticSize (E := E)) contDiff_quadraticSize
      (by simp [quadraticSize]) norm_sq_le_quadraticSize
      (B := 4) norm_fderiv_quadraticSize_le hU hu hz
      hd.hasFDerivAt hmin (continuous_spatialJetOperator hH).continuousAt
      (fun y hy ψ hψ hcontact ↦ by
        rw [spatialJetOperator_fderiv ((hψ.differentiable (by simp)) y)]
        exact htest y hy ψ hψ.contDiffOn hcontact)
    simpa only [spatialJetOperator_fderiv hd] using h

end HamiltonJacobi

end
