/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.TransportCone
public import PDE.Analysis.Calculus.LocalExtension.Ball
import PDE.Analysis.Calculus.Divergence.Continuity
import PDE.Analysis.Calculus.Divergence.Locality

/-!
# Localizing the ball divergence theorem

Finite-order regularity at every point of the closed ball suffices for Gauss.
A compact extension preserves germs on the ball, and
`ballIntegral_divergence_eq_sphereIntegral_inner_normal` then supplies both the flux
identity and integrability.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.RadialSquareFlux

open MeasureTheory Metric Set Filter
open scoped Topology RealInnerProductSpace

variable {n : ℕ}

/-- Extend C¹ germs on a closed ball without altering any germ on that ball. -/
theorem exists_contDiff_eq_near_closedBall {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ^n → F} {c : ℝ^n} {r : ℝ} (hr : 0 < r)
    (hf : ∀ x ∈ closedBall c r, ContDiffAt ℝ 1 f x) :
    ∃ g : ℝ^n → F, ContDiff ℝ 1 g ∧
      ∀ x ∈ closedBall c r, g =ᶠ[𝓝 x] f := by
  let Ω := {x | ContDiffAt ℝ 1 f x}
  have hΩ : IsOpen Ω := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact (show ContDiffAt ℝ 1 f x from hx).eventually (by simp)
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall c r).exists_cthickening_subset_open hΩ hf
  rw [cthickening_closedBall hδ.le hr.le] at hsub
  have hfΩ : ContDiffOn ℝ 1 f Ω := fun x hx ↦ (show ContDiffAt ℝ 1 f x from hx).contDiffWithinAt
  obtain ⟨g, hg, _, _, heq⟩ := hfΩ.exists_contDiff_tsupport_subset_eqOn_closedBall hΩ
    (r := r + δ / 2) (R := δ + r) (by positivity) (by linarith) hsub
  refine ⟨g, hg, fun x hx ↦ ?_⟩
  have hx' : x ∈ ball c (r + δ / 2) := by
    apply (closedBall_subset_ball (by linarith : r < r + δ / 2)) hx
  filter_upwards [isOpen_ball.mem_nhds hx'] with y hy
  exact heq (ball_subset_closedBall hy)

/-- Gauss on a closed ball only needs C¹ regularity near its points. -/
theorem gauss_of_contDiffAt_closedBall [Fact (0 < n)]
    {F : ℝ^n → ℝ^n} {c : ℝ^n} {r : ℝ} (hr : 0 < r)
    (hF : ∀ x ∈ closedBall c r, ContDiffAt ℝ 1 F x) :
    IntegrableOn (∇· F) (ball c r) ∧
      (∫ x in ball c r, ∇· F x) =
        sphereIntegral n (fun x ↦ ⟪F x, NormedSpace.normalize (x - c)⟫) c r := by
  obtain ⟨G, hG, heq⟩ := exists_contDiff_eq_near_closedBall hr hF
  have hae : (∇· G) =ᵐ[volume.restrict (ball c r)] ∇· F := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
    exact (heq x (ball_subset_closedBall hx)).divergence_eq
  refine ⟨((hG.continuous_divergence.continuousOn.integrableOn_compact
    (isCompact_closedBall c r)).mono_set ball_subset_closedBall).congr hae, ?_⟩
  rw [← integral_congr_ae hae]
  change ballIntegral n (∇· G) c r = _
  rw [ballIntegral_divergence_eq_sphereIntegral_inner_normal hG c hr]
  apply sphereIntegral_congr_on_sphere hr
  intro x hx
  change ⟪G x, _⟫ = ⟪F x, _⟫
  rw [(heq x (sphere_subset_closedBall hx)).eq_of_nhds]

end PDE.Analysis.RadialSquareFlux
