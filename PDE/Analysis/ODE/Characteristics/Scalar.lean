/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.InverseFunction.Parameter
public import PDE.Analysis.ODE.SmoothDependence.Nonautonomous
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Local first integrals of scalar characteristic equations

Invert the initial-data map of the local family solving `y' = c(s,y)`.
The inverse label is C² and constant along the constructed characteristics.
Differentiating the inverse law proves its transport equation with the actual
Fréchet derivative. The elapsed-time coordinate has origin `s₀`.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace PDE.Analysis.ODE

/-- A C² scalar nonautonomous equation constructs a C² characteristic label.
The label equals the initial position at elapsed time zero and its derivative
annihilates the characteristic direction `(1,c(s₀+t,y))` near the base point. -/
theorem exists_local_characteristic_label
    {c : ℝ × ℝ → ℝ} {s₀ y₀ : ℝ} (hc : ContDiffAt ℝ 2 c (s₀, y₀)) :
    ∃ ξ : ℝ × ℝ → ℝ, ContDiffAt ℝ 2 ξ (0, y₀) ∧
      ((fun y ↦ ξ (0, y)) =ᶠ[𝓝 y₀] id) ∧
      (∀ᶠ p : ℝ × ℝ in 𝓝 (0, y₀),
        fderiv ℝ ξ p (1, c (s₀ + p.1, p.2)) = 0) := by
  obtain ⟨Φ, hΦ, hΦ₀, hode⟩ := exists_local_contDiff_two_nonautonomous_family hc
  let ξ : ℝ × ℝ → ℝ := fun p ↦ localSpatialInverse hΦ hΦ₀ p.1 p.2
  have hξ : ContDiffAt ℝ 2 ξ (0, y₀) := contDiffAt_localSpatialInverse hΦ hΦ₀
  have hξ₀ : ξ (0, y₀) = y₀ := localSpatialInverse_zero_apply hΦ hΦ₀
  have hleft : (fun p : ℝ × ℝ ↦ ξ (p.1, Φ p.1 p.2)) =ᶠ[𝓝 (0, y₀)] Prod.snd :=
    localSpatialInverse_left_inverse hΦ hΦ₀
  have hregular : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, y₀),
      ContDiffAt ℝ 2 ξ (p.1, Φ p.1 p.2) := by
    have ht : ContinuousAt (fun p : ℝ × ℝ ↦ (p.1, Φ p.1 p.2)) (0, y₀) :=
      continuousAt_fst.prodMk hΦ.continuousAt
    have ht' : Tendsto (fun p : ℝ × ℝ ↦ (p.1, Φ p.1 p.2))
        (𝓝 (0, y₀)) (𝓝 (0, y₀)) := by
      change Tendsto _ _ (𝓝 (0, Φ 0 y₀)) at ht
      simpa only [hΦ₀.eq_of_nhds, id_eq] using ht
    exact ht'.eventually (hξ.eventually (by norm_num))
  have hforward : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, y₀),
      fderiv ℝ ξ (p.1, Φ p.1 p.2) (1, c (s₀ + p.1, Φ p.1 p.2)) = 0 := by
    filter_upwards [hleft.eventuallyEq_nhds, hode, hregular] with p hp hsol hreg
    have hpath : (fun t ↦ ξ (t, Φ t p.2)) =ᶠ[𝓝 p.1] (fun _ ↦ p.2) :=
      hp.comp_tendsto (continuousAt_id.prodMk continuousAt_const)
    have hd := (hreg.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk hsol)
    exact hd.unique ((hasDerivAt_const p.1 p.2).congr_of_eventuallyEq hpath)
  refine ⟨ξ, hξ, localSpatialInverse_zero hΦ hΦ₀, ?_⟩
  have hback : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, y₀),
      fderiv ℝ ξ (p.1, Φ p.1 (ξ p)) (1, c (s₀ + p.1, Φ p.1 (ξ p))) = 0 := by
    have ht : ContinuousAt (fun p : ℝ × ℝ ↦ (p.1, ξ p)) (0, y₀) :=
      continuousAt_fst.prodMk hξ.continuousAt
    exact ht.eventually (by simpa only [hξ₀] using hforward)
  filter_upwards [hback, localSpatialInverse_right_inverse hΦ hΦ₀] with p hp heq
  change Φ p.1 (ξ p) = p.2 at heq
  simpa only [heq] using hp

end PDE.Analysis.ODE
