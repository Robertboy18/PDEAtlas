/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Representative

/-!
# Uniform convergence and support of real H¹ representatives

The one-dimensional Sobolev estimate controls every point with the same
constant. Bundling the continuous representative as a bounded continuous
function therefore turns H¹ convergence into uniform convergence on the
whole line. A common closed support enclosure and oddness pass to the limit.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology BoundedContinuousFunction Sobolev

namespace SobolevSpace.GraphSpace

/-- The real continuous H¹ representative, equipped with its global bound. -/
def realLineBoundedRepresentative (U : W^{1,2}(ℝ^1)) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (realLineRepresentative U)
    (continuous_realLineRepresentative U) (2 * ‖U‖)
    (norm_realLineRepresentative_le U)

/-- Bundling the representative does not change its pointwise values. -/
@[simp] theorem coe_realLineBoundedRepresentative (U : W^{1,2}(ℝ^1)) :
    (realLineBoundedRepresentative U : ℝ → ℝ) = realLineRepresentative U := rfl

/-- The uniform distance between representatives is bounded by their H¹ distance. -/
theorem norm_realLineBoundedRepresentative_sub_le (U V : W^{1,2}(ℝ^1)) :
    ‖realLineBoundedRepresentative U - realLineBoundedRepresentative V‖ ≤
      2 * ‖U - V‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  have h := norm_realLineRepresentative_le (U - V) x
  rw [realLineRepresentative_sub] at h
  exact h

/-- The real H¹ representative map is globally Lipschitz into the uniform norm. -/
theorem lipschitzWith_realLineBoundedRepresentative :
    LipschitzWith 2 realLineBoundedRepresentative := by
  apply LipschitzWith.of_dist_le_mul
  intro U V
  simpa only [dist_eq_norm, NNReal.coe_ofNat] using
    norm_realLineBoundedRepresentative_sub_le U V

/-- H¹ convergence gives uniform convergence of the continuous representatives. -/
theorem tendsto_realLineBoundedRepresentative
    {ι : Type*} {l : Filter ι} {u : ι → W^{1,2}(ℝ^1)} {U : W^{1,2}(ℝ^1)}
    (hu : Tendsto u l (𝓝 U)) :
    Tendsto (fun i ↦ realLineBoundedRepresentative (u i)) l
      (𝓝 (realLineBoundedRepresentative U)) :=
  (lipschitzWith_realLineBoundedRepresentative.continuous.tendsto U).comp hu

/-- Oddness of an H¹ convergent family passes to the continuous limit. -/
theorem odd_realLineRepresentative_of_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → W^{1,2}(ℝ^1)} {U : W^{1,2}(ℝ^1)}
    (hu : Tendsto u l (𝓝 U))
    (hodd : ∀ᶠ i in l, Function.Odd (realLineRepresentative (u i))) :
    Function.Odd (realLineRepresentative U) := by
  intro x
  have hx := ((lipschitzWith_realLineRepresentative_eval x).continuous.tendsto U).comp hu
  have hn := ((lipschitzWith_realLineRepresentative_eval (-x)).continuous.tendsto U).comp hu
  apply tendsto_nhds_unique hn
  apply hx.neg.congr'
  filter_upwards [hodd] with i hi
  exact (hi x).symm

/-- A common closed support enclosure survives an H¹ limit, pointwise rather
than merely almost everywhere. -/
theorem tsupport_realLineRepresentative_subset_of_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → W^{1,2}(ℝ^1)} {U : W^{1,2}(ℝ^1)} {K : Set ℝ}
    (hu : Tendsto u l (𝓝 U)) (hK : IsClosed K)
    (hsupport : ∀ᶠ i in l, Function.support (realLineRepresentative (u i)) ⊆ K) :
    tsupport (realLineRepresentative U) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hnot
  have hzero : realLineRepresentative U x = 0 := by
    apply realLineRepresentative_limit_value hu
    filter_upwards [hsupport] with i hi
    by_contra hne
    exact hnot (hi hne)
  exact hx hzero

/-- Compactness of the common enclosure gives compact support of the limit. -/
theorem hasCompactSupport_realLineRepresentative_of_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → W^{1,2}(ℝ^1)} {U : W^{1,2}(ℝ^1)} {K : Set ℝ}
    (hu : Tendsto u l (𝓝 U)) (hK : IsCompact K)
    (hsupport : ∀ᶠ i in l, Function.support (realLineRepresentative (u i)) ⊆ K) :
    HasCompactSupport (realLineRepresentative U) :=
  hK.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_realLineRepresentative_subset_of_tendsto hu hK.isClosed hsupport)

end SobolevSpace.GraphSpace
