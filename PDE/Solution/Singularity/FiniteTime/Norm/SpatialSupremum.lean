/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Solution.Singularity.FiniteTime.Norm.Trajectory

/-!
# Finite-time blow-up in the spatial supremum norm

Definitions and transfer theorems for finite-time blow-up measured by the pointwise spatial
supremum. The supremum takes values in `ℝ≥0∞`, so an unbounded spatial slice has value `⊤`
rather than the junk value `0` of a real `sSup`. Divergence of this extended supremum is stated
with `Tendsto`; finite-time blow-up additionally requires finite slices eventually before `T`.
Norm divergence along a spatial sample `x = sample t`, which may move with time, gives
divergence of the supremum along any filter of times
(`tendsto_spatial_sup_norm_nhds_top_of_sample`), and finite-time blow-up once the slices are
eventually finite (`SpatialSupNormBlowsUpAt.of_sample`).

The spatial type is arbitrary and the field may take values in any normed type, so the same
definitions cover scalar, complex, and vector-valued fields. This is a pointwise supremum, not
an essential supremum and not the norm of a function space; quotient spaces such as `Lᵖ` are
handled through their own norms with the trajectory predicates of `Norm.Trajectory`.
-/

@[expose] public section

namespace PDE.Solution.Singularity.FiniteTime

open Filter Topology
open scoped ENNReal

/-- The extended pointwise spatial supremum `sup_x ‖u(x,t)‖`.

The codomain `ℝ≥0∞` records an unbounded slice as `⊤`. This is not an essential supremum:
changing the field at one point may change the value. -/
noncomputable def spatialSupNorm {X E : Type*} [Norm E]
    (u : X → ℝ → E) (t : ℝ) : ℝ≥0∞ :=
  ⨆ x, ENNReal.ofReal ‖u x t‖

/-- The spatial supremum is finite eventually before `T` and tends to `⊤` as `t → T⁻`.

Finiteness is required only near `T`, with no uniform bound in time. In particular, a field whose
spatial slices are already unbounded throughout a left neighborhood of `T` does not blow up in
this sense. No PDE solution predicate is part of the definition: equation modules establish
the equation and blow-up separately. -/
def SpatialSupNormBlowsUpAt {X E : Type*} [Norm E]
    (u : X → ℝ → E) (T : ℝ) : Prop :=
  Tendsto (spatialSupNorm u) (nhdsWithin T (Set.Iio T)) (nhds ⊤) ∧
    ∀ᶠ t in nhdsWithin T (Set.Iio T), spatialSupNorm u t ≠ ⊤

/-- Every pointwise norm, embedded in `ℝ≥0∞`, is bounded by the spatial supremum. -/
theorem ofReal_norm_le_spatial_sup_norm {X E : Type*} [Norm E]
    (u : X → ℝ → E) (t : ℝ) (x : X) :
    ENNReal.ofReal ‖u x t‖ ≤ spatialSupNorm u t :=
  le_iSup (fun y ↦ ENNReal.ofReal ‖u y t‖) x

/-- A spatial slice has finite supremum exactly when its pointwise norms have a real bound. -/
theorem spatial_sup_norm_ne_top_iff {X E : Type*} [Norm E]
    (u : X → ℝ → E) (t : ℝ) :
    spatialSupNorm u t ≠ ⊤ ↔ ∃ C : ℝ, ∀ x, ‖u x t‖ ≤ C := by
  constructor
  · intro hfinite
    exact ⟨(spatialSupNorm u t).toReal, fun x ↦
      (ENNReal.ofReal_le_iff_le_toReal hfinite).mp
        (ofReal_norm_le_spatial_sup_norm u t x)⟩
  · rintro ⟨C, hC⟩
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (iSup_le fun x ↦ ENNReal.ofReal_le_ofReal (hC x))

/-- Slices that are already unbounded eventually before `T` exclude finite-time blow-up. -/
theorem not_spatial_sup_norm_blows_up_at_of_eventually_eq_top
    {X E : Type*} [Norm E] {u : X → ℝ → E} {T : ℝ}
    (hunbounded : ∀ᶠ t in nhdsWithin T (Set.Iio T), spatialSupNorm u t = ⊤) :
    ¬ SpatialSupNormBlowsUpAt u T := by
  intro h
  obtain ⟨t, hfinite, htop⟩ := (h.2.and hunbounded).exists
  exact hfinite htop

/-- Norm blow-up along a possibly moving spatial sample forces divergence of the spatial
supremum norm.

Allowing the sample point to depend on time is useful for similarity profiles: a fixed profile
coordinate corresponds to a moving physical point as the spatial scale changes. -/
theorem tendsto_spatial_sup_norm_nhds_top_of_sample
    {X E : Type*} [Norm E] {l : Filter ℝ}
    {u : X → ℝ → E} (sample : ℝ → X)
    (hsample : Tendsto (fun t ↦ ‖u (sample t) t‖) l atTop) :
    Tendsto (spatialSupNorm u) l (nhds ⊤) := by
  exact tendsto_nhds_top_mono
    (ENNReal.tendsto_ofReal_nhds_top.mpr hsample)
    (Eventually.of_forall fun t ↦
      ofReal_norm_le_spatial_sup_norm u t (sample t))

/-- A diverging spatial sample proves blow-up when the spatial slices are eventually finite. -/
theorem SpatialSupNormBlowsUpAt.of_sample
    {X E : Type*} [Norm E] {u : X → ℝ → E} {T : ℝ}
    (sample : ℝ → X)
    (hfinite : ∀ᶠ t in nhdsWithin T (Set.Iio T), spatialSupNorm u t ≠ ⊤)
    (hsample : NormBlowsUpAt (fun t ↦ u (sample t) t) T) :
    SpatialSupNormBlowsUpAt u T :=
  ⟨tendsto_spatial_sup_norm_nhds_top_of_sample sample hsample, hfinite⟩

end PDE.Solution.Singularity.FiniteTime
