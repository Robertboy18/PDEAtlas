/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.RealL2.Geometry
public import PDE.Analysis.MeasureTheory.Lp.RealL2
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.WeakConvergence

/-!
# Support, oddness, and mass of real H¹ limits

A uniform H¹ bound constructs the graph of a strong L² limit. Its continuous
representative inherits a common compact support and oddness from the
approximants. Continuity also forces zero values at the support endpoints.

A positive lower bound on the L² norm prevents the limit from vanishing.
Closeness to a fixed reference supplies such a bound when the error radius
is smaller than the reference norm. Both constructions retain the resulting
quantitative lower bound for the square integral.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology Sobolev

namespace SobolevSpace.GraphSpace

/-- An exterior a.e. zero condition gives closed support for the continuous representative. -/
theorem tsupport_realLineRepresentative_subset_of_ae
    (U : W^{1,2}(ℝ^1)) {K : Set ℝ} (hK : IsClosed K)
    (hsupport : (realLineCoordinateCLM (baseIndex 1 1) U : ℝ → ℝ)
      =ᵐ[volume.restrict Kᶜ] 0) :
    tsupport (realLineRepresentative U) ⊆ K := by
  have hrep := ae_restrict_of_ae (s := Kᶜ) (realLineCoordinate_ae_representative U)
  have hzero : realLineRepresentative U =ᵐ[volume.restrict Kᶜ] (0 : ℝ → ℝ) :=
    (EventuallyEq.symm hrep).trans hsupport
  have heq := Measure.eqOn_open_of_ae_eq hzero hK.isOpen_compl
    (continuous_realLineRepresentative U).continuousOn continuous_const.continuousOn
  apply closure_minimal _ hK
  intro x hx
  by_contra hnot
  exact hx (heq hnot)

/-- Almost-everywhere oddness of the base gives oddness of its continuous representative. -/
theorem odd_realLineRepresentative_of_ae (U : W^{1,2}(ℝ^1))
    (hodd : ∀ᵐ x ∂volume, realLineCoordinateCLM (baseIndex 1 1) U (-x) =
      -realLineCoordinateCLM (baseIndex 1 1) U x) :
    Function.Odd (realLineRepresentative U) := by
  have hreflect := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving
    |>.ae_eq_comp (realLineCoordinate_ae_representative U)
  have hae : (fun x ↦ realLineRepresentative U (-x)) =ᵐ[volume]
      (fun x ↦ -realLineRepresentative U x) := by
    filter_upwards [hodd, hreflect, realLineCoordinate_ae_representative U] with x hx hn hp
    exact hn.symm.trans (hx.trans (congrArg Neg.neg hp))
  exact congrFun (Measure.eq_of_ae_eq hae
    ((continuous_realLineRepresentative U).comp continuous_neg)
    (continuous_realLineRepresentative U).neg)

/-- A common closed support enclosure passes from strongly convergent L² bases to the H¹ limit. -/
theorem tsupport_realLineRepresentative_subset_of_L2_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → W^{1,2}(ℝ^1)} {U : W^{1,2}(ℝ^1)} {K : Set ℝ}
    (hbase : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (u i)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) U)))
    (hK : IsClosed K)
    (hsupport : ∀ᶠ i in l,
      (realLineCoordinateCLM (baseIndex 1 1) (u i) : ℝ → ℝ) =ᵐ[volume.restrict Kᶜ] 0) :
    tsupport (realLineRepresentative U) ⊆ K :=
  tsupport_realLineRepresentative_subset_of_ae U hK
    (Lp.ae_eq_zero_restrict_of_tendsto_L2 hbase hsupport)

/-- Oddness passes through strong convergence of real L² bases to the H¹ representative. -/
theorem odd_realLineRepresentative_of_L2_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → W^{1,2}(ℝ^1)} {U : W^{1,2}(ℝ^1)}
    (hbase : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (u i)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) U)))
    (hodd : ∀ᶠ i in l, ∀ᵐ x ∂volume,
      realLineCoordinateCLM (baseIndex 1 1) (u i) (-x) =
        -realLineCoordinateCLM (baseIndex 1 1) (u i) x) :
    Function.Odd (realLineRepresentative U) :=
  odd_realLineRepresentative_of_ae U (Lp.ae_odd_of_tendsto_L2 hbase hodd)

/-- A common interval enclosure gives zero values at both endpoints and outside the interval. -/
theorem realLineRepresentative_eq_zero_outside_Ioo_of_L2_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → W^{1,2}(ℝ^1)} {U : W^{1,2}(ℝ^1)} {a b x : ℝ}
    (hbase : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (u i)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) U)))
    (hsupport : ∀ᶠ i in l,
      (realLineCoordinateCLM (baseIndex 1 1) (u i) : ℝ → ℝ)
        =ᵐ[volume.restrict (Icc a b)ᶜ] 0)
    (hx : x ∉ Ioo a b) : realLineRepresentative U x = 0 := by
  have hs := tsupport_realLineRepresentative_subset_of_L2_tendsto hbase isClosed_Icc hsupport
  have hopen := (continuous_realLineRepresentative U).isOpen_support
  have hsub : Function.support (realLineRepresentative U) ⊆ interior (Icc a b) :=
    hopen.subset_interior_iff.mpr ((subset_tsupport _).trans hs)
  rw [interior_Icc] at hsub
  by_contra hne
  exact hx (hsub hne)

/-- The square integral of the representative is the squared norm of its real L² class. -/
theorem integral_sq_realLineRepresentative_eq (U : W^{1,2}(ℝ^1)) :
    (∫ x, realLineRepresentative U x ^ 2) =
      ‖realLineCoordinateCLM (baseIndex 1 1) U‖ ^ 2 := by
  rw [integral_sq_eq_eLpNorm_toReal_sq (memLp_realLineRepresentative U),
    ← Lp.norm_toLp _ (memLp_realLineRepresentative U), toLp_realLineRepresentative]

/-- A positive L² lower bound along the family prevents the continuous limit from vanishing. -/
theorem realLineRepresentative_ne_zero_of_L2_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → W^{1,2}(ℝ^1)} {U : W^{1,2}(ℝ^1)} {δ : ℝ}
    (hbase : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (u i)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) U)))
    (hδ : 0 < δ)
    (hlower : ∀ᶠ i in l, δ ≤ ‖realLineCoordinateCLM (baseIndex 1 1) (u i)‖) :
    realLineRepresentative U ≠ 0 := by
  have hnorm : 0 < ‖realLineCoordinateCLM (baseIndex 1 1) U‖ :=
    hδ.trans_le (ge_of_tendsto hbase.norm hlower)
  intro hzero
  have hbasezero : realLineCoordinateCLM (baseIndex 1 1) U = 0 := by
    apply Lp.ext
    exact (realLineCoordinate_ae_representative U).trans
      (hzero ▸ (Lp.coeFn_zero ℝ 2 volume).symm)
  exact (norm_pos_iff.mp hnorm) hbasezero

/-- The L² norm floor gives the same square-integral floor for the continuous limit. -/
theorem integral_sq_realLineRepresentative_ge_of_L2_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → W^{1,2}(ℝ^1)} {U : W^{1,2}(ℝ^1)} {δ : ℝ}
    (hbase : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (u i)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) U)))
    (hδ : 0 ≤ δ)
    (hlower : ∀ᶠ i in l, δ ≤ ‖realLineCoordinateCLM (baseIndex 1 1) (u i)‖) :
    δ ^ 2 ≤ ∫ x, realLineRepresentative U x ^ 2 := by
  rw [integral_sq_realLineRepresentative_eq]
  exact (sq_le_sq₀ hδ (norm_nonneg _)).mpr (ge_of_tendsto hbase.norm hlower)

/-- Strong L² convergence and a bounded H¹ family construct a nonzero, odd, compactly
supported continuous representative. The support and norm floor concern only the family. -/
theorem exists_odd_compact_nonzero_h1_of_L2_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (u : ι → W^{1,2}(ℝ^1)) (F : Lp ℝ 2 (volume : Measure ℝ))
    {B δ : ℝ} {K : Set ℝ} (hbound : ∀ i, ‖u i‖ ≤ B)
    (hbase : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (u i)) l (𝓝 F))
    (hK : IsCompact K)
    (hsupport : ∀ᶠ i in l,
      (realLineCoordinateCLM (baseIndex 1 1) (u i) : ℝ → ℝ) =ᵐ[volume.restrict Kᶜ] 0)
    (hodd : ∀ᶠ i in l, ∀ᵐ x ∂volume,
      realLineCoordinateCLM (baseIndex 1 1) (u i) (-x) =
        -realLineCoordinateCLM (baseIndex 1 1) (u i) x)
    (hδ : 0 < δ)
    (hlower : ∀ᶠ i in l, δ ≤ ‖realLineCoordinateCLM (baseIndex 1 1) (u i)‖) :
    ∃ U : W^{1,2}(ℝ^1), ‖U‖ ≤ B ∧ realLineCoordinateCLM (baseIndex 1 1) U = F ∧
      Continuous (realLineRepresentative U) ∧
      tsupport (realLineRepresentative U) ⊆ K ∧
      HasCompactSupport (realLineRepresentative U) ∧
      Function.Odd (realLineRepresentative U) ∧ realLineRepresentative U ≠ 0 ∧
      δ ^ 2 ≤ ∫ x, realLineRepresentative U x ^ 2 := by
  obtain ⟨U, hU, hUF⟩ := exists_h1_of_tendsto_realLineCoordinate u F hbound hbase
  have hconv : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (u i)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) U)) := hUF ▸ hbase
  have hs := tsupport_realLineRepresentative_subset_of_L2_tendsto hconv hK.isClosed hsupport
  exact ⟨U, hU, hUF, continuous_realLineRepresentative U, hs,
    hK.of_isClosed_subset (isClosed_tsupport _) hs,
    odd_realLineRepresentative_of_L2_tendsto hconv hodd,
    realLineRepresentative_ne_zero_of_L2_tendsto hconv hδ hlower,
    integral_sq_realLineRepresentative_ge_of_L2_tendsto hconv hδ.le hlower⟩

/-- Uniform L² closeness to a fixed reference retains a positive quantitative mass floor
when the error radius is strictly smaller than the reference norm. -/
theorem exists_odd_compact_nonzero_h1_of_L2_tendsto_reference
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (u : ι → W^{1,2}(ℝ^1)) (F R : Lp ℝ 2 (volume : Measure ℝ))
    {B ε : ℝ} {K : Set ℝ} (hbound : ∀ i, ‖u i‖ ≤ B)
    (hbase : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (u i)) l (𝓝 F))
    (hK : IsCompact K)
    (hsupport : ∀ᶠ i in l,
      (realLineCoordinateCLM (baseIndex 1 1) (u i) : ℝ → ℝ) =ᵐ[volume.restrict Kᶜ] 0)
    (hodd : ∀ᶠ i in l, ∀ᵐ x ∂volume,
      realLineCoordinateCLM (baseIndex 1 1) (u i) (-x) =
        -realLineCoordinateCLM (baseIndex 1 1) (u i) x)
    (hε : ε < ‖R‖)
    (hclose : ∀ᶠ i in l, ‖realLineCoordinateCLM (baseIndex 1 1) (u i) - R‖ ≤ ε) :
    ∃ U : W^{1,2}(ℝ^1), ‖U‖ ≤ B ∧ realLineCoordinateCLM (baseIndex 1 1) U = F ∧
      Continuous (realLineRepresentative U) ∧
      tsupport (realLineRepresentative U) ⊆ K ∧
      HasCompactSupport (realLineRepresentative U) ∧
      Function.Odd (realLineRepresentative U) ∧ realLineRepresentative U ≠ 0 ∧
      (‖R‖ - ε) ^ 2 ≤ ∫ x, realLineRepresentative U x ^ 2 := by
  apply exists_odd_compact_nonzero_h1_of_L2_tendsto u F hbound hbase hK hsupport hodd
    (sub_pos.mpr hε)
  filter_upwards [hclose] with i hi
  have hnorm := norm_sub_norm_le R (realLineCoordinateCLM (baseIndex 1 1) (u i))
  rw [norm_sub_rev] at hnorm
  linarith

end SobolevSpace.GraphSpace
