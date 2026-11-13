/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Characteristics.RescaledSupport
import CAS.ExactTactic

/-!
# Derivative bounds and physical support evolution

A bound on the spatial velocity derivative yields global spatial Lipschitz control
by the mean value theorem. On a finite time interval the continuous spatial rate is
bounded, so the rescaled transport velocity `U + cl x` also has a uniform Lipschitz
constant, which is the hypothesis of `rescaled_vorticity_support_subset`.

Nonzero amplitude and spatial scales give an exact identity between physical support
and the dilation of rescaled support. A positive spatial scale therefore turns fixed
rescaled support in `[-L, L]` into physical support in `[-Cl(τ) L, Cl(τ) L]`.
-/

@[expose] public section

noncomputable section

open Set
open PDE.Representations.Similarity

namespace DeGregorio

/-- A bounded spatial derivative controls the Lipschitz constant of the transport
velocity after adding the linear rescaling drift. -/
theorem lipschitzWith_rescaled_velocity_of_deriv_bound
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) {M : NNReal}
    (hbound : ∀ x, ‖deriv u x‖₊ ≤ M) (cl : ℝ) :
    LipschitzWith (M + ‖cl‖₊) (fun x ↦ u x + cl * x) := by
  have hd (x : ℝ) : HasDerivAt (fun y ↦ u y + cl * y) (deriv u x + cl) x := by
    convert! (hu x).hasDerivAt.add ((hasDerivAt_id x).const_mul cl) using 1
    simp
  apply lipschitzWith_of_nnnorm_deriv_le (fun x ↦ (hd x).differentiableAt)
  intro x
  rw [(hd x).deriv]
  exact (nnnorm_add_le _ _).trans (add_le_add (hbound x) le_rfl)

/-- A uniform velocity-derivative bound and a continuous rate give a uniform global
Lipschitz constant for the transport velocity on each prescribed finite time interval. -/
theorem exists_lipschitzWith_rescaled_velocity_on_Icc
    {u : ℝ → ℝ → ℝ} {cl : ℝ → ℝ} {t₀ T : ℝ}
    (hu : ContDiff ℝ 1 (Function.uncurry u)) (hcl : Continuous cl)
    (M : NNReal)
    (hbound : ∀ x t, t ∈ Icc t₀ T → ‖deriv (fun y ↦ u y t) x‖₊ ≤ M) :
    ∃ K : NNReal, ∀ t ∈ Icc t₀ T, LipschitzWith K (fun x ↦ u x t + cl t * x) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcl.continuousOn
  let N : NNReal := ⟨max C 0, le_max_right _ _⟩
  refine ⟨M + N, ?_⟩
  intro t ht
  have hslice : Differentiable ℝ (fun x ↦ u x t) :=
    (hu.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
  have hrate : ‖cl t‖₊ ≤ N :=
    NNReal.coe_le_coe.mp ((hC t ht).trans (le_max_left C 0))
  exact (lipschitzWith_rescaled_velocity_of_deriv_bound hslice
    (fun x ↦ hbound x t ht) (cl t)).weaken (add_le_add le_rfl hrate)

/-- Support in `[-L, L]` is preserved when the spatial velocity derivative is uniformly
bounded on the time interval. -/
theorem rescaled_vorticity_support_subset_of_deriv_bound
    {fields : Fields} {cl cw : ℝ → ℝ} {t₀ T L : ℝ}
    (hu : ContDiff ℝ 1 (Function.uncurry fields.velocity))
    (hcl : Continuous cl) (hcw : Continuous cw)
    (M : NNReal)
    (hbound : ∀ x t, t ∈ Icc t₀ T →
      ‖deriv (fun y ↦ fields.velocity y t) x‖₊ ≤ M)
    (hleft : ∀ t ∈ Icc t₀ T, fields.velocity (-L) t + cl t * (-L) = 0)
    (hright : ∀ t ∈ Icc t₀ T, fields.velocity L t + cl t * L = 0)
    (hregularity : HasClassicalRegularityOn fields (Icc t₀ T))
    (htransport : SatisfiesRescaledTransportEquationOn 1 fields cl cw (Icc t₀ T))
    (hinitial : Function.support (fun x ↦ fields.vorticity x t₀) ⊆ Icc (-L) L) :
    ∀ t ∈ Icc t₀ T,
      Function.support (fun x ↦ fields.vorticity x t) ⊆ Icc (-L) L := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_rescaled_velocity_on_Icc hu hcl M hbound
  exact rescaled_vorticity_support_subset hu hcl hcw K hK hleft hright
    hregularity htransport hinitial

/-- For nonzero scales, the physical support at time `t(τ)` is the image of the
rescaled support under `x ↦ Cl(τ) x`. -/
theorem physical_vorticity_support_eq_image
    (data : DynamicRescalingData) (fields : Fields) (τ : ℝ)
    (hamplitude : data.vorticityScale τ ≠ 0) (hspace : data.spatialScale τ ≠ 0) :
    Function.support (fun y ↦ fields.vorticity y (data.physicalTime τ)) =
      (fun x ↦ data.spatialScale τ * x) ''
        Function.support (fun x ↦ (dynamicallyRescaledFields data fields).vorticity x τ) := by
  ext y
  constructor
  · intro hy
    have hcancel : data.spatialScale τ * (y / data.spatialScale τ) = y := by
      cas using hspace
    refine ⟨y / data.spatialScale τ, ?_, hcancel⟩
    change (dynamicallyRescaledFields data fields).vorticity (y / data.spatialScale τ) τ ≠ 0
    unfold dynamicallyRescaledFields dynamicPullback
    simpa only [smul_eq_mul, hcancel] using mul_ne_zero hamplitude hy
  · rintro ⟨x, hx, rfl⟩
    change (dynamicallyRescaledFields data fields).vorticity x τ ≠ 0 at hx
    unfold dynamicallyRescaledFields dynamicPullback at hx
    exact (mul_ne_zero_iff.mp hx).2

/-- Fixed rescaled support is equivalent to the corresponding moving physical support
enclosure when the amplitude is nonzero and the spatial scale is positive. -/
theorem rescaled_vorticity_support_subset_iff_physical
    (data : DynamicRescalingData) (fields : Fields) (τ L : ℝ)
    (hamplitude : data.vorticityScale τ ≠ 0) (hspace : 0 < data.spatialScale τ) :
    Function.support (fun x ↦ (dynamicallyRescaledFields data fields).vorticity x τ) ⊆
        Icc (-L) L ↔
      Function.support (fun y ↦ fields.vorticity y (data.physicalTime τ)) ⊆
        Icc (-(data.spatialScale τ * L)) (data.spatialScale τ * L) := by
  rw [physical_vorticity_support_eq_image data fields τ hamplitude hspace.ne']
  constructor
  · intro hrescaled y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hbounds := hrescaled hx
    constructor
    · simpa only [mul_neg] using mul_le_mul_of_nonneg_left hbounds.1 hspace.le
    · exact mul_le_mul_of_nonneg_left hbounds.2 hspace.le
  · intro hphysical x hx
    have hbounds := hphysical ⟨x, hx, rfl⟩
    constructor
    · apply le_of_mul_le_mul_left (a := data.spatialScale τ) _ hspace
      simpa only [mul_neg] using hbounds.1
    · exact le_of_mul_le_mul_left hbounds.2 hspace

/-- If the physical vorticity at time `t(τ₀)` is supported in `[-Cl(τ₀) L, Cl(τ₀) L]` and
the rescaled fields satisfy the transport equation with bounded `U_x` and zero transport
velocity at `±L`, then the physical vorticity at `t(τ)` is supported in
`[-Cl(τ) L, Cl(τ) L]` for every `τ ∈ [τ₀, T]`. -/
theorem physical_vorticity_support_subset_of_rescaled_transport
    (data : DynamicRescalingData) (fields : Fields) {τ₀ T L : ℝ} (hT : τ₀ ≤ T)
    (hu : ContDiff ℝ 1 (Function.uncurry (dynamicallyRescaledFields data fields).velocity))
    (hcl : Continuous data.spatialRate) (hcw : Continuous data.vorticityRate)
    (M : NNReal)
    (hbound : ∀ x τ, τ ∈ Icc τ₀ T →
      ‖deriv (fun y ↦ (dynamicallyRescaledFields data fields).velocity y τ) x‖₊ ≤ M)
    (hleft : ∀ τ ∈ Icc τ₀ T,
      (dynamicallyRescaledFields data fields).velocity (-L) τ +
        data.spatialRate τ * (-L) = 0)
    (hright : ∀ τ ∈ Icc τ₀ T,
      (dynamicallyRescaledFields data fields).velocity L τ + data.spatialRate τ * L = 0)
    (hregularity : HasClassicalRegularityOn (dynamicallyRescaledFields data fields) (Icc τ₀ T))
    (htransport : SatisfiesRescaledTransportEquationOn 1
      (dynamicallyRescaledFields data fields) data.spatialRate data.vorticityRate (Icc τ₀ T))
    (hamplitude : ∀ τ ∈ Icc τ₀ T, data.vorticityScale τ ≠ 0)
    (hspace : ∀ τ ∈ Icc τ₀ T, 0 < data.spatialScale τ)
    (hinitial : Function.support (fun y ↦ fields.vorticity y (data.physicalTime τ₀)) ⊆
      Icc (-(data.spatialScale τ₀ * L)) (data.spatialScale τ₀ * L)) :
    ∀ τ ∈ Icc τ₀ T,
      Function.support (fun y ↦ fields.vorticity y (data.physicalTime τ)) ⊆
        Icc (-(data.spatialScale τ * L)) (data.spatialScale τ * L) := by
  have hτ₀ : τ₀ ∈ Icc τ₀ T := left_mem_Icc.mpr hT
  have hrescaled₀ := (rescaled_vorticity_support_subset_iff_physical data fields τ₀ L
    (hamplitude τ₀ hτ₀) (hspace τ₀ hτ₀)).mpr hinitial
  have hrescaled := rescaled_vorticity_support_subset_of_deriv_bound
    hu hcl hcw M hbound hleft hright hregularity htransport hrescaled₀
  intro τ hτ
  exact (rescaled_vorticity_support_subset_iff_physical data fields τ L
    (hamplitude τ hτ) (hspace τ hτ)).mp (hrescaled τ hτ)

end DeGregorio
