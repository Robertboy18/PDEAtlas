/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.RescaledTraceBounds

/-!
# Finite terminal traces of a rescaled solution

Uniform supported H² control constructs a strong L² terminal limit for the
normalized equal-rate rescaled equation. Weak closedness gives its H² graph.
Compact C¹ convergence then identifies the velocity, its spatial
derivative, the normalization rate, and the vorticity time-derivative trace.

The PDE itself supplies the time control, and the velocity bounds come from the
supported H² control.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio

/-- The normalized equal-rate rescaled PDE has a constructed H² terminal
state under uniform supported H² control. All four coupled spatial traces,
the endpoint rate, and the pointwise time derivative converge to the
expressions determined by that state. -/
theorem IsClassicalRescaledSolutionOn.exists_h2_terminal_normalized
    {fields : Fields} {ρ : ℝ → ℝ} {a T R : ℝ} {B : NNReal}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo a T))
    (haT : a < T) (hR : 0 < R) {K : Set ℝ} (hK : IsCompact K)
    {F : ℝ → DerivLp 1 2 univ}
    (hbound : ∀ t ∈ Ioo a T, F t ∈ supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B)
    (hrep : ∀ t ∈ Ioo a T,
      (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume]
        (fun x ↦ fields.vorticity x t))
    (hzero : ∀ t ∈ Ioo a T, fields.velocity 0 t = 0)
    (hnormalized : ∀ t ∈ Ioo a T, ρ t = -fields.velocity R t / R) :
    ∃ (U : W^{2,2}(ℝ^1)) (v : ℝ → ℝ) (C : NNReal),
      ‖U‖ ≤ B ∧
      wkpBaseCoordinateCLM U ∈ supportedHkBaseBall 1 2 univ
        (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B ∧
      ContDiff ℝ 1 v ∧ tsupport v ⊆ K ∧
      (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM U) : ℝ → ℝ) =ᵐ[volume] v ∧
      Tendsto F (𝓝[<] T) (𝓝 (wkpBaseCoordinateCLM U)) ∧
      (∀ t ∈ Ioo a T, ‖F t - wkpBaseCoordinateCLM U‖ ≤ C * (T - t)) ∧
      (∀ A : Set ℝ, IsCompact A →
        TendstoUniformlyOn (fun t x ↦ fields.vorticity x t) v (𝓝[<] T) A ∧
        TendstoUniformlyOn (fun t ↦ deriv (fun x ↦ fields.vorticity x t))
          (deriv v) (𝓝[<] T) A ∧
        TendstoUniformlyOn (fun t ↦ deriv (fun x ↦ fields.velocity x t))
          (hilbertPV v) (𝓝[<] T) A ∧
        TendstoUniformlyOn (fun t x ↦ fields.velocity x t)
          (hilbertPVVelocity v) (𝓝[<] T) A) ∧
      Tendsto ρ (𝓝[<] T) (𝓝 (-hilbertPVVelocity v R / R)) ∧
      ∀ x, Tendsto (deriv (fields.vorticity x)) (𝓝[<] T)
        (𝓝 ((-hilbertPVVelocity v R / R + hilbertPV v x) * v x -
          ((-hilbertPVVelocity v R / R) * x + hilbertPVVelocity v x) * deriv v x)) := by
  obtain ⟨C, hC⟩ :=
    hsol.exists_lipschitzOnWith_base_of_supported_h2 hR hK hbound hrep hzero hnormalized
  have hw (t : ℝ) (ht : t ∈ Ioo a T) :
      Continuous (fun x ↦ fields.vorticity x t) :=
    continuous_iff_continuousAt.mpr fun _ ↦
      (hsol.regularity.vorticity_spatial_differentiableAt ht).continuousAt
  obtain ⟨U, v, hU, hUb, hv, hs, hr, hlim, hrate, hspatial⟩ :=
    Iteration.exists_h2_c1_terminal_of_lipschitzOnWith haT hK.isClosed hbound hC hw hrep
  have hreg (t : ℝ) (ht : t ∈ Ioo a T) :
      ContDiff ℝ 1 (fun x ↦ fields.vorticity x t) :=
    (contDiff_and_bounds_of_hkBaseBall (hbound t ht).1 (hw t ht) (hrep t ht)).1
  have hsupp (t : ℝ) (ht : t ∈ Ioo a T) :
      HasCompactSupport (fun x ↦ fields.vorticity x t) :=
    hK.of_isClosed_subset (isClosed_tsupport _)
      (Iteration.tsupport_subset_of_mem_supportedHkBaseBall hK.isClosed
        (hbound t ht) (hw t ht) (hrep t ht))
  have hueq (t : ℝ) (ht : t ∈ Ioo a T) :
      (fun x ↦ fields.velocity x t) = hilbertPVVelocity (fun x ↦ fields.vorticity x t) :=
    hsol.velocity_eq_hilbertPVVelocity ht (hreg t ht) (hsupp t ht) (hzero t ht)
  have huxeq (t : ℝ) (ht : t ∈ Ioo a T) (x : ℝ) :
      deriv (fun y ↦ fields.velocity y t) x = hilbertPV (fun y ↦ fields.vorticity y t) x :=
    hueq t ht ▸ (hasDerivAt_hilbertPVVelocity_of_contDiff_one_compactSupport
      (hreg t ht) (hsupp t ht) x).deriv
  have hvs : HasCompactSupport v := hK.of_isClosed_subset (isClosed_tsupport _) hs
  have htimes : ∀ᶠ t in 𝓝[<] T, t ∈ Ioo a T := Ioo_mem_nhdsLT haT
  have hc (A : Set ℝ) (hA : IsCompact A) :
      TendstoUniformlyOn (fun t ↦ hilbertPV (fun x ↦ fields.vorticity x t))
        (hilbertPV v) (𝓝[<] T) A := by
    let l := comap (Subtype.val : Ioo a T → ℝ) (𝓝[<] T)
    have hmap : map (Subtype.val : Ioo a T → ℝ) l = 𝓝[<] T :=
      map_comap_of_mem (by simpa only [Subtype.range_val] using Ioo_mem_nhdsLT haT)
    have hconv := Iteration.tendstoUniformlyOn_hilbertPV_of_h2_base
      (l := l) (fun t : Ioo a T ↦ (hbound t t.property).1) hUb.1
      (hlim.comp (show Tendsto (Subtype.val : Ioo a T → ℝ) l (𝓝[<] T)
        from map_comap_le))
      (fun t : Ioo a T ↦ hreg t t.property) (fun t : Ioo a T ↦ hsupp t t.property)
      hv hvs (fun t : Ioo a T ↦ hrep t t.property) hr hA
    exact fun V hV ↦ by rw [← hmap]; exact hconv V hV
  have hu (A : Set ℝ) (hA : IsCompact A) :
      TendstoUniformlyOn (fun t x ↦ fields.velocity x t)
        (hilbertPVVelocity v) (𝓝[<] T) A := by
    rw [Iteration.hilbertPVVelocity_eq_l2Primitive_of_ae hv hvs hr]
    refine (Iteration.tendstoUniformlyOn_normalized_hilbert_velocity hlim hA).congr <|
      htimes.mono fun t ht x _ ↦ ?_
    rw [hueq t ht,
      Iteration.hilbertPVVelocity_eq_l2Primitive_of_ae (hreg t ht) (hsupp t ht) (hrep t ht)]
  have hux (A : Set ℝ) (hA : IsCompact A) :
      TendstoUniformlyOn (fun t ↦ deriv (fun x ↦ fields.velocity x t))
        (hilbertPV v) (𝓝[<] T) A :=
    (hc A hA).congr <| htimes.mono fun t ht x _ ↦ (huxeq t ht x).symm
  have hρ : Tendsto ρ (𝓝[<] T) (𝓝 (-hilbertPVVelocity v R / R)) :=
    (((hu {R} isCompact_singleton).tendsto_at (mem_singleton R)).neg.div_const R).congr'
      (htimes.mono fun t ht ↦ (hnormalized t ht).symm)
  refine ⟨U, v, C, hU, hUb, hv, hs, hr, hlim, hrate,
    fun A hA ↦ ⟨(hspatial A hA).1, (hspatial A hA).2, hux A hA, hu A hA⟩, hρ, ?_⟩
  intro x
  have hwx := hspatial {x} (isCompact_singleton (x := x))
  have hcx := (hux {x} isCompact_singleton).tendsto_at (mem_singleton x)
  have hux := (hu {x} isCompact_singleton).tendsto_at (mem_singleton x)
  apply (((hρ.add hcx).mul (hwx.1.tendsto_at (mem_singleton x))).sub
    (((hρ.mul_const x).add hux).mul (hwx.2.tendsto_at (mem_singleton x)))).congr'
  filter_upwards [htimes] with t ht
  simpa only [one_mul] using (eq_sub_of_add_eq (hsol.transport (x := x) ht)).symm

end DeGregorio
