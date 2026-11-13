/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.CompactEnergy.Integration
public import PDE.Analysis.Evolution.Core.Gronwall
import PDE.FDeriv.Calculus
import PDE.DistributionTheory.TestFunction.IntegrationByParts

/-!
# From a compact classical energy inequality to zero energy

The hypotheses here are a pointwise differential inequality for actual fields,
their regularity, and compact spatial support. Integration eliminates the
divergence. Grönwall uses a right limit at the initial time, without requiring
the differential inequality at that time.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Filter MeasureTheory Set PDE.Common
open scoped Topology

variable {n : ℕ}

/-- A spatial slice of a field with local `C¹` regularity is `C¹`. -/
theorem contDiff_spatial_slice {f : ℝ^(n + 1) → ℝ} {t : ℝ}
    (hf : ∀ x, ContDiffAt ℝ 1 f (timeSpaceCons t x)) :
    ContDiff ℝ 1 (fun x ↦ f (timeSpaceCons t x)) :=
  contDiff_iff_contDiffAt.mpr fun x ↦
    (hf x).comp x (contDiff_timeSpaceCons_spatial n t (m := 1)).contDiffAt

/-- A time derivative vanishes off a common spatial support. -/
theorem time_partial_eq_zero_off_support
    {f : ℝ^(n + 1) → ℝ} {I : Set ℝ} {K : Set (ℝ^n)}
    (hI : IsOpen I)
    (hf : ∀ t ∈ I, ∀ x, ContDiffAt ℝ 1 f (timeSpaceCons t x))
    (hs : ∀ t ∈ I, ∀ x ∉ K, f (timeSpaceCons t x) = 0)
    {t : ℝ} (ht : t ∈ I) {x : ℝ^n} (hx : x ∉ K) :
    (∂[0] f) (timeSpaceCons t x) = 0 := by
  have heq : (fun s ↦ f (timeSpaceCons s x)) =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hI.mem_nhds ht] with s hsI using hs s hsI x hx
  exact (hasDerivAt_timeSpaceCons f t x
    ((hf t ht x).differentiableAt one_ne_zero)).unique
      ((hasDerivAt_const t 0).congr_of_eventuallyEq heq)

/-- Integrating a compactly supported pointwise energy inequality removes the flux. -/
theorem integral_time_partial_le
    {e : ℝ^(n + 1) → ℝ} {g : Fin n → ℝ^(n + 1) → ℝ}
    {I : Set ℝ} {K : Set (ℝ^n)} {C : ℝ}
    (hI : IsOpen I) (hK : IsCompact K)
    (he : ∀ t ∈ I, ∀ x, ContDiffAt ℝ 1 e (timeSpaceCons t x))
    (hg : ∀ j t, t ∈ I → ∀ x, ContDiffAt ℝ 1 (g j) (timeSpaceCons t x))
    (hes : ∀ t ∈ I, ∀ x ∉ K, e (timeSpaceCons t x) = 0)
    (hgs : ∀ j t, t ∈ I → ∀ x ∉ K, g j (timeSpaceCons t x) = 0)
    (hle : ∀ t ∈ I, ∀ x,
      (∂[0] e) (timeSpaceCons t x) -
        ∑ j, (∂[j.succ] (g j)) (timeSpaceCons t x) ≤ C * e (timeSpaceCons t x))
    {t : ℝ} (ht : t ∈ I) :
    (∫ x, (∂[0] e) (timeSpaceCons t x)) ≤ C * ∫ x, e (timeSpaceCons t x) := by
  have hec := contDiff_spatial_slice (he t ht)
  have hei : Integrable (fun x ↦ e (timeSpaceCons t x)) :=
    hec.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.intro hK (hes t ht))
  have hdi : Integrable (fun x ↦ (∂[0] e) (timeSpaceCons t x)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact continuous_iff_continuousAt.mpr fun x ↦
        (contDiffAt_partialDeriv 0 (he t ht x) 0).continuousAt.comp
          (contDiff_timeSpaceCons_spatial n t (m := 1)).continuous.continuousAt
    · exact HasCompactSupport.intro hK fun x hx ↦
        time_partial_eq_zero_off_support hI he hes ht hx
  have hgc (j : Fin n) := contDiff_spatial_slice (hg j t ht)
  have hgcompact (j : Fin n) := HasCompactSupport.intro hK (hgs j t ht)
  have hgeq (j : Fin n) : (fun x ↦ (∂[j.succ] (g j)) (timeSpaceCons t x)) =
      (∂[j] (fun x ↦ g j (timeSpaceCons t x))) := by
    funext x
    exact (partialDeriv_timeSpaceCons_spatial j (g j) t x
      ((hg j t ht x).differentiableAt one_ne_zero)).symm
  have hgi (j : Fin n) :
      Integrable (fun x ↦ (∂[j.succ] (g j)) (timeSpaceCons t x)) := by
    rw [hgeq]
    exact ((hgc j).continuous_fderiv one_ne_zero |>.clm_apply
      continuous_const).integrable_of_hasCompactSupport
        ((hgcompact j).fderiv_apply ℝ _)
  have hz (j : Fin n) :
      (∫ x, (∂[j.succ] (g j)) (timeSpaceCons t x)) = 0 := by
    rw [hgeq]
    exact PDE.DistributionTheory.integral_partialDeriv_eq_zero_of_hasCompactSupport j (hgc j)
      (hgcompact j)
  have hh := integral_mono (hdi.sub (integrable_finsetSum _ fun j _ ↦ hgi j))
    (hei.const_mul C) (fun x ↦ hle t ht x)
  simpa [integral_sub hdi (integrable_finsetSum _ fun j _ ↦ hgi j),
    integral_finsetSum _ (fun j _ ↦ hgi j), hz, integral_const_mul] using hh

/-- Grönwall with a zero right limit forces a nonnegative energy to vanish. -/
theorem eq_zero_of_hasDerivAt_le_of_tendsto_zero
    {E D : ℝ → ℝ} {b C : ℝ}
    (hd : ∀ t ∈ Ioo 0 b, HasDerivAt E (D t) t)
    (hle : ∀ t ∈ Ioo 0 b, D t ≤ C * E t)
    (hzero : Tendsto E (𝓝[>] 0) (𝓝 0))
    (hnonneg : ∀ t ∈ Ioo 0 b, 0 ≤ E t)
    {t : ℝ} (ht : t ∈ Ioo 0 b) :
    E t = 0 := by
  have hbound (s : ℝ) (hs : s ∈ Ioo 0 t) :
      E t ≤ E s * Real.exp (C * (t - s)) := by
    have hinterval (r : ℝ) (hr : r ∈ Icc s t) : r ∈ Ioo 0 b :=
      ⟨hs.1.trans_le hr.1, hr.2.trans_lt ht.2⟩
    have hh := Evolution.le_gronwallBound_of_hasDerivWithinAt_le
      (K := C) (ε := 0)
      (fun r hr ↦ (hd r (hinterval r hr)).hasDerivWithinAt)
      (le_refl (E s)) (fun r hr ↦ by simpa using hle r (hinterval r hr))
      t (show t ∈ Icc s t from ⟨hs.2.le, le_rfl⟩)
    simpa [gronwallBound_ε0] using hh
  have hlim : Tendsto (fun s ↦ E s * Real.exp (C * (t - s))) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ ↦ Real.exp (C * (t - s))) := by fun_prop
    simpa using hzero.mul (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  apply le_antisymm _ (hnonneg t ht)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (Iio_mem_nhds ht.1)] with s hs hst
  exact hbound s ⟨hs, hst⟩

end PDE.Analysis
