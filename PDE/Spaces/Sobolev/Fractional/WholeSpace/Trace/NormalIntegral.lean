/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.NormalRestriction
import Mathlib.MeasureTheory.Integral.Prod
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# The integral formula for normal-frequency restriction

The normalized kernel is an `L²` unit vector on each normal line. Cauchy–Schwarz
therefore bounds integration against it. Applying this estimate on almost every
normal line and then Fubini identifies the adjoint restriction with its concrete
fiber integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace SobolevSpace.Fractional.Trace

/-- Integration against the normal kernel is absolutely convergent on `L²`. -/
theorem integrable_normalKernel_smul (a : ℝ≥0) {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    Integrable (fun t ↦ normalKernel a t • f t) volume :=
  memLp_one_iff_integrable.1 ((memLp_normalKernel a).smul hf)

/-- Cauchy–Schwarz on one normal line, with the kernel's exact normalization. -/
theorem norm_integral_normalKernel_smul_le (a : ℝ≥0) (ha : a ≠ 0)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    ‖∫ t, normalKernel a t • f t‖ ≤ ‖hf.toLp f‖ := by
  let hk : MemLp (fun t ↦ (normalKernel a t : ℂ)) 2 volume :=
    (memLp_normalKernel a).ofReal
  let k := hk.toLp (fun t ↦ (normalKernel a t : ℂ))
  have hk_norm : ‖k‖ = 1 := by
    rw [show ‖k‖ = ‖(memLp_normalKernel a).toLp (normalKernel a)‖ by
      simp only [k, Lp.norm_toLp]
      congr 1
      exact eLpNorm_congr_norm_ae hk.aestronglyMeasurable
        (measurable_normalKernel a).aestronglyMeasurable
        (Filter.Eventually.of_forall fun t ↦ Complex.norm_real _)]
    exact norm_normalKernel_toLp a ha
  have heq : (∫ t, normalKernel a t • f t) = ⟪k, hf.toLp f⟫_ℂ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hk.coeFn_toLp, hf.coeFn_toLp] with t h1 h2
    change normalKernel a t • f t = ⟪k t, hf.toLp f t⟫_ℂ
    rw [h1, h2]
    simp [RCLike.inner_apply, Complex.real_smul, mul_comm]
  rw [heq]
  simpa only [hk_norm, one_mul] using norm_inner_le_norm k (hf.toLp f)

/-- The squared fiber estimate in integral form. -/
theorem norm_integral_normalKernel_smul_sq_le (a : ℝ≥0) (ha : a ≠ 0)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    ‖∫ t, normalKernel a t • f t‖ ^ 2 ≤ ∫ t, ‖f t‖ ^ 2 := by
  calc
    _ ≤ ‖hf.toLp f‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_integral_normalKernel_smul_le a ha hf) 2
    _ = _ := by
      rw [Lp.norm_sq_eq_integral_norm_sq]
      exact integral_congr_ae (hf.coeFn_toLp.fun_comp (fun z : ℂ ↦ ‖z‖ ^ 2))

variable {n : ℕ}

/-- The concrete integral on each normal-frequency line. -/
def normalRestrictionFun (u : Lp ℂ 2 (volume : Measure (ℝ^n × ℝ))) (ξ : ℝ^n) : ℂ :=
  ∫ t : ℝ, normalKernel (tangentialScale ξ) t • u (ξ, t)

/-- A product-frequency `L²` function is square integrable on almost every normal line. -/
theorem ae_memLp_normalSlice (u : Lp ℂ 2 (volume : Measure (ℝ^n × ℝ))) :
    ∀ᵐ ξ ∂volume, MemLp (fun t : ℝ ↦ u (ξ, t)) 2 volume := by
  have hm : AEStronglyMeasurable u (volume.prod volume) := Lp.aestronglyMeasurable u
  have hi : Integrable (fun z ↦ ‖u z‖ ^ 2) (volume.prod volume) :=
    (Lp.memLp u).norm.integrable_sq
  filter_upwards [hm.prodMk_left, hi.prod_right_ae] with ξ hξ iξ
  exact (memLp_two_iff_integrable_sq_norm hξ).2 iξ

private theorem aestronglyMeasurable_normalRestrictionFun
    (u : Lp ℂ 2 (volume : Measure (ℝ^n × ℝ))) :
    AEStronglyMeasurable (normalRestrictionFun u) volume := by
  have hu : AEStronglyMeasurable u (volume.prod volume) := Lp.aestronglyMeasurable u
  exact (measurable_normalKernel_tangentialScale.aestronglyMeasurable.smul hu).integral_prod_right'

/-- The fiber integral is a boundary `L²` function. -/
theorem memLp_normalRestrictionFun (u : Lp ℂ 2 (volume : Measure (ℝ^n × ℝ))) :
    MemLp (normalRestrictionFun u) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_normalRestrictionFun u)).2
  have hi : Integrable (fun z ↦ ‖u z‖ ^ 2) (volume.prod volume) :=
    (Lp.memLp u).norm.integrable_sq
  apply hi.integral_prod_left.mono_nonneg
    (aestronglyMeasurable_normalRestrictionFun u |>.norm.pow 2)
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
  filter_upwards [ae_memLp_normalSlice u] with ξ hξ
  exact norm_integral_normalKernel_smul_sq_le
    (tangentialScale ξ) (tangentialScale_ne_zero ξ) hξ

private theorem inner_normalLiftFun (v : Lp ℂ 2 (volume : Measure ℝ^n))
    (u : Lp ℂ 2 (volume : Measure (ℝ^n × ℝ))) (z : ℝ^n × ℝ) :
    ⟪normalLiftFun v z, u z⟫_ℂ =
      ⟪v z.1, normalKernel (tangentialScale z.1) z.2 • u z⟫_ℂ := by
  simp [normalLiftFun, RCLike.inner_apply, Complex.real_smul,
    mul_left_comm, mul_comm, mul_assoc]

/-- The adjoint restriction equals the fiber integral as an `L²` element. -/
theorem normalRestriction_eq_toLp (u : Lp ℂ 2 (volume : Measure (ℝ^n × ℝ))) :
    normalRestriction n u =
      (memLp_normalRestrictionFun u).toLp (normalRestrictionFun u) := by
  apply ext_inner_left ℂ
  intro v
  rw [inner_normalRestriction, L2.inner_def, L2.inner_def]
  have hlift := normalLift_apply_ae v
  have hprod : Integrable
      (fun z : ℝ^n × ℝ ↦ ⟪v z.1, normalKernel (tangentialScale z.1) z.2 • u z⟫_ℂ)
      (volume.prod volume) := by
    have h := L2.integrable_inner (𝕜 := ℂ) (normalLift v) u
    rw [← Measure.volume_eq_prod]
    apply h.congr
    filter_upwards [hlift] with z hz
    rw [hz, inner_normalLiftFun]
  calc
    _ = ∫ z : ℝ^n × ℝ, ⟪v z.1, normalKernel (tangentialScale z.1) z.2 • u z⟫_ℂ := by
      apply integral_congr_ae
      filter_upwards [hlift] with z hz
      rw [hz, inner_normalLiftFun]
    _ = ∫ ξ : ℝ^n, ∫ t : ℝ, ⟪v ξ, normalKernel (tangentialScale ξ) t • u (ξ, t)⟫_ℂ :=
      integral_prod _ hprod
    _ = ∫ ξ : ℝ^n, ⟪v ξ, normalRestrictionFun u ξ⟫_ℂ := by
      apply integral_congr_ae
      filter_upwards [ae_memLp_normalSlice u] with ξ hξ
      exact integral_inner (integrable_normalKernel_smul _ hξ) _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(memLp_normalRestrictionFun u).coeFn_toLp] with ξ hξ
      rw [hξ]

/-- Almost everywhere, bounded restriction is integration against the normalized kernel. -/
theorem normalRestriction_apply_ae (u : Lp ℂ 2 (volume : Measure (ℝ^n × ℝ))) :
    normalRestriction n u =ᵐ[volume] normalRestrictionFun u := by
  rw [normalRestriction_eq_toLp]
  exact (memLp_normalRestrictionFun u).coeFn_toLp

end SobolevSpace.Fractional.Trace
