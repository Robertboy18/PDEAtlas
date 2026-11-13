/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Time derivatives of Lp curves

A common `Lp` envelope for the spatial modulus of the time derivatives controls
the Taylor remainder in `Lp`. This gives a strong derivative from derivatives of
spatial representatives, including within derivatives at interval endpoints.
Pointwise differentiability alone would not control that remainder.

For `L∞`, the envelope can be constant on an infinite-measure space. Joint continuity
of the derivative on a compact cylinder gives the uniform modulus in that case.
The general criterion needs neither finite spatial measure nor a complete range.
-/

@[expose] public section

noncomputable section

namespace MeasureTheory

open Filter Set
open scoped ENNReal Topology

/-- A common `Lp` envelope for the time-derivative modulus identifies the derivative
of the represented `Lp` curve. The time set is convex and may have endpoints.
For each error tolerance, the spatial exceptional set is common to every nearby time.
The measure need not be finite, and the envelope need not be bounded. -/
theorem hasDerivWithinAt_lp_of_ae_uniform_derivative
    {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {S : Set ℝ} (hS : Convex ℝ S) {t : ℝ} (ht : t ∈ S)
    (F : ℝ → Lp E p μ) (D : Lp E p μ) (G : Lp ℝ p μ) (f fdot : ℝ → α → E)
    (hrep : ∀ s ∈ S, (F s : α → E) =ᵐ[μ] f s)
    (hD : (D : α → E) =ᵐ[μ] fdot t)
    (hderiv : ∀ᵐ x ∂μ, ∀ s ∈ S,
      HasDerivWithinAt (fun r ↦ f r x) (fdot s x) S s)
    (hmod : ∀ ε > 0, ∃ δ > 0, ∀ᵐ x ∂μ, ∀ s ∈ S,
      dist s t < δ → ‖fdot s x - fdot t x‖ ≤ ε * ‖G x‖) :
    HasDerivWithinAt F D S t := by
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  let η := ε / (‖G‖ + 1)
  have hden : 0 < ‖G‖ + 1 := add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
  have hη : 0 < η := div_pos hε hden
  have hηG : η * ‖G‖ ≤ ε := by
    dsimp only [η]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).2
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hε.le
  obtain ⟨δ, hδ, hmod⟩ := hmod η hη
  apply Metric.mem_nhdsWithin_iff.mpr
  refine ⟨δ, hδ, ?_⟩
  rintro s ⟨hsδ, hs⟩
  have hpoint :
      ∀ᵐ x ∂μ,
        ‖((F s - F t - (s - t) • D : Lp E p μ) : α → E) x‖ ≤
          (η * ‖s - t‖) * ‖G x‖ := by
    filter_upwards [hderiv, hmod, hrep s hs, hrep t ht, hD,
      Lp.coeFn_sub (F s) (F t),
      Lp.coeFn_sub (F s - F t) ((s - t) • D),
      Lp.coeFn_smul (s - t) D] with x hdx hmx hsx htx hDx hsub hrem hsmul
    have hlinear (r : ℝ) :
        HasDerivWithinAt (fun q : ℝ ↦ (q - t) • fdot t x)
          (fdot t x) (S ∩ Metric.ball t δ) r := by
      simpa only [id, one_smul] using
        (((hasDerivAt_id r).sub_const t).smul_const (fdot t x)).hasDerivWithinAt
    have hestimate :=
      (hS.inter (convex_ball t δ)).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun r hr ↦ ((hdx r hr.1).mono inter_subset_left).sub (hlinear r))
        (fun r hr ↦ hmx r hr.1 hr.2)
        (show t ∈ S ∩ Metric.ball t δ from ⟨ht, Metric.mem_ball_self hδ⟩)
        (show s ∈ S ∩ Metric.ball t δ from ⟨hs, hsδ⟩)
    rw [hrem, Pi.sub_apply, hsub, Pi.sub_apply, hsmul, Pi.smul_apply]
    change ‖(F s : α → E) x - (F t : α → E) x - (s - t) • (D : α → E) x‖ ≤ _
    rw [hsx, htx, hDx]
    simpa only [Pi.sub_apply, sub_self, zero_smul, sub_zero, mul_right_comm,
      sub_right_comm (f s x) ((s - t) • fdot t x) (f t x)] using hestimate
  change ‖F s - F t - (s - t) • D‖ ≤ ε * ‖s - t‖
  calc
    ‖F s - F t - (s - t) • D‖ ≤ (η * ‖s - t‖) * ‖G‖ :=
      Lp.norm_le_mul_norm_of_ae_le_mul hpoint
    _ = (η * ‖G‖) * ‖s - t‖ := mul_right_comm _ _ _
    _ ≤ ε * ‖s - t‖ := mul_le_mul_of_nonneg_right hηG (norm_nonneg _)

/-- A uniform modulus for the time derivative of spatial representatives identifies
the derivative in `L∞` norm. This is the constant-envelope case of the `Lp` criterion;
no finite spatial measure is needed. -/
theorem hasDerivWithinAt_lp_top_of_ae_uniform_derivative
    {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b t : ℝ} (ht : t ∈ Icc a b)
    (F : ℝ → Lp E ∞ μ) (D : Lp E ∞ μ) (f fdot : ℝ → α → E)
    (hrep : ∀ s ∈ Icc a b, (F s : α → E) =ᵐ[μ] f s)
    (hD : (D : α → E) =ᵐ[μ] fdot t)
    (hderiv : ∀ᵐ x ∂μ, ∀ s ∈ Icc a b,
      HasDerivWithinAt (fun r ↦ f r x) (fdot s x) (Icc a b) s)
    (hmod : ∀ ε > 0, ∃ δ > 0, ∀ᵐ x ∂μ, ∀ s ∈ Icc a b,
      dist s t < δ → ‖fdot s x - fdot t x‖ ≤ ε) :
    HasDerivWithinAt F D (Icc a b) t := by
  let hG : MemLp (fun _ : α ↦ (1 : ℝ)) ∞ μ := memLp_top_const 1
  apply hasDerivWithinAt_lp_of_ae_uniform_derivative (convex_Icc a b) ht F D
    (hG.toLp (fun _ ↦ 1)) f fdot hrep hD hderiv
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := hmod ε hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hmod, hG.coeFn_toLp] with x hx hGx
  simpa only [hGx, norm_one, mul_one] using hx

/-- Joint continuity of the time derivative on a compact cylinder supplies the
uniform spatial remainder needed to differentiate its represented `L∞` curve. -/
theorem hasDerivWithinAt_lp_top_of_continuousOn_compact
    {α E : Type*} [MetricSpace α] [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set α} (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K)
    {a b t : ℝ} (ht : t ∈ Icc a b)
    (F : ℝ → Lp E ∞ μ) (D : Lp E ∞ μ) (f fdot : ℝ → α → E)
    (hrep : ∀ s ∈ Icc a b, (F s : α → E) =ᵐ[μ] f s)
    (hD : (D : α → E) =ᵐ[μ] fdot t)
    (hderiv : ∀ x ∈ K, ∀ s ∈ Icc a b,
      HasDerivWithinAt (fun r ↦ f r x) (fdot s x) (Icc a b) s)
    (hcont : ContinuousOn (Function.uncurry fdot) (Icc a b ×ˢ K)) :
    HasDerivWithinAt F D (Icc a b) t := by
  apply hasDerivWithinAt_lp_top_of_ae_uniform_derivative ht F D f fdot hrep hD
  · exact hμ.mono fun x hx ↦ hderiv x hx
  · intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
      ((isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hcont) ε hε
    refine ⟨δ, hδ, hμ.mono ?_⟩
    intro x hx s hs hst
    have hpair : dist (s, x) (t, x) < δ := by
      simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hst
    simpa only [Function.uncurry_def, dist_eq_norm] using
      (hmod (s, x) ⟨hs, hx⟩ (t, x) ⟨ht, hx⟩ hpair).le

end MeasureTheory
