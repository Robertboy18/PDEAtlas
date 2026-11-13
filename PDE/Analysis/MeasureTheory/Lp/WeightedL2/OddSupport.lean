/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.ExponentialConvergence
public import PDE.Analysis.MeasureTheory.Lp.WeightedL2.Coercivity
public import PDE.Analysis.MeasureTheory.Integral.Reflection
import CAS.ExactTactic

/-!
# From weighted half-interval energy to global L² decay

The energy estimate for an odd compactly supported vorticity is stated on
`(0,L)`. A positive lower bound for the weight controls the unweighted square
integral there. Reflection and the support condition then control the whole
real line, including `MemLp` membership.

The final convergence criteria combine this estimate with scalar Grönwall.
-/

@[expose] public section

noncomputable section

open Filter Set PDE.Analysis.Evolution
open scoped Topology

namespace MeasureTheory

/-- An odd function vanishing to the right of `L` belongs to global L² if
its square has finite energy against a weight bounded below on `(0,L)`. -/
theorem memLp_two_of_odd_supported_weighted_energy
    {q φ : ℝ → ℝ} {L c : ℝ} (hc : 0 < c)
    (hq : AEStronglyMeasurable q volume) (hodd : Function.Odd q)
    (hsupport : ∀ x, L ≤ x → q x = 0)
    (hφ : ∀ᵐ x ∂volume.restrict (Ioo 0 L), c ≤ φ x)
    (henergy : IntegrableOn (fun x ↦ q x ^ 2 * φ x) (Ioo 0 L)) :
    MemLp q 2 volume := by
  have hlocal := memLp_two_of_integrable_sq_mul_of_weight_lower_bound
    hc hq.restrict hφ henergy
  have hright : IntegrableOn (fun x ↦ q x ^ 2) (Ioi 0) := by
    apply IntegrableOn.of_forall_sdiff_eq_zero hlocal.integrable_sq measurableSet_Ioi
    intro x hx
    rw [hsupport x (not_lt.mp fun hlt ↦ hx.2 ⟨hx.1, hlt⟩)]
    norm_num
  have hleft : IntegrableOn (fun x ↦ q x ^ 2) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ ↦ -x) :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def, neg_preimage, neg_Iic, neg_zero]
    have heven : (fun x ↦ q (-x) ^ 2) = (fun x ↦ q x ^ 2) :=
      funext fun x ↦ by rw [hodd x, neg_sq]
    rw [heven]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hright
  apply (memLp_two_iff_integrable_sq hq).2
  simpa only [Iic_union_Ioi, integrableOn_univ] using hleft.union hright

/-- Reflection gives the exact factor two when weighted half-interval
energy bounds a global odd supported L² function. -/
theorem norm_toLp_sq_le_two_mul_weighted_energy_div
    {q φ : ℝ → ℝ} {L c : ℝ} (hc : 0 < c)
    (hq : MemLp q 2 volume) (hodd : Function.Odd q)
    (hsupport : ∀ x, L ≤ x → q x = 0)
    (hφ : ∀ᵐ x ∂volume.restrict (Ioo 0 L), c ≤ φ x)
    (henergy : IntegrableOn (fun x ↦ q x ^ 2 * φ x) (Ioo 0 L)) :
    ‖hq.toLp q‖ ^ 2 ≤ 2 * ((∫ x in Ioo 0 L, q x ^ 2 * φ x) / c) := by
  have hhalf := norm_toLp_sq_le_integral_sq_mul_div hc (hq.restrict (Ioo 0 L))
    hφ henergy
  rw [Lp.norm_toLp, ← integral_sq_eq_eLpNorm_toReal_sq (hq.restrict (Ioo 0 L))]
    at hhalf
  have heven : Function.Even (fun x ↦ q x ^ 2) := by
    intro x
    change q (-x) ^ 2 = q x ^ 2
    rw [hodd x, neg_sq]
  rw [Lp.norm_toLp, ← integral_sq_eq_eLpNorm_toReal_sq hq,
    integral_eq_two_mul_integral_Ioo_of_even_support heven
      (fun x hx ↦ by rw [hsupport x hx]; norm_num)]
  exact mul_le_mul_of_nonneg_left hhalf (by norm_num)

/-- Decay of weighted half-interval energy implies decay of the global
unweighted L² classes for odd supported functions. -/
theorem tendsto_toLp_zero_of_odd_supported_weighted_energy
    {ι : Type*} {l : Filter ι} {q : ι → ℝ → ℝ} {φ : ℝ → ℝ} {L c : ℝ}
    (hc : 0 < c) (hq : ∀ i, MemLp (q i) 2 volume)
    (hodd : ∀ i, Function.Odd (q i))
    (hsupport : ∀ i x, L ≤ x → q i x = 0)
    (hφ : ∀ᵐ x ∂volume.restrict (Ioo 0 L), c ≤ φ x)
    (hint : ∀ i, IntegrableOn (fun x ↦ q i x ^ 2 * φ x) (Ioo 0 L))
    (henergy : Tendsto (fun i ↦ ∫ x in Ioo 0 L, q i x ^ 2 * φ x) l (𝓝 0)) :
    Tendsto (fun i ↦ (hq i).toLp (q i)) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have hroot : Tendsto
      (fun i ↦ √(2 * ((∫ x in Ioo 0 L, q i x ^ 2 * φ x) / c))) l (𝓝 0) := by
    simpa only [zero_div, mul_zero, Real.sqrt_zero] using
      ((henergy.div_const c).const_mul 2).sqrt
  apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_) hroot
  have hsq := norm_toLp_sq_le_two_mul_weighted_energy_div
    hc (hq i) (hodd i) (hsupport i) hφ (hint i)
  exact (Real.le_sqrt (norm_nonneg _) ((sq_nonneg _).trans hsq)).2 hsq

/-- A weighted exponential energy estimate gives the square-root rate in the
global L² norm. The initial energy appears with its exact constant. -/
theorem norm_toLp_le_exp_of_weighted_energy_bound
    {q φ : ℝ → ℝ} {L c E δ a t : ℝ} (hc : 0 < c) (hE : 0 ≤ E)
    (hq : MemLp q 2 volume) (hodd : Function.Odd q)
    (hsupport : ∀ x, L ≤ x → q x = 0)
    (hφ : ∀ᵐ x ∂volume.restrict (Ioo 0 L), c ≤ φ x)
    (hint : IntegrableOn (fun x ↦ q x ^ 2 * φ x) (Ioo 0 L))
    (hbound : (∫ x in Ioo 0 L, q x ^ 2 * φ x) ≤
      E * Real.exp (-(2 * δ) * (t - a))) :
    ‖hq.toLp q‖ ≤ √(2 * (E / c)) * Real.exp (-δ * (t - a)) := by
  have hsq : ‖hq.toLp q‖ ^ 2 ≤ 2 * (E * Real.exp (-(2 * δ) * (t - a)) / c) :=
    (norm_toLp_sq_le_two_mul_weighted_energy_div hc hq hodd hsupport hφ hint).trans
      (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hbound hc.le)
        (by norm_num))
  calc
    ‖hq.toLp q‖ ≤ √(2 * (E * Real.exp (-(2 * δ) * (t - a)) / c)) :=
      (Real.le_sqrt (norm_nonneg _) ((sq_nonneg _).trans hsq)).2 hsq
    _ = √(2 * (E / c)) * Real.exp (-δ * (t - a)) := by
      rw [show 2 * (E * Real.exp (-(2 * δ) * (t - a)) / c) =
        (2 * (E / c)) * Real.exp (-(2 * δ) * (t - a)) by cas,
        Real.sqrt_mul (by positivity), ← Real.exp_half]
      congr 2
      cas

/-- A weighted energy differential inequality forces the supplied L²
coordinates to vanish along any sampling filter tending to infinity.
Oddness and support convert the half-interval energy to a global norm. -/
theorem tendsto_L2_zero_of_weighted_energy_differential_inequality
    {ι : Type*} {l : Filter ι} {τ : ι → ℝ}
    {w : ι → Lp ℝ 2 (volume : Measure ℝ)} {q : ℝ → ℝ → ℝ}
    {φ : ℝ → ℝ} {production : ℝ → ℝ} {L c a δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) (hτ : Tendsto τ l atTop)
    (hrep : ∀ i, (w i : ℝ → ℝ) =ᵐ[volume] q (τ i))
    (hodd : ∀ i, Function.Odd (q (τ i)))
    (hsupport : ∀ i x, L ≤ x → q (τ i) x = 0)
    (hφ : ∀ᵐ x ∂volume.restrict (Ioo 0 L), c ≤ φ x)
    (hint : ∀ i, IntegrableOn (fun x ↦ q (τ i) x ^ 2 * φ x) (Ioo 0 L))
    (hderiv : ∀ t ∈ Ici a,
      HasDerivAt (fun s ↦ ∫ x in Ioo 0 L, q s x ^ 2 * φ x) (production t) t)
    (hbound : ∀ t ∈ Ici a, production t ≤
      -(2 * δ) * ∫ x in Ioo 0 L, q t x ^ 2 * φ x) :
    Tendsto w l (𝓝 0) := by
  have henergy := energy_tendsto_zero_of_differential_inequality hδ
    (fun t _ ↦ integral_nonneg_of_ae <| by
      filter_upwards [hφ] with x hx
      exact mul_nonneg (sq_nonneg (q t x)) (hc.le.trans hx)) hderiv hbound
  have hq (i : ι) : MemLp (q (τ i)) 2 volume :=
    (memLp_congr_ae (hrep i)).mp (Lp.memLp (w i))
  have htoLp (i : ι) : (hq i).toLp (q (τ i)) = w i :=
    Lp.ext ((hq i).coeFn_toLp.trans (hrep i).symm)
  have hlimit := tendsto_toLp_zero_of_odd_supported_weighted_energy
    hc hq hodd hsupport hφ hint (henergy.comp hτ)
  simpa only [htoLp] using hlimit

/-- Finite energy against an inverse fourth-power floor places the
second origin quotient in global L². -/
theorem memLp_div_sq_of_odd_supported_weighted_energy
    {q φ : ℝ → ℝ} {L a : ℝ} (ha : 0 < a)
    (hq : AEStronglyMeasurable q volume) (hodd : Function.Odd q)
    (hsupport : ∀ x, L ≤ x → q x = 0)
    (hfloor : ∀ x ∈ Ioo 0 L, a / x ^ 4 ≤ φ x)
    (henergy : IntegrableOn (fun x ↦ q x ^ 2 * φ x) (Ioo 0 L)) :
    MemLp (fun x ↦ q x / x ^ 2) 2 volume := by
  have hm := hq.div₀ (measurable_id.pow_const 2).aestronglyMeasurable
  have hi : IntegrableOn (fun x ↦ (q x / x ^ 2) ^ 2 * a) (Ioo 0 L) := by
    apply henergy.mono_nonneg ((hm.restrict.pow 2).mul aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun _ ↦ mul_nonneg (sq_nonneg _) ha.le)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    calc
      (q x / x ^ 2) ^ 2 * a = q x ^ 2 * (a / x ^ 4) := by
        generalize q x = z
        cas
      _ ≤ q x ^ 2 * φ x :=
        mul_le_mul_of_nonneg_left (hfloor x hx) (sq_nonneg _)
  apply memLp_two_of_odd_supported_weighted_energy ha hm
    (φ := fun _ ↦ a) (L := L) ?_ ?_
    (Filter.Eventually.of_forall fun _ ↦ le_rfl) hi
  · intro x
    change q (-x) / (-x) ^ 2 = -(q x / x ^ 2)
    simp only [hodd x, neg_sq, neg_div]
  · intro x hx
    change q x / x ^ 2 = 0
    simp only [hsupport x hx, zero_div]

end MeasureTheory
