/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.WeightedL2.OddSupport
import CAS.ExactTactic

/-!
# Global L² Cauchy families from weighted perturbations

A weight bounded below by `c > 0` on `(0,L)` controls the global norm of an
odd function supported in `[-L,L]`, with factor `sqrt (2/c)`. Applying this
estimate to differences transfers the Cauchy property of weighted
perturbations to their unweighted L² classes.

The reference cancels in every difference and need not belong to the
weighted space. Oddness and common support are required only eventually.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace MeasureTheory

/-- Reflection and a positive weight floor bound the global norm by the
weighted half-interval norm. Both classes are identified with their raw functions. -/
theorem norm_le_weighted_norm_of_odd_supported
    {q φ : ℝ → ℝ} {L c : ℝ} (hc : 0 < c)
    {u : Lp ℝ 2 (volume : Measure ℝ)}
    {v : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) L))}
    (hu : (u : ℝ → ℝ) =ᵐ[volume] q)
    (hv : (v : ℝ → ℝ) =ᵐ[volume.restrict (Ioo 0 L)] (fun x ↦ q x * √(φ x)))
    (hodd : Function.Odd q) (hsupport : ∀ x, L ≤ x → q x = 0)
    (hφ : ∀ᵐ x ∂volume.restrict (Ioo 0 L), c ≤ φ x) :
    ‖u‖ ≤ √(2 / c) * ‖v‖ := by
  have hq : MemLp q 2 volume := (memLp_congr_ae hu).mp (Lp.memLp u)
  have hw : MemLp (fun x ↦ q x * √(φ x)) 2 (volume.restrict (Ioo 0 L)) :=
    (memLp_congr_ae hv).mp (Lp.memLp v)
  have hsquare :
      (fun x ↦ (q x * √(φ x)) ^ 2) =ᵐ[volume.restrict (Ioo 0 L)]
        (fun x ↦ q x ^ 2 * φ x) := by
    filter_upwards [hφ] with x hx
    rw [mul_pow, Real.sq_sqrt (hc.le.trans hx)]
  have hto : hq.toLp q = u := Lp.ext (hq.coeFn_toLp.trans hu.symm)
  have hweighted : hw.toLp (fun x ↦ q x * √(φ x)) = v :=
    Lp.ext (hw.coeFn_toLp.trans hv.symm)
  have henergy : (∫ x in Ioo 0 L, q x ^ 2 * φ x) = ‖v‖ ^ 2 := by
    rw [← integral_congr_ae hsquare, integral_sq_eq_eLpNorm_toReal_sq hw,
      ← Lp.norm_toLp _ hw, hweighted]
  have hbound := norm_toLp_sq_le_two_mul_weighted_energy_div
    hc hq hodd hsupport hφ (hw.integrable_sq.congr hsquare)
  rw [hto, henergy] at hbound
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 / c)]
  exact hbound.trans_eq (by cas)

/-- Weighted perturbations that are Cauchy give a global unweighted Cauchy
family. No weighted integrability assumption is imposed on the fixed reference. -/
theorem cauchy_of_odd_supported_weighted_cauchy
    {ι : Type*} {l : Filter ι} {q : ι → ℝ → ℝ} {reference φ : ℝ → ℝ} {L c : ℝ}
    (hc : 0 < c)
    {u : ι → Lp ℝ 2 (volume : Measure ℝ)}
    {v : ι → Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) L))}
    (hu : ∀ i, (u i : ℝ → ℝ) =ᵐ[volume] q i)
    (hv : ∀ i, (v i : ℝ → ℝ) =ᵐ[volume.restrict (Ioo 0 L)]
      (fun x ↦ (q i x - reference x) * √(φ x)))
    (hodd : ∀ᶠ i in l, Function.Odd (q i))
    (hsupport : ∀ᶠ i in l, ∀ x, L ≤ x → q i x = 0)
    (hφ : ∀ᵐ x ∂volume.restrict (Ioo 0 L), c ≤ φ x)
    (hweighted : Cauchy (map v l)) :
    Cauchy (map u l) := by
  obtain ⟨hl, hvlimit⟩ := cauchy_map_iff.mp hweighted
  have hnorm : Tendsto (fun p : ι × ι ↦ ‖v p.1 - v p.2‖) (l ×ˢ l) (𝓝 0) := by
    simpa only [dist_eq_norm] using
      tendsto_uniformity_iff_dist_tendsto_zero.mp hvlimit
  have hbound : ∀ᶠ p : ι × ι in l ×ˢ l,
      ‖u p.1 - u p.2‖ ≤ √(2 / c) * ‖v p.1 - v p.2‖ := by
    filter_upwards [hodd.prod_mk hodd, hsupport.prod_mk hsupport] with p ho hs
    apply norm_le_weighted_norm_of_odd_supported hc (q := fun x ↦ q p.1 x - q p.2 x)
    · filter_upwards [Lp.coeFn_sub (u p.1) (u p.2), hu p.1, hu p.2] with x hx hi hj
      simpa only [Pi.sub_apply, hi, hj] using hx
    · filter_upwards [Lp.coeFn_sub (v p.1) (v p.2), hv p.1, hv p.2] with x hx hi hj
      simp only [Pi.sub_apply, hi, hj] at hx
      rw [hx]
      cas
    · intro x
      change q p.1 (-x) - q p.2 (-x) = -(q p.1 x - q p.2 x)
      rw [ho.1 x, ho.2 x]
      cas
    · intro x hx
      simp only [hs.1 x hx, hs.2 x hx, sub_self]
    · exact hφ
  apply cauchy_map_iff.mpr
  refine ⟨hl, tendsto_uniformity_iff_dist_tendsto_zero.mpr ?_⟩
  simp only [dist_eq_norm]
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hbound
  simpa only [mul_zero] using hnorm.const_mul (√(2 / c))

end MeasureTheory
