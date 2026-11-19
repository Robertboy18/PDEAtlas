/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakCoefficient
public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakRealEnergy
public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakSourceEvolution
import PDE.Analysis.MeasureTheory.Lp.Primitive.CompactConvergence
import CAS.ExactTactic

/-!
# Weak second-derivative energy for the normalized equation

The normalized velocity is the primitive of the Hilbert transform of the
L² vorticity curve. Its continuity on compact spatial sets supplies one
time-continuous compact transport coefficient. The second weak derivative
vanishes outside the vorticity support, so the cutoff disappears from the
transport energy identity.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Topology Sobolev

namespace DeGregorio

local notation "e" => PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
local notation "L₂" => Lp ℝ 2 (volume : Measure ℝ)

variable {fields : Fields} {ρ : ℝ → ℝ} {a T R : ℝ} {B : NNReal}
  (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo a T))
  (hR : 0 < R) {K : Set ℝ} (hK : IsCompact K)
  {F : ℝ → DerivLp 1 2 univ}
  (hbound : ∀ t ∈ Ioo a T, F t ∈ supportedHkBaseBall 1 2 univ ((e) ⁻¹' K) B)
  (hrep : ∀ t ∈ Ioo a T,
    (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume]
      (fun x ↦ fields.vorticity x t))
  (hzero : ∀ t ∈ Ioo a T, fields.velocity 0 t = 0)
  (hnormalized : ∀ t ∈ Ioo a T, ρ t = -fields.velocity R t / R)

include hsol hR hK hbound hrep hzero hnormalized in
/-- The normalized drift is continuous in time uniformly on compact
spatial sets. Both rate continuity and L² continuity of the vorticity are
consequences of the PDE and the local supported H² bound. -/
theorem IsClassicalRescaledSolutionOn.tendstoUniformlyOn_drift_of_supported_h2
    {c d : ℝ} (hcd : Icc c d ⊆ Ioo a T)
    {D : Set ℝ} (hD : IsCompact D) {t : ℝ} (ht : t ∈ Icc c d) :
    TendstoUniformlyOn (fun s x ↦ ρ s * x + fields.velocity x s)
      (fun x ↦ ρ t * x + fields.velocity x t) (𝓝[Icc c d] t) D := by
  obtain ⟨C, hC⟩ :=
    hsol.exists_lipschitzOnWith_base_of_supported_h2 hR hK hbound hrep hzero hnormalized
  have hρ := (hsol.continuousOn_rate_of_supported_h2 hR hK hbound hrep hzero hnormalized).mono
    hcd
  let H := fun s ↦ realHilbertTransformL2 (oneDimensionalPushforwardL2 (F s))
  have hCH := realHilbertTransformL2.continuous.comp oneDimensionalPushforwardL2.continuous
  have hH : ContinuousOn H (Icc c d) :=
    hCH.comp_continuousOn (hC.continuousOn.mono hcd)
  have hu (s : ℝ) (hs : s ∈ Icc c d) : (fun x ↦ fields.velocity x s) = l2Primitive (H s) := by
    have hi := hcd hs
    have hw : Continuous (fun x ↦ fields.vorticity x s) :=
      continuous_iff_continuousAt.mpr fun _ ↦
        (hsol.regularity.vorticity_spatial_differentiableAt hi).continuousAt
    have hreg := (contDiff_and_bounds_of_hkBaseBall (hbound s hi).1 hw (hrep s hi)).1
    have hsupp : HasCompactSupport (fun x ↦ fields.vorticity x s) :=
      hK.of_isClosed_subset (isClosed_tsupport _)
        (Iteration.tsupport_subset_of_mem_supportedHkBaseBall hK.isClosed (hbound s hi) hw
          (hrep s hi))
    rw [hsol.velocity_eq_hilbertPVVelocity hi hreg hsupp (hzero s hi),
      Iteration.hilbertPVVelocity_eq_l2Primitive_of_ae hreg hsupp (hrep s hi)]
  obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn continuous_id.continuousOn
  have hρt : Tendsto ρ (𝓝[Icc c d] t) (𝓝 (ρ t)) := hρ t ht
  have hHt : Tendsto H (𝓝[Icc c d] t) (𝓝 (H t)) := hH t ht
  have hlim : Tendsto
      (fun s ↦ ‖ρ s - ρ t‖ * M + √M * ‖H s - H t‖) (𝓝[Icc c d] t) (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_mul, mul_zero, add_zero] using
      ((hρt.sub (tendsto_const_nhds (x := ρ t))).norm.mul_const M).add
        ((hHt.sub (tendsto_const_nhds (x := H t))).norm.const_mul (√M))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε), self_mem_nhdsWithin] with s hs hst
  intro x hx
  rw [dist_eq_norm, congrFun (hu t ht) x, congrFun (hu s hst) x]
  have heq : ρ t * x + l2Primitive (H t) x - (ρ s * x + l2Primitive (H s) x) =
      (ρ t - ρ s) * x + l2Primitive (H t - H s) x := by
    rw [l2Primitive_sub]
    ring
  rw [heq]
  have hMx : |x| ≤ M := by simpa only [Real.norm_eq_abs, id_eq] using hM x hx
  calc
    ‖(ρ t - ρ s) * x + l2Primitive (H t - H s) x‖ ≤
        ‖ρ t - ρ s‖ * |x| + ‖l2Primitive (H t - H s) x‖ := by
      simpa only [norm_mul, Real.norm_eq_abs] using
        norm_add_le ((ρ t - ρ s) * x) (l2Primitive (H t - H s) x)
    _ ≤ ‖ρ t - ρ s‖ * M + √M * ‖H t - H s‖ := by
      apply add_le_add (mul_le_mul_of_nonneg_left hMx (norm_nonneg _))
      calc
        ‖l2Primitive (H t - H s) x‖ ≤ √|x| * ‖H t - H s‖ := by
          simpa only [l2Primitive, sub_zero] using
            norm_intervalIntegral_le_sqrt_abs_mul_norm 0 x (H t - H s)
        _ ≤ √M * ‖H t - H s‖ :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hMx) (norm_nonneg _)
    _ < ε := by
      rw [norm_sub_rev (ρ t) (ρ s), norm_sub_rev (H t) (H s)]
      exact hs

include hsol hR hK hbound hrep hzero hnormalized in
/-- The equal-rate normalized drift supplies a compact W¹,∞
transport coefficient on any closed interior slab, with its L∞ time
continuity and derivative bound derived from the local H² bound. -/
theorem IsClassicalRescaledSolutionOn.exists_localized_transport_coefficient
    {c d : ℝ} (hcd : Icc c d ⊆ Ioo a T) :
    ∃ (f : ℝ → ℝ → ℝ) (L : NNReal)
      (A : ℝ → W^{1,∞}((univ : Set (ℝ^1)))),
      ContinuousOn (fun t ↦ (A t : WkpAmbientOn 1 1 ∞ univ) (baseIndex 1 1)) (Icc c d) ∧
      ∀ t ∈ Icc c d,
        ‖(A t : WkpAmbientOn 1 1 ∞ univ) (singleDerivIndex 1 0)‖ ≤ L ∧
        (fun x ↦ (A t : WkpAmbientOn 1 1 ∞ univ) (baseIndex 1 1) ((e).symm x))
          =ᵐ[volume] f t ∧
        (fun x ↦ (A t : WkpAmbientOn 1 1 ∞ univ) (singleDerivIndex 1 0) ((e).symm x))
          =ᵐ[volume] deriv (f t) ∧
        EqOn (f t) (fun x ↦ ρ t * x + fields.velocity x t) K ∧
        EqOn (deriv (f t)) (fun x ↦ ρ t + deriv (fun y ↦ fields.velocity y t) x) K := by
  let V := fun t x ↦ ρ t * x + fields.velocity x t
  have hV (t : ℝ) (ht : t ∈ Icc c d) : ContDiff ℝ 1 (V t) := by
    have hi := hcd ht
    have hw : Continuous (fun x ↦ fields.vorticity x t) :=
      continuous_iff_continuousAt.mpr fun _ ↦
        (hsol.regularity.vorticity_spatial_differentiableAt hi).continuousAt
    have hreg := (contDiff_and_bounds_of_hkBaseBall (hbound t hi).1 hw (hrep t hi)).1
    have hs : HasCompactSupport (fun x ↦ fields.vorticity x t) :=
      hK.of_isClosed_subset (isClosed_tsupport _)
        (Iteration.tsupport_subset_of_mem_supportedHkBaseBall hK.isClosed (hbound t hi) hw
          (hrep t hi))
    have hu : ContDiff ℝ 1 (fun x ↦ fields.velocity x t) := by
      rw [hsol.velocity_eq_hilbertPVVelocity hi hreg hs (hzero t hi)]
      obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hreg one_ne_zero
      exact contDiff_one_hilbertPVVelocity_of_lipschitzWith_compactSupport hD hs
    exact (contDiff_const.mul contDiff_id).add hu
  have hdV (t : ℝ) (ht : t ∈ Icc c d) (x : ℝ) :
      deriv (V t) x = ρ t + deriv (fun y ↦ fields.velocity y t) x := by
    simpa only [V, id_eq, Pi.add_def, mul_one] using
      (((hasDerivAt_id x).const_mul (ρ t)).add
        (hsol.regularity.velocity_differentiableAt (hcd ht)).hasDerivAt).deriv
  have hb (t : ℝ) (ht : t ∈ Icc c d) (x : ℝ) :
      ‖V t x‖ ≤ (4 * B : NNReal) * |x| ∧ ‖deriv (V t) x‖ ≤ (4 * B : NNReal) := by
    have h := hsol.norm_velocity_and_rate_le_of_h2 (hcd ht) hR hK
      (hbound t (hcd ht)) (hrep t (hcd ht)) (hzero t (hcd ht)) (hnormalized t (hcd ht))
    constructor
    · calc
        ‖V t x‖ ≤ ‖ρ t‖ * |x| + ‖fields.velocity x t‖ := by
          simpa only [V, norm_mul, Real.norm_eq_abs] using
            norm_add_le (ρ t * x) (fields.velocity x t)
        _ ≤ 2 * B * |x| + 2 * B * |x| :=
          add_le_add (mul_le_mul_of_nonneg_right h.1 (abs_nonneg _)) (h.2 x).2
        _ = (4 * B : NNReal) * |x| := by push_cast; cas
    · rw [hdV t ht]
      calc
        ‖ρ t + deriv (fun y ↦ fields.velocity y t) x‖ ≤
            ‖ρ t‖ + ‖deriv (fun y ↦ fields.velocity y t) x‖ := norm_add_le _ _
        _ ≤ 2 * B + 2 * B := add_le_add h.1 (h.2 x).1
        _ = (4 * B : NNReal) := by push_cast; cas
  obtain ⟨f, L, A, hAc, hA⟩ := Iteration.exists_localized_w1Top_curve hK hV
    (fun D hD t ht ↦ hsol.tendstoUniformlyOn_drift_of_supported_h2
      hR hK hbound hrep hzero hnormalized hcd hD ht) (4 * B) hb
  refine ⟨f, L, A, hAc, ?_⟩
  intro t ht
  exact ⟨(hA t ht).1, (hA t ht).2.1, (hA t ht).2.2.1, (hA t ht).2.2.2.1,
    fun x hx ↦ ((hA t ht).2.2.2.2 hx).trans (hdV t ht x)⟩

include hsol hR hK hbound hrep hzero hnormalized in
/-- The constructed weak second derivative of the normalized trajectory satisfies the
exact L² energy identity on every closed interior slab, with integrable production.
Local supported H² control justifies the Bochner commutator argument. -/
theorem IsClassicalRescaledSolutionOn.exists_secondDerivative_energy :
    ∃ r G : ℝ → L₂,
      (∀ t ∈ Ioo a T, ‖r t‖ ≤ B ∧
        HasWeakTimeDerivativeOn univ (fun x ↦ fields.vorticity x t)
          (deriv (fun x ↦ fields.vorticity x t)) ∧
        HasWeakTimeDerivativeOn univ (deriv (fun x ↦ fields.vorticity x t)) (r t)) ∧
      (∀ ℓ : L₂ →L[ℝ] ℝ, ContinuousOn (fun t ↦ ℓ (r t)) (Ioo a T)) ∧
      (∀ c d : ℝ, Icc c d ⊆ Ioo a T →
        MemLp r 2 (volume.restrict (Ioc c d)) ∧
        MemLp G 2 (volume.restrict (Ioc c d))) ∧
      (∀ t ∈ Ioo a T, (G t : ℝ → ℝ) =ᵐ[volume] fun x ↦
        -(ρ t + deriv (fun y ↦ fields.velocity y t) x) * r t x +
          realHilbertTransformL2 (r t) x * fields.vorticity x t +
            deriv (deriv (fun y ↦ fields.velocity y t)) x *
              deriv (fun y ↦ fields.vorticity y t) x) ∧
      ∀ c d : ℝ, c < d → Icc c d ⊆ Ioo a T →
        Integrable (fun t ↦
          (∫ x, (ρ t + deriv (fun y ↦ fields.velocity y t) x) * (r t x) ^ 2) +
            2 * inner ℝ (G t) (r t)) (volume.restrict (Ioc c d)) ∧
        ‖r d‖ ^ 2 - ‖r c‖ ^ 2 =
          ∫ t in Ioc c d,
            (∫ x, (ρ t + deriv (fun y ↦ fields.velocity y t) x) * (r t x) ^ 2) +
              2 * inner ℝ (G t) (r t) := by
  obtain ⟨r, G, hr, hrc, hmem, hG, htest⟩ :=
    hsol.exists_bochner_secondDerivative_transport hR hK hbound hrep hzero hnormalized
  refine ⟨r, G, hr, hrc, hmem, hG, ?_⟩
  intro c d hlt hcd
  obtain ⟨f, L, A, hAc, hA⟩ :=
    hsol.exists_localized_transport_coefficient hR hK hbound hrep hzero hnormalized hcd
  have hproducts (t : ℝ) (ht : t ∈ Icc c d) :
      (fun x ↦ f t x * r t x) =ᵐ[volume]
        (fun x ↦ (ρ t * x + fields.velocity x t) * r t x) ∧
      (fun x ↦ deriv (f t) x * r t x) =ᵐ[volume]
        (fun x ↦ (ρ t + deriv (fun y ↦ fields.velocity y t) x) * r t x) := by
    have hi := hcd ht
    have hw : Continuous (fun x ↦ fields.vorticity x t) :=
      continuous_iff_continuousAt.mpr fun _ ↦
        (hsol.regularity.vorticity_spatial_differentiableAt hi).continuousAt
    have hreg := (contDiff_and_bounds_of_hkBaseBall (hbound t hi).1 hw (hrep t hi)).1
    have hsupp := Iteration.tsupport_subset_of_mem_supportedHkBaseBall hK.isClosed
      (hbound t hi) hw (hrep t hi)
    have hrzero := Iteration.ae_weakDerivative_eq_zero_outside (hr t hi).2.2
      (hreg.continuous_deriv le_rfl) (tsupport_deriv_subset.trans hsupp)
    constructor
    · filter_upwards [hrzero] with x hx
      by_cases hxK : x ∈ K
      · rw [(hA t ht).2.2.2.1 hxK]
      · rw [hx hxK, mul_zero, mul_zero]
    · filter_upwards [hrzero] with x hx
      by_cases hxK : x ∈ K
      · rw [(hA t ht).2.2.2.2 hxK]
      · rw [hx hxK, mul_zero, mul_zero]
  have hlocalized :
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
        ∀ t ∈ Icc c d, HasDerivAt (fun τ ↦ ∫ x, r τ x * ψ x)
          ((∫ x, f t x * r t x * deriv ψ x) +
            ∫ x, (deriv (f t) x * r t x + G t x) * ψ x) t := by
    intro ψ hψ hψc t ht
    apply (htest t (hcd ht) ψ hψ hψc).congr_deriv
    congr 1
    · apply integral_congr_ae
      filter_upwards [(hproducts t ht).1] with x hx
      rw [hx]
    · apply integral_congr_ae
      filter_upwards [(hproducts t ht).2] with x hx
      rw [hx]
  have heq :
      (fun t ↦ (∫ x, deriv (f t) x * (r t x) ^ 2) + 2 * inner ℝ (G t) (r t))
        =ᵐ[volume.restrict (Ioc c d)] (fun t ↦
          (∫ x, (ρ t + deriv (fun y ↦ fields.velocity y t) x) * (r t x) ^ 2) +
            2 * inner ℝ (G t) (r t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    congr 1
    apply integral_congr_ae
    filter_upwards [(hproducts t (Ioc_subset_Icc_self ht)).2] with x hx
    rw [pow_two, ← mul_assoc, hx, mul_assoc]
  have hI := Iteration.integrable_real_transport_production hlt.le A hAc L
    (fun t ht ↦ (hA t ht).1) (fun t ht ↦ (hA t ht).2.2.1)
    (hmem c d hcd).1 (hmem c d hcd).2
  have hE := Iteration.real_energy_sub_eq_integral_of_smooth_test_derivative hlt A hAc L
    (fun t ht ↦ (hA t ht).1) (fun t ht ↦ (hA t ht).2.1)
    (fun t ht ↦ (hA t ht).2.2.1) (fun ℓ ↦ (hrc ℓ).mono hcd)
    (hmem c d hcd).1 (hmem c d hcd).2 hlocalized
  exact ⟨hI.congr heq, hE.trans (integral_congr_ae heq)⟩

end DeGregorio
