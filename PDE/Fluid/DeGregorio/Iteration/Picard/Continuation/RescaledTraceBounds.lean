/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.FiniteTraceNormalized
public import PDE.Fluid.DeGregorio.DynamicRescaling.PrincipalValue
import CAS.ExactTactic

/-!
# Time control for the normalized rescaled equation

A supported H² slice controls the normalized velocity and its derivative.
The endpoint formula for the equal rescaling rates then bounds both the
stretching coefficient and the transport drift on the support. The PDE
therefore gives a common L² majorant for the time derivative and a Lipschitz
L² trajectory.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- An H² base bound controls the principal-value coefficient and primitive
through the lower-order H¹ graph. -/
theorem norm_hilbertPV_and_velocity_of_h2_base
    {B : ℝ} {F : DerivLp 1 2 univ} (hF : F ∈ hkBaseBall 1 2 univ B)
    {v : ℝ → ℝ} (hv : ContDiff ℝ 1 v) (hs : HasCompactSupport v)
    (hrep : (oneDimensionalPushforwardL2 F : ℝ → ℝ) =ᵐ[volume] v) (x : ℝ) :
    ‖hilbertPV v x‖ ≤ 2 * B ∧ ‖hilbertPVVelocity v x‖ ≤ 2 * B * |x| := by
  obtain ⟨W, hW, hWbase⟩ := hF
  let J := lowerOrderCLM (by decide : 1 ≤ 2) W
  have hJ : ‖J‖ ≤ B := (norm_lowerOrderCLM_apply_le _ W).trans hW
  have hr : (realLineCoordinateCLM (baseIndex 1 1) J : ℝ → ℝ) =ᵐ[volume] v := by
    apply (realLineCoordinate_ae_representative J).trans
    apply (realLineRepresentative_lowerOrder_ae W).symm.trans
    simpa only [hWbase] using hrep
  have hb := norm_hilbertPV_and_velocity_of_h1 J hv hs hr x
  have hJB : 2 * ‖J‖ ≤ 2 * B := mul_le_mul_of_nonneg_left hJ (by norm_num)
  exact ⟨hb.1.trans hJB, hb.2.trans (mul_le_mul_of_nonneg_right hJB (abs_nonneg _))⟩

/-- A pointwise time derivative with a common L² majorant controls the L²
trajectory. The mean value theorem is applied before taking the spatial norm. -/
theorem lipschitzOnWith_base_of_time_derivative_majorant
    {a T : ℝ} {F : ℝ → DerivLp 1 2 univ} {w z : ℝ → ℝ → ℝ} {M : ℝ → ℝ}
    (hrep : ∀ t ∈ Ioo a T,
      (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume] fun x ↦ w x t)
    (hderiv : ∀ x, ∀ t ∈ Ioo a T, HasDerivAt (w x) (z x t) t)
    (hM : MemLp M 2 volume)
    (hmajorant : ∀ᵐ x ∂volume, ∀ t ∈ Ioo a T, ‖z x t‖ ≤ M x) :
    LipschitzOnWith ‖hM.toLp M‖₊ F (Ioo a T) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [dist_eq_norm, ← oneDimensionalPushforwardL2.norm_map, map_sub, Real.dist_eq]
  have hnorm :
      ‖oneDimensionalPushforwardL2 (F s) - oneDimensionalPushforwardL2 (F t)‖ ≤
        ‖s - t‖ * ‖hM.toLp M‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub (oneDimensionalPushforwardL2 (F s))
      (oneDimensionalPushforwardL2 (F t)), hrep s hs, hrep t ht,
      hM.coeFn_toLp, hmajorant] with x hsub hxs hxt hxM hx
    rw [hsub, Pi.sub_apply, hxs, hxt, hxM]
    have hdiff := (convex_Ioo a T).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r hr ↦ (hderiv x r hr).hasDerivWithinAt) hx ht hs
    exact hdiff.trans (by
      calc
        M x * ‖s - t‖ ≤ ‖M x‖ * ‖s - t‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
        _ = ‖s - t‖ * ‖M x‖ := mul_comm _ _)
  simpa only [Real.norm_eq_abs, coe_nnnorm, mul_comm] using hnorm

end DeGregorio.Iteration

namespace DeGregorio

/-- The rescaled velocity and its endpoint-normalized rate are bounded
by the supported H² slice. Classical C¹ spatial regularity is recovered from
the graph bound, and the Hilbert relation identifies the normalized velocity. -/
theorem IsClassicalRescaledSolutionOn.norm_velocity_and_rate_le_of_h2
    {fields : Fields} {ρ : ℝ → ℝ} {times : Set ℝ}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ times)
    {t R : ℝ} {B : NNReal} (ht : t ∈ times) (hR : 0 < R)
    {K : Set ℝ} (hK : IsCompact K) {F : DerivLp 1 2 univ}
    (hbound : F ∈ supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B)
    (hrep : (oneDimensionalPushforwardL2 F : ℝ → ℝ) =ᵐ[volume]
      (fun x ↦ fields.vorticity x t))
    (hzero : fields.velocity 0 t = 0) (hnormalized : ρ t = -fields.velocity R t / R) :
    |ρ t| ≤ 2 * B ∧ ∀ x,
      ‖deriv (fun y ↦ fields.velocity y t) x‖ ≤ 2 * B ∧
        ‖fields.velocity x t‖ ≤ 2 * B * |x| := by
  have hw : Continuous (fun x ↦ fields.vorticity x t) :=
    continuous_iff_continuousAt.mpr fun _ ↦
      (hsol.regularity.vorticity_spatial_differentiableAt ht).continuousAt
  have hreg := (contDiff_and_bounds_of_hkBaseBall hbound.1 hw hrep).1
  have hs : HasCompactSupport (fun x ↦ fields.vorticity x t) :=
    hK.of_isClosed_subset (isClosed_tsupport _)
      (Iteration.tsupport_subset_of_mem_supportedHkBaseBall hK.isClosed hbound hw hrep)
  have hu := hsol.velocity_eq_hilbertPVVelocity ht hreg hs hzero
  have hpoint (x : ℝ) :
      ‖deriv (fun y ↦ fields.velocity y t) x‖ ≤ 2 * B ∧
        ‖fields.velocity x t‖ ≤ 2 * B * |x| := by
    have h := Iteration.norm_hilbertPV_and_velocity_of_h2_base hbound.1 hreg hs hrep x
    rw [hu, (hasDerivAt_hilbertPVVelocity_of_contDiff_one_compactSupport hreg hs x).deriv]
    exact ⟨h.1, by simpa only [← congrFun hu x] using h.2⟩
  refine ⟨?_, hpoint⟩
  rw [hnormalized, abs_div, abs_neg, abs_of_pos hR]
  apply (div_le_iff₀ hR).mpr
  simpa only [Real.norm_eq_abs, abs_of_pos hR] using (hpoint R).2

/-- Uniform supported H² control constructs a common L² majorant for the
time derivative of the vorticity. The endpoint normalization supplies the rate bound. -/
theorem IsClassicalRescaledSolutionOn.exists_timeDerivative_majorant_of_supported_h2
    {fields : Fields} {ρ : ℝ → ℝ} {a T R : ℝ} {B : NNReal}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo a T))
    (hR : 0 < R) {K : Set ℝ} (hK : IsCompact K)
    {F : ℝ → DerivLp 1 2 univ}
    (hbound : ∀ t ∈ Ioo a T, F t ∈ supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B)
    (hrep : ∀ t ∈ Ioo a T,
      (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume]
        (fun x ↦ fields.vorticity x t))
    (hzero : ∀ t ∈ Ioo a T, fields.velocity 0 t = 0)
    (hnormalized : ∀ t ∈ Ioo a T, ρ t = -fields.velocity R t / R) :
    ∃ M : ℝ → ℝ, MemLp M 2 volume ∧
      ∀ x, ∀ t ∈ Ioo a T, ‖deriv (fields.vorticity x) t‖ ≤ M x := by
  let V := fun x t ↦ ρ t * x + fields.velocity x t
  have hV (x t : ℝ) (ht : t ∈ Ioo a T) :
      deriv (fun y ↦ V y t) x = ρ t + deriv (fun y ↦ fields.velocity y t) x := by
    simpa only [V, id_eq, Pi.add_def, mul_one] using
      (((hasDerivAt_id x).const_mul (ρ t)).add
      (hsol.regularity.velocity_differentiableAt ht).hasDerivAt).deriv
  have hb (t : ℝ) (ht : t ∈ Ioo a T) :=
    hsol.norm_velocity_and_rate_le_of_h2 ht hR hK (hbound t ht) (hrep t ht)
      (hzero t ht) (hnormalized t ht)
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  have hvelocity (t : ℝ) (ht : t ∈ Ioo a T) (x : ℝ) (hx : x ∈ K) :
      ‖V x t‖ ≤ (4 * B * D.toNNReal : NNReal) ∧
        ‖deriv (fun y ↦ V y t) x‖ ≤ (4 * B : NNReal) := by
    have hfour : 2 * (B : ℝ) + 2 * B = 4 * B := by cas
    have hxD : |x| ≤ D.toNNReal :=
      (show |x| ≤ D by simpa only [Real.norm_eq_abs, id_eq] using hD x hx).trans
        (Real.le_coe_toNNReal D)
    constructor
    · calc
        ‖V x t‖ ≤ ‖ρ t‖ * |x| + ‖fields.velocity x t‖ := by
          simpa only [V, norm_mul, Real.norm_eq_abs] using
            norm_add_le (ρ t * x) (fields.velocity x t)
        _ ≤ 2 * B * |x| + 2 * B * |x| :=
          add_le_add (mul_le_mul_of_nonneg_right (hb t ht).1 (abs_nonneg _))
            ((hb t ht).2 x).2
        _ = 4 * B * |x| := by rw [← add_mul, hfour]
        _ ≤ (4 * B * D.toNNReal : NNReal) :=
          mul_le_mul_of_nonneg_left hxD (by positivity)
    · rw [hV x t ht]
      exact (norm_add_le _ _).trans ((add_le_add (hb t ht).1 ((hb t ht).2 x).1).trans_eq
        hfour)
  have hw (t : ℝ) (ht : t ∈ Ioo a T) : Continuous (fun x ↦ fields.vorticity x t) :=
    continuous_iff_continuousAt.mpr fun _ ↦
      (hsol.regularity.vorticity_spatial_differentiableAt ht).continuousAt
  obtain ⟨M, hM, hmajorant⟩ :=
    Iteration.exists_transport_majorant_of_supported_h2 hK hbound hw hrep hvelocity
  refine ⟨M, hM, ?_⟩
  intro x t ht
  have heq : deriv (fields.vorticity x) t =
      deriv (fun y ↦ V y t) x * fields.vorticity x t -
        V x t * deriv (fun y ↦ fields.vorticity y t) x := by
    rw [hV x t ht]
    simpa only [one_mul, V] using eq_sub_of_add_eq (hsol.transport (x := x) ht)
  rw [heq]
  exact hmajorant x t ht

/-- Uniform supported H² control gives a time-Lipschitz L² trajectory for the
equal-rate rescaled PDE. The rate and time-derivative bounds come from the H² control
and the endpoint normalization. -/
theorem IsClassicalRescaledSolutionOn.exists_lipschitzOnWith_base_of_supported_h2
    {fields : Fields} {ρ : ℝ → ℝ} {a T R : ℝ} {B : NNReal}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo a T))
    (hR : 0 < R) {K : Set ℝ} (hK : IsCompact K)
    {F : ℝ → DerivLp 1 2 univ}
    (hbound : ∀ t ∈ Ioo a T, F t ∈ supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B)
    (hrep : ∀ t ∈ Ioo a T,
      (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume]
        (fun x ↦ fields.vorticity x t))
    (hzero : ∀ t ∈ Ioo a T, fields.velocity 0 t = 0)
    (hnormalized : ∀ t ∈ Ioo a T, ρ t = -fields.velocity R t / R) :
    ∃ C : NNReal, LipschitzOnWith C F (Ioo a T) := by
  obtain ⟨M, hM, hmajorant⟩ :=
    hsol.exists_timeDerivative_majorant_of_supported_h2 hR hK hbound hrep hzero hnormalized
  exact ⟨‖hM.toLp M‖₊, Iteration.lipschitzOnWith_base_of_time_derivative_majorant hrep
    (fun _ _ ht ↦ (hsol.regularity.vorticity_time_differentiableAt ht).hasDerivAt)
    hM (Eventually.of_forall hmajorant)⟩

end DeGregorio
