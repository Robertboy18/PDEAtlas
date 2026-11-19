/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.DynamicRescaling
public import PDE.Representations.Similarity.Pointwise
import CAS.ExactTactic

/-!
# Expanding self-similar fields from an almost everywhere stationary profile

Equal negative stationary rates give the exponent `γ = -1`. With stationary
profile `F`, velocity `U`, and rate `c`, the physical fields are
`ω(x,t) = F((T-t)x) / (|c|(T-t))` and
`u(x,t) = U((T-t)x) / (|c|(T-t)²)`, which is (1.5) of Chen, Hou and Huang with `cl = cω = c`.

The profile and its velocity are assumed differentiable almost everywhere. The
transport equation then holds almost everywhere in space at each time `t < T`, and
the spectral Hilbert relation holds at each such time. If `F y ≠ 0`, the vorticity
tends to infinity in absolute value along the ray `x = y / (T - t)`. The derivative and
residual identities are closed by the `cas` tactic of SymLean.

## References

* J. Chen, T. Y. Hou, and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), no. 6, 1282-1350; numbering of
  arXiv:1905.06387v3, Section 1.2, (1.4) and (1.5), p. 2.
  <https://doi.org/10.1002/cpa.21991>
  <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open PDE.Analysis PDE.Representations.Similarity
open scoped Topology

namespace DeGregorio

/-- The expanding self-similar fields associated with equal stationary rates.
Dividing the profile by `|c|` puts vorticity in the normalization of (1.5) of Chen, Hou and
Huang. -/
def expandingSelfSimilarFields (F U : ℝ → ℝ) (c T : ℝ) : Fields where
  vorticity x t := F ((T - t) * x) / (|c| * (T - t))
  velocity x t := U ((T - t) * x) / (|c| * (T - t) ^ 2)

/-- The vorticity is literally the backward ansatz with amplitude exponent one,
spatial exponent minus one, and profile `F / |c|`. -/
theorem expandingSelfSimilarFields_vorticity_eq_ansatz (F U : ℝ → ℝ) (c T x t : ℝ) :
    (expandingSelfSimilarFields F U c T).vorticity x t =
      backwardSelfSimilarAnsatz (fun y ↦ F y / |c|) 1 (-1) T 0 x t := by
  simp only [expandingSelfSimilarFields, backwardSelfSimilarAnsatz, scaledProfileAnsatz,
    backwardPowerScale, centeredDilation, sub_zero, smul_eq_mul, neg_neg,
    Real.rpow_one, Real.rpow_neg_one, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The spatial derivative of self-similar vorticity at a differentiability point
of the stationary profile. -/
theorem hasDerivAt_expandingSelfSimilarFields_vorticity
    {F U : ℝ → ℝ} {c T x t : ℝ} (hc : c < 0) (ht : t < T)
    (hF : DifferentiableAt ℝ F ((T - t) * x)) :
    HasDerivAt (fun y ↦ (expandingSelfSimilarFields F U c T).vorticity y t)
      (deriv F ((T - t) * x) / |c|) x := by
  have h := (hF.hasDerivAt.comp x ((hasDerivAt_id x).const_mul (T - t))).div_const
    (|c| * (T - t))
  apply h.congr_deriv
  have hcne := (abs_pos.mpr hc.ne).ne'
  have htne := (sub_pos.mpr ht).ne'
  cas

/-- At a differentiability point of the profile, the self-similar vorticity has the
displayed time derivative. -/
theorem hasDerivAt_expandingSelfSimilarFields_time
    {F U : ℝ → ℝ} {c T x t : ℝ} (hc : c < 0) (ht : t < T)
    (hF : DifferentiableAt ℝ F ((T - t) * x)) :
    HasDerivAt ((expandingSelfSimilarFields F U c T).vorticity x)
      ((F ((T - t) * x) - (T - t) * x * deriv F ((T - t) * x)) /
        (|c| * (T - t) ^ 2)) t := by
  have htime := (hasDerivAt_const t T).sub (hasDerivAt_id t)
  have hcne := (abs_pos.mpr hc.ne).ne'
  have htne := (sub_pos.mpr ht).ne'
  have h := (hF.hasDerivAt.comp t (htime.mul_const x)).div (htime.const_mul |c|)
    (mul_ne_zero hcne htne)
  apply h.congr_deriv
  cas

/-- The self-similar velocity has the amplitude required by Biot–Savart. -/
theorem hasDerivAt_expandingSelfSimilarFields_velocity
    {F U : ℝ → ℝ} {c T x t : ℝ} (hc : c < 0) (ht : t < T)
    (hU : DifferentiableAt ℝ U ((T - t) * x)) :
    HasDerivAt (fun y ↦ (expandingSelfSimilarFields F U c T).velocity y t)
      (deriv U ((T - t) * x) / (|c| * (T - t))) x := by
  have h := (hU.hasDerivAt.comp x ((hasDerivAt_id x).const_mul (T - t))).div_const
    (|c| * (T - t) ^ 2)
  apply h.congr_deriv
  have hcne := (abs_pos.mpr hc.ne).ne'
  have htne := (sub_pos.mpr ht).ne'
  cas

/-- Where `F` and `U` are differentiable and the stationary residual vanishes, the
self-similar fields satisfy the physical transport equation with the same `a`. -/
theorem transportResidual_expandingSelfSimilarFields_eq_zero
    {F U : ℝ → ℝ} {a c T x t : ℝ} (hc : c < 0) (ht : t < T)
    (hF : DifferentiableAt ℝ F ((T - t) * x))
    (hU : DifferentiableAt ℝ U ((T - t) * x))
    (hstationary : stationaryResidual a c c F U ((T - t) * x) = 0) :
    transportResidual a (expandingSelfSimilarFields F U c T) x t = 0 := by
  unfold transportResidual
  rw [(hasDerivAt_expandingSelfSimilarFields_time hc ht hF).deriv,
    (hasDerivAt_expandingSelfSimilarFields_vorticity hc ht hF).deriv,
    (hasDerivAt_expandingSelfSimilarFields_velocity hc ht hU).deriv]
  simp only [expandingSelfSimilarFields, abs_of_neg hc]
  unfold stationaryResidual at hstationary
  have hcne := hc.ne
  have htne := (sub_pos.mpr ht).ne'
  cas using hstationary

/-- A stationary a.e. differentiable Hilbert pair produces a self-similar
solution a.e. in space at every time before `T`. All derivatives appearing
in transport are proved to exist on that same full-measure set. -/
theorem expandingSelfSimilarFields_solves_ae
    {F U : ℝ → ℝ} {a c T : ℝ} (hc : c < 0)
    (hF : ∀ᵐ x ∂volume, DifferentiableAt ℝ F x)
    (hU : ∀ᵐ x ∂volume, DifferentiableAt ℝ U x)
    (hstationary : ∀ᵐ x ∂volume, stationaryResidual a c c F U x = 0)
    (hpair : IsHilbertPair F (deriv U)) {t : ℝ} (ht : t < T) :
    (∀ᵐ x ∂volume,
      DifferentiableAt ℝ ((expandingSelfSimilarFields F U c T).vorticity x) t ∧
      DifferentiableAt ℝ (fun y ↦ (expandingSelfSimilarFields F U c T).vorticity y t) x ∧
      DifferentiableAt ℝ (fun y ↦ (expandingSelfSimilarFields F U c T).velocity y t) x ∧
      transportResidual a (expandingSelfSimilarFields F U c T) x t = 0) ∧
    IsHilbertPair (fun x ↦ (expandingSelfSimilarFields F U c T).vorticity x t)
      (deriv (fun x ↦ (expandingSelfSimilarFields F U c T).velocity x t)) := by
  have hdilation := quasiMeasurePreserving_real_dilation (sub_pos.mpr ht).ne'
  have hFd := hdilation.ae hF
  have hUd := hdilation.ae hU
  refine ⟨?_, ?_⟩
  · filter_upwards [hFd, hUd, hdilation.ae hstationary] with x hxF hxU hxs
    exact ⟨(hasDerivAt_expandingSelfSimilarFields_time hc ht hxF).differentiableAt,
      (hasDerivAt_expandingSelfSimilarFields_vorticity hc ht hxF).differentiableAt,
      (hasDerivAt_expandingSelfSimilarFields_velocity hc ht hxU).differentiableAt,
      transportResidual_expandingSelfSimilarFields_eq_zero hc ht hxF hxU hxs⟩
  · have h := (hpair.dilate (sub_pos.mpr ht)).const_mul (|c| * (T - t))⁻¹
    simp only [← div_eq_inv_mul] at h
    apply h.congr_right_ae
    filter_upwards [hUd] with x hx
    exact (hasDerivAt_expandingSelfSimilarFields_velocity hc ht hx).deriv.symm

/-- If `F y ≠ 0`, then `|ω(y / (T - t), t)| → ∞` as `t → T⁻`. This is a property of the
explicit formula and uses no regularity of `F`. -/
theorem expandingSelfSimilarFields_abs_tendsto_atTop
    {F U : ℝ → ℝ} {c T y : ℝ} (hc : c < 0) (hy : F y ≠ 0) :
    Tendsto
      (fun t ↦ |(expandingSelfSimilarFields F U c T).vorticity (y / (T - t)) t|)
      (𝓝[<] T) atTop := by
  have hremaining : Tendsto (fun t : ℝ ↦ T - t) (𝓝[<] T) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hcont : Continuous (fun t : ℝ ↦ T - t) := continuous_const.sub continuous_id
      have hzero : Tendsto (fun t : ℝ ↦ T - t) (𝓝[<] T) (𝓝 (T - T)) :=
        (hcont.tendsto T).mono_left nhdsWithin_le_nhds
      simpa only [sub_self] using hzero
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.mpr ht
  have h := (tendsto_inv_nhdsGT_zero.comp hremaining).const_mul_atTop
    (div_pos (abs_pos.mpr hy) (abs_pos.mpr hc.ne))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hdt : 0 < T - t := sub_pos.mpr ht
  have harg : (T - t) * (y / (T - t)) = y := by cas using hdt.ne'
  change |F y| / |c| * (T - t)⁻¹ =
    |F ((T - t) * (y / (T - t))) / (|c| * (T - t))|
  rw [harg, abs_div, abs_mul, abs_abs, abs_of_pos hdt]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end DeGregorio
