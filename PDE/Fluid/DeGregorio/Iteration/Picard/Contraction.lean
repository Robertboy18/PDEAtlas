/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.DifferenceEnergy.Interior
public import PDE.Fluid.DeGregorio.Iteration.Picard.Output
public import PDE.Analysis.MeasureTheory.Lp.Distance
public import PDE.Fluid.DeGregorio.Iteration.Contraction
import CAS.ExactTactic

/-!
# Contraction of the frozen H² outputs

The output graph gives the spatial bounds, the frozen PDE gives the energy
rate, and the L²-continuous curve gives both endpoint traces. The velocity
enters only through its spatial derivatives.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Common DeGregorio
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

variable {B : NNReal} {T R : ℝ} {hT : 0 ≤ T}
  {f g F G : C(Icc (0 : ℝ) T,
    supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)}
  {W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))} {w₀ : ℝ → ℝ} {c d w z : ℝ → ℝ → ℝ}

/-- The frozen velocity has C¹ spatial slices; its time dependence
requires only the joint continuity constructed from the L² input curve. -/
theorem IsHkFrozenOutput.contDiff_velocity
    (h : IsHkFrozenOutput hT f F W₀ w₀ c w) (t : ℝ) :
    ContDiff ℝ 1 (fun x ↦ hkCurveHilbertVelocity hT f x t) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x ↦ (h.velocity_derivative x t).differentiableAt, ?_⟩
  have heq : deriv (fun x ↦ hkCurveHilbertVelocity hT f x t) = fun x ↦ c x t :=
    funext fun x ↦ (h.velocity_derivative x t).deriv
  rw [heq]
  exact h.coefficient_continuous.comp (continuous_id.prodMk continuous_const)

/-- The output H² bound gives the spatial bounds used in the energy inequality. -/
theorem IsHkFrozenOutput.spatial_bounds
    (h : IsHkFrozenOutput hT f F W₀ w₀ c w) (t : Icc (0 : ℝ) T) (x : ℝ) :
    ‖w x t‖ ≤ 2 * (B : ℝ) ∧ ‖deriv (fun y ↦ w y t) x‖ ≤ 2 * (B : ℝ) := by
  exact (contDiff_and_bounds_of_hkBaseBall (F t).property.1
    (h.continuous.comp (continuous_id.prodMk continuous_const)) (h.representative t)).2 x

/-- The coefficient form of the frozen PDE equals the velocity derivative form. -/
theorem IsHkFrozenOutput.satisfies_transport
    (h : IsHkFrozenOutput hT f F W₀ w₀ c w) :
    SatisfiesTransportEquationOn 1 ⟨w, hkCurveHilbertVelocity hT f⟩ (Ioo 0 T) := by
  intro x t ht
  simpa only [one_mul, (h.velocity_derivative x t).deriv] using h.transport x t ht

/-- The bounded spatial energy is exactly the squared output L² distance,
including the endpoint times. -/
theorem IsHkFrozenOutput.differenceEnergy_eq_dist_sq
    (hf : IsHkFrozenOutput hT f F W₀ w₀ c w)
    (hg : IsHkFrozenOutput hT g G W₀ w₀ d z)
    {L : ℝ} (hRL : R ≤ L) (t : Icc (0 : ℝ) T) :
    differenceEnergy ⟨w, hkCurveHilbertVelocity hT f⟩
      ⟨z, hkCurveHilbertVelocity hT g⟩ L t = dist (F t) (G t) ^ 2 := by
  have heq := dist_sq_eq_setIntegral_sq_sub_of_support
    (oneDimensionalPushforwardL2 (F t).val) (oneDimensionalPushforwardL2 (G t).val)
    (hf.representative t) (hg.representative t) (K := Icc (-L) L) (by
      intro x hx
      have hLx : L < |x| := lt_of_not_ge fun h ↦ hx (abs_le.mp h)
      exact ⟨hf.support x t t.property (hRL.trans_lt hLx),
        hg.support x t t.property (hRL.trans_lt hLx)⟩)
  rw [oneDimensionalPushforwardL2.isometry.dist_eq] at heq
  exact heq.symm

/-- Two frozen outputs satisfy the quantitative difference estimate
in terms of the uniform L² distance of their inputs. -/
theorem IsHkFrozenOutput.dist_sq_le
    (hf : IsHkFrozenOutput hT f F W₀ w₀ c w)
    (hg : IsHkFrozenOutput hT g G W₀ w₀ d z)
    {L : ℝ} (hL : 0 ≤ L) (hRL : R < L) (t : Icc (0 : ℝ) T) :
    dist (F t) (G t) ^ 2 ≤ dist f g ^ 2 *
      gronwallBound 0 (5 * (2 * (B : ℝ)))
        ((2 * (B : ℝ)) * (1 + 2 * L ^ 2)) t := by
  let fields : Fields := ⟨w, hkCurveHilbertVelocity hT f⟩
  let other : Fields := ⟨z, hkCurveHilbertVelocity hT g⟩
  have htrace : ContinuousOn (differenceEnergy fields other L) (Icc 0 T) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : (Icc (0 : ℝ) T).domRestrict (differenceEnergy fields other L) =
        fun s ↦ dist (F s) (G s) ^ 2 := by
      funext s
      exact hf.differenceEnergy_eq_dist_sq hg hRL.le s
    rw [heq]
    exact (F.continuous.dist G.continuous).pow 2
  have hinit : differenceEnergy fields other L 0 = 0 := by
    simp only [differenceEnergy, fields, other, hf.initial, hg.initial,
      sub_self, zero_pow (by norm_num : 2 ≠ 0), integral_zero]
  have hestimate := differenceEnergy_le_gronwallBound_of_frozen_transport_interior
    (fields := fields) (other := other)
    (f := fun x s ↦ oneDimensionalPushforwardL2 (f (projIcc 0 T hT s)).val x)
    (g := fun x s ↦ oneDimensionalPushforwardL2 (g (projIcc 0 T hT s)).val x)
    hf.classical hg.classical (fun s _ ↦ hf.contDiff_velocity s)
    (fun s _ ↦ hg.contDiff_velocity s) hf.satisfies_transport hg.satisfies_transport
    (fun s _ ↦ (hf.hilbert_pair s).congr_right_ae
      (.of_forall fun x ↦ (hf.velocity_derivative x s).deriv.symm))
    (fun s _ ↦ (hg.hilbert_pair s).congr_right_ae
      (.of_forall fun x ↦ (hg.velocity_derivative x s).deriv.symm))
    hL (by positivity : 0 ≤ 2 * (B : ℝ)) (by
      intro s hs
      have hl : R < |-L| := by simpa only [abs_neg, abs_of_nonneg hL] using hRL
      have hr : R < |L| := by simpa only [abs_of_nonneg hL] using hRL
      exact ⟨(hf.support (-L) s (Ioo_subset_Icc_self hs) hl).trans
        (hg.support (-L) s (Ioo_subset_Icc_self hs) hl).symm,
        (hf.support L s (Ioo_subset_Icc_self hs) hr).trans
        (hg.support L s (Ioo_subset_Icc_self hs) hr).symm⟩) (by
      intro s _
      simp only [fields, other, hkCurveHilbertVelocity, l2Primitive,
        intervalIntegral.integral_same]) (by
      intro s hs x _
      have hb := hg.spatial_bounds ⟨s, Ioo_subset_Icc_self hs⟩ x
      change |deriv (fun y ↦ hkCurveHilbertVelocity hT f y s) x| ≤ _ ∧ _
      rw [(hf.velocity_derivative x s).deriv]
      exact ⟨hf.coefficient_bound x s, hb⟩) htrace hinit (M := dist f g ^ 2) (by
      intro s _
      rw [← dist_sq_eq_integral_sq_sub_of_ae_eq
        (oneDimensionalPushforwardL2 (f (projIcc 0 T hT s)).val)
        (oneDimensionalPushforwardL2 (g (projIcc 0 T hT s)).val)
        EventuallyEq.rfl EventuallyEq.rfl, oneDimensionalPushforwardL2.isometry.dist_eq]
      change dist (f (projIcc 0 T hT s)) (g (projIcc 0 T hT s)) ^ 2 ≤ dist f g ^ 2
      gcongr
      exact ContinuousMap.dist_apply_le_dist _)
  have hresult := hestimate t t.property
  rw [hf.differenceEnergy_eq_dist_sq hg hRL.le t] at hresult
  simpa only [sub_zero] using hresult

/-- A numerical bound on the explicit time factor makes any two frozen
outputs contract in the uniform L² metric of the complete supported H² class. -/
theorem IsHkFrozenOutput.dist_le_sqrt_half
    (hf : IsHkFrozenOutput hT f F W₀ w₀ c w)
    (hg : IsHkFrozenOutput hT g G W₀ w₀ d z)
    {L : ℝ} (hL : 0 ≤ L) (hRL : R < L)
    (hsmall : ∀ s ∈ Icc 0 T,
      gronwallBound 0 (5 * (2 * (B : ℝ)))
        ((2 * (B : ℝ)) * (1 + 2 * L ^ 2)) s ≤ 1 / 2) :
    dist F G ≤ Real.sqrt (1 / 2) * dist f g := by
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro t
  apply (sq_le_sq₀ dist_nonneg (by positivity)).mp
  calc
    dist (F t) (G t) ^ 2 ≤ dist f g ^ 2 *
        gronwallBound 0 (5 * (2 * (B : ℝ)))
          ((2 * (B : ℝ)) * (1 + 2 * L ^ 2)) t :=
      hf.dist_sq_le hg hL hRL t
    _ ≤ dist f g ^ 2 * (1 / 2) :=
      mul_le_mul_of_nonneg_left (hsmall t t.property) (sq_nonneg _)
    _ = (Real.sqrt (1 / 2) * dist f g) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      cas

end DeGregorio.Iteration
