/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakH1Energy
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Grönwall for the weak second derivative of the normalized equation

The energy identity first supplies continuity of the squared norm by an
integrable primitive. The H¹ production estimate then gives an exponential
bound whose constants do not depend on the local H² bound used to justify
the weak transport calculation.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Topology Sobolev

namespace DeGregorio.Iteration

/-- Integral energy balance supplies the norm continuity needed for
Grönwall. The scalar production need only be integrable. -/
theorem augmented_energy_le_exp_of_integral_eq
    {E : Type*} [NormedAddCommGroup E] {r : ℝ → E} {P : ℝ → ℝ}
    {a b M C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (hP : Integrable P (volume.restrict (Ioc a b)))
    (henergy : ∀ t ∈ Icc a b,
      ‖r t‖ ^ 2 - ‖r a‖ ^ 2 = ∫ s in Ioc a t, P s)
    (hbound : ∀ t ∈ Icc a b, P t ≤ C * (M ^ 2 + ‖r t‖ ^ 2)) :
    ∀ t ∈ Icc a b,
      M ^ 2 + ‖r t‖ ^ 2 ≤ (M ^ 2 + ‖r a‖ ^ 2) * Real.exp (C * (t - a)) := by
  let e := fun t ↦ M ^ 2 + ‖r t‖ ^ 2
  have hPi : IntervalIntegrable P volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hP
  have heq (t : ℝ) (ht : t ∈ Icc a b) : e t = e a + ∫ s in a..t, P s := by
    rw [intervalIntegral.integral_of_le ht.1, ← henergy t ht]
    dsimp only [e]
    ring
  have hprimitive : ContinuousOn (fun t ↦ ∫ s in a..t, P s) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval' hPi left_mem_uIcc
  have he : ContinuousOn e (Icc a b) :=
    (continuousOn_const.add hprimitive).congr (fun t ht ↦ heq t ht)
  apply le_mul_exp_of_le_const_add_mul_intervalIntegral he hC
  intro t ht
  have hPiAt := hPi.mono_set (uIcc_subset_uIcc_left (by simpa only [uIcc_of_le hab] using ht))
  have heiAt : IntervalIntegrable e volume a t :=
    (he.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hi := intervalIntegral.integral_mono_on ht.1 hPiAt (heiAt.const_mul C)
    (fun s hs ↦ hbound s ((Icc_subset_Icc_right ht.2) hs))
  rw [intervalIntegral.integral_const_mul] at hi
  rw [heq t ht]
  exact add_le_add le_rfl hi

end DeGregorio.Iteration

namespace DeGregorio

local notation "e" => PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
local notation "L₂" => Lp ℝ 2 (volume : Measure ℝ)

/-- H¹ control bounds the weak second derivative on each
interior slab of a normalized trajectory. The local H² bound supplies
integrability only: the exponential bound is independent of that bound.
Rate bounds and velocity bounds are derived from endpoint normalization
and the coupled Hilbert relation. -/
theorem IsClassicalRescaledSolutionOn.exists_secondDerivative_gronwall
    {fields : Fields} {ρ : ℝ → ℝ} {a T R M : ℝ} {B : NNReal}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo a T))
    (hR : 0 < R) {K : Set ℝ} (hK : IsCompact K)
    {F : ℝ → DerivLp 1 2 univ}
    (hbound : ∀ t ∈ Ioo a T, F t ∈ supportedHkBaseBall 1 2 univ ((e) ⁻¹' K) B)
    (hrep : ∀ t ∈ Ioo a T,
      (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume]
        (fun x ↦ fields.vorticity x t))
    (hzero : ∀ t ∈ Ioo a T, fields.velocity 0 t = 0)
    (hnormalized : ∀ t ∈ Ioo a T, ρ t = -fields.velocity R t / R)
    (hH1 : ∀ t ∈ Ioo a T,
      lpNorm (fun x ↦ fields.vorticity x t) 2 volume +
        lpNorm (deriv (fun x ↦ fields.vorticity x t)) 2 volume ≤ M) :
    ∃ r : ℝ → L₂,
      (∀ t ∈ Ioo a T,
        HasWeakTimeDerivativeOn univ (fun x ↦ fields.vorticity x t)
          (deriv (fun x ↦ fields.vorticity x t)) ∧
        HasWeakTimeDerivativeOn univ (deriv (fun x ↦ fields.vorticity x t)) (r t)) ∧
      ∀ c d : ℝ, c < d → Icc c d ⊆ Ioo a T → ∀ t ∈ Icc c d,
        M ^ 2 + ‖r t‖ ^ 2 ≤ (M ^ 2 + ‖r c‖ ^ 2) * Real.exp (11 * M * (t - c)) := by
  obtain ⟨r, G, hr, _, _, hG, hE⟩ :=
    hsol.exists_secondDerivative_energy hR hK hbound hrep hzero hnormalized
  refine ⟨r, fun t ht ↦ (hr t ht).2, ?_⟩
  intro c d hlt hcd
  let P := fun t ↦
    (∫ x, (ρ t + deriv (fun y ↦ fields.velocity y t) x) * (r t x) ^ 2) +
      2 * inner ℝ (G t) (r t)
  have hM : 0 ≤ M :=
    (add_nonneg lpNorm_nonneg lpNorm_nonneg).trans (hH1 c (hcd ⟨le_rfl, hlt.le⟩))
  have hproduction (t : ℝ) (ht : t ∈ Icc c d) : P t ≤ 11 * M * (M ^ 2 + ‖r t‖ ^ 2) := by
    have hi := hcd ht
    have hw : Continuous (fun x ↦ fields.vorticity x t) :=
      continuous_iff_continuousAt.mpr fun _ ↦
        (hsol.regularity.vorticity_spatial_differentiableAt hi).continuousAt
    obtain ⟨W, _, hWbase⟩ := (hbound t hi).1
    have hrepW : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) : ℝ → ℝ)
        =ᵐ[volume] fun x ↦ fields.vorticity x t := hWbase ▸ hrep t hi
    obtain ⟨_, hreg, hq, _, _⟩ := Iteration.exists_weak_secondDerivative_of_h2 W hw hrepW
    have hs : HasCompactSupport (fun x ↦ fields.vorticity x t) :=
      hK.of_isClosed_subset (isClosed_tsupport _)
        (Iteration.tsupport_subset_of_mem_supportedHkBaseBall hK.isClosed (hbound t hi) hw
          (hrep t hi))
    have hu : ContDiff ℝ 1 (fun x ↦ fields.velocity x t) := by
      rw [hsol.velocity_eq_hilbertPVVelocity hi hreg hs (hzero t hi)]
      obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hreg one_ne_zero
      exact contDiff_one_hilbertPVVelocity_of_lipschitzWith_compactSupport hD hs
    have hsource := hG t hi
    rw [hnormalized t hi] at hsource
    have hp := Iteration.norm_secondDerivative_energy_production_le_of_weak_jet
      hreg hu (hsol.biotSavart hi) (hr t hi).2.1 (hr t hi).2.2 hq (hzero t hi) hR
      (hH1 t hi) hsource
    apply (le_abs_self (P t)).trans
    simpa only [P, hnormalized t hi, Real.norm_eq_abs] using hp
  apply Iteration.augmented_energy_le_exp_of_integral_eq hlt.le
    (mul_nonneg (by norm_num) hM) (hE c d hlt hcd).1 _ hproduction
  intro t ht
  rcases ht.1.eq_or_lt with heq | hct
  · subst t
    simp only [sub_self, Ioc_self, Measure.restrict_empty, integral_zero_measure]
  · exact (hE c t hct ((Icc_subset_Icc_right ht.2).trans hcd)).2

end DeGregorio
