/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Operator
public import PDE.Analysis.Calculus.CompactEnergy.Integration
import PDE.DistributionTheory.TestFunction.IntegrationByParts

/-!
# Spatial mass of a compactly propagating wave

The mass is the spatial integral of a spacetime field. Forward finite propagation and
joint `C²` regularity suffice to differentiate it twice at positive times.

The time derivative inherits the forward support cone, including its initial slice. The proof at
that boundary uses uniqueness of right derivatives. Spatial coordinate integration by parts then
removes the Laplacian.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common
open scoped Topology

namespace WaveEquation.SmallData

variable {n : ℕ}

/-- The spatial mass of a real spacetime field. -/
def spatialMass (u : ℝ^(n + 1) → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ^n, u (timeSpaceCons t x)

/-- Forward propagation at speed one from the closed ball of radius `R`. -/
def HasForwardSupport (u : ℝ^(n + 1) → ℝ) (R : ℝ) : Prop :=
  ∀ t, 0 ≤ t → ∀ x : ℝ^n, R + t < ‖x‖ → u (timeSpaceCons t x) = 0

/-- Every forward slice has compact support. -/
theorem HasForwardSupport.hasCompactSupport_slice {u : ℝ^(n + 1) → ℝ} {R t : ℝ}
    (hs : HasForwardSupport u R) (ht : 0 ≤ t) :
    HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^n) (R + t)) ?_
  intro x hx
  exact hs t ht x (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx)

/-- The time derivative inherits the forward support, also at time zero. -/
theorem HasForwardSupport.partialDeriv_time {u : ℝ^(n + 1) → ℝ} {R : ℝ}
    (hs : HasForwardSupport u R) :
    HasForwardSupport (∂[0] u) R := by
  intro t ht x hx
  by_cases hu : DifferentiableAt ℝ u (timeSpaceCons t x)
  swap
  · change fderiv ℝ u (timeSpaceCons t x) (EuclideanSpace.single 0 1) = 0
    rw [fderiv_zero_of_not_differentiableAt hu, zero_apply]
  have hnear : ∀ᶠ s in 𝓝 t, s < ‖x‖ - R :=
    Iio_mem_nhds (by linarith)
  have heq : (fun s ↦ u (timeSpaceCons s x)) =ᶠ[𝓝[≥] t] fun _ ↦ (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin, hnear.filter_mono nhdsWithin_le_nhds] with s hst hsx
    exact hs s (ht.trans hst) x (by linarith [hsx])
  have hd := (PDE.hasDerivAt_timeSpaceCons u t x hu).hasDerivWithinAt (s := Ici t)
  have hz := (hasDerivWithinAt_const t (Ici t) (0 : ℝ)).congr_of_eventuallyEq heq (hs t ht x hx)
  exact (hd.derivWithin (uniqueDiffWithinAt_Ici t)).symm.trans
    (hz.derivWithin (uniqueDiffWithinAt_Ici t))

/-- The first mass derivative follows from the local compact integral theorem. -/
theorem hasDerivAt_spatialMass {u : ℝ^(n + 1) → ℝ} {R t : ℝ} (hu : ContDiff ℝ 1 u)
    (hs : HasForwardSupport u R) (ht : 0 < t) :
    HasDerivAt (spatialMass u) (spatialMass (∂[0] u) t) t := by
  apply PDE.Analysis.hasDerivAt_integral_compact_support
    (I := Ioo 0 (t + 1)) (K := Metric.closedBall 0 (R + (t + 1)))
    isOpen_Ioo (isCompact_closedBall _ _) (fun _ _ _ ↦ hu.contDiffAt)
  · intro s hsI x hx
    have hnorm : R + (t + 1) < ‖x‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    exact hs s hsI.1.le x (by linarith [hsI.2])
  · exact ⟨ht, by linarith⟩

/-- The second mass derivative is the integral of the second time derivative. -/
theorem hasDerivAt_spatialMass_time {u : ℝ^(n + 1) → ℝ} {R t : ℝ} (hu : ContDiff ℝ 2 u)
    (hs : HasForwardSupport u R) (ht : 0 < t) :
    HasDerivAt (spatialMass (∂[0] u)) (spatialMass (∂[0] (∂[0] u)) t) t :=
  hasDerivAt_spatialMass (PDE.contDiff_partialDeriv_of_succ (m := 1) hu)
    hs.partialDeriv_time ht

/-- Integrating the spatial Laplacian of a compact `C²` slice gives zero. -/
theorem integral_spatial_laplacian_eq_zero {u : ℝ^(n + 1) → ℝ} {t : ℝ} (hu : ContDiff ℝ 2 u)
    (hs : HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) :
    (∫ x : ℝ^n, ∑ i : Fin n, (∂[i.succ] (∂[i.succ] u)) (timeSpaceCons t x)) = 0 := by
  let v : ℝ^n → ℝ := fun x ↦ u (timeSpaceCons t x)
  have hv : ContDiff ℝ 2 v := hu.comp (contDiff_timeSpaceCons_spatial n t)
  have hfirst (i : Fin n) :
      (∂[i] v) = fun x ↦ (∂[i.succ] u) (timeSpaceCons t x) := by
    funext x
    exact PDE.partialDeriv_timeSpaceCons_spatial i u t x (hu.differentiable (by norm_num) _)
  have hsecond (i : Fin n) (x : ℝ^n) :
      (∂[i] (∂[i] v)) x = (∂[i.succ] (∂[i.succ] u)) (timeSpaceCons t x) := by
    rw [hfirst]
    exact PDE.partialDeriv_timeSpaceCons_spatial i (∂[i.succ] u) t x
      ((PDE.contDiff_partialDeriv_of_succ (m := 1) hu).differentiable one_ne_zero _)
  have hc (i : Fin n) : ContDiff ℝ 1 (∂[i] v) := PDE.contDiff_partialDeriv_of_succ (m := 1) hv
  have hk (i : Fin n) : HasCompactSupport (∂[i] v) := hs.fderiv_apply ℝ (EuclideanSpace.single i 1)
  simp_rw [← hsecond]
  rw [integral_finsetSum Finset.univ (fun i _ ↦
    PDE.DistributionTheory.integrable_partialDeriv_of_hasCompactSupport i (hc i) (hk i))]
  simp only [PDE.DistributionTheory.integral_partialDeriv_eq_zero_of_hasCompactSupport _ (hc _)
    (hk _), Finset.sum_const_zero]

/-- The integrated wave equation, with its source integral. -/
theorem spatialMass_time_time_eq_integral_source {u : ℝ^(n + 1) → ℝ} {R t p : ℝ}
    (hu : ContDiff ℝ 2 u) (hs : HasForwardSupport u R) (ht : 0 ≤ t)
    (hwave : ∀ x : ℝ^n, waveOperator u (timeSpaceCons t x) = |u (timeSpaceCons t x)| ^ p) :
    spatialMass (∂[0] (∂[0] u)) t = ∫ x : ℝ^n, |u (timeSpaceCons t x)| ^ p := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hud : ContDiff ℝ 1 (∂[0] u) := PDE.contDiff_partialDeriv_of_succ (m := 1) hu
  have hint : Integrable (fun x : ℝ^n ↦ (∂[0] (∂[0] u)) (timeSpaceCons t x)) :=
    ((PDE.contDiff_partialDeriv_of_succ (m := 0) hud).continuous.comp
      (contDiff_timeSpaceCons_spatial n t (m := 1)).continuous).integrable_of_hasCompactSupport
        (hs.partialDeriv_time.partialDeriv_time |>.hasCompactSupport_slice ht)
  have hsum : Integrable (fun x : ℝ^n ↦
      ∑ i : Fin n, (∂[i.succ] (∂[i.succ] u)) (timeSpaceCons t x)) := by
    apply integrable_finsetSum
    intro i _
    have hc := PDE.contDiff_partialDeriv_of_succ (m := 1) (i := i.succ) hu
    have hslicec : ContDiff ℝ 1 (fun x : ℝ^n ↦ (∂[i.succ] u) (timeSpaceCons t x)) :=
      hc.comp (contDiff_timeSpaceCons_spatial n t)
    have hslicek : HasCompactSupport (fun x : ℝ^n ↦
        (∂[i.succ] u) (timeSpaceCons t x)) := by
      have heq : (fun x : ℝ^n ↦ (∂[i.succ] u) (timeSpaceCons t x)) =
          ∂[i] (fun x : ℝ^n ↦ u (timeSpaceCons t x)) := by
        funext x
        exact (PDE.partialDeriv_timeSpaceCons_spatial i u t x
          (hu1.differentiable one_ne_zero _)).symm
      rw [heq]
      exact (hs.hasCompactSupport_slice ht).fderiv_apply ℝ (EuclideanSpace.single i 1)
    have hd := PDE.DistributionTheory.integrable_partialDeriv_of_hasCompactSupport i hslicec hslicek
    exact hd.congr (Eventually.of_forall fun x ↦
      PDE.partialDeriv_timeSpaceCons_spatial i (∂[i.succ] u) t x (hc.differentiable one_ne_zero _))
  have heq : (∫ x : ℝ^n, |u (timeSpaceCons t x)| ^ p) =
      spatialMass (∂[0] (∂[0] u)) t := by
    simp_rw [← hwave]
    change (∫ x : ℝ^n, (∂[0] (∂[0] u)) (timeSpaceCons t x) -
      ∑ i : Fin n, (∂[i.succ] (∂[i.succ] u)) (timeSpaceCons t x)) = _
    rw [integral_sub hint hsum,
      integral_spatial_laplacian_eq_zero hu (hs.hasCompactSupport_slice ht), sub_zero]
    rfl
  exact heq.symm

/-- The derivative of the mass velocity is the nonnegative source integral. -/
theorem hasDerivAt_spatialMass_time_eq_source {u : ℝ^(n + 1) → ℝ} {R t p : ℝ} (hu : ContDiff ℝ 2 u)
    (hs : HasForwardSupport u R) (ht : 0 < t)
    (hwave : ∀ x : ℝ^n, waveOperator u (timeSpaceCons t x) = |u (timeSpaceCons t x)| ^ p) :
    HasDerivAt (spatialMass (∂[0] u)) (∫ x : ℝ^n, |u (timeSpaceCons t x)| ^ p) t := by
  rw [← spatialMass_time_time_eq_integral_source hu hs ht.le hwave]
  exact hasDerivAt_spatialMass_time hu hs ht

/-- Ordinary second derivatives of the mass satisfy the integrated PDE. -/
theorem deriv_deriv_spatialMass_eq_source {u : ℝ^(n + 1) → ℝ} {R t p : ℝ} (hu : ContDiff ℝ 2 u)
    (hs : HasForwardSupport u R) (ht : 0 < t)
    (hwave : ∀ x : ℝ^n, waveOperator u (timeSpaceCons t x) = |u (timeSpaceCons t x)| ^ p) :
    deriv (deriv (spatialMass u)) t = ∫ x : ℝ^n, |u (timeSpaceCons t x)| ^ p := by
  have heq : deriv (spatialMass u) =ᶠ[𝓝 t] spatialMass (∂[0] u) := by
    filter_upwards [Ioi_mem_nhds ht] with s hsI
    exact (hasDerivAt_spatialMass (hu.of_le (by norm_num)) hs hsI).deriv
  exact (hasDerivAt_spatialMass_time_eq_source hu hs ht hwave
    |>.congr_of_eventuallyEq heq).deriv

end WaveEquation.SmallData
