/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
public import PDE.FDeriv.SpaceTime
public import PDE.Hyperbolic.Models.Wave.Equation
import PDE.FDeriv.Calculus

/-!
# Spacetime calculus for the wave operator

The coordinate wave operator agrees with time differentiation minus the
spatial Laplacian. For a `C³` field it commutes with every coordinate derivative.
These facts apply to wave constructions in every spatial dimension.
-/

@[expose] public noncomputable section

open PDE (partialDeriv laplacian)

namespace WaveEquation

open PDE.Common

/-- The spatial slice Laplacian uses only the C² germ at the spacetime point. -/
theorem laplacian_timeSlice_of_contDiffAt {n : ℕ} (u : ℝ^(n + 1) → ℝ) (t : ℝ) (y : ℝ^n)
    (hu : ContDiffAt ℝ 2 u (timeSpaceCons t y)) :
    laplacian (fun z ↦ u (timeSpaceCons t z)) y = ∑ i : Fin n,
      (∂[i.succ] (fun p ↦ (∂[i.succ] u) p)) (timeSpaceCons t y) := by
  classical
  unfold laplacian
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hfirst : (fun z ↦ (∂[i] (fun w ↦ u (timeSpaceCons t w))) z) =ᶠ[nhds y]
        fun z ↦ (∂[i.succ] u) (timeSpaceCons t z) := by
    have hevent := hu.eventually (by simp)
    have hcurve : ContinuousAt (timeSpaceCons (n := n) t) y :=
      (contDiff_timeSpaceCons_spatial n t (m := 1)).continuous.continuousAt
    filter_upwards [hcurve.preimage_mem_nhds hevent] with z hz
    change ContDiffAt ℝ 2 u (timeSpaceCons t z) at hz
    exact PDE.partialDeriv_timeSpaceCons_spatial i u t z
      (hz.differentiableAt (by norm_num))
  rw [PDE.partialDeriv_congr_nhds i hfirst]
  exact PDE.partialDeriv_timeSpaceCons_spatial i (fun p ↦ (∂[i.succ] u) p) t y
    ((PDE.contDiffAt_partialDeriv 1 hu i.succ).differentiableAt one_ne_zero)

/-- The Laplacian of a fixed-time spatial slice is the sum of the spacetime
second derivatives in the spatial coordinates. -/
theorem laplacian_timeSlice {n : ℕ} (u : ℝ^(n + 1) → ℝ) (t : ℝ) (y : ℝ^n) (hu : ContDiff ℝ 2 u) :
    laplacian (fun z ↦ u (timeSpaceCons t z)) y = ∑ i : Fin n,
      (∂[i.succ] (fun p ↦ (∂[i.succ] u) p)) (timeSpaceCons t y) :=
  laplacian_timeSlice_of_contDiffAt u t y hu.contDiffAt

/-- Computing the second time derivative only requires a C² germ. -/
theorem secondPartialDeriv_timeSpaceCons_of_contDiffAt {n : ℕ} {u : ℝ^(n + 1) → ℝ} {x : ℝ^n} {t : ℝ}
    (hu : ContDiffAt ℝ 2 u (timeSpaceCons t x)) :
    (∂[0] (∂[0] u)) (timeSpaceCons t x) = deriv (deriv (fun s ↦ u (timeSpaceCons s x))) t := by
  rw [PDE.partialDeriv_timeSpaceCons_eq_deriv _ _ _
    ((PDE.contDiffAt_partialDeriv 1 hu 0).differentiableAt one_ne_zero)]
  apply Filter.EventuallyEq.deriv_eq
  have hc : ContinuousAt (fun s ↦ timeSpaceCons (n := n) s x) t :=
    ((timeSpaceContinuousLinearEquiv n).symm.continuous.comp
      (continuous_id.prodMk continuous_const)).continuousAt
  filter_upwards [hc.preimage_mem_nhds (hu.eventually (by norm_num))] with s hs
  change ContDiffAt ℝ 2 u (timeSpaceCons s x) at hs
  exact PDE.partialDeriv_timeSpaceCons_eq_deriv u x s (hs.differentiableAt (by norm_num))

/-- The second time-coordinate derivative is the second derivative of a
fixed-space time trace. -/
theorem secondPartialDeriv_timeSpaceCons {n : ℕ} {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (x : ℝ^n) (t : ℝ) :
    (∂[0] (∂[0] u)) (timeSpaceCons t x) = deriv (deriv (fun s ↦ u (timeSpaceCons s x))) t :=
  secondPartialDeriv_timeSpaceCons_of_contDiffAt hu.contDiffAt

/-- The trace form of the wave operator uses only C² regularity near the point. -/
theorem waveOperator_timeSpaceCons_of_contDiffAt {n : ℕ} {u : ℝ^(n + 1) → ℝ} {x : ℝ^n} {t : ℝ}
    (hu : ContDiffAt ℝ 2 u (timeSpaceCons t x)) :
    waveOperator u (timeSpaceCons t x) = deriv (deriv (fun s ↦ u (timeSpaceCons s x))) t -
      laplacian (fun y ↦ u (timeSpaceCons t y)) x := by
  rw [waveOperator, ← laplacian_timeSlice_of_contDiffAt u t x hu,
    secondPartialDeriv_timeSpaceCons_of_contDiffAt hu]

/-- The coordinate wave operator agrees with the time-trace derivative minus
the Laplacian of the fixed-time slice. -/
theorem waveOperator_timeSpaceCons {n : ℕ} {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (x : ℝ^n) (t : ℝ) :
    waveOperator u (timeSpaceCons t x) = deriv (deriv (fun s ↦ u (timeSpaceCons s x))) t -
      laplacian (fun y ↦ u (timeSpaceCons t y)) x :=
  waveOperator_timeSpaceCons_of_contDiffAt hu.contDiffAt

/-- Differentiating a `C³` field commutes with the constant-coefficient wave
operator. -/
theorem waveOperator_partialDeriv {n : ℕ} {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 3 u) (i : Fin (n + 1)) (p : ℝ^(n + 1)) :
    waveOperator (∂[i] u) p = (∂[i] (waveOperator u)) p := by
  have hreg (j : Fin (n + 1)) : ContDiff ℝ 1 (∂[j] (∂[j] u)) :=
    PDE.contDiff_partialDeriv_of_succ (m := 1) (PDE.contDiff_partialDeriv_of_succ (m := 2) hu)
  have hcomm (j : Fin (n + 1)) : (∂[i] (∂[j] (∂[j] u))) =
        (∂[j] (∂[j] (∂[i] u))) := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      PDE.partialDeriv_iterate_partialDeriv_comm i j 2 hu
  have hsum : (∂[i] (fun q ↦ ∑ j : Fin n, (∂[j.succ] (∂[j.succ] u)) q)) p =
      ∑ j : Fin n, (∂[i] (∂[j.succ] (∂[j.succ] u))) p := by
    unfold partialDeriv
    rw [fderiv_fun_sum (fun j _ ↦ (hreg j.succ).differentiable one_ne_zero p)]
    simp
  have hsumdiff : DifferentiableAt ℝ (fun q ↦ ∑ j : Fin n, (∂[j.succ] (∂[j.succ] u)) q) p :=
    DifferentiableAt.fun_sum fun j _ ↦ (hreg j.succ).differentiable one_ne_zero p
  unfold waveOperator
  rw [PDE.partialDeriv_sub ((hreg 0).differentiable one_ne_zero p) hsumdiff, hsum]
  simp only [hcomm]

/-- A coordinate derivative of a `C³` wave is a wave on the open
positive-time half-space. The residual is differentiated only there. -/
theorem waveOperator_partialDeriv_eq_zero_of_positive_time {n : ℕ} {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 3 u) (hw : ∀ p, 0 < p 0 → waveOperator u p = 0) (i : Fin (n + 1))
    {p : ℝ^(n + 1)} (hp : 0 < p 0) :
    waveOperator (∂[i] u) p = 0 := by
  rw [waveOperator_partialDeriv hu]
  have hlocal : waveOperator u =ᶠ[nhds p] fun _ ↦ 0 := by
    have hopen : IsOpen {q : ℝ^(n + 1) | 0 < q 0} :=
      isOpen_lt continuous_const (PiLp.continuous_apply 2 _ 0)
    filter_upwards [hopen.mem_nhds hp] with q hq using hw q hq
  rw [PDE.partialDeriv_congr_nhds i hlocal, PDE.partialDeriv_const]

end WaveEquation
