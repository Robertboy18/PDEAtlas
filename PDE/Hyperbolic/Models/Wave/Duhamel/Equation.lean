/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Calculus.Hessian
public import PDE.Analysis.Integration.Retarded.Regularity

/-!
# The wave operator of a retarded integral

The second Leibniz endpoint is the kernel's initial velocity. The remaining
term integrates its wave operator. Joint continuity of two spatial and age derivatives gives
integrability on the finite time interval.
-/

@[expose] public noncomputable section

namespace WaveEquation

open PDE.Analysis PDE.Common MeasureTheory

/-- The wave operator of a retarded kernel is its age-zero velocity plus the
retarded integral of its wave operator. This identity also holds at signed times. -/
theorem waveOperator_retardedIntegral {n : ℕ} {F : ℝ → ℝ^n × ℝ → ℝ} (hF : ∀ s, ContDiff ℝ 2 (F s))
    (hjet : ∀ j ≤ 2, Continuous (fun p : ℝ × (ℝ^n × ℝ) ↦ iteratedFDeriv ℝ j (F p.1) p.2))
    (hzero : ∀ s x, F s (x, 0) = 0) (x : ℝ^n) (t : ℝ) :
    waveOperator (fun p ↦ retardedIntegral F (splitSpaceTime p)) (timeSpaceCons t x) =
      fderiv ℝ (F t) (x, 0) (0, 1) + ∫ s in (0 : ℝ)..t,
      waveOperator (fun p ↦ F s (splitSpaceTime p)) (timeSpaceCons (t - s) x) := by
  have hc : Continuous (fun p : ℝ × (ℝ^n × ℝ) ↦ F p.1 p.2) :=
    PDE.continuous_of_continuous_iteratedFDeriv_zero_family (hjet 0 (by omega))
  have hD : Continuous (fun p : ℝ × (ℝ^n × ℝ) ↦ fderiv ℝ (F p.1) p.2) :=
    PDE.continuous_of_continuous_iteratedFDeriv_zero_family (f := fun s ↦ fderiv ℝ (F s))
      (PDE.continuous_iteratedFDeriv_fderiv_family (f := F) (j := 0) (hjet 1 (by omega)))
  have hDD : Continuous (fun p : ℝ × (ℝ^n × ℝ) ↦ fderiv ℝ (fderiv ℝ (F p.1)) p.2) :=
    PDE.continuous_of_continuous_iteratedFDeriv_zero_family (f := fun s ↦ fderiv ℝ (fderiv ℝ (F s)))
      (PDE.continuous_iteratedFDeriv_fderiv_family (f := fun s ↦ fderiv ℝ (F s)) (j := 0)
        (PDE.continuous_iteratedFDeriv_fderiv_family (f := F) (j := 1) (hjet 2 (by omega))))
  have hint (v : ℝ^n × ℝ) : IntervalIntegrable
      (fun s ↦ fderiv ℝ (fderiv ℝ (F s)) (x, t - s) v v) volume 0 t :=
    (((hDD.comp (continuous_id.prodMk
      (continuous_const.prodMk (continuous_const.sub continuous_id)))).clm_apply
        continuous_const).clm_apply continuous_const).intervalIntegrable 0 t
  have hsecond (v : ℝ^n × ℝ) := fderiv_fderiv_retardedIntegral_apply
      (fun s ↦ (hF s).differentiable (by norm_num))
      (fun s ↦ ((hF s).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero)
      hc hD hDD hzero (x, t) v v
  have hi : (∫ s in (0 : ℝ)..t,
      waveOperator (fun p ↦ F s (splitSpaceTime p)) (timeSpaceCons (t - s) x)) =
      (∫ s in (0 : ℝ)..t, fderiv ℝ (fderiv ℝ (F s)) (x, t - s) (0, 1) (0, 1)) -
        ∑ i : Fin n, ∫ s in (0 : ℝ)..t, fderiv ℝ (fderiv ℝ (F s)) (x, t - s)
            (EuclideanSpace.single i (1 : ℝ), 0) (EuclideanSpace.single i (1 : ℝ), 0) := by
    simp_rw [waveOperator_comp_splitSpaceTime (hF _)]
    change (∫ s in (0 : ℝ)..t, fderiv ℝ (fderiv ℝ (F s)) (x, t - s) (0, 1) (0, 1) -
        ∑ i : Fin n, fderiv ℝ (fderiv ℝ (F s)) (x, t - s)
          (EuclideanSpace.single i (1 : ℝ), 0) (EuclideanSpace.single i (1 : ℝ), 0)) = _
    rw [intervalIntegral.integral_sub (hint (0, 1))
      (by
        simpa only [Finset.sum_fn] using (IntervalIntegrable.sum (Finset.univ : Finset (Fin n))
          (fun i _ ↦ hint (EuclideanSpace.single i (1 : ℝ), 0))))]
    congr 1
    exact intervalIntegral.integral_finsetSum (fun i _ ↦ hint (EuclideanSpace.single i (1 : ℝ), 0))
  rw [waveOperator_comp_splitSpaceTime (contDiff_two_retardedIntegral hF hjet hzero)]
  change fderiv ℝ (fderiv ℝ (retardedIntegral F)) (x, t) (0, 1) (0, 1) -
    ∑ i : Fin n, fderiv ℝ (fderiv ℝ (retardedIntegral F)) (x, t)
      (EuclideanSpace.single i (1 : ℝ), 0) (EuclideanSpace.single i (1 : ℝ), 0) = _
  simp only [hsecond, one_smul, zero_smul, zero_add, hi]
  ring

end WaveEquation
