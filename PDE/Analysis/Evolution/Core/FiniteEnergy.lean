/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Core.Dissipation
public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Distributional
import PDE.Analysis.Evolution.Core.EnergyIdentity
import PDE.Analysis.Evolution.Time.AbsoluteContinuity
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Finite Hilbert energies with weak time derivatives

For a real Hilbert space `X`, a function in `L²(a, b; X)` with weak time
derivative in `L²(a, b; X)` has an absolutely continuous representative. For a
finite family `uᵢ`, an almost-everywhere inequality
`2 ∑ᵢ ⟪uᵢ, uᵢ'⟫ + d ≤ K ∑ᵢ ‖uᵢ‖² + f` therefore bounds `∑ᵢ ‖uᵢ(t)‖²` at every
`t ∈ [a, b]` and bounds `∫ₐᵇ d`. The bounds hold for any continuous
representative, since two continuous representatives agree on `[a, b]`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Evolution

open MeasureTheory Set
open scoped InnerProductSpace

/-- Grönwall and dissipation estimates for a finite family of weak
trajectories. Let `uᵢ ∈ L²(a, b; X)` have weak derivatives `vᵢ` on `(a, b)` and
let `z` be continuous on `[a, b]` with `z(·)ᵢ = uᵢ` almost everywhere. If
`2 ∑ᵢ ⟪uᵢ, vᵢ⟫ + d ≤ K ∑ᵢ ‖uᵢ‖² + f` almost everywhere, with `K ≥ 0` and `d, f`
integrable and nonnegative, then
`∑ᵢ ‖z(t)ᵢ‖² ≤ (∑ᵢ ‖z(a)ᵢ‖² + ∫ₐᵇ f) e^{K(t-a)}` on `[a, b]` and
`∫ₐᵇ d ≤ (1 + K(b-a) e^{K(b-a)}) (∑ᵢ ‖z(a)ᵢ‖² + ∫ₐᵇ f)`. -/
theorem finite_weak_energy_estimates
    {X ι : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [Fintype ι] {a b K : ℝ} (hab : a < b) (hK : 0 ≤ K)
    (u v : ι → Lp X 2 (volume.restrict (Ioc a b)))
    (hweak : ∀ i, HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ u i t) (fun t ↦ v i t))
    (z : ℝ → ι → X) (hz : ContinuousOn z (Icc a b))
    (hzu : ∀ i, (fun t ↦ z t i) =ᵐ[volume.restrict (Ioc a b)] fun t ↦ u i t)
    (d f : ℝ → ℝ)
    (hd : IntervalIntegrable d volume a b) (hf : IntervalIntegrable f volume a b)
    (hd0 : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ d t)
    (hf0 : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ f t)
    (he : ∀ᵐ t ∂volume.restrict (Ioc a b),
      2 * (∑ i, ⟪u i t, v i t⟫_ℝ) + d t ≤ K * (∑ i, ‖u i t‖ ^ 2) + f t) :
    (∀ t ∈ Icc a b,
      (∑ i, ‖z t i‖ ^ 2) ≤
        ((∑ i, ‖z a i‖ ^ 2) + ∫ s in a..b, f s) * Real.exp (K * (t - a))) ∧
    (∫ t in a..b, d t) ≤
      (1 + K * (b - a) * Real.exp (K * (b - a))) *
        ((∑ i, ‖z a i‖ ^ 2) + ∫ s in a..b, f s) := by
  classical
  choose w hw huw hwd hwa using fun i ↦
    (hweak i).exists_absolutelyContinuousRepresentative_eq_initial hab
      (fun t ↦ z t i) ((continuous_apply i).comp_continuousOn hz) (hzu i)
  let e (t : ℝ) := ∑ i, ‖w i t‖ ^ 2
  have hAC : AbsolutelyContinuousOnInterval e a b :=
    AbsolutelyContinuousOnInterval.finset_sum Finset.univ
      (fun i _ ↦ absolutelyContinuousOnInterval_norm_sq (hw i))
  have hnonneg (t : ℝ) (_ht : t ∈ Icc a b) : 0 ≤ e t :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hzpoint (t : ℝ) (ht : t ∈ Icc a b) (i : ι) : z t i = w i t := by
    have hae : (fun t ↦ z t i) =ᵐ[volume.restrict (Icc a b)] w i := by
      rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
      exact (hzu i).trans (huw i)
    exact Measure.eqOn_Icc_of_ae_eq volume hab.ne hae
      ((continuous_apply i).comp_continuousOn hz)
      (by simpa only [uIcc_of_le hab.le] using (hw i).continuousOn) ht
  have heq : ∀ᵐ t ∂volume.restrict (Ioc a b),
      deriv e t + d t ≤ K * e t + f t := by
    filter_upwards [ae_all_iff.mpr hwd, ae_all_iff.mpr huw, he] with t hdt hut het
    have hderiv : HasDerivAt e (2 * ∑ i, ⟪w i t, v i t⟫_ℝ) t := by
      simpa only [e, Finset.mul_sum] using
        HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ (hdt i).norm_sq)
    rw [hderiv.deriv]
    simpa only [e, hut] using het
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioc a b),
      deriv e t ≤ K * e t + f t := by
    filter_upwards [heq, hd0] with t ht hdt
    linarith
  have hbound := le_mul_exp_of_absolutelyContinuousOnInterval_deriv_le
    hab.le hAC hf hf0 hK hdiff
  have hdiss := integral_dissipation_le_of_deriv_add_le
    hab.le hK hAC hnonneg hd hf hd0 hf0 heq
  have hinit : e a = ∑ i, ‖z a i‖ ^ 2 := by simp only [e, hwa]
  constructor
  · intro t ht
    have htrace : e t = ∑ i, ‖z t i‖ ^ 2 := by simp only [e, hzpoint t ht]
    simpa only [htrace, hinit] using hbound t ht
  · simpa only [hinit] using hdiss

end PDE.Analysis.Evolution
