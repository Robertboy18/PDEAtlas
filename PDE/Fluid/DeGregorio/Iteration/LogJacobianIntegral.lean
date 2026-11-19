/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.WeakJacobianIntegrand
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Integral

/-!
# The differentiated log-Jacobian as an H¹ integral

The characteristic integrand `c_x(X(x,t),t) J(x,t)` has a uniformly bounded
H¹ graph by the frozen slice construction. Its continuous scalar evaluations
give a Bochner-integrable graph family. The resulting L² integral
has an H¹ representative equal at every point to the derivative of the
log-Jacobian.

This integral gives the weak derivative needed to construct the H²
characteristic amplitude.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

private theorem continuous_clamped_characteristic_integrand
    {T : ℝ} (hT : 0 ≤ T) {c d X : ℝ → ℝ → ℝ}
    (hc : Continuous (Function.uncurry c)) (hd : Continuous (Function.uncurry d))
    (hX : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ X p.1 p.2)) :
    Continuous (fun p : ℝ × ℝ ↦
      d (X p.1 (projIcc 0 T hT p.2)) (projIcc 0 T hT p.2) *
        Real.exp (∫ s in 0..(projIcc 0 T hT p.2 : ℝ), c (X p.1 s) s)) := by
  let Z : ℝ → ℝ → ℝ := fun x t ↦ X x (projIcc 0 T hT t)
  have hZ : Continuous (Function.uncurry Z) :=
    hX.comp (continuous_fst.prodMk ((continuous_projIcc (h := hT)).comp continuous_snd))
  let k : ℝ → ℝ → ℝ := fun x t ↦ c (Z x t) t
  have hk : Continuous (Function.uncurry k) := hc.comp (hZ.prodMk continuous_snd)
  have hint (x : ℝ) (t : Icc (0 : ℝ) T) :
      (∫ s in 0..(t : ℝ), k x s) = ∫ s in 0..(t : ℝ), c (X x s) s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.property.1] at hs
    change c (X x (projIcc 0 T hT s)) s = c (X x s) s
    rw [projIcc_of_mem hT ⟨hs.1, hs.2.trans t.property.2⟩]
  have htime : Continuous (fun p : ℝ × ℝ ↦ (projIcc 0 T hT p.2 : ℝ)) :=
    continuous_subtype_val.comp ((continuous_projIcc (h := hT)).comp continuous_snd)
  have hJ := (intervalIntegral.continuous_parametric_primitive_of_continuous
    (μ := volume) (a₀ := (0 : ℝ)) hk).rexp.comp (continuous_fst.prodMk htime)
  simpa only [Function.comp_def, hint, Z, Function.uncurry, Pi.mul_def] using
    (hd.comp (hZ.prodMk htime)).mul hJ

/-- The spatial derivative of the log-Jacobian is the time integral
of the characteristic integrand, including the endpoints of the time interval. -/
theorem hasDerivAt_hkCurve_logJacobian
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    {c X : ℝ → ℝ → ℝ} (hchar : HkForwardCharacteristics hT f c X)
    (x t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivAt (fun y ↦ ∫ s in 0..t, c (X y s) s)
      (∫ s in 0..t, deriv (fun y ↦ c y s) (X x s) *
        Real.exp (∫ r in 0..s, c (X x r) r)) x := by
  have h := (hasDerivAt_hkCurve_jacobian hT f hchar x t ht).log (Real.exp_ne_zero _)
  simpa only [Real.log_exp, mul_div_cancel_left₀ _ (Real.exp_ne_zero _)] using h

/-- The characteristic integrand is Bochner integrable in L² on `0..t`.
Its integral has an H¹ graph bounded by `t` times the frozen slice budget,
and its continuous representative is the spatial derivative of the
log-Jacobian. The L² family is identified with the integrand at every time. -/
theorem exists_h1_hkCurve_logJacobian_derivative
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    {c X Y : ℝ → ℝ → ℝ} (hchar : HkCharacteristics hT f c X Y)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∃ F : ℝ → Lp ℝ 2 volume, IntervalIntegrable F volume 0 t ∧
      (∀ s, s ∈ Icc (0 : ℝ) T →
        (F s : ℝ → ℝ) =ᵐ[volume] (fun x ↦ deriv (fun y ↦ c y s) (X x s) *
          Real.exp (∫ r in 0..s, c (X x r) r))) ∧
      ∃ U : W^{1,2}((Set.univ : Set (ℝ^1))),
        ‖U‖ ≤ t * (Real.sqrt (Real.exp (2 * (B : ℝ) * T)) *
          ((Real.exp (2 * (B : ℝ) * T) +
            (2 * (B : ℝ) * T + 1) * Real.exp (4 * (B : ℝ) * T)) * B)) ∧
        realLineCoordinateCLM (baseIndex 1 1) U = (∫ s in 0..t, F s) ∧
        realLineRepresentative U = (fun x ↦ ∫ s in 0..t,
          deriv (fun y ↦ c y s) (X x s) * Real.exp (∫ r in 0..s, c (X x r) r)) ∧
        (∀ x, HasDerivAt (fun y ↦ ∫ s in 0..t, c (X y s) s)
          (realLineRepresentative U x) x) := by
  obtain ⟨d, hd, hcd, _hdbound, _hdmod⟩ :=
    exists_hkCurve_hilbert_coefficient_hasDerivAt hT f hchar.coefficient_continuous
      hchar.hilbert_pair
  let D : ℝ → ℝ → ℝ := fun s x ↦
    d (X x (projIcc 0 T hT s)) (projIcc 0 T hT s) *
      Real.exp (∫ r in 0..(projIcc 0 T hT s : ℝ), c (X x r) r)
  have hD : ∀ q : ℚ, Measurable (fun s ↦ D s q) := by
    intro q
    exact ((continuous_clamped_characteristic_integrand hT hchar.coefficient_continuous hd
      hchar.flow_continuous).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hDeq (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      D s = (fun x ↦ deriv (fun y ↦ c y s) (X x s) *
        Real.exp (∫ r in 0..s, c (X x r) r)) := by
    funext x
    simp only [D, projIcc_of_mem hT hs, (hcd (X x s) s).deriv]
  let C := Real.sqrt (Real.exp (2 * (B : ℝ) * T)) *
    ((Real.exp (2 * (B : ℝ) * T) +
      (2 * (B : ℝ) * T + 1) * Real.exp (4 * (B : ℝ) * T)) * B)
  have hgraph (s : ℝ) : ∃ U : W^{1,2}((Set.univ : Set (ℝ^1))), ‖U‖ ≤ C ∧
      realLineRepresentative U = D s := by
    obtain ⟨U, hU, hrep⟩ := exists_h1_hkCurve_jacobian_integrand hT f hchar (projIcc 0 T hT
      s).property
    refine ⟨U, hU, ?_⟩
    rw [hrep]
    funext x
    exact congrArg (· * Real.exp (∫ r in 0..(projIcc 0 T hT s : ℝ), c (X x r) r))
      (hcd (X x (projIcc 0 T hT s)) (projIcc 0 T hT s)).deriv
  obtain ⟨G, _hGi, hG, hGb, _hbound, hbase, hrep⟩ :=
    exists_integrable_h1_of_measurable_representative
      (μ := volume.restrict (Ioc 0 t)) hD hgraph
  let U : W^{1,2}((Set.univ : Set (ℝ^1))) := ∫ s in Ioc 0 t, G s
  have hUrep : realLineRepresentative U = (fun x ↦ ∫ s in 0..t,
      deriv (fun y ↦ c y s) (X x s) * Real.exp (∫ r in 0..s, c (X x r) r)) := by
    rw [hrep]
    funext x
    rw [intervalIntegral.integral_of_le ht.1]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact congrFun (hDeq s ⟨hs.1.le, hs.2.trans ht.2⟩) x
  refine ⟨fun s ↦ realLineCoordinateCLM (baseIndex 1 1) (G s),
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr hGb, ?_, U, ?_, ?_,
    hUrep, ?_⟩
  · intro s hs
    exact (realLineCoordinate_ae_representative (G s)).trans
      (Filter.EventuallyEq.of_eq ((hG s).2.trans (hDeq s hs)))
  · change ‖∫ s in Ioc 0 t, G s‖ ≤ t * C
    rw [← intervalIntegral.integral_of_le ht.1]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := t) (fun s _ ↦ (hG s).1)
    simpa only [sub_zero, abs_of_nonneg ht.1, mul_comm C t] using h
  · rw [intervalIntegral.integral_of_le ht.1]
    exact hbase
  · intro x
    rw [hUrep]
    exact hasDerivAt_hkCurve_logJacobian hT f hchar.toHkForwardCharacteristics x t ht

end DeGregorio.Iteration
