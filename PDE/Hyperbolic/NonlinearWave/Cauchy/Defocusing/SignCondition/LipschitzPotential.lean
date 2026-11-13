/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ConvexIntegralPotential
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.Potential

/-!
# Integral potentials of Lipschitz reactions

A Lipschitz reaction vanishing at zero defines a finite differentiable potential
on L² over any measure space. Adding a sufficiently large linear reaction makes
the scalar potential convex. Subtracting the linear reaction's potential then
reduces differentiability to the convex integral-potential theorem.
No monotonicity or sign condition on the original reaction is needed.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace
open PDE.Analysis (primitive primitive_zero hasDerivAt_primitive)

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- A monotone continuous reaction has a convex normalized potential. -/
theorem convexOn_potential_of_monotone {f : ℝ → ℝ} (hf : Continuous f)
    (hm : Monotone f) : ConvexOn ℝ univ (primitive f) := by
  apply Monotone.convexOn_univ_of_deriv (fun z ↦ (hasDerivAt_primitive hf z).differentiableAt)
  intro x y hxy
  rw [(hasDerivAt_primitive hf x).deriv, (hasDerivAt_primitive hf y).deriv]
  exact hm hxy

/-- Adding the Lipschitz constant times the identity makes a real reaction monotone. -/
theorem monotone_reaction_add_linear {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) : Monotone (fun z ↦ f z + (K : ℝ) * z) := by
  intro x y hxy
  have h := hf.norm_sub_le x y
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hxy)] at h
  have h' := le_abs_self (f x - f y)
  dsimp
  nlinarith

/-- Subtracting continuous reactions subtracts their normalized potentials. -/
theorem potential_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (z : ℝ) : primitive (fun s ↦ f s - g s) z = primitive f z - primitive g z :=
  intervalIntegral.integral_sub (hf.intervalIntegrable 0 z) (hg.intervalIntegrable 0 z)

variable {α V : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The potential of a Lipschitz reaction vanishing at zero is integrable for every
L² argument, even when the measure is infinite. -/
theorem integrable_potential_of_lipschitz {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hf0 : f 0 = 0) (u : Lp ℝ 2 μ) :
    Integrable (fun x ↦ primitive f (u x)) μ := by
  let g : ℝ → ℝ := fun z ↦ f z + (K : ℝ) * z
  let h : ℝ → ℝ := fun z ↦ (K : ℝ) * z
  have hg : Continuous g := hf.continuous.add (continuous_const.mul continuous_id)
  have hh : Continuous h := continuous_const.mul continuous_id
  have hg0 : g 0 = 0 := by simp [g, hf0]
  have hh0 : h 0 = 0 := by simp [h]
  have hm : Monotone h := fun _ _ hxy ↦ mul_le_mul_of_nonneg_left hxy K.coe_nonneg
  have hae : (K : ℝ) • u =ᵐ[μ] fun x ↦ h (u x) := by
    filter_upwards [Lp.coeFn_smul (K : ℝ) u] with x hx using hx
  have hgae : hf.compLp hf0 u + (K : ℝ) • u =ᵐ[μ] fun x ↦ g (u x) := by
    filter_upwards [Lp.coeFn_add (hf.compLp hf0 u) ((K : ℝ) • u),
      hf.coeFn_compLp hf0 u, hae] with x hx hx' hx''
    simp only [hx, Pi.add_apply, hx', hx'', g, h, Function.comp_apply]
  have hi := PDE.Analysis.Calculus.integrable_convex_potential_of_L2_gradient
    (convexOn_potential_of_monotone hg (monotone_reaction_add_linear hf))
    (hasDerivAt_primitive hg) (primitive_zero g) hg0 u _ hgae
  have hj := PDE.Analysis.Calculus.integrable_convex_potential_of_L2_gradient
    (convexOn_potential_of_monotone hh hm) (hasDerivAt_primitive hh) (primitive_zero h) hh0 u _ hae
  convert hi.sub hj using 1
  funext x
  simp only [Pi.sub_apply]
  rw [← potential_sub hg hh]
  simp only [g, h, add_sub_cancel_right]

/-- The L² composition with a Lipschitz reaction is the Fréchet gradient
of its integral potential, after any continuous linear map into L². -/
theorem hasFDerivAt_integral_lipschitz_potential (J : V →L[ℝ] Lp ℝ 2 μ) {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hf0 : f 0 = 0) (v : V) :
    HasFDerivAt (fun w ↦ ∫ x, primitive f (J w x) ∂μ)
      ((innerSL ℝ (hf.compLp hf0 (J v))).comp J) v := by
  let g : ℝ → ℝ := fun z ↦ f z + (K : ℝ) * z
  let h : ℝ → ℝ := fun z ↦ (K : ℝ) * z
  let M : V → Lp ℝ 2 μ := fun w ↦ (K : ℝ) • J w
  let N : V → Lp ℝ 2 μ := fun w ↦ hf.compLp hf0 (J w) + M w
  have hg : Continuous g := hf.continuous.add (continuous_const.mul continuous_id)
  have hh : Continuous h := continuous_const.mul continuous_id
  have hg0 : g 0 = 0 := by simp [g, hf0]
  have hh0 : h 0 = 0 := by simp [h]
  have hm : Monotone h := fun _ _ hxy ↦ mul_le_mul_of_nonneg_left hxy K.coe_nonneg
  have hM : Continuous M := J.continuous.const_smul (K : ℝ)
  have hN : Continuous N := ((hf.continuous_compLp hf0).comp J.continuous).add hM
  have hMae (w : V) : M w =ᵐ[μ] fun x ↦ h (J w x) := by
    filter_upwards [Lp.coeFn_smul (K : ℝ) (J w)] with x hx using hx
  have hNae (w : V) : N w =ᵐ[μ] fun x ↦ g (J w x) := by
    filter_upwards [Lp.coeFn_add (hf.compLp hf0 (J w)) (M w),
      hf.coeFn_compLp hf0 (J w), hMae w] with x hx hx' hx''
    simp only [N, hx, Pi.add_apply, hx', hx'', g, h, Function.comp_apply]
  have hconv := convexOn_potential_of_monotone hg (monotone_reaction_add_linear hf)
  have hconv' := convexOn_potential_of_monotone hh hm
  have hd := PDE.Analysis.Calculus.hasFDerivAt_integral_convex_potential J hconv
    (hasDerivAt_primitive hg) (primitive_zero g) hg0 N hNae v hN.continuousAt
  have hd' := PDE.Analysis.Calculus.hasFDerivAt_integral_convex_potential J hconv'
    (hasDerivAt_primitive hh) (primitive_zero h) hh0 M hMae v hM.continuousAt
  convert hd.sub hd' using 1
  · funext w
    have hi := PDE.Analysis.Calculus.integrable_convex_potential_of_L2_gradient
      hconv (hasDerivAt_primitive hg) (primitive_zero g) hg0 (J w) (N w) (hNae w)
    have hj := PDE.Analysis.Calculus.integrable_convex_potential_of_L2_gradient
      hconv' (hasDerivAt_primitive hh) (primitive_zero h) hh0 (J w) (M w) (hMae w)
    simp only [Pi.sub_apply]
    rw [← integral_sub hi hj]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      change primitive f (J w x) = primitive g (J w x) - primitive h (J w x)
      rw [← potential_sub hg hh]
      simp only [g, h, add_sub_cancel_right]
  · ext w
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, N, inner_add_left, add_sub_cancel_right]

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
