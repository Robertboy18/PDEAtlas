/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.ParametricIntervalSmooth.Local
public import PDE.Analysis.Evolution.ODE.Linear.Scalar.Constant
import CAS.ExactTactic

/-!
# Parameter variation for constant-rate scalar solutions

For `r' = -κ r + F(p, t)` with fixed rate `κ` and initial time `a`, let the initial
value `r₀(p)`, the forcing `F(p, ·)` and a terminal time `L(p)` depend on a real
parameter `p`. If `F` and its parameter derivative `D` are continuous on
`U × [lo, hi]` for an open set `U` and `L(p)` is an interior time, then
`d/dp r(p, L(p))` equals

`e^{-κ(L(p)-a)} r₀'(p) + ∫ₐ^{L(p)} e^{-κ(L(p)-s)} D(p, s) ds`
`+ (F(p, L(p)) - κ r(p, L(p))) L'(p)`.

The formula is proved for `scalarLinearSolution`, for jointly `C¹` forcing, and for
any family of solutions continuous on `[a, b]` that solve the equation on `(a, b)`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Interval Topology

namespace PDE.Analysis.Evolution

/-- Derivative of `p ↦ scalarLinearSolution κ (F p) a (r₀ p) (L p)` when `D` is the
parameter derivative of `F` on `U × [lo, hi]` and `L p` is interior. The initial time
`a ∈ [lo, hi]` may lie on either side of `L p`. -/
theorem hasDerivAt_scalarLinearSolution_terminal
    {U : Set ℝ} {F D : ℝ → ℝ → ℝ} {r₀ L : ℝ → ℝ} {κ a lo hi p r₀' ℓ : ℝ}
    (hU : IsOpen U) (hp : p ∈ U) (ha : a ∈ Icc lo hi)
    (hT : L p ∈ Ioo lo hi)
    (hF : ContinuousOn F.uncurry (U ×ˢ Icc lo hi))
    (hD : ContinuousOn D.uncurry (U ×ˢ Icc lo hi))
    (hd : ∀ q ∈ U, ∀ s ∈ Icc lo hi, HasDerivAt (fun v ↦ F v s) (D q s) q)
    (hr₀ : HasDerivAt r₀ r₀' p) (hL : HasDerivAt L ℓ p) :
    HasDerivAt (fun q ↦ scalarLinearSolution (fun _ ↦ κ) (F q) a (r₀ q) (L q))
      (Real.exp (-κ * (L p - a)) * r₀' +
        (∫ s in a..L p, Real.exp (-κ * (L p - s)) * D p s) +
        (F p (L p) - κ * scalarLinearSolution (fun _ ↦ κ) (F p) a (r₀ p) (L p)) * ℓ)
      p := by
  have hform (v : ℝ → ℝ) (c t : ℝ) :
      scalarLinearSolution (fun _ ↦ κ) v a c t = Real.exp (-κ * (t - a)) *
        (c + ∫ s in a..t, Real.exp (κ * (s - a)) * v s) := by
    have hconst (t : ℝ) : (∫ _ in a..t, κ) = κ * (t - a) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    simp only [scalarLinearSolution, hconst, neg_mul]
  let K : ℝ → ℝ → ℝ := fun q s ↦ Real.exp (κ * (s - a)) * F q s
  let J : ℝ → ℝ → ℝ := fun q s ↦ Real.exp (κ * (s - a)) * D q s
  have hw : Continuous (fun z : ℝ × ℝ ↦ Real.exp (κ * (z.2 - a))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_snd.sub continuous_const))
  have hK : ContinuousOn K.uncurry (U ×ˢ Icc lo hi) := hw.continuousOn.mul hF
  have hJ : ContinuousOn J.uncurry (U ×ˢ Icc lo hi) := hw.continuousOn.mul hD
  have hIntegral := PDE.Analysis.hasDerivAt_intervalIntegral_moving_right_of_continuousOn
    hU hp ha hT hK hJ
    (fun q hq s hs ↦ (hd q hq s hs).const_mul (Real.exp (κ * (s - a)))) hL
  have he := ((hL.sub_const a).const_mul (-κ)).exp
  have hv := (he.mul (hr₀.add hIntegral)).congr_of_eventuallyEq
    (Eventually.of_forall fun q ↦ hform (F q) (r₀ q) (L q))
  have hcancel : Real.exp (-κ * (L p - a)) * Real.exp (κ * (L p - a)) = 1 := by
    rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
  -- The zero-initial-value normal form supplies the same weighted integral.
  have hfactor : (∫ s in a..L p, Real.exp (-κ * (L p - s)) * D p s) =
      Real.exp (-κ * (L p - a)) *
        ∫ s in a..L p, Real.exp (κ * (s - a)) * D p s := by
    have h := scalarLinearSolution_const_eq_exp_mul_add_integral κ (D p) a 0 (L p)
    rw [hform] at h
    simpa only [zero_add, mul_zero] using h.symm
  apply hv.congr_deriv
  dsimp only [K, J, Pi.add_apply]
  rw [hform, hfactor]
  generalize (∫ s in a..L p, Real.exp (κ * (s - a)) * F p s) = I
  generalize (∫ s in a..L p, Real.exp (κ * (s - a)) * D p s) = I'
  generalize r₀ p = R
  generalize F p (L p) = V
  generalize Real.exp (-κ * (L p - a)) = E at hcancel ⊢
  generalize Real.exp (κ * (L p - a)) = E' at hcancel ⊢
  cas using hcancel

/-- `hasDerivAt_scalarLinearSolution_terminal` for `F` jointly `C¹` on `U × [lo, hi]`,
with `D(p, s)` the derivative of `F` within `U × [lo, hi]` in the parameter
direction. -/
theorem hasDerivAt_scalarLinearSolution_terminal_of_contDiffOn
    {U : Set ℝ} {F : ℝ → ℝ → ℝ} {r₀ L : ℝ → ℝ} {κ a lo hi p r₀' ℓ : ℝ}
    (hU : IsOpen U) (hp : p ∈ U) (ha : a ∈ Icc lo hi)
    (hT : L p ∈ Ioo lo hi) (hF : ContDiffOn ℝ 1 F.uncurry (U ×ˢ Icc lo hi))
    (hr₀ : HasDerivAt r₀ r₀' p) (hL : HasDerivAt L ℓ p) :
    HasDerivAt (fun q ↦ scalarLinearSolution (fun _ ↦ κ) (F q) a (r₀ q) (L q))
      (Real.exp (-κ * (L p - a)) * r₀' +
        (∫ s in a..L p, Real.exp (-κ * (L p - s)) *
          (fderivWithin ℝ F.uncurry (U ×ˢ Icc lo hi) (p, s)) (1, 0)) +
        (F p (L p) - κ * scalarLinearSolution (fun _ ↦ κ) (F p) a (r₀ p) (L p)) * ℓ)
      p := by
  have hS : UniqueDiffOn ℝ (U ×ˢ Icc lo hi) :=
    hU.uniqueDiffOn.prod (uniqueDiffOn_Icc (hT.1.trans hT.2))
  apply hasDerivAt_scalarLinearSolution_terminal (κ := κ)
    (D := fun q s ↦ (fderivWithin ℝ F.uncurry (U ×ˢ Icc lo hi) (q, s)) (1, 0))
    hU hp ha hT hF.continuousOn
    ((hF.continuousOn_fderivWithin hS le_rfl).clm_apply continuousOn_const) ?_ hr₀ hL
  intro q hq s hs
  have hd := (hF.differentiableOn one_ne_zero (q, s) ⟨hq, hs⟩).hasFDerivWithinAt
  have hv := hd.comp_hasFDerivAt q (hasFDerivAt_prodMk_left (𝕜 := ℝ) q s)
    (by filter_upwards [hU.mem_nhds hq] with v hv using ⟨hv, hs⟩)
  simpa only [Function.comp_def, Function.uncurry_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply] using hv.hasDerivAt

/-- The terminal variation formula for a family `r(q, ·)` continuous on `[a, b]` with
`r' = -κ r + F(q, ·)` on `(a, b)`. Near `p` the family equals `scalarLinearSolution`,
and only the derivative of the initial value `r(q, a)` in `q` is assumed. -/
theorem hasDerivAt_terminal_of_scalar_linear_ode
    {U : Set ℝ} {r F D : ℝ → ℝ → ℝ} {L : ℝ → ℝ} {κ a b p r₀' ℓ : ℝ}
    (hU : IsOpen U) (hp : p ∈ U) (hT : L p ∈ Ioo a b)
    (hF : ContinuousOn F.uncurry (U ×ˢ Icc a b))
    (hD : ContinuousOn D.uncurry (U ×ˢ Icc a b))
    (hd : ∀ q ∈ U, ∀ s ∈ Icc a b, HasDerivAt (fun v ↦ F v s) (D q s) q)
    (hr : ∀ q ∈ U, ContinuousOn (r q) (Icc a b))
    (hode : ∀ q ∈ U, ∀ s ∈ Ioo a b,
      HasDerivAt (r q) (-κ * r q s + F q s) s)
    (hr₀ : HasDerivAt (fun q ↦ r q a) r₀' p) (hL : HasDerivAt L ℓ p) :
    HasDerivAt (fun q ↦ r q (L q))
      (Real.exp (-κ * (L p - a)) * r₀' +
        (∫ s in a..L p, Real.exp (-κ * (L p - s)) * D p s) +
        (F p (L p) - κ * r p (L p)) * ℓ) p := by
  have heq : (fun q ↦ r q (L q)) =ᶠ[𝓝 p]
      (fun q ↦ scalarLinearSolution (fun _ ↦ κ) (F q) a (r q a) (L q)) := by
    filter_upwards [hU.mem_nhds hp,
      hL.continuousAt (isOpen_Ioo.mem_nhds hT)] with q hq hqt
    have hsub : Icc a (L q) ⊆ Icc a b :=
      fun s hs ↦ ⟨hs.1, hs.2.trans hqt.2.le⟩
    have hforcing : ContinuousOn (F q) (Icc a b) :=
      hF.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hs ↦ ⟨hq, hs⟩)
    exact eq_scalarLinearSolution_const_of_hasDerivAt (κ := κ) hqt.1.le
      ((hr q hq).mono hsub) (hforcing.mono hsub)
      (fun s hs ↦ hode q hq s ⟨hs.1, hs.2.trans hqt.2⟩)
  have hv := (hasDerivAt_scalarLinearSolution_terminal (κ := κ) hU hp
    (show a ∈ Icc a b from ⟨le_rfl, (hT.1.trans hT.2).le⟩)
    hT hF hD hd hr₀ hL).congr_of_eventuallyEq heq
  simpa only [← heq.self_of_nhds] using hv

end PDE.Analysis.Evolution
