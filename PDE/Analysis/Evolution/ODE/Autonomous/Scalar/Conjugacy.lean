/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import CAS.ExactTactic

/-!
# An integral conjugacy for a scalar vector field

The coordinate `H(s) = s exp(-∫₀ˢ b(v) / (c + v b(v)) dv)` conjugates the scalar
field `s ↦ c * s + s ^ 2 * b s` to its linear part `s ↦ c * s`, without changing
time. On an interval `(-r, r)` where `b` is continuous and `c + s b(s) > 0`, it
satisfies `H'(s) (c s + s² b(s)) = c H(s)`, `H(0) = 0` and `H'(0) = 1`, and it is
strictly increasing. It is smooth when `b` is. The interval integral has its usual
orientation for either sign of `s`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff Topology

namespace PDE.Analysis.Evolution.Scalar

/-- The integral change of coordinate `H(s) = s exp(-∫₀ˢ b(v) / (c + v b(v)) dv)` for
`s ↦ c * s + s ^ 2 * b s`. It is defined for all `s`, and its regularity is proved
on intervals around zero where `c + v b(v) > 0`. -/
noncomputable def scalarConjugacy (c : ℝ) (b : ℝ → ℝ) (s : ℝ) : ℝ :=
  s * Real.exp (-(∫ v in (0 : ℝ)..s, b v / (c + v * b v)))

/-- The change of coordinate fixes the equilibrium at zero. -/
@[simp] theorem scalarConjugacy_zero (c : ℝ) (b : ℝ → ℝ) :
    scalarConjugacy c b 0 = 0 := by
  simp [scalarConjugacy]

private theorem hasDerivAt_scalarConjugacy_primitive
    {c r s : ℝ} {b : ℝ → ℝ}
    (hb : ContinuousOn b (Ioo (-r) r))
    (hden : ∀ v ∈ Ioo (-r) r, 0 < c + v * b v)
    (hs : s ∈ Ioo (-r) r) :
    HasDerivAt (fun t ↦ ∫ v in (0 : ℝ)..t, b v / (c + v * b v))
      (b s / (c + s * b s)) s := by
  have hg : ContinuousOn (fun v : ℝ ↦ b v / (c + v * b v)) (Ioo (-r) r) :=
    hb.div (continuousOn_const.add (continuousOn_id.mul hb))
      (fun v hv ↦ ne_of_gt (hden v hv))
  have hr : 0 < r := by linarith [hs.1, hs.2]
  have hzero : (0 : ℝ) ∈ Ioo (-r) r := ⟨neg_lt_zero.mpr hr, hr⟩
  have hint : IntervalIntegrable (fun v : ℝ ↦ b v / (c + v * b v)) volume 0 s :=
    (hg.mono (ordConnected_Ioo.uIcc_subset hzero hs)).intervalIntegrable
  exact intervalIntegral.integral_hasDerivAt_right hint
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hg s hs)
    ((hg s hs).continuousAt (isOpen_Ioo.mem_nhds hs))

/-- The derivative is the positive exponential factor times
`c / (c + s * b s)`. Continuity of `b` suffices for this identity. -/
theorem hasDerivAt_scalarConjugacy
    {c r s : ℝ} {b : ℝ → ℝ}
    (hb : ContinuousOn b (Ioo (-r) r))
    (hden : ∀ v ∈ Ioo (-r) r, 0 < c + v * b v)
    (hs : s ∈ Ioo (-r) r) :
    HasDerivAt (scalarConjugacy c b)
      (Real.exp (-(∫ v in (0 : ℝ)..s, b v / (c + v * b v))) *
        (c / (c + s * b s))) s := by
  have hne : c + s * b s ≠ 0 := ne_of_gt (hden s hs)
  unfold scalarConjugacy
  apply ((hasDerivAt_id s).mul
    (hasDerivAt_scalarConjugacy_primitive hb hden hs).neg.exp).congr_deriv
  simp only [Pi.neg_apply, id_eq]
  generalize (∫ v in (0 : ℝ)..s, b v / (c + v * b v)) = A
  generalize b s = B at hne ⊢
  cas using hne

/-- If `b` is smooth on `(-r, r)` and `c + v b(v) > 0` there, then `H` is smooth on
`(-r, r)`. -/
theorem contDiffOn_scalarConjugacy
    {c r : ℝ} {b : ℝ → ℝ}
    (hb : ContDiffOn ℝ ∞ b (Ioo (-r) r))
    (hden : ∀ v ∈ Ioo (-r) r, 0 < c + v * b v) :
    ContDiffOn ℝ ∞ (scalarConjugacy c b) (Ioo (-r) r) := by
  have hg : ContDiffOn ℝ ∞ (fun v : ℝ ↦ b v / (c + v * b v)) (Ioo (-r) r) :=
    hb.div (contDiffOn_const.add (contDiffOn_id.mul hb))
      (fun v hv ↦ ne_of_gt (hden v hv))
  have hprimitive :
      ContDiffOn ℝ ∞ (fun s ↦ ∫ v in (0 : ℝ)..s, b v / (c + v * b v))
        (Ioo (-r) r) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨?_, ?_⟩
    · intro s hs
      have hderiv := hasDerivAt_scalarConjugacy_primitive hb.continuousOn hden hs
      exact hderiv.differentiableAt.differentiableWithinAt
    · exact hg.congr fun s hs ↦
        (hasDerivAt_scalarConjugacy_primitive hb.continuousOn hden hs).deriv
  exact contDiffOn_id.mul hprimitive.neg.exp

/-- The coordinate is normalized by derivative one at the equilibrium. -/
theorem hasDerivAt_scalarConjugacy_zero
    {c r : ℝ} {b : ℝ → ℝ} (hr : 0 < r)
    (hb : ContinuousOn b (Ioo (-r) r))
    (hden : ∀ v ∈ Ioo (-r) r, 0 < c + v * b v) :
    HasDerivAt (scalarConjugacy c b) 1 0 := by
  have hzero : (0 : ℝ) ∈ Ioo (-r) r := ⟨neg_lt_zero.mpr hr, hr⟩
  have hc : 0 < c := by simpa using hden 0 hzero
  simpa [ne_of_gt hc] using hasDerivAt_scalarConjugacy hb hden hzero

/-- Conjugacy identity `H'(s) (c s + s² b(s)) = c H(s)` on `(-r, r)`. -/
theorem deriv_scalarConjugacy_mul_eq
    {c r s : ℝ} {b : ℝ → ℝ}
    (hb : ContinuousOn b (Ioo (-r) r))
    (hden : ∀ v ∈ Ioo (-r) r, 0 < c + v * b v)
    (hs : s ∈ Ioo (-r) r) :
    deriv (scalarConjugacy c b) s * (c * s + s ^ 2 * b s) =
      c * scalarConjugacy c b s := by
  have hne : c + s * b s ≠ 0 := ne_of_gt (hden s hs)
  rw [(hasDerivAt_scalarConjugacy hb hden hs).deriv, scalarConjugacy]
  generalize (∫ v in (0 : ℝ)..s, b v / (c + v * b v)) = A
  generalize b s = B at hne ⊢
  cas using hne

/-- The derivative stays positive throughout the interval where the nonlinear
coefficient does. In particular, the coordinate has no critical points there. -/
theorem deriv_scalarConjugacy_pos
    {c r s : ℝ} {b : ℝ → ℝ}
    (hb : ContinuousOn b (Ioo (-r) r))
    (hden : ∀ v ∈ Ioo (-r) r, 0 < c + v * b v)
    (hs : s ∈ Ioo (-r) r) :
    0 < deriv (scalarConjugacy c b) s := by
  have hr : 0 < r := by linarith [hs.1, hs.2]
  have hzero : (0 : ℝ) ∈ Ioo (-r) r := ⟨neg_lt_zero.mpr hr, hr⟩
  have hc : 0 < c := by simpa using hden 0 hzero
  rw [(hasDerivAt_scalarConjugacy hb hden hs).deriv]
  exact mul_pos (Real.exp_pos _) (div_pos hc (hden s hs))

/-- The integral coordinate preserves order throughout the interval where the
nonlinear coefficient stays positive. Only continuity of `b` is needed. -/
theorem strictMonoOn_scalarConjugacy
    {c r : ℝ} {b : ℝ → ℝ}
    (hb : ContinuousOn b (Ioo (-r) r))
    (hden : ∀ v ∈ Ioo (-r) r, 0 < c + v * b v) :
    StrictMonoOn (scalarConjugacy c b) (Ioo (-r) r) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (-r) r)
    (fun s hs ↦ (hasDerivAt_scalarConjugacy hb hden hs).continuousAt.continuousWithinAt)
  intro s hs
  exact deriv_scalarConjugacy_pos hb hden (interior_subset hs)

end PDE.Analysis.Evolution.Scalar
