/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.JointContinuity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Duhamel integrals for strongly continuous semigroups

Continuous forcing gives a continuous retarded integral. Compact-time operator bounds
control its norm, and splitting the integral gives the restart identity. These facts
apply to every strongly continuous semigroup on a real Banach space.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The retarded semigroup integral. Negative semigroup times are truncated to zero;
for `t ≥ 0`, only times `0 ≤ s ≤ t` contribute. -/
def duhamel (T : StronglyContinuousSemigroup E) (f : ℝ → E) (t : ℝ) : E :=
  ∫ s in (0 : ℝ)..t, T (t - s).toNNReal (f s)

/-- Continuous forcing gives a continuous integrand at every fixed terminal time. -/
theorem continuous_duhamelIntegrand (T : StronglyContinuousSemigroup E)
    {f : ℝ → E} (hf : Continuous f) (t : ℝ) :
    Continuous (fun s ↦ T (t - s).toNNReal (f s)) :=
  T.continuous_apply.comp
    ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).prodMk hf)

/-- The Duhamel integral of continuous forcing is continuous in terminal time. -/
theorem continuous_duhamel (T : StronglyContinuousSemigroup E)
    {f : ℝ → E} (hf : Continuous f) :
    Continuous (T.duhamel f) := by
  have hkernel : Continuous (fun p : ℝ × ℝ ↦ T (p.1 - p.2).toNNReal (f p.2)) :=
    T.continuous_apply.comp
      ((continuous_real_toNNReal.comp (continuous_fst.sub continuous_snd)).prodMk
        (hf.comp continuous_snd))
  exact (intervalIntegral.continuous_parametric_primitive_of_continuous
    (f := fun t s : ℝ ↦ T (t - s).toNNReal (f s)) hkernel).comp
    (continuous_id.prodMk continuous_id)

omit [CompleteSpace E] in
/-- The forcing contributes nothing at the initial time. -/
@[simp]
theorem duhamel_zero (T : StronglyContinuousSemigroup E) (f : ℝ → E) :
    T.duhamel f 0 = 0 := by
  simp [duhamel]

/-- A uniform forcing difference of size `D` contributes at most `M * D * t`
when the semigroup has operator norm at most `M` up to time `t`. -/
theorem norm_duhamel_sub_le (T : StronglyContinuousSemigroup E)
    {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g)
    {τ M : NNReal} (hbound : ∀ r ∈ Icc (0 : NNReal) τ, ‖T r‖ ≤ M)
    {t D : ℝ} (ht : t ∈ Icc (0 : ℝ) τ)
    (hfg : ∀ s ∈ Icc (0 : ℝ) t, ‖f s - g s‖ ≤ D) :
    ‖T.duhamel f t - T.duhamel g t‖ ≤ (M : ℝ) * D * t := by
  rw [duhamel, duhamel, ← intervalIntegral.integral_sub
    ((T.continuous_duhamelIntegrand hf t).intervalIntegrable _ _)
    ((T.continuous_duhamelIntegrand hg t).intervalIntegrable _ _)]
  have hnorm : ∀ s ∈ Ι (0 : ℝ) t,
      ‖T (t - s).toNNReal (f s) - T (t - s).toNNReal (g s)‖ ≤ (M : ℝ) * D := by
    intro s hs
    rw [uIoc_of_le ht.1] at hs
    have hlag : (t - s).toNNReal ≤ τ := by
      simpa only [Real.toNNReal_coe] using
        Real.toNNReal_mono ((sub_le_self t hs.1.le).trans ht.2)
    rw [← map_sub]
    exact ((T (t - s).toNNReal).le_of_opNorm_le
      (hbound _ ⟨zero_le, hlag⟩) _).trans
        (mul_le_mul_of_nonneg_left (hfg s ⟨hs.1.le, hs.2⟩) M.property)
  simpa only [sub_zero, abs_of_nonneg ht.1] using
    intervalIntegral.norm_integral_le_of_norm_le_const hnorm

omit [CompleteSpace E] in
/-- Only the values of the forcing between zero and the terminal time enter Duhamel's
integral. In particular, the choice of continuous extension outside that interval
does not affect the mild equation. -/
theorem duhamel_congr (T : StronglyContinuousSemigroup E)
    {f g : ℝ → E} {t : ℝ} (ht : 0 ≤ t) (hfg : EqOn f g (Icc 0 t)) :
    T.duhamel f t = T.duhamel g t := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  exact congrArg (T (t - s).toNNReal) (hfg hs)

/-- Splitting the forcing at time `a` separates the evolved earlier contribution
from the forcing accumulated during the following interval of length `h`. -/
theorem duhamel_add (T : StronglyContinuousSemigroup E)
    {f : ℝ → E} (hf : Continuous f) {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) :
    T.duhamel f (a + h) =
      T h.toNNReal (T.duhamel f a) + T.duhamel (fun s ↦ f (a + s)) h := by
  have hearly :
      (∫ s in (0 : ℝ)..a, T (a + h - s).toNNReal (f s)) =
        T h.toNNReal (T.duhamel f a) := by
    rw [duhamel, ← (T h.toNNReal).intervalIntegral_comp_comm
      ((T.continuous_duhamelIntegrand hf a).intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ha] at hs
    change T (a + h - s).toNNReal (f s) =
      T h.toNNReal (T (a - s).toNNReal (f s))
    have hlag : a + h - s = h + (a - s) := by ring
    rw [hlag, Real.toNNReal_add hh (sub_nonneg.mpr hs.2), T.map_add_apply]
  have hlate :
      (∫ s in a..(a + h), T (a + h - s).toNNReal (f s)) =
        T.duhamel (fun s ↦ f (a + s)) h := by
    have htranslate := intervalIntegral.integral_comp_add_left
      (fun s ↦ T (a + h - s).toNNReal (f s)) a (a := 0) (b := h)
    rw [add_zero] at htranslate
    rw [← htranslate, duhamel]
    apply intervalIntegral.integral_congr
    intro s _
    change T (a + h - (a + s)).toNNReal (f (a + s)) =
      T (h - s).toNNReal (f (a + s))
    have hlag : a + h - (a + s) = h - s := by ring
    rw [hlag]
  rw [duhamel, ← intervalIntegral.integral_add_adjacent_intervals
    ((T.continuous_duhamelIntegrand hf (a + h)).intervalIntegrable 0 a)
    ((T.continuous_duhamelIntegrand hf (a + h)).intervalIntegrable a (a + h))]
  rw [hearly, hlate]

/-- Integrating a time-dependent bound on the forcing difference gives a Duhamel
estimate suitable for Grönwall, without differentiating a mild solution. -/
theorem norm_duhamel_sub_le_integral (T : StronglyContinuousSemigroup E)
    {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g)
    {τ M : NNReal} (hbound : ∀ r ∈ Icc (0 : NNReal) τ, ‖T r‖ ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) τ)
    {D : ℝ → ℝ} (hD : Continuous D)
    (hfg : ∀ s ∈ Icc (0 : ℝ) t, ‖f s - g s‖ ≤ D s) :
    ‖T.duhamel f t - T.duhamel g t‖ ≤ (M : ℝ) * ∫ s in (0 : ℝ)..t, D s := by
  rw [duhamel, duhamel, ← intervalIntegral.integral_sub
    ((T.continuous_duhamelIntegrand hf t).intervalIntegrable _ _)
    ((T.continuous_duhamelIntegrand hg t).intervalIntegrable _ _),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le ht.1
    (Filter.Eventually.of_forall ?_) ((continuous_const.mul hD).intervalIntegrable _ _)
  intro s hs
  have hlag : (t - s).toNNReal ≤ τ := by
    simpa only [Real.toNNReal_coe] using
      Real.toNNReal_mono ((sub_le_self t hs.1.le).trans ht.2)
  rw [← (T (t - s).toNNReal).map_sub]
  exact ((T (t - s).toNNReal).le_of_opNorm_le
    (hbound _ ⟨zero_le, hlag⟩) _).trans
      (mul_le_mul_of_nonneg_left (hfg s ⟨hs.1.le, hs.2⟩) M.coe_nonneg)

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
