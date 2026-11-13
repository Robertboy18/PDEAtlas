/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Constant
public import PDE.Analysis.Evolution.Time.WeakDerivative.Primitive
public import PDE.Spaces.Sobolev.Calculus.Slicing.LineRepresentative
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# The continuous representative of locally integrable weak derivative data

The `lineRepresentative f g` is the primitive of `g`, normalized
to have the same mean as `f` on `[0,1]`. Local integrability of `g` makes
this primitive continuous and locally absolutely continuous.

When `g` is the weak derivative of `f`, their difference has weak derivative
zero and is almost everywhere constant. The mean normalization forces that
constant to vanish, identifying the explicit primitive with `f` almost
everywhere. In particular, the construction applies to arbitrary weak H¹ data.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis

namespace SobolevSpace.Slices

/-- Local integrability of the derivative suffices for continuity of the
mean-normalized primitive. -/
theorem continuous_lineRepresentative {f g : ℝ → ℝ}
    (hg : LocallyIntegrable g volume) : Continuous (lineRepresentative f g) := by
  have hprim : Continuous (fun x ↦ ∫ t in (0 : ℝ)..x, g t) :=
    intervalIntegral.continuous_primitive
      (fun _ _ ↦ (hg.integrableOn_isCompact isCompact_uIcc).intervalIntegrable) 0
  exact (continuous_const.add hprim).sub continuous_const

/-- The normalized primitive is absolutely continuous on each compact
interval when its derivative is only locally integrable. -/
theorem absolutelyContinuousOnInterval_lineRepresentative_of_locallyIntegrable
    {f g : ℝ → ℝ} (hg : LocallyIntegrable g volume) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (lineRepresentative f g) a b := by
  have hconst (c : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ c) a b :=
    (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
  have hprim := Evolution.absolutelyContinuousOnInterval_intervalPrimitive hg 0 a b
  exact ((hconst _).add hprim).sub (hconst _)

/-- Lebesgue differentiation identifies the classical derivative of the
normalized primitive almost everywhere, with only local integrability. -/
theorem ae_hasDerivAt_lineRepresentative_of_locallyIntegrable
    {f g : ℝ → ℝ} (hg : LocallyIntegrable g volume) :
    ∀ᵐ x ∂volume, HasDerivAt (lineRepresentative f g) (g x) x := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg] with x hx
  exact ((hx 0).const_add (∫ t in (0 : ℝ)..1, f t)).sub_const
    (∫ r in (0 : ℝ)..1, ∫ t in (0 : ℝ)..r, g t)

/-- The locally absolutely continuous primitive has weak derivative equal
to its integrand. -/
theorem hasWeakTimeDerivativeOn_lineRepresentative {f g : ℝ → ℝ}
    (hg : LocallyIntegrable g volume) :
    Evolution.HasWeakTimeDerivativeOn univ (lineRepresentative f g) g :=
  Evolution.HasWeakTimeDerivativeOn.of_absolutelyContinuousOnInterval
    (continuous_lineRepresentative hg).locallyIntegrable hg
    (absolutelyContinuousOnInterval_lineRepresentative_of_locallyIntegrable hg)
    (ae_hasDerivAt_lineRepresentative_of_locallyIntegrable hg)

/-- The normalization preserves the integral of the original data on the
unit interval. -/
theorem intervalIntegral_lineRepresentative {f g : ℝ → ℝ}
    (hg : LocallyIntegrable g volume) :
    (∫ x in (0 : ℝ)..1, lineRepresentative f g x) = ∫ x in (0 : ℝ)..1, f x := by
  have hprim : Continuous (fun x ↦ ∫ t in (0 : ℝ)..x, g t) :=
    intervalIntegral.continuous_primitive
      (fun _ _ ↦ (hg.integrableOn_isCompact isCompact_uIcc).intervalIntegrable) 0
  have hint : IntervalIntegrable (fun x ↦ ∫ t in (0 : ℝ)..x, g t) volume 0 1 :=
    hprim.intervalIntegrable 0 1
  dsimp only [lineRepresentative]
  rw [intervalIntegral.integral_sub (intervalIntegrable_const.add hint) intervalIntegrable_const,
    intervalIntegral.integral_add intervalIntegrable_const hint]
  simp

end SobolevSpace.Slices

namespace PDE.Analysis.Evolution.HasWeakTimeDerivativeOn

open SobolevSpace.Slices

/-- Any locally integrable real weak-derivative pair agrees almost everywhere
with its explicitly mean-normalized primitive. -/
theorem ae_eq_lineRepresentative {f g : ℝ → ℝ}
    (hweak : HasWeakTimeDerivativeOn univ f g) :
    f =ᵐ[volume] lineRepresentative f g := by
  have hg : LocallyIntegrable g volume := locallyIntegrableOn_univ.mp hweak.locallyIntegrable_g
  have hf : LocallyIntegrable f volume := locallyIntegrableOn_univ.mp hweak.locallyIntegrable_f
  have hrep := hasWeakTimeDerivativeOn_lineRepresentative (f := f) hg
  have hcont := continuous_lineRepresentative (f := f) hg
  have hzero : HasWeakTimeDerivativeOn univ (fun x ↦ f x - lineRepresentative f g x) 0 := by
    apply (hweak.sub hrep).congr_ae Filter.EventuallyEq.rfl
    exact Filter.Eventually.of_forall fun x ↦ by simp
  obtain ⟨c, hc⟩ := hzero.exists_ae_eq_const_of_zero
  have hint : (∫ x in (0 : ℝ)..1, f x - lineRepresentative f g x) = 0 := by
    rw [intervalIntegral.integral_sub
      (hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
      (hcont.intervalIntegrable 0 1), intervalIntegral_lineRepresentative hg, sub_self]
  have hintc : (∫ x in (0 : ℝ)..1, f x - lineRepresentative f g x) = c := by
    calc
      _ = ∫ _x in (0 : ℝ)..1, c := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hc] with x hx _hmem
        exact hx
      _ = c := by simp
  have hc0 : c = 0 := hintc.symm.trans hint
  filter_upwards [hc] with x hx
  exact sub_eq_zero.mp (hx.trans hc0)

/-- Every locally integrable real weak-derivative pair has a continuous
representative with the same weak derivative. The representative is obtained
from the explicit normalized interval primitive. -/
theorem exists_continuous_ae_eq {f g : ℝ → ℝ}
    (hweak : HasWeakTimeDerivativeOn univ f g) :
    ∃ F : ℝ → ℝ, Continuous F ∧ f =ᵐ[volume] F ∧
      HasWeakTimeDerivativeOn univ F g := by
  have hg := locallyIntegrableOn_univ.mp hweak.locallyIntegrable_g
  exact ⟨lineRepresentative f g, continuous_lineRepresentative hg,
    hweak.ae_eq_lineRepresentative, hasWeakTimeDerivativeOn_lineRepresentative hg⟩

end PDE.Analysis.Evolution.HasWeakTimeDerivativeOn

namespace PDE.Analysis.Evolution.HasWeakTimeDerivativeOn

/-- Integrating a weak derivative recovers the increments of its continuous
primitive, with either orientation of the interval. -/
theorem intervalIntegral_eq_sub {u g : ℝ → ℝ}
    (hweak : HasWeakTimeDerivativeOn Set.univ u g) (hu : Continuous u) (a b : ℝ) :
    (∫ x in a..b, g x) = u b - u a := by
  have hg : LocallyIntegrable g volume :=
    locallyIntegrableOn_univ.mp hweak.locallyIntegrable_g
  have heq : u = SobolevSpace.Slices.lineRepresentative u g :=
    Measure.eq_of_ae_eq hweak.ae_eq_lineRepresentative hu
      (SobolevSpace.Slices.continuous_lineRepresentative hg)
  have ha := congrFun heq a
  have hb := congrFun heq b
  dsimp only [SobolevSpace.Slices.lineRepresentative] at ha hb
  have hint (x y : ℝ) : IntervalIntegrable g volume x y :=
    (hg.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  rw [← intervalIntegral.integral_interval_sub_left (hint 0 b) (hint 0 a)]
  linarith

end PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
