/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Distributional
public import PDE.Analysis.Evolution.Time.WeakDerivative.InitialPrimitive
public import PDE.Analysis.Evolution.Time.AbsoluteContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Time-dependent operators acting on weakly differentiable curves

An absolutely continuous operator curve acts on a Sobolev curve by the usual
product rule. The proof first constructs an absolutely continuous representative,
then identifies its distributional derivative. Endpoint values of an arbitrary
Bochner representative are never used as traces.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

omit [CompleteSpace X] in
/-- On the empty set every pair of curves is a weak derivative pair: there are no test
functions to integrate against. -/
theorem HasWeakTimeDerivativeOn.of_empty (f g : ℝ → X) : HasWeakTimeDerivativeOn ∅ f g where
  locallyIntegrable_f := fun x hx ↦ (notMem_empty x hx).elim
  locallyIntegrable_g := fun x hx ↦ (notMem_empty x hx).elim
  integral_eq := fun ell φ _ _ hφ ↦ by
    obtain rfl : φ = 0 :=
      Function.support_eq_empty_iff.mp (subset_empty_iff.mp (subset_closure.trans hφ))
    simp

/-- On a finite interval an absolutely continuous curve with an integrable
almost-everywhere derivative has that distributional derivative. -/
theorem HasWeakTimeDerivativeOn.of_absolutelyContinuousOnInterval_Icc
    {a b : ℝ} {f g : ℝ → X}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : IntegrableOn g (Ioc a b))
    (hd : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt f (g t) t) :
    HasWeakTimeDerivativeOn (Ioo a b) f g := by
  by_cases hab : a ≤ b
  swap
  · rw [Ioo_eq_empty fun h ↦ hab h.le]
    exact .of_empty f g
  obtain ⟨Q, _hQcont, hQa, _hQFTC, hQAC, hQderiv, hQweak⟩ :=
    exists_initial_primitive_of_integrableOn hg (f a)
  have hzero : ∀ᵐ t ∂volume.restrict (Icc a b),
      HasDerivAt (fun s ↦ f s - Q s) 0 t := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    filter_upwards [hd, hQderiv] with t hft hQt
    simpa only [sub_self, Pi.sub_def] using hft.sub hQt
  have hzero' : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      HasDerivAt (fun s ↦ f s - Q s) 0 t := by
    rw [uIcc_of_le hab]
    exact (ae_restrict_iff' measurableSet_Icc).mp hzero
  obtain ⟨c, hc⟩ := (hf.sub hQAC).const_of_ae_hasDerivAt_zero hzero'
  have hc0 : c = 0 := by
    have h := hc a left_mem_uIcc
    simpa only [Pi.sub_apply, hQa, sub_self] using h.symm
  apply hQweak.congr_ae_restrict measurableSet_Ioo _ EventuallyEq.rfl
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have h := hc t (by simpa only [uIcc_of_le hab] using Ioo_subset_Icc_self ht)
  rw [hc0] at h
  exact (sub_eq_zero.mp h).symm

/-- The product rule for an absolutely continuous bounded-operator curve
and an L² Sobolev curve. Integrability is required only of the displayed
product derivative, so the rule applies beyond continuously differentiable
operator paths. -/
theorem HasWeakTimeDerivativeOn.clm_apply_of_lp
    {a b : ℝ}
    {u du : Lp X 2 (volume.restrict (Ioc a b))}
    (hweak : HasWeakTimeDerivativeOn (Ioo a b) u du)
    {A dA : ℝ → X →L[ℝ] Y}
    (hA : AbsolutelyContinuousOnInterval A a b)
    (hdA : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt A (dA t) t)
    (hprod : IntegrableOn (fun t ↦ dA t (u t) + A t (du t)) (Ioc a b)) :
    HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ A t (u t))
      (fun t ↦ dA t (u t) + A t (du t)) := by
  rcases le_or_gt b a with hba | hab
  · rw [Ioo_eq_empty (not_lt.mpr hba)]
    exact .of_empty _ _
  obtain ⟨w, hwAC, huw, hwDeriv⟩ :=
    hweak.exists_absolutelyContinuousRepresentative_of_lp hab
  have hderiv : ∀ᵐ t ∂volume.restrict (Ioc a b),
      HasDerivAt (fun s ↦ A s (w s)) (dA t (w t) + A t (du t)) t := by
    filter_upwards [hdA, hwDeriv] with t hAt hwt
    exact hAt.clm_apply hwt
  have hprod' : IntegrableOn (fun t ↦ dA t (w t) + A t (du t)) (Ioc a b) :=
    hprod.congr (huw.mono fun t ht ↦ by simp only [ht])
  have h := HasWeakTimeDerivativeOn.of_absolutelyContinuousOnInterval_Icc
    (AbsolutelyContinuousOnInterval.clm_apply hA hwAC) hprod' hderiv
  have huw' := huw.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))
  apply h.congr_ae_restrict measurableSet_Ioo
  · exact huw'.symm.mono fun t ht ↦ by simp only [ht]
  · exact huw'.symm.mono fun t ht ↦ by simp only [ht]

end PDE.Analysis.Evolution
