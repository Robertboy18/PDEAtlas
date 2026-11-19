/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Extending derivatives across countable exceptional sets

Continuity of a function and its candidate derivative removes countable
exceptions to the derivative formula on an open interval.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Calculus

/-- A continuous candidate derivative extends across a countable exceptional
set on an open interval, by the two parts of the fundamental theorem of calculus. -/
theorem hasDerivAt_on_Ioo_of_off_countable {f d : ℝ → ℝ} {a b x : ℝ} {s : Set ℝ}
    (hs : s.Countable) (hf : ContinuousOn f (Ioo a b))
    (hd : ContinuousOn d (Ioo a b))
    (hderiv : ∀ y ∈ Ioo a b \ s, HasDerivAt f (d y) y) (hx : x ∈ Ioo a b) :
    HasDerivAt f (d x) x := by
  have hn : Ioo a b ∈ 𝓝 x := Ioo_mem_nhds hx.1 hx.2
  have hFTC := intervalIntegral.integral_hasDerivAt_right
    (IntervalIntegrable.refl (f := d) (a := x))
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hd x hx) (hd.continuousAt hn)
  apply (hFTC.add_const (f x)).congr_of_eventuallyEq
  filter_upwards [hn] with y hy
  have hi : uIcc x y ⊆ Ioo a b := ordConnected_Ioo.uIcc_subset hx hy
  have h := integral_eq_of_hasDerivAt_off_countable f d hs (hf.mono hi)
    (fun z hz ↦ hderiv z ⟨hi (Ioo_subset_Icc_self hz.1), hz.2⟩)
    (hd.mono hi).intervalIntegrable
  linarith

end PDE.Analysis.Calculus
