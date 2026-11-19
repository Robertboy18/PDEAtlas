/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Measurable evaluation of continuous families

If `F(x, v)` is continuous in `v` and strongly measurable in `x` for each fixed `v`,
then `F(x, u(x))` is strongly measurable for every strongly measurable `u`.
Simple approximation of `u` suffices; no measurability into a space of operators is needed.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace MeasureTheory

/-- Evaluation along an almost everywhere strongly measurable argument preserves strong
measurability for a family continuous in that argument and measurable at each fixed value. -/
theorem AEStronglyMeasurable.eval_of_continuous
    {α E F : Type*} [MeasurableSpace α] [TopologicalSpace E] [Nonempty E]
    [TopologicalSpace F] [TopologicalSpace.PseudoMetrizableSpace F]
    {μ : Measure α} {u : α → E} (hu : AEStronglyMeasurable u μ)
    {f : α → E → F} (hf : ∀ v, AEStronglyMeasurable (fun x ↦ f x v) μ)
    (hc : ∀ x, Continuous (f x)) :
    AEStronglyMeasurable (fun x ↦ f x (u x)) μ := by
  classical
  have hm : AEStronglyMeasurable (fun x ↦ f x (hu.mk u x)) μ := by
    induction hu.mk u, hu.stronglyMeasurable_mk using StronglyMeasurable.induction' with
    | const v => exact hf v
    | @pcw g h s hg hh hs hfg hfh =>
      simpa only [Set.apply_piecewise] using
        hfg.restrict.piecewise hs.nullMeasurableSet hfh.restrict
    | @lim g h hg hh hfg hlim =>
      exact aestronglyMeasurable_of_tendsto_ae atTop hfg
        (Filter.Eventually.of_forall fun x ↦ (hc x).continuousAt.tendsto.comp (hlim x))
  apply hm.congr
  filter_upwards [hu.ae_eq_mk] with x hx
  rw [hx]

end MeasureTheory
