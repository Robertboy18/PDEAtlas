/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Caratheodory.Nonlinear

/-!
# Response to a measurable control

For bounded continuous dynamics uniformly Lipschitz in the state, every
measurable control has a response on each finite time interval.
Its speed bound gives a Lipschitz representative, and the nonlinear
Carathéodory uniqueness theorem identifies every absolutely continuous
response satisfying the same initial value and almost-everywhere equation.

The state may be any separable real Banach space. A compact or nonempty
control space is unnecessary once a particular control is supplied. The
representative is extended constantly beyond the time interval, so its
Lipschitz estimate is global while its differential equation is local.

Evans states this existence and uniqueness without proof in §10.3.1, after the bounds (3): for
each admissible control (2) the equation (1) has a unique Lipschitz solution, the response,
which solves it almost everywhere. He takes the state in `ℝⁿ` and the controls in a compact
subset of `ℝᵐ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.3.1, equations (1)-(3).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace
open scoped Topology

namespace HamiltonJacobi

open PDE.Analysis.Evolution

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [TopologicalSpace A] [PseudoMetrizableSpace A]
  [MeasurableSpace A] [BorelSpace A]

/-- Every measurable control drives a unique absolutely continuous response.
The bound `M` on the dynamics becomes the trajectory's Lipschitz
constant. The control need only be a.e. strongly measurable on the prescribed
interval; its values on null sets and outside the interval are unrestricted. -/
theorem exists_measurable_control_response {a b : ℝ} (hab : a ≤ b) (f : E → A → E)
    (hf : Continuous (fun p : E × A ↦ f p.1 p.2)) (K M : NNReal)
    (hK : ∀ c, LipschitzWith K (fun x ↦ f x c)) (hM : ∀ x c, ‖f x c‖ ≤ (M : ℝ)) (α : ℝ → A)
    (hα : AEStronglyMeasurable α (volume.restrict (Set.Icc a b))) (x₀ : E) :
    ∃ u : ℝ → E, LipschitzWith M u ∧ u a = x₀ ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioc a b), HasDerivAt u (f (u t) (α t)) t) ∧
      (∀ t ∈ Set.Icc a b, u t = x₀ + ∫ s in a..t, f (u s) (α s)) ∧
      (∀ v : ℝ → E, AbsolutelyContinuousOnInterval v a b → v a = x₀ →
        (∀ᵐ t ∂volume.restrict (Set.Ioc a b), HasDerivAt v (f (v t) (α t)) t) →
        Set.EqOn v u (Set.Icc a b)) := by
  let β : ℝ → A := hα.mk α
  have hβ : Measurable β := hα.stronglyMeasurable_mk.measurable
  have hαβ : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), α t = β t :=
    hα.ae_eq_mk.filter_mono (MeasureTheory.ae_mono
      ((volume : Measure ℝ).restrict_mono_set (fun _ ht ↦ ⟨ht.1.le, ht.2⟩)))
  have hαβ' : ∀ᵐ t ∂volume, t ∈ Set.Icc a b → α t = β t :=
    (ae_restrict_iff' measurableSet_Icc).mp hα.ae_eq_mk
  let F : ℝ → E → E := fun t x ↦ f x (β t)
  have hF (x : E) : Measurable (Set.indicator (Set.Icc a b) (fun t ↦ F t x)) :=
    (hf.measurable.comp (measurable_const.prodMk hβ)).indicator measurableSet_Icc
  have hFK (t : ℝ) (_ht : t ∈ Set.Icc a b) : LipschitzWith K (F t) := hK (β t)
  have hzero : IntegrableOn (fun t ↦ F t 0) (Set.Icc a b) volume := by
    apply IntegrableOn.of_bound measure_Icc_lt_top
      (hf.measurable.comp (measurable_const.prodMk hβ)).aestronglyMeasurable (M : ℝ)
    exact Filter.Eventually.of_forall fun t ↦ hM 0 (β t)
  obtain ⟨u, hua, huac, hdu, hg, heq⟩ :=
    exists_nonlinear_caratheodory_trajectory hab F hF K hFK hzero x₀
  let g : ℝ → E := Set.indicator (Set.Icc a b) (fun t ↦ F t (u t))
  have hgbound (t : ℝ) : ‖g t‖ ≤ (M : ℝ) := by
    by_cases ht : t ∈ Set.Icc a b
    · simpa only [g, Set.indicator_of_mem ht] using hM (u t) (β t)
    · simp only [g, Set.indicator_of_notMem ht, norm_zero, NNReal.zero_le_coe]
  have hulip : LipschitzWith M u := by
    refine LipschitzWith.of_dist_le_mul fun s t ↦ ?_
    rw [heq s, heq t, dist_eq_norm, add_sub_add_left_eq_sub]
    rw [intervalIntegral.integral_interval_sub_left hg.intervalIntegrable hg.intervalIntegrable]
    simpa only [Real.dist_eq] using (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := t) (b := s) (fun r _hr ↦ hgbound r))
  have hduα : ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      HasDerivAt u (f (u t) (α t)) t := by
    filter_upwards [hdu, hαβ] with t ht hsame
    simpa only [F, ← hsame] using ht
  refine ⟨u, hulip, hua, hduα, ?_, ?_⟩
  · intro t ht
    rw [integral_eq_of_nonlinear_ae_equation hab F hF K hFK hzero huac hua hdu t ht]
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hαβ'] with s hs hsI
    have hsC : s ∈ Set.Icc a b :=
      subset_trans Set.uIoc_subset_uIcc (Set.uIcc_subset_Icc ⟨le_rfl, hab⟩ ht) hsI
    exact congrArg (f (u s)) (hs hsC).symm
  · intro v hv hva hdv
    have hdvβ : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), HasDerivAt v (F t (v t)) t := by
      filter_upwards [hdv, hαβ] with t ht hsame
      simpa only [F, ← hsame] using ht
    exact eqOn_of_nonlinear_ae_equation hab F hF K hFK hzero hv huac hva hua hdvβ hdu

end HamiltonJacobi
