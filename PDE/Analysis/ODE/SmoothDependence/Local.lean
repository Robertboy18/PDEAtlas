/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension
public import PDE.Analysis.ODE.SmoothDependence.Construction

/-!
# Jointly differentiable local flows of differentiable germs

A locally `C¹` vector field has a jointly `C¹` flow near time zero and its base
point. A compactly supported representative reduces this to the global-field
construction. Continuity keeps the trajectories in the region of agreement, so
the resulting differential equation uses the original field.

At time zero the full derivative sends `(a,h)` to `h + a v(q)`. Both the
initial-state derivative and the time derivative come from the constructed flow.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.ODE

open Filter Metric Set
open scoped ContDiff Topology

/-- A finite-dimensional `C¹` germ constructs a jointly `C¹` local flow.
The original vector field governs every trajectory in a common neighborhood. -/
theorem exists_local_flow_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {v : E → E} {q₀ : E} (hv : ContDiffAt ℝ 1 v q₀) :
    ∃ R : ℝ × E → E, R (0, q₀) = q₀ ∧ ContDiffAt ℝ 1 R (0, q₀) ∧
      (∀ᶠ q in 𝓝 q₀, R (0, q) = q ∧
        HasFDerivAt R
          (ContinuousLinearMap.snd ℝ ℝ E +
            (ContinuousLinearMap.fst ℝ ℝ E).smulRight (v q)) (0, q)) ∧
      (∀ᶠ p in 𝓝 ((0 : ℝ), q₀),
        HasDerivAt (fun t ↦ R (t, p.2)) (v (R p)) p.1) := by
  obtain ⟨w, hw, _hcompact, heq⟩ :=
    hv.exists_contDiff_compactSupport_eventuallyEq
  obtain ⟨r, hr, T, hT, flow, variation, hflow, _hvariation, _hLip, hsolve⟩ :=
    exists_local_contDiff_one_family_of_contDiff_one w hw q₀
  let R : ℝ × E → E := fun p ↦ flow (p.2, p.1)
  have hzero : (0 : ℝ) ∈ Ioo (-T) T := ⟨neg_lt_zero.mpr hT, hT⟩
  have hq₀ : q₀ ∈ ball q₀ r := mem_ball_self hr
  have hopen : IsOpen (ball q₀ r ×ˢ Ioo (-T) T) := isOpen_ball.prod isOpen_Ioo
  have hR (t : ℝ) (q : E) (hq : q ∈ ball q₀ r) (ht : t ∈ Ioo (-T) T) :
      ContDiffAt ℝ 1 R (t, q) :=
    (hflow.contDiffAt (hopen.mem_nhds ⟨hq, ht⟩)).comp (t, q)
      (contDiffAt_snd.prodMk contDiffAt_fst)
  have hR0 : R (0, q₀) = q₀ := (hsolve q₀ hq₀).1
  refine ⟨R, hR0, hR 0 q₀ hq₀ hzero, ?_, ?_⟩
  · filter_upwards [isOpen_ball.mem_nhds hq₀, heq] with q hq heqq
    have hRq : R (0, q) = q := (hsolve q hq).1
    have hd : HasFDerivAt R (fderiv ℝ R (0, q)) (0, q) :=
      ((hR 0 q hq hzero).differentiableAt one_ne_zero).hasFDerivAt
    have htime : HasDerivAt (fun t ↦ R (t, q)) (v q) 0 := by
      simpa only [R, (hsolve q hq).1, heqq] using (hsolve q hq).2.2 0 hzero |>.1
    have hspace : HasFDerivAt (fun x ↦ R (0, x)) (ContinuousLinearMap.id ℝ E) q := by
      simpa only [R, (hsolve q hq).2.1] using (hsolve q hq).2.2 0 hzero |>.2.2
    have hleft :
        (fderiv ℝ R (0, q)).comp (ContinuousLinearMap.inl ℝ ℝ E) =
          ContinuousLinearMap.toSpanSingleton ℝ (v q) := by
      have hc : HasFDerivAt (fun t : ℝ ↦ R (t, q))
          ((fderiv ℝ R (0, q)).comp (ContinuousLinearMap.inl ℝ ℝ E)) 0 := by
        simpa only [Function.comp_def] using
          hd.comp (f := fun t : ℝ ↦ (t, q)) (0 : ℝ)
            (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : ℝ) q)
      exact hc.unique htime.hasFDerivAt
    have hright :
        (fderiv ℝ R (0, q)).comp (ContinuousLinearMap.inr ℝ ℝ E) =
          ContinuousLinearMap.id ℝ E :=
      (hd.comp q (hasFDerivAt_prodMk_right (0 : ℝ) q)).unique hspace
    have hderiv : fderiv ℝ R (0, q) =
        ContinuousLinearMap.snd ℝ ℝ E +
          (ContinuousLinearMap.fst ℝ ℝ E).smulRight (v q) := by
      apply ContinuousLinearMap.prod_ext
      · rw [hleft]
        ext
        simp
      · rw [hright]
        ext
        simp
    exact ⟨hRq, hderiv ▸ hd⟩
  · have hdomain : ∀ᶠ p : ℝ × E in 𝓝 (0, q₀),
        p.2 ∈ ball q₀ r ∧ p.1 ∈ Ioo (-T) T :=
      (continuousAt_snd.prodMk continuousAt_fst) (hopen.mem_nhds ⟨hq₀, hzero⟩)
    have hvalues : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), v (R p) = w (R p) := by
      have ht : Tendsto R (𝓝 (0, q₀)) (𝓝 q₀) := by
        simpa only [ContinuousAt, hR0] using (hR 0 q₀ hq₀ hzero).continuousAt
      exact ht.eventually heq
    filter_upwards [hdomain, hvalues] with p hp heqp
    simpa only [R, heqp] using ((hsolve p.2 hp.1).2.2 p.1 hp.2).1

end PDE.Analysis.ODE
