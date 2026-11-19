/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension
public import PDE.Analysis.ODE.SmoothDependence.HigherOrder

/-!
# Jointly C² local flows of C² germs

The finite-dimensional C² flow construction applies to a compactly supported
representative of the vector-field germ. Continuity keeps the resulting trajectories
in the region of agreement, so the local differential equation uses the original
vector field. No extension or regular solution family is required as input.
-/

@[expose] public noncomputable section

open Filter Metric Set
open scoped Topology

namespace PDE.Analysis.ODE

/-- A finite-dimensional C² vector-field germ constructs a jointly C² local flow,
with the original vector field governing trajectories on a common neighborhood. -/
theorem exists_local_contDiff_two_flow_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {v : E → E} {q₀ : E} (hv : ContDiffAt ℝ 2 v q₀) :
    ∃ R : ℝ × E → E, R (0, q₀) = q₀ ∧ ContDiffAt ℝ 2 R (0, q₀) ∧
      (∀ᶠ q in 𝓝 q₀, R (0, q) = q) ∧
      (∀ᶠ p in 𝓝 ((0 : ℝ), q₀),
        HasDerivAt (fun t ↦ R (t, p.2)) (v (R p)) p.1) := by
  obtain ⟨w, hw, _hcompact, heq⟩ :=
    hv.exists_contDiff_compactSupport_eventuallyEq
  obtain ⟨r, hr, T, hT, flow, variation, hflow, _hvariation, _hLip, hsolve⟩ :=
    exists_local_contDiff_succ_family 1 w hw q₀
  let R : ℝ × E → E := fun p ↦ flow (p.2, p.1)
  have ht₀ : (0 : ℝ) ∈ Ioo (-T) T := ⟨neg_lt_zero.mpr hT, hT⟩
  have hq₀ : q₀ ∈ ball q₀ r := mem_ball_self hr
  have hopen : IsOpen (ball q₀ r ×ˢ Ioo (-T) T) := isOpen_ball.prod isOpen_Ioo
  have hR : ContDiffAt ℝ 2 R (0, q₀) :=
    (hflow.contDiffAt (hopen.mem_nhds ⟨hq₀, ht₀⟩)).comp (0, q₀)
      (contDiffAt_snd.prodMk contDiffAt_fst)
  have hR₀ : R (0, q₀) = q₀ := (hsolve q₀ hq₀).1
  refine ⟨R, hR₀, hR, ?_, ?_⟩
  · filter_upwards [isOpen_ball.mem_nhds hq₀] with q hq
    exact (hsolve q hq).1
  · have hdomain : ∀ᶠ p : ℝ × E in 𝓝 (0, q₀),
        p.2 ∈ ball q₀ r ∧ p.1 ∈ Ioo (-T) T :=
      (continuousAt_snd.prodMk continuousAt_fst).eventually
        (hopen.mem_nhds ⟨hq₀, ht₀⟩)
    have hvalues : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), v (R p) = w (R p) := by
      have ht : Tendsto R (𝓝 (0, q₀)) (𝓝 q₀) := by
        simpa only [ContinuousAt, hR₀] using hR.continuousAt
      exact ht.eventually heq
    filter_upwards [hdomain, hvalues] with p hp heqp
    simpa only [R, heqp] using ((hsolve p.2 hp.1).2.2 p.1 hp.2).1

end PDE.Analysis.ODE
