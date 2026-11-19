/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension
public import PDE.Hyperbolic.ConservationLaw.Scalar.Characteristics.GlobalInverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import PDE.FDeriv.Calculus

/-!
# Characteristics from local C¹ speed and initial data

The characteristic inverse only needs C¹ germs of the speed and the initial data.
Compactly supported representatives let us apply the scalar inverse
theorem. Restricting its neighborhood removes the extensions from every conclusion.

The construction has a positive local lifespan. On a fixed interval of initial
labels the spatial Jacobian stays positive, so characteristics are strictly ordered.
The inverse recovers each label, and the transported phase attains its initial data.
Its values can be confined to any prescribed neighborhood of the initial value.

This is the local solution of Evans, §3.2.5, Example 5, where the noncharacteristic condition
holds on all of `t = 0` and Theorem 2 of §3.2.4 applies; we obtain it from the inverse function
theorem for the characteristic map.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.4, Theorem 2; §3.2.5, Example 5, equations (58)-(61).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Metric Set PDE.Common
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar

/-- Local C¹ speed and data construct a C¹ characteristic solution, with a
positive time interval and noncrossing on an interval of initial labels.
The set `V` is an arbitrary neighborhood in which the phase is required to remain. -/
theorem exists_local_characteristics_of_contDiffAt {a g : ℝ → ℝ} {x₀ : ℝ} {V : Set ℝ}
    (ha : ContDiffAt ℝ 1 a (g x₀)) (hg : ContDiffAt ℝ 1 g x₀) (hV : V ∈ 𝓝 (g x₀)) :
    ∃ U : Set (ℝ^2), ∃ ξ : ℝ^2 → ℝ, ∃ T δ : ℝ,
      IsOpen U ∧ !₂[0, x₀] ∈ U ∧ 0 < T ∧ 0 < δ ∧
      (∀ p ∈ U,
        ContDiffAt ℝ 1 ξ p ∧ ContDiffAt ℝ 1 (g ∘ ξ) p ∧ g (ξ p) ∈ V ∧
        p 1 = ξ p + p 0 * a (g (ξ p)) ∧
        (∂[0] (g ∘ ξ)) p + a (g (ξ p)) * (∂[1] (g ∘ ξ)) p = 0) ∧
      (∀ x, !₂[0, x] ∈ U → (g ∘ ξ) !₂[0, x] = g x) ∧
      (∀ t, |t| < T →
        StrictMonoOn (conservationCharPosition a g t) (ball x₀ δ) ∧
        ∀ x ∈ ball x₀ δ,
          HasDerivAt (conservationCharPosition a g t)
            (1 + t * deriv a (g x) * deriv g x) x ∧
          0 < 1 + t * deriv a (g x) * deriv g x ∧
          !₂[t, conservationCharPosition a g t x] ∈ U ∧
          ξ !₂[t, conservationCharPosition a g t x] = x) ∧
      ∀ p : ℝ^2, |p 0| < T → |p 1 - x₀| < δ → p ∈ U := by
  obtain ⟨A, hA, _, haeq⟩ := ha.exists_contDiff_compactSupport_eventuallyEq
  obtain ⟨G, hG, _, hgeq⟩ := hg.exists_contDiff_compactSupport_eventuallyEq
  have hgood : ∀ᶠ x in 𝓝 x₀,
      g =ᶠ[𝓝 x] G ∧ a =ᶠ[𝓝 (g x)] A ∧ g x ∈ V := by
    filter_upwards [hgeq.eventuallyEq_nhds, hg.continuousAt.eventually haeq.eventuallyEq_nhds,
      hg.continuousAt.eventually hV] with x hx hax hxV using ⟨hx, hax, hxV⟩
  have hden : Continuous (fun p : ℝ × ℝ ↦ 1 + p.1 * deriv A (G p.2) * deriv G p.2) := by
    have := hA.continuous_deriv_one
    have := hG.continuous_deriv_one
    have := hG.continuous
    fun_prop
  have hlarge : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, x₀), 0 < 1 + p.1 * deriv A (G p.2) * deriv G p.2 ∧
      (g =ᶠ[𝓝 p.2] G ∧ a =ᶠ[𝓝 (g p.2)] A ∧ g p.2 ∈ V) :=
    (hden.continuousAt.eventually (Ioi_mem_nhds (by simp))).and
      ((continuousAt_snd : ContinuousAt (Prod.snd : ℝ × ℝ → ℝ) (0, x₀)).eventually hgood)
  obtain ⟨d, hd, hdball⟩ := Metric.mem_nhds_iff.mp hlarge
  have hrect {t x : ℝ} (ht : |t| < d) (hx : x ∈ ball x₀ d) : 0 < 1 + t * deriv A (G x) * deriv G x ∧
      (g =ᶠ[𝓝 x] G ∧ a =ᶠ[𝓝 (g x)] A ∧ g x ∈ V) := by
    refine hdball (a := (t, x)) ?_
    simpa only [mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff] using And.intro ht hx
  have hdata {x : ℝ} (hx : x ∈ ball x₀ d) :=
    (hrect (by simpa using hd : |(0 : ℝ)| < d) hx).2
  have hderiv {t x : ℝ} (ht : |t| < d) (hx : x ∈ ball x₀ d) :
      HasDerivAt (conservationCharPosition a g t) (1 + t * deriv a (g x) * deriv g x) x ∧
      0 < 1 + t * deriv a (g x) * deriv g x := by
    obtain ⟨hpos, hgx, hax, _⟩ := hrect ht hx
    refine ⟨((hasDerivAt_id x).add ((((hA.differentiable_one _).congr_of_eventuallyEq
      hax).hasDerivAt.comp x ((hG.differentiable_one _).congr_of_eventuallyEq
        hgx).hasDerivAt).const_mul t)).congr_deriv (by simp [mul_assoc]), ?_⟩
    rwa [hax.deriv_eq, hgx.deriv_eq, hgx.self_of_nhds]
  have hmono {t : ℝ} (ht : |t| < d) : StrictMonoOn (conservationCharPosition a g t) (ball x₀ d) :=
    strictMonoOn_of_deriv_pos (convex_ball x₀ d)
      (fun x hx ↦ (hderiv ht hx).1.continuousAt.continuousWithinAt) fun x hx ↦ by
        rw [(hderiv ht (interior_subset hx)).1.deriv]
        exact (hderiv ht (interior_subset hx)).2
  obtain ⟨W, hW, hpW, ξ, hξ₀, hrel, hξ⟩ :=
    exists_local_contDiff_footpointMap_of_denom_ne_zero A G !₂[0, x₀] hA hG
      (by simp [conservationCharDenom])
  have hmap₀ : conservationCharMap A G !₂[0, x₀] = !₂[0, x₀] := by
    simp [conservationCharMap]
  rw [hmap₀] at hpW hξ₀
  change ξ !₂[0, x₀] = x₀ at hξ₀
  have hnear : ∀ᶠ p in 𝓝 (!₂[0, x₀] : ℝ^2), p ∈ W ∧ ξ p ∈ ball x₀ d ∧ |p 0| < d :=
    (hW.eventually_mem hpW).and (((hξ _ hpW).continuousAt.eventually (isOpen_ball.mem_nhds
      (by rw [hξ₀]; exact mem_ball_self hd) : ball x₀ d ∈ _)).and ((show ContinuousAt
        (fun p : ℝ^2 ↦ |p 0|) !₂[0, x₀] by fun_prop).eventually (Iio_mem_nhds (by simpa using hd))))
  obtain ⟨U, hUsub, hU, hpU⟩ := _root_.mem_nhds_iff.mp hnear
  have hproperties (p : ℝ^2) (hp : p ∈ U) :
      ContDiffAt ℝ 1 ξ p ∧ ContDiffAt ℝ 1 (g ∘ ξ) p ∧ g (ξ p) ∈ V ∧ p 1 = ξ p + p 0 * a (g (ξ p)) ∧
      (∂[0] (g ∘ ξ)) p + a (g (ξ p)) * (∂[1] (g ∘ ξ)) p = 0 := by
    obtain ⟨hpW', hx, _⟩ := hUsub hp
    obtain ⟨hgp, hap, hpV⟩ := hdata hx
    have hξp := hξ p hpW'
    have hphase : (g ∘ ξ) =ᶠ[𝓝 p] conservationSolutionFromFoot G ξ :=
      hgp.comp_tendsto hξp.continuousAt
    have hvel : a (g (ξ p)) = A (G (ξ p)) := hap.self_of_nhds.trans (congrArg A hgp.self_of_nhds)
    refine ⟨hξp, (hG.contDiffAt.comp p hξp).congr_of_eventuallyEq hphase, hpV, hvel ▸ hrel p hpW',
      ?_⟩
    have hpde := hrel.satisfies_pde_at hW hA.differentiable_one hG.differentiable_one
      hpW' hξp.differentiableAt_one
    rw [← partialDeriv_congr_nhds 0 hphase, ← partialDeriv_congr_nhds 1 hphase] at hpde
    exact hvel ▸ hpde
  let χ : ℝ × ℝ → ℝ^2 := fun p ↦ !₂[p.1, conservationCharPosition A G p.1 p.2]
  let j : ℝ × ℝ → ℝ^2 := fun p ↦ !₂[p.1, p.2]
  have hχ : Continuous χ := by unfold χ conservationCharPosition; fun_prop
  have hj : Continuous j := by unfold j; fun_prop
  have hsmall : ∀ᶠ p in 𝓝 ((0 : ℝ), x₀), χ p ∈ U ∧ j p ∈ U :=
    (hχ.continuousAt.eventually (by
      simpa [χ, conservationCharPosition] using hU.mem_nhds hpU)).and
      (hj.continuousAt.eventually (hU.mem_nhds hpU))
  obtain ⟨e, he, heball⟩ := Metric.mem_nhds_iff.mp hsmall
  let ρ := min d e
  have hρ : 0 < ρ := lt_min hd he
  have hsmallrect {t x : ℝ} (ht : |t| < ρ) (hx : |x - x₀| < ρ) :
      χ (t, x) ∈ U ∧ j (t, x) ∈ U := by
    refine heball (a := (t, x)) ?_
    simpa only [mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff] using
      And.intro (ht.trans_le (min_le_right d e)) (hx.trans_le (min_le_right d e))
  refine ⟨U, ξ, ρ, ρ, hU, hpU, hρ, hρ, hproperties, ?_, ?_, ?_⟩
  · exact fun x hx ↦ conservationSolutionFromFoot_initial !₂[0, x] (by simp)
      (hproperties _ hx).2.2.2.1
  · intro t ht
    have htd : |t| < d := ht.trans_le (min_le_left d e)
    refine ⟨(hmono htd).mono (ball_subset_ball (min_le_left d e)), fun x hx ↦ ?_⟩
    have hxd : x ∈ ball x₀ d := ball_subset_ball (min_le_left d e) hx
    have hvel : a (g x) = A (G x) :=
      (hdata hxd).2.1.self_of_nhds.trans (congrArg A (hdata hxd).1.self_of_nhds)
    have hχx : !₂[t, conservationCharPosition a g t x] ∈ U := by
      change !₂[t, x + t * a (g x)] ∈ U
      rw [hvel]
      exact (hsmallrect ht (by simpa only [mem_ball, Real.dist_eq] using hx)).1
    exact ⟨(hderiv htd hxd).1, (hderiv htd hxd).2, hχx,
      (hmono htd).injOn (hUsub hχx).2.1 hxd (hproperties _ hχx).2.2.2.1.symm⟩
  · intro p ht hx
    have hp := (hsmallrect ht hx).2
    have hpj : j (p 0, p 1) = p := by ext i; fin_cases i <;> simp [j]
    rwa [hpj] at hp

end PDE.Hyperbolic.ConservationLaw.Scalar
