/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.SmoothDependence.LocalSecondOrder

/-!
# Jointly C² local families for nonautonomous equations

Adjoin the clock variable to turn `y' = c(s,y)` into the autonomous equation
`(s,y)' = (1,c(s,y))`. The constructed clock equals its initial value plus elapsed
time, by the mean value theorem. This gives joint C² dependence on elapsed time and
initial data from a C² germ of the original nonautonomous vector field.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Analysis.ODE

/-- A local C² nonautonomous vector field constructs a jointly C² solution family,
with identity initial data and the original differential equation near the base point. -/
theorem exists_local_contDiff_two_nonautonomous_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {c : ℝ × E → E} {s₀ : ℝ} {y₀ : E} (hc : ContDiffAt ℝ 2 c (s₀, y₀)) :
    ∃ Φ : ℝ → E → E,
      ContDiffAt ℝ 2 (fun p : ℝ × E ↦ Φ p.1 p.2) (0, y₀) ∧
      (Φ 0 =ᶠ[𝓝 y₀] id) ∧
      (∀ᶠ p : ℝ × E in 𝓝 (0, y₀),
        HasDerivAt (fun t ↦ Φ t p.2) (c (s₀ + p.1, Φ p.1 p.2)) p.1) := by
  let v : ℝ × E → ℝ × E := fun p ↦ (1, c p)
  obtain ⟨R, _hR₀, hR, hzero, hode⟩ :=
    exists_local_contDiff_two_flow_of_contDiffAt (contDiffAt_const.prodMk hc)
  let F : ℝ × E → ℝ × E := fun p ↦ R (p.1, (s₀, p.2))
  have hF : ContDiffAt ℝ 2 F (0, y₀) :=
    hR.comp (0, y₀) (contDiffAt_fst.prodMk (contDiffAt_const.prodMk contDiffAt_snd))
  have hinit : ∀ᶠ y in 𝓝 y₀, F (0, y) = (s₀, y) :=
    (continuousAt_const.prodMk continuousAt_id).eventually hzero
  have hsolve : ∀ᶠ p : ℝ × E in 𝓝 (0, y₀),
      HasDerivAt (fun t ↦ F (t, p.2)) (v (F p)) p.1 := by
    have hmap : ContinuousAt (fun p : ℝ × E ↦ (p.1, (s₀, p.2))) (0, y₀) :=
      continuousAt_fst.prodMk (continuousAt_const.prodMk continuousAt_snd)
    exact hmap.eventually hode
  have hclock : ∀ᶠ p : ℝ × E in 𝓝 (0, y₀), (F p).1 = s₀ + p.1 := by
    have hprod := hsolve
    rw [nhds_prod_eq] at hprod
    obtain ⟨pa, ha, pb, hb, hp⟩ := eventually_prod_iff.mp hprod
    obtain ⟨a, b, ⟨ha₀, h₀b⟩, hab⟩ := ha.exists_Ioo_subset
    filter_upwards [continuousAt_fst.eventually (Ioo_mem_nhds ha₀ h₀b),
      continuousAt_snd.eventually (hb.and hinit)] with p ht hy
    have hd (t : ℝ) (ht : t ∈ Ioo a b) :
        HasDerivAt (fun s ↦ (F (s, p.2)).1) 1 t :=
      (hp (hab ht) hy.1).fst
    have hg (t : ℝ) : HasDerivAt (fun s ↦ s₀ + s) 1 t := by
      have h := (hasDerivAt_const t s₀).add (hasDerivAt_id t)
      change HasDerivAt (fun s : ℝ ↦ s₀ + s) ((0 : ℝ) + 1) t at h
      simpa only [zero_add] using h
    have heq := isOpen_Ioo.eqOn_of_deriv_eq isPreconnected_Ioo
      (fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt)
      (fun t _ ↦ (hg t).differentiableAt.differentiableWithinAt)
      (fun t ht ↦ (hd t ht).deriv.trans (hg t).deriv.symm)
      (show (0 : ℝ) ∈ Ioo a b from ⟨ha₀, h₀b⟩)
      (show (F (0, p.2)).1 = s₀ + 0 by simp only [hy.2, add_zero])
    exact heq ht
  refine ⟨fun t y ↦ (F (t, y)).2, hF.snd, ?_, ?_⟩
  · exact hinit.mono fun _ hy ↦ congrArg Prod.snd hy
  · filter_upwards [hsolve, hclock] with p hp ht
    have h := hp.snd
    change HasDerivAt (fun t ↦ (F (t, p.2)).2) (c (F p)) p.1 at h
    simpa only [← ht, Prod.eta] using h

end PDE.Analysis.ODE
