/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Regularity of an existing implicit solution

Local uniqueness in the implicit function theorem transfers regularity to an
already constructed continuous solution. The solution need not be the particular
function chosen by the theorem.
-/

@[expose] public section

open Filter Set
open scoped ContDiff Topology

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- A continuous solution of a regular implicit equation has the regularity of
the equation. This includes infinite differentiability. -/
theorem ContDiffAt.of_implicit_eq
    {n : ℕ∞ω} {f : E × F → G} {s : E → F} {x : E}
    (hf : ContDiffAt ℝ n f (x, s x)) (hn : n ≠ 0)
    (hinv : ((fderiv ℝ f (x, s x)).comp
      (ContinuousLinearMap.inr ℝ E F)).IsInvertible)
    (hs : ContinuousAt s x)
    (heq : ∀ᶠ y in 𝓝 x, f (y, s y) = f (x, s x)) :
    ContDiffAt ℝ n s x := by
  have hnear := (continuousAt_id.prodMk hs).eventually
    (hf.eventually_apply_eq_iff_implicitFunction hn hinv)
  apply (hf.contDiffAt_implicitFunction hn hinv).congr_of_eventuallyEq
  filter_upwards [hnear, heq] with y hy hfy
  exact (hy.mp hfy).symm

/-- On a smaller open neighborhood, an existing continuous implicit solution
has the regularity of the equation on its open domain. The neighborhood works
for the given order, including `∞`; no passage through finite-order
neighborhoods is involved. -/
theorem ContDiffOn.exists_contDiffOn_of_implicit_eq
    {n : ℕ∞ω} {f : E × F → G} {s : E → F} {x : E}
    {U : Set (E × F)} {I : Set E} {c : G}
    (hf : ContDiffOn ℝ n f U) (hn : n ≠ 0) (hU : IsOpen U)
    (hI : IsOpen I) (hx : x ∈ I) (hs : ContinuousOn s I)
    (hgraph : ∀ y ∈ I, (y, s y) ∈ U)
    (heq : ∀ y ∈ I, f (y, s y) = c)
    (hinv : ((fderiv ℝ f (x, s x)).comp
      (ContinuousLinearMap.inr ℝ E F)).IsInvertible) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ I ∧ ContDiffOn ℝ n s V := by
  have hsx : ContinuousAt s x := hs.continuousAt (hI.mem_nhds hx)
  have hfx : ContDiffAt ℝ n f (x, s x) :=
    hf.contDiffAt (hU.mem_nhds (hgraph x hx))
  have hpartial : ContinuousAt
      (fun z : E × F ↦ (fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ E F))
      (x, s x) :=
    (hfx.continuousAt_fderiv hn).clm_comp continuousAt_const
  have hnear : ∀ᶠ y in 𝓝 x,
      ((fderiv ℝ f (y, s y)).comp (ContinuousLinearMap.inr ℝ E F)).IsInvertible :=
    (continuousAt_id.prodMk hsx).eventually
      (hpartial.eventually hinv.eventually_nhds)
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp (inter_mem (hI.mem_nhds hx) hnear)
  refine ⟨V, hVo, hxV, fun y hy ↦ (hV hy).1, ?_⟩
  intro y hy
  have hyI := (hV hy).1
  have hfy := hf.contDiffAt (hU.mem_nhds (hgraph y hyI))
  apply (hfy.of_implicit_eq hn (hV hy).2
    (hs.continuousAt (hI.mem_nhds hyI)) ?_).contDiffWithinAt
  filter_upwards [hI.mem_nhds hyI] with z hz
  exact (heq z hz).trans (heq y hyI).symm
