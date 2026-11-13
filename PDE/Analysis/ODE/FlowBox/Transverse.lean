/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import PDE.Analysis.ODE.SmoothDependence.Local
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Flow coordinates from a transverse linear section

Flow a transverse affine section of a C¹ vector field. Its derivative at time zero is
the prescribed linear coordinate equivalence, so the inverse function theorem constructs
local C¹ coordinates in which the vector field is the first coordinate vector.

The chart is Mathlib's `OpenPartialHomeomorph`; regularity is asserted on its open source
and target. Only the germ of the vector field at the base point is used.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Analysis.ODE

/-- A transverse linear section constructs a C¹ flow box. The coordinate derivative
at the base point is prescribed, and throughout the source the vector field becomes
the constant time direction. -/
theorem exists_flow_box_of_transverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {v : E → E} {q₀ : E} (hv : ContDiffAt ℝ 1 v q₀)
    (e : (ℝ × F) ≃L[ℝ] E) (he : v q₀ = e (1, 0)) :
    ∃ c : OpenPartialHomeomorph E (ℝ × F),
      q₀ ∈ c.source ∧ c q₀ = 0 ∧
      ContDiffOn ℝ 1 c c.source ∧ ContDiffOn ℝ 1 c.symm c.target ∧
      HasFDerivAt c (e.symm : E →L[ℝ] ℝ × F) q₀ ∧
      ∀ q ∈ c.source, fderiv ℝ c q (v q) = (1, 0) := by
  obtain ⟨R, hR₀, hR, hzero, hode⟩ := exists_local_flow_of_contDiffAt hv
  let j : ℝ × F → ℝ × E := fun p ↦ (p.1, q₀ + e (0, p.2))
  let X : ℝ × F → E := R ∘ j
  have hj₀ : j 0 = (0, q₀) := by simp [j]
  have hj : ContDiff ℝ 1 j :=
    contDiff_fst.prodMk (contDiff_const.add (e.contDiff.comp
      (contDiff_const.prodMk contDiff_snd)))
  have hX : ContDiffAt ℝ 1 X 0 := (hj₀ ▸ hR).comp 0 hj.contDiffAt
  have hX₀ : X 0 = q₀ := by simp [X, hj₀, hR₀]
  have hDj : HasFDerivAt j
      ((ContinuousLinearMap.fst ℝ ℝ F).prod
        (e.toContinuousLinearMap.comp
          ((0 : (ℝ × F) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ F)))) 0 :=
    hasFDerivAt_fst.prodMk
      ((e.hasFDerivAt.comp 0 ((hasFDerivAt_const 0 0).prodMk hasFDerivAt_snd)).const_add q₀)
  have hDX : HasFDerivAt X (e : (ℝ × F) →L[ℝ] E) 0 := by
    have hd := (hj₀ ▸ (hzero.self_of_nhds).2).comp 0 hDj
    convert! hd using 1
    refine ContinuousLinearMap.ext fun p ↦ ?_
    change e p = e (0, p.2) + p.1 • v q₀
    rw [he, ← map_smul, ← map_add]
    congr 1
    simp
  let a : OpenPartialHomeomorph (ℝ × F) E :=
    hX.toOpenPartialHomeomorph X hDX one_ne_zero
  have ha₀ : (0 : ℝ × F) ∈ a.source :=
    hX.mem_toOpenPartialHomeomorph_source hDX one_ne_zero
  have hqa : q₀ ∈ a.target := by
    simpa only [hX₀] using hX.image_mem_toOpenPartialHomeomorph_target hDX one_ne_zero
  have hca₀ : a.symm q₀ = 0 := hX₀ ▸ a.left_inv ha₀
  have hc : ContDiffAt ℝ 1 a.symm q₀ := hX₀ ▸ hX.to_localInverse hDX one_ne_zero
  have hDc : HasFDerivAt a.symm (e.symm : E →L[ℝ] ℝ × F) q₀ :=
    hX₀ ▸ (hX.hasStrictFDerivAt' hDX one_ne_zero).to_localInverse.hasFDerivAt
  have hsolve : ∀ᶠ p : ℝ × F in 𝓝 0,
      HasDerivAt (fun t ↦ X (t, p.2)) (v (X p)) p.1 := by
    have ht : Tendsto j (𝓝 0) (𝓝 (0, q₀)) := by
      simpa only [ContinuousAt, hj₀] using hj.continuous.continuousAt (x := 0)
    exact ht.eventually hode
  have hnear : ∀ᶠ q in 𝓝 q₀,
      q ∈ a.target ∧ ContDiffAt ℝ 1 a.symm q ∧
      ContDiffAt ℝ 1 X (a.symm q) ∧
      HasDerivAt (fun t ↦ X (t, (a.symm q).2)) (v (X (a.symm q))) (a.symm q).1 := by
    have ht : Tendsto a.symm (𝓝 q₀) (𝓝 (0 : ℝ × F)) := hca₀ ▸ hc.continuousAt
    filter_upwards [a.open_target.mem_nhds hqa, hc.eventually (by simp),
      ht.eventually (hX.eventually (by simp)), ht.eventually hsolve] with q hq hreg hx hs
      using ⟨hq, hreg, hx, hs⟩
  obtain ⟨V, hVsub, hV, hqV⟩ := mem_nhds_iff.mp hnear
  let c := a.symm.restrOpen V hV
  have hsource (q : E) (hq : q ∈ c.source) : q ∈ V := hq.2
  refine ⟨c, ⟨hqa, hqV⟩, hca₀, fun q hq ↦ (hVsub (hsource q hq)).2.1.contDiffWithinAt, ?_,
    hDc, ?_⟩
  · intro p hp
    have hq := hVsub (hsource (c.symm p) (c.map_target hp))
    have hi : a.symm (c.symm p) = p := c.right_inv hp
    exact (hi ▸ hq.2.2.1).contDiffWithinAt
  · intro q hq
    obtain ⟨hqt, hreg, _, hs⟩ := hVsub (hsource q hq)
    let p := a.symm q
    have hp : p ∈ a.source := a.map_target hqt
    have hXq : X p = q := a.right_inv hqt
    have hd := (hXq ▸ hreg.differentiableAt_one.hasFDerivAt).comp_hasDerivAt p.1 hs
    have hid : (fun t ↦ a.symm (X (t, p.2))) =ᶠ[𝓝 p.1] fun t ↦ (t, p.2) := by
      filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually
        (a.open_source.mem_nhds hp)] with t ht
      exact a.left_inv ht
    have hi := (hd.congr_of_eventuallyEq hid.symm).unique
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
    change fderiv ℝ a.symm (X p) (v (X p)) = (1, 0) at hi
    simpa only [c, OpenPartialHomeomorph.coe_restrOpen, hXq] using hi

end PDE.Analysis.ODE
