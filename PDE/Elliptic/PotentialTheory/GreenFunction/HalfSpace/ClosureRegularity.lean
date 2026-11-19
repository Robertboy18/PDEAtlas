/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.SecondDerivative
import Mathlib.Analysis.Calculus.FDeriv.Extend
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.ClassicalExtension
import PDE.FDeriv.Laplacian.Congruence

/-!
# Planar Green potentials are C² up to the boundary

For a compact `C²` source, the canonical half-space Green potential is `C²`
within the closed upper half-plane. The continuous tangential and mixed
second derivatives determine the missing normal derivative through the
interior Poisson equation. Mathlib's derivative-extension theorem then
extends the first derivatives to derivatives within the closure.

The source may be nonzero on the boundary. The assertion is within the
physical half-plane; the odd potential need not be `C²` across that boundary.

## Main definitions

* `normalDerivativeFDeriv`: the continuous derivative field of the normal first derivative of the
  potential on the closed half-plane, with normal component supplied by the Poisson equation.

## Main results

* `contDiffOn_one_partialDeriv_halfSpaceGreenPotential_normal_closure`: the normal first
  derivative is `C¹` within the closed upper half-plane.
* `contDiffOn_two_halfSpaceGreenPotential_closure`: a compact `C²` source has a `C²` Green
  potential within the closed upper half-plane, also with nonzero boundary vorticity.
* `exists_contDiff_two_halfSpaceGreenPotential_extension`: the Green potential has a global `C²`
  representative agreeing with it on the closed half-plane.
* `contDiffOn_two_halfSpaceGreenPotential_closure_of_contDiffOn`: the same regularity when the
  source is only smooth within the closed half-plane.
* `exists_contDiff_two_halfSpaceGreenPotential_extension_of_contDiffOn`: the global `C²`
  representative for such a source.
-/

@[expose] public section

noncomputable section

namespace GreenFunction

open MeasureTheory Filter Topology Set SobolevSpace

/-- The continuous derivative field of the potential's normal first derivative
on the closed physical half-plane. The Poisson equation supplies its normal component. -/
def normalDerivativeFDeriv (f : ℝ^2 → ℝ) (x : ℝ^2) : ℝ^2 →L[ℝ] ℝ :=
  (∂[(1 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential f))) x •
      (EuclideanSpace.proj (0 : Fin 2)) +
    (-f x - (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential f))) x) •
      (EuclideanSpace.proj (1 : Fin 2))

/-- The normal first derivative's prescribed derivative field is continuous. -/
theorem continuous_normalDerivativeFDeriv
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Continuous (normalDerivativeFDeriv f) := by
  unfold normalDerivativeFDeriv
  exact ((continuous_secondPartialDeriv_halfSpaceGreenPotential_tangential hf hc 1).smul
    continuous_const).add
      ((hf.continuous.neg.sub
        (continuous_secondPartialDeriv_halfSpaceGreenPotential_tangential hf hc 0)).smul
          continuous_const)

/-- Inside the physical half-plane, the normal derivative field agrees with the
classical derivative. -/
theorem hasFDerivAt_partialDeriv_halfSpaceGreenPotential_normal
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    {x : ℝ^2} (hx : x ∈ HalfSpace.upper 2) :
    HasFDerivAt (∂[(1 : Fin 2)] (halfSpaceGreenPotential f))
      (normalDerivativeFDeriv f x) x := by
  obtain ⟨hreg, hpoisson⟩ := halfSpaceGreenPotential_local_poisson hf.continuous hc hx hf.contDiffAt
  have hderiv := (PDE.contDiffAt_partialDeriv 1 hreg (1 : Fin 2)).differentiableAt_one.hasFDerivAt
  have hswap := PDE.partialDeriv_partialDeriv_comm_at (0 : Fin 2) (1 : Fin 2) hreg
  have hnormal : (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] (halfSpaceGreenPotential f))) x =
      -f x - (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential f))) x := by
    simp only [PDE.laplacian, Fin.sum_univ_two] at hpoisson
    linarith
  rw [PDE.fderiv_eq_sum_partialDeriv_smul_proj, Fin.sum_univ_two, hswap, hnormal] at hderiv
  exact hderiv

/-- The normal first derivative has its prescribed derivative within the closed
upper half-plane, including at points with nonzero boundary source. -/
theorem hasFDerivWithinAt_partialDeriv_halfSpaceGreenPotential_normal_closure
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (x : ℝ^2) :
    HasFDerivWithinAt (∂[(1 : Fin 2)] (halfSpaceGreenPotential f))
      (normalDerivativeFDeriv f x) (closure (HalfSpace.upper 2)) x := by
  have hg : Continuous (∂[(1 : Fin 2)] (halfSpaceGreenPotential f)) := by
    change Continuous (fun y ↦ fderiv ℝ (halfSpaceGreenPotential f) y
      (EuclideanSpace.single 1 (1 : ℝ)))
    exact ((contDiff_one_halfSpaceGreenPotential hf.continuous hc).continuous_fderiv
      one_ne_zero).clm_apply continuous_const
  have hlim : Tendsto (fderiv ℝ (∂[(1 : Fin 2)] (halfSpaceGreenPotential f)))
      (𝓝[HalfSpace.upper 2] x) (𝓝 (normalDerivativeFDeriv f x)) := by
    have heq : fderiv ℝ (∂[(1 : Fin 2)] (halfSpaceGreenPotential f)) =ᶠ[
        𝓝[HalfSpace.upper 2] x] normalDerivativeFDeriv f := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hasFDerivAt_partialDeriv_halfSpaceGreenPotential_normal hf hc hy).fderiv
    exact (tendsto_congr' heq).mpr
      ((continuous_normalDerivativeFDeriv (hf.of_le (by norm_num)) hc).tendsto x
        |>.mono_left nhdsWithin_le_nhds)
  exact hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy ↦ by
      have hd := hasFDerivAt_partialDeriv_halfSpaceGreenPotential_normal hf hc hy
      exact hd.differentiableAt.differentiableWithinAt)
    (HalfSpace.convex_upper 2) (HalfSpace.isOpen_upper 2)
    (fun _ _ ↦ hg.continuousWithinAt) hlim

/-- The normal first derivative is `C¹` within the closed upper half-plane. -/
theorem contDiffOn_one_partialDeriv_halfSpaceGreenPotential_normal_closure
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ContDiffOn ℝ 1 (∂[(1 : Fin 2)] (halfSpaceGreenPotential f))
      (closure (HalfSpace.upper 2)) := by
  apply (contDiffOn_succ_iff_hasFDerivWithinAt (n := 0) (by simp)).mpr
  intro x hx
  refine ⟨closure (HalfSpace.upper 2), ?_, by simp, normalDerivativeFDeriv f, ?_, ?_⟩
  · simpa only [insert_eq_of_mem hx] using
      (self_mem_nhdsWithin : closure (HalfSpace.upper 2) ∈ 𝓝[closure (HalfSpace.upper 2)] x)
  · intro y _
    exact hasFDerivWithinAt_partialDeriv_halfSpaceGreenPotential_normal_closure hf hc y
  · exact contDiffOn_zero.mpr
      (continuous_normalDerivativeFDeriv (hf.of_le (by norm_num)) hc).continuousOn

/-- A compact `C²` source has a `C²` Green potential within the closed upper half-plane.
Nonzero boundary vorticity is allowed. -/
theorem contDiffOn_two_halfSpaceGreenPotential_closure
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ContDiffOn ℝ 2 (halfSpaceGreenPotential f) (closure (HalfSpace.upper 2)) := by
  have hpartial (i : Fin 2) : ContDiffOn ℝ 1 (∂[i] (halfSpaceGreenPotential f))
      (closure (HalfSpace.upper 2)) := by
    fin_cases i
    · exact (contDiff_one_partialDeriv_halfSpaceGreenPotential
        (hf.of_le (by norm_num)) hc).contDiffOn
    · exact contDiffOn_one_partialDeriv_halfSpaceGreenPotential_normal_closure hf hc
  have hD : ContDiffOn ℝ 1 (fderiv ℝ (halfSpaceGreenPotential f))
      (closure (HalfSpace.upper 2)) := by
    have heq : fderiv ℝ (halfSpaceGreenPotential f) = fun x ↦
        ∑ i : Fin 2, (∂[i] (halfSpaceGreenPotential f)) x •
          (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ) := by
      funext x
      exact PDE.fderiv_eq_sum_partialDeriv_smul_proj _ x
    rw [heq]
    exact ContDiffOn.sum fun i _ ↦ (hpartial i).smul contDiffOn_const
  apply (contDiffOn_succ_iff_hasFDerivWithinAt (n := 1) (by simp)).mpr
  intro x hx
  refine ⟨closure (HalfSpace.upper 2), ?_, by simp, fderiv ℝ (halfSpaceGreenPotential f), ?_, hD⟩
  · simpa only [insert_eq_of_mem hx] using
      (self_mem_nhdsWithin : closure (HalfSpace.upper 2) ∈ 𝓝[closure (HalfSpace.upper 2)] x)
  · intro y _
    have hd := (hasFDerivAt_halfSpaceGreenPotential hf.continuous hc y).differentiableAt
    exact hd.hasFDerivAt.hasFDerivWithinAt

/-- A compact `C²` source's Green potential has a global `C²` representative agreeing
on the closed physical half-plane. The representative preserves Poisson inversion
and the zero boundary values, including for nonzero boundary source. -/
theorem exists_contDiff_two_halfSpaceGreenPotential_extension
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ∃ u : ℝ^2 → ℝ, ContDiff ℝ 2 u ∧
      EqOn u (halfSpaceGreenPotential f) (closure (HalfSpace.upper 2)) ∧
      (∀ x ∈ HalfSpace.upper 2, -PDE.laplacian u x = f x) ∧
      ∀ x ∈ HalfSpace.boundary 2, u x = 0 := by
  have hclosed := contDiffOn_two_halfSpaceGreenPotential_closure hf hc
  rw [HalfSpace.closure_upper_two] at hclosed
  obtain ⟨u, hu, heq⟩ := PDE.Analysis.exists_contDiff_extension_halfSpace (1 : Fin 2) 2 hclosed
  have heqClosure : EqOn u (halfSpaceGreenPotential f) (closure (HalfSpace.upper 2)) := by
    rwa [HalfSpace.closure_upper_two]
  refine ⟨u, hu, heqClosure, ?_, ?_⟩
  · intro x hx
    have hgerm : u =ᶠ[𝓝 x] halfSpaceGreenPotential f := by
      filter_upwards [(HalfSpace.isOpen_upper 2).mem_nhds hx] with y hy
      exact heqClosure (subset_closure hy)
    rw [EuclideanLaplacian.laplacian_congr_nhds hgerm]
    exact (halfSpaceGreenPotential_local_poisson hf.continuous hc hx hf.contDiffAt).2
  · intro x hx
    have hxcl : x ∈ closure (HalfSpace.upper 2) := by
      apply frontier_subset_closure
      simpa only [HalfSpace.frontier_upper] using hx
    rw [heqClosure hxcl, halfSpaceGreenPotential_boundary f hx]

/-- Only physical-domain regularity of the source is required for `C²` Green
regularity up to the boundary. The source outside the closed half-plane is unrestricted. -/
theorem contDiffOn_two_halfSpaceGreenPotential_closure_of_contDiffOn
    {f : ℝ^2 → ℝ} (hf : ContDiffOn ℝ 2 f (closure (HalfSpace.upper 2)))
    (hc : HasCompactSupport f) :
    ContDiffOn ℝ 2 (halfSpaceGreenPotential f) (closure (HalfSpace.upper 2)) := by
  rw [HalfSpace.closure_upper_two] at hf
  obtain ⟨F, hF, hFc, heq⟩ :=
    PDE.Analysis.exists_contDiff_compact_extension_halfSpace (1 : Fin 2) 2 hf hc
  rw [← HalfSpace.closure_upper_two] at heq
  have hpotential : halfSpaceGreenPotential f = halfSpaceGreenPotential F :=
    halfSpaceGreenPotential_congr (fun y hy ↦ (heq (subset_closure hy)).symm)
  rw [hpotential]
  exact contDiffOn_two_halfSpaceGreenPotential_closure hF hFc

/-- A compact source smooth within the closed physical half-plane has a globally
`C²` representative of its Green potential preserving Poisson inversion and the boundary
values. -/
theorem exists_contDiff_two_halfSpaceGreenPotential_extension_of_contDiffOn
    {f : ℝ^2 → ℝ} (hf : ContDiffOn ℝ 2 f (closure (HalfSpace.upper 2)))
    (hc : HasCompactSupport f) :
    ∃ u : ℝ^2 → ℝ, ContDiff ℝ 2 u ∧
      EqOn u (halfSpaceGreenPotential f) (closure (HalfSpace.upper 2)) ∧
      (∀ x ∈ HalfSpace.upper 2, -PDE.laplacian u x = f x) ∧
      ∀ x ∈ HalfSpace.boundary 2, u x = 0 := by
  rw [HalfSpace.closure_upper_two] at hf
  obtain ⟨F, hF, hFc, heq⟩ :=
    PDE.Analysis.exists_contDiff_compact_extension_halfSpace (1 : Fin 2) 2 hf hc
  rw [← HalfSpace.closure_upper_two] at heq
  have hpotential : halfSpaceGreenPotential F = halfSpaceGreenPotential f :=
    halfSpaceGreenPotential_congr (fun y hy ↦ heq (subset_closure hy))
  obtain ⟨u, hu, hueq, hupoisson, huboundary⟩ :=
    exists_contDiff_two_halfSpaceGreenPotential_extension hF hFc
  refine ⟨u, hu, ?_, ?_, huboundary⟩
  · simpa only [hpotential] using hueq
  · intro x hx
    rw [hupoisson x hx, heq (subset_closure hx)]

end GreenFunction
