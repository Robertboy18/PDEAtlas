/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.ClosureRegularity
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.ClassicalExtension

/-!
# Planar Green potentials are `Cᵏ` up to the boundary

For a compact `Cᵏ` source with `k ≥ 2`, the canonical half-space Green potential is `Cᵏ` within
the closed upper half-plane, also when the source is nonzero on the boundary. The proof is an
induction on `k` from the `C²` case: the tangential derivative of the potential is the potential
of the tangential derivative of the source, and the derivative of the normal first derivative is
the field `normalDerivativeFDeriv`, whose normal component `-f - ∂₀²u` comes from the Poisson
equation. Only values of the source on the closed half-plane matter, so the same holds for
sources that are `Cᵏ` within the closed half-plane.

## Main results

* `contDiffOn_partialDeriv_closure_upper_two`: a coordinate derivative of a differentiable
  function that is `C^(k+1)` within the closed upper half-plane is `Cᵏ` there.
* `contDiffOn_halfSpaceGreenPotential_closure`: a compact `Cᵏ` source with `k ≥ 2` has a Green
  potential that is `Cᵏ` within the closed upper half-plane.
* `contDiffOn_halfSpaceGreenPotential_closure_of_contDiffOn`: the same for a compact source that
  is `Cᵏ` only within the closed upper half-plane.
-/

@[expose] public section

noncomputable section

namespace GreenFunction

open Filter Topology Set SobolevSpace

/-- The closed upper half-plane has unique derivatives. -/
theorem uniqueDiffOn_closure_upper_two : UniqueDiffOn ℝ (closure (HalfSpace.upper 2)) := by
  apply uniqueDiffOn_convex (HalfSpace.convex_upper 2).closure
  obtain ⟨x, hx⟩ : (HalfSpace.upper 2).Nonempty :=
    ⟨EuclideanSpace.single 1 1, by simp [HalfSpace.upper, PDE.Common.lastIndex]⟩
  exact ⟨x, interior_mono subset_closure ((HalfSpace.isOpen_upper 2).interior_eq.symm ▸ hx)⟩

/-- A coordinate derivative of a globally differentiable function that is `C^(k+1)` within the
closed upper half-plane is `Cᵏ` there. -/
theorem contDiffOn_partialDeriv_closure_upper_two {v : ℝ^2 → ℝ} {k : ℕ}
    (hv : Differentiable ℝ v) (hk : ContDiffOn ℝ (k + 1) v (closure (HalfSpace.upper 2)))
    (i : Fin 2) :
    ContDiffOn ℝ k (∂[i] v) (closure (HalfSpace.upper 2)) := by
  have hD := hk.fderivWithin uniqueDiffOn_closure_upper_two (m := k) (by norm_cast)
  have heq : EqOn (fun y ↦ fderivWithin ℝ v (closure (HalfSpace.upper 2)) y) (fderiv ℝ v)
      (closure (HalfSpace.upper 2)) := fun y hy ↦
    (hv y).hasFDerivAt.hasFDerivWithinAt.fderivWithin (uniqueDiffOn_closure_upper_two y hy)
  exact (hD.congr fun y hy ↦ (heq hy).symm).clm_apply contDiffOn_const

/-- A compact `Cᵏ` source with `k ≥ 2` has a Green potential that is `Cᵏ` within the closed
upper half-plane. The source may be nonzero on the boundary. -/
theorem contDiffOn_halfSpaceGreenPotential_closure {k : ℕ} (hk : 2 ≤ k) {f : ℝ^2 → ℝ}
    (hf : ContDiff ℝ k f) (hc : HasCompactSupport f) :
    ContDiffOn ℝ k (halfSpaceGreenPotential f) (closure (HalfSpace.upper 2)) := by
  induction k, hk using Nat.le_induction generalizing f with
  | base => exact contDiffOn_two_halfSpaceGreenPotential_closure hf hc
  | succ k hk ih =>
    set s := closure (HalfSpace.upper 2)
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_cast; omega)
    have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_cast; omega)
    -- the tangential derivative of the source and its potential
    have hd : ContDiff ℝ k (∂[(0 : Fin 2)] f) := by
      simpa using hf.partialDeriv (0 : Fin 2)
    have hdc : HasCompactSupport (∂[(0 : Fin 2)] f) :=
      hc.fderiv_apply ℝ (EuclideanSpace.single 0 (1 : ℝ))
    have htan : ∂[(0 : Fin 2)] (halfSpaceGreenPotential f) =
        halfSpaceGreenPotential (∂[(0 : Fin 2)] f) :=
      partialDeriv_halfSpaceGreenPotential_eq hf1 hc
    have hv := ih hd hdc
    have hvdiff : Differentiable ℝ (halfSpaceGreenPotential (∂[(0 : Fin 2)] f)) :=
      (contDiff_one_halfSpaceGreenPotential hd.continuous hdc).differentiable one_ne_zero
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    -- the normal derivative is `C^(j+1)` by its derivative field
    have hnormal : ContDiffOn ℝ (j + 1 : ℕ) (∂[(1 : Fin 2)] (halfSpaceGreenPotential f)) s := by
      refine (contDiffOn_succ_iff_hasFDerivWithinAt (n := j) (by simp)).mpr fun x hx ↦
        ⟨s, by simpa only [insert_eq_of_mem hx] using (self_mem_nhdsWithin : s ∈ 𝓝[s] x), by simp,
          normalDerivativeFDeriv f, fun y _ ↦
            hasFDerivWithinAt_partialDeriv_halfSpaceGreenPotential_normal_closure hf2 hc y, ?_⟩
      · have h10 : ContDiffOn ℝ j (∂[(1 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential f)))
            s := by
          rw [htan]
          exact contDiffOn_partialDeriv_closure_upper_two hvdiff (by exact_mod_cast hv) 1
        have h00 : ContDiffOn ℝ j (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential f)))
            s := by
          rw [htan]
          exact contDiffOn_partialDeriv_closure_upper_two hvdiff (by exact_mod_cast hv) 0
        have hfj : ContDiffOn ℝ j f s := (hf.of_le (by norm_cast; omega)).contDiffOn
        unfold normalDerivativeFDeriv
        exact (h10.smul contDiffOn_const).add ((hfj.neg.sub h00).smul contDiffOn_const)
    have hpartial (i : Fin 2) :
        ContDiffOn ℝ (j + 1 : ℕ) (∂[i] (halfSpaceGreenPotential f)) s := by
      fin_cases i
      exacts [htan ▸ hv, hnormal]
    have hD : ContDiffOn ℝ (j + 1 : ℕ) (fderiv ℝ (halfSpaceGreenPotential f)) s := by
      rw [show fderiv ℝ (halfSpaceGreenPotential f) = fun x ↦ ∑ i : Fin 2,
          (∂[i] (halfSpaceGreenPotential f)) x • (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ) from
        funext (PDE.fderiv_eq_sum_partialDeriv_smul_proj _)]
      exact ContDiffOn.sum fun i _ ↦ (hpartial i).smul contDiffOn_const
    have hu := contDiff_one_halfSpaceGreenPotential hf.continuous hc
    refine (contDiffOn_succ_iff_hasFDerivWithinAt (n := (j + 1 : ℕ)) (by simp)).mpr fun x hx ↦
      ⟨s, by simpa only [insert_eq_of_mem hx] using (self_mem_nhdsWithin : s ∈ 𝓝[s] x), by simp,
        fderiv ℝ _, fun y _ ↦ ((hu.differentiable one_ne_zero) y).hasFDerivAt.hasFDerivWithinAt,
        hD⟩

/-- Only regularity within the closed half-plane is needed: a compact source that is `Cᵏ`
within the closed upper half-plane, `k ≥ 2`, has a Green potential that is `Cᵏ` there. -/
theorem contDiffOn_halfSpaceGreenPotential_closure_of_contDiffOn {k : ℕ} (hk : 2 ≤ k)
    {f : ℝ^2 → ℝ} (hf : ContDiffOn ℝ k f (closure (HalfSpace.upper 2)))
    (hc : HasCompactSupport f) :
    ContDiffOn ℝ k (halfSpaceGreenPotential f) (closure (HalfSpace.upper 2)) := by
  rw [HalfSpace.closure_upper_two] at hf
  obtain ⟨F, hF, hFc, heq⟩ :=
    PDE.Analysis.exists_contDiff_compact_extension_halfSpace (1 : Fin 2) k hf hc
  rw [← HalfSpace.closure_upper_two] at heq
  have hpotential : halfSpaceGreenPotential f = halfSpaceGreenPotential F :=
    halfSpaceGreenPotential_congr (fun y hy ↦ (heq (subset_closure hy)).symm)
  rw [hpotential]
  exact contDiffOn_halfSpaceGreenPotential_closure hk hF hFc

end GreenFunction
