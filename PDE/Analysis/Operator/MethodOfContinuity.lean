/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# The method of continuity

For a norm-continuous family of bounded linear operators `A t : X →L[𝕜] Y`,
the estimate `‖u‖ ≤ C * ‖A t u‖` controls both uniqueness and the size of a
solvability-preserving perturbation. If this estimate holds locally uniformly
in the parameter, surjectivity is locally constant. On a connected parameter
space, solvability at one parameter therefore implies unique solvability
everywhere.

This is the continuation step of nonvariational elliptic existence proofs.
Only `X` must be complete, and the a priori constants need only be locally
uniform in the parameter.

For the segment `(1 - t) • f + t • g`, `0 ≤ t ≤ 1`, norm continuity is
automatic: `bijective_of_uniform_bound_on_segment` needs only surjectivity of
`f` and one constant `C` with `‖u‖ ≤ C * ‖((1 - t) • f + t • g) u‖` along the
segment. In an elliptic application the boundary condition is built into `X`,
and this a priori estimate is what remains to prove.
-/

@[expose] public section

namespace PDE.Analysis.Operator

open Filter Topology
open scoped NNReal

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A surjective operator with inverse bound `C` remains surjective under a
perturbation of operator norm less than `1 / C`. The product formulation also
includes `C = 0`, when the hypotheses force both spaces to be trivial.

The proof solves `g u = y` by contraction of
`u ↦ f⁻¹ (y - (g - f) u)` on the complete solution space. -/
theorem surjective_of_uniform_bound_of_norm_sub_mul_lt_one
    (f g : X →L[𝕜] Y) {C : NNReal}
    (hbound : ∀ u, ‖u‖ ≤ (C : ℝ) * ‖f u‖)
    (hf : Function.Surjective f)
    (hsmall : (C : ℝ) * ‖g - f‖ < 1) :
    Function.Surjective g := by
  classical
  let inverse : Y → X := Function.surjInv hf
  have hinverse : Function.RightInverse inverse f := Function.rightInverse_surjInv hf
  have hlip : LipschitzWith C inverse :=
    (f.antilipschitz_of_bound hbound).to_rightInverse hinverse
  intro y
  let T : X → X := fun u ↦ inverse (y - (g - f) u)
  have hload : LipschitzWith ‖g - f‖₊ (fun u ↦ y - (g - f) u) := by
    refine LipschitzWith.of_dist_le_mul fun u v ↦ ?_
    rw [dist_sub_left]
    exact (g - f).lipschitzWith.dist_le_mul u v
  have hT : ContractingWith (C * ‖g - f‖₊) T :=
    ⟨by exact_mod_cast hsmall, hlip.comp hload⟩
  refine ⟨hT.fixedPoint T, ?_⟩
  have hfixed := congrArg f hT.fixedPoint_isFixedPt
  change f (inverse (y - (g - f) (hT.fixedPoint T))) = f (hT.fixedPoint T) at hfixed
  rw [hinverse, sub_apply, sub_eq_iff_eq_add] at hfixed
  simpa only [← add_sub_assoc, add_sub_cancel_left] using hfixed.symm

variable {ι : Type*} [TopologicalSpace ι]

/-- Surjectivity is locally constant when a norm-continuous operator family
obeys locally uniform inverse estimates. In particular, a nonsurjective
operator cannot be approached by solvable operators with uniformly bounded
inverses. -/
theorem isLocallyConstant_surjective_of_locally_uniform_bound
    (A : ι → X →L[𝕜] Y) (hA : Continuous A)
    (hbound : ∀ t, ∃ C : NNReal, ∀ᶠ s in 𝓝 t,
      ∀ u, ‖u‖ ≤ (C : ℝ) * ‖A s u‖) :
    IsLocallyConstant (fun t ↦ Function.Surjective (A t)) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun t ↦ ?_
  obtain ⟨C, hC⟩ := hbound t
  have ht : ∀ u, ‖u‖ ≤ (C : ℝ) * ‖A t u‖ := hC.self_of_nhds
  have hsmall : ∀ᶠ s in 𝓝 t, (C : ℝ) * ‖A s - A t‖ < 1 := by
    have hc : Continuous (fun s ↦ (C : ℝ) * ‖A s - A t‖) :=
      continuous_const.mul (hA.sub continuous_const).norm
    exact hc.continuousAt.eventually (gt_mem_nhds (by simp))
  filter_upwards [hC, hsmall] with s hs hst
  apply propext
  constructor
  · intro hsurj
    exact surjective_of_uniform_bound_of_norm_sub_mul_lt_one (A s) (A t) hs hsurj
      (by simpa only [norm_sub_rev] using hst)
  · intro hsurj
    exact surjective_of_uniform_bound_of_norm_sub_mul_lt_one (A t) (A s) ht hsurj hst

/-- **Method of continuity.** A norm-continuous family on a preconnected
parameter space is bijective everywhere if it is surjective at one parameter
and satisfies locally uniform a priori estimates.

The estimates imply injectivity; surjectivity is propagated by the
small-perturbation contraction argument. -/
theorem bijective_of_continuous_of_locally_uniform_bound
    [PreconnectedSpace ι]
    (A : ι → X →L[𝕜] Y) (hA : Continuous A)
    (hbound : ∀ t, ∃ C : NNReal, ∀ᶠ s in 𝓝 t,
      ∀ u, ‖u‖ ≤ (C : ℝ) * ‖A s u‖)
    (t₀ : ι) (hsurj : Function.Surjective (A t₀)) (t : ι) :
    Function.Bijective (A t) := by
  obtain ⟨C, hC⟩ := hbound t
  refine ⟨((A t).antilipschitz_of_bound (K := C) hC.self_of_nhds).injective, ?_⟩
  have heq := IsLocallyConstant.apply_eq_of_preconnectedSpace
    (isLocallyConstant_surjective_of_locally_uniform_bound A hA hbound) t t₀
  exact heq.mpr hsurj

/-- The usual global-estimate form of the method of continuity. The parameter
space may be any preconnected space, including a closed real interval. -/
theorem bijective_of_continuous_of_uniform_bound
    [PreconnectedSpace ι]
    (A : ι → X →L[𝕜] Y) (hA : Continuous A) {C : NNReal}
    (hbound : ∀ t u, ‖u‖ ≤ (C : ℝ) * ‖A t u‖)
    (t₀ : ι) (hsurj : Function.Surjective (A t₀)) (t : ι) :
    Function.Bijective (A t) :=
  bijective_of_continuous_of_locally_uniform_bound A hA
    (fun _ ↦ ⟨C, Filter.Eventually.of_forall hbound⟩) t₀ hsurj t

variable [NormedSpace ℝ X] [NormedSpace ℝ Y]

/-- Unique solvability at the endpoint of the affine family
`(1 - t) • f + t • g`, from solvability of `f` and a uniform estimate along
`0 ≤ t ≤ 1`. This is the usual interpolation between a model elliptic
operator and the operator whose solvability is sought. -/
theorem bijective_of_uniform_bound_on_segment
    (f g : X →L[ℝ] Y) {C : NNReal}
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u,
      ‖u‖ ≤ (C : ℝ) * ‖((1 - t) • f + t • g) u‖)
    (hf : Function.Surjective f) :
    Function.Bijective g := by
  let A : Set.Icc (0 : ℝ) 1 → X →L[ℝ] Y :=
    fun t ↦ (1 - (t : ℝ)) • f + (t : ℝ) • g
  have hA : Continuous A :=
    ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
      (continuous_subtype_val.smul continuous_const)
  have : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  have hzero : Function.Surjective (A ⟨0, by simp⟩) := by
    simpa [A] using hf
  have h := bijective_of_continuous_of_uniform_bound A hA
    (fun t ↦ hbound t t.property) ⟨0, by simp⟩ hzero ⟨1, by simp⟩
  simpa [A] using h

end PDE.Analysis.Operator
