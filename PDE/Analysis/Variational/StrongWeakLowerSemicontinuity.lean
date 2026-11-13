/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import PDE.Analysis.WeakCompactness

/-!
# Energy bounds under strong and weak convergence

A convex differentiable energy lies above each of its tangent affine functions.
For an energy depending on both a parameter and a state, we fix the limiting state
in this inequality. If the parameter converges strongly, the energy and its
supporting functional at that fixed state converge. The functional may then be
paired with the bounded, weakly convergent state family. Its correction tends
to zero, passing an upper energy bound to the limit.

The theorem takes the supporting inequality directly, so a chosen subgradient
also suffices. It works in any real normed space and along arbitrary nontrivial
filters. For an integral energy, continuity and integrability of the
supporting fields are the hypotheses to check.

This abstracts step 4 of the proof of weak lower semicontinuity in Evans, §8.2.2, Theorem 1.
There the parameter is `u_k`, which converges to `u` strongly, the state is `Du_k ⇀ Du`,
`F z v = ∫_{G_ε} L(v, z, x) dx`, and `D z v` is integration against `D_pL(v, z, x)` over
`G_ε`. Then `hsupport` is his convexity inequality (23), and the two limits are his (24) and
(25). Evans obtains them from the uniform convergence (17) on the sets `G_ε`; we assume
instead continuity in the parameter at the limit, with the state fixed. As the Remark after
his proof says, `Du_k` enters (23) linearly, so no convexity in `z` is needed.

## Main results

* `le_of_tendsto_strong_weak_of_supporting_functionals`: if `x i → xLimit`, `y i ⇀ yLimit`
  with `‖y i‖ ≤ R`, `F` and `D` are continuous in the parameter at `xLimit` with the state
  `yLimit` fixed, and `F z v + D z v (w - v) ≤ F z w`, then an eventual bound
  `F (x i) (y i) ≤ c` gives `F xLimit yLimit ≤ c`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.2, Theorem 1 (Weak lower semicontinuity) and its
  proof, (12)-(25), pp. 468-469, and the Remark after it, p. 470.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Filter
open scoped Topology

namespace PDE.Analysis

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A supporting-functional inequality passes an upper energy bound to a limit
when the parameter converges strongly and the state converges weakly with a
uniform norm bound. Continuity is needed only at the limiting parameter and
with the limiting state held fixed. Convex differentiable energies supply the
supporting inequality through their derivative in the second variable. -/
theorem le_of_tendsto_strong_weak_of_supporting_functionals
    {X ι : Type*} [TopologicalSpace X] {l : Filter ι} [l.NeBot]
    {x : ι → X} {xLimit : X} (hx : Tendsto x l (𝓝 xLimit))
    {y : ι → G} {yLimit : G}
    (hy : Tendsto (fun i ↦ toWeakSpace ℝ G (y i)) l
      (𝓝 (toWeakSpace ℝ G yLimit)))
    (R : ℝ) (hyR : ∀ i, ‖y i‖ ≤ R)
    (F : X → G → ℝ) (D : X → G → StrongDual ℝ G)
    (hF : ContinuousAt (fun z ↦ F z yLimit) xLimit)
    (hD : ContinuousAt (fun z ↦ D z yLimit) xLimit)
    (hsupport : ∀ z v w, F z v + D z v (w - v) ≤ F z w)
    {c : ℝ} (hbound : ∀ᶠ i in l, F (x i) (y i) ≤ c) :
    F xLimit yLimit ≤ c := by
  have hdual := hD.tendsto.comp hx
  have hpair := WeakCompactness.tendsto_dual_apply_of_tendsto_strong_weak
    hdual hy R hyR
  have hfixed := (ContinuousLinearMap.apply ℝ ℝ yLimit).continuous.continuousAt.tendsto.comp
    hdual
  have hcorrection : Tendsto (fun i ↦ D (x i) yLimit (y i - yLimit)) l (𝓝 0) := by
    simpa only [map_sub, Function.comp_apply, ContinuousLinearMap.apply_apply, sub_self]
      using hpair.sub hfixed
  have hminor := (hF.tendsto.comp hx).add hcorrection
  simpa only [add_zero] using le_of_tendsto hminor
    (hbound.mono fun i hi ↦ (hsupport (x i) yLimit (y i)).trans hi)

end PDE.Analysis
