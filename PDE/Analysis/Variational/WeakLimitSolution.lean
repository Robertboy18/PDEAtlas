/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Variational.Exhaustion
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Weak limits of approximate solutions, with the limit kept

A bounded family of approximate solutions in a Hilbert space has a weakly convergent refinement,
and its weak limit solves the tested equations (`exists_solution_of_eventually_eq`). That theorem
keeps two image radii and the linear constraints, and forgets the refinement. Here the refinement
is part of the conclusion: the solution is a weak limit of the family along an ultrafilter finer
than the given filter. Every weakly lower semicontinuous bound of the family then passes to the
limit, and the caller chooses which, for example a weighted energy ball or a bound for every
combination `p ‖u‖ + q ‖∇u‖`. Nothing here identifies the limit of a nonlinear quantity that is
not observed through a compact map.

## Main results

* `exists_tendsto_weak_solution_of_eventually_eq` (all Hilbert spaces, all filters): a solution
  of the tested equations that is a weak limit of the family along an ultrafilter.
* `mul_norm_add_mul_norm_le_of_tendsto_weak` (all Hilbert spaces, all `p, q ≥ 0`): a bound of
  `p ‖A u‖ + q ‖A' u‖` passes to a weak limit.
* `exists_tendsto_weak_solution_of_scalar_feedback` (all Hilbert spaces): tested equations
  `lin t u - ℓ u · coef t u = forcing t`, with bounded linear functionals `lin t`, `ℓ` and
  `coef t`, pass to a weak limit along an ultrafilter, with no compactness.

## How it works

`WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter` extracts the
ultrafilter, and `tested_equation_of_tendsto_weak` passes each tested equation to the limit. A
nonnegative combination `p ‖A u‖ + q ‖A' u‖` of two image norms is the norm of `(p A u, q A' u)`
in the `ℓ¹` product of the two image spaces, so `norm_map_le_of_tendsto_weak` applies to it.
The weighted bound `a ‖u‖² + b ‖v‖² ≤ C` passes to the limit by
`WeakCompactness.weighted_norm_sq_add_le_of_tendsto_weak`. With a scalar feedback, the values
`lin t u`, `ℓ u` and `coef t u` converge along the ultrafilter because a bounded linear functional
is weakly continuous, and so does their combination.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 4.3, "Taking weak
  limits", and Section 4.4, the weak lower semicontinuity of the weighted `H¹` norm.
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public section

namespace PDE.Analysis.Variational

open Filter Set
open scoped Topology

variable {H Y Z T ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- **A weak limit that solves the tested equations.** Let `u` be a bounded family in a
Hilbert space such that each tested equation, with a linear part and a continuous nonlinear
part of a compact observation, holds eventually along `l`. Then some weak limit of the family
along an ultrafilter finer than `l` satisfies every tested equation. -/
theorem exists_tendsto_weak_solution_of_eventually_eq [CompleteSpace H]
    (l : Filter ι) [l.NeBot] (u : ι → H) (hbounded : Bornology.IsBounded (range u))
    (linear : T → StrongDual ℝ H) (observe : T → H →L[ℝ] Y)
    (hcompact : ∀ t, IsCompactOperator (observe t))
    (nonlinear : T → Y → ℝ) (hcontinuous : ∀ t, Continuous (nonlinear t))
    (forcing : T → ℝ)
    (hequation : ∀ t, ∀ᶠ i in l,
      linear t (u i) + nonlinear t (observe t (u i)) = forcing t) :
    ∃ (uLimit : H) (F : Ultrafilter ι), (F : Filter ι) ≤ l ∧
      Tendsto (fun i ↦ toWeakSpace ℝ H (u i)) F (𝓝 (toWeakSpace ℝ H uLimit)) ∧
      ∀ t, linear t uLimit + nonlinear t (observe t uLimit) = forcing t := by
  obtain ⟨uLimit, F, hle, hu⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter l u hbounded
  refine ⟨uLimit, F, hle, hu, fun t ↦ ?_⟩
  refine tested_equation_of_tendsto_weak (linear t) (observe t) (hcompact t) (nonlinear t)
    (hcontinuous t) (forcing t) hbounded hu ?_
  apply tendsto_const_nhds.congr'
  filter_upwards [(hequation t).filter_mono hle] with i hi
  exact (sub_eq_zero.mpr hi).symm

/-- **A combination of two image norms is weakly lower semicontinuous.** If `uᵢ ⇀ u` weakly
and eventually `p ‖A uᵢ‖ + q ‖A' uᵢ‖ ≤ ρ` with `p, q ≥ 0`, then `p ‖A u‖ + q ‖A' u‖ ≤ ρ`. The
combination is the norm of `(p A u, q A' u)` in the `ℓ¹` product of the two image spaces. -/
theorem mul_norm_add_mul_norm_le_of_tendsto_weak (A : H →L[ℝ] Y) (A' : H →L[ℝ] Z)
    {p q ρ : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) {l : Filter ι} [l.NeBot] {u : ι → H} {uLimit : H}
    (hu : Tendsto (fun i ↦ toWeakSpace ℝ H (u i)) l (𝓝 (toWeakSpace ℝ H uLimit)))
    (hbound : ∀ᶠ i in l, p * ‖A (u i)‖ + q * ‖A' (u i)‖ ≤ ρ) :
    p * ‖A uLimit‖ + q * ‖A' uLimit‖ ≤ ρ := by
  let L : H →L[ℝ] WithLp 1 (Y × Z) :=
    (WithLp.prodContinuousLinearEquiv 1 ℝ Y Z).symm.toContinuousLinearMap.comp
      ((p • A).prod (q • A'))
  have hL (w : H) : ‖L w‖ = p * ‖A w‖ + q * ‖A' w‖ := by
    rw [WithLp.prod_norm_eq_of_L1]
    change ‖p • A w‖ + ‖q • A' w‖ = _
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hp, Real.norm_of_nonneg hq]
  rw [← hL]
  exact norm_map_le_of_tendsto_weak L hu (hbound.mono fun i hi ↦ by rwa [hL])

/-- **A weak limit that solves tested equations with a scalar feedback.** Let `u` be a bounded
family in a Hilbert space and `ℓ` a bounded linear functional. If each tested equation
`lin t (u i) - ℓ (u i) · coef t (u i) = forcing t`, with bounded linear functionals `lin t` and
`coef t`, holds eventually along `l`, then some weak limit `w` of the family along an ultrafilter
finer than `l` satisfies `lin t w - ℓ w · coef t w = forcing t` for every test. A bounded linear
functional is weakly continuous, so the three values converge and so does the product; no
compactness is used. -/
theorem exists_tendsto_weak_solution_of_scalar_feedback [CompleteSpace H]
    (l : Filter ι) [l.NeBot] (u : ι → H) (hbounded : Bornology.IsBounded (range u))
    (ℓ : StrongDual ℝ H) (lin coef : T → StrongDual ℝ H) (forcing : T → ℝ)
    (hequation : ∀ t, ∀ᶠ i in l, lin t (u i) - ℓ (u i) * coef t (u i) = forcing t) :
    ∃ (w : H) (F : Ultrafilter ι), (F : Filter ι) ≤ l ∧
      Tendsto (fun i ↦ toWeakSpace ℝ H (u i)) F (𝓝 (toWeakSpace ℝ H w)) ∧
      ∀ t, lin t w - ℓ w * coef t w = forcing t := by
  obtain ⟨w, F, hle, hu⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter l u hbounded
  refine ⟨w, F, hle, hu, fun t ↦ ?_⟩
  have hev (ell : StrongDual ℝ H) : Tendsto (fun i ↦ ell (u i)) F (𝓝 (ell w)) := by
    simpa only [LinearEquiv.symm_apply_apply] using WeakCompactness.tendsto_evaluation hu ell
  have hlim : Tendsto (fun i ↦ lin t (u i) - ℓ (u i) * coef t (u i)) F
      (𝓝 (lin t w - ℓ w * coef t w)) :=
    (hev (lin t)).sub ((hev ℓ).mul (hev (coef t)))
  refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
  filter_upwards [(hequation t).filter_mono hle] with i hi
  exact hi.symm

end PDE.Analysis.Variational
