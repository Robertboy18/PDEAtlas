/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.Representative
public import PDE.Spaces.Sobolev.Calculus.IsolatedPoint.Membership

/-!
# Divergence-free `H¹` fields from fields that are smooth away from the origin

A vector field on `ℝⁿ⁺¹`, `n ≥ 1`, that is `C¹` except at the origin, whose components and
classical partial derivatives are square integrable, and whose classical divergence vanishes
away from the origin, is a divergence-free element of `H¹(ℝⁿ⁺¹)ⁿ⁺¹`. Its representative is the
field, and the representative of its gradient is the matrix of classical partial derivatives. In
the regularity argument for a self-similar profile, the difference of the profile and its far
field is a field of this kind.

## Main results

* `NavierStokes.Stationary.exists_solenoidal_H1_of_contDiffOn` (all fields on `ℝⁿ⁺¹`, `n ≥ 1`,
  that are `C¹` off the origin, with square-integrable components and partial derivatives and
  with classical divergence zero off the origin): there is `w ∈ H¹(ℝⁿ⁺¹)ⁿ⁺¹` with
  `divergenceCLM w = 0`, representative the field, and gradient representative its classical
  partial derivatives.

## How it works

A point is removable for `H¹` in dimension at least two, so each component is an element of
`H¹` whose weak derivatives are its classical partial derivatives
(`SobolevSpace.exists_wkpSpace_of_contDiffAt_off_zero`). The weak divergence is then the
classical divergence almost everywhere, which is zero.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 2.1, proof of
  Proposition 3: `Ū - U_far ∈ H¹`. <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Stationary

variable {n : ℕ}

/-- A field on `ℝⁿ⁺¹`, `n ≥ 1`, that is `C¹` away from the origin, whose components and their
classical partial derivatives are square integrable, and whose classical divergence vanishes
away from the origin, is a divergence-free element of `H¹(ℝⁿ⁺¹)ⁿ⁺¹`: its representative is the
field and its gradient representative is the matrix of classical partial derivatives. -/
theorem exists_solenoidal_H1_of_contDiffOn [NeZero n] {V : ℝ^(n + 1) → ℝ^(n + 1)}
    (hV : ContDiffOn ℝ 1 V {0}ᶜ) (hdiv : ∀ x, x ≠ 0 → PDE.divergence V x = 0)
    (hV2 : ∀ i, MemLp (fun x ↦ V x i) 2 volume)
    (hD2 : ∀ i j, MemLp (PDE.partialDeriv j fun x ↦ V x i) 2 volume) :
    ∃ w : PiLp 2 (fun _ : Fin (n + 1) ↦ H¹(ℝ^(n + 1))), divergenceCLM w = 0 ∧
      representative w =ᵐ[volume] V ∧
      ∀ i j, (fun x ↦ gradientRepresentative w x i j) =ᵐ[volume]
        PDE.partialDeriv j fun x ↦ V x i := by
  have hcomp : ∀ i, ∃ U : H¹(ℝ^(n + 1)), baseRepresentative U =ᵐ[volume] (fun x ↦ V x i) ∧
      ∀ j, (wkpCoordinateCLM (singleDerivIndex (n + 1) j) U : ℝ^(n + 1) → ℝ) =ᵐ[volume]
        PDE.partialDeriv j fun x ↦ V x i := fun i ↦
    exists_wkpSpace_of_contDiffAt_off_zero (p := 2)
      (fun x hx ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.comp x
        (hV.contDiffAt (isOpen_compl_singleton.mem_nhds hx)))
      (hV2 i) (hD2 i)
  choose U hbase hderiv using hcomp
  -- The weak divergence is the classical divergence almost everywhere.
  have hsum : (∑ j, wkpCoordinateCLM (singleDerivIndex (n + 1) j) (U j) :
      DerivLp (n + 1) 2 univ) = 0 := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
        (fun j ↦ wkpCoordinateCLM (singleDerivIndex (n + 1) j) (U j)),
      ae_restrict_of_ae (ae_all_iff.mpr fun j ↦ hderiv j j),
      ae_restrict_of_ae ((volume : Measure (ℝ^(n + 1))).ae_ne 0),
      Lp.coeFn_zero ℝ 2 (domainMeasure (n + 1) univ)] with x hs hc hx hz
    rw [hs, hz]
    simp only [hc]
    exact hdiv x hx
  refine ⟨WithLp.toLp 2 U, ?_, ?_, fun i j ↦ ?_⟩
  · rw [divergenceCLM_apply]
    exact hsum
  · filter_upwards [ae_all_iff.mpr hbase] with x hx
    ext i
    simp only [representative_apply, massCLM_apply]
    exact hx i
  · filter_upwards [hderiv i j] with x hx
    simp only [gradientRepresentative, gradientCLM_apply]
    exact hx

end NavierStokes.Stationary
