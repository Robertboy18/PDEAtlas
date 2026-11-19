/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.FirstVariation.EulerLagrange
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Classical Euler–Lagrange equations at a local minimum

For each compactly supported smooth variation `v`, it suffices that the action of
`u + t • v` have a local minimum at `t = 0`. The neighborhood may depend on `v`;
no comparison with distant competitors is required.

The first variation therefore vanishes. Testing one component at a time and applying
the fundamental lemma gives the Euler–Lagrange system almost everywhere. The fundamental
lemma is Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`. The density's
continuous second jet and the candidate's `C²` regularity make the residual continuous,
so the system holds at every interior point.

The density `L(P,z,x)` may couple all matrix and value coordinates. This is the classical
necessary condition of Evans, §8.1.4(a), where a smooth minimizer is shown to solve the
Euler–Lagrange system (16).
The candidate has ambient `C²` regularity, as required by the first-variation API;
the density needs only a continuous second jet up to the spatial boundary.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.1.4(a).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Matrix.Norms.Elementwise ContDiff

namespace PDE.CalculusOfVariations

open Analysis SobolevSpace

variable {n m : ℕ} {Ω : Set (ℝ^n)}
  {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ} {u v : ℝ^n → ℝ^m}

/-- A local minimum along one classical variation has zero integrated first variation.
No boundary condition is needed for this derivative identity. -/
theorem integral_lagrangian_firstVariation_eq_zero_of_isLocalMin
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hL : ContinuousSecondJetOn
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      {a | a.2.2 ∈ Ω})
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hmin : IsLocalMin
      (fun t : ℝ ↦ lagrangianAction Ω L (fun x ↦ u x + t • v x)) 0) :
    (∫ x in Ω, fderiv ℝ
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix u x, (u x, x)) (jacobianMatrix v x, (v x, 0))) = 0 := by
  simpa only [zero_smul, add_zero] using
    hmin.hasDerivAt_eq_zero (hasDerivAt_lagrangianAction hopen hbounded hL hu hv 0)

/-- The classical Euler–Lagrange residual is continuous in the domain.
Its regularity follows from the density and candidate, rather than being assumed. -/
theorem continuousOn_classicalEulerLagrange
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hL : ContinuousSecondJetOn
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      {a | a.2.2 ∈ Ω})
    (hu : ContDiff ℝ 2 u) (k : Fin m) :
    ContinuousOn (fun x ↦ classicalEulerLagrange L u x k) Ω := by
  apply ContinuousOn.add
  · apply ContinuousOn.neg
    apply continuousOn_finsetSum
    intro i _
    have hA := contDiffUpToBoundary_lagrangian_matrix_deriv hopen hbounded hL hu k i
    exact (hA.partialDeriv_of_succ hopen i).contDiffOn.continuousOn
  · have hB := contDiffUpToBoundary_lagrangian_value_deriv hopen hbounded hL hu k
    exact hB.contDiffOn.continuousOn

/-- At a local minimum along a zero-boundary variation, the integrated
Euler–Lagrange pairing vanishes. -/
theorem integral_classicalEulerLagrange_eq_zero_of_isLocalMin
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hL : ContinuousSecondJetOn
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      {a | a.2.2 ∈ Ω})
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hzero : ∀ x ∈ frontier Ω, v x = 0)
    (hmin : IsLocalMin
      (fun t : ℝ ↦ lagrangianAction Ω L (fun x ↦ u x + t • v x)) 0) :
    (∫ x in Ω, ∑ k, classicalEulerLagrange L u x k * v x k) = 0 := by
  rw [← integral_lagrangian_firstVariation_eq hopen hbounded hgraph hL hu hv hzero]
  exact integral_lagrangian_firstVariation_eq_zero_of_isLocalMin
    hopen hbounded hL hu hv hmin

/-- A classical local minimizer satisfies the coupled Euler–Lagrange system pointwise.
Only local minimality along smooth compactly supported variations is required. -/
theorem classicalEulerLagrange_eq_zero_of_isLocalMin
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hL : ContinuousSecondJetOn
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      {a | a.2.2 ∈ Ω})
    (hu : ContDiff ℝ 2 u)
    (hmin : ∀ v : ℝ^n → ℝ^m, ContDiff ℝ ∞ v → HasCompactSupport v →
      tsupport v ⊆ Ω → IsLocalMin
        (fun t : ℝ ↦ lagrangianAction Ω L (fun x ↦ u x + t • v x)) 0) :
    ∀ x ∈ Ω, ∀ k, classicalEulerLagrange L u x k = 0 := by
  intro x hx k
  have hc := continuousOn_classicalEulerLagrange hopen hbounded hL hu k
  have hae : ∀ᵐ y, y ∈ Ω → classicalEulerLagrange L u y k = 0 := by
    apply hopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hc.locallyIntegrableOn hopen.measurableSet)
    intro g hg hgK hgs
    let v (y : ℝ^n) : ℝ^m := g y • EuclideanSpace.single k 1
    have hv : ContDiff ℝ ∞ v := hg.smul contDiff_const
    have hvK : HasCompactSupport v := hgK.smul_right
    have hvs : tsupport v ⊆ Ω :=
      (tsupport_smul_subset_left g (fun _ ↦ EuclideanSpace.single k (1 : ℝ))).trans hgs
    have hvzero : ∀ y ∈ frontier Ω, v y = 0 := by
      intro y hy
      have hnot : y ∉ Ω := (hopen.frontier_eq ▸ hy).2
      have hgzero : g y = 0 := image_eq_zero_of_notMem_tsupport (fun hy ↦ hnot (hgs hy))
      simp only [v, hgzero, zero_smul]
    have hfirst := integral_classicalEulerLagrange_eq_zero_of_isLocalMin
      hopen hbounded hgraph hL hu (hv.of_le (by simp)) hvzero (hmin v hv hvK hvs)
    have hpair : (∫ y in Ω, g y * classicalEulerLagrange L u y k) = 0 := by
      simpa [v, PiLp.single_apply, mul_comm] using hfirst
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Ω) (fun y hy ↦ ?_)]
    · simpa only [smul_eq_mul] using hpair
    · have hgzero : g y = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hgs h))
      simp only [hgzero, zero_smul]
  exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hopen.measurableSet).mpr hae)
    hopen hc continuousOn_const hx

end PDE.CalculusOfVariations
