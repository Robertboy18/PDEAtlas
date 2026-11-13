/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.InteriorWeakForm
import PDE.DistributionTheory.TestFunction

/-!
# Initial-boundary weak forms for one-dimensional conservation laws

We give the weak formulation, for an arbitrary state space, of

`u_t + (f(u))_x = 0,    u(0, x) = u₀(x)`

on the forward half-space. For a real Banach state space `E`, the equation is
the Bochner identity

`∫_{t > 0} (φ_t • u + φ_x • f(u)) + ∫ φ(0, x) • u₀(x) = 0`.

This single coordinate-free formulation specializes to scalar laws and to
finite-dimensional systems. In a Euclidean state space, evaluating the
Bochner identity in each coordinate is equivalent to the usual formulation
with vector-valued tests and Euclidean pairings.

The spacetime integrability field is not redundant: local integrability on the open
half-space does not control behavior as `t ↓ 0`.

In a Euclidean state space this is the identity (13) of Evans, §11.1.1, with the same signs;
Evans uses it to define integral solutions of systems. For a scalar law it is the identity (4)
of Evans, §3.4.1(a), which defines integral solutions there.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.1(a), equations (2)-(4) and the definition of
  integral solution; §11.1.1, equations (12)-(13) and the definition of integral solution.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw

/-- The open forward half-space `t > 0`. -/
def forwardHalfSpace : Opens ℝ^2 where
  carrier := {p | 0 < p 0}
  is_open' := by
    let time : ℝ^2 →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 2)
    change IsOpen (time ⁻¹' Ioi 0)
    exact isOpen_Ioi.preimage time.continuous

/-- A compactly supported `C¹` scalar test that may meet the initial
hyperplane `t = 0`. -/
abbrev InitialValueTestFunction :=
  𝓓^{1}((⊤ : Opens ℝ^2), ℝ)

/-- The initial-time slice of an admissible test has compact support on the
spatial line. -/
theorem InitialValueTestFunction.hasCompactSupport_initialSlice (φ : InitialValueTestFunction) :
    HasCompactSupport (fun x : ℝ ↦ φ !₂[0, x]) := by
  let K : Set ℝ := (fun p : ℝ^2 ↦ p 1) '' tsupport (φ : ℝ^2 → ℝ)
  have hK : IsCompact K := φ.hasCompactSupport.isCompact.image
      (EuclideanSpace.proj (1 : Fin 2)).continuous
  refine HasCompactSupport.intro hK ?_
  intro x hx
  by_contra hne
  have hsupport : (!₂[0, x] : ℝ^2) ∈ Function.support
        (φ : ℝ^2 → ℝ) := by
    simpa [Function.support] using hne
  exact hx ⟨!₂[0, x], subset_closure hsupport, by simp⟩

/-- All time slices of a compact spacetime test have support in a common spatial interval. -/
theorem InitialValueTestFunction.exists_spatial_support_interval (φ : InitialValueTestFunction) :
    ∃ R : ℝ, ∀ t x : ℝ, x ∉ Icc (-R) R → φ !₂[t, x] = 0 := by
  have hcompact : IsCompact ((fun p : ℝ^2 ↦ p 1) '' tsupport (φ : ℝ^2 → ℝ)) :=
    φ.hasCompactSupport.isCompact.image (EuclideanSpace.proj (1 : Fin 2)).continuous
  obtain ⟨R, hR⟩ := hcompact.isBounded.subset_closedBall (0 : ℝ)
  rw [Real.closedBall_zero_eq_Icc] at hR
  refine ⟨R, fun t x hx ↦ ?_⟩
  exact image_eq_zero_of_notMem_tsupport fun hp ↦ hx (hR ⟨!₂[t, x], hp, by simp⟩)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The direct initial-boundary weak formulation for a one-dimensional
conservation law with values in a real Banach space.

Scalar tests are used with an `E`-valued Bochner identity. This is the
coordinate-free distribution equation and avoids duplicating scalar and
finite-dimensional system structures. Completeness prevents the Bochner
integrals from degenerating to zero for an incomplete target space.
-/
structure IsWeakInitialValueSolution [CompleteSpace E]
    (flux : E → E) (u₀ : ℝ → E) (u : ℝ^2 → E) : Prop where
  /-- Local integrability of the conserved state for positive time. -/
  u_locallyIntegrable :
    LocallyIntegrableOn u forwardHalfSpace volume
  /-- Local integrability of the flux for positive time. -/
  flux_locallyIntegrable :
    LocallyIntegrableOn
      (fun p : ℝ^2 ↦ flux (u p)) forwardHalfSpace volume
  /-- Local integrability of the prescribed initial state. -/
  initial_locallyIntegrable :
    LocallyIntegrable u₀ volume
  /-- Integrability of the spacetime term up to the initial boundary. -/
  spacetime_integrable :
    ∀ φ : InitialValueTestFunction,
      IntegrableOn
        (InteriorWeakForm.integrand u (fun p ↦ flux (u p)) φ)
        forwardHalfSpace volume
  /-- The weak identity, including the initial-boundary contribution. -/
  weak_initial_eq :
    ∀ φ : InitialValueTestFunction,
      (∫ p : ℝ^2 in forwardHalfSpace,
          InteriorWeakForm.integrand u (fun q ↦ flux (u q)) φ p ∂volume) +
        ∫ x : ℝ, φ !₂[0, x] • u₀ x ∂volume = 0

variable [CompleteSpace E]

/-- The initial-boundary term in the direct weak identity is integrable. -/
theorem IsWeakInitialValueSolution.integrable_initialBoundary {flux : E → E} {u₀ : ℝ → E}
    {u : ℝ^2 → E} (hu : IsWeakInitialValueSolution flux u₀ u) (φ : InitialValueTestFunction) :
    Integrable (fun x : ℝ ↦ φ !₂[0, x] • u₀ x) volume :=
  hu.initial_locallyIntegrable.integrable_smul_left_of_hasCompactSupport
    (φ.contDiff.continuous.comp (by fun_prop)) φ.hasCompactSupport_initialSlice

/-- Forgetting the initial-boundary term gives the interior weak identity on
the open half-space.

An interior test is included into the whole-spacetime test space. Its initial
slice vanishes because its support is contained in `t > 0`, and its
derivatives vanish off that open set, so the restricted spacetime integral is
the ordinary interior integral.
-/
theorem IsWeakInitialValueSolution.interior_identity {flux : E → E} {u₀ : ℝ → E} {u : ℝ^2 → E}
    (hu : IsWeakInitialValueSolution flux u₀ u) (φ : 𝓓^{1}(forwardHalfSpace, ℝ)) :
    ∫ p : ℝ^2, InteriorWeakForm.integrand u (fun q ↦ flux (u q)) φ p ∂volume = 0 := by
  let φGlobal : InitialValueTestFunction := TestFunction.monoCLM ℝ φ
  have hφGlobal :
      (φGlobal : ℝ^2 → ℝ) = (φ : ℝ^2 → ℝ) := by
    simp [φGlobal]
  have hintegrand : InteriorWeakForm.integrand u (fun q ↦ flux (u q)) φGlobal =
        InteriorWeakForm.integrand u (fun q ↦ flux (u q)) φ := by
    funext p
    change (∂[(0 : Fin 2)] (φGlobal : ℝ^2 → ℝ)) p • u p +
          (∂[(1 : Fin 2)] (φGlobal : ℝ^2 → ℝ)) p • flux (u p) =
        (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) p • u p + (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) p • flux (u p)
    rw [hφGlobal]
  have hboundary :
      (∫ x : ℝ, φGlobal !₂[0, x] • u₀ x ∂volume) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards with x
    have hnot : (!₂[0, x] : ℝ^2) ∉ forwardHalfSpace := by
      simp [forwardHalfSpace]
    have hzero : φ !₂[0, x] = 0 := φ.zero_on_compl hnot
    rw [show φGlobal !₂[0, x] = φ !₂[0, x] from congrFun hφGlobal !₂[0, x]]
    simp [hzero]
  have hrestrict : (∫ p : ℝ^2 in forwardHalfSpace,
          InteriorWeakForm.integrand u (fun q ↦ flux (u q)) φ p ∂volume) = ∫ p : ℝ^2,
          InteriorWeakForm.integrand u (fun q ↦ flux (u q)) φ p ∂volume := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp ↦ ?_
    have htime := φ.partialDeriv_eq_zero_of_notMem hp (0 : Fin 2)
    have hspace := φ.partialDeriv_eq_zero_of_notMem hp (1 : Fin 2)
    simp [InteriorWeakForm.integrand, htime, hspace]
  have hdirect := hu.weak_initial_eq φGlobal
  rwa [hintegrand, hrestrict, hboundary, add_zero] at hdirect

end PDE.Hyperbolic.ConservationLaw
