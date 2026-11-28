/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.ExtremalFamily.BoundaryPrimitive
public import PDE.CalculusOfVariations.ExtremalFamily.Density
public import PDE.CalculusOfVariations.ExtremalFamily.Divergence
public import PDE.Spaces.Sobolev.Boundary.Flux.GaussGreen.Closure
import PDE.Analysis.Calculus.Divergence.Locality

/-!
# Energy comparison along a family of extremals

## Motivation

A one-parameter family `U t` of solutions of the Euler–Lagrange system covers a region, and a
competitor is a graph `w(x) = U (θ x) x` chosen from the family by a parameter `θ`. Which
integral over the graph depends on the boundary values of `θ` only? How do the actions of `w`
and of the member `U 0` compare when `θ` vanishes on the boundary?

## The idea

Integrating the family flux to the selected parameter gives a calibration flux. Its divergence
is the difference of the family densities plus the endpoint pairing
(`divergence_extremalFamilyPrimitive`). On the boundary the flux at a point depends on the
value of `θ` at that point only. So by Gauss–Green the integral of the density of the member
through each point plus the endpoint pairing is the same for two parameters that agree on the
boundary. For a parameter that vanishes on the boundary it is the action of `U 0`. The density
of the graph exceeds that integrand by Weierstrass's excess `graphExcess`, so the difference
of the two actions is the integral of the excess. Convexity in the gradient makes the excess
nonnegative, which gives the energy comparison of Evans, §8.2.5, Theorem 10. The target may
have any finite dimension; Evans treats scalar functions.

## Main results

All are for every family of extremals in the sense of `IsExtremalFamily` (continuous closure
jets of the density and the family, a bounded open set with `C¹` graph boundary, any number of
unknowns) and every parameter in the sense of `IsGraphParameter` (`C¹`, with values in the
parameter interval).

* `integrableOn_invariant_parameter_graph`: the density of the member through each point plus
  the endpoint pairing is integrable.
* `integral_invariant_eq_of_eqOn_frontier`: the integral of this function has the same value
  for two parameters that agree on the boundary.
* `integral_invariant_parameter_graph`: for a parameter that vanishes on the boundary this
  integral is the action of `U 0`.
* `lagrangianAction_parameter_graph_sub_eq_integral_graphExcess`: for such a parameter the
  action of the graph minus the action of `U 0` is the integral of the excess. No convexity is
  assumed.
* `lagrangianAction_le_parameter_graph_of_graphExcess_nonneg`: if the excess is nonnegative on
  `Ω`, `U 0` has no larger action than the graph.
* `lagrangianAction_le_parameter_graph_of_closureJets`: for a density that is convex in the
  gradient, `U 0` has the least action among the graphs of the parameters that vanish on the
  boundary.

## Relations

* The third result is the second for `θ` and the parameter `0`. The fifth is the fourth with a
  nonnegative integrand, and the sixth is the fifth with `graphExcess_nonneg`.
* `divergence_extremalFamilyPrimitive` is `divergence_parameterPrimitive_of_hasDerivAt` for
  the family flux, with `hasDerivAt_fieldDensity_divergence_familyFlux`.
* `exists_calibration_parameter_graph` holds the common part of the proofs.
* `PDE.Examples.PlaneFamily.isExtremalFamily_plane` and
  `PDE.Examples.PlaneFamily.isGraphParameter_bump` are instances of the two structures.

## What stays open

Competitors that are not parameter graphs of the family, and the description of the field by
slope functions of the point instead of a family. The family is not assumed to cover a region
simply. For more than one unknown the parameter graphs of a family with one parameter are a
thin class: the matrix of derivatives of the graph differs from that of the member through the
point by a matrix of rank at most one (`jacobianMatrix_parameter_graph`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.5, Theorem 10.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Matrix.Norms.Elementwise Topology Interval

namespace PDE.CalculusOfVariations.ExtremalFamily

open Analysis Noether SobolevSpace

variable {n m : ℕ}
  {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ}
  {U : ℝ → ℝ^n → ℝ^m} {θ : ℝ^n → ℝ} {J : Set ℝ} {x : ℝ^n}

/-- Integrating the velocity-momentum flux along an extremal family produces the
exact density difference and the moving-endpoint term. -/
theorem divergence_extremalFamilyPrimitive
    (hJ : IsOpen J) (hJc : OrdConnected J) (h0 : 0 ∈ J) (hθJ : θ x ∈ J)
    (hL : ∀ t ∈ J, ContDiffAt ℝ 2
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix (U t) x, (U t x, x)))
    (hU : ∀ t ∈ J, ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (t, x))
    (hθ : DifferentiableAt ℝ θ x)
    (hEL : ∀ t ∈ J, ∀ k, classicalEulerLagrange L (U t) x k = 0) :
    ∇· (parameterPrimitive (fun p : ℝ^n × ℝ ↦ familyFlux L U p.2 p.1) θ) x =
      fderiv ℝ θ x (familyFlux L U (θ x) x) +
        (fieldDensity L (U (θ x)) x - fieldDensity L (U 0) x) := by
  have hH (t : ℝ) (ht : t ∈ J) :
      ContDiffAt ℝ 1 (fun p : ℝ^n × ℝ ↦ familyFlux L U p.2 p.1) (x, t) :=
    (contDiffAt_familyFlux (hL t ht) (hU t ht)).comp (x, t) (f := Prod.swap)
      (contDiffAt_snd.prodMk contDiffAt_fst)
  exact divergence_parameterPrimitive_of_hasDerivAt hJ hJc h0 hθJ hH hθ
    (c := fun t ↦ fieldDensity L (U t) x)
    (fun t ht ↦ hasDerivAt_fieldDensity_divergence_familyFlux (hL t ht) (hU t ht) (hEL t ht))

section Calibration

variable {d : ℕ} {Ω : Set (ℝ^(d + 1))}
  {L : Matrix (Fin m) (Fin (d + 1)) ℝ → ℝ^m → ℝ^(d + 1) → ℝ}
  {U : ℝ → ℝ^(d + 1) → ℝ^m} {θ θ' : ℝ^(d + 1) → ℝ}

/-- A family of extremals with the regularity that the comparison theorems use: `Ω` is a
bounded open set with `C¹` graph boundary, the parameter set `J` is an open interval that
contains `0`, the density and the family have continuous closure jets of second order, and
every member `U t` solves the Euler–Lagrange system in `Ω`. -/
structure IsExtremalFamily (Ω : Set (ℝ^(d + 1))) (J : Set ℝ)
    (L : Matrix (Fin m) (Fin (d + 1)) ℝ → ℝ^m → ℝ^(d + 1) → ℝ)
    (U : ℝ → ℝ^(d + 1) → ℝ^m) : Prop where
  /-- The domain is open. -/
  isOpen : IsOpen Ω
  /-- The domain is bounded. -/
  isBounded : Bornology.IsBounded Ω
  /-- The boundary of the domain is a `C¹` graph locally. -/
  graphBoundary : Boundary.HasC1GraphBoundary Ω
  /-- The parameter set is open. -/
  isOpen_parameter : IsOpen J
  /-- The parameter set is an interval. -/
  ordConnected : OrdConnected J
  /-- The parameter `0` belongs to the family. -/
  zero_mem : 0 ∈ J
  /-- The density has continuous closure jets of second order. -/
  density : Nonempty (ContinuousSecondJetOn
    (fun a : Matrix (Fin m) (Fin (d + 1)) ℝ × (ℝ^m × ℝ^(d + 1)) ↦
      L a.1 a.2.1 a.2.2) {a | a.2.2 ∈ Ω})
  /-- The family has continuous closure jets of second order in the point and the parameter. -/
  family : Nonempty (ContinuousSecondJetOn (fun p : ℝ^(d + 1) × ℝ ↦ U p.2 p.1) (Ω ×ˢ J))
  /-- Every member of the family solves the Euler–Lagrange system. -/
  eulerLagrange : ∀ t ∈ J, ∀ x ∈ Ω, ∀ k, classicalEulerLagrange L (U t) x k = 0

/-- The parameter of a graph `x ↦ U (θ x) x` chosen from a family: `θ` is `C¹` and takes
values in the parameter set on the closure of `Ω`. Two parameters that agree on the boundary
give graphs with the same boundary values, and a parameter that vanishes on the boundary
gives a graph with the boundary values of `U 0`. -/
structure IsGraphParameter (Ω : Set (ℝ^(d + 1))) (J : Set ℝ) (θ : ℝ^(d + 1) → ℝ) : Prop where
  /-- The parameter is continuously differentiable. -/
  contDiff : ContDiff ℝ 1 θ
  /-- The parameter takes values in the parameter set. -/
  mapsTo : MapsTo θ (closure Ω) J

/-- The constant `0` is a parameter. Its graph is the member `U 0`. -/
theorem IsExtremalFamily.isGraphParameter_zero (hfam : IsExtremalFamily Ω J L U) :
    IsGraphParameter Ω J fun _ ↦ 0 :=
  ⟨contDiff_const, fun _ _ ↦ hfam.zero_mem⟩

/-- The calibration of a family of extremals. Every parameter `θ` has a vector field `B θ`,
the primitive of the family flux from `0` to `θ x`, with these properties. Its divergence is
integrable on `Ω`, and at every point of `Ω` it is the endpoint pairing of the family flux
plus the difference of the densities of `U (θ x)` and `U 0`. The density of the parameter
graph is integrable, and it is the density of `U (θ x)` plus the endpoint pairing plus the
excess. For two parameters that agree on the boundary the two divergences have the same
integral: by Gauss–Green each integral is the flux through the boundary, and the two fields
agree there. -/
theorem exists_calibration_parameter_graph (hfam : IsExtremalFamily Ω J L U) :
    ∃ B : (ℝ^(d + 1) → ℝ) → ℝ^(d + 1) → ℝ^(d + 1),
      (∀ θ, IsGraphParameter Ω J θ →
        IntegrableOn (∇· (B θ)) Ω ∧
        IntegrableOn (fieldDensity L (fun x ↦ U (θ x) x)) Ω ∧
        (∀ x ∈ Ω, ∇· (B θ) x = fderiv ℝ θ x (familyFlux L U (θ x) x) +
          (fieldDensity L (U (θ x)) x - fieldDensity L (U 0) x)) ∧
        ∀ x ∈ Ω, fieldDensity L (fun y ↦ U (θ y) y) x =
          fieldDensity L (U (θ x)) x + fderiv ℝ θ x (familyFlux L U (θ x) x) +
            graphExcess L U θ x) ∧
      ∀ θ θ', IsGraphParameter Ω J θ → IsGraphParameter Ω J θ' → EqOn θ θ' (frontier Ω) →
        (∫ x in Ω, ∇· (B θ) x) = ∫ x in Ω, ∇· (B θ') x := by
  obtain ⟨hopen, hbounded, hgraph, hJ, hJc, h0, ⟨hL⟩, ⟨hU⟩, hEL⟩ := hfam
  obtain ⟨H, D, hHc, hDc, hH, hHeq, hDeq⟩ :=
    exists_familyFlux_coordinate_extensions hopen hJ hL hU
  let B (θ : ℝ^(d + 1) → ℝ) (x : ℝ^(d + 1)) : ℝ^(d + 1) :=
    WithLp.toLp 2 (fun j ↦ parameterPrimitive (H j) θ x)
  have hBup (θ : ℝ^(d + 1) → ℝ) (hpar : IsGraphParameter Ω J θ) (j : Fin (d + 1)) :
      ContDiffUpToBoundary 1 (fun x ↦ B θ x j) Ω :=
    contDiffUpToBoundary_parameterPrimitive hbounded hJ hJc h0 (hH j) (hHc j)
      (fun i ↦ hDc i j) (fun i ↦ hDeq i j) hpar.contDiff hpar.mapsTo
  have hBc (θ : ℝ^(d + 1) → ℝ) (hpar : IsGraphParameter Ω J θ) :
      ContinuousOn (B θ) (closure Ω) :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) ↦ ℝ)).symm.continuous).comp_continuousOn
      (continuousOn_pi.mpr fun j ↦
        continuousOn_parameterPrimitive hJc h0 (hHc j) hpar.contDiff.continuous.continuousOn
          hpar.mapsTo)
  have hLi (P) (z) (x : ℝ^(d + 1)) (hx : x ∈ Ω) : ContDiffAt ℝ 2
      (fun a : Matrix (Fin m) (Fin (d + 1)) ℝ × (ℝ^m × ℝ^(d + 1)) ↦
        L a.1 a.2.1 a.2.2) (P, (z, x)) :=
    hL.contDiffOn.contDiffAt ((hopen.preimage (continuous_snd.comp continuous_snd)).mem_nhds hx)
  have hUi (t : ℝ) (ht : t ∈ J) (x : ℝ^(d + 1)) (hx : x ∈ Ω) :
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ^(d + 1) ↦ U p.1 p.2) (t, x) :=
    (hU.contDiffOn.contDiffAt ((hopen.prod hJ).mem_nhds ⟨hx, ht⟩)).comp (t, x)
      (f := Prod.swap) (contDiffAt_snd.prodMk contDiffAt_fst)
  have heq (θ : ℝ^(d + 1) → ℝ) (hpar : IsGraphParameter Ω J θ) : EqOn (B θ)
      (parameterPrimitive (fun p : ℝ^(d + 1) × ℝ ↦ familyFlux L U p.2 p.1) θ) Ω := by
    intro x hx
    have hi : IntervalIntegrable (fun t ↦ familyFlux L U t x) volume 0 (θ x) := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      exact (contDiffAt_familyFlux (hLi _ _ x hx)
        (hUi t (hJc.uIcc_subset h0 (hpar.mapsTo (subset_closure hx)) ht) x hx)).continuousAt.comp
          (f := fun s : ℝ ↦ (s, x)) (continuousAt_id.prodMk continuousAt_const)
          |>.continuousWithinAt
    ext j
    change (∫ t in 0..θ x, H j (x, t)) =
      (EuclideanSpace.proj j) (∫ t in 0..θ x, familyFlux L U t x)
    rw [← (EuclideanSpace.proj j).intervalIntegral_comp_comm hi]
    apply intervalIntegral.integral_congr
    intro t ht
    exact hHeq j x hx t (hJc.uIcc_subset h0 (hpar.mapsTo (subset_closure hx)) ht)
  let := hgraph.c1ExtensionAtlas hopen hbounded
  have hGG (θ : ℝ^(d + 1) → ℝ) (hpar : IsGraphParameter Ω J θ) :=
    Boundary.Flux.gaussGreen_of_raw_graph hopen hbounded hgraph (hBup θ hpar) (hBc θ hpar)
  refine ⟨B, fun θ hpar ↦ ⟨(hGG θ hpar).1, ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩,
    fun θ θ' hpar hpar' hfr ↦ ?_⟩
  · exact integrableOn_fieldDensity_parameter_graph hopen hbounded hJ hL hU hpar.contDiff
      hpar.mapsTo
  · rw [((heq θ hpar).eventuallyEq_of_mem (hopen.mem_nhds hx)).divergence_eq]
    exact divergence_extremalFamilyPrimitive hJ hJc h0 (hpar.mapsTo (subset_closure hx))
      (fun _ _ ↦ hLi _ _ x hx) (fun t ht ↦ hUi t ht x hx)
      (hpar.contDiff.differentiable (by norm_num) x) (fun t ht ↦ hEL t ht x hx)
  · exact fieldDensity_parameter_graph_eq
      ((hLi _ _ x hx).differentiableAt (by norm_num))
      ((hUi (θ x) (hpar.mapsTo (subset_closure hx)) x hx).differentiableAt (by norm_num))
      (hpar.contDiff.differentiable (by norm_num) x)
  · -- by Gauss–Green both integrals are the flux through the boundary, where the fields agree
    rw [(hGG θ hpar).2.2, (hGG θ' hpar').2.2]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
    have hB : B θ x = B θ' x := by
      simp only [B, parameterPrimitive, hfr hx]
    rw [Trace.C1.normalFlux_eq_inner (B θ) hx, Trace.C1.normalFlux_eq_inner (B θ') hx, hB]

/-- The invariant integrand of a family of extremals is integrable. For every parameter `θ`,
the density of the member `U (θ x)` through each point plus the pairing of the family flux
with the differential of `θ` is integrable on `Ω`: there it is the density of `U 0` plus the
divergence of the calibration field. -/
theorem integrableOn_invariant_parameter_graph
    (hfam : IsExtremalFamily Ω J L U) (hpar : IsGraphParameter Ω J θ) :
    IntegrableOn
      (fun x ↦ fieldDensity L (U (θ x)) x + fderiv ℝ θ x (familyFlux L U (θ x) x)) Ω := by
  obtain ⟨B, hB, -⟩ := exists_calibration_parameter_graph hfam
  obtain ⟨hBi, -, hdiv, -⟩ := hB θ hpar
  have hui : IntegrableOn (fieldDensity L (U 0)) Ω := (hB _ hfam.isGraphParameter_zero).2.1
  have hsum : IntegrableOn (fun x ↦ fieldDensity L (U 0) x + ∇· (B θ) x) Ω := hui.add hBi
  have heq : (fun x ↦ fieldDensity L (U 0) x + ∇· (B θ) x) =ᵐ[volume.restrict Ω] fun x ↦
      fieldDensity L (U (θ x)) x + fderiv ℝ θ x (familyFlux L U (θ x) x) := by
    filter_upwards [ae_restrict_mem hfam.isOpen.measurableSet] with x hx
    rw [hdiv x hx]
    ring
  exact hsum.congr heq

/-- **The invariant integral depends on the boundary values of the parameter only.** For two
parameters `θ` and `θ'` that agree on the boundary of `Ω`, the integral over `Ω` of the density
of the member through each point plus the pairing of the family flux with the differential of
the parameter has the same value. So this integral does not change when the parameter is
varied with its boundary values fixed. Two graphs with the same boundary values whose
parameters differ on the boundary are not compared. No convexity is assumed. Both integrands
are integrable (`integrableOn_invariant_parameter_graph`).

On `Ω` the integrand is the density of `U 0` plus the divergence of the calibration field, and
the integral of the divergence depends on the boundary values of the parameter only. -/
theorem integral_invariant_eq_of_eqOn_frontier
    (hfam : IsExtremalFamily Ω J L U) (hpar : IsGraphParameter Ω J θ)
    (hpar' : IsGraphParameter Ω J θ') (hfr : EqOn θ θ' (frontier Ω)) :
    (∫ x in Ω, (fieldDensity L (U (θ x)) x + fderiv ℝ θ x (familyFlux L U (θ x) x))) =
      ∫ x in Ω, (fieldDensity L (U (θ' x)) x + fderiv ℝ θ' x (familyFlux L U (θ' x) x)) := by
  obtain ⟨B, hB, hBfr⟩ := exists_calibration_parameter_graph hfam
  have hui : IntegrableOn (fieldDensity L (U 0)) Ω := (hB _ hfam.isGraphParameter_zero).2.1
  -- for each parameter the integral is the action of `U 0` plus the integral of `∇· B`
  have key (η : ℝ^(d + 1) → ℝ) (hη : IsGraphParameter Ω J η) :
      (∫ x in Ω, (fieldDensity L (U (η x)) x + fderiv ℝ η x (familyFlux L U (η x) x))) =
        (∫ x in Ω, fieldDensity L (U 0) x) + ∫ x in Ω, ∇· (B η) x := by
    obtain ⟨hBi, -, hdiv, -⟩ := hB η hη
    have heq : ∀ᵐ x ∂volume.restrict Ω,
        fieldDensity L (U (η x)) x + fderiv ℝ η x (familyFlux L U (η x) x) =
          fieldDensity L (U 0) x + ∇· (B η) x := by
      filter_upwards [ae_restrict_mem hfam.isOpen.measurableSet] with x hx
      rw [hdiv x hx]
      ring
    rw [integral_congr_ae heq, integral_add hui hBi]
  rw [key θ hpar, key θ' hpar', hBfr θ θ' hpar hpar' hfr]

/-- The invariant integral of a family of extremals. For every parameter `θ` that vanishes on
the boundary, the integral over `Ω` of the density of the member `U (θ x)` through each point
plus the pairing of the family flux with the differential of `θ` is the action of `U 0`. No
convexity is assumed. This is `integral_invariant_eq_of_eqOn_frontier` for `θ` and the
parameter `0`. -/
theorem integral_invariant_parameter_graph
    (hfam : IsExtremalFamily Ω J L U) (hpar : IsGraphParameter Ω J θ)
    (hzero : ∀ x ∈ frontier Ω, θ x = 0) :
    (∫ x in Ω, (fieldDensity L (U (θ x)) x + fderiv ℝ θ x (familyFlux L U (θ x) x))) =
      lagrangianAction Ω L (U 0) := by
  rw [integral_invariant_eq_of_eqOn_frontier hfam hpar hfam.isGraphParameter_zero hzero]
  change _ = ∫ x in Ω, fieldDensity L (U 0) x
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp

/-- **Weierstrass's formula for a family of extremals.** For a parameter that vanishes on the
boundary, the action of the parameter graph minus the action of `U 0` is the integral of the
excess of the graph over the field of the family, and the excess is integrable. No convexity
is assumed.

The invariant integrand differs from the density of the graph by the excess, and its integral
is the action of `U 0`. -/
theorem lagrangianAction_parameter_graph_sub_eq_integral_graphExcess
    (hfam : IsExtremalFamily Ω J L U) (hpar : IsGraphParameter Ω J θ)
    (hzero : ∀ x ∈ frontier Ω, θ x = 0) :
    IntegrableOn (graphExcess L U θ) Ω ∧
      lagrangianAction Ω L (fun x ↦ U (θ x) x) - lagrangianAction Ω L (U 0) =
        ∫ x in Ω, graphExcess L U θ x := by
  obtain ⟨B, hB, -⟩ := exists_calibration_parameter_graph hfam
  obtain ⟨-, hwi, -, hgraphEq⟩ := hB θ hpar
  have hinv := integrableOn_invariant_parameter_graph hfam hpar
  -- on `Ω` the excess is the density of the graph minus the invariant integrand
  have heq : graphExcess L U θ =ᵐ[volume.restrict Ω] fun x ↦
      fieldDensity L (fun y ↦ U (θ y) y) x -
        (fieldDensity L (U (θ x)) x + fderiv ℝ θ x (familyFlux L U (θ x) x)) := by
    filter_upwards [ae_restrict_mem hfam.isOpen.measurableSet] with x hx
    have h1 := hgraphEq x hx
    linarith
  have hint : IntegrableOn (fun x ↦ fieldDensity L (fun y ↦ U (θ y) y) x -
      (fieldDensity L (U (θ x)) x + fderiv ℝ θ x (familyFlux L U (θ x) x))) Ω :=
    hwi.sub hinv
  refine ⟨hint.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_sub hwi hinv,
    integral_invariant_parameter_graph hfam hpar hzero]
  rfl

/-- **A nonnegative excess gives a minimum.** For a parameter that vanishes on the boundary,
if the excess of the parameter graph over the field of the family is nonnegative on `Ω`, the
member `U 0` has no larger action than the graph. This is
`lagrangianAction_parameter_graph_sub_eq_integral_graphExcess` with a nonnegative integrand. -/
theorem lagrangianAction_le_parameter_graph_of_graphExcess_nonneg
    (hfam : IsExtremalFamily Ω J L U) (hpar : IsGraphParameter Ω J θ)
    (hzero : ∀ x ∈ frontier Ω, θ x = 0) (hE : ∀ x ∈ Ω, 0 ≤ graphExcess L U θ x) :
    lagrangianAction Ω L (U 0) ≤ lagrangianAction Ω L (fun x ↦ U (θ x) x) := by
  have h := (lagrangianAction_parameter_graph_sub_eq_integral_graphExcess hfam hpar hzero).2
  have hnonneg : 0 ≤ ∫ x in Ω, graphExcess L U θ x :=
    setIntegral_nonneg hfam.isOpen.measurableSet hE
  linarith

/-- A family of Euler–Lagrange solutions minimizes the action against parameter
 graphs with zero boundary parameter. Closure jets suffice; no derivative of the
 exterior values is required. Convexity is only in the gradient matrix. This is
 `lagrangianAction_le_parameter_graph_of_graphExcess_nonneg` with `graphExcess_nonneg`. -/
theorem lagrangianAction_le_parameter_graph_of_closureJets
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hJ : IsOpen J) (hJc : OrdConnected J) (h0 : 0 ∈ J)
    (hL : ContinuousSecondJetOn
      (fun a : Matrix (Fin m) (Fin (d + 1)) ℝ × (ℝ^m × ℝ^(d + 1)) ↦
        L a.1 a.2.1 a.2.2) {a | a.2.2 ∈ Ω})
    (hU : ContinuousSecondJetOn (fun p : ℝ^(d + 1) × ℝ ↦ U p.2 p.1) (Ω ×ˢ J))
    (hθ : ContDiff ℝ 1 θ) (hθJ : MapsTo θ (closure Ω) J)
    (hboundary : ∀ x ∈ frontier Ω, θ x = 0)
    (hEL : ∀ t ∈ J, ∀ x ∈ Ω, ∀ k, classicalEulerLagrange L (U t) x k = 0)
    (hconvex : ∀ x ∈ Ω, ∀ z, ConvexOn ℝ univ (fun P ↦ L P z x)) :
    lagrangianAction Ω L (U 0) ≤ lagrangianAction Ω L (fun x ↦ U (θ x) x) :=
  lagrangianAction_le_parameter_graph_of_graphExcess_nonneg
    (⟨hopen, hbounded, hgraph, hJ, hJc, h0, ⟨hL⟩, ⟨hU⟩, hEL⟩ : IsExtremalFamily Ω J L U)
    ⟨hθ, hθJ⟩ hboundary fun x hx ↦ graphExcess_nonneg
      ((hL.contDiffOn.contDiffAt ((hopen.preimage
        (continuous_snd.comp continuous_snd)).mem_nhds hx)).differentiableAt (by norm_num))
      (hconvex x hx (U (θ x) x))

end Calibration

end PDE.CalculusOfVariations.ExtremalFamily
