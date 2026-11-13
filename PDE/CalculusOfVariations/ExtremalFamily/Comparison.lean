/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtremalFamily.BoundaryPrimitive
public import PDE.CalculusOfVariations.ExtremalFamily.Density
public import PDE.CalculusOfVariations.ExtremalFamily.Divergence
public import PDE.Spaces.Sobolev.Boundary.Flux.GaussGreen.Closure
import PDE.Analysis.Calculus.Divergence.Locality

/-!
# Energy comparison along a family of extremals

Integrating the family flux to the selected parameter gives a calibration flux.
Its divergence is the difference of the family densities plus the endpoint pairing.
Gradient convexity bounds the competitor density from below by this divergence and
the original density. The flux vanishes on the boundary, so Gauss–Green gives the
energy comparison of Evans, §8.2.5, Theorem 10. The target may have any finite dimension;
Evans treats scalar functions.

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
  rw [divergence_parameterPrimitive hJ hJc h0 hθJ hH hθ]
  congr 1
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t ↦ fieldDensity L (U t) x) ?_ ?_
  · intro t ht
    exact hasDerivAt_fieldDensity_divergence_familyFlux
      (hL t (hJc.uIcc_subset h0 hθJ ht)) (hU t (hJc.uIcc_subset h0 hθJ ht))
      (hEL t (hJc.uIcc_subset h0 hθJ ht))
  · exact ((continuousOn_divergence_slices hH).mono
      (hJc.uIcc_subset h0 hθJ)).intervalIntegrable

/-- A family of Euler–Lagrange solutions minimizes the action against parameter
 graphs with zero boundary parameter. Closure jets suffice; no derivative of the
 exterior values is required. Convexity is only in the gradient matrix. -/
theorem lagrangianAction_le_parameter_graph_of_closureJets
    {d : ℕ} {Ω : Set (ℝ^(d + 1))}
    {L : Matrix (Fin m) (Fin (d + 1)) ℝ → ℝ^m → ℝ^(d + 1) → ℝ}
    {U : ℝ → ℝ^(d + 1) → ℝ^m} {θ : ℝ^(d + 1) → ℝ}
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
    lagrangianAction Ω L (U 0) ≤ lagrangianAction Ω L (fun x ↦ U (θ x) x) := by
  obtain ⟨H, D, hHc, hDc, hH, hHeq, hDeq⟩ :=
    exists_familyFlux_coordinate_extensions hopen hJ hL hU
  let B (x : ℝ^(d + 1)) : ℝ^(d + 1) :=
    WithLp.toLp 2 (fun j ↦ parameterPrimitive (H j) θ x)
  have hBup (j : Fin (d + 1)) : ContDiffUpToBoundary 1 (fun x ↦ B x j) Ω :=
    contDiffUpToBoundary_parameterPrimitive hbounded hJ hJc h0 (hH j) (hHc j)
      (fun i ↦ hDc i j) (fun i ↦ hDeq i j) hθ hθJ
  have hBc : ContinuousOn B (closure Ω) :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) ↦ ℝ)).symm.continuous).comp_continuousOn
      (continuousOn_pi.mpr fun j ↦
        continuousOn_parameterPrimitive hJc h0 (hHc j) hθ.continuous.continuousOn hθJ)
  have hBzero (x : ℝ^(d + 1)) (hx : x ∈ frontier Ω) : B x = 0 := by
    ext j
    simp [B, parameterPrimitive, hboundary x hx]
  have hLi (P) (z) (x : ℝ^(d + 1)) (hx : x ∈ Ω) : ContDiffAt ℝ 2
      (fun a : Matrix (Fin m) (Fin (d + 1)) ℝ × (ℝ^m × ℝ^(d + 1)) ↦
        L a.1 a.2.1 a.2.2) (P, (z, x)) :=
    hL.contDiffOn.contDiffAt ((hopen.preimage (continuous_snd.comp continuous_snd)).mem_nhds hx)
  have hUi (t : ℝ) (ht : t ∈ J) (x : ℝ^(d + 1)) (hx : x ∈ Ω) :
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ^(d + 1) ↦ U p.1 p.2) (t, x) :=
    (hU.contDiffOn.contDiffAt ((hopen.prod hJ).mem_nhds ⟨hx, ht⟩)).comp (t, x)
      (f := Prod.swap) (contDiffAt_snd.prodMk contDiffAt_fst)
  have heq : EqOn B
      (parameterPrimitive (fun p : ℝ^(d + 1) × ℝ ↦ familyFlux L U p.2 p.1) θ) Ω := by
    intro x hx
    have hi : IntervalIntegrable (fun t ↦ familyFlux L U t x) volume 0 (θ x) := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      exact (contDiffAt_familyFlux (hLi _ _ x hx)
        (hUi t (hJc.uIcc_subset h0 (hθJ (subset_closure hx)) ht) x hx)).continuousAt.comp
          (f := fun s : ℝ ↦ (s, x)) (continuousAt_id.prodMk continuousAt_const)
          |>.continuousWithinAt
    ext j
    change (∫ t in 0..θ x, H j (x, t)) =
      (EuclideanSpace.proj j) (∫ t in 0..θ x, familyFlux L U t x)
    rw [← (EuclideanSpace.proj j).intervalIntegral_comp_comm hi]
    apply intervalIntegral.integral_congr
    intro t ht
    exact hHeq j x hx t (hJc.uIcc_subset h0 (hθJ (subset_closure hx)) ht)
  let := hgraph.c1ExtensionAtlas hopen hbounded
  have hGG := Boundary.Flux.gaussGreen_of_raw_graph hopen hbounded hgraph hBup hBc
  have hdivzero : (∫ x in Ω, ∇· B x) = 0 := by
    rw [hGG.2.2]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
    rw [Trace.C1.normalFlux_eq_inner B hx, hBzero x hx, inner_zero_left]
    rfl
  have hui : IntegrableOn (fieldDensity L (U 0)) Ω :=
    integrableOn_fieldDensity_parameter_graph hopen hbounded hJ hL hU contDiff_const
      (fun _ _ ↦ h0)
  have hwi := integrableOn_fieldDensity_parameter_graph hopen hbounded hJ hL hU hθ hθJ
  have hle : (∫ x in Ω, fieldDensity L (U 0) x + ∇· B x) ≤
      ∫ x in Ω, fieldDensity L (fun y ↦ U (θ y) y) x := by
    apply integral_mono_ae (hui.add hGG.1) hwi
    filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
    have hd := divergence_extremalFamilyPrimitive hJ hJc h0 (hθJ (subset_closure hx))
      (fun _ _ ↦ hLi _ _ x hx) (fun t ht ↦ hUi t ht x hx)
      (hθ.differentiable (by norm_num) x) (fun t ht ↦ hEL t ht x hx)
    have hc := fieldDensity_parameter_graph_ge
      ((hLi _ _ x hx).differentiableAt (by norm_num))
      ((hUi (θ x) (hθJ (subset_closure hx)) x hx).differentiableAt (by norm_num))
      (hθ.differentiable (by norm_num) x) (hconvex x hx (U (θ x) x))
    change fieldDensity L (U 0) x + ∇· B x ≤ _
    rw [(heq.eventuallyEq_of_mem (hopen.mem_nhds hx)).divergence_eq, hd]
    linarith
  rw [integral_add hui hGG.1, hdivzero, add_zero] at hle
  exact hle

end PDE.CalculusOfVariations.ExtremalFamily
