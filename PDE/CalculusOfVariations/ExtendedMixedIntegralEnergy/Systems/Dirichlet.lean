/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Systems.DirectMethod
public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Systems.Sobolev

/-!
# Minimization of coupled extended energies in affine Sobolev classes

Finite products of the zero-boundary graph spaces are reflexive and
separable. Matrix coercivity bounds their finite affine energy sublevels.
The vector weak lower-semicontinuity theorem then gives a minimizer, with the
all-infinite case included by the extended direct method.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Topology Sobolev

namespace PDE.CalculusOfVariations

/-- Every prescribed affine finite Sobolev class has a minimizer for a coupled
matrix-coercive extended energy convex in the full gradient. No finite-energy
competitor or upper growth bound is assumed. -/
theorem exists_minimizer_vectorWkpLIntegral_prescribed_boundary
    {m n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 1 < p)
    {F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ}
    {D : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ^(m * n)} {b : ℝ^n → ℝ}
    (hF : Measurable (Function.uncurry F))
    (hD : Measurable (Function.uncurry D)) (hb : Measurable b)
    (hFcont : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^(m * n),
      Continuous (fun s : ℝ^m ↦ F x (s, z)))
    (hDcont : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^(m * n),
      Continuous (fun s : ℝ^m ↦ D x (s, z)))
    (hconvex : ∀ᵐ x ∂domainMeasure n Ω, ∀ s : ℝ^m,
      ConvexOn ℝ univ (fun z : ℝ^(m * n) ↦ F x (s, z)))
    (hderiv : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ^m) (z : ℝ^(m * n)),
      HasFDerivAt (fun y : ℝ^(m * n) ↦ F x (s, y)) (innerSL ℝ (D x (s, z))) z)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ^m) (z : ℝ^(m * n)),
      c * ‖z‖ ^ (p : ℝ) - b x ≤ F x (s, z))
    (g : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) :
    ∃ u : Fin m → W^{1,(p : ℝ≥0∞)}(Ω),
      (∀ i, u i - g i ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)) ∧
      ∀ v : Fin m → W^{1,(p : ℝ≥0∞)}(Ω),
        (∀ i, v i - g i ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)) →
        vectorWkpLIntegral F b u ≤ vectorWkpLIntegral F b v := by
  have hclosed : IsSeqClosed (toWeakSpace ℝ
      (Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) '' univ) := by
    rw [image_univ_of_surjective (toWeakSpace ℝ _).surjective]
    exact isClosed_univ.isSeqClosed
  suffices hlsc : ∀ {u : ℕ → Fin m → W^{1,(p : ℝ≥0∞)}(Ω)}
      {U : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)},
      Tendsto (fun j ↦ toWeakSpace ℝ _ (u j)) atTop (𝓝 (toWeakSpace ℝ _ U)) →
      vectorWkpLIntegral F b U ≤ liminf (fun j ↦ vectorWkpLIntegral F b (u j)) atTop by
    obtain ⟨u, _, hu, hmin⟩ :=
      exists_minimizer_vectorWkpLIntegral_prescribed_boundary_of_weak_lsc
        hbounded hp hc hlower hlsc hclosed g (mem_univ _)
    exact ⟨u, hu, fun v hv ↦ hmin v (mem_univ _) hv⟩
  intro u U hu
  have hlower' : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^m × ℝ^(m * n), -b x ≤ F x z := by
    filter_upwards [hlower] with x hx
    intro z
    have hnonneg := mul_nonneg hc.le (Real.rpow_nonneg (norm_nonneg z.2) (p : ℝ))
    have h := hx z.1 z.2
    linarith
  simpa only [vectorWkpLIntegral, Pi.neg_apply, sub_neg_eq_add] using
    lintegral_le_liminf_of_tendsto_weak_vectorWkp_of_c1Domain
      hopen hbounded hgraph hp hF hD hb.neg hFcont hDcont hconvex hderiv hlower' hu

end PDE.CalculusOfVariations
