/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Rellich.Multiplier
public import PDE.Spaces.Sobolev.Boundary.Flux.GaussGreen.Vector
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.ClassicalGradient
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.Transverse
public import PDE.Spaces.Sobolev.Extension.C1.ClassicalHigherOrder.Gradient
import PDE.Analysis.Calculus.Divergence.Continuity

/-!
# Classical Rellich estimate for a transverse multiplier

A C¹ multiplier gives the full signed stress identity on a bounded C¹ graph
domain. For a scalar function with C² closure jets and zero boundary values,
the completed gradient is normal on the boundary. Transversality then bounds
its squared normal derivative by the volume forcing and gradient norms.

The estimate is for classical functions; it uses no trace of a weak solution
and no approximation of the domain.

The main result, `exists_normalFlux_sq_integral_bound`, gives `C > 0`, depending only on `Ω`, with
`∫_{∂Ω} (∂u/∂ν)² dS ≤ C (∫_Ω (Δu)² dx + ∫_Ω |∇u|² dx)` for every such `u`. For the multiplier
`X(x) = x` the identity of `rellich_multiplier_identity_of_contDiffUpToBoundary` is the computation
in steps 2-3 of the proof of Evans §9.4.2, Theorem 3, which multiplies `-Δu` by `x · Du`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.2, proof of Theorem 3, steps 1-3, (14)-(17),
  pp. 552-553.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (laplacian)

open scoped Gradient

namespace SobolevSpace.Boundary.Flux

open Set MeasureTheory Trace.C1 Geometry.SurfaceMeasure PDE.Analysis

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : C1ExtensionAtlas (m + 1) Ω]

/-- Rellich's multiplier identity for a C¹ vector field `X`: if `Ω` carries a
`C1ExtensionAtlas` (so is bounded and open) and has C¹ graph boundary, and `u` is C² up to the
boundary, continuous on `closure Ω` and zero on `frontier Ω`, then with
`Q = (X · ∇u) Δu + (DX ∇u) · ∇u - (|∇u|²/2) div X`, the functions `|∇u|²`, `(Δu)²` and `Q` are
integrable on `Ω`, the functions `(G₀ · ν)²` and `(G₀ · ν)² (X · ν)` are integrable for the
surface measure, and `∫_Ω Q = (1/2) ∫_{∂Ω} (G₀ · ν)² (X · ν) dS`, where `G₀` is the completed
gradient of `u`. -/
theorem rellich_multiplier_identity_of_contDiffUpToBoundary
    (hgraph : HasC1GraphBoundary Ω) {u : ℝ^(m + 1) → ℝ}
    (hu : ContDiffUpToBoundary 2 u Ω) (hc : ContinuousOn u (closure Ω))
    (hzero : ∀ x ∈ frontier Ω, u x = 0)
    {X : ℝ^(m + 1) → ℝ^(m + 1)} (hX : ContDiff ℝ 1 X) :
    let G₀ := (hu.of_le (show 1 ≤ 2 by omega)).completedGradient
    let Q := fun x ↦ inner ℝ (X x) (∇ u x) * laplacian u x +
      inner ℝ (fderiv ℝ X x (∇ u x)) (∇ u x) -
      (‖∇ u x‖ ^ 2 / 2) * ∇· X x
    IntegrableOn (fun x ↦ ‖∇ u x‖ ^ 2) Ω ∧
      IntegrableOn (fun x ↦ laplacian u x ^ 2) Ω ∧
      Integrable (fun x ↦ normalFlux (Ω := Ω) G₀ x ^ 2) (surfaceMeasure Ω) ∧
      IntegrableOn Q Ω ∧
      Integrable (fun x ↦ normalFlux (Ω := Ω) G₀ x ^ 2 * normalFlux (Ω := Ω) X x)
        (surfaceMeasure Ω) ∧
      (∫ x in Ω, Q x) = (1 / 2 : ℝ) *
        ∫ x, normalFlux (Ω := Ω) G₀ x ^ 2 * normalFlux (Ω := Ω) X x
          ∂surfaceMeasure Ω := by
  have hu₁ := hu.of_le (show 1 ≤ 2 by omega)
  let G₀ := hu₁.completedGradient
  obtain ⟨G, hG, hext⟩ :=
    hu.exists_contDiff_one_gradient_extension hΩ.isOpen hΩ.bounded hgraph
  have heq : EqOn G (∇ u) Ω :=
    (hext.mono subset_closure).trans hu₁.completedGradient_eq_gradient
  have hgerm {x : ℝ^(m + 1)} (hx : x ∈ Ω) : G =ᶠ[nhds x] ∇ u :=
    heq.eventuallyEq_of_mem (hΩ.isOpen.mem_nhds hx)
  have hlap {x : ℝ^(m + 1)} (hx : x ∈ Ω) : ∇· G x = laplacian u x :=
    (hgerm hx).divergence_eq.trans (PDE.laplacian_eq_divergence_gradient u x).symm
  have he : IntegrableOn (fun x ↦ ‖∇ u x‖ ^ 2) Ω :=
    (((hG.continuous.norm.pow 2).continuousOn.integrableOn_compact (μ := volume)
      hΩ.bounded.isCompact_closure).mono_set subset_closure).congr_fun
      (fun x hx ↦ congrArg (‖·‖ ^ 2) (heq hx)) hΩ.isOpen.measurableSet
  have hl : IntegrableOn (fun x ↦ laplacian u x ^ 2) Ω :=
    (((hG.continuous_divergence.pow 2).continuousOn.integrableOn_compact (μ := volume)
      hΩ.bounded.isCompact_closure).mono_set subset_closure).congr_fun
      (fun x hx ↦ congrArg (· ^ 2) (hlap hx)) hΩ.isOpen.measurableSet
  have hboundary : IsCompact (frontier Ω) :=
    hΩ.bounded.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hncont : ContinuousOn (normalFlux (Ω := Ω) G₀) (frontier Ω) :=
    continuousOn_normalFlux hu₁.continuous_completedGradient.continuousOn
  have hsurf {f : ℝ^(m + 1) → ℝ} (hf : ContinuousOn f (frontier Ω)) :
      Integrable f (surfaceMeasure Ω) := by
    simpa only [IntegrableOn, surfaceMeasure,
      Measure.restrict_restrict isClosed_frontier.measurableSet, Set.inter_self] using
      hf.integrableOn_compact (μ := surfaceMeasure Ω) hboundary
  have hn := hsurf (hncont.fun_pow 2)
  have hnX := hsurf ((hncont.fun_pow 2).fun_mul
    (continuousOn_normalFlux hX.continuous.continuousOn))
  have hd : EqOn (∇· (rellichMultiplierField X G))
      (fun x ↦ inner ℝ (X x) (∇ u x) * laplacian u x +
        inner ℝ (fderiv ℝ X x (∇ u x)) (∇ u x) -
        (‖∇ u x‖ ^ 2 / 2) * ∇· X x) Ω := by
    intro x hx
    rw [divergence_rellichMultiplierField_of_gradient
      (hu.contDiffOn.contDiffAt (hΩ.isOpen.mem_nhds hx))
      (hX.differentiable one_ne_zero x) (hG.differentiable one_ne_zero x) (hgerm hx), heq hx]
  have hQ := (integrableOn_divergence (Ω := Ω) (contDiff_rellichMultiplierField hX hG)).congr_fun
    hd hΩ.isOpen.measurableSet
  refine ⟨he, hl, hn, hQ, hnX, ?_⟩
  have hb : normalFlux (Ω := Ω) (rellichMultiplierField X G) =ᵐ[surfaceMeasure Ω]
      fun x ↦ (1 / 2 : ℝ) *
        (normalFlux (Ω := Ω) G₀ x ^ 2 * normalFlux (Ω := Ω) X x) := by
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
    have hnormal : G x =
        inner ℝ (G x) (outwardUnitNormal (Ω := Ω) ⟨x, hx⟩) •
          outwardUnitNormal (Ω := Ω) ⟨x, hx⟩ := by
      rw [hext (frontier_subset_closure hx)]
      exact completedGradient_eq_normal_smul hgraph hu₁ hc hzero hx
    have hnorm : ‖G x‖ ^ 2 = normalFlux (Ω := Ω) G₀ x ^ 2 := by
      have h := congrArg (fun z ↦ inner ℝ (G x) z) hnormal
      simp only [real_inner_self_eq_norm_sq, inner_smul_right, ← pow_two] at h
      rw [h, normalFlux_eq_inner _ hx]
      exact congrArg (fun z ↦ inner ℝ z (outwardUnitNormal (Ω := Ω) ⟨x, hx⟩) ^ 2)
        (hext (frontier_subset_closure hx))
    rw [normalFlux_eq_inner _ hx,
      inner_rellichMultiplierField_of_normal x _ hnormal, hnorm,
      normalFlux_eq_inner X hx]
    ring
  have hgg := integral_divergence_eq_normalFlux hgraph (contDiff_rellichMultiplierField hX hG)
  rwa [setIntegral_congr_fun hΩ.isOpen.measurableSet (fun x hx ↦ hd hx),
    integral_congr_ae hb, integral_const_mul] at hgg

/-- A transverse multiplier bounds the normal derivative: under the hypotheses of
`rellich_multiplier_identity_of_contDiffUpToBoundary`, if moreover `δ ≤ X · ν` on `∂Ω` for some
`δ > 0`, and `|X| ≤ M`, `‖DX‖ ≤ K` and `|div X| ≤ D` on `Ω`, then `(G₀ · ν)²` is integrable for
the surface measure and
`∫_{∂Ω} (G₀ · ν)² dS ≤ δ⁻¹ (∫_Ω (Δu)² + (M² + 2K + D) ∫_Ω |∇u|²)`. -/
theorem normalFlux_sq_integral_le_of_transverse
    (hgraph : HasC1GraphBoundary Ω) {u : ℝ^(m + 1) → ℝ}
    (hu : ContDiffUpToBoundary 2 u Ω) (hc : ContinuousOn u (closure Ω))
    (hzero : ∀ x ∈ frontier Ω, u x = 0)
    {X : ℝ^(m + 1) → ℝ^(m + 1)} (hX : ContDiff ℝ 1 X)
    {δ M K D : ℝ} (hδ : 0 < δ)
    (htrans : ∀ x ∈ frontier Ω, δ ≤ normalFlux (Ω := Ω) X x)
    (hM : ∀ x ∈ Ω, ‖X x‖ ≤ M)
    (hK : ∀ x ∈ Ω, ‖fderiv ℝ X x‖ ≤ K)
    (hD : ∀ x ∈ Ω, |∇· X x| ≤ D) :
    let G₀ := (hu.of_le (show 1 ≤ 2 by omega)).completedGradient
    Integrable (fun x ↦ normalFlux (Ω := Ω) G₀ x ^ 2) (surfaceMeasure Ω) ∧
      (∫ x, normalFlux (Ω := Ω) G₀ x ^ 2 ∂surfaceMeasure Ω) ≤
        (δ⁻¹) * ((∫ x in Ω, laplacian u x ^ 2) +
          (M ^ 2 + 2 * K + D) * ∫ x in Ω, ‖∇ u x‖ ^ 2) := by
  let G₀ := (hu.of_le (show 1 ≤ 2 by omega)).completedGradient
  obtain ⟨he, hl, hn, hQ, hnX, hid⟩ :=
    rellich_multiplier_identity_of_contDiffUpToBoundary hgraph hu hc hzero hX
  refine ⟨hn, ?_⟩
  have hb : δ * (∫ x, normalFlux (Ω := Ω) G₀ x ^ 2 ∂surfaceMeasure Ω) ≤
      ∫ x, normalFlux (Ω := Ω) G₀ x ^ 2 * normalFlux (Ω := Ω) X x
        ∂surfaceMeasure Ω := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hn.const_mul δ) hnX
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
    exact (mul_le_mul_of_nonneg_right (htrans x hx) (sq_nonneg _)).trans_eq (mul_comm _ _)
  have hv : 2 * (∫ x in Ω,
        inner ℝ (X x) (∇ u x) * laplacian u x +
        inner ℝ (fderiv ℝ X x (∇ u x)) (∇ u x) -
        (‖∇ u x‖ ^ 2 / 2) * ∇· X x) ≤
      (∫ x in Ω, laplacian u x ^ 2) +
        (M ^ 2 + 2 * K + D) * ∫ x in Ω, ‖∇ u x‖ ^ 2 := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add hl (he.const_mul _)]
    apply integral_mono_ae (hQ.const_mul 2) (hl.add (he.const_mul _))
    filter_upwards [ae_restrict_mem hΩ.isOpen.measurableSet] with x hx
    exact two_mul_rellich_integrand_le (hM x hx) (hK x hx) (hD x hx)
  rw [hid] at hv
  exact (le_inv_mul_iff₀ hδ).2 (by linarith)

omit hΩ in
/-- `normalFlux_sq_integral_le_of_transverse` for a bounded open `Ω` with C¹ graph boundary, with
no atlas assumed: normals, fluxes and the surface measure are those of the atlas
`hgraph.c1ExtensionAtlas hopen hbounded`. -/
theorem normalFlux_sq_integral_le_of_raw_graph_transverse
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω) {u : ℝ^(m + 1) → ℝ}
    (hu : ContDiffUpToBoundary 2 u Ω) (hc : ContinuousOn u (closure Ω))
    (hzero : ∀ x ∈ frontier Ω, u x = 0)
    {X : ℝ^(m + 1) → ℝ^(m + 1)} (hX : ContDiff ℝ 1 X)
    {δ M K D : ℝ} (hδ : 0 < δ)
    (htrans : letI := hgraph.c1ExtensionAtlas hopen hbounded
      ∀ x ∈ frontier Ω, δ ≤ normalFlux (Ω := Ω) X x)
    (hM : ∀ x ∈ Ω, ‖X x‖ ≤ M)
    (hK : ∀ x ∈ Ω, ‖fderiv ℝ X x‖ ≤ K)
    (hD : ∀ x ∈ Ω, |∇· X x| ≤ D) :
    letI := hgraph.c1ExtensionAtlas hopen hbounded
    let G₀ := (hu.of_le (show 1 ≤ 2 by omega)).completedGradient
    Integrable (fun x ↦ normalFlux (Ω := Ω) G₀ x ^ 2) (surfaceMeasure Ω) ∧
      (∫ x, normalFlux (Ω := Ω) G₀ x ^ 2 ∂surfaceMeasure Ω) ≤
        δ⁻¹ * ((∫ x in Ω, laplacian u x ^ 2) +
          (M ^ 2 + 2 * K + D) * ∫ x in Ω, ‖∇ u x‖ ^ 2) := by
  let := hgraph.c1ExtensionAtlas hopen hbounded
  exact normalFlux_sq_integral_le_of_transverse hgraph hu hc hzero hX hδ htrans hM hK hD

omit hΩ in
/-- For a bounded open `Ω` with C¹ graph boundary there is `C > 0` such that every `u` that is C²
up to the boundary, continuous on `closure Ω` and zero on `frontier Ω` has `(G₀ · ν)²`
integrable for the surface measure, with
`∫_{∂Ω} (G₀ · ν)² dS ≤ C (∫_Ω (Δu)² + ∫_Ω |∇u|²)`; `G₀` is the completed gradient of `u`. -/
theorem exists_normalFlux_sq_integral_bound
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω) :
    letI := hgraph.c1ExtensionAtlas hopen hbounded
    ∃ C > 0, ∀ (u : ℝ^(m + 1) → ℝ) (hu : ContDiffUpToBoundary 2 u Ω),
      ContinuousOn u (closure Ω) → (∀ x ∈ frontier Ω, u x = 0) →
      let G₀ := (hu.of_le (show 1 ≤ 2 by omega)).completedGradient
      Integrable (fun x ↦ normalFlux (Ω := Ω) G₀ x ^ 2) (surfaceMeasure Ω) ∧
        (∫ x, normalFlux (Ω := Ω) G₀ x ^ 2 ∂surfaceMeasure Ω) ≤
          C * ((∫ x in Ω, laplacian u x ^ 2) +
            ∫ x in Ω, ‖∇ u x‖ ^ 2) := by
  let := hgraph.c1ExtensionAtlas hopen hbounded
  obtain ⟨X, hX, _, hM, htrans, K, hKpos, hK⟩ :=
    hgraph.exists_contDiff_transverse hopen hbounded
  have hX1 : ContDiff ℝ 1 X := hX.of_le (by simp)
  obtain ⟨D₀, hD₀⟩ := hbounded.isCompact_closure.exists_bound_of_continuousOn
    hX1.continuous_divergence.continuousOn
  let D : ℝ := max D₀ 1
  have hDpos : 0 < D := zero_lt_one.trans_le (le_max_right _ _)
  have hD : ∀ x ∈ Ω, |∇· X x| ≤ D := fun x hx ↦
    (hD₀ x (subset_closure hx)).trans (le_max_left _ _)
  have ht : ∀ x ∈ frontier Ω, (1 / 2 : ℝ) ≤ normalFlux (Ω := Ω) X x := fun x hx ↦ by
    rw [normalFlux_eq_inner _ hx]
    exact htrans ⟨x, hx⟩
  let A : ℝ := 1 + 2 * K + D
  have hA : 1 ≤ A := by dsimp [A]; linarith
  refine ⟨2 * A, mul_pos (by norm_num) (zero_lt_one.trans_le hA), ?_⟩
  intro u hu hc hzero
  obtain ⟨hi, hb⟩ := normalFlux_sq_integral_le_of_transverse hgraph hu hc hzero hX1
    (by norm_num : (0 : ℝ) < 1 / 2) ht (fun x _ ↦ hM x) (fun x _ ↦ hK x) hD
  refine ⟨hi, ?_⟩
  have hl : 0 ≤ ∫ x in Ω, laplacian u x ^ 2 :=
    integral_nonneg (fun x ↦ sq_nonneg (laplacian u x))
  calc _ ≤ 2 * ((∫ x in Ω, laplacian u x ^ 2) + A * ∫ x in Ω, ‖∇ u x‖ ^ 2) := by
        simpa only [A, one_pow, one_div, inv_inv] using hb
    _ ≤ _ := by linarith [mul_nonneg (sub_nonneg.mpr hA) hl]

end SobolevSpace.Boundary.Flux
