/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtremalFamily.Primitive
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Closure

/-!
# Boundary regularity of moving-endpoint primitives

Continuous extensions of the integrand and its spatial derivatives suffice for
first-order closure regularity of its primitive. No derivative of the extensions
across the boundary is required.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

namespace PDE.CalculusOfVariations.ExtremalFamily

open Analysis SobolevSpace

/-- Joint continuity along an interval gives continuity of the moving-endpoint
primitive on an arbitrary parameter set. -/
theorem continuousOn_parameterPrimitive
    {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {J : Set ℝ} {H : E × ℝ → F} {θ : E → ℝ}
    (hJ : OrdConnected J) (h0 : 0 ∈ J) (hH : ContinuousOn H (S ×ˢ J))
    (hθ : ContinuousOn θ S) (hθJ : MapsTo θ S J) :
    ContinuousOn (parameterPrimitive H θ) S := by
  have hmap : MapsTo (fun p : E × ℝ ↦ (p.1, p.2 * θ p.1))
      (S ×ˢ uIcc (0 : ℝ) 1) (S ×ˢ J) := by
    intro p hp
    refine ⟨hp.1, hJ.uIcc_subset h0 (hθJ hp.1) ?_⟩
    have ht : p.2 ∈ Icc (0 : ℝ) 1 := by simpa using hp.2
    by_cases h : 0 ≤ θ p.1
    · rw [uIcc_of_le h]
      exact ⟨mul_nonneg ht.1 h, mul_le_of_le_one_left h ht.2⟩
    · rw [uIcc_of_ge (le_of_not_ge h)]
      exact ⟨by nlinarith [ht.2], mul_nonpos_of_nonneg_of_nonpos ht.1 (le_of_not_ge h)⟩
  have hi : ContinuousOn (fun x ↦ ∫ t in (0 : ℝ)..1, H (x, t * θ x)) S :=
    continuousOn_intervalIntegral (hH.comp
      (continuousOn_fst.prodMk (continuousOn_snd.mul
        (hθ.comp continuousOn_fst (fun _ hp ↦ hp.1)))) hmap)
  apply (hθ.smul hi).congr
  intro x _
  symm
  change θ x • (∫ t in (0 : ℝ)..1, H (x, t * θ x)) = ∫ t in (0 : ℝ)..θ x, H (x, t)
  simpa only [zero_mul, one_mul] using
    (intervalIntegral.smul_integral_comp_mul_right
      (f := fun t ↦ H (x, t)) (a := 0) (b := 1) (θ x))

/-- Continuous closure extensions of the spatial partial derivatives provide
raw first-order boundary regularity of a scalar primitive. -/
theorem contDiffUpToBoundary_parameterPrimitive
    {n : ℕ} {Ω : Set (ℝ^n)} {J : Set ℝ} {H : ℝ^n × ℝ → ℝ}
    {D : Fin n → ℝ^n × ℝ → ℝ} {θ : ℝ^n → ℝ}
    (hbounded : Bornology.IsBounded Ω)
    (hJ : IsOpen J) (hJc : OrdConnected J) (h0 : 0 ∈ J)
    (hH : ∀ x ∈ Ω, ∀ t ∈ J, ContDiffAt ℝ 1 H (x, t))
    (hHc : ContinuousOn H (closure Ω ×ˢ J))
    (hDc : ∀ i, ContinuousOn (D i) (closure Ω ×ˢ J))
    (hD : ∀ i x, x ∈ Ω → ∀ t ∈ J,
      D i (x, t) = fderiv ℝ H (x, t) (EuclideanSpace.single i 1, 0))
    (hθ : ContDiff ℝ 1 θ) (hθJ : MapsTo θ (closure Ω) J) :
    ContDiffUpToBoundary 1 (parameterPrimitive H θ) Ω := by
  have hc := continuousOn_parameterPrimitive hJc h0 hHc hθ.continuous.continuousOn hθJ
  apply ContDiffUpToBoundary.of_continuous_first_derivative_extensions
    (fun x hx ↦ (contDiffAt_parameterPrimitive
      (fun t ht ↦ hH x hx t (hJc.uIcc_subset h0 (hθJ (subset_closure hx)) ht))
      hθ.contDiffAt).contDiffWithinAt) hbounded hc (fun _ _ ↦ rfl)
  intro i
  let e := EuclideanSpace.single i (1 : ℝ)
  refine ⟨fun x ↦ fderiv ℝ θ x e * H (x, θ x) + parameterPrimitive (D i) θ x, ?_, ?_⟩
  · exact ((((hθ.continuous_fderiv (by norm_num)).clm_apply continuous_const).continuousOn).mul
      (hHc.comp (continuousOn_id.prodMk hθ.continuous.continuousOn)
        (fun x hx ↦ ⟨hx, hθJ hx⟩))).add
      (continuousOn_parameterPrimitive hJc h0 (hDc i) hθ.continuous.continuousOn hθJ)
  · intro x hx
    have hd := hasFDerivAt_parameterPrimitive hJ hJc h0 (hθJ (subset_closure hx))
      (hH x hx) (hθ.differentiable (by norm_num) x)
    have hint : IntervalIntegrable
        (fun t ↦ (fderiv ℝ H (x, t)).comp (ContinuousLinearMap.inl ℝ (ℝ^n) ℝ))
        volume 0 (θ x) := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      exact (((hH x hx t (hJc.uIcc_subset h0 (hθJ (subset_closure hx)) ht)).fderiv_right
        (m := 0) (by norm_num)).continuousAt.comp
          (continuousAt_const.prodMk continuousAt_id)).clm_comp
            continuousAt_const |>.continuousWithinAt
    change _ = fderiv ℝ (parameterPrimitive H θ) x e
    rw [hd.fderiv, add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.intervalIntegral_apply hint]
    simp only [smul_eq_mul, parameterPrimitive]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    exact hD i x hx t (hJc.uIcc_subset h0 (hθJ (subset_closure hx)) ht)

end PDE.CalculusOfVariations.ExtremalFamily
