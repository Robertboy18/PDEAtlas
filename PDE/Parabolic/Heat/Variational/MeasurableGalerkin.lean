/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Measurable.L2Solution
public import PDE.Parabolic.Heat.Variational.MeasurableBounds

/-!
# Galerkin solutions for raw measurable parabolic coefficients

The spectral trial spaces have pivot-orthogonal projections contractive in the
energy norm. Their mass-inverted Carathéodory equations use the original L² load.
The resulting absolutely continuous trajectories and their weak derivatives
satisfy the three-term bound uniformly over the trial spaces.

This is the construction and estimate (20) of Evans's §7.1.2, Theorems 1 and 2, with
whole spectral eigenspaces as trial spaces in place of the spans of the first `m` basis
functions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, (12)-(16), p. 375, Theorem 1 (Construction of
  approximate solutions), p. 376, and Theorem 2 (Energy estimates), (20), pp. 376-378.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Sobolev

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace HeatEquation.Variational.BoundedMeasurableCoefficients

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Adding the left endpoint does not change measurability of form evaluations. -/
theorem aestronglyMeasurable_form_apply_Icc
    (C : BoundedMeasurableCoefficients n Ω (volume.restrict (Ioc a b)))
    (v : H¹₀(Ω)) :
    AEStronglyMeasurable (fun t ↦ C.form t v) (volume.restrict (Icc a b)) := by
  rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b))]
  exact C.aestronglyMeasurable_form_apply v

/-- The original forcing defines a square-integrable dual load. -/
theorem pivotLoad_memLp (hΩopen : IsOpen Ω)
    (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))) :
    MemLp (fun t ↦ (h10L2GelfandTriple hΩopen).pivotToDual (f t))
      2 (volume.restrict (Ioc a b)) :=
  (h10L2GelfandTriple hΩopen).pivotToDual.comp_memLp' (Lp.memLp f)

/-- Every canonical trial space admits an AC Galerkin solution with
projected initial data, a weak derivative, and the uniform three-term
estimate in the original data norms. -/
theorem exists_galerkinSolution
    (C : BoundedMeasurableCoefficients n Ω (volume.restrict (Ioc a b)))
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (hab : a ≤ b)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hElliptic : ∀ᵐ z ∂(volume.restrict (Ioc a b)).prod (domainMeasure n Ω),
      ∀ ξ : Fin n → ℝ,
        alpha * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, C.principal i j z * ξ j * ξ i)
    (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
    (uInit : DerivLp n 2 Ω) (m : ℕ) :
    let T := h10L2GelfandTriple hΩopen
    let S := h10L2SpectralTrialSystem hΩopen hΩbounded
    letI := S.finiteDimensional m
    let ell := fun t ↦ T.pivotToDual (f t)
    ∃ U : AffineCaratheodorySolutionOn
        (fun t ↦ -(gelfandGalerkinOperator T (S.space m) (C.form t)))
        (gelfandGalerkinForcing T (S.space m) ell) a b ((S.projection m).projection uInit),
      HasGelfandWeakTimeDerivativeOn T (U.gelfandGalerkinStateLp hab)
        (U.gelfandGalerkinDualLp hab C.aestronglyMeasurable_form_apply_Icc
          (pivotLoad_memLp hΩopen f) C.formBound (fun t _ ↦ C.norm_form_le t)) ∧
      ∀ t ∈ Icc a b,
        ‖T.inclusion (U.trajectory t : H¹₀(Ω))‖ +
          ‖U.gelfandGalerkinStateLp hab‖ +
          ‖U.gelfandGalerkinDualLp hab C.aestronglyMeasurable_form_apply_Icc
            (pivotLoad_memLp hΩopen f) C.formBound (fun t _ ↦ C.norm_form_le t)‖ ≤
        gardingThreeTermConstant (alpha / 2) (coerciveShift (n := n) alpha C.bound C.bound)
          (b - a) C.formBound 1 * (‖uInit‖ + ‖f‖) := by
  let T := h10L2GelfandTriple hΩopen
  let S := h10L2SpectralTrialSystem hΩopen hΩbounded
  let := S.finiteDimensional m
  let ell := fun t ↦ T.pivotToDual (f t)
  have hell := pivotLoad_memLp hΩopen f
  obtain ⟨U⟩ := exists_gelfandGalerkinCaratheodory_of_integrable T (S.space m) C.form ell
    hab C.aestronglyMeasurable_form_apply_Icc (hell.integrable (by norm_num))
    C.formBound (fun t _ ↦ C.norm_form_le t) ((S.projection m).projection uInit)
  refine ⟨U, U.gelfandGalerkin_weakDerivative hab C.aestronglyMeasurable_form_apply_Icc
    hell C.formBound (fun t _ ↦ C.norm_form_le t), ?_⟩
  have hgamma : 0 ≤ coerciveShift (n := n) alpha C.bound C.bound := by
    unfold coerciveShift gardingMass
    positivity
  have hnorm : ‖hell.toLp ell‖ ≤ ‖f‖ := by
    have heq : hell.toLp ell = T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f := by
      apply Lp.ext
      exact hell.coeFn_toLp.trans (T.pivotToDual.coeFn_compLpL f).symm
    rw [heq]
    exact norm_pivotLoadLp_le hΩopen f
  have hC : 0 ≤ gardingThreeTermConstant (alpha / 2)
      (coerciveShift (n := n) alpha C.bound C.bound) (b - a) C.formBound 1 := by
    unfold gardingThreeTermConstant
    positivity
  intro t ht
  have h := U.gelfandGalerkin_three_term_bound (S.projection m) hab (half_pos halpha)
    hgamma C.aestronglyMeasurable_form_apply_Icc hell C.formBound
    (fun t _ ↦ C.norm_form_le t) (C.ae_garding hΩopen halpha hElliptic) t ht
  exact h.trans (mul_le_mul_of_nonneg_left
    (add_le_add ((S.projection m).norm_inclusion_projection_le uInit) hnorm) hC)

end HeatEquation.Variational.BoundedMeasurableCoefficients
