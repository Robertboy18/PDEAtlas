/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Measurable.Coordinates
public import PDE.Parabolic.Heat.Variational.MeasurableGalerkin

/-!
# Galerkin solutions on every initial segment of an orthogonal basis

The basis is orthogonal and total in the energy space and orthonormal in L².
The first `m` vectors give stable trial projections with bound one. The original
measurable parabolic coefficients and L² data therefore give absolutely
continuous Galerkin solutions on these spaces, with the finite initial
coefficient sum and the uniform three-term estimate. This is Evans's §7.1.2, Theorems 1
and 2, for his basis (12)-(13), with the initial coefficients (15) and the estimate (20)
(`exists_firstGalerkinCoefficients`, `exists_firstGalerkinSolution`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, (12)-(16), p. 375, Theorem 1 (Construction of
  approximate solutions) and its proof, (17)-(19), p. 376, and Theorem 2 (Energy estimates), (20),
  pp. 376-378.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Sobolev

open Filter MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace

namespace HeatEquation.Variational.BoundedMeasurableCoefficients

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- The first-`m` coefficient system has an AC solution, unique among
all AC vectors satisfying the original scalar equations and initial coefficients.
The synthesis map is the finite sum in the given basis. This is Evans's §7.1.2, Theorem 1,
with the system (19) and the initial conditions (15). -/
theorem exists_firstGalerkinCoefficients
    (C : BoundedMeasurableCoefficients n Ω (volume.restrict (Ioc a b)))
    (hΩopen : IsOpen Ω) (hab : a ≤ b)
    (w : ℕ → H¹₀(Ω))
    (hw : Pairwise (fun i j ↦ ⟪w i, w j⟫_ℝ = 0))
    (hJw : Orthonormal ℝ (fun i ↦ (h10L2GelfandTriple hΩopen).inclusion (w i)))
    (hdense : Dense (Submodule.span ℝ (range w) : Set (H¹₀(Ω))))
    (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
    (uInit : DerivLp n 2 Ω) (m : ℕ) :
    let T := h10L2GelfandTriple hΩopen
    let F := finiteTrialCombination w (Finset.range m)
    let rhs := fun (d : ℝ → (Finset.range m) → ℝ) t (i : Finset.range m) ↦
      ⟪f t, T.inclusion (w i)⟫_ℝ - C.form t (F (d t) : H¹₀(Ω)) (w i)
    ∃ d : ℝ → (Finset.range m) → ℝ,
      AbsolutelyContinuousOnInterval d a b ∧
      (∀ i, d a i = ⟪T.inclusion (w i), uInit⟫_ℝ) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt d (rhs d t) t) ∧
      ∀ e : ℝ → (Finset.range m) → ℝ,
        AbsolutelyContinuousOnInterval e a b →
        (∀ i, e a i = ⟪T.inclusion (w i), uInit⟫_ℝ) →
        (∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt e (rhs e t) t) →
        EqOn d e (Icc a b) := by
  let T := h10L2GelfandTriple hΩopen
  let s := Finset.range m
  let S := Submodule.span ℝ (w '' (s : Set ℕ))
  let := FiniteDimensional.span_of_finite ℝ (s.finite_toSet.image w)
  let P := stableTrialProjectionOfOrthogonalFamily T hw hJw.2 hdense s
  let ell := fun t ↦ T.pivotToDual (f t)
  have hell := pivotLoad_memLp hΩopen f
  obtain ⟨U⟩ := exists_gelfandGalerkinCaratheodory_of_integrable T S C.form ell hab
    C.aestronglyMeasurable_form_apply_Icc (hell.integrable (by norm_num))
    C.formBound (fun t _ ↦ C.norm_form_le t) (P.projection uInit)
  let d := fun t (i : s) ↦ ⟪T.inclusion (w i), T.inclusion (U.trajectory t : H¹₀(Ω))⟫_ℝ
  have hcoeff (i : s) :
      ⟪T.inclusion (w i), T.inclusion (P.projection uInit : H¹₀(Ω))⟫_ℝ =
        ⟪T.inclusion (w i), uInit⟫_ℝ := by
    have h := P.pivotOrthogonal
      ⟨w i, Submodule.subset_span ⟨i, i.property, rfl⟩⟩ uInit
    rw [inner_sub_right] at h
    exact (sub_eq_zero.mp h).symm
  obtain ⟨hAC, hdeq⟩ := U.gelfandGalerkin_finiteCoefficients s
  have hrec (t : ℝ) :
      finiteTrialCombination w s (d t) = U.trajectory t :=
    P.finiteTrialCombination_inner_eq_self T hJw s (U.trajectory t)
  refine ⟨d, hAC, ?_, ?_, ?_⟩
  · intro i
    change ⟪T.inclusion (w i), T.inclusion (U.trajectory a : H¹₀(Ω))⟫_ℝ = _
    rw [U.initial_value]
    exact hcoeff i
  · filter_upwards [hdeq] with t ht
    change HasDerivAt d (fun i : s ↦ ell t (w i) -
      C.form t (finiteTrialCombination w s (d t) : H¹₀(Ω)) (w i)) t
    rw [hrec]
    exact ht
  · intro e heAC heinit heeq
    exact U.gelfandGalerkin_finiteCoefficients_unique s P hJw hab
      C.aestronglyMeasurable_form_apply_Icc C.formBound (fun t _ ↦ C.norm_form_le t)
      e heAC (fun i ↦ (heinit i).trans (hcoeff i).symm) heeq

/-- Every first-`m` span of a simultaneous energy-orthogonal and pivot-orthonormal
basis has an AC Galerkin solution. Its initial value is the finite L²
coefficient sum, and its state and dual derivative satisfy a bound
independent of `m`, in the original forcing and initial-data norms, as in Evans's (20). -/
theorem exists_firstGalerkinSolution
    (C : BoundedMeasurableCoefficients n Ω (volume.restrict (Ioc a b)))
    (hΩopen : IsOpen Ω) (hab : a ≤ b)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hElliptic : ∀ᵐ z ∂(volume.restrict (Ioc a b)).prod (domainMeasure n Ω),
      ∀ ξ : Fin n → ℝ,
        alpha * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, C.principal i j z * ξ j * ξ i)
    (w : ℕ → H¹₀(Ω))
    (hw : Pairwise (fun i j ↦ ⟪w i, w j⟫_ℝ = 0))
    (hJw : Orthonormal ℝ (fun i ↦ (h10L2GelfandTriple hΩopen).inclusion (w i)))
    (hdense : Dense (Submodule.span ℝ (range w) : Set (H¹₀(Ω))))
    (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
    (uInit : DerivLp n 2 Ω) (m : ℕ) :
    let T := h10L2GelfandTriple hΩopen
    let S := Submodule.span ℝ (w '' (Finset.range m : Set ℕ))
    letI := FiniteDimensional.span_of_finite ℝ ((Finset.range m).finite_toSet.image w)
    let P := stableTrialProjectionOfOrthogonalFamily T hw hJw.2 hdense (Finset.range m)
    let ell := fun t ↦ T.pivotToDual (f t)
    ∃ U : AffineCaratheodorySolutionOn
        (fun t ↦ -(gelfandGalerkinOperator T S (C.form t)))
        (gelfandGalerkinForcing T S ell) a b (P.projection uInit),
      (U.trajectory a : H¹₀(Ω)) =
        ∑ i ∈ Finset.range m, ⟪T.inclusion (w i), uInit⟫_ℝ • w i ∧
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
  let S := Submodule.span ℝ (w '' (Finset.range m : Set ℕ))
  let := FiniteDimensional.span_of_finite ℝ ((Finset.range m).finite_toSet.image w)
  let P := stableTrialProjectionOfOrthogonalFamily T hw hJw.2 hdense (Finset.range m)
  let ell := fun t ↦ T.pivotToDual (f t)
  have hell := pivotLoad_memLp hΩopen f
  obtain ⟨U⟩ := exists_gelfandGalerkinCaratheodory_of_integrable T S C.form ell hab
    C.aestronglyMeasurable_form_apply_Icc (hell.integrable (by norm_num))
    C.formBound (fun t _ ↦ C.norm_form_le t) (P.projection uInit)
  refine ⟨U, ?_, U.gelfandGalerkin_weakDerivative hab C.aestronglyMeasurable_form_apply_Icc
    hell C.formBound (fun t _ ↦ C.norm_form_le t), ?_⟩
  · rw [U.initial_value]
    exact P.projection_eq_sum T hJw (Finset.range m) uInit
  · have hgamma : 0 ≤ coerciveShift (n := n) alpha C.bound C.bound := by
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
    have h := U.gelfandGalerkin_three_term_bound P hab (half_pos halpha) hgamma
      C.aestronglyMeasurable_form_apply_Icc hell C.formBound (fun t _ ↦ C.norm_form_le t)
      (C.ae_garding hΩopen halpha hElliptic) t ht
    exact h.trans (mul_le_mul_of_nonneg_left
      (add_le_add (P.norm_inclusion_projection_le uInit) hnorm) hC)

end HeatEquation.Variational.BoundedMeasurableCoefficients
