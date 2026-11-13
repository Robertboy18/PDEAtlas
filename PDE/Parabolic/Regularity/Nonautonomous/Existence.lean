/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.AbsoluteContinuity
public import PDE.Elliptic.Variational.CoefficientDependence
public import PDE.Elliptic.Regularity.Boundary.GeometricAtlas
public import PDE.Parabolic.Regularity.Nonautonomous.SpatialH2
import PDE.Analysis.Evolution.Galerkin.ImprovedRegularity.MeasurableForcing
import PDE.Spaces.Sobolev.Variational.Galerkin.SpectralTrial

/-!
# Time regularity for nonautonomous divergence-form equations

On a bounded open domain, consider

`uₜ - ∑ᵢⱼ ∂ᵢ(aᵢⱼ(t,x) ∂ⱼu) = f`, with zero Dirichlet boundary values.

The matrix is symmetric, measurable and bounded in space, and uniformly elliptic. Its time
dependence is absolutely continuous in the `L∞` matrix norm, with a given almost-everywhere
derivative bounded in that norm. For `f ∈ L²_t L²_x` and initial data in `H¹₀`,
`exists_nonautonomous_symmetric_solution_with_l2_time_derivative` constructs
`u ∈ L²_t H¹₀ ∩ L∞_t H¹₀` with `uₜ ∈ L²_t L²_x`. The initial datum enters through the integrated
weak equation.

With a `C²` graph boundary and spatial `W¹,∞` coefficients continuous in time,
`exists_nonautonomous_symmetric_solution_with_spatial_h2` also constructs a Bochner `L²_t H²_x`
representative of this same solution. Its elliptic estimate is uniform in time and is derived from
the coefficient and domain hypotheses. The `_data_bounds` versions retain the quantitative Galerkin
estimates and give `‖u‖_{L∞ H¹₀} + ‖uₜ‖_{L² L²} + ‖U‖_{L² H²} ≤ C (‖f‖_{L² L²} + ‖uInit‖_{H¹₀})`,
with `C` chosen before either datum.

These theorems extend Evans's §7.1.3, Theorem 5(i), and its estimate (46), for a symmetric principal
part without lower-order terms, to coefficients that depend on time; Evans assumes coefficients
independent of `t`, (45). Bounded linear dependence on the coefficient matrix gives the time
regularity of the forms, Poincaré's inequality gives uniform coercivity, and compactness of
`H¹₀ ↪ L²` gives the stable Galerkin spaces; all three are derived from the coefficient hypotheses.
The time derivative of the coefficients is taken in the `L∞` norm, not pointwise in space.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.3, (45), p. 381, Theorem 5 (Improved regularity), (46),
  p. 382, and steps 1-3 of its proof, (48)-(49), pp. 382-384.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace

namespace PDE.Parabolic.DivergenceFormHeat

open PDE.Analysis.Evolution
open PDE.Analysis.Evolution.IsGelfandIntegratedWeakSolution
open SobolevSpace.GraphSpace

/-- An absolutely continuous Banach-valued curve is strongly measurable and uniformly
bounded on its closed time interval. -/
private theorem measurable_bounded_of_absolutelyContinuous
    {E : Type*} [NormedAddCommGroup E] {g : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AEStronglyMeasurable g (volume.restrict (Icc a b)) ∧
      ∃ M : ℝ≥0, ∀ t ∈ Icc a b, ‖g t‖ ≤ M := by
  have hcontinuous : ContinuousOn g (Icc a b) := by
    simpa only [uIcc_of_le hab] using hg.continuousOn
  let : SecondCountableTopologyEither ℝ E := ⟨Or.inl inferInstance⟩
  refine ⟨hcontinuous.aestronglyMeasurable (μ := volume) measurableSet_Icc, ?_⟩
  obtain ⟨M, hM⟩ := hg.exists_bound
  refine ⟨⟨M, (norm_nonneg (g a)).trans (hM a left_mem_uIcc)⟩, ?_⟩
  intro t ht
  exact hM t (by simpa only [uIcc_of_le hab] using ht)

/-- Absolute continuity and the identified derivative of an `L∞` coefficient matrix
pass to its bounded form. The derivative bound grows by at most `n²`. -/
private theorem coefficient_form_time_regularity
    {n : ℕ} {Ω : Set (ℝ^n)} {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (D : Fin n → U →L[ℝ] DerivLp n 2 Ω) (hD : ∀ i u, ‖D i u‖ ≤ ‖u‖)
    (E : Fin n → W →L[ℝ] DerivLp n 2 Ω) (hE : ∀ i w, ‖E i w‖ ≤ ‖w‖)
    {a b : ℝ}
    (coeff coeffDot : ℝ → Fin n → Fin n → DerivLp n ∞ Ω)
    (hcoeffAC : AbsolutelyContinuousOnInterval coeff a b)
    (hcoeffDeriv : ∀ᵐ t ∂volume.restrict (Ioc a b),
      HasDerivAt coeff (coeffDot t) t)
    (N : ℝ≥0)
    (hcoeffDot : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖coeffDot t‖ ≤ N) :
    let F := multiplicationCoeffFormCLMOf U W D hD E hE
    AbsolutelyContinuousOnInterval (fun t ↦ F (coeff t)) a b ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b),
        HasDerivAt (fun s ↦ F (coeff s)) (F (coeffDot t)) t) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b),
        ‖F (coeffDot t)‖ ≤ (((n : ℝ≥0) ^ 2 * N : ℝ≥0) : ℝ)) := by
  let F := multiplicationCoeffFormCLMOf U W D hD E hE
  refine ⟨?_, ?_, ?_⟩
  · exact LipschitzWith.comp_absolutelyContinuousOnInterval
      (lipschitzWith_multiplicationCoeffFormCLMOf U W D hD E hE) hcoeffAC
  · filter_upwards [hcoeffDeriv] with t ht
    exact hasDerivAt_multiplicationCoeffFormOf U W D hD E hE ht
  · filter_upwards [hcoeffDot] with t ht
    calc
      ‖F (coeffDot t)‖ ≤ (n : ℝ) ^ 2 * ‖coeffDot t‖ :=
        norm_multiplicationCoeffFormOf_le U W D hD E hE (coeffDot t)
      _ ≤ (n : ℝ) ^ 2 * N := mul_le_mul_of_nonneg_left ht (sq_nonneg _)
      _ = (((n : ℝ≥0) ^ 2 * N : ℝ≥0) : ℝ) := by
        simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast]

/-- An absolutely continuous family of symmetric coercive forms with a bounded
almost-everywhere derivative gives the improved Galerkin solution on any stable trial
system. Absolute continuity gives measurability and boundedness of the family, and the
equation holds for a.e. time against every energy-space test function. -/
private theorem exists_symmetric_principal_solution
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace V] [CompleteSpace H]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    (T : GelfandTriple (V := V) (H := H)) (trials : StableTrialSystem T)
    (A Adot : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b C : ℝ} {N : ℝ≥0}
    (hab : a < b) (hC : 0 < C)
    (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt A (Adot t) t)
    (hAdot : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖Adot t‖ ≤ N)
    (hA_symm : ∀ t ∈ Icc a b, ∀ u v : V, A t u v = A t v u)
    (hAprincipal : ∀ t ∈ Icc a b, ∀ w : V, C * ‖w‖ ^ 2 ≤ A t w w) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : Lp H 2 (volume.restrict (Ioc a b))) (uInit : V),
      ∃ (u : Lp V 2 (volume.restrict (Ioc a b)))
        (ut : Lp H 2 (volume.restrict (Ioc a b))),
        IsGelfandIntegratedWeakSolution T A
          (fun t ↦ T.pivotToDual (f t)) u (T.inclusion uInit) ∧
        HasGelfandWeakTimeDerivativeOn T u
          (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) ut) ∧
        (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : V,
          ⟪ut t, T.inclusion v⟫_ℝ + A t (u t) v = ⟪f t, T.inclusion v⟫_ℝ) ∧
        MemLp (u : ℝ → V) ∞ (volume.restrict (Ioc a b)) ∧
        (eLpNormEssSup (u : ℝ → V) (volume.restrict (Ioc a b))).toReal + ‖ut‖ ≤
          K * (‖f‖ + ‖uInit‖) := by
  obtain ⟨hAmeas, MB, hAbound⟩ :=
    @measurable_bounded_of_absolutelyContinuous (V →L[ℝ] StrongDual ℝ V)
      (ContinuousLinearMap.toNormedAddCommGroup
        (E := V) (F := StrongDual ℝ V) (σ₁₂ := RingHom.id ℝ))
      A a b hab.le hAAC
  let Q := ‖A a‖ * (trials.stabilityConstant : ℝ) ^ 2 +
    2 * (1 + (N : ℝ) / 2 * ((2 / C) *
      ((1 / 2 : ℝ) * ‖T.inclusion‖ ^ 2 + (1 / (2 * C)) * ‖T.pivotToDual‖ ^ 2)))
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  refine ⟨Real.sqrt (Q / C) + Real.sqrt Q + 1, by positivity, ?_⟩
  intro f uInit
  obtain ⟨u, ut, hsolution, hderivative, hequation, hut, hstate⟩ :=
    exists_of_symmetric_principal_measurable_galerkin_L2
      T trials.space trials.finiteDimensional trials.projection trials.denseEnergy
      A Adot f hab hC hAmeas MB hAbound uInit hAAC hAderiv hAdot hA_symm hAprincipal
  let D := ‖f‖ + ‖uInit‖
  have hD : 0 ≤ D := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hfD : ‖f‖ ≤ D := le_add_of_nonneg_right (norm_nonneg _)
  have hgD : ‖uInit‖ ≤ D := le_add_of_nonneg_left (norm_nonneg _)
  have hinit : ‖T.inclusion uInit‖ ≤ ‖T.inclusion‖ * D :=
    (T.inclusion.le_opNorm uInit).trans (mul_le_mul_of_nonneg_left hgD (norm_nonneg _))
  have hforce : ‖T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f‖ ≤
      ‖T.pivotToDual‖ * D :=
    (T.pivotToDual.norm_compLp_le f).trans (mul_le_mul_of_nonneg_left hfD (norm_nonneg _))
  let budget := ‖A a‖ * (trials.stabilityConstant * ‖uInit‖) ^ 2 +
    2 * (‖f‖ ^ 2 + (N : ℝ) / 2 * ((2 / C) *
      ((1 / 2 : ℝ) * ‖T.inclusion uInit‖ ^ 2 + (1 / (2 * C)) *
        ‖T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f‖ ^ 2)))
  have hbudget : budget ≤ Q * D ^ 2 := by
    dsimp only [budget]
    calc
      _ ≤ ‖A a‖ * (trials.stabilityConstant * D) ^ 2 +
          2 * (D ^ 2 + (N : ℝ) / 2 * ((2 / C) *
            ((1 / 2 : ℝ) * (‖T.inclusion‖ * D) ^ 2 +
              (1 / (2 * C)) * (‖T.pivotToDual‖ * D) ^ 2))) := by gcongr
      _ = Q * D ^ 2 := by dsimp only [Q]; ring
  have hutBound : ‖ut‖ ≤ Real.sqrt Q * D := by
    have h := Real.sqrt_le_sqrt (hut.trans hbudget)
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hQ, Real.sqrt_sq hD] at h
  have hstateBound : ∀ᵐ t ∂volume.restrict (Ioc a b),
      ‖u t‖ ≤ Real.sqrt (Q / C) * D := by
    filter_upwards [hstate] with t ht
    refine ht.trans ?_
    calc
      Real.sqrt (budget / C) ≤ Real.sqrt (Q * D ^ 2 / C) :=
        Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hbudget hC.le)
      _ = Real.sqrt (Q / C) * D := by
        rw [mul_div_right_comm, Real.sqrt_mul (div_nonneg hQ hC.le), Real.sqrt_sq hD]
  have hsup : (eLpNormEssSup (u : ℝ → V) (volume.restrict (Ioc a b))).toReal ≤
      Real.sqrt (Q / C) * D :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (eLpNormEssSup_le_of_ae_bound hstateBound)).trans_eq
        (ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) hD))
  refine ⟨u, ut, hsolution, hderivative, ?_,
    memLp_top_of_bound (Lp.aestronglyMeasurable u) _ hstateBound, ?_⟩
  · filter_upwards [hequation] with t ht
    intro v
    have hv := congrArg (fun ell : StrongDual ℝ V ↦ ell v) ht
    simpa only [add_apply, GelfandTriple.pivotToDual_apply] using hv
  · change _ ≤ (Real.sqrt (Q / C) + Real.sqrt Q + 1) * D
    nlinarith only [hsup, hutBound, hD]

/-- A symmetric coercive coefficient form on an abstract energy space has the improved
Galerkin solution. Bounded dependence on the coefficients gives its time regularity. -/
private theorem exists_coefficient_form_solution
    {n : ℕ} {Ω : Set (ℝ^n)} {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace V] [CompleteSpace H]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    (T : GelfandTriple (V := V) (H := H)) (trials : StableTrialSystem T)
    (D : Fin n → V →L[ℝ] DerivLp n 2 Ω) (hD : ∀ i v, ‖D i v‖ ≤ ‖v‖)
    {a b C : ℝ} (hab : a < b) (hC : 0 < C)
    (coeff coeffDot : ℝ → Fin n → Fin n → DerivLp n ∞ Ω)
    (hcoeffAC : AbsolutelyContinuousOnInterval coeff a b)
    (hcoeffDeriv : ∀ᵐ t ∂volume.restrict (Ioc a b),
      HasDerivAt coeff (coeffDot t) t)
    (N : ℝ≥0)
    (hcoeffDot : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖coeffDot t‖ ≤ N)
    (hsymm : ∀ t ∈ Icc a b, ∀ u v : V,
      variableCoeffFormOf V V D hD D hD (multiplicationCoefficientOperator (coeff t)) u v =
        variableCoeffFormOf V V D hD D hD (multiplicationCoefficientOperator (coeff t)) v u)
    (hcoercive : ∀ t ∈ Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤
        variableCoeffFormOf V V D hD D hD (multiplicationCoefficientOperator (coeff t)) w w) :
    let A := fun t ↦
      variableCoeffFormOf V V D hD D hD (multiplicationCoefficientOperator (coeff t))
    ∃ K : ℝ, 0 < K ∧ ∀ (f : Lp H 2 (volume.restrict (Ioc a b))) (uInit : V),
      ∃ (u : Lp V 2 (volume.restrict (Ioc a b)))
        (ut : Lp H 2 (volume.restrict (Ioc a b))),
        IsGelfandIntegratedWeakSolution T A
          (fun t ↦ T.pivotToDual (f t)) u (T.inclusion uInit) ∧
        HasGelfandWeakTimeDerivativeOn T u
          (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) ut) ∧
        (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : V,
          ⟪ut t, T.inclusion v⟫_ℝ +
              ∑ i : Fin n, ∑ j : Fin n, ⟪coeff t i j • D j (u t), D i v⟫_ℝ =
            ⟪f t, T.inclusion v⟫_ℝ) ∧
        MemLp (u : ℝ → V) ∞ (volume.restrict (Ioc a b)) ∧
        (eLpNormEssSup (u : ℝ → V) (volume.restrict (Ioc a b))).toReal + ‖ut‖ ≤
          K * (‖f‖ + ‖uInit‖) := by
  obtain ⟨hAAC, hAderiv, hAdot⟩ :=
    coefficient_form_time_regularity D hD D hD
      coeff coeffDot hcoeffAC hcoeffDeriv N hcoeffDot
  obtain ⟨K, hK, hsolve⟩ :=
    exists_symmetric_principal_solution T trials
      (fun t ↦ multiplicationCoeffFormCLMOf V V D hD D hD (coeff t))
      (fun t ↦ multiplicationCoeffFormCLMOf V V D hD D hD (coeffDot t))
      hab hC hAAC hAderiv hAdot hsymm hcoercive
  refine ⟨K, hK, ?_⟩
  intro f uInit
  obtain ⟨u, ut, hsolution, hderivative, hequation, hstate, hbound⟩ := hsolve f uInit
  refine ⟨u, ut, hsolution, hderivative, ?_, hstate, hbound⟩
  filter_upwards [hequation] with t ht
  intro v
  simpa only [multiplicationCoeffFormCLMOf_apply, variableCoeffFormOf_apply,
    multiplicationCoefficientOperator_apply] using ht v

section Sobolev

-- Use the cached `H¹₀` normed group and inner product instances.
attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

/-- The normed-space structure induced by the cached `H¹₀` inner product. -/
local instance nonautonomousH10NormedSpace {n : ℕ} {Ω : Set (ℝ^n)} :
    NormedSpace ℝ (H¹₀(Ω)) :=
  (h10InnerProductSpace (n := n) (Ω := Ω)).toNormedSpace

/-- A symmetric uniformly elliptic `L∞` coefficient matrix that is absolutely continuous
in time, with an identified essentially bounded `L∞` derivative, admits a weak Dirichlet
solution with `L²_t L²_x` time derivative and `L∞_t H¹₀` state.

The norm estimate for the state and its time derivative has a constant fixed before
both data. The same witnesses satisfy the integrated initial-value problem and,
almost everywhere in time, the spatial variational equation for every `H¹₀` test. -/
theorem exists_nonautonomous_symmetric_solution_with_l2_time_derivative_data_bounds
    {n : ℕ} {Ω : Set (ℝ^n)} (hn : 0 < n)
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    {a b : ℝ} (hab : a < b)
    (coeff coeffDot : ℝ → Fin n → Fin n → DerivLp n ∞ Ω)
    (hcoeffAC : AbsolutelyContinuousOnInterval coeff a b)
    (hcoeffDeriv : ∀ᵐ t ∂volume.restrict (Ioc a b),
      HasDerivAt coeff (coeffDot t) t)
    (N : ℝ≥0)
    (hcoeffDot : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖coeffDot t‖ ≤ N)
    (hsymm : ∀ t ∈ Icc a b, AESymmetricCoefficient (coeff t))
    {alpha : ℝ}
    (hElliptic : ∀ t ∈ Icc a b, AEUniformlyElliptic (coeff t) alpha) :
    let T := h10L2GelfandTriple hΩopen
    ∃ K : ℝ, 0 < K ∧
      ∀ (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))) (uInit : H¹₀(Ω)),
        ∃ (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
          (ut : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))),
          IsGelfandIntegratedWeakSolution T
            (fun t ↦ variableCoeffForm (multiplicationCoefficientOperator (coeff t)))
            (fun t ↦ T.pivotToDual (f t)) u (T.inclusion uInit) ∧
          HasGelfandWeakTimeDerivativeOn T u
            (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) ut) ∧
          (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : H¹₀(Ω),
            ⟪ut t, baseCoordCLM v⟫_ℝ +
                ∑ i : Fin n, ∑ j : Fin n,
                  ⟪coeff t i j • derivCoordCLM j ((u : ℝ → H¹₀(Ω)) t),
                    derivCoordCLM i v⟫_ℝ =
              ⟪f t, baseCoordCLM v⟫_ℝ) ∧
          MemLp (u : ℝ → H¹₀(Ω)) ∞ (volume.restrict (Ioc a b)) ∧
          (eLpNormEssSup (u : ℝ → H¹₀(Ω)) (volume.restrict (Ioc a b))).toReal + ‖ut‖ ≤
            K * (‖f‖ + ‖uInit‖) := by
  obtain ⟨C, hC, hAprincipal⟩ :=
    exists_uniform_coercivity_coefficient_forms hn hΩbounded hab coeff hElliptic
  exact exists_coefficient_form_solution
    (h10L2GelfandTriple hΩopen) (h10L2SpectralTrialSystem hΩopen hΩbounded)
    (fun i ↦ derivCoordCLM (n := n) (Ω := Ω) i)
    (fun i v ↦ derivCoordCLM_norm_le i v) hab hC
    coeff coeffDot hcoeffAC hcoeffDeriv N hcoeffDot
    (fun t ht u v ↦ variableCoeffForm_symm
      (symmetricCoefficientOperator_multiplication_of_ae (coeff t) (hsymm t ht)) u v)
    hAprincipal

/-- A symmetric uniformly elliptic `L∞` coefficient matrix that is absolutely continuous
in time, with an identified essentially bounded `L∞` derivative, admits a weak Dirichlet
solution with `L²_t L²_x` time derivative and `L∞_t H¹₀` state.

The same witnesses satisfy the integrated initial-value problem and, almost everywhere
in time, the concrete spatial variational equation for every `H¹₀` test function. -/
theorem exists_nonautonomous_symmetric_solution_with_l2_time_derivative
    {n : ℕ} {Ω : Set (ℝ^n)} (hn : 0 < n)
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    {a b : ℝ} (hab : a < b)
    (coeff coeffDot : ℝ → Fin n → Fin n → DerivLp n ∞ Ω)
    (hcoeffAC : AbsolutelyContinuousOnInterval coeff a b)
    (hcoeffDeriv : ∀ᵐ t ∂volume.restrict (Ioc a b),
      HasDerivAt coeff (coeffDot t) t)
    (N : ℝ≥0)
    (hcoeffDot : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖coeffDot t‖ ≤ N)
    (hsymm : ∀ t ∈ Icc a b, AESymmetricCoefficient (coeff t))
    {alpha : ℝ}
    (hElliptic : ∀ t ∈ Icc a b, AEUniformlyElliptic (coeff t) alpha)
    (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
    (uInit : H¹₀(Ω)) :
    let T := h10L2GelfandTriple hΩopen
    ∃ (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
      (ut : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))),
      IsGelfandIntegratedWeakSolution T
        (fun t ↦ variableCoeffForm (multiplicationCoefficientOperator (coeff t)))
        (fun t ↦ T.pivotToDual (f t)) u (T.inclusion uInit) ∧
      HasGelfandWeakTimeDerivativeOn T u
        (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) ut) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : H¹₀(Ω),
        ⟪ut t, baseCoordCLM v⟫_ℝ +
            ∑ i : Fin n, ∑ j : Fin n,
              ⟪coeff t i j • derivCoordCLM j ((u : ℝ → H¹₀(Ω)) t),
                derivCoordCLM i v⟫_ℝ =
          ⟪f t, baseCoordCLM v⟫_ℝ) ∧
      MemLp (u : ℝ → H¹₀(Ω)) ∞ (volume.restrict (Ioc a b)) := by
  obtain ⟨_, _, hsolve⟩ :=
    exists_nonautonomous_symmetric_solution_with_l2_time_derivative_data_bounds
      hn hΩopen hΩbounded hab coeff coeffDot hcoeffAC hcoeffDeriv N hcoeffDot hsymm hElliptic
  obtain ⟨u, ut, hu, hut, heq, hstate, _⟩ := hsolve f uInit
  exact ⟨u, ut, hu, hut, heq, hstate⟩

end Sobolev

open SobolevSpace SobolevSpace.GraphSpace.BoundaryRegularity

/-- A symmetric time-dependent divergence equation admits a weak Dirichlet solution
in `L²_t H²_x ∩ L∞_t H¹₀`, with `uₜ ∈ L²_t L²_x`, from coefficient and domain data.

The coefficients are continuous in time in the spatial `W¹,∞` norm, have `C¹`
spatial representatives on the time slab, and their base coordinates are absolutely
continuous in `L∞`, with an essentially bounded identified time derivative.
The domain is bounded and open with a geometric `C²` graph boundary.

The proof first constructs the time-regular weak solution and then its spatial
lift. The full `H¹` restriction of the lift agrees with the original solution,
so the conclusion retains both its spatial derivatives and its zero boundary trace.
A positive constant, chosen before the forcing and initial datum, bounds the sum
of the three regularity norms by the norms of these data. It also bounds the spatial
lift by the elliptic residual `f - uₜ`. -/
theorem exists_nonautonomous_symmetric_solution_with_spatial_h2_data_bounds
    {n : ℕ} {Ω : Set (ℝ^n)} (hn : 0 < n)
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    {t₀ t₁ : ℝ} (htime : t₀ < t₁)
    (A : ℝ → Fin n → Fin n → W^{1,∞}(Ω))
    (hA : ContinuousOn A (Icc t₀ t₁))
    (a : ℝ → ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ t ∈ Icc t₀ t₁, ∀ i j,
      ⇑((A t i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1))
        =ᵐ[domainMeasure n Ω] fun x ↦ a t x i j)
    (haC1 : ∀ t ∈ Icc t₀ t₁, ∀ i j, ContDiff ℝ 1 (fun x ↦ a t x i j))
    (coeffDot : ℝ → Fin n → Fin n → DerivLp n ∞ Ω)
    (hcoeffAC : AbsolutelyContinuousOnInterval (fun t ↦ coefficientBase (A t)) t₀ t₁)
    (hcoeffDeriv : ∀ᵐ t ∂volume.restrict (Ioc t₀ t₁),
      HasDerivAt (fun s ↦ coefficientBase (A s)) (coeffDot t) t)
    (N : ℝ≥0)
    (hcoeffDot : ∀ᵐ t ∂volume.restrict (Ioc t₀ t₁), ‖coeffDot t‖ ≤ N)
    (hsymm : ∀ t ∈ Icc t₀ t₁, ∀ x ∈ Ω, ∀ i j, a t x i j = a t x j i)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ t ∈ Icc t₀ t₁, ∀ x ∈ Ω,
      MatrixEllipticLowerBound (a t x) alpha) :
    let T := h10L2GelfandTriple hΩopen
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc t₀ t₁)))
        (uInit : H¹₀(Ω)),
        ∃ (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc t₀ t₁)))
          (ut : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc t₀ t₁)))
          (U : Lp (W^{2,2}(Ω)) 2 (volume.restrict (Ioc t₀ t₁))),
          IsGelfandIntegratedWeakSolution T
            (fun t ↦ variableCoeffForm (multiplicationCoefficientOperator (coefficientBase (A t))))
            (fun t ↦ T.pivotToDual (f t)) u (T.inclusion uInit) ∧
          HasGelfandWeakTimeDerivativeOn T u
            (T.pivotToDual.compLpL 2 (volume.restrict (Ioc t₀ t₁)) ut) ∧
          (∀ᵐ t ∂volume.restrict (Ioc t₀ t₁), ∀ v : H¹₀(Ω),
            ⟪ut t, baseCoordCLM v⟫_ℝ +
              variableCoeffForm (multiplicationCoefficientOperator (coefficientBase (A t)))
                (u t) v = ⟪f t, baseCoordCLM v⟫_ℝ) ∧
          MemLp (u : ℝ → H¹₀(Ω)) ∞ (volume.restrict (Ioc t₀ t₁)) ∧
          ((fun t ↦ lowerOrderCLM (k := 1) (m := 2) (by omega) (U t))
            =ᵐ[volume.restrict (Ioc t₀ t₁)] fun t ↦ h10SubtypeL (u t)) ∧
          ‖U‖ ≤ C * ‖f - ut‖ ∧
          (eLpNormEssSup (u : ℝ → H¹₀(Ω)) (volume.restrict (Ioc t₀ t₁))).toReal +
              ‖ut‖ + ‖U‖ ≤ C * (‖f‖ + ‖uInit‖) := by
  let : Fact (0 < n) := ⟨hn⟩
  let atlas := hgraph.c2BoundaryAtlas le_rfl hΩopen hΩbounded
  obtain ⟨C, hC, hlift⟩ :=
    exists_nonautonomous_spatial_h2_lp_of_ae_weak_residual_identity
      atlas htime.le A hA a haRep haC1 alpha halpha hElliptic
  obtain ⟨K, hK, hsolve⟩ :=
    exists_nonautonomous_symmetric_solution_with_l2_time_derivative_data_bounds
      hn hΩopen hΩbounded htime (fun t ↦ coefficientBase (A t)) coeffDot
      hcoeffAC hcoeffDeriv N hcoeffDot
      (fun t ht ↦ coefficientBase_aeSymmetric hΩopen.measurableSet
        (A t) (a t) (haRep t ht) (hsymm t ht))
      (fun t ht ↦ coefficientBase_aeUniformlyElliptic hΩopen.measurableSet
        (A t) (a t) (haRep t ht) alpha halpha (hElliptic t ht))
  refine ⟨max C (K + C * (1 + K)), hC.trans_le (le_max_left _ _), ?_⟩
  intro f uInit
  obtain ⟨u, ut, hu, hut, hresidual, hstate, hbound⟩ := hsolve f uInit
  have hresidual' : ∀ᵐ t ∂volume.restrict (Ioc t₀ t₁), ∀ v : H¹₀(Ω),
      ⟪ut t, baseCoordCLM v⟫_ℝ +
        variableCoeffForm (multiplicationCoefficientOperator (coefficientBase (A t))) (u t) v =
          ⟪f t, baseCoordCLM v⟫_ℝ := by
    filter_upwards [hresidual] with t ht
    intro v
    simpa only [variableCoeffForm_apply, multiplicationCoefficientOperator_apply] using ht v
  obtain ⟨U, hU, hnorm⟩ := hlift f ut u hresidual'
  have hutNorm : ‖ut‖ ≤ K * (‖f‖ + ‖uInit‖) :=
    (le_add_of_nonneg_left ENNReal.toReal_nonneg).trans hbound
  have hresidualNorm : ‖f - ut‖ ≤ (1 + K) * (‖f‖ + ‖uInit‖) := by
    calc
      ‖f - ut‖ ≤ ‖f‖ + ‖ut‖ := norm_sub_le f ut
      _ ≤ (‖f‖ + ‖uInit‖) + K * (‖f‖ + ‖uInit‖) :=
        add_le_add (le_add_of_nonneg_right (norm_nonneg _)) hutNorm
      _ = (1 + K) * (‖f‖ + ‖uInit‖) := by rw [add_mul, one_mul]
  refine ⟨u, ut, U, hu, hut, hresidual', hstate, hU, ?_, ?_⟩
  · exact hnorm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · calc
      _ ≤ K * (‖f‖ + ‖uInit‖) + C * ((1 + K) * (‖f‖ + ‖uInit‖)) :=
        add_le_add hbound (hnorm.trans (mul_le_mul_of_nonneg_left hresidualNorm hC.le))
      _ = (K + C * (1 + K)) * (‖f‖ + ‖uInit‖) := by ring
      _ ≤ max C (K + C * (1 + K)) * (‖f‖ + ‖uInit‖) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- A symmetric time-dependent divergence equation admits a weak Dirichlet solution
in `L²_t H²_x ∩ L∞_t H¹₀`, with `uₜ ∈ L²_t L²_x`, from coefficient and domain data.

The coefficients are continuous in time in the spatial `W¹,∞` norm, have `C¹`
spatial representatives on the time slab, and their base coordinates are absolutely
continuous in `L∞`, with an essentially bounded identified time derivative.
The domain is bounded and open with a geometric `C²` graph boundary.

The proof first constructs the time-regular weak solution and then its spatial
lift. The full `H¹` restriction of the lift agrees with the original solution,
so the conclusion retains both its spatial derivatives and its zero boundary trace.
The positive elliptic constant is chosen before the forcing and initial datum. -/
theorem exists_nonautonomous_symmetric_solution_with_spatial_h2
    {n : ℕ} {Ω : Set (ℝ^n)} (hn : 0 < n)
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    {t₀ t₁ : ℝ} (htime : t₀ < t₁)
    (A : ℝ → Fin n → Fin n → W^{1,∞}(Ω))
    (hA : ContinuousOn A (Icc t₀ t₁))
    (a : ℝ → ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ t ∈ Icc t₀ t₁, ∀ i j,
      ⇑((A t i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1))
        =ᵐ[domainMeasure n Ω] fun x ↦ a t x i j)
    (haC1 : ∀ t ∈ Icc t₀ t₁, ∀ i j, ContDiff ℝ 1 (fun x ↦ a t x i j))
    (coeffDot : ℝ → Fin n → Fin n → DerivLp n ∞ Ω)
    (hcoeffAC : AbsolutelyContinuousOnInterval (fun t ↦ coefficientBase (A t)) t₀ t₁)
    (hcoeffDeriv : ∀ᵐ t ∂volume.restrict (Ioc t₀ t₁),
      HasDerivAt (fun s ↦ coefficientBase (A s)) (coeffDot t) t)
    (N : ℝ≥0)
    (hcoeffDot : ∀ᵐ t ∂volume.restrict (Ioc t₀ t₁), ‖coeffDot t‖ ≤ N)
    (hsymm : ∀ t ∈ Icc t₀ t₁, ∀ x ∈ Ω, ∀ i j, a t x i j = a t x j i)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ t ∈ Icc t₀ t₁, ∀ x ∈ Ω,
      MatrixEllipticLowerBound (a t x) alpha) :
    let T := h10L2GelfandTriple hΩopen
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc t₀ t₁)))
        (uInit : H¹₀(Ω)),
        ∃ (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc t₀ t₁)))
          (ut : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc t₀ t₁)))
          (U : Lp (W^{2,2}(Ω)) 2 (volume.restrict (Ioc t₀ t₁))),
          IsGelfandIntegratedWeakSolution T
            (fun t ↦ variableCoeffForm (multiplicationCoefficientOperator (coefficientBase (A t))))
            (fun t ↦ T.pivotToDual (f t)) u (T.inclusion uInit) ∧
          HasGelfandWeakTimeDerivativeOn T u
            (T.pivotToDual.compLpL 2 (volume.restrict (Ioc t₀ t₁)) ut) ∧
          (∀ᵐ t ∂volume.restrict (Ioc t₀ t₁), ∀ v : H¹₀(Ω),
            ⟪ut t, baseCoordCLM v⟫_ℝ +
              variableCoeffForm (multiplicationCoefficientOperator (coefficientBase (A t)))
                (u t) v = ⟪f t, baseCoordCLM v⟫_ℝ) ∧
          MemLp (u : ℝ → H¹₀(Ω)) ∞ (volume.restrict (Ioc t₀ t₁)) ∧
          ((fun t ↦ lowerOrderCLM (k := 1) (m := 2) (by omega) (U t))
            =ᵐ[volume.restrict (Ioc t₀ t₁)] fun t ↦ h10SubtypeL (u t)) ∧
          ‖U‖ ≤ C * ‖f - ut‖ := by
  obtain ⟨C, hC, hsolve⟩ :=
    exists_nonautonomous_symmetric_solution_with_spatial_h2_data_bounds
      hn hΩopen hΩbounded hgraph htime A hA a haRep haC1 coeffDot hcoeffAC hcoeffDeriv
      N hcoeffDot hsymm alpha halpha hElliptic
  refine ⟨C, hC, ?_⟩
  intro f uInit
  obtain ⟨u, ut, U, hu, hut, hresidual, hstate, hU, hnorm, _⟩ := hsolve f uInit
  exact ⟨u, ut, U, hu, hut, hresidual, hstate, hU, hnorm⟩

end PDE.Parabolic.DivergenceFormHeat
