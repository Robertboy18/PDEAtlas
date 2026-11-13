/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.OperatorFamily
public import PDE.Parabolic.Regularity.Nonautonomous.Existence
public import PDE.Parabolic.Regularity.Nonautonomous.LowerOrder.Coefficients
public import PDE.Parabolic.Regularity.Nonautonomous.LowerOrder.Garding
import PDE.Analysis.Evolution.Integrated.Uniqueness

/-!
# Nonautonomous `H²` regularity with bounded drift and potential

Consider the zero Dirichlet problem

`uₜ - ∑ᵢⱼ ∂ᵢ(aᵢⱼ(t,x) ∂ⱼu) + b(t,x) · Du + c(t,x)u = f`.

The principal matrix has the symmetry, ellipticity, and time and spatial regularity
used by the principal-part `H²` theorem. The drift and potential are merely jointly
measurable and bounded, with arbitrary signs and no smallness condition.

First the Gårding construction supplies a full weak solution with an `L² H¹₀` bound.
Its lower-order expression is therefore an `L² L²` load. Moving that expression to
the forcing and applying principal-part uniqueness identifies the same solution with
the time-regular solution and its spatial `H²` lift. The equality of the full `H¹`
restrictions retains the zero trace; no solution or elliptic lift is assumed.
-/

@[expose] public noncomputable section

open scoped Sobolev
open MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace

namespace PDE.Parabolic.DivergenceFormHeat.LowerOrder

open PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.BoundaryRegularity

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace
attribute [local instance] nonautonomousH10NormedSpace

private theorem principal_form_bounds
    {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ} (hab : a ≤ b)
    (coeff : ℝ → Fin n → Fin n → DerivLp n ∞ Ω)
    (hcoeff : AbsolutelyContinuousOnInterval coeff a b) :
    let P := fun t ↦ variableCoeffForm (multiplicationCoefficientOperator (coeff t))
    (∀ v, AEStronglyMeasurable (fun t ↦ P t v) (volume.restrict (Ioc a b))) ∧
      ∃ M : ℝ≥0, ∀ᵐ t ∂volume.restrict (Ioc a b), ‖P t‖ ≤ M := by
  let P := fun t ↦ variableCoeffForm (multiplicationCoefficientOperator (coeff t))
  have hPc : ContinuousOn P (Icc a b) := by
    have hc : ContinuousOn coeff (Icc a b) := by
      simpa only [uIcc_of_le hab] using hcoeff.continuousOn
    let F := multiplicationCoeffFormCLMOf (H¹₀(Ω)) (H¹₀(Ω))
      derivCoordCLM derivCoordCLM_norm_le derivCoordCLM derivCoordCLM_norm_le
    exact F.continuous.comp_continuousOn hc
  refine ⟨?_, ?_⟩
  · intro v
    let : SecondCountableTopologyEither ℝ (StrongDual ℝ (H¹₀(Ω))) :=
      ⟨Or.inl inferInstance⟩
    have hv := (hPc.clm_apply (g := fun _ ↦ v) continuousOn_const).mono Ioc_subset_Icc_self
    exact hv.aestronglyMeasurable measurableSet_Ioc
  · obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (E := H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω))) hPc
    refine ⟨⟨max M 0, le_max_right _ _⟩, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hM t (Ioc_subset_Icc_self ht)).trans (le_max_left _ _)

private theorem exists_lower_order_load
    {n : ℕ} {Ω : Set (ℝ^n)} {μ : Measure ℝ}
    (L : BoundedCoefficients n Ω μ) (u : Lp (H¹₀(Ω)) 2 μ) :
    ∃ r : Lp (DerivLp n 2 Ω) 2 μ,
      (r : ℝ → DerivLp n 2 Ω) =ᵐ[μ] (fun t ↦ L.operator t (u t)) ∧
        ‖r‖ ≤ L.operatorBound * ‖u‖ := by
  have hmem := (Lp.memLp u).operatorFamily L.operator
    L.aestronglyMeasurable_operator_apply L.operatorBound
    (Filter.Eventually.of_forall L.norm_operator_le)
  let r : Lp (DerivLp n 2 Ω) 2 μ := hmem.toLp (fun t ↦ L.operator t (u t))
  have hr : (r : ℝ → DerivLp n 2 Ω) =ᵐ[μ] fun t ↦ L.operator t (u t) :=
    hmem.coeFn_toLp
  refine ⟨r, hr, ?_⟩
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hr] with t ht
  rw [ht]
  exact ((L.operator t).le_opNorm (u t)).trans
    (mul_le_mul_of_nonneg_right (L.norm_operator_le t) (norm_nonneg _))

private theorem eq_principal_state
    {n : ℕ} {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω) {a b : ℝ} (hab : a < b)
    (P : ℝ → H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)))
    (R : ℝ → H¹₀(Ω) →L[ℝ] DerivLp n 2 Ω)
    (hPm : ∀ v, AEStronglyMeasurable (fun t ↦ P t v) (volume.restrict (Ioc a b)))
    (M : ℝ≥0) (hPb : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖P t‖ ≤ M)
    (hpos : ∀ t ∈ Icc a b, ∀ v, 0 ≤ P t v v)
    (f r : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))) (g : H¹₀(Ω))
    (u q : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (hr : (r : ℝ → DerivLp n 2 Ω) =ᵐ[volume.restrict (Ioc a b)] fun t ↦ R t (u t))
    (hu : IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hΩ)
      (fun t ↦ P t + (h10L2GelfandTriple hΩ).pivotToDual.comp (R t))
      ((h10L2GelfandTriple hΩ).pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f)
      u ((h10L2GelfandTriple hΩ).inclusion g))
    (hq : IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hΩ) P
      (fun t ↦ (h10L2GelfandTriple hΩ).pivotToDual ((f - r) t))
      q ((h10L2GelfandTriple hΩ).inclusion g)) :
    q = u := by
  let T := h10L2GelfandTriple hΩ
  exact IsGelfandIntegratedWeakSolution.unique (T := T) (B := P) hPm M hPb hpos
    (hq.congr_forcing_ae (T.pivotToDual.coeFn_compLpL (f - r)).symm)
    (hu.sub_timeDependent_pivot_perturbation P R hPm M hPb hr) hab

/-- A unique weak Dirichlet solution with an `L² L²` time derivative and an `L² H²`
lift, satisfying one bound for its three regularity norms. The lift agrees with the
state in the full `H¹` space, so its boundary trace is zero.

This predicate records all witnesses and conclusions; it makes no existence or
regularity assumption. The integrated equation retains the specified initial datum. -/
def HasSpatialH2SolutionWithBound
    {n : ℕ} {Ω : Set (ℝ^n)} (hΩopen : IsOpen Ω) {t₀ t₁ : ℝ}
    (B : ℝ → H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω))) (C : ℝ)
    (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc t₀ t₁))) (uInit : H¹₀(Ω)) :
    Prop :=
  let T := h10L2GelfandTriple hΩopen
  ∃ (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc t₀ t₁)))
    (ut : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc t₀ t₁)))
    (U : Lp (W^{2,2}(Ω)) 2 (volume.restrict (Ioc t₀ t₁))),
    IsGelfandIntegratedWeakSolution T B
      (fun t ↦ T.pivotToDual (f t)) u (T.inclusion uInit) ∧
    HasGelfandWeakTimeDerivativeOn T u
      (T.pivotToDual.compLpL 2 (volume.restrict (Ioc t₀ t₁)) ut) ∧
    (∀ᵐ t ∂volume.restrict (Ioc t₀ t₁), ∀ v : H¹₀(Ω),
      ⟪ut t, baseCoordCLM v⟫_ℝ + B t (u t) v = ⟪f t, baseCoordCLM v⟫_ℝ) ∧
    MemLp (u : ℝ → H¹₀(Ω)) ∞ (volume.restrict (Ioc t₀ t₁)) ∧
    ((fun t ↦ lowerOrderCLM (k := 1) (m := 2) (by decide) (U t))
      =ᵐ[volume.restrict (Ioc t₀ t₁)] fun t ↦ h10SubtypeL (u t)) ∧
    (eLpNormEssSup (u : ℝ → H¹₀(Ω)) (volume.restrict (Ioc t₀ t₁))).toReal +
        ‖ut‖ + ‖U‖ ≤ C * (‖f‖ + ‖uInit‖) ∧
    (∀ v : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc t₀ t₁)),
      IsGelfandIntegratedWeakSolution T B
        (fun t ↦ T.pivotToDual (f t)) v (T.inclusion uInit) → v = u)

section Existence

variable
    {n : ℕ} {Ω : Set (ℝ^n)} (hn : 0 < n)
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    {t₀ t₁ : ℝ} (htime : t₀ < t₁)

variable
    (A : ℝ → Fin n → Fin n → W^{1,∞}(Ω))
    (hA : ContinuousOn A (Icc t₀ t₁))
    (a : ℝ → ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ t ∈ Icc t₀ t₁, ∀ i j,
      ⇑((A t i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1))
        =ᵐ[domainMeasure n Ω] fun x ↦ a t x i j)
    (haC1 : ∀ t ∈ Icc t₀ t₁, ∀ i j, ContDiff ℝ 1 (fun x ↦ a t x i j))

variable
    (coeffDot : ℝ → Fin n → Fin n → DerivLp n ∞ Ω)
    (hcoeffAC : AbsolutelyContinuousOnInterval (fun t ↦ coefficientBase (A t)) t₀ t₁)
    (hcoeffDeriv : ∀ᵐ t ∂volume.restrict (Ioc t₀ t₁),
      HasDerivAt (fun s ↦ coefficientBase (A s)) (coeffDot t) t)
    (N : ℝ≥0)
    (hcoeffDot : ∀ᵐ t ∂volume.restrict (Ioc t₀ t₁), ‖coeffDot t‖ ≤ N)

variable
    (hsymm : ∀ t ∈ Icc t₀ t₁, ∀ x ∈ Ω, ∀ i j, a t x i j = a t x j i)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ t ∈ Icc t₀ t₁, ∀ x ∈ Ω,
      MatrixEllipticLowerBound (a t x) alpha)
    (L : BoundedCoefficients n Ω (volume.restrict (Ioc t₀ t₁)))

include hn hΩopen hΩbounded hgraph htime A hA a haRep haC1 coeffDot
  hcoeffAC hcoeffDeriv N hcoeffDot hsymm alpha halpha hElliptic L

/-- A symmetric uniformly elliptic nonautonomous principal part with arbitrary bounded
measurable drift and potential admits a unique weak Dirichlet solution in
`L∞ H¹₀ ∩ L² H²`, with time derivative in `L² L²`.

The positive estimate constant is chosen before both the `L² L²` forcing and the
`H¹₀` initial datum. The spatial lift agrees in `H¹` with the original zero-trace
state. Only the principal coefficients have time derivatives or spatial regularity;
the lower-order coefficients have no sign, smallness, or time-continuity requirement. -/
theorem exists_solution_with_spatial_h2_data_bounds :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc t₀ t₁)))
        (uInit : H¹₀(Ω)),
        HasSpatialH2SolutionWithBound hΩopen
          (L.form (fun t ↦ coefficientBase (A t))) C f uInit := by
  let T := h10L2GelfandTriple hΩopen
  let μ := volume.restrict (Ioc t₀ t₁)
  let P := fun t ↦ variableCoeffForm (multiplicationCoefficientOperator (coefficientBase (A t)))
  obtain ⟨hPm, MP, hPb⟩ :=
    principal_form_bounds htime.le (fun t ↦ coefficientBase (A t)) hcoeffAC
  obtain ⟨c₀, hc₀, hcoercive⟩ :=
    exists_uniform_coercivity_coefficient_forms hn hΩbounded htime
      (fun t ↦ coefficientBase (A t))
      (fun t ht ↦ coefficientBase_aeUniformlyElliptic hΩopen.measurableSet
        (A t) (a t) (haRep t ht) alpha halpha (hElliptic t ht))
  have hRb : ∀ᵐ t ∂μ, ‖L.operator t‖ ≤ L.operatorBound :=
    Filter.Eventually.of_forall L.norm_operator_le
  obtain ⟨K₀, hK₀, hbasic⟩ := exists_solution_with_state_bound hΩopen hΩbounded
    P L.operator hc₀ htime hcoercive hPm MP hPb
    L.aestronglyMeasurable_operator_apply L.operatorBound hRb
  obtain ⟨K₁, hK₁, hprincipal⟩ :=
    exists_nonautonomous_symmetric_solution_with_spatial_h2_data_bounds
      hn hΩopen hΩbounded hgraph htime A hA a haRep haC1 coeffDot hcoeffAC
      hcoeffDeriv N hcoeffDot hsymm alpha halpha hElliptic
  refine ⟨K₁ * (1 + L.operatorBound * K₀), by positivity, ?_⟩
  intro f uInit
  obtain ⟨u, hu, hunique, hunorm⟩ := hbasic f uInit
  obtain ⟨r, hr, hrnorm⟩ := exists_lower_order_load L u
  obtain ⟨q, ut, U, hq, hqt, hresidual, hstate, hlift, _, hnorm⟩ :=
    hprincipal (f - r) uInit
  have hqu : q = u := eq_principal_state hΩopen htime P L.operator hPm MP hPb
    (fun t ht v ↦ (mul_nonneg hc₀.le (sq_nonneg _)).trans (hcoercive t ht v))
    f r uInit u q hr hu hq
  rw [hqu] at hqt hresidual hstate hlift hnorm
  have hform : L.form (fun t ↦ coefficientBase (A t)) =
      fun t ↦ P t + T.pivotToDual.comp (L.operator t) :=
    funext fun t ↦ L.form_eq_principal_add_pivot hΩopen _ t
  refine ⟨u, ut, U, ?_, hqt, ?_, hstate, hlift, ?_, ?_⟩
  · rw [hform]
    exact hu.congr_forcing_ae (T.pivotToDual.coeFn_compLpL f)
  · filter_upwards [hresidual, Lp.coeFn_sub f r, hr] with t ht hsub hrt
    intro v
    have heq := ht v
    rw [hsub, Pi.sub_apply, hrt, inner_sub_left] at heq
    rw [L.form_eq_principal_add_pivot hΩopen]
    change ⟪ut t, baseCoordCLM v⟫_ℝ +
      (P t (u t) v + ⟪L.operator t (u t), baseCoordCLM v⟫_ℝ) =
        ⟪f t, baseCoordCLM v⟫_ℝ
    change ⟪ut t, baseCoordCLM v⟫_ℝ + P t (u t) v =
      ⟪f t, baseCoordCLM v⟫_ℝ - ⟪L.operator t (u t), baseCoordCLM v⟫_ℝ at heq
    linarith
  · have hr' := hrnorm.trans (mul_le_mul_of_nonneg_left hunorm L.operatorBound.2)
    have hforcing : ‖f - r‖ + ‖uInit‖ ≤ (1 + L.operatorBound * K₀) * (‖f‖ + ‖uInit‖) := by
      linarith [norm_sub_le f r]
    exact hnorm.trans ((mul_le_mul_of_nonneg_left hforcing hK₁.le).trans_eq
      (mul_assoc _ _ _).symm)
  · intro v hv
    rw [hform] at hv
    exact hunique v (hv.congr_forcing_ae (T.pivotToDual.coeFn_compLpL f).symm)

end Existence

end PDE.Parabolic.DivergenceFormHeat.LowerOrder
