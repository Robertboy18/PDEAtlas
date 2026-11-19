/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.AbsoluteContinuity
public import PDE.Elliptic.Variational.DivergenceSolution
public import PDE.Elliptic.Variational.LowerOrderDependence
public import PDE.Hyperbolic.WeakWave.Compactness.Nonautonomous
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2

/-!
# Weak waves from time-dependent `L∞` coefficients

A symmetric uniformly elliptic principal matrix, absolutely continuous in `L∞`
with a bounded identified norm derivative, determines the principal wave form.
Drift and potential need only strong measurability in `L∞` and a uniform bound.
The coefficient-to-form maps supply all operator bounds and measurability.

Poincaré coercivity and the compact Sobolev Gelfand inclusion feed the
nonautonomous Galerkin construction. The result keeps both initial values,
`L∞` energy-space bounds and dual acceleration for arbitrary `H¹₀ × L²` data and
`L²` pivot forcing.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open Hyperbolic.Variational
open scoped ENNReal NNReal

/-- A bound for the drift and potential controls both the operator norm and the
work pairing against the spatial `L²` component. No sign condition is needed. -/
private theorem multiplication_lower_form_bounds
    {n : ℕ} {Ω : Set (ℝ^n)}
    (z : (Fin n → DerivLp n ∞ Ω) × DerivLp n ∞ Ω)
    (Z : ℝ≥0) (hz : ‖z‖ ≤ Z) :
    ‖lowerOrderForm (fun i ↦ mulLpLeft (z.1 i)) (mulLpLeft z.2)‖ ≤
        ((n : ℝ) + 1) * Z ∧
      ∀ u v : H¹₀(Ω),
        |lowerOrderForm (fun i ↦ mulLpLeft (z.1 i)) (mulLpLeft z.2) u v| ≤
          (((n : ℝ) + 1) * Z) * ‖u‖ * ‖baseCoordCLM v‖ := by
  have hsum : (∑ i : Fin n, ‖z.1 i‖) + ‖z.2‖ ≤ ((n : ℝ) + 1) * Z := by
    calc
      _ ≤ (∑ _i : Fin n, (Z : ℝ)) + Z :=
        add_le_add (Finset.sum_le_sum fun i _ ↦
          ((norm_le_pi_norm z.1 i).trans (norm_fst_le z)).trans hz)
          ((norm_snd_le z).trans hz)
      _ = ((n : ℝ) + 1) * Z := by simp [add_mul]
  constructor
  · exact (norm_multiplicationLowerOrderFormOf_le (H¹₀(Ω))
      (fun i ↦ derivCoordCLM i) derivCoordCLM_norm_le
      baseCoordCLM baseCoordCLM_norm_le z.1 z.2).trans hsum
  · intro u v
    have hbase : |lowerOrderForm (fun i ↦ mulLpLeft (z.1 i)) (mulLpLeft z.2) u v| ≤
        ((∑ i : Fin n, ‖z.1 i‖) + ‖z.2‖) * ‖u‖ * ‖baseCoordCLM v‖ := by
      unfold lowerOrderForm
      simpa only [Real.norm_eq_abs] using
        norm_multiplicationLowerOrderFormOf_apply_le_base (H¹₀(Ω))
          (fun i ↦ derivCoordCLM i) derivCoordCLM_norm_le
          baseCoordCLM baseCoordCLM_norm_le z.1 z.2 u v
    exact hbase.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsum (norm_nonneg _)) (norm_nonneg _))

/-- Absolute continuity bounds the principal coefficients on the time interval.
Together with the lower-order bound, it gives one uniform bound for the full form. -/
private theorem exists_multiplication_full_form_bound
    {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ} (hab : a < b)
    (coeff : ℝ → Fin n → Fin n → DerivLp n ∞ Ω)
    (z : ℝ → (Fin n → DerivLp n ∞ Ω) × DerivLp n ∞ Ω)
    (hcoeffAC : AbsolutelyContinuousOnInterval coeff a b)
    (Z : ℝ≥0) (hzbound : ∀ t ∈ Icc a b, ‖z t‖ ≤ Z) :
    ∃ MB : ℝ≥0, ∀ t ∈ Icc a b,
      ‖fullDivergenceForm (multiplicationCoefficientOperator (coeff t))
        (fun i ↦ mulLpLeft ((z t).1 i)) (mulLpLeft (z t).2)‖ ≤ MB := by
  obtain ⟨M₀, hM₀⟩ := hcoeffAC.exists_bound
  let M : ℝ≥0 := ⟨max M₀ 0, le_max_right _ _⟩
  have hM (t : ℝ) (ht : t ∈ Icc a b) : ‖coeff t‖ ≤ M :=
    (hM₀ t (by simpa only [uIcc_of_le hab.le] using ht)).trans (le_max_left _ _)
  refine ⟨(n : ℝ≥0) ^ 2 * M + ((n : ℝ≥0) + 1) * Z, ?_⟩
  intro t ht
  let A : H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
    variableCoeffForm (multiplicationCoefficientOperator (coeff t))
  let R : H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
    lowerOrderForm (fun i ↦ mulLpLeft ((z t).1 i)) (mulLpLeft (z t).2)
  have hA : ‖A‖ ≤ (n : ℝ) ^ 2 * M :=
    (norm_multiplicationCoeffFormOf_le (H¹₀(Ω)) (H¹₀(Ω))
      (fun i ↦ derivCoordCLM i) derivCoordCLM_norm_le
      (fun i ↦ derivCoordCLM i) derivCoordCLM_norm_le (coeff t)).trans
      (mul_le_mul_of_nonneg_left (hM t ht) (sq_nonneg _))
  have hR : ‖R‖ ≤ ((n : ℝ) + 1) * Z :=
    (multiplication_lower_form_bounds (z t) Z (hzbound t ht)).1
  change ‖A + R‖ ≤ _
  simpa only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_natCast, NNReal.coe_one] using!
    (norm_add_le A R).trans (add_le_add hA hR)

/-- The bounded linear coefficient-to-form map preserves absolute continuity and
identifies the form derivative. The coefficient curve is also strongly measurable. -/
private theorem multiplication_principal_time_regularity
    {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ} (hab : a < b)
    (coeff coeffDot : ℝ → Fin n → Fin n → DerivLp n ∞ Ω)
    (hcoeffAC : AbsolutelyContinuousOnInterval coeff a b)
    (hcoeffDeriv : ∀ᵐ t ∂volume.restrict (Ioc a b),
      HasDerivAt coeff (coeffDot t) t) :
    AbsolutelyContinuousOnInterval
        (fun t ↦ variableCoeffForm (multiplicationCoefficientOperator (coeff t))) a b ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b),
        HasDerivAt
          (fun s ↦ variableCoeffForm (multiplicationCoefficientOperator (coeff s)))
          (variableCoeffForm (multiplicationCoefficientOperator (coeffDot t))) t) ∧
      AEStronglyMeasurable coeff (volume.restrict (Ioc a b)) := by
  have hcont : ContinuousOn coeff (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using hcoeffAC.continuousOn
  refine ⟨?_, ?_, AEStronglyMeasurable.mono_set Ioc_subset_Icc_self
    (hcont.aestronglyMeasurable_of_isCompact (μ := volume) isCompact_Icc
      measurableSet_Icc)⟩
  · let F : (Fin n → Fin n → DerivLp n ∞ Ω) →L[ℝ]
        (H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω))) :=
      multiplicationCoeffFormCLMOf (H¹₀(Ω)) (H¹₀(Ω))
        (fun i ↦ derivCoordCLM i) derivCoordCLM_norm_le
        (fun i ↦ derivCoordCLM i) derivCoordCLM_norm_le
    have hF (d : Fin n → Fin n → DerivLp n ∞ Ω) :
        F d = variableCoeffForm (multiplicationCoefficientOperator d) := rfl
    have hLip : LipschitzWith ((n : ℝ≥0) ^ 2) F :=
      lipschitzWith_multiplicationCoeffFormCLMOf (H¹₀(Ω)) (H¹₀(Ω))
        (fun i ↦ derivCoordCLM i) derivCoordCLM_norm_le
        (fun i ↦ derivCoordCLM i) derivCoordCLM_norm_le
    have hAC : AbsolutelyContinuousOnInterval (F ∘ coeff) a b :=
      hLip.comp_absolutelyContinuousOnInterval hcoeffAC
    simpa only [Function.comp_def, hF] using hAC
  · filter_upwards [hcoeffDeriv] with t ht
    exact hasDerivAt_multiplicationCoeffFormOf (H¹₀(Ω)) (H¹₀(Ω))
      (fun i ↦ derivCoordCLM i) derivCoordCLM_norm_le
      (fun i ↦ derivCoordCLM i) derivCoordCLM_norm_le ht

/-- A matrix `L∞` bound controls its quadratic form against norm-nonincreasing
coordinate maps. The same estimate applies to the principal time derivative. -/
private theorem multiplication_principal_quadratic_le
    {n : ℕ} {Ω : Set (ℝ^n)}
    (U : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U]
    (D : Fin n → U →L[ℝ] DerivLp n 2 Ω) (hD : ∀ i u, ‖D i u‖ ≤ ‖u‖)
    (d : Fin n → Fin n → DerivLp n ∞ Ω) (N : ℝ≥0) (hd : ‖d‖ ≤ N)
    (u : U) :
    variableCoeffFormOf U U D hD D hD (multiplicationCoefficientOperator d) u u ≤
      ((n : ℝ) ^ 2 * N) * ‖u‖ ^ 2 := by
  let B : U →L[ℝ] U →L[ℝ] ℝ :=
    variableCoeffFormOf U U D hD D hD (multiplicationCoefficientOperator d)
  have hB : ‖B‖ ≤ (n : ℝ) ^ 2 * N :=
    (norm_multiplicationCoeffFormOf_le U U D hD D hD d).trans
      (mul_le_mul_of_nonneg_left hd (sq_nonneg _))
  calc
    B u u ≤ ‖B u u‖ := Real.le_norm_self _
    _ ≤ ‖B‖ * ‖u‖ * ‖u‖ := B.le_opNorm₂ u u
    _ ≤ ((n : ℝ) ^ 2 * N) * ‖u‖ * ‖u‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hB (norm_nonneg _)) (norm_nonneg _)
    _ = ((n : ℝ) ^ 2 * N) * ‖u‖ ^ 2 := by rw [pow_two ‖u‖, mul_assoc]

/-- Ellipticity and Poincaré give one coercivity constant for the whole time
interval. Symmetry and the coefficient bounds give the other three energy estimates;
the lower-order term uses only the base-coordinate norm of its second argument. -/
private theorem multiplication_wave_energy_estimates
    {n : ℕ} {Ω : Set (ℝ^n)} (hn : 0 < n)
    (hΩbounded : Bornology.IsBounded Ω) {a b : ℝ} (hab : a < b)
    (coeff coeffDot : ℝ → Fin n → Fin n → DerivLp n ∞ Ω)
    (z : ℝ → (Fin n → DerivLp n ∞ Ω) × DerivLp n ∞ Ω)
    (N Z : ℝ≥0)
    (hcoeffDot : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖coeffDot t‖ ≤ N)
    (hzbound : ∀ t ∈ Icc a b, ‖z t‖ ≤ Z)
    (hsymm : ∀ t ∈ Icc a b, AESymmetricCoefficient (coeff t))
    {alpha : ℝ}
    (hElliptic : ∀ t ∈ Icc a b, AEUniformlyElliptic (coeff t) alpha) :
    let A := fun t ↦ variableCoeffForm (multiplicationCoefficientOperator (coeff t))
    let Adot := fun t ↦ variableCoeffForm (multiplicationCoefficientOperator (coeffDot t))
    let R := fun t ↦ lowerOrderForm (fun i ↦ mulLpLeft ((z t).1 i)) (mulLpLeft (z t).2)
    ∃ c : ℝ, 0 < c ∧
      (∀ t ∈ Icc a b, ∀ u v : H¹₀(Ω), A t u v = A t v u) ∧
      (∀ t ∈ Icc a b, ∀ u : H¹₀(Ω), c * ‖u‖ ^ 2 ≤ A t u u) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ u v : H¹₀(Ω),
        |R t u v| ≤ (((n : ℝ) + 1) * Z) * ‖u‖ * ‖baseCoordCLM v‖) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ u : H¹₀(Ω),
        Adot t u u ≤ ((n : ℝ) ^ 2 * N) * ‖u‖ ^ 2) := by
  obtain ⟨c, hc, hcoercive⟩ :=
    exists_uniform_coercivity_coefficient_forms hn hΩbounded hab coeff hElliptic
  refine ⟨c, hc, ?_, hcoercive, ?_, ?_⟩
  · intro t ht u v
    exact variableCoeffForm_symm
      (symmetricCoefficientOperator_multiplication_of_ae (coeff t) (hsymm t ht)) u v
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht u v
    exact (multiplication_lower_form_bounds (z t) Z
      (hzbound t (Ioc_subset_Icc_self ht))).2 u v
  · filter_upwards [hcoeffDot] with t ht u
    exact multiplication_principal_quadratic_le (H¹₀(Ω))
      (fun i ↦ derivCoordCLM i) derivCoordCLM_norm_le (coeffDot t) N ht u

/-- The coefficient curves give a measurable bounded full form and an absolutely
continuous principal form. Together with the energy estimates, these are the form
hypotheses for the Galerkin construction; none depend on the forcing or initial data. -/
private theorem multiplication_wave_form_hypotheses
    {n : ℕ} {Ω : Set (ℝ^n)} (hn : 0 < n)
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    {a b : ℝ} (hab : a < b)
    (coeff coeffDot : ℝ → Fin n → Fin n → DerivLp n ∞ Ω)
    (z : ℝ → (Fin n → DerivLp n ∞ Ω) × DerivLp n ∞ Ω)
    (hcoeffAC : AbsolutelyContinuousOnInterval coeff a b)
    (hcoeffDeriv : ∀ᵐ t ∂volume.restrict (Ioc a b),
      HasDerivAt coeff (coeffDot t) t)
    (N Z : ℝ≥0)
    (hcoeffDot : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖coeffDot t‖ ≤ N)
    (hzmeas : AEStronglyMeasurable z (volume.restrict (Ioc a b)))
    (hzbound : ∀ t ∈ Icc a b, ‖z t‖ ≤ Z)
    (hsymm : ∀ t ∈ Icc a b, AESymmetricCoefficient (coeff t))
    {alpha : ℝ}
    (hElliptic : ∀ t ∈ Icc a b, AEUniformlyElliptic (coeff t) alpha) :
    let T : PDE.Analysis.Evolution.GelfandTriple
        (V := H¹₀(Ω)) (H := DerivLp n 2 Ω) := h10L2GelfandTriple hΩopen
    let A : ℝ → H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
      fun t ↦ variableCoeffForm (multiplicationCoefficientOperator (coeff t))
    let Adot : ℝ → H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
      fun t ↦ variableCoeffForm (multiplicationCoefficientOperator (coeffDot t))
    let R : ℝ → H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
      fun t ↦ lowerOrderForm (fun i ↦ mulLpLeft ((z t).1 i)) (mulLpLeft (z t).2)
    ∃ (MB : ℝ≥0) (c : ℝ), 0 < c ∧
      AEStronglyMeasurable (fun t ↦ A t + R t) (volume.restrict (Ioc a b)) ∧
      (∀ t ∈ Icc a b, ‖A t + R t‖ ≤ MB) ∧
      AbsolutelyContinuousOnInterval A a b ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt A (Adot t) t) ∧
      (∀ t ∈ Icc a b, ∀ u v : H¹₀(Ω), A t u v = A t v u) ∧
      (∀ t ∈ Icc a b, ∀ u : H¹₀(Ω), c * ‖u‖ ^ 2 ≤ A t u u) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ u v : H¹₀(Ω),
        |R t u v| ≤ (((n : ℝ) + 1) * Z) * ‖u‖ * ‖T.inclusion v‖) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ u : H¹₀(Ω),
        Adot t u u ≤ ((n : ℝ) ^ 2 * N) * ‖u‖ ^ 2) := by
  let T : PDE.Analysis.Evolution.GelfandTriple
      (V := H¹₀(Ω)) (H := DerivLp n 2 Ω) := h10L2GelfandTriple hΩopen
  let A : ℝ → H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
    fun t ↦ variableCoeffForm (multiplicationCoefficientOperator (coeff t))
  let Adot : ℝ → H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
    fun t ↦ variableCoeffForm (multiplicationCoefficientOperator (coeffDot t))
  let R : ℝ → H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
    fun t ↦ lowerOrderForm (fun i ↦ mulLpLeft ((z t).1 i)) (mulLpLeft (z t).2)
  obtain ⟨MB, hBbound⟩ :=
    exists_multiplication_full_form_bound hab coeff z hcoeffAC Z hzbound
  obtain ⟨hAAC, hAderiv, hcoeffMeas⟩ :=
    multiplication_principal_time_regularity hab coeff coeffDot hcoeffAC hcoeffDeriv
  have hBmeas : AEStronglyMeasurable (fun t ↦ A t + R t)
      (volume.restrict (Ioc a b)) :=
    aestronglyMeasurable_multiplicationFullFormOf (H¹₀(Ω))
      (fun i ↦ derivCoordCLM i) derivCoordCLM_norm_le
      baseCoordCLM baseCoordCLM_norm_le hcoeffMeas hzmeas
  obtain ⟨c, hc, hAsymm, hcoercive, hRbase, hAdotBound⟩ :=
    multiplication_wave_energy_estimates hn hΩbounded hab coeff coeffDot z N Z
      hcoeffDot hzbound hsymm hElliptic
  have hRbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ u v : H¹₀(Ω),
      |R t u v| ≤ (((n : ℝ) + 1) * Z) * ‖u‖ * ‖T.inclusion v‖ := by
    simpa only [T, h10L2GelfandTriple_inclusion_apply] using hRbase
  exact ⟨MB, c, hc, hBmeas, hBbound, hAAC, hAderiv, hAsymm,
    hcoercive, hRbound, hAdotBound⟩

/-- The coefficient hypotheses give one energy constant for all forcing and initial
data. The constructed weak wave retains both initial values and the quantitative
`L∞(H¹₀) × L∞(L²)` bound. -/
theorem exists_uniform_energy_bound_of_linf_coefficients
    {n : ℕ} {Ω : Set (ℝ^n)} (hn : 0 < n)
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    {a b : ℝ} (hab : a < b)
    (coeff coeffDot : ℝ → Fin n → Fin n → DerivLp n ∞ Ω)
    (z : ℝ → (Fin n → DerivLp n ∞ Ω) × DerivLp n ∞ Ω)
    (hcoeffAC : AbsolutelyContinuousOnInterval coeff a b)
    (hcoeffDeriv : ∀ᵐ t ∂volume.restrict (Ioc a b),
      HasDerivAt coeff (coeffDot t) t)
    (N Z : ℝ≥0)
    (hcoeffDot : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖coeffDot t‖ ≤ N)
    (hzmeas : AEStronglyMeasurable z (volume.restrict (Ioc a b)))
    (hzbound : ∀ t ∈ Icc a b, ‖z t‖ ≤ Z)
    (hsymm : ∀ t ∈ Icc a b, AESymmetricCoefficient (coeff t))
    {alpha : ℝ}
    (hElliptic : ∀ t ∈ Icc a b, AEUniformlyElliptic (coeff t) alpha) :
    let T := h10L2GelfandTriple hΩopen
    ∃ M : ℝ, 0 < M ∧
      ∀ (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
        (q₀ : H¹₀(Ω)) (p₀ : DerivLp n 2 Ω),
    ∃ (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
        (velocity : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
        (acceleration :
          Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))),
      Hyperbolic.Variational.IsGelfandWeakWaveSolution T
          (fun t ↦ fullDivergenceForm (multiplicationCoefficientOperator (coeff t))
            (fun i ↦ mulLpLeft ((z t).1 i)) (mulLpLeft (z t).2))
          (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f)
          u velocity acceleration q₀ p₀ ∧
        MemLp (fun t ↦ u t) ∞ (volume.restrict (Ioc a b)) ∧
        MemLp (fun t ↦ velocity t) ∞ (volume.restrict (Ioc a b)) ∧
        ∀ᵐ t ∂volume.restrict (Ioc a b),
          ‖u t‖ + ‖velocity t‖ ≤ M * (‖f‖ + ‖q₀‖ + ‖p₀‖) := by
  classical
  let T : PDE.Analysis.Evolution.GelfandTriple
      (V := H¹₀(Ω)) (H := DerivLp n 2 Ω) := h10L2GelfandTriple hΩopen
  let A : ℝ → H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
    fun t ↦ variableCoeffForm (multiplicationCoefficientOperator (coeff t))
  let Adot : ℝ → H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
    fun t ↦ variableCoeffForm (multiplicationCoefficientOperator (coeffDot t))
  let R : ℝ → H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
    fun t ↦ lowerOrderForm (fun i ↦ mulLpLeft ((z t).1 i)) (mulLpLeft (z t).2)
  have hdata :=
    multiplication_wave_form_hypotheses hn hΩopen hΩbounded hab coeff coeffDot z
      hcoeffAC hcoeffDeriv N Z hcoeffDot hzmeas hzbound hsymm hElliptic
  let MB := hdata.choose
  let c := hdata.choose_spec.choose
  have hforms := hdata.choose_spec.choose_spec
  -- Project the form hypotheses without repeated elimination over the large solution goal.
  have hc := hforms.1
  have hBmeas := hforms.2.1
  have hBbound := hforms.2.2.1
  have hAAC := hforms.2.2.2.1
  have hAderiv := hforms.2.2.2.2.1
  have hAsymm := hforms.2.2.2.2.2.1
  have hcoercive := hforms.2.2.2.2.2.2.1
  have hRbound := hforms.2.2.2.2.2.2.2.1
  have hAdotBound := hforms.2.2.2.2.2.2.2.2
  exact
    IsGelfandWeakWaveSolution.exists_uniform_energy_bound_of_compact_inclusion
      (V := H¹₀(Ω)) (H := DerivLp n 2 Ω)
      T (h10L2GelfandTriple_inclusion_isCompactOperator hΩopen hΩbounded)
      A R Adot hab hBmeas MB hBbound hAAC hAderiv hAsymm
      c (((n : ℝ) + 1) * Z) ((n : ℝ) ^ 2 * N) hc (by positivity)
      hcoercive hRbound hAdotBound

/-- Bounded scalar divergence-form coefficients construct a weak Dirichlet wave on
a bounded open domain. Only the principal matrix is symmetric and elliptic. Its
time regularity is measured in `L∞`, while drift and potential need only strong
measurability in that norm and a uniform bound on the closed time interval.

Compactness, form coercivity, all operator bounds, and the lower-order work estimate
are derived. Arbitrary `H¹₀ × L²` initial data and `L²_t L²_x` forcing are allowed.
The result includes both initial values and the uniform energy regularity. -/
theorem exists_weakWave_of_linf_coefficients
    {n : ℕ} {Ω : Set (ℝ^n)} (hn : 0 < n)
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    {a b : ℝ} (hab : a < b)
    (coeff coeffDot : ℝ → Fin n → Fin n → DerivLp n ∞ Ω)
    (z : ℝ → (Fin n → DerivLp n ∞ Ω) × DerivLp n ∞ Ω)
    (hcoeffAC : AbsolutelyContinuousOnInterval coeff a b)
    (hcoeffDeriv : ∀ᵐ t ∂volume.restrict (Ioc a b),
      HasDerivAt coeff (coeffDot t) t)
    (N Z : ℝ≥0)
    (hcoeffDot : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖coeffDot t‖ ≤ N)
    (hzmeas : AEStronglyMeasurable z (volume.restrict (Ioc a b)))
    (hzbound : ∀ t ∈ Icc a b, ‖z t‖ ≤ Z)
    (hsymm : ∀ t ∈ Icc a b, AESymmetricCoefficient (coeff t))
    {alpha : ℝ}
    (hElliptic : ∀ t ∈ Icc a b, AEUniformlyElliptic (coeff t) alpha)
    (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
    (q₀ : H¹₀(Ω)) (p₀ : DerivLp n 2 Ω) :
    let T := h10L2GelfandTriple hΩopen
    ∃ (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
        (velocity : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
        (acceleration :
          Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))),
      Hyperbolic.Variational.IsGelfandWeakWaveSolution T
          (fun t ↦ fullDivergenceForm (multiplicationCoefficientOperator (coeff t))
            (fun i ↦ mulLpLeft ((z t).1 i)) (mulLpLeft (z t).2))
          (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f)
          u velocity acceleration q₀ p₀ ∧
        MemLp (fun t ↦ u t) ∞ (volume.restrict (Ioc a b)) ∧
        MemLp (fun t ↦ velocity t) ∞ (volume.restrict (Ioc a b)) := by
  obtain ⟨M, _, hM⟩ := exists_uniform_energy_bound_of_linf_coefficients
    hn hΩopen hΩbounded hab coeff coeffDot z hcoeffAC hcoeffDeriv
    N Z hcoeffDot hzmeas hzbound hsymm hElliptic
  obtain ⟨u, v, w, hu, huTop, hvTop, _⟩ := hM f q₀ p₀
  exact ⟨u, v, w, hu, huTop, hvTop⟩

end SobolevSpace.GraphSpace
