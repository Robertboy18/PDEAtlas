/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Variational.GelfandGalerkin.Energy.Basic
public import PDE.Hyperbolic.WeakWave.Galerkin.BochnerRealization
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Energy bounds for weak-wave Galerkin trajectories

Uniform coercivity converts pointwise Gelfand wave-energy estimates into
dimension-independent bounds for the canonical displacement and velocity.
The results include essential pointwise bounds and the corresponding Bochner
`L²` estimates on a finite time interval. Stable trial projections also give a common
initial-energy bound for arbitrary displacement and velocity data.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, Theorem 2, estimate (19), and §7.2.3, proof of
  Theorem 5, estimate (52).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Projecting the displacement in the energy space and the velocity in the pivot space
bounds the initial wave energy uniformly in the trial dimension. No symmetry or positivity
of the initial form is needed for this upper bound. -/
theorem GelfandGalerkin.projected_initial_energy_le (T : GelfandTriple (V := V) (H := H))
    {S : Submodule ℝ V} {K : NNReal} (P : StableTrialProjection T S K) (A : V →L[ℝ] StrongDual ℝ V)
    (q₀ : V) (p₀ : H) :
    (1 / 2 : ℝ) * ‖T.inclusion (P.projection p₀ : V)‖ ^ 2 + (1 / 2 : ℝ) *
      A (P.energyProjection q₀ : V) (P.energyProjection q₀ : V) ≤
      (1 / 2 : ℝ) * ‖p₀‖ ^ 2 + (1 / 2 : ℝ) * ‖A‖ * ((K : ℝ) * ‖q₀‖) ^ 2 := by
  have hq : ‖(P.energyProjection q₀ : V)‖ ≤ (K : ℝ) * ‖q₀‖ := P.norm_le q₀
  have hp : ‖T.inclusion (P.projection p₀ : V)‖ ^ 2 ≤ ‖p₀‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (P.norm_inclusion_projection_le p₀)
  have hpotential : A (P.energyProjection q₀ : V) (P.energyProjection q₀ : V) ≤
        ‖A‖ * ((K : ℝ) * ‖q₀‖) ^ 2 := by
    calc
      A (P.energyProjection q₀ : V) (P.energyProjection q₀ : V) ≤
          ‖A (P.energyProjection q₀ : V) (P.energyProjection q₀ : V)‖ := Real.le_norm_self _
      _ ≤ ‖A (P.energyProjection q₀ : V)‖ * ‖(P.energyProjection q₀ : V)‖ :=
        (A (P.energyProjection q₀ : V)).le_opNorm _
      _ ≤ (‖A‖ * ‖(P.energyProjection q₀ : V)‖) * ‖(P.energyProjection q₀ : V)‖ :=
        mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
      _ = ‖A‖ * ‖(P.energyProjection q₀ : V)‖ ^ 2 := by ring
      _ ≤ ‖A‖ * ((K : ℝ) * ‖q₀‖) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg A)
        exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg K.coe_nonneg (norm_nonneg q₀))).mpr hq
  linarith

namespace SecondOrderSolutionOn

variable
  {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {T : GelfandTriple (V := V) (H := H)}
  {S : Submodule ℝ V} [FiniteDimensional ℝ S] [CompleteSpace S]
  {B : ℝ → V →L[ℝ] StrongDual ℝ V}
  {ell : ℝ → StrongDual ℝ V}
  {a b : ℝ} {q₀ p₀ : S}

omit [CompleteSpace V] in
/--
The Gelfand wave energy controls the energy-space displacement whenever the
principal form is uniformly coercive.

This estimate is pointwise and dimension-free:

`‖q(t)‖_V² ≤ (2 / c) E(t)`.
-/
theorem displacement_norm_sq_le_of_gelfandWaveEnergy_le {A R : ℝ → V →L[ℝ] StrongDual ℝ V} {c C : ℝ}
    (hc : 0 < c) {t : ℝ}
    (U : SecondOrderSolutionOn (fun s ↦ gelfandGalerkinOperator T S (A s + R s))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hcoercive : c * ‖(U.displacement t : V)‖ ^ 2 ≤
      A t (U.displacement t : V) (U.displacement t : V))
    (henergy : gelfandWaveEnergy T S A U.displacement U.velocity t ≤ C) :
    ‖(U.displacement t : V)‖ ^ 2 ≤ (2 / c) * C := by
  have hkinetic : 0 ≤ (1 / 2 : ℝ) *
        ‖T.inclusion (U.velocity t : V)‖ ^ 2 := by
    positivity
  have hbase :
      (c / 2) * ‖(U.displacement t : V)‖ ^ 2 ≤ C := by
    dsimp only [gelfandWaveEnergy] at henergy
    nlinarith
  calc
    ‖(U.displacement t : V)‖ ^ 2 = (2 / c) *
          ((c / 2) * ‖(U.displacement t : V)‖ ^ 2) := by
      field_simp
    _ ≤ (2 / c) * C :=
      mul_le_mul_of_nonneg_left hbase (by positivity)

omit [CompleteSpace V] in
/--
The Gelfand wave energy controls the pivot-space velocity whenever the
principal form is coercive.

The estimate is `‖Jp(t)‖_H² ≤ 2 E(t)` and is independent of the trial-space
dimension.
-/
theorem pivotVelocity_norm_sq_le_of_gelfandWaveEnergy_le {A R : ℝ → V →L[ℝ] StrongDual ℝ V}
    {c C : ℝ} (hc : 0 < c) {t : ℝ}
    (U : SecondOrderSolutionOn (fun s ↦ gelfandGalerkinOperator T S (A s + R s))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hcoercive : c * ‖(U.displacement t : V)‖ ^ 2 ≤
      A t (U.displacement t : V) (U.displacement t : V))
    (henergy : gelfandWaveEnergy T S A U.displacement U.velocity t ≤ C) :
    ‖T.inclusion (U.velocity t : V)‖ ^ 2 ≤ 2 * C := by
  have hpotential : 0 ≤ A t (U.displacement t : V) (U.displacement t : V) :=
    (mul_nonneg (le_of_lt hc) (sq_nonneg _)).trans hcoercive
  dsimp only [gelfandWaveEnergy] at henergy
  nlinarith

omit [CompleteSpace V] in
/--
The pointwise Galerkin energy estimate gives an essential `L∞(a,b;V)`
bound for the canonical displacement `L²` representative.

The square root is not cosmetic: Evans's estimate (52) is naturally first
obtained for the squared energy.  Uniform coercivity gives

`‖uₘ(t)‖_V² ≤ (2/c) C`,

and nonnegativity converts this to the displayed norm bound.  The
`displacementLp_apply_ae` equality is used only almost everywhere, so the proof
does not evaluate an arbitrary Bochner representative.
-/
theorem ae_norm_displacementLp_le_of_gelfandWaveEnergy_le {A R : ℝ → V →L[ℝ] StrongDual ℝ V}
    {c C : ℝ}
    (U : SecondOrderSolutionOn (fun s ↦ gelfandGalerkinOperator T S (A s + R s))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hab : a ≤ b) (hc : 0 < c)
    (hcoercive : ∀ t ∈ Set.Icc a b, c * ‖(U.displacement t : V)‖ ^ 2 ≤
      A t (U.displacement t : V) (U.displacement t : V))
    (henergy : ∀ t ∈ Set.Icc a b, gelfandWaveEnergy T S A U.displacement U.velocity t ≤ C) :
    ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖U.displacementLp hab t‖ ≤ Real.sqrt ((2 / c) * C) := by
  filter_upwards [ U.displacementLp_apply_ae hab, ae_restrict_mem measurableSet_Ioc] with t ht htIoc
  rw [ht]
  change ‖(U.displacement t : V)‖ ≤ Real.sqrt ((2 / c) * C)
  have hsquare : ‖(U.displacement t : V)‖ ^ 2 ≤ (2 / c) * C :=
    U.displacement_norm_sq_le_of_gelfandWaveEnergy_le
      hc (hcoercive t (Set.Ioc_subset_Icc_self htIoc)) (henergy t (Set.Ioc_subset_Icc_self htIoc))
  exact Real.le_sqrt_of_sq_le hsquare

omit [CompleteSpace V] in
/--
The kinetic part of the Galerkin energy gives an essential
`L∞(a,b;H)` bound for the canonical velocity representative:

`‖uₘ'(t)‖_H ≤ sqrt (2 C)`.

As for the displacement, the coercion theorem for `velocityLp` is used only
almost everywhere.  This is the second half of the uniform estimate (52)
that survives the weak compactness passage in Evans, §7.2.3.
-/
theorem ae_norm_velocityLp_le_of_gelfandWaveEnergy_le {A R : ℝ → V →L[ℝ] StrongDual ℝ V} {c C : ℝ}
    (U : SecondOrderSolutionOn (fun s ↦ gelfandGalerkinOperator T S (A s + R s))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hab : a ≤ b) (hc : 0 < c)
    (hcoercive : ∀ t ∈ Set.Icc a b, c * ‖(U.displacement t : V)‖ ^ 2 ≤
      A t (U.displacement t : V) (U.displacement t : V))
    (henergy : ∀ t ∈ Set.Icc a b, gelfandWaveEnergy T S A U.displacement U.velocity t ≤ C) :
    ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖U.velocityLp hab t‖ ≤ Real.sqrt (2 * C) := by
  filter_upwards [ U.velocityLp_apply_ae hab, ae_restrict_mem measurableSet_Ioc] with t ht htIoc
  rw [ht]
  change ‖T.inclusion (U.velocity t : V)‖ ≤ Real.sqrt (2 * C)
  have hsquare : ‖T.inclusion (U.velocity t : V)‖ ^ 2 ≤ 2 * C :=
    U.pivotVelocity_norm_sq_le_of_gelfandWaveEnergy_le
      hc (hcoercive t (Set.Ioc_subset_Icc_self htIoc)) (henergy t (Set.Ioc_subset_Icc_self htIoc))
  exact Real.le_sqrt_of_sq_le hsquare

omit [CompleteSpace V] in
/--
Dimension-independent Bochner `L²(a,b;V)` bound obtained from a uniform
Gelfand wave-energy estimate.

Uniform coercivity converts the principal potential energy into the
`V`-norm, and integration over the finite time interval gives

`‖q‖²_{L²(V)} ≤ (2/c) C (b-a)`.
-/
theorem norm_displacementLp_sq_le_of_gelfandWaveEnergy_le {A R : ℝ → V →L[ℝ] StrongDual ℝ V}
    {c C : ℝ}
    (U : SecondOrderSolutionOn (fun s ↦ gelfandGalerkinOperator T S (A s + R s))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hab : a ≤ b) (hc : 0 < c)
    (hcoercive : ∀ t ∈ Set.Icc a b, c * ‖(U.displacement t : V)‖ ^ 2 ≤
      A t (U.displacement t : V) (U.displacement t : V))
    (henergy : ∀ t ∈ Set.Icc a b, gelfandWaveEnergy T S A U.displacement U.velocity t ≤ C) :
    ‖U.displacementLp hab‖ ^ 2 ≤ ((2 / c) * C) * (b - a) := by
  rw [MeasureTheory.Lp.norm_sq_eq_integral_norm_sq]
  have hae : (fun t ↦ ‖U.displacementLp hab t‖ ^ 2) =ᵐ[volume.restrict (Set.Ioc a b)]
        fun t ↦ ‖(U.displacement t : V)‖ ^ 2 := (U.displacementLp_apply_ae hab).fun_comp
      (fun z : V ↦ ‖z‖ ^ 2)
  rw [integral_congr_ae hae, ← intervalIntegral.integral_of_le hab]
  have hcontinuous : ContinuousOn (fun t ↦ ‖(U.displacement t : V)‖ ^ 2) (Set.Icc a b) :=
    (U.continuousOn_ambientDisplacement hab).norm.pow 2
  have hintegrable : IntervalIntegrable (fun t ↦ ‖(U.displacement t : V)‖ ^ 2) volume a b :=
    hcontinuous.intervalIntegrable_of_Icc hab
  calc
    (∫ t in a..b, ‖(U.displacement t : V)‖ ^ 2) ≤ ∫ _t in a..b, (2 / c) * C :=
      intervalIntegral.integral_mono_on hab hintegrable intervalIntegrable_const (fun t ht ↦
          U.displacement_norm_sq_le_of_gelfandWaveEnergy_le hc (hcoercive t ht) (henergy t ht))
    _ = ((2 / c) * C) * (b - a) := by
      rw [intervalIntegral.integral_const]
      ring

omit [CompleteSpace V] in
/--
Dimension-independent Bochner `L²(a,b;H)` bound for the Galerkin velocity.

The kinetic part of the wave energy gives

`‖Jp‖²_{L²(H)} ≤ 2 C (b-a)`.
-/
theorem norm_velocityLp_sq_le_of_gelfandWaveEnergy_le {A R : ℝ → V →L[ℝ] StrongDual ℝ V} {c C : ℝ}
    (U : SecondOrderSolutionOn (fun s ↦ gelfandGalerkinOperator T S (A s + R s))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hab : a ≤ b) (hc : 0 < c)
    (hcoercive : ∀ t ∈ Set.Icc a b, c * ‖(U.displacement t : V)‖ ^ 2 ≤
      A t (U.displacement t : V) (U.displacement t : V))
    (henergy : ∀ t ∈ Set.Icc a b, gelfandWaveEnergy T S A U.displacement U.velocity t ≤ C) :
    ‖U.velocityLp hab‖ ^ 2 ≤ (2 * C) * (b - a) := by
  rw [MeasureTheory.Lp.norm_sq_eq_integral_norm_sq]
  have hae : (fun t ↦ ‖U.velocityLp hab t‖ ^ 2) =ᵐ[volume.restrict (Set.Ioc a b)]
        fun t ↦ ‖T.inclusion (U.velocity t : V)‖ ^ 2 := (U.velocityLp_apply_ae hab).fun_comp
      (fun z : H ↦ ‖z‖ ^ 2)
  rw [integral_congr_ae hae, ← intervalIntegral.integral_of_le hab]
  have hcontinuous : ContinuousOn (fun t ↦ ‖T.inclusion (U.velocity t : V)‖ ^ 2) (Set.Icc a b) :=
    (U.continuousOn_pivotVelocity hab).norm.pow 2
  have hintegrable : IntervalIntegrable (fun t ↦ ‖T.inclusion (U.velocity t : V)‖ ^ 2) volume a b :=
    hcontinuous.intervalIntegrable_of_Icc hab
  calc
    (∫ t in a..b, ‖T.inclusion (U.velocity t : V)‖ ^ 2) ≤ ∫ _t in a..b, 2 * C :=
      intervalIntegral.integral_mono_on hab hintegrable intervalIntegrable_const (fun t ht ↦
          U.pivotVelocity_norm_sq_le_of_gelfandWaveEnergy_le hc (hcoercive t ht) (henergy t ht))
    _ = (2 * C) * (b - a) := by
      rw [intervalIntegral.integral_const]
      ring

end SecondOrderSolutionOn

end Hyperbolic.Variational
