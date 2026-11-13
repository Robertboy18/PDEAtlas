/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Measurable.Coefficients
public import PDE.Analysis.Evolution.Galerkin.TrialProjection
public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Temporal compactness for Aubin–Lions

The time-compactness half of the Hilbert-space Aubin–Lions argument.  For a
trajectory `u ∈ L²(a, b; V)` whose Lions–Magenes derivative `g = u'` lies in
`L²(a, b; V*)`, the pairing identity
`⟪u(t), ι v⟫_H - ⟪u(s), ι v⟫_H = ∫_s^t ⟨g(r), v⟩ dr` and the Cauchy–Schwarz
inequality give the one-half Hölder bound
`|⟪u(t) - u(s), ι v⟫_H| ≤ |t - s|^{1/2} ‖⟨g(·), v⟩‖_{L²}` for every fixed
`v ∈ V`, and likewise for the projection of `u` onto a fixed
finite-dimensional trial space.  Uniform bounds on the trajectories and on the
derivatives thus produce an equicontinuous, uniformly bounded family of curves
into a finite-dimensional space, which is precompact in the uniform norm by
the Arzelà–Ascoli theorem.  Combined with the spatial tail estimate of
`SpatialApproximation`, this yields Aubin–Lions compactness.

## Main results

* `norm_intervalIntegral_coeFn_L2_restrict_Ioc_le`:
  `‖∫_s^t f‖ ≤ |t - s|^{1/2} ‖f‖_{L²}` for `f ∈ L²(a, b; E)`.
* `ContinuousPivotEvolutionOn.abs_pairing_sub_le_sqrt_mul`,
  `ContinuousPivotEvolutionOn.norm_projection_sub_le_sqrt_mul`: the one-half
  Hölder modulus of scalar coefficients and of trial-space projections.
* `isCompact_closure_boundedContinuousFunction_of_sqrt_modulus`: the
  Arzelà–Ascoli step for curves with a common `|t - s|^{1/2}` modulus.
* `isCompact_closure_range_pairingBoundedContinuousFunction`,
  `isCompact_closure_range_projectionBoundedContinuousFunction`:
  precompactness of the coefficient curves and projected trajectories of a
  uniformly bounded family.

## References

* R. Temam, *Navier-Stokes Equations: Theory and Numerical Analysis*, AMS Chelsea Publishing,
  2001, Chapter III (the evolution Navier-Stokes equation). <https://doi.org/10.1090/chel/343>
* J. Simon, "Compact sets in the space L^p(0,T;B)", *Ann. Mat. Pura Appl.* 146 (1986), 65-96.
  <https://doi.org/10.1007/BF01762360>
-/

@[expose] public section

noncomputable section


open MeasureTheory Set
open scoped BoundedContinuousFunction ENNReal InnerProductSpace

open InnerProductSpace

namespace PDE.Analysis.Evolution

/-- Between two points of `[a, b]`, Lebesgue measure restricted to `uIoc s t` is at most its
restriction to `(a, b]`. -/
private theorem restrict_uIoc_le {a b s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    volume.restrict (uIoc s t) ≤ volume.restrict (Ioc a b) :=
  Measure.restrict_mono_set _ fun r hr ↦ by
    rcases mem_uIoc.mp hr with h | h
    exacts [⟨hs.1.trans_lt h.1, h.2.trans ht.2⟩, ⟨ht.1.trans_lt h.1, h.2.trans hs.2⟩]

/--
An `L²(a,b;E)` trajectory has a one-half Hölder bound on each interval
integral:

`‖∫ₛᵗ f(r) dr‖ ≤ |t-s|¹ᐟ² ‖f‖_{L²(a,b;E)}`.
-/
theorem norm_intervalIntegral_coeFn_L2_restrict_Ioc_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b s t : ℝ}
    (f : Lp E 2 (volume.restrict (Ioc a b)))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖∫ r in s..t, f r‖ ≤ √|t - s| * ‖f‖ := by
  let ν := volume.restrict (uIoc s t)
  have hνμ : ν ≤ volume.restrict (Ioc a b) := restrict_uIoc_le hs ht
  have hOne : MemLp (fun _ : ℝ ↦ (1 : ℝ)) 2 ν :=
    (memLp_const_iff (by norm_num) (by norm_num)).2 (Or.inr (by simp [ν]))
  have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := ν) Real.HolderConjugate.two_two
    (by simpa only [ENNReal.ofReal_ofNat] using ((Lp.memLp f).mono_measure hνμ).norm)
    (by simpa only [ENNReal.ofReal_ofNat] using hOne)
  have hsqrt : √(∫ r, ‖f r‖ ^ 2 ∂ν) ≤ ‖f‖ := by
    rw [← abs_norm f, ← Real.sqrt_sq_eq_abs, Lp.norm_sq_eq_integral_norm_sq f]
    exact Real.sqrt_le_sqrt (integral_mono_measure hνμ (ae_of_all _ fun _ ↦ sq_nonneg _)
      ((Lp.memLp f).integrable_norm_pow (by norm_num)))
  calc ‖∫ r in s..t, f r‖ ≤ ∫ r in uIoc s t, ‖f r‖ :=
        intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ = ∫ r, ‖‖f r‖‖ * ‖(1 : ℝ)‖ ∂ν := by simp [ν]
    _ ≤ √(∫ r, ‖‖f r‖‖ ^ 2 ∂ν) * √(∫ r, ‖(1 : ℝ)‖ ^ 2 ∂ν) := by
        simpa [Real.rpow_two, one_div, Real.sqrt_eq_rpow] using hholder
    _ = √(∫ r, ‖f r‖ ^ 2 ∂ν) * √|t - s| := by simp [ν, measureReal_def, Real.volume_uIoc]
    _ ≤ √|t - s| * ‖f‖ := by rw [mul_comm]; gcongr

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
Every fixed energy-space test vector sees a one-half Hölder scalar
coefficient along a Lions–Magenes evolution.

The modulus is controlled by the `L²` norm of the dual derivative evaluated
at that vector. This is the temporal estimate used to compactify every
fixed finite-dimensional Galerkin projection.
-/
theorem ContinuousPivotEvolutionOn.abs_pairing_sub_le_sqrt_mul
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ContinuousPivotEvolutionOn T (fun r ↦ u r) (fun r ↦ g r) a b)
    (v : V) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    |inner ℝ (E.representative t) (T.inclusion v) -
        inner ℝ (E.representative s) (T.inclusion v)| ≤
      √|t - s| *
        ‖(ContinuousLinearMap.apply ℝ ℝ v).compLpL
          2 (volume.restrict (Ioc a b)) g‖ := by
  let gv : Lp ℝ 2 (volume.restrict (Ioc a b)) :=
    (ContinuousLinearMap.apply ℝ ℝ v).compLpL 2 (volume.restrict (Ioc a b)) g
  have hgv : ∀ᵐ r ∂volume, r ∈ uIoc s t → gv r = g r v := (ae_restrict_iff' measurableSet_uIoc).mp
    (((ContinuousLinearMap.apply ℝ ℝ v).coeFn_compLpL g).filter_mono
      (ae_mono (restrict_uIoc_le hs ht)))
  have hab : a ≤ b := hs.1.trans hs.2
  rw [E.integratedDerivative.pairing_sub_eq_integral v (by simpa [uIcc_of_le hab] using hs)
    (by simpa [uIcc_of_le hab] using ht), ← intervalIntegral.integral_congr_ae hgv]
  simpa only [Real.norm_eq_abs, gv] using norm_intervalIntegral_coeFn_L2_restrict_Ioc_le gv hs ht

/--
A uniformly bounded family of continuous curves into a proper normed space
with a common one-half Hölder modulus has compact closure in the uniform norm.

This is the Arzelà–Ascoli step used for fixed finite-dimensional Galerkin
trajectories in the Aubin–Lions argument.
-/
theorem isCompact_closure_boundedContinuousFunction_of_sqrt_modulus
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {a b M C : ℝ}
    (A : Set (Icc a b →ᵇ E))
    (hrange : ∀ f ∈ A, ∀ t, ‖f t‖ ≤ M)
    (hmod : ∀ f ∈ A, ∀ s t,
      ‖f t - f s‖ ≤ C * √|(t : ℝ) - s|) :
    IsCompact (closure A) := by
  apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : E) M)
    (isCompact_closedBall (0 : E) M) A
  · intro f t hf
    simpa only [Metric.mem_closedBall, dist_zero_right] using hrange f hf t
  · refine Metric.equicontinuous_of_continuity_modulus (fun r ↦ C * √r) ?_ _ fun s t f ↦ ?_
    · simpa only [ContinuousAt, Real.sqrt_zero, mul_zero] using
        continuousAt_const.fun_mul (f := fun _ : ℝ ↦ C) (Real.continuous_sqrt.continuousAt (x := 0))
    · simpa only [Subtype.dist_eq, dist_eq_norm, norm_sub_rev, Real.norm_eq_abs] using
        hmod f.1 f.2 t s

/--
The scalar coefficient obtained by pairing a Lions–Magenes representative
with one fixed energy-space test vector, regarded as a bounded continuous
function on the closed time interval.
-/
def ContinuousPivotEvolutionOn.pairingBoundedContinuousFunction
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ContinuousPivotEvolutionOn T (fun r ↦ u r) (fun r ↦ g r) a b)
    (hab : a ≤ b) (v : V) : Icc a b →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨Set.domRestrict (Icc a b)
        (fun t ↦ inner ℝ (E.representative t) (T.inclusion v)),
      continuousOn_iff_continuous_domRestrict.mp <| by
        simpa only [uIcc_of_le hab] using
          E.continuousOn.inner continuousOn_const⟩

/-- Evaluating the bundled coefficient curve at `t` gives the pairing
`⟪u(t), ι v⟫_H` of the representative with the included test vector. -/
@[simp]
theorem ContinuousPivotEvolutionOn.pairingBoundedContinuousFunction_apply
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ContinuousPivotEvolutionOn T (fun r ↦ u r) (fun r ↦ g r) a b)
    (hab : a ≤ b) (v : V) (t : Icc a b) :
    E.pairingBoundedContinuousFunction hab v t =
      inner ℝ (E.representative t) (T.inclusion v) := by
  rfl

/--
Uniform pivot bounds and uniform evaluated-dual-derivative bounds make
every fixed Galerkin coefficient precompact in the uniform norm.
-/
theorem isCompact_closure_range_pairingBoundedContinuousFunction
    {ι : Type*} {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : ι → Lp V 2 (volume.restrict (Ioc a b))}
    {g : ι → Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ∀ j, ContinuousPivotEvolutionOn T
      (fun r ↦ u j r) (fun r ↦ g j r) a b)
    (hab : a ≤ b) (v : V) (U D : ℝ)
    (hU : ∀ j t, t ∈ Icc a b → ‖(E j).representative t‖ ≤ U)
    (hD : ∀ j,
      ‖(ContinuousLinearMap.apply ℝ ℝ v).compLpL
        2 (volume.restrict (Ioc a b)) (g j)‖ ≤ D) :
    IsCompact (closure (range fun j ↦
      (E j).pairingBoundedContinuousFunction hab v)) := by
  apply isCompact_closure_boundedContinuousFunction_of_sqrt_modulus
  · rintro f ⟨j, rfl⟩ t
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hU j t t.2) (norm_nonneg _))
  · rintro f ⟨j, rfl⟩ s t
    exact ((E j).abs_pairing_sub_le_sqrt_mul v s.2 t.2).trans
      ((mul_le_mul_of_nonneg_left (hD j) (Real.sqrt_nonneg _)).trans_eq (mul_comm _ _))

/--
The trial projection of a Lions–Magenes representative evolves by the
Bochner integral of the pivot-mass-inverted restricted dual derivative.
-/
theorem ContinuousPivotEvolutionOn.projection_sub_eq_intervalIntegral
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ContinuousPivotEvolutionOn T (fun r ↦ u r) (fun r ↦ g r) a b)
    {S : Submodule ℝ V} [FiniteDimensional ℝ S] [CompleteSpace S]
    {K : NNReal} (P : StableTrialProjection T S K)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    P.projection (E.representative t) -
        P.projection (E.representative s) =
      ∫ r in s..t, (gelfandGalerkinForcingMap T S) (g r) := by
  refine trialMassOperator_injective T S (ext_inner_right ℝ fun v ↦ ?_)
  have hgInt : IntervalIntegrable (fun r ↦ g r) volume s t := by
    rw [intervalIntegrable_iff]
    exact ((Lp.memLp g).integrable (by norm_num)).mono_measure (restrict_uIoc_le hs ht)
  have hqInt : IntervalIntegrable (fun r ↦ (gelfandGalerkinForcingMap T S) (g r)) volume s t :=
    ⟨(gelfandGalerkinForcingMap T S).integrable_comp hgInt.1,
      (gelfandGalerkinForcingMap T S).integrable_comp hgInt.2⟩
  have hMqInt : IntervalIntegrable
      (fun r ↦ (trialMassOperator T S) ((gelfandGalerkinForcingMap T S) (g r))) volume s t :=
    ⟨(trialMassOperator T S).integrable_comp hqInt.1,
      (trialMassOperator T S).integrable_comp hqInt.2⟩
  have hproj (r : ℝ) :
      inner ℝ (T.inclusion ((P.projection (E.representative r) : S) : V)) (T.inclusion (v : V)) =
        inner ℝ (E.representative r) (T.inclusion (v : V)) := by
    have horth := P.pivotOrthogonal v (E.representative r)
    rw [inner_sub_right] at horth
    rw [real_inner_comm, real_inner_comm _ (E.representative r)]
    linarith
  have hab : a ≤ b := hs.1.trans hs.2
  have hleft : inner ℝ ((trialMassOperator T S)
      (P.projection (E.representative t) - P.projection (E.representative s))) v =
        inner ℝ (E.representative t) (T.inclusion (v : V)) -
          inner ℝ (E.representative s) (T.inclusion (v : V)) := by
    rw [map_sub, inner_sub_left]
    simp only [trialMassOperator, continuousLinearMapOfBilin_apply]
    exact congrArg₂ (· - ·) (hproj t) (hproj s)
  have hright : inner ℝ ((trialMassOperator T S)
      (∫ r in s..t, (gelfandGalerkinForcingMap T S) (g r))) v = ∫ r in s..t, g r v := by
    rw [← (trialMassOperator T S).intervalIntegral_comp_comm hqInt, real_inner_comm]
    change (innerSL ℝ v) (∫ r in s..t, (trialMassOperator T S)
      ((gelfandGalerkinForcingMap T S) (g r))) = ∫ r in s..t, g r v
    rw [← (innerSL ℝ v).intervalIntegral_comp_comm hMqInt]
    refine intervalIntegral.integral_congr_ae (.of_forall fun r _ ↦ ?_)
    rw [innerSL_apply_apply, real_inner_comm, gelfandGalerkinForcingMap_apply, trialMassOperator]
    change inner ℝ ((trialMassEquiv T S) ((trialMassEquiv T S).symm
      ((toDual ℝ _).symm (restrictFunctional S (g r))))) v = g r v
    rw [ContinuousLinearEquiv.apply_symm_apply, toDual_symm_apply, restrictFunctional_apply]
  rw [hleft, hright]
  exact E.integratedDerivative.pairing_sub_eq_integral v
    (by simpa [uIcc_of_le hab] using hs)
    (by simpa [uIcc_of_le hab] using ht)

/--
Finite-dimensional trial projections of a Lions–Magenes evolution have a
one-half Hölder modulus controlled by the mass-inverted restricted dual
derivative.
-/
theorem ContinuousPivotEvolutionOn.norm_projection_sub_le_sqrt_mul
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ContinuousPivotEvolutionOn T (fun r ↦ u r) (fun r ↦ g r) a b)
    {S : Submodule ℝ V} [FiniteDimensional ℝ S] [CompleteSpace S]
    {K : NNReal} (P : StableTrialProjection T S K)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖P.projection (E.representative t) -
        P.projection (E.representative s)‖ ≤
      √|t - s| *
        ‖(gelfandGalerkinForcingMap T S).compLpL
          2 (volume.restrict (Ioc a b)) g‖ := by
  let q : Lp S 2 (volume.restrict (Ioc a b)) :=
    (gelfandGalerkinForcingMap T S).compLpL 2 (volume.restrict (Ioc a b)) g
  have hq : ∀ᵐ r ∂volume, r ∈ uIoc s t → q r = (gelfandGalerkinForcingMap T S) (g r) :=
    (ae_restrict_iff' measurableSet_uIoc).mp (((gelfandGalerkinForcingMap T S).coeFn_compLpL
      g).filter_mono (ae_mono (restrict_uIoc_le hs ht)))
  rw [E.projection_sub_eq_intervalIntegral P hs ht, ← intervalIntegral.integral_congr_ae hq]
  simpa only [q] using norm_intervalIntegral_coeFn_L2_restrict_Ioc_le q hs ht

/--
The projection of a Lions–Magenes representative onto one fixed trial space,
regarded as a bounded continuous trial-space-valued curve.
-/
noncomputable def
    ContinuousPivotEvolutionOn.projectionBoundedContinuousFunction
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ContinuousPivotEvolutionOn T (fun r ↦ u r) (fun r ↦ g r) a b)
    (hab : a ≤ b)
    {S : Submodule ℝ V} {K : NNReal} (P : StableTrialProjection T S K) :
    Icc a b →ᵇ S :=
  BoundedContinuousFunction.mkOfCompact
    ⟨Set.domRestrict (Icc a b) (fun t ↦ P.projection (E.representative t)),
      continuousOn_iff_continuous_domRestrict.mp <| P.projection.continuous.comp_continuousOn <| by
        simpa only [uIcc_of_le hab] using E.continuousOn⟩

/-- Evaluating the bundled projected curve at `t` gives the trial projection
`P (u(t))` of the representative. -/
@[simp]
theorem
    ContinuousPivotEvolutionOn.projectionBoundedContinuousFunction_apply
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ContinuousPivotEvolutionOn T (fun r ↦ u r) (fun r ↦ g r) a b)
    (hab : a ≤ b)
    {S : Submodule ℝ V} {K : NNReal} (P : StableTrialProjection T S K)
    (t : Icc a b) :
    E.projectionBoundedContinuousFunction hab P t =
      P.projection (E.representative t) := by
  rfl

/--
At a fixed Galerkin dimension, uniform pivot bounds and uniform
mass-inverted dual-derivative bounds make the projected trajectories
precompact in the uniform norm.
-/
theorem
    isCompact_closure_range_projectionBoundedContinuousFunction
    {ι : Type*} {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : ι → Lp V 2 (volume.restrict (Ioc a b))}
    {g : ι → Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ∀ j, ContinuousPivotEvolutionOn T
      (fun r ↦ u j r) (fun r ↦ g j r) a b)
    (hab : a ≤ b)
    {S : Submodule ℝ V} [FiniteDimensional ℝ S] [CompleteSpace S]
    {K : NNReal} (P : StableTrialProjection T S K)
    (U D : ℝ)
    (hU : ∀ j t, t ∈ Icc a b → ‖(E j).representative t‖ ≤ U)
    (hD : ∀ j,
      ‖(gelfandGalerkinForcingMap T S).compLpL
        2 (volume.restrict (Ioc a b)) (g j)‖ ≤ D) :
    IsCompact (closure (range fun j ↦
      (E j).projectionBoundedContinuousFunction hab P)) := by
  let _ : ProperSpace S := FiniteDimensional.proper ℝ S
  apply isCompact_closure_boundedContinuousFunction_of_sqrt_modulus
  · rintro f ⟨j, rfl⟩ t
    exact (P.projection.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hU j t t.2) (norm_nonneg P.projection))
  · rintro f ⟨j, rfl⟩ s t
    exact ((E j).norm_projection_sub_le_sqrt_mul P s.2 t.2).trans
      ((mul_le_mul_of_nonneg_left (hD j) (Real.sqrt_nonneg _)).trans_eq (mul_comm _ _))

end PDE.Analysis.Evolution
