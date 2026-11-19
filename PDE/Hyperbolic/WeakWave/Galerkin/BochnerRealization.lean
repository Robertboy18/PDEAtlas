/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Compactness.Lp.Galerkin
public import PDE.Analysis.Evolution.Integrated.TimeDependentForm
public import PDE.Analysis.Evolution.Bochner.Duality
public import PDE.Analysis.Evolution.Galerkin.Gelfand.VectorField
public import PDE.Hyperbolic.Variational.SecondOrder.Basic
import PDE.Analysis.Evolution.Galerkin.Measurable.Coefficients

/-!
# Bochner realizations of weak-wave Galerkin trajectories

A Galerkin approximation of the abstract wave equation `u'' + B(t) u = ℓ(t)` on a
Gelfand triple `V ⊂ H ⊂ V*` is an ODE solution `U` taking values in a
finite-dimensional trial space `S ⊂ V`.  To pass to the limit one needs `U`, `U'`
and `U''` as elements of `L²(a,b;V)`, `L²(a,b;H)` and `L²(a,b;V*)` together with
bounds that do not depend on `dim S`.  We realize a
`SecondOrderSolutionOn` trajectory as those Bochner classes.

The displacement and velocity are continuous on `[a,b]`, so their `L²` classes are
canonical.  The acceleration is subtler: the Galerkin equation holds only against
test functions in `S`, so the coefficient acceleration (the Galerkin ODE right-hand
side, embedded into `V*`) satisfies `⟪U'', v⟫ + B(t)(U, v) = ℓ(t)(v)` only for `v ∈ S`.
Given a stable trial projection `P : V → S` with `‖P‖ ≤ K` (uniform in `S`) and
orthogonal in the pivot inner product, the dual acceleration against an arbitrary
`v ∈ V` equals the residual `ℓ(t) - B(t)U(t)` tested against `P v`.  This yields a
pointwise `V*` bound with constant `K`, and an `L²(V*)` bound on the acceleration
by `K (‖ℓ‖ + M_B ‖U‖)` where `M_B` bounds `‖B(t)‖`.

The projection is the abstract `StableTrialProjection T S K`, orthogonal in the
pivot inner product, and `K` is carried through `norm_projectedDual_le` and
`norm_accelerationLp_le_stable`, so the bound is uniform in `dim S`. Trial spaces
spanned by a basis orthogonal in both `H` and `V`, as in Evans, §7.2.2, (11)-(12)
(for example eigenfunctions of `-Δ`), have `K = 1`.

## Main results

* `displacementLp`, `velocityLp`: canonical `L²(a,b;V)` and `L²(a,b;H)` classes of
  the Galerkin displacement and velocity, with `_apply_ae` representatives.
* `projectedEquation`: the pointwise Galerkin equation against every `v ∈ S`.
* `dualAcceleration_apply_eq_projected`, `norm_dualAcceleration_le`: the ambient
  dual acceleration tested against `v` equals the residual tested against `P v`,
  hence the pointwise `V*` bound with constant `K`.
* `projectedDual`, `norm_projectedDual_le`: precomposition with `P` as a continuous
  linear map on `V*`, with operator norm at most `K`.
* `inner_riesz_projectedDual_compLpL`, `tendsto_inner_riesz_projectedDual_compLpL`:
  the adjoint identity in Bochner `L²` and the resulting weak convergence of
  projected dual trajectories when the projections converge strongly to the
  identity.
* `accelerationLp`, `accelerationLp_apply_ae`, `norm_accelerationLp_le_stable`:
  the `L²(a,b;V*)` acceleration, its pointwise representative, and the
  dimension-independent estimate.

## Implementation notes

Bochner classes are taken with respect to `volume.restrict (Ioc a b)`; this is the
convention used throughout `PDE.Analysis.Evolution`.  The estimate
`norm_accelerationLp_le` contains `‖projectedDual P‖`, while
`norm_accelerationLp_le_stable` has `K` in its place, which gives bounds uniform
in the Galerkin dimension.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, equations (10)-(16) (Galerkin approximations), and
  the proof of Theorem 2, step 3.
  <https://doi.org/10.1090/gsm/019>
* R. Temam, *Navier-Stokes Equations: Theory and Numerical Analysis*, AMS Chelsea Publishing, 2001,
  Chapter III.
  <https://doi.org/10.1090/chel/343/03>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution

/-! ## Bochner realizations of finite-dimensional wave trajectories -/

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

/-- The finite-dimensional displacement, viewed in the ambient energy
space.  This is the pointwise representative used to construct its canonical
Bochner class. -/
def ambientDisplacement
    (U : SecondOrderSolutionOn
      (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀) : ℝ → V :=
  fun t ↦ (U.displacement t : V)

/-- The finite-dimensional velocity, viewed in the pivot space.  The wave
energy controls this realization rather than the inherited norm on the
coefficient space `S`. -/
def pivotVelocity
    (U : SecondOrderSolutionOn
      (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀) : ℝ → H :=
  fun t ↦ T.inclusion (U.velocity t : V)

omit [CompleteSpace V] in
/-- The ambient displacement is continuous on the closed time interval. -/
theorem continuousOn_ambientDisplacement
    (U : SecondOrderSolutionOn (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hab : a ≤ b) :
    ContinuousOn U.ambientDisplacement (Set.Icc a b) := by
  apply S.subtypeL.continuous.comp_continuousOn
  simpa only [Set.uIcc_of_le hab] using U.displacementAbsolutelyContinuous.continuousOn

omit [CompleteSpace V] in
/-- The pivot velocity is continuous on the closed time interval. -/
theorem continuousOn_pivotVelocity
    (U : SecondOrderSolutionOn (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hab : a ≤ b) :
    ContinuousOn U.pivotVelocity (Set.Icc a b) := by
  apply (T.inclusion.comp S.subtypeL).continuous.comp_continuousOn
  simpa only [Set.uIcc_of_le hab] using U.velocityAbsolutelyContinuous.continuousOn

/-- Canonical `L²(a,b;V)` realization of a Galerkin displacement. -/
noncomputable def displacementLp
    (U : SecondOrderSolutionOn
      (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hab : a ≤ b) :
    Lp V 2 (volume.restrict (Set.Ioc a b)) :=
  (memLp_restrict_Ioc_of_continuousOn
    (U.continuousOn_ambientDisplacement hab)).toLp U.ambientDisplacement

/-- Canonical `L²(a,b;H)` realization of a Galerkin velocity. -/
noncomputable def velocityLp
    (U : SecondOrderSolutionOn
      (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hab : a ≤ b) :
    Lp H 2 (volume.restrict (Set.Ioc a b)) :=
  (memLp_restrict_Ioc_of_continuousOn
    (U.continuousOn_pivotVelocity hab)).toLp U.pivotVelocity

omit [CompleteSpace V] in
/-- The displacement Bochner class agrees almost everywhere with the
finite-dimensional trajectory included into `V`. -/
theorem displacementLp_apply_ae
    (U : SecondOrderSolutionOn (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hab : a ≤ b) :
    (U.displacementLp hab : ℝ → V) =ᵐ[volume.restrict (Set.Ioc a b)] U.ambientDisplacement :=
  (memLp_restrict_Ioc_of_continuousOn (U.continuousOn_ambientDisplacement hab)).coeFn_toLp

omit [CompleteSpace V] in
/-- The velocity Bochner class agrees almost everywhere with the
finite-dimensional trajectory included into the pivot space. -/
theorem velocityLp_apply_ae
    (U : SecondOrderSolutionOn (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hab : a ≤ b) :
    (U.velocityLp hab : ℝ → H) =ᵐ[volume.restrict (Set.Ioc a b)] U.pivotVelocity :=
  (memLp_restrict_Ioc_of_continuousOn (U.continuousOn_pivotVelocity hab)).coeFn_toLp

/-- The coefficient-space acceleration prescribed by the Galerkin ODE. -/
def coefficientAcceleration
    (U : SecondOrderSolutionOn
      (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (t : ℝ) : S :=
  -(gelfandGalerkinOperator T S (B t)) (U.displacement t) +
    gelfandGalerkinForcing T S ell t

/-- The Galerkin acceleration embedded canonically into `V*`.

This is an ambient dual vector, but its equation is valid only after the
spatial test has been projected to `S`, and the theorems about it keep that
distinction. -/
noncomputable def dualAcceleration
    (U : SecondOrderSolutionOn
      (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (t : ℝ) : StrongDual ℝ V :=
  T.energyToDual (U.coefficientAcceleration t : V)

omit [CompleteSpace V] in
/-- Unfolding lemma: the dual acceleration tested against `v ∈ V` is the pivot inner
product of the (embedded) coefficient acceleration with `v`. -/
@[simp]
theorem dualAcceleration_apply
    (U : SecondOrderSolutionOn (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (t : ℝ) (v : V) :
    U.dualAcceleration t v =
      inner ℝ (T.inclusion (U.coefficientAcceleration t : V)) (T.inclusion v) :=
  rfl

omit [CompleteSpace V] in
/-- The pointwise coefficient acceleration satisfies the Galerkin equation
against every trial-space test. -/
theorem projectedEquation
    (U : SecondOrderSolutionOn (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (t : ℝ) (v : S) :
    U.dualAcceleration t (v : V) + B t (U.displacement t : V) (v : V) = ell t (v : V) := by
  have hfield : U.coefficientAcceleration t =
        gelfandGalerkinVectorField T S B ell t (U.displacement t) :=
    neg_gelfandGalerkinOperator_add_forcing T S B ell t (U.displacement t)
  rw [dualAcceleration_apply, hfield]
  exact gelfandGalerkinVectorField_equation T S B ell t (U.displacement t) v

omit [CompleteSpace V] in
/-- Pivot orthogonality rewrites the ambient dual acceleration against an
arbitrary energy-space test as the Galerkin equation against its stable
trial projection. -/
theorem dualAcceleration_apply_eq_projected {K : NNReal}
    (U : SecondOrderSolutionOn (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (P : StableTrialProjection T S K) (t : ℝ) (v : V) :
    U.dualAcceleration t v = ell t (P.energyProjection v : V) -
      B t (U.displacement t : V) (P.energyProjection v : V) := by
  have hdecomp : T.inclusion v = T.inclusion (P.energyProjection v : V) +
        (T.inclusion v - T.inclusion (P.energyProjection v : V)) := by
    abel
  have horth : inner ℝ (T.inclusion (U.coefficientAcceleration t : V))
          (T.inclusion v - T.inclusion (P.energyProjection v : V)) = 0 := by
    simpa only [StableTrialProjection.energyProjection_apply] using
      P.pivotOrthogonal (U.coefficientAcceleration t) (T.inclusion v)
  have htrial := U.projectedEquation t (P.energyProjection v)
  rw [dualAcceleration_apply] at htrial
  rw [dualAcceleration_apply, hdecomp, inner_add_right, horth, add_zero]
  linarith

omit [CompleteSpace V] in
/-- Dimension-independent pointwise `V*` estimate for the Galerkin
acceleration.  The only trial-space constant is the uniform energy stability
constant `K` of the pivot projection. -/
theorem norm_dualAcceleration_le {K : NNReal}
    (U : SecondOrderSolutionOn (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (P : StableTrialProjection T S K) (t : ℝ) :
    ‖U.dualAcceleration t‖ ≤ (K : ℝ) * (‖ell t‖ + ‖B t‖ * ‖(U.displacement t : V)‖) := by
  apply ContinuousLinearMap.opNorm_le_bound _
  · exact mul_nonneg K.coe_nonneg (add_nonneg (norm_nonneg (ell t)) (mul_nonneg (norm_nonneg (B t))
          (norm_nonneg (U.displacement t : V))))
  · intro v
    rw [U.dualAcceleration_apply_eq_projected P t v]
    calc
      ‖ell t (P.energyProjection v : V) - B t (U.displacement t : V) (P.energyProjection v : V)‖
          ≤ ‖ell t (P.energyProjection v : V)‖ + ‖B t (U.displacement t : V)
              (P.energyProjection v : V)‖ := norm_sub_le _ _
      _ ≤ ‖ell t‖ * ‖P.energyProjection v‖ + (‖B t‖ * ‖(U.displacement t : V)‖) *
              ‖P.energyProjection v‖ := by
          apply add_le_add
          · exact (ell t).le_opNorm _
          · exact ((B t (U.displacement t : V)).le_opNorm (P.energyProjection v : V)).trans
                (mul_le_mul_of_nonneg_right ((B t).le_opNorm (U.displacement t : V))
                  (norm_nonneg _))
      _ = (‖ell t‖ + ‖B t‖ * ‖(U.displacement t : V)‖) *
            ‖P.energyProjection v‖ := by
          ring
      _ ≤ (‖ell t‖ + ‖B t‖ * ‖(U.displacement t : V)‖) * ((K : ℝ) * ‖v‖) :=
          mul_le_mul_of_nonneg_left (P.norm_le v) (add_nonneg (norm_nonneg _)
              (mul_nonneg (norm_nonneg (B t)) (norm_nonneg (U.displacement t : V))))
      _ = ((K : ℝ) *
            (‖ell t‖ + ‖B t‖ * ‖(U.displacement t : V)‖)) * ‖v‖ := by
          ring

/-- Precomposition by the stable energy projection, bundled as a continuous
linear map on `V*`.  Applying this to a residual is the intrinsic,
basis-free way to recover the Galerkin acceleration. -/
noncomputable def projectedDual
    {K : NNReal} (P : StableTrialProjection T S K) :
    StrongDual ℝ V →L[ℝ] StrongDual ℝ V :=
  (ContinuousLinearMap.compL ℝ V V ℝ).flip
    (S.subtypeL.comp P.energyProjection)

omit [CompleteSpace V] [FiniteDimensional ℝ S] [CompleteSpace S] in
/-- Unfolding lemma: `projectedDual P f` evaluated at `v` is `f (P v)`. -/
@[simp]
theorem projectedDual_apply {K : NNReal} (P : StableTrialProjection T S K) (f : StrongDual ℝ V)
    (v : V) :
    projectedDual P f v = f (P.energyProjection v : V) :=
  rfl

omit [CompleteSpace V] [FiniteDimensional ℝ S] [CompleteSpace S] in
/-- The dual projection has the same dimension-independent stability bound as
the underlying trial projection.

The map on `V*` is precomposition by `P : V → S ↪ V`; consequently its
operator norm is at most `K`.  This estimate is the quantitative link
between the projected Galerkin equation and a uniform `L²(V*)` acceleration
bound. -/
theorem norm_projectedDual_le {K : NNReal} (P : StableTrialProjection T S K) :
    ‖projectedDual P‖ ≤ (K : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound _ K.coe_nonneg fun f ↦ ?_
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg K.coe_nonneg (norm_nonneg f))
  intro v
  rw [projectedDual_apply]
  calc
    ‖f (P.energyProjection v : V)‖ ≤ ‖f‖ * ‖(P.energyProjection v : V)‖ :=
      f.le_opNorm (P.energyProjection v : V)
    _ ≤ ‖f‖ * ((K : ℝ) * ‖v‖) := mul_le_mul_of_nonneg_left (P.norm_le v) (norm_nonneg f)
    _ = ((K : ℝ) * ‖f‖) * ‖v‖ := by ring

omit [FiniteDimensional ℝ S] [CompleteSpace S] in
/-- The projected dual residual and the ambiently projected test have the
same Bochner `L²` pairing.

This adjoint relation links the finite-dimensional Galerkin equation and weak
convergence in `L²(V*)`.  It is proved from the
pointwise definitions and the Riesz representation, without assuming that
the trial projection is self-adjoint in the energy norm. -/
theorem inner_riesz_projectedDual_compLpL {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {K : NNReal} (P : StableTrialProjection T S K) (g : Lp (StrongDual ℝ V) 2 μ) (y : Lp V 2 μ) :
    inner ℝ y (rieszFromDualLp ((projectedDual P).compLpL 2 μ g)) =
      inner ℝ (P.ambientEnergyProjection.compLpL 2 μ y) (rieszFromDualLp g) := by
  calc
    inner ℝ y (rieszFromDualLp ((projectedDual P).compLpL 2 μ g)) = inner ℝ
          (rieszFromDualLp ((projectedDual P).compLpL 2 μ g)) y := real_inner_comm _ _
    _ = ∫ t, ((projectedDual P).compLpL 2 μ g) t (y t) ∂μ := (integral_dual_pairing_eq_L2_inner
        ((projectedDual P).compLpL 2 μ g) y).symm
    _ = ∫ t, g t
          (P.ambientEnergyProjection.compLpL 2 μ y t) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ (projectedDual P).coeFn_compLpL g,
        P.ambientEnergyProjection.coeFn_compLpL y] with t hdual hproject
      rw [hdual, hproject, projectedDual_apply, StableTrialProjection.ambientEnergyProjection_apply]
    _ = inner ℝ (rieszFromDualLp g) (P.ambientEnergyProjection.compLpL 2 μ y) :=
      integral_dual_pairing_eq_L2_inner g (P.ambientEnergyProjection.compLpL 2 μ y)
    _ = inner ℝ (P.ambientEnergyProjection.compLpL 2 μ y) (rieszFromDualLp g) := real_inner_comm _ _

omit [FiniteDimensional ℝ S] [CompleteSpace S] in
/-- Weak dual trajectories remain convergent when tested through stable
Galerkin projections that converge strongly to the identity.

For a fixed space-time test `y`, the projected pairing is rewritten as

`⟪Pₙy, Riesz(gₙ)⟫`.

The lifted projections converge strongly in Bochner `L²`, while the Riesz
representatives converge weakly and remain uniformly bounded.  The
weak-strong pairing lemma therefore gives the claimed limit. -/
theorem tendsto_inner_riesz_projectedDual_compLpL {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {K : NNReal} {Sseq : ℕ → Submodule ℝ V} (P : ∀ n, StableTrialProjection T (Sseq n) K)
    (hP : ∀ v : V, Filter.Tendsto (fun n ↦ ((P n).energyProjection v : V)) Filter.atTop (nhds v))
    {l : Filter ℕ} (hl : l ≤ Filter.atTop) (g : ℕ → Lp (StrongDual ℝ V) 2 μ)
    (gLimit : Lp (StrongDual ℝ V) 2 μ)
    (hg : Filter.Tendsto (fun n ↦ toWeakSpace ℝ _ (rieszFromDualLp (g n))) l
      (nhds (toWeakSpace ℝ _ (rieszFromDualLp gLimit))))
    (R : ℝ) (hgR : ∀ n, ‖rieszFromDualLp (g n)‖ ≤ R) (y : Lp V 2 μ) :
    Filter.Tendsto (fun n ↦ inner ℝ y (rieszFromDualLp ((projectedDual (P n)).compLpL 2 μ (g n)))) l
      (nhds (inner ℝ y (rieszFromDualLp gLimit))) := by
  have hproject : Filter.Tendsto (fun n ↦ (P n).ambientEnergyProjection.compLpL 2 μ y) l (nhds y) :=
    (StableTrialProjection.tendsto_ambientEnergyProjection_compLpL P hP y).mono_left hl
  have hpair := tendsto_inner_of_tendsto_weak_of_tendsto_strong hg hproject R hgR
  simpa only [inner_riesz_projectedDual_compLpL] using hpair

/-- Canonical Bochner `L²(V*)` acceleration associated with a Galerkin
trajectory.

The construction first forms the ambient residual `ell - B(·)u` in
`L²(V*)` and then precomposes it with the stable trial projection.  The
pointwise representative theorem below proves that this class is exactly the
pivot-embedded coefficient acceleration. -/
noncomputable def accelerationLp
    {MB : ℝ} {K : NNReal}
    (U : SecondOrderSolutionOn
      (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (P : StableTrialProjection T S K) (hab : a ≤ b)
    (ellLp : Lp (StrongDual ℝ V) 2
      (volume.restrict (Set.Ioc a b)))
    (hBmeas : AEStronglyMeasurable B
      (volume.restrict (Set.Ioc a b)))
    (hBbound : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖B t‖ ≤ MB) :
    Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)) :=
  (projectedDual P).compLpL 2 (volume.restrict (Set.Ioc a b))
    (gelfandResidualLp B ellLp (U.displacementLp hab)
      (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound)

omit [CompleteSpace V] in
/-- The Bochner acceleration agrees almost everywhere with the
pivot-embedded coefficient acceleration, provided `ellLp` represents the
pointwise forcing used by the Galerkin ODE. -/
theorem accelerationLp_apply_ae {MB : ℝ} {K : NNReal}
    (U : SecondOrderSolutionOn (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (P : StableTrialProjection T S K) (hab : a ≤ b)
    (ellLp : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (hEll : (ellLp : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Set.Ioc a b)] ell)
    (hBmeas : AEStronglyMeasurable B (volume.restrict (Set.Ioc a b)))
    (hBbound : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖B t‖ ≤ MB) :
    (U.accelerationLp P hab ellLp hBmeas hBbound : ℝ → StrongDual ℝ V)
      =ᵐ[volume.restrict (Set.Ioc a b)] U.dualAcceleration := by
  filter_upwards [ (projectedDual P).coeFn_compLpL (gelfandResidualLp B ellLp (U.displacementLp hab)
        (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound),
    gelfandResidualLp_apply_ae B ellLp (U.displacementLp hab)
      (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound, U.displacementLp_apply_ae hab,
    hEll] with t hprojected hresidual hu hellt
  refine ContinuousLinearMap.ext fun v ↦ ?_
  change ((projectedDual P).compLpL 2 (volume.restrict (Set.Ioc a b))
      (gelfandResidualLp B ellLp (U.displacementLp hab)
        (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound) t) v = U.dualAcceleration t v
  rw [hprojected, projectedDual_apply, hresidual, hu, hellt]
  exact (U.dualAcceleration_apply_eq_projected P t v).symm

omit [CompleteSpace V] in
/-- Quantitative `L²(V*)` acceleration estimate inherited from the residual
bound and the stable trial projection. -/
theorem norm_accelerationLp_le {MB : ℝ} {K : NNReal}
    (U : SecondOrderSolutionOn (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (P : StableTrialProjection T S K) (hab : a ≤ b)
    (ellLp : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (hBmeas : AEStronglyMeasurable B (volume.restrict (Set.Ioc a b)))
    (hBbound : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖B t‖ ≤ MB) :
    ‖U.accelerationLp P hab ellLp hBmeas hBbound‖ ≤
      ‖projectedDual P‖ * (‖ellLp‖ + MB * ‖U.displacementLp hab‖) := by
  let residual := gelfandResidualLp B ellLp (U.displacementLp hab)
      (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound
  calc
    ‖U.accelerationLp P hab ellLp hBmeas hBbound‖ ≤ ‖(projectedDual P).compLpL 2
              (volume.restrict (Set.Ioc a b))‖ * ‖residual‖ := (projectedDual P).compLpL 2
            (volume.restrict (Set.Ioc a b)) |>.le_opNorm residual
    _ ≤ ‖projectedDual P‖ * ‖residual‖ := by
          gcongr
          exact ContinuousLinearMap.norm_compLpL_le (projectedDual P)
    _ ≤ ‖projectedDual P‖ *
          (‖ellLp‖ + MB * ‖U.displacementLp hab‖) := by
          gcongr
          exact norm_gelfandResidualLp_le B ellLp (U.displacementLp hab)
            (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound

omit [CompleteSpace V] in
/-- Dimension-independent acceleration estimate expressed only through the
stable trial-projection constant.

Unlike `norm_accelerationLp_le`, this bound does not involve the operator
norm of the induced map on `V*`.  If the trial projections share one constant
`K`, the right-hand side is uniform in the Galerkin dimension. -/
theorem norm_accelerationLp_le_stable {MB : ℝ} {K : NNReal}
    (U : SecondOrderSolutionOn (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (P : StableTrialProjection T S K) (hab : a ≤ b)
    (ellLp : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (hBmeas : AEStronglyMeasurable B (volume.restrict (Set.Ioc a b))) (hMB : 0 ≤ MB)
    (hBbound : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖B t‖ ≤ MB) :
    ‖U.accelerationLp P hab ellLp hBmeas hBbound‖ ≤
      (K : ℝ) * (‖ellLp‖ + MB * ‖U.displacementLp hab‖) := by
  calc
    ‖U.accelerationLp P hab ellLp hBmeas hBbound‖ ≤ ‖projectedDual P‖ *
          (‖ellLp‖ + MB * ‖U.displacementLp hab‖) :=
      U.norm_accelerationLp_le P hab ellLp hBmeas hBbound
    _ ≤ (K : ℝ) * (‖ellLp‖ + MB * ‖U.displacementLp hab‖) :=
      mul_le_mul_of_nonneg_right (norm_projectedDual_le P) (add_nonneg (norm_nonneg ellLp)
          (mul_nonneg hMB (norm_nonneg (U.displacementLp hab))))

end SecondOrderSolutionOn

end Hyperbolic.Variational
