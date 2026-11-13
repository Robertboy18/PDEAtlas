/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Core.WeakEvolution
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Riesz reduction for variational evolution equations

Riesz representation (Mathlib's `InnerProductSpace.toDual`) identifies a Hilbert-space dual
forcing with a vector and a continuous bilinear form with a bounded endomorphism. Under this
identification, the weak equation

`⟪u',v⟫ + B(u,v) = ell(v)`

becomes an affine linear ODE. We prove the norm estimates for that
reduction and build the constant-coefficient propagator from the operator exponential
`NormedSpace.exp`. Global existence comes from the variation-of-constants formula and local
existence from Mathlib's Picard–Lindelöf theorem,
`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, proof of Theorem 1 (the linear system (19)), and
  Appendix D.3, Theorem 2 (Riesz Representation Theorem). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

open Function Filter
open InnerProductSpace
open scoped Topology InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section RieszReduction

variable [CompleteSpace V]

-- Operator exponentials use the normed-ring structure on continuous
-- endomorphisms.  Reuse its analytic proofs while pinning the parent
-- structures to the canonical continuous-linear-map instances; this keeps
-- algebraic exponentiation and Fréchet differentiation in the same topology.
/-- The canonical normed-ring structure on bounded endomorphisms of `V`, used by the
operator-exponential construction in the Riesz-reduced ODE. -/
local instance (priority := 10000) endNormedRing :
    NormedRing (V →L[ℝ] V) :=
  { ContinuousLinearMap.toNormedRing with
    toNorm := inferInstance
    toRing := inferInstance
    toMetricSpace := inferInstance }

/-- The rational normed-algebra structure obtained by restricting scalars from `ℝ`; it supplies
the scalar coefficients in operator power series. -/
local instance normedAlgebraRatEnd : NormedAlgebra ℚ (V →L[ℝ] V) :=
  NormedAlgebra.restrictScalars ℚ ℝ (V →L[ℝ] V)

/-! ## Riesz reduction to an ordinary differential equation

On each finite-dimensional Galerkin space, the Riesz representation theorem
turns the weak system into a vector-valued linear ODE. Evans does this in
coordinates: with an `L²`-orthonormal basis the Galerkin equations become the linear
system (19) in the proof of §7.1.2, Theorem 1.
-/

/-- A weak evolution equation on a Hilbert space is equivalent to equality of
its Riesz representatives. -/
theorem satisfiesWeakEvolutionAt_iff_riesz
    (B : V →L[ℝ] StrongDual ℝ V) (ell : StrongDual ℝ V) (u du : V) :
    SatisfiesWeakEvolutionAt B ell u du ↔
      du + continuousLinearMapOfBilin B u = (toDual ℝ _).symm ell := by
  constructor
  · intro h
    apply ext_inner_right ℝ
    intro v
    rw [inner_add_left, continuousLinearMapOfBilin_apply, toDual_symm_apply]
    exact h v
  · intro h v
    have := congrArg (fun w : V ↦ inner ℝ w v) h
    change inner ℝ (du + continuousLinearMapOfBilin B u) v =
      inner ℝ ((toDual ℝ _).symm ell) v at this
    rw [inner_add_left, continuousLinearMapOfBilin_apply, toDual_symm_apply] at this
    exact this

/-- ODE form of the weak equation: `u' = Riesz(ell) - A u`. -/
theorem satisfiesWeakEvolutionAt_iff_ode
    (B : V →L[ℝ] StrongDual ℝ V) (ell : StrongDual ℝ V) (u du : V) :
    SatisfiesWeakEvolutionAt B ell u du ↔
      du = (toDual ℝ _).symm ell - continuousLinearMapOfBilin B u := by
  rw [satisfiesWeakEvolutionAt_iff_riesz]
  constructor <;> intro h
  · exact eq_sub_of_add_eq h
  · exact add_eq_of_eq_sub h

/-- Riesz-represented vector field associated with a time-dependent weak
evolution equation. -/
def weakEvolutionVectorField
    (B : V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V) : ℝ → V → V :=
  fun t u ↦ (toDual ℝ _).symm (ell t) - continuousLinearMapOfBilin B u

/-- Standard growth estimate for the Riesz-represented weak evolution vector
field. -/
theorem norm_weakEvolutionVectorField_le
    (B : V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    (t : ℝ) (u : V) :
    ‖weakEvolutionVectorField B ell t u‖ ≤
      ‖ell t‖ + ‖continuousLinearMapOfBilin B‖ * ‖u‖ := by
  calc
    ‖weakEvolutionVectorField B ell t u‖ ≤
        ‖(toDual ℝ _).symm (ell t)‖ + ‖continuousLinearMapOfBilin B u‖ := by
      simpa [weakEvolutionVectorField] using
        norm_sub_le ((toDual ℝ _).symm (ell t)) (continuousLinearMapOfBilin B u)
    _ ≤ ‖ell t‖ + ‖continuousLinearMapOfBilin B‖ * ‖u‖ := by
      rw [LinearIsometryEquiv.norm_map]
      gcongr
      exact (continuousLinearMapOfBilin B).le_opNorm u

/-! ## Global affine linear evolution

The Galerkin systems in Evans, §7.1.2, are affine linear ODEs. The
variation-of-constants formula in the Banach algebra of continuous linear
endomorphisms solves them globally, so the public Galerkin theorem needs no
ball or step-size data.
-/

/-- The homogeneous propagator `exp (-(t-t₀) A)` for `u' = c - A u`. -/
def linearEvolutionPropagator
    (A : V →L[ℝ] V) (t₀ t : ℝ) : V →L[ℝ] V :=
  NormedSpace.exp ((t - t₀) • (-A))

/-- The integrating factor `exp ((t-t₀) A)` for `u' = c - A u`. -/
def linearEvolutionIntegratingFactor
    (A : V →L[ℝ] V) (t₀ t : ℝ) : V →L[ℝ] V :=
  NormedSpace.exp ((t - t₀) • A)

/-- The variation-of-constants solution of `u' = c - A u` with `u(t₀)=u₀`. -/
def affineLinearEvolutionSolution
    (A : V →L[ℝ] V) (c : ℝ → V) (t₀ : ℝ) (u₀ : V) (t : ℝ) : V :=
  linearEvolutionPropagator A t₀ t
    (u₀ + ∫ s in t₀..t, linearEvolutionIntegratingFactor A t₀ s (c s))

/-- The propagator and integrating factor are mutual inverses at each time. -/
theorem linearEvolutionPropagator_mul_integratingFactor
    (A : V →L[ℝ] V) (t₀ t : ℝ) :
    linearEvolutionPropagator A t₀ t * linearEvolutionIntegratingFactor A t₀ t = 1 := by
  rw [linearEvolutionPropagator, linearEvolutionIntegratingFactor,
    ← NormedSpace.exp_add_of_commute]
  · simp
  · exact (Commute.refl A).neg_left.smul_left (t - t₀) |>.smul_right (t - t₀)

/-- Derivative of the positive operator integrating factor. -/
theorem hasDerivAt_linearEvolutionIntegratingFactor
    (A : V →L[ℝ] V) (t₀ t : ℝ) :
    HasDerivAt (linearEvolutionIntegratingFactor A t₀)
      (linearEvolutionIntegratingFactor A t₀ t * A) t := by
  have h := (hasDerivAt_exp_smul_const A (t - t₀)).scomp t
    (hasDerivAt_id t |>.sub_const t₀)
  rcases h with ⟨h⟩
  constructor
  simpa [linearEvolutionIntegratingFactor, Function.comp_def] using h

/-- Derivative of the homogeneous propagator. -/
theorem hasDerivAt_linearEvolutionPropagator
    (A : V →L[ℝ] V) (t₀ t : ℝ) :
    HasDerivAt (linearEvolutionPropagator A t₀)
      (linearEvolutionPropagator A t₀ t * (-A)) t := by
  have h := (hasDerivAt_exp_smul_const (-A) (t - t₀)).scomp t
    (hasDerivAt_id t |>.sub_const t₀)
  rcases h with ⟨h⟩
  constructor
  simpa [linearEvolutionPropagator, Function.comp_def] using h

/-- A continuous forcing remains continuous after multiplication by the
operator integrating factor. -/
theorem continuous_linearEvolutionIntegrand
    (A : V →L[ℝ] V) (c : ℝ → V) (t₀ : ℝ) (hc : Continuous c) :
    Continuous (fun t ↦ linearEvolutionIntegratingFactor A t₀ t (c t)) := by
  apply Continuous.clm_apply _ hc
  exact continuous_iff_continuousAt.2 fun t ↦
    (hasDerivAt_linearEvolutionIntegratingFactor A t₀ t).continuousAt

/-- The variation-of-constants formula is a classical solution of the affine
linear evolution equation at every time. -/
theorem hasDerivAt_affineLinearEvolutionSolution
    (A : V →L[ℝ] V) (c : ℝ → V) (t₀ : ℝ) (u₀ : V)
    (hc : Continuous c) (t : ℝ) :
    HasDerivAt (affineLinearEvolutionSolution A c t₀ u₀)
      (c t - A (affineLinearEvolutionSolution A c t₀ u₀ t)) t := by
  let q : ℝ → V := fun s ↦ linearEvolutionIntegratingFactor A t₀ s (c s)
  have hq : Continuous q := continuous_linearEvolutionIntegrand A c t₀ hc
  have hprim : HasDerivAt (fun r ↦ u₀ + ∫ s in t₀..r, q s) (q t) t :=
    (intervalIntegral.integral_hasDerivAt_right
      (hq.intervalIntegrable t₀ t) hq.aestronglyMeasurable.stronglyMeasurableAtFilter
      hq.continuousAt).const_add u₀
  have hprod := (hasDerivAt_linearEvolutionPropagator A t₀ t).clm_apply hprim
  rw [show affineLinearEvolutionSolution A c t₀ u₀ = fun r ↦
      linearEvolutionPropagator A t₀ r
        (u₀ + ∫ s in t₀..r, q s) by rfl]
  convert hprod using 1
  dsimp [q]
  have hcomm : Commute (linearEvolutionPropagator A t₀ t) A := by
    apply Commute.exp_left
    exact (Commute.refl A).neg_left.smul_left (t - t₀)
  calc
    c t - A (linearEvolutionPropagator A t₀ t
        (u₀ + ∫ s in t₀..t, linearEvolutionIntegratingFactor A t₀ s (c s))) =
      -(linearEvolutionPropagator A t₀ t
          (A (u₀ + ∫ s in t₀..t, linearEvolutionIntegratingFactor A t₀ s (c s)))) + c t := by
        rw [← mul_apply_eq_comp, ← hcomm.eq, mul_apply_eq_comp]
        simp
        abel
    _ = linearEvolutionPropagator A t₀ t
          (-A (u₀ + ∫ s in t₀..t, linearEvolutionIntegratingFactor A t₀ s (c s))) +
        (linearEvolutionPropagator A t₀ t * linearEvolutionIntegratingFactor A t₀ t) (c t) := by
          rw [linearEvolutionPropagator_mul_integratingFactor]
          simp

omit [CompleteSpace V] in
/-- The variation-of-constants formula takes the prescribed value `u₀` at the initial time. -/
@[simp] theorem affineLinearEvolutionSolution_initial
    (A : V →L[ℝ] V) (c : ℝ → V) (t₀ : ℝ) (u₀ : V) :
    affineLinearEvolutionSolution A c t₀ u₀ t₀ = u₀ := by
  simp [affineLinearEvolutionSolution, linearEvolutionPropagator]

/-- Classical solution of an affine linear ODE on a closed interval when the
forcing is only known to be continuous there.  Time clamping extends the
forcing without adding hypotheses outside the interval. -/
theorem exists_affineLinearEvolution_on_Icc
    (A : V →L[ℝ] V) (c : ℝ → V) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn c (Set.Icc a b)) (t₀ : Set.Icc a b) (u₀ : V) :
    ∃ u : ℝ → V, u t₀ = u₀ ∧ ∀ t ∈ Set.Icc a b,
      HasDerivAt u (c t - A (u t)) t := by
  let cExt : ℝ → V := fun t ↦ c (Set.projIcc a b hab t)
  have hcExt : Continuous cExt := hc.domRestrict.comp continuous_projIcc
  let u := affineLinearEvolutionSolution A cExt t₀ u₀
  refine ⟨u, affineLinearEvolutionSolution_initial _ _ _ _, fun t ht ↦ ?_⟩
  have hext : cExt t = c t := by
    simp [cExt, Set.projIcc_of_mem hab ht]
  simpa [u, hext] using
    hasDerivAt_affineLinearEvolutionSolution A cExt t₀ u₀ hcExt t

/-- Global classical existence for the Riesz-represented weak evolution
equation with continuous forcing.  This is the abstract linear ODE used by
each Galerkin approximation in Evans, §7.1.2. -/
theorem exists_weakEvolution_global
    (B : V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    (hell : Continuous ell) (t₀ : ℝ) (u₀ : V) :
    ∃ u : ℝ → V, u t₀ = u₀ ∧ ∀ t : ℝ,
      HasDerivAt u (weakEvolutionVectorField B ell t (u t)) t ∧
      SatisfiesWeakEvolutionAt B (ell t) (u t)
        (weakEvolutionVectorField B ell t (u t)) := by
  let c : ℝ → V := fun t ↦ (toDual ℝ _).symm (ell t)
  have hc : Continuous c :=
    (toDual ℝ V).symm.continuous.comp hell
  let u := affineLinearEvolutionSolution (continuousLinearMapOfBilin B) c t₀ u₀
  refine ⟨u, affineLinearEvolutionSolution_initial _ _ _ _, fun t ↦ ⟨?_, ?_⟩⟩
  · simpa [u, c, weakEvolutionVectorField] using
      hasDerivAt_affineLinearEvolutionSolution (continuousLinearMapOfBilin B) c t₀ u₀ hc t
  · apply (satisfiesWeakEvolutionAt_iff_ode B (ell t) (u t) _).2
    rfl

/-- Classical existence on a prescribed closed interval from forcing that is
continuous only on that interval.  The proof extends the forcing by clamping
time to the interval and then applies global existence. -/
theorem exists_weakEvolution_on_Icc
    (B : V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    {a b : ℝ} (hab : a ≤ b) (hell : ContinuousOn ell (Set.Icc a b))
    (t₀ : Set.Icc a b) (u₀ : V) :
    ∃ u : ℝ → V, u t₀ = u₀ ∧ ∀ t ∈ Set.Icc a b,
      HasDerivAt u (weakEvolutionVectorField B ell t (u t)) t ∧
      SatisfiesWeakEvolutionAt B (ell t) (u t)
        (weakEvolutionVectorField B ell t (u t)) := by
  let ellExt : ℝ → StrongDual ℝ V := fun t ↦ ell (Set.projIcc a b hab t)
  have hellExt : Continuous ellExt := by
    exact hell.domRestrict.comp continuous_projIcc
  obtain ⟨u, hu₀, hu⟩ := exists_weakEvolution_global B ellExt hellExt t₀ u₀
  refine ⟨u, hu₀, fun t ht ↦ ?_⟩
  have hext : ellExt t = ell t := by
    simp [ellExt, Set.projIcc_of_mem hab ht]
  simpa [hext, weakEvolutionVectorField] using hu t

/--
Closed-interval weak evolution existence, stated with the interval-level
weak equation.

This is the theorem-facing version of `exists_weakEvolution_on_Icc`: the
trajectory is returned together with its classical derivative and a single
`SatisfiesWeakEvolutionOn` hypothesis over `[a,b]`.
-/
theorem exists_weakEvolutionOn_Icc
    (B : V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    {a b : ℝ} (hab : a ≤ b) (hell : ContinuousOn ell (Set.Icc a b))
    (t₀ : Set.Icc a b) (u₀ : V) :
    ∃ u du : ℝ → V,
      u t₀ = u₀ ∧
      (∀ t ∈ Set.Icc a b, du t = weakEvolutionVectorField B ell t (u t)) ∧
      (∀ t ∈ Set.Icc a b, HasDerivAt u (du t) t) ∧
      SatisfiesWeakEvolutionOn (fun _ ↦ B) ell u du (Set.Icc a b) := by
  obtain ⟨u, hu₀, hu⟩ := exists_weakEvolution_on_Icc B ell hab hell t₀ u₀
  let du : ℝ → V := fun t ↦ weakEvolutionVectorField B ell t (u t)
  refine ⟨u, du, hu₀, ?_, ?_, ?_⟩
  · intro t _ht
    rfl
  · intro t ht
    exact (hu t ht).1
  · intro t ht
    exact (hu t ht).2

/-- Build the Picard–Lindelöf hypotheses for a weak evolution vector field
from ordinary analytic assumptions.  The state Lipschitz constant is the
operator norm of the Riesz-represented form. -/
theorem isPicardLindelof_weakEvolutionVectorField
    (B : V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    {tmin tmax : ℝ} (t₀ : Set.Icc tmin tmax) (u₀ : V)
    (a L : NNReal)
    (hell : ContinuousOn ell (Set.Icc tmin tmax))
    (hnorm : ∀ t ∈ Set.Icc tmin tmax,
      ∀ u ∈ Metric.closedBall u₀ a, ‖weakEvolutionVectorField B ell t u‖ ≤ L)
    (hinterval : L * max (tmax - t₀) (t₀ - tmin) ≤ a) :
    IsPicardLindelof (weakEvolutionVectorField B ell) t₀ u₀ a 0 L
      ‖continuousLinearMapOfBilin B‖₊ where
  lipschitzOnWith t _ := by
    apply (LipschitzWith.of_dist_le_mul (fun x y ↦ ?_)).lipschitzOnWith
    have h := (continuousLinearMapOfBilin B).lipschitzWith.dist_le_mul y x
    simpa [weakEvolutionVectorField, dist_eq_norm, norm_sub_rev] using h
  continuousOn x _ := by
    have hriesz : ContinuousOn (fun t ↦ (toDual ℝ _).symm (ell t)) (Set.Icc tmin tmax) :=
      (toDual ℝ V).symm.continuous.comp_continuousOn hell
    exact hriesz.sub continuousOn_const
  norm_le := hnorm
  mul_max_le := by simpa using hinterval

/-- Time-dependent weak evolution existence under the standard
Picard–Lindelöf hypotheses for its Riesz-represented vector field.

Unlike the autonomous convenience theorem below, this result allows general
time-dependent forcing. Its hypotheses are exactly the usual local bounded,
continuous-in-time, Lipschitz-in-state assumptions of Mathlib's
`IsPicardLindelof`. -/
theorem exists_weakEvolution_of_isPicardLindelof
    (B : V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    {tmin tmax : ℝ} (t₀ : Set.Icc tmin tmax) (u₀ : V)
    (a L K : NNReal)
    (hPL : IsPicardLindelof (weakEvolutionVectorField B ell) t₀ u₀ a 0 L K) :
    ∃ u : ℝ → V, u t₀ = u₀ ∧ ∀ t ∈ Set.Icc tmin tmax,
      HasDerivWithinAt u (weakEvolutionVectorField B ell t (u t))
        (Set.Icc tmin tmax) t ∧
      SatisfiesWeakEvolutionAt B (ell t) (u t)
        (weakEvolutionVectorField B ell t (u t)) := by
  obtain ⟨u, hu₀, hu⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨u, hu₀, fun t ht ↦ ⟨hu t ht, ?_⟩⟩
  apply (satisfiesWeakEvolutionAt_iff_ode B (ell t) (u t) _).2
  rfl

/-- Time-dependent weak evolution existence stated with ordinary
Picard–Lindelöf assumptions instead of the `IsPicardLindelof` structure. -/
theorem exists_weakEvolution
    (B : V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    {tmin tmax : ℝ} (t₀ : Set.Icc tmin tmax) (u₀ : V)
    (a L : NNReal)
    (hell : ContinuousOn ell (Set.Icc tmin tmax))
    (hnorm : ∀ t ∈ Set.Icc tmin tmax,
      ∀ u ∈ Metric.closedBall u₀ a, ‖weakEvolutionVectorField B ell t u‖ ≤ L)
    (hinterval : L * max (tmax - t₀) (t₀ - tmin) ≤ a) :
    ∃ u : ℝ → V, u t₀ = u₀ ∧ ∀ t ∈ Set.Icc tmin tmax,
      HasDerivWithinAt u (weakEvolutionVectorField B ell t (u t))
        (Set.Icc tmin tmax) t ∧
      SatisfiesWeakEvolutionAt B (ell t) (u t)
        (weakEvolutionVectorField B ell t (u t)) := by
  exact exists_weakEvolution_of_isPicardLindelof B ell t₀ u₀ a L
    ‖continuousLinearMapOfBilin B‖₊
    (isPicardLindelof_weakEvolutionVectorField B ell t₀ u₀ a L
      hell hnorm hinterval)

/--
Picard–Lindelöf weak evolution existence, returned with an interval-level
weak equation.

The hypotheses are the local boundedness and step-size conditions; the
solution satisfies `SatisfiesWeakEvolutionOn`, so the energy and uniqueness
theorems apply to it.
-/
theorem exists_weakEvolutionOn
    (B : V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    {tmin tmax : ℝ} (t₀ : Set.Icc tmin tmax) (u₀ : V)
    (a L : NNReal)
    (hell : ContinuousOn ell (Set.Icc tmin tmax))
    (hnorm : ∀ t ∈ Set.Icc tmin tmax,
      ∀ u ∈ Metric.closedBall u₀ a, ‖weakEvolutionVectorField B ell t u‖ ≤ L)
    (hinterval : L * max (tmax - t₀) (t₀ - tmin) ≤ a) :
    ∃ u du : ℝ → V,
      u t₀ = u₀ ∧
      (∀ t ∈ Set.Icc tmin tmax, du t = weakEvolutionVectorField B ell t (u t)) ∧
      (∀ t ∈ Set.Icc tmin tmax,
        HasDerivWithinAt u (du t) (Set.Icc tmin tmax) t) ∧
      SatisfiesWeakEvolutionOn (fun _ ↦ B) ell u du (Set.Icc tmin tmax) := by
  obtain ⟨u, hu₀, hu⟩ := exists_weakEvolution B ell t₀ u₀ a L hell hnorm hinterval
  let du : ℝ → V := fun t ↦ weakEvolutionVectorField B ell t (u t)
  refine ⟨u, du, hu₀, ?_, ?_, ?_⟩
  · intro t _ht
    rfl
  · intro t ht
    exact (hu t ht).1
  · intro t ht
    exact (hu t ht).2

/-- Local existence for an autonomous weak evolution equation with bounded
bilinear form and constant forcing.  The proof is a direct application of
Picard–Lindelöf to the Riesz-represented affine vector field.

This supplies the finite-dimensional ODE existence step for Galerkin spaces
when the forcing is frozen in time; the general time-dependent Galerkin
problem additionally requires continuity or integrability hypotheses on the
forcing. -/
theorem exists_local_weakEvolution_const
    (B : V →L[ℝ] StrongDual ℝ V) (ell : StrongDual ℝ V)
    (t₀ : ℝ) (u₀ : V) :
    ∃ u : ℝ → V, u t₀ = u₀ ∧ ∃ ε > 0, ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
      HasDerivAt u ((toDual ℝ _).symm ell - continuousLinearMapOfBilin B (u t)) t ∧
      SatisfiesWeakEvolutionAt B ell (u t)
        ((toDual ℝ _).symm ell - continuousLinearMapOfBilin B (u t)) := by
  let F : V → V := fun u ↦ (toDual ℝ _).symm ell - continuousLinearMapOfBilin B u
  have hF : ContDiffAt ℝ 1 F u₀ := by
    dsimp [F]
    fun_prop
  obtain ⟨u, hu₀, ε, hε, hu⟩ :=
    hF.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  refine ⟨u, hu₀, ε, hε, fun t ht ↦ ⟨?_, ?_⟩⟩
  · exact hu t ht
  · apply (satisfiesWeakEvolutionAt_iff_ode B ell (u t) _).2
    rfl

end RieszReduction

end PDE.Analysis.Evolution
