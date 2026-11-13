/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Gelfand.Existence
public import PDE.Analysis.Evolution.Galerkin.Measurable.L2Caratheodory
public import PDE.Analysis.Evolution.Galerkin.OrthogonalFamily
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Pivot coefficients of absolutely continuous Galerkin solutions

Testing the Carathéodory trajectory gives absolutely continuous scalar
coefficients satisfying the projected equation almost everywhere. Conversely, an
absolutely continuous trial trajectory with the weak projected equation solves
the same mass-inverted system, so the usual uniqueness theorem applies.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped InnerProductSpace

namespace PDE.Analysis.Evolution.AffineCaratheodorySolutionOn

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
  [FiniteDimensional ℝ S] [CompleteSpace S]
  {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
  {a b : ℝ} {u₀ : S}

variable (U : AffineCaratheodorySolutionOn
  (fun t ↦ -(gelfandGalerkinOperator T S (B t)))
  (gelfandGalerkinForcing T S ell) a b u₀)

/-- Every pivot coefficient of an AC Galerkin trajectory is absolutely
continuous, including at both endpoints of the time interval. -/
theorem gelfandGalerkin_coefficient_absolutelyContinuous (v : V) :
    AbsolutelyContinuousOnInterval
      (fun t ↦ ⟪T.inclusion v, T.inclusion (U.trajectory t : V)⟫_ℝ) a b := by
  let L := ((innerSL ℝ (T.inclusion v)).comp T.inclusion).comp S.subtypeL
  exact L.lipschitzWith.comp_absolutelyContinuousOnInterval U.absolutely_continuous

/-- For every `v ∈ S`, the coefficient `t ↦ ⟪ι v, ι u(t)⟫_H` has derivative
`ℓ(t)(v) - B(t)(u(t), v)` almost everywhere. -/
theorem gelfandGalerkin_coefficient_equation (v : S) :
    ∀ᵐ t ∂volume.restrict (Ioc a b),
      HasDerivAt (fun t ↦ ⟪T.inclusion (v : V), T.inclusion (U.trajectory t : V)⟫_ℝ)
        (ell t (v : V) - B t (U.trajectory t : V) (v : V)) t := by
  let L := ((innerSL ℝ (T.inclusion (v : V))).comp T.inclusion).comp S.subtypeL
  filter_upwards [U.gelfandGalerkin_derivative_ae] with t ht
  have heq := gelfandGalerkinVectorField_equation T S B ell t (U.trajectory t) v
  have hderiv := L.hasFDerivAt.comp_hasDerivAt t ht
  apply hderiv.congr_deriv
  change ⟪T.inclusion (v : V),
    T.inclusion (gelfandGalerkinVectorField T S B ell t (U.trajectory t) : V)⟫_ℝ = _
  rw [real_inner_comm]
  exact eq_sub_of_add_eq heq

/-- Uniqueness against an arbitrary AC trial trajectory satisfying the weak
projected equation with its derivative and the same initial value. -/
theorem gelfandGalerkin_eq_of_weakEquation (hab : a ≤ b)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) (volume.restrict (Icc a b)))
    (MB : NNReal) (hbound : ∀ t ∈ Icc a b, ‖B t‖ ≤ MB)
    (u du : ℝ → S) (hinit : u a = u₀)
    (hAC : AbsolutelyContinuousOnInterval u a b)
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt u (du t) t)
    (heq : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : S,
      ⟪T.inclusion (du t : V), T.inclusion (v : V)⟫_ℝ +
        B t (u t : V) (v : V) = ell t (v : V)) :
    EqOn U.trajectory u (Icc a b) := by
  let W : AffineCaratheodorySolutionOn
      (fun t ↦ -(gelfandGalerkinOperator T S (B t)))
      (gelfandGalerkinForcing T S ell) a b u₀ :=
    { trajectory := u
      initial_value := hinit
      absolutely_continuous := hAC
      equation_ae := by
        filter_upwards [hderiv, heq] with t ht hweak
        apply ht.congr_deriv
        exact (gelfandGalerkin_derivative_eq_vectorField T S B ell t (u t) (du t)
          hweak).trans (neg_gelfandGalerkinOperator_add_forcing T S B ell t (u t)).symm }
  exact U.gelfandGalerkin_trajectory_eq hab W hB MB hbound

end PDE.Analysis.Evolution.AffineCaratheodorySolutionOn

namespace PDE.Analysis.Evolution.AffineCaratheodorySolutionOn

variable {V H ι : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {T : GelfandTriple (V := V) (H := H)} {w : ι → V} (s : Finset ι)

variable [FiniteDimensional ℝ (Submodule.span ℝ (w '' (s : Set ι)))]
  [CompleteSpace (Submodule.span ℝ (w '' (s : Set ι)))]
  {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
  {a b : ℝ} {u₀ : Submodule.span ℝ (w '' (s : Set ι))}
  (U : AffineCaratheodorySolutionOn
    (fun t ↦ -(gelfandGalerkinOperator T (Submodule.span ℝ (w '' (s : Set ι))) (B t)))
    (gelfandGalerkinForcing T (Submodule.span ℝ (w '' (s : Set ι))) ell) a b u₀)

/-- The finite vector of pivot coefficients is absolutely continuous and
satisfies the scalar Galerkin equations simultaneously almost everywhere. -/
theorem gelfandGalerkin_finiteCoefficients :
    let d := fun t (i : s) ↦ ⟪T.inclusion (w i), T.inclusion (U.trajectory t : V)⟫_ℝ
    AbsolutelyContinuousOnInterval d a b ∧
      ∀ᵐ t ∂volume.restrict (Ioc a b),
        HasDerivAt d (fun i ↦ ell t (w i) - B t (U.trajectory t : V) (w i)) t := by
  let L : Submodule.span ℝ (w '' (s : Set ι)) →L[ℝ] (s → ℝ) := ContinuousLinearMap.pi fun i ↦
    ((innerSL ℝ (T.inclusion (w i))).comp T.inclusion).comp
      (Submodule.span ℝ (w '' (s : Set ι))).subtypeL
  refine ⟨L.lipschitzWith.comp_absolutelyContinuousOnInterval U.absolutely_continuous, ?_⟩
  have hcoeff (i : s) := U.gelfandGalerkin_coefficient_equation
    ⟨w i, Submodule.subset_span ⟨i, i.property, rfl⟩⟩
  filter_upwards [ae_all_iff.2 hcoeff] with t ht
  exact hasDerivAt_pi.mpr ht

/-- Any AC coefficient vector with the same initial value and the scalar
Galerkin equations agrees with the coefficients of the constructed trajectory.
The proof synthesizes a trial trajectory and applies weak-equation uniqueness. -/
theorem gelfandGalerkin_finiteCoefficients_unique
    {K : NNReal} (P : StableTrialProjection T (Submodule.span ℝ (w '' (s : Set ι))) K)
    (hJw : Orthonormal ℝ (fun i ↦ T.inclusion (w i))) (hab : a ≤ b)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) (volume.restrict (Icc a b)))
    (MB : NNReal) (hbound : ∀ t ∈ Icc a b, ‖B t‖ ≤ MB)
    (e : ℝ → s → ℝ) (hAC : AbsolutelyContinuousOnInterval e a b)
    (hinit : ∀ i, e a i = ⟪T.inclusion (w i), T.inclusion (u₀ : V)⟫_ℝ)
    (heq : ∀ᵐ t ∂volume.restrict (Ioc a b),
      HasDerivAt e
        (fun i ↦ ell t (w i) - B t (finiteTrialCombination w s (e t) : V) (w i)) t) :
    EqOn (fun t (i : s) ↦ ⟪T.inclusion (w i), T.inclusion (U.trajectory t : V)⟫_ℝ)
      e (Icc a b) := by
  let F := finiteTrialCombination w s
  let u := fun t ↦ F (e t)
  let de := fun t (i : s) ↦ ell t (w i) - B t (u t : V) (w i)
  let du := fun t ↦ F (de t)
  have huinit : u a = u₀ := by
    change F (e a) = u₀
    rw [show e a = fun (i : s) ↦ ⟪T.inclusion (w i), T.inclusion (u₀ : V)⟫_ℝ
      from funext hinit]
    exact P.finiteTrialCombination_inner_eq_self T hJw s u₀
  have huderiv : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt u (du t) t := by
    filter_upwards [heq] with t ht
    exact F.hasFDerivAt.comp_hasDerivAt t ht
  have hueq : ∀ t, ∀ v : Submodule.span ℝ (w '' (s : Set ι)),
      ⟪T.inclusion (du t : V), T.inclusion (v : V)⟫_ℝ +
        B t (u t : V) (v : V) = ell t (v : V) := by
    intro t
    let L := (innerSL ℝ (T.inclusion (du t : V))).comp T.inclusion + B t (u t : V)
    have hgen : EqOn L (ell t) (w '' (s : Set ι)) := by
      rintro _ ⟨i, hi, rfl⟩
      change ⟪T.inclusion (F (de t) : V), T.inclusion (w i)⟫_ℝ +
        B t (u t : V) (w i) = ell t (w i)
      rw [real_inner_comm, inner_inclusion_finiteTrialCombination T hJw s (de t) ⟨i, hi⟩]
      exact sub_add_cancel _ _
    exact fun v ↦ LinearMap.eqOn_span' (f := L.toLinearMap) (g := (ell t).toLinearMap)
      hgen v.property
  have hequal := U.gelfandGalerkin_eq_of_weakEquation hab hB MB hbound u du huinit
    (F.lipschitzWith.comp_absolutelyContinuousOnInterval hAC) huderiv
    (Eventually.of_forall hueq)
  intro t ht
  funext i
  change ⟪T.inclusion (w i), T.inclusion (U.trajectory t : V)⟫_ℝ = e t i
  rw [hequal ht]
  exact inner_inclusion_finiteTrialCombination T hJw s (e t) i

end PDE.Analysis.Evolution.AffineCaratheodorySolutionOn
