/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Measurable.Bochner
public import PDE.Analysis.Evolution.Galerkin.TrialProjection
public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
public import PDE.Analysis.Evolution.Integrated.Solution
import PDE.Analysis.Evolution.Galerkin.ImprovedRegularity.ForcingCompletion
import PDE.Analysis.Evolution.Galerkin.ImprovedRegularity.NonautonomousEnergy
import PDE.Analysis.Evolution.Galerkin.Measurable.Bounds
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Galerkin limits with improved time regularity

We combine the dimension-independent nonautonomous energy estimate with
Galerkin compactness. Stable energy projections provide compatible initial
data, and the `L²(H)` velocity estimate survives the weak limit. The resulting
weak solution therefore has a pivot-valued distributional time derivative.

The Galerkin family for a Bochner `L²(H)` load is a hypothesis.
`exists_of_symmetric_principal_measurable_galerkin_L2_with_remainder` constructs such
families for bounded continuous loads and completes in `L²(H)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.3, Theorem 5(i) and step 2 of its proof (the
  passage to the limit), there for coefficients independent of `t`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

/-! ## Galerkin limits for symmetric principal forms -/

section SymmetricPrincipalGalerkinLimit

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The coercive state estimate is uniform under pivot-orthogonal projection
of the initial data and uses the `L²` norm of the pivot forcing. -/
private theorem norm_ambientTrajectoryLp_sq_le_projected
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    {K : NNReal} (P : StableTrialProjection T S K)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) {a b C M : ℝ}
    (f : Lp H 2 (volume.restrict (Ioc a b))) (hab : a ≤ b) (hC : 0 < C)
    (hcoercive : ∀ t ∈ Icc a b, ∀ w : V, C * ‖w‖ ^ 2 ≤ B t w w)
    (uInit : V)
    (G : AEGelfandGalerkinApproximation T S B (fun t ↦ T.pivotToDual (f t))
      a b C M (P.energyProjection uInit)) :
    ‖G.ambientTrajectoryLp hab‖ ^ 2 ≤
      (2 / C) * ((1 / 2 : ℝ) * ‖T.inclusion uInit‖ ^ 2 +
        (1 / (2 * C)) *
          ‖T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f‖ ^ 2) := by
  have hell := (Lp.memLp f).continuousLinearMap_comp T.pivotToDual
  have hforcing : hell.toLp (fun t ↦ T.pivotToDual (f t)) =
      T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f := by
    apply Lp.ext
    filter_upwards [hell.coeFn_toLp, T.pivotToDual.coeFn_compLpL f] with t ht hcomp
    rw [ht, hcomp]
  have hbasic := G.norm_ambientTrajectoryLp_sq_le_of_forcing_memLp hab hC hcoercive hell
  rw [hforcing] at hbasic
  refine hbasic.trans ?_
  gcongr
  simpa only [StableTrialProjection.energyProjection_apply] using
    P.norm_inclusion_projection_le (T.inclusion uInit)

/-- The weighted forcing and trajectory integral is exactly the sum of their
squared Bochner norms. The weight need not be nonnegative for this identity. -/
private theorem integral_norm_sq_add_mul_trajectory_eq
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {a b C M : ℝ} {u₀ : S}
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀)
    (hab : a ≤ b) (f : Lp H 2 (volume.restrict (Ioc a b))) (weight : ℝ) :
    (∫ t in a..b, ‖f t‖ ^ 2 + weight * ‖(G.trajectory t : V)‖ ^ 2) =
      ‖f‖ ^ 2 + weight * ‖G.ambientTrajectoryLp hab‖ ^ 2 := by
  have hcoe :
      (fun t ↦ ‖f t‖ ^ 2 + weight * ‖(G.trajectory t : V)‖ ^ 2) =ᵐ[
        volume.restrict (Ioc a b)]
      fun t ↦ ‖f t‖ ^ 2 + weight * ‖G.ambientTrajectoryLp hab t‖ ^ 2 := by
    filter_upwards [G.ambientTrajectoryLp_apply_ae hab] with t ht
    rw [ht]
  rw [intervalIntegral.integral_of_le hab, integral_congr_ae hcoe,
    integral_add ((Lp.memLp f).integrable_norm_pow (by norm_num))
      (((Lp.memLp (G.ambientTrajectoryLp hab)).integrable_norm_pow
        (by norm_num)).const_mul weight), integral_const_mul,
    ← Lp.norm_sq_eq_integral_norm_sq, ← Lp.norm_sq_eq_integral_norm_sq]

/-- Stable projection of the initial data and the basic state estimate turn
principal-energy differentiation into a bound independent of the trial dimension. -/
private theorem norm_pivotDerivativeLp_sq_le_projected
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    {K : NNReal} (P : StableTrialProjection T S K)
    (A Adot R : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b C M L : ℝ} {N : NNReal}
    (f : Lp H 2 (volume.restrict (Ioc a b))) (hab : a ≤ b) (hC : 0 < C)
    (hcoercive : ∀ t ∈ Icc a b, ∀ w : V, C * ‖w‖ ^ 2 ≤ (A t + R t) w w)
    (uInit : V)
    (G : AEGelfandGalerkinApproximation T S
      (fun t ↦ A t + R t) (fun t ↦ T.pivotToDual (f t))
      a b C M (P.energyProjection uInit))
    (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ t ∂(volume.restrict (Ioc a b)), HasDerivAt A (Adot t) t)
    (hAdot : ∀ᵐ t ∂(volume.restrict (Ioc a b)), ‖Adot t‖ ≤ N)
    (hA_symm : ∀ t ∈ Icc a b, ∀ u v : V, A t u v = A t v u)
    (hA_nonneg : ∀ u : V, 0 ≤ A b u u)
    (hR : ∀ t ∈ Icc a b, ∀ u v : V,
      |R t u v| ≤ L * ‖u‖ * ‖T.inclusion v‖) :
    ‖G.pivotDerivativeLp T S‖ ^ 2 ≤
      ‖A a‖ * ((K : ℝ) * ‖uInit‖) ^ 2 +
        2 * (‖f‖ ^ 2 + (L ^ 2 + (N : ℝ) / 2) *
          ((2 / C) * ((1 / 2 : ℝ) * ‖T.inclusion uInit‖ ^ 2 +
            (1 / (2 * C)) *
              ‖T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f‖ ^ 2))) := by
  let D : ℝ := (2 / C) * ((1 / 2 : ℝ) * ‖T.inclusion uInit‖ ^ 2 +
    (1 / (2 * C)) * ‖T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f‖ ^ 2)
  have hstate : ‖G.ambientTrajectoryLp hab‖ ^ 2 ≤ D :=
    norm_ambientTrajectoryLp_sq_le_projected T S P (fun t ↦ A t + R t)
      f hab hC hcoercive uInit G
  have hAinitial : A a (P.energyProjection uInit : V) (P.energyProjection uInit : V) ≤
      ‖A a‖ * ((K : ℝ) * ‖uInit‖) ^ 2 :=
    (le_abs_self _).trans <| ((A a).le_of_opNorm₂_le_of_le le_rfl (P.norm_le uInit)
      (P.norm_le uInit)).trans_eq (by ring)
  have hintegral :
      (∫ t in a..b, ‖f t‖ ^ 2 + (L ^ 2 + (N : ℝ) / 2) * ‖(G.trajectory t : V)‖ ^ 2) ≤
        ‖f‖ ^ 2 + (L ^ 2 + (N : ℝ) / 2) * D := by
    rw [integral_norm_sq_add_mul_trajectory_eq G hab f]
    gcongr
  exact (G.norm_pivotDerivativeLp_sq_le_of_symmetric_principal T S A Adot R f hab
    hAAC hAderiv hAdot hA_symm hA_nonneg hR).trans
    (add_le_add hAinitial (mul_le_mul_of_nonneg_left hintegral (by norm_num)))

namespace IsGelfandIntegratedWeakSolution

/--
Improved time regularity of weak solutions obtained from Galerkin approximations, for a
principal part that depends on time. Evans proves the corresponding statement for
coefficients independent of `t` (§7.1.3, Theorem 5(i)).

Let the parabolic form split as `B(t) = A(t) + R(t)`, where `A` is absolutely
continuous in operator norm, symmetric, nonnegative at the final time, and has
the operator-norm derivative `Adot(t)` almost everywhere, with `‖Adot(t)‖ ≤ N`
almost everywhere. The remainder satisfies

`|R(t)(u,v)| ≤ L ‖u‖_V ‖Jv‖_H`.

For initial data `uInit ∈ V`, use the uniformly `V`-stable energy projections
`PₘuInit` as the Galerkin initial values. Testing with `uₘ'`, the basic energy estimate,
and weak lower semicontinuity then produce a weak solution
whose distributional time derivative is represented by an element of
`L²(a,b;H)`.

The displayed bound records all constants used in the passage. In
particular, the first term controls the projected initial principal energy,
while the final term uses the coercive Galerkin state estimate with the
Bochner `L²(a,b;V*)` norm of the forcing. The equation retains `A(t) + R(t)`
throughout the weak limit; only the initial-energy term evaluates `A` at `a`.
-/
theorem exists_of_symmetric_principal_ae_approximations_with_remainder
    [CompleteSpace V] [CompleteSpace H]
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V)
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (A Adot R : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b C M L MB : ℝ} {N : NNReal}
    (f : Lp H 2 (volume.restrict (Set.Ioc a b)))
    (hab : a < b) (hC : 0 < C) (hMB : 0 ≤ MB)
    (hBmeas : AEStronglyMeasurable (fun t ↦ A t + R t)
      (volume.restrict (Set.Ioc a b)))
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      ‖A t + R t‖ ≤ MB)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ (A t + R t) w w)
    (uInit : V)
    (G : ∀ n, AEGelfandGalerkinApproximation T (S n)
      (fun t ↦ A t + R t) (fun t ↦ T.pivotToDual (f t))
      a b C M ((P n).energyProjection uInit))
    (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ t ∂(volume.restrict (Ioc a b)), HasDerivAt A (Adot t) t)
    (hAdot : ∀ᵐ t ∂(volume.restrict (Ioc a b)), ‖Adot t‖ ≤ N)
    (hA_symm : ∀ t ∈ Icc a b, ∀ u v : V, A t u v = A t v u)
    (hA_nonneg : ∀ u : V, 0 ≤ A b u u)
    (hR : ∀ t ∈ Set.Icc a b, ∀ u v : V,
      |R t u v| ≤ L * ‖u‖ * ‖T.inclusion v‖) :
    ∃ (u : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (du : Lp H 2 (volume.restrict (Set.Ioc a b))),
      IsGelfandIntegratedWeakSolution T (fun t ↦ A t + R t)
          (fun t ↦ T.pivotToDual (f t)) u (T.inclusion uInit) ∧
      HasGelfandWeakTimeDerivativeOn T u
        (T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) du) ∧
      ‖du‖ ^ 2 ≤
        ‖A a‖ * ((K : ℝ) * ‖uInit‖) ^ 2 +
          2 * (‖f‖ ^ 2 + (L ^ 2 + (N : ℝ) / 2) *
            ((2 / C) *
              ((1 / 2 : ℝ) * ‖T.inclusion uInit‖ ^ 2 +
                (1 / (2 * C)) *
                  ‖T.pivotToDual.compLpL 2
                    (volume.restrict (Set.Ioc a b)) f‖ ^ 2))) ∧
      (∀ stateBound : ℝ,
        (∀ n, ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
          ‖(G n).ambientTrajectoryLp hab.le t‖ ≤ stateBound) →
        ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
          ‖u t‖ ≤ stateBound) := by
  have hu₀ : Filter.Tendsto (fun n ↦ T.inclusion ((P n).energyProjection uInit : V))
      Filter.atTop (nhds (T.inclusion uInit)) :=
    (T.inclusion.continuous.tendsto uInit).comp
      (StableTrialProjection.tendsto_energyProjection_of_eventually_approximable P hdenseEnergy
        uInit)
  have hvelocity (n : ℕ) := norm_pivotDerivativeLp_sq_le_projected T (S n) (P n) A Adot R f
    hab.le hC hcoercive uInit (G n) hAAC hAderiv hAdot hA_symm hA_nonneg hR
  obtain ⟨u, du, hsolution, hderivative, -, hdu, hstateBoundPreserved⟩ :=
    exists_of_ae_approximations_with_pivot_derivative_eq_residual T S P hdenseEnergy
      (fun t ↦ A t + R t) (fun t ↦ T.pivotToDual (f t)) hab hC hMB hBmeas hBbound
      ((Lp.memLp f).continuousLinearMap_comp T.pivotToDual)
      (fun n ↦ (P n).energyProjection uInit) (T.inclusion uInit) hu₀
      (‖T.inclusion uInit‖ ^ 2) (by positivity)
      (fun n ↦ pow_le_pow_left₀ (norm_nonneg _) (by
        simpa only [StableTrialProjection.energyProjection_apply] using
          (P n).norm_inclusion_projection_le (T.inclusion uInit)) 2)
      G _ (by positivity) hvelocity
  exact ⟨u, du, hsolution, hderivative, hdu, hstateBoundPreserved⟩

end IsGelfandIntegratedWeakSolution

end SymmetricPrincipalGalerkinLimit

end PDE.Analysis.Evolution
