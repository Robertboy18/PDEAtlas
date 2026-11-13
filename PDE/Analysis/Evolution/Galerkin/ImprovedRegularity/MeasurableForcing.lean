/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.TrialProjection
public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
public import PDE.Analysis.Evolution.Integrated.Solution
import PDE.Analysis.Evolution.Galerkin.ImprovedRegularity.ForcingCompletion
import PDE.Analysis.Evolution.Galerkin.ImprovedRegularity.GalerkinLimit
import PDE.Analysis.Evolution.Galerkin.ImprovedRegularity.NonautonomousEnergy
import PDE.Analysis.Evolution.Galerkin.Measurable.Bounds
import PDE.Analysis.Evolution.Galerkin.Measurable.Caratheodory

/-!
# Measurable forcing in Evans's first regularity theorem

We construct weak solutions with improved time regularity for arbitrary
Bochner `L²(H)` forcing. The symmetric principal form is absolutely continuous
in operator norm. Its derivative `Adot` is identified almost everywhere
and has essentially bounded operator norm. A measurable lower-order remainder
satisfies the mixed estimate

`|R(t)(u,v)| ≤ L ‖u‖_V ‖Jv‖_H`.

Both the principal form and the full form are coercive on the energy space `V`.
The trial spaces have uniformly `V`-stable pivot projections and approximate every
element of `V`. Finite-dimensional trajectories are constructed from these data.

The bounds depend continuously on the load, so the load can be approximated by bounded
continuous functions while every approximating problem keeps the same form `A(t) + R(t)`.
Neither the remainder nor the forcing is differentiated. The limit satisfies the weak
equation, has an `L²(H)` time derivative equal to the residual, and obeys the explicit
velocity and `L∞(V)` estimates. Evans proves the corresponding statement,
`u' ∈ L²(0, T; L²(U))`, for coefficients independent of `t` (§7.1.3, Theorem 5(i)).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.3, Theorem 5(i). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

/-! ## Measurable pivot forcing -/

section MeasurablePivotForcing

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

namespace IsGelfandIntegratedWeakSolution

/--
The coercive `L²(a,b;V)` state bound used in Evans's first regularity
improvement.  Writing it as a function of the pivot load makes the bound
continuous under Bochner `L²(H)` approximation.
-/
private def symmetricPrincipalStateBound
    (T : GelfandTriple (V := V) (H := H))
    (a b C : ℝ) (uInit : V) :
    Lp H 2 (volume.restrict (Set.Ioc a b)) → ℝ := fun g ↦
  (2 / C) *
    ((1 / 2 : ℝ) * ‖T.inclusion uInit‖ ^ 2 +
      (1 / (2 * C)) *
        ‖T.pivotToDual.compLpL 2
          (volume.restrict (Set.Ioc a b)) g‖ ^ 2)

/--
The squared `L²(a,b;H)` bound for the Galerkin time derivatives.  Its first
term is the projected initial principal energy; the second combines the
pivot load with the lower-order remainder and the derivative of the principal form.
-/
private def symmetricPrincipalVelocityBound
    (T : GelfandTriple (V := V) (H := H))
    (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    (a b C K L N : ℝ) (uInit : V) :
    Lp H 2 (volume.restrict (Set.Ioc a b)) → ℝ := fun g ↦
  ‖A a‖ * (K * ‖uInit‖) ^ 2 +
    2 * (‖g‖ ^ 2 +
      (L ^ 2 + N / 2) * symmetricPrincipalStateBound T a b C uInit g)

/--
Coercivity converts the improved principal-energy estimate into an almost
everywhere `L∞(a,b;V)` bound for the completed state.
-/
private def symmetricPrincipalLinftyStateBound
    (T : GelfandTriple (V := V) (H := H))
    (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    (a b C K L N : ℝ) (uInit : V) :
    Lp H 2 (volume.restrict (Set.Ioc a b)) → ℝ := fun g ↦
  √
    (symmetricPrincipalVelocityBound T A a b C K L N uInit g / C)

private theorem continuous_symmetricPrincipalVelocityBound
    (T : GelfandTriple (V := V) (H := H))
    (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    (a b C K L N : ℝ) (uInit : V) :
    Continuous
      (symmetricPrincipalVelocityBound T A a b C K L N uInit) := by
  unfold symmetricPrincipalVelocityBound symmetricPrincipalStateBound
  fun_prop

private theorem continuous_symmetricPrincipalLinftyStateBound
    (T : GelfandTriple (V := V) (H := H))
    (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    (a b C K L N : ℝ) (uInit : V) :
    Continuous
      (symmetricPrincipalLinftyStateBound T A a b C K L N uInit) := by
  unfold symmetricPrincipalLinftyStateBound
    symmetricPrincipalVelocityBound symmetricPrincipalStateBound
  fun_prop

/-- The basic state estimate and principal coercivity give the uniform
almost-everywhere energy-space bound for a single projected trajectory. -/
private theorem ae_norm_ambientTrajectoryLp_le_projected
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
    (hAprincipal : ∀ t ∈ Icc a b, ∀ w : V, C * ‖w‖ ^ 2 ≤ A t w w)
    (hR : ∀ t ∈ Icc a b, ∀ u v : V,
      |R t u v| ≤ L * ‖u‖ * ‖T.inclusion v‖) :
    ∀ᵐ t ∂(volume.restrict (Ioc a b)), ‖G.ambientTrajectoryLp hab t‖ ≤
      symmetricPrincipalLinftyStateBound T A a b C K L N uInit f := by
  have hell : MemLp (fun t ↦ T.pivotToDual (f t)) 2 (volume.restrict (Ioc a b)) :=
    (Lp.memLp f).continuousLinearMap_comp T.pivotToDual
  have hellToLp : hell.toLp _ = T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f :=
    Lp.ext <| hell.coeFn_toLp.trans (T.pivotToDual.coeFn_compLpL f).symm
  have hstateL2 :
      ‖G.ambientTrajectoryLp hab‖ ^ 2 ≤ symmetricPrincipalStateBound T a b C uInit f := by
    refine (hellToLp ▸ G.norm_ambientTrajectoryLp_sq_le_of_forcing_memLp hab hC hcoercive
      hell).trans ?_
    unfold symmetricPrincipalStateBound
    gcongr
    simpa only [StableTrialProjection.energyProjection_apply] using
      P.norm_inclusion_projection_le (T.inclusion uInit)
  filter_upwards [G.ambientTrajectoryLp_apply_ae hab, ae_restrict_mem measurableSet_Ioc]
    with t hcoe ht
  rw [hcoe]
  refine (G.norm_trajectory_le_of_symmetric_principal_coercive T S A Adot R f hab hC hAAC hAderiv
    hAdot hA_symm hAprincipal hR hstateL2 t (Ioc_subset_Icc_self ht)).trans ?_
  unfold symmetricPrincipalLinftyStateBound symmetricPrincipalVelocityBound
  gcongr
  exact P.norm_le uInit

/--
The bounded-continuous forcing stage of the time-regularity theorem.

The Carathéodory solver first constructs finite-dimensional trajectories.
The nonautonomous symmetric estimate controls their pivot derivatives, while
principal coercivity upgrades the same estimate to an almost-everywhere
state bound.
-/
private theorem exists_of_boundedContinuous_symmetric_principal
    [CompleteSpace V] [CompleteSpace H]
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V)
    (hfinite : ∀ n, FiniteDimensional ℝ (S n))
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (A Adot R : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b C L : ℝ} {N : NNReal}
    (hab : a < b) (hC : 0 < C)
    (hBmeas : AEStronglyMeasurable (fun t ↦ A t + R t)
      (volume.restrict (Set.Icc a b)))
    (hBmeasIoc : AEStronglyMeasurable (fun t ↦ A t + R t)
      (volume.restrict (Set.Ioc a b)))
    (MB : NNReal)
    (hBbound : ∀ t ∈ Set.Icc a b, ‖A t + R t‖ ≤ MB)
    (hBboundAE : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      ‖A t + R t‖ ≤ (MB : ℝ))
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ (A t + R t) w w)
    (uInit : V)
    (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ t ∂(volume.restrict (Ioc a b)), HasDerivAt A (Adot t) t)
    (hAdot : ∀ᵐ t ∂(volume.restrict (Ioc a b)), ‖Adot t‖ ≤ N)
    (hA_symm : ∀ t ∈ Icc a b, ∀ u v : V, A t u v = A t v u)
    (hAprincipal : ∀ t ∈ Icc a b, ∀ w : V, C * ‖w‖ ^ 2 ≤ A t w w)
    (hR : ∀ t ∈ Set.Icc a b, ∀ u v : V,
      |R t u v| ≤ L * ‖u‖ * ‖T.inclusion v‖)
    (fCont : BoundedContinuousFunction ℝ H) :
    ∃ (u : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (du : Lp H 2 (volume.restrict (Set.Ioc a b))),
      IsGelfandIntegratedWeakSolution T (fun t ↦ A t + R t)
          (fun t ↦ T.pivotToDual (fCont t)) u (T.inclusion uInit) ∧
      HasGelfandWeakTimeDerivativeOn T u
        (T.pivotToDual.compLpL 2
          (volume.restrict (Set.Ioc a b)) du) ∧
      ‖du‖ ^ 2 ≤
        symmetricPrincipalVelocityBound T A a b C K L N uInit
          (BoundedContinuousFunction.toLp 2
            (volume.restrict (Set.Ioc a b)) ℝ fCont) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        ‖u t‖ ≤
          symmetricPrincipalLinftyStateBound T A a b C K L N uInit
            (BoundedContinuousFunction.toLp 2
              (volume.restrict (Set.Ioc a b)) ℝ fCont)) := by
  let μab := volume.restrict (Set.Ioc a b)
  let fLp : Lp H 2 μab := BoundedContinuousFunction.toLp 2 μab ℝ fCont
  have hellBound (t : ℝ) (_ : t ∈ Set.Icc a b) :
      ‖T.pivotToDual (fCont t)‖ ≤ (‖T.pivotToDual‖₊ * ‖fCont‖₊ : NNReal) := by
    simpa only [NNReal.coe_mul, coe_nnnorm] using (T.pivotToDual.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (fCont.norm_coe_le_norm t) (norm_nonneg _))
  obtain ⟨G⟩ := AEGelfandGalerkinApproximation.exists_sequence T S hfinite (fun t ↦ A t + R t)
    (fun t ↦ T.pivotToDual (fCont t)) hab.le hC (fun v ↦ hBmeas.apply_continuousLinearMap v)
    (T.pivotToDual.continuous.comp fCont.continuous).aestronglyMeasurable.restrict MB _ hBbound
    hellBound hcoercive fun n ↦ (P n).energyProjection uInit
  have hellAE : (fun t ↦ T.pivotToDual (fCont t)) =ᵐ[μab] fun t ↦ T.pivotToDual (fLp t) :=
    (BoundedContinuousFunction.coeFn_toLp (p := 2) (μ := μab) (𝕜 := ℝ) fCont).mono
      fun _ ht ↦ congrArg T.pivotToDual ht.symm
  let G' n := (G n).congrForcingAE hellAE
  have hA_nonneg (w : V) : 0 ≤ A b w w :=
    (mul_nonneg hC.le (sq_nonneg _)).trans (hAprincipal b ⟨hab.le, le_rfl⟩ w)
  obtain ⟨u, du, hsolution, hderivative, hdu, hstateBoundPreserved⟩ :=
    exists_of_symmetric_principal_ae_approximations_with_remainder T S P hdenseEnergy A Adot R fLp
      hab hC MB.2 hBmeasIoc hBboundAE hcoercive uInit G' hAAC hAderiv hAdot hA_symm hA_nonneg hR
  exact ⟨u, du, hsolution.congr_forcing_ae hellAE.symm, hderivative, hdu,
    hstateBoundPreserved _ fun n ↦ ae_norm_ambientTrajectoryLp_le_projected T (S n) (P n) A Adot R
      fLp hab.le hC hcoercive uInit (G' n) hAAC hAderiv hAdot hA_symm hAprincipal hR⟩

/--
Time regularity for an arbitrary Bochner `L²(H)` forcing.

For bounded continuous pivot loads the measurable Carathéodory solver
constructs the Galerkin family internally. The improved Galerkin estimate
uses only the load's `L²` norm, so density and coercive completion pass both
the solution and its `L²(H)` time derivative to an arbitrary Bochner load.
The functions `A`, `Adot`, and `R` are fixed across these forcing approximations,
and `A` remains time-dependent in the limiting equation.
The derivative bound `N` of the principal form contributes `N/2` beside the
remainder's coefficient `L²` in the energy budget. Principal coercivity gives
the `L∞(V)` bound; coercivity of the full form supplies the basic `L²(V)`
estimate and continuous dependence on the load.
-/
theorem exists_of_symmetric_principal_measurable_galerkin_L2_with_remainder
    [CompleteSpace V] [CompleteSpace H]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V)
    (hfinite : ∀ n, FiniteDimensional ℝ (S n))
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (A Adot R : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b C L : ℝ} {N : NNReal}
    (f : Lp H 2 (volume.restrict (Set.Ioc a b)))
    (hab : a < b) (hC : 0 < C)
    (hBmeas : AEStronglyMeasurable (fun t ↦ A t + R t)
      (volume.restrict (Set.Icc a b)))
    (MB : NNReal)
    (hBbound : ∀ t ∈ Set.Icc a b, ‖A t + R t‖ ≤ MB)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ (A t + R t) w w)
    (uInit : V)
    (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ t ∂(volume.restrict (Ioc a b)), HasDerivAt A (Adot t) t)
    (hAdot : ∀ᵐ t ∂(volume.restrict (Ioc a b)), ‖Adot t‖ ≤ N)
    (hA_symm : ∀ t ∈ Icc a b, ∀ u v : V, A t u v = A t v u)
    (hAprincipal : ∀ t ∈ Icc a b, ∀ w : V, C * ‖w‖ ^ 2 ≤ A t w w)
    (hR : ∀ t ∈ Set.Icc a b, ∀ u v : V,
      |R t u v| ≤ L * ‖u‖ * ‖T.inclusion v‖) :
    ∃ (u : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (du : Lp H 2 (volume.restrict (Set.Ioc a b))),
      IsGelfandIntegratedWeakSolution T (fun t ↦ A t + R t)
          (fun t ↦ T.pivotToDual (f t)) u (T.inclusion uInit) ∧
      HasGelfandWeakTimeDerivativeOn T u
        (T.pivotToDual.compLpL 2
          (volume.restrict (Set.Ioc a b)) du) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        T.pivotToDual (du t) + A t (u t) + R t (u t) =
          T.pivotToDual (f t)) ∧
      ‖du‖ ^ 2 ≤
        ‖A a‖ * (K * ‖uInit‖) ^ 2 +
          2 * (‖f‖ ^ 2 + (L ^ 2 + (N : ℝ) / 2) *
            ((2 / C) *
              ((1 / 2 : ℝ) * ‖T.inclusion uInit‖ ^ 2 +
                (1 / (2 * C)) *
                  ‖T.pivotToDual.compLpL 2
                    (volume.restrict (Set.Ioc a b)) f‖ ^ 2))) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        ‖u t‖ ≤
          √
            ((‖A a‖ * (K * ‖uInit‖) ^ 2 +
                2 * (‖f‖ ^ 2 + (L ^ 2 + (N : ℝ) / 2) *
                  ((2 / C) *
                    ((1 / 2 : ℝ) * ‖T.inclusion uInit‖ ^ 2 +
                      (1 / (2 * C)) *
                        ‖T.pivotToDual.compLpL 2
                          (volume.restrict (Set.Ioc a b)) f‖ ^ 2)))) / C)) := by
  let μab := volume.restrict (Set.Ioc a b)
  let B : ℝ → V →L[ℝ] StrongDual ℝ V := fun t ↦ A t + R t
  have hBmeasIoc : AEStronglyMeasurable B μab :=
    hBmeas.mono_measure (Measure.restrict_mono_set _ Ioc_subset_Icc_self)
  have hBboundAE : ∀ᵐ t ∂μab, ‖B t‖ ≤ (MB : ℝ) :=
    (ae_restrict_mem measurableSet_Ioc).mono fun t ht ↦ hBbound t (Ioc_subset_Icc_self ht)
  obtain ⟨u, du, hsolution, hderivative, hresidual, hdu, hstate⟩ :=
    exists_of_boundedContinuous_pivot_forcing T B f hab hC hBmeasIoc (MB : ℝ) hBboundAE hcoercive
      (T.inclusion uInit) _ (continuous_symmetricPrincipalVelocityBound T A a b C K L N uInit) _
      (continuous_symmetricPrincipalLinftyStateBound T A a b C K L N uInit)
      (exists_of_boundedContinuous_symmetric_principal T S hfinite P hdenseEnergy A Adot R hab hC
        hBmeas hBmeasIoc MB hBbound hBboundAE hcoercive uInit hAAC hAderiv hAdot hA_symm
        hAprincipal hR)
  have hresidualToDerivative :
      (gelfandResidualLp B (T.pivotToDual.compLpL 2 μab f) u
          (fun v ↦ hBmeasIoc.apply_continuousLinearMap v) (MB : ℝ) hBboundAE :
          ℝ → StrongDual ℝ V) =ᵐ[μab] fun t ↦ T.pivotToDual (du t) :=
    hresidual ▸ T.pivotToDual.coeFn_compLpL du
  refine ⟨u, du, hsolution, hderivative, ?_, hdu, hstate⟩
  filter_upwards [hresidualToDerivative, gelfandResidualLp_apply_ae B _ u
      (fun v ↦ hBmeasIoc.apply_continuousLinearMap v) (MB : ℝ) hBboundAE,
    T.pivotToDual.coeFn_compLpL f] with t hduCoe hresCoe hfCoe
  rw [← hduCoe, hresCoe, hfCoe, add_apply]
  abel

/-- The case `R = 0` of
`exists_of_symmetric_principal_measurable_galerkin_L2_with_remainder`: the form is
the symmetric, coercive, absolutely continuous principal part alone. -/
theorem exists_of_symmetric_principal_measurable_galerkin_L2
    [CompleteSpace V] [CompleteSpace H]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V)
    (hfinite : ∀ n, FiniteDimensional ℝ (S n))
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (A Adot : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b C : ℝ} {N : NNReal}
    (f : Lp H 2 (volume.restrict (Set.Ioc a b)))
    (hab : a < b) (hC : 0 < C)
    (hAmeas : AEStronglyMeasurable A (volume.restrict (Set.Icc a b)))
    (MB : NNReal)
    (hAbound : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ MB)
    (uInit : V)
    (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ t ∂(volume.restrict (Ioc a b)), HasDerivAt A (Adot t) t)
    (hAdot : ∀ᵐ t ∂(volume.restrict (Ioc a b)), ‖Adot t‖ ≤ N)
    (hA_symm : ∀ t ∈ Icc a b, ∀ u v : V, A t u v = A t v u)
    (hAprincipal : ∀ t ∈ Icc a b, ∀ w : V, C * ‖w‖ ^ 2 ≤ A t w w) :
    ∃ (u : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (du : Lp H 2 (volume.restrict (Set.Ioc a b))),
      IsGelfandIntegratedWeakSolution T A
          (fun t ↦ T.pivotToDual (f t)) u (T.inclusion uInit) ∧
      HasGelfandWeakTimeDerivativeOn T u
        (T.pivotToDual.compLpL 2
          (volume.restrict (Set.Ioc a b)) du) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        T.pivotToDual (du t) + A t (u t) = T.pivotToDual (f t)) ∧
      ‖du‖ ^ 2 ≤
        ‖A a‖ * (K * ‖uInit‖) ^ 2 +
          2 * (‖f‖ ^ 2 + (N : ℝ) / 2 *
            ((2 / C) *
              ((1 / 2 : ℝ) * ‖T.inclusion uInit‖ ^ 2 +
                (1 / (2 * C)) *
                  ‖T.pivotToDual.compLpL 2
                    (volume.restrict (Set.Ioc a b)) f‖ ^ 2))) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        ‖u t‖ ≤
          √
            ((‖A a‖ * (K * ‖uInit‖) ^ 2 +
                2 * (‖f‖ ^ 2 + (N : ℝ) / 2 *
                  ((2 / C) *
                    ((1 / 2 : ℝ) * ‖T.inclusion uInit‖ ^ 2 +
                      (1 / (2 * C)) *
                        ‖T.pivotToDual.compLpL 2
                          (volume.restrict (Set.Ioc a b)) f‖ ^ 2)))) / C)) := by
  have hAR : (fun t ↦ A t + (0 : V →L[ℝ] StrongDual ℝ V)) = A := funext fun t ↦ add_zero (A t)
  obtain ⟨u, du, hsolution, hderivative, hresidual, hdu, hstate⟩ :=
    exists_of_symmetric_principal_measurable_galerkin_L2_with_remainder (L := 0)
      T S hfinite P hdenseEnergy A Adot (fun _ ↦ 0) f hab hC (by rwa [hAR]) MB
      (fun t ht ↦ by rw [congrFun hAR t]; exact hAbound t ht)
      (fun t ht ↦ by rw [congrFun hAR t]; exact hAprincipal t ht)
      uInit hAAC hAderiv hAdot hA_symm hAprincipal fun t _ u v ↦ by simp
  rw [hAR] at hsolution
  refine ⟨u, du, hsolution, hderivative, ?_, ?_, ?_⟩
  · filter_upwards [hresidual] with t ht
    rwa [zero_apply, add_zero] at ht
  · simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] using hdu
  · simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] using hstate

end IsGelfandIntegratedWeakSolution

end MeasurablePivotForcing

end PDE.Analysis.Evolution
