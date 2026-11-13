/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
public import PDE.Analysis.Evolution.Integrated.Solution
public import PDE.Elliptic.Regularity.SolutionOperator.H2
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2
import PDE.Analysis.Evolution.Galerkin.ImprovedRegularity.MeasurableForcing
import PDE.Parabolic.Regularity.SpatialH2.WeakResidual
import PDE.Spaces.Sobolev.Variational.Galerkin.SpectralTrial

/-!
# Existence for the autonomous parabolic regularity estimate

We prove the qualitative part of the symmetric principal-part case (`b = c = 0`) of Evans's §7.1.3,
Theorem 5(i). The coefficients are autonomous, in `W¹,∞`, with globally `C¹` representatives that
are symmetric and uniformly elliptic on the domain. For `L²_t L²_x` forcing and `H¹₀` initial data,
the Galerkin construction gives `u ∈ L∞_t H¹₀` and `uₜ ∈ L²_t L²`
(`nonempty_autonomous_weak_solution_with_l2_time_derivative`). On a domain with a `C2BoundaryAtlas`,
elliptic regularity applied to the weak residual then gives an `L²_t H²` representative
(`exists_autonomous_symmetric_solution_with_spatial_h2`).

The bounds in terms of the data alone, Evans's estimate (46), are in
`PDE.Parabolic.Regularity.Autonomous.Estimate`. The spatial `H²` step,
`PDE.Parabolic.Regularity.SpatialH2.WeakResidual`, does not use Galerkin theory and applies to any
weak evolution satisfying the almost-everywhere equation.

## How it works

Evans tests the Galerkin equation (16) with `u_m'`. Symmetry and time independence of `aⁱʲ` make the
principal term `d/dt (½ A[u_m, u_m])`, which bounds `u_m'` in `L²_t L²_x` and `u_m` in `L∞_t H¹₀`,
(48). He then applies §6.3.2, Theorem 4 to `Lu = f - u'` at almost every time, (49). We follow the
same two steps. The Galerkin step is `exists_of_symmetric_principal_measurable_galerkin_L2` on the
spectral trial spaces `h10L2SpectralTrialSystem`, with `‖uₜ‖² ≤ ‖A‖ ‖u(t₀)‖² + 2 ‖f‖²`. The elliptic
step applies the bounded solution operator `globalH2SolveLpCLM` to the Bochner class `f - uₜ`
(`exists_spatial_h2_lp_of_ae_weak_residual_identity`), so the lift needs no measurable selection,
and its bound `‖globalH2SolveCLM‖ ‖f - uₜ‖` has no `‖u‖_{L²}` term.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 4 (Boundary H²-regularity), p. 334; §7.1.2,
  (16), p. 375; §7.1.3, (45), p. 381, Theorem 5 (Improved regularity), (46), p. 382, and steps 1-3
  of its proof, (48)-(49), pp. 382-384.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory

namespace PDE.Parabolic.DivergenceFormHeat

open PDE.Analysis.Evolution
open PDE.Analysis.Evolution.IsGelfandIntegratedWeakSolution
open SobolevSpace
open SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal InnerProductSpace

/--
The Galerkin theorem with measurable remainder, specialized to a constant
symmetric coercive form and zero remainder.
-/
private theorem exists_principal_galerkin_solution
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V)
    (hfinite : ∀ n, FiniteDimensional ℝ (S n))
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (A : V →L[ℝ] StrongDual ℝ V)
    {a b C : ℝ}
    (f : Lp H 2 (volume.restrict (Set.Ioc a b)))
    (hab : a < b) (hC : 0 < C)
    (hcoercive : ∀ w : V, C * ‖w‖ ^ 2 ≤ A w w)
    (uInit : V)
    (hA_symm : ∀ u v : V, A u v = A v u) :
    ∃ (u : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (du : Lp H 2 (volume.restrict (Set.Ioc a b))),
      IsGelfandIntegratedWeakSolution T (fun _ ↦ A)
          (fun t ↦ T.pivotToDual (f t)) u (T.inclusion uInit) ∧
      HasGelfandWeakTimeDerivativeOn T u
        (T.pivotToDual.compLpL 2
          (volume.restrict (Set.Ioc a b)) du) ∧
      ‖du‖ ^ 2 ≤
        ‖A‖ * (K * ‖uInit‖) ^ 2 + 2 * ‖f‖ ^ 2 ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        ‖u t‖ ≤
          Real.sqrt
            ((‖A‖ * (K * ‖uInit‖) ^ 2 + 2 * ‖f‖ ^ 2) / C)) := by
  obtain ⟨u, du, hsolution, hderivative, _, hdu, hstate⟩ :=
    exists_of_symmetric_principal_measurable_galerkin_L2
      (K := K) (a := a) (b := b) (C := C) (N := 0)
      T S hfinite P hdenseEnergy (fun _ ↦ A) (fun _ ↦ 0) f hab hC
      aestronglyMeasurable_const ‖A‖₊ (fun _ _ ↦ le_rfl) uInit
      (LipschitzWith.const A).lipschitzOnWith.absolutelyContinuousOnInterval
      (Filter.Eventually.of_forall fun t ↦ hasDerivAt_const t A)
      (Filter.Eventually.of_forall fun _ ↦
        (@norm_zero (V →L[ℝ] StrongDual ℝ V) inferInstance).le)
      (fun _ _ ↦ hA_symm) (fun _ _ ↦ hcoercive)
  simp only [NNReal.coe_zero, zero_div, add_zero, zero_mul] at hdu hstate
  exact ⟨u, du, hsolution, hderivative, hdu, hstate⟩

variable {n : ℕ} [Fact (0 < n)]
variable {Ω : Set (ℝ^n)}

/--
A weak solution of an autonomous symmetric parabolic problem together with
the improved Galerkin regularity and time-derivative estimate.

The trajectory `u` is represented in `L²_t H¹₀`, while `state_memLp_top`
certifies its stronger `L∞_t H¹₀` regularity. The pivot derivative `ut`
belongs to `L²_t L²`, and its canonical image in `L²_t H⁻¹` is the weak
time derivative. The almost-everywhere variational equation follows from these
two facts (`ae_weak_equation`) and is not a field.
-/
structure AutonomousWeakSolutionWithL2TimeDerivative
    (t₀ t₁ : ℝ)
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (f : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (uInit : H¹₀(Ω)) where
  /-- The energy-space trajectory, represented in `L²_t H¹₀(Ω)`. -/
  u : Lp
    (H¹₀(Ω)) 2
    (volume.restrict (Set.Ioc t₀ t₁))
  /-- The pivot-valued time derivative in `L²_t L²(Ω)`. -/
  ut : Lp (DerivLp n 2 Ω) 2
    (volume.restrict (Set.Ioc t₀ t₁))
  /-- The integrated weak equation, including the initial condition. -/
  weak_solution :
    IsGelfandIntegratedWeakSolution
      (_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
        hΩopen)
      (fun _ ↦
        variableCoeffForm (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω)
            (coefficientBase A)))
      (fun t ↦
        (_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
          hΩopen).pivotToDual (f t))
      u
      ((_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
        hΩopen).inclusion uInit)
  /-- The weak time derivative of `u` is the canonical Bochner lift of `ut`. -/
  weak_time_derivative :
    HasGelfandWeakTimeDerivativeOn
      (_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
        hΩopen)
      u
      ((_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
        hΩopen).pivotToDual.compLpL
          2 (volume.restrict (Set.Ioc t₀ t₁)) ut)
  /-- The improved Galerkin estimate for the pivot derivative. -/
  time_derivative_bound :
    ‖ut‖ ^ 2 ≤
      ‖variableCoeffForm (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω)
          (coefficientBase A))‖ * ‖uInit‖ ^ 2 +
        2 * ‖f‖ ^ 2
  /-- The energy-space trajectory is essentially bounded in time. -/
  state_memLp_top :
    MemLp
      (fun t ↦
        ((u : ℝ → H¹₀(Ω)) t))
      (⊤ : ℝ≥0∞) (volume.restrict (Set.Ioc t₀ t₁))

namespace AutonomousWeakSolutionWithL2TimeDerivative

omit [Fact (0 < n)] in
/--
The integrated weak solution and its identified pivot derivative satisfy the
parabolic variational equation almost everywhere.

This follows from uniqueness of weak derivatives: the integrated equation
identifies the derivative with the residual `f - A u`, while
`weak_time_derivative` identifies it with the dual lift of `uₜ`.
-/
theorem ae_weak_equation
    {t₀ t₁ : ℝ}
    {hΩopen : IsOpen Ω}
    {A : Fin n → Fin n → W^{1,∞}(Ω)}
    {f : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁))}
    {uInit : H¹₀(Ω)}
    (solution :
      AutonomousWeakSolutionWithL2TimeDerivative t₀ t₁ hΩopen A f uInit) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc t₀ t₁)),
      ∀ v : H¹₀(Ω),
        ⟪solution.ut t, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ +
          variableCoeffForm (n := n) (Ω := Ω)
            (multiplicationCoefficientOperator (n := n) (Ω := Ω)
              (coefficientBase A))
            ((solution.u : ℝ → H¹₀(Ω)) t) v =
          ⟪f t, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ := by
  let μ := volume.restrict (Set.Ioc t₀ t₁)
  let T := _root_.SobolevSpace.GraphSpace.h10L2GelfandTriple hΩopen
  have hsolution :
      IsGelfandIntegratedWeakSolution T
        (fun _ ↦
          variableCoeffForm (n := n) (Ω := Ω)
            (multiplicationCoefficientOperator (n := n) (Ω := Ω)
              (coefficientBase A)))
        (fun t ↦ (T.pivotToDual.compLpL 2 μ f) t)
        solution.u (T.inclusion uInit) := by
    exact solution.weak_solution.congr_forcing_ae
      (T.pivotToDual.coeFn_compLpL f).symm
  exact
    ae_weak_residual_identity_of_integrated_solution
      hΩopen A f solution.ut solution.u (T.inclusion uInit)
      hsolution solution.weak_time_derivative

end AutonomousWeakSolutionWithL2TimeDerivative

/--
Construct an autonomous symmetric weak solution with the improved Galerkin
time regularity and derivative bound.

Only openness and boundedness of `Ω` are used; the boundary charts enter with the
spatial `H²` lift in `exists_autonomous_symmetric_solution_with_spatial_h2`.
-/
theorem nonempty_autonomous_weak_solution_with_l2_time_derivative
    (t₀ t₁ : ℝ) (ht : t₀ < t₁)
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Ω)
          (baseIndex n 1) : DerivLp n ∞ Ω)
        =ᵐ[domainMeasure n Ω] fun x ↦ a x i j)
    (haSymm : ∀ x ∈ Ω, ∀ i j, a x i j = a x j i)
    (f : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (uInit : H¹₀(Ω))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    Nonempty (AutonomousWeakSolutionWithL2TimeDerivative t₀ t₁ hΩopen A f uInit) := by
  let μ := volume.restrict (Set.Ioc t₀ t₁)
  let V := H¹₀(Ω)
  let H := DerivLp n 2 Ω
  let T := _root_.SobolevSpace.GraphSpace.h10L2GelfandTriple hΩopen
  let coeff := coefficientBase A
  let Aop : V →L[ℝ] StrongDual ℝ V :=
    variableCoeffForm (n := n) (Ω := Ω) (multiplicationCoefficientOperator coeff)
  let trials := _root_.SobolevSpace.GraphSpace.h10L2SpectralTrialSystem hΩopen hΩbounded
  let h10InnerProductSpace : InnerProductSpace ℝ V := inferInstance
  let h10CompleteSpace : CompleteSpace V := inferInstance
  have hAElliptic : AEUniformlyElliptic (n := n) (Ω := Ω) coeff alpha :=
    coefficientBase_aeUniformlyElliptic hΩopen.measurableSet A a haRep alpha halpha hElliptic
  have hAESymm : AESymmetricCoefficient (n := n) (Ω := Ω) coeff :=
    coefficientBase_aeSymmetric hΩopen.measurableSet A a haRep haSymm
  obtain ⟨C, hC, hcoerciveOp⟩ := variableCoeffForm_isCoercive (Fact.out : 0 < n) hΩbounded
    (multiplicationCoefficientOperator coeff)
    (integratedElliptic_multiplication_of_ae coeff hAElliptic)
  have hcoercive (w : V) : C * ‖w‖ ^ 2 ≤ Aop w w := by
    simpa only [Aop, pow_two, mul_assoc] using hcoerciveOp w
  have hA_symm (u v : V) : Aop u v = Aop v u :=
    variableCoeffForm_symm (symmetricCoefficientOperator_multiplication_of_ae coeff hAESymm) u v
  obtain ⟨u, ut, hsolution, hderivative, hut, hstateBound⟩ :=
    @exists_principal_galerkin_solution
      V H inferInstance h10InnerProductSpace h10CompleteSpace
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      T trials.space trials.finiteDimensional trials.stabilityConstant
      trials.projection trials.denseEnergy Aop t₀ t₁ C f ht hC
      hcoercive uInit hA_symm
  have hK : trials.stabilityConstant = 1 := rfl
  simp only [hK, NNReal.coe_one, one_mul] at hut hstateBound
  have hstateMemLpTop : MemLp (fun t ↦ (u : ℝ → V) t) (⊤ : ℝ≥0∞) μ :=
    memLp_top_of_bound (Lp.aestronglyMeasurable u)
      (Real.sqrt ((‖Aop‖ * ‖uInit‖ ^ 2 + 2 * ‖f‖ ^ 2) / C)) hstateBound
  refine ⟨{
    u := u
    ut := ut
    weak_solution := ?_
    weak_time_derivative := ?_
    time_derivative_bound := ?_
    state_memLp_top := ?_
  }⟩
  · simpa only [T, Aop, coeff] using hsolution
  · simpa only [T, hΩopen, μ] using hderivative
  · exact hut
  · simpa only [V, μ] using hstateMemLpTop

/--
The qualitative part of Evans's §7.1.3, Theorem 5(i), for autonomous symmetric
divergence-form equations without lower-order terms.

On a domain with a `C2BoundaryAtlas`, assume autonomous `W¹,∞` principal
coefficients with globally `C¹` representatives that are symmetric and
uniformly elliptic on the domain. Every Bochner `L²_t L²_x` forcing and `H¹₀`
initial datum then admit a weak solution whose `L²_t L²_x` time derivative
comes from the improved Galerkin estimate. Identifying this derivative with
the variational residual gives the almost-everywhere weak evolution equation,
and elliptic regularity gives an `L²_t H²_x` lift with
`‖h2Lift‖ ≤ ‖S₂‖ ‖f - uₜ‖`, where `S₂` is the global `H²` solution operator.
-/
theorem exists_autonomous_symmetric_solution_with_spatial_h2
    (t₀ t₁ : ℝ) (ht : t₀ < t₁)
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Ω)
          (baseIndex n 1) : DerivLp n ∞ Ω)
        =ᵐ[domainMeasure n Ω] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (haSymm : ∀ x ∈ Ω, ∀ i j, a x i j = a x j i)
    (f : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (uInit : H¹₀(Ω))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    ∃ (solution :
        AutonomousWeakSolutionWithL2TimeDerivative
          t₀ t₁ hΩ.toC1ExtensionAtlas.isOpen A f uInit)
      (h2Lift : Lp (W^{2,2}(Ω)) 2
        (volume.restrict (Set.Ioc t₀ t₁))),
      ((fun t ↦
          lowerOrderCLM
            (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
            (by omega)
            ((h2Lift : ℝ → W^{2,2}(Ω)) t))
        =ᵐ[volume.restrict (Set.Ioc t₀ t₁)]
          fun t ↦
            h10SubtypeL (n := n) (Ω := Ω)
              ((solution.u : ℝ → H¹₀(Ω)) t)) ∧
      ‖h2Lift‖ ≤
        ‖globalH2SolveCLM hΩ A a haRep haC1
          alpha halpha hElliptic‖ * ‖f - solution.ut‖ := by
  obtain ⟨solution⟩ :=
    nonempty_autonomous_weak_solution_with_l2_time_derivative
      t₀ t₁ ht hΩ.toC1ExtensionAtlas.isOpen hΩ.toC1ExtensionAtlas.bounded A a haRep haSymm f uInit
      alpha halpha hElliptic
  obtain ⟨h2Lift, h2_order_one, h2_norm_bound⟩ :=
    exists_spatial_h2_lp_of_ae_weak_residual_identity
      t₀ t₁ hΩ A a haRep haC1 f solution.ut solution.u
      solution.ae_weak_equation
      alpha halpha hElliptic
  exact ⟨solution, h2Lift, h2_order_one, h2_norm_bound⟩

end PDE.Parabolic.DivergenceFormHeat
