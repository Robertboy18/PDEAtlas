/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Higher.Assembly

/-!
# Higher autonomous parabolic regularity

For the symmetric principal-part case (`b = c = 0`) of Evans's §7.1.3, Theorem 5(ii), the domain
carries a `C2BoundaryAtlas`, and the coefficients are autonomous, in `W¹,∞`, with globally `C¹`
representatives that are symmetric and uniformly elliptic on the domain. Initial data belong to
`H²(Ω) ∩ H¹₀(Ω)`, and the forcing belongs to `H¹(t₀, t₁; L²(Ω))`.

The weak solution has a second weak time derivative in `L²(t₀, t₁; H⁻¹(Ω))`, a first time derivative
in `L∞(t₀, t₁; L²(Ω)) ∩ L²(t₀, t₁; H¹₀(Ω))` with a continuous `L²(Ω)` representative, and an
essentially bounded spatial `H²` lift (`exists_weak_solution_with_higher_regularity`). Bounds in
terms of the data, as in Evans's (47), are in
`exists_weak_solution_with_higher_regularity_estimates`. The pivot-valued derivative is the
inclusion of the energy-space derivative `ut`, not a separate witness.

## How it works

Evans differentiates the Galerkin equations in time, which needs coefficients independent of `t`,
(45), and bounds `u_m'` by Gronwall's inequality, (50)-(51). The equation at `t = 0` controls
`u_m'(0)` by `‖u_m(0)‖_{H²}`, which he bounds by `‖g‖_{H²}` because the `w_k` are eigenfunctions of
`-Δ` (step 5), and the spatial bound comes from the inequality (54) applied to the Galerkin
approximations (step 6). We start the Galerkin approximations from the Ritz projections of `g` for
the elliptic form, so the equation at `t₀` makes each initial velocity the projection of
`f(t₀) - strongLoad A G` and no `H²` bound on the initial approximations is needed
(`nonempty_differentiated_weak_trajectory`). The approximations and their velocities converge along
one compactness subnet, so the limit of the velocities is the weak time derivative of the limit
(`DifferentiatedWeakTrajectory`). The bounds on `uₜ` and `uₜₜ` come from the coercive energy
estimate for the limiting differentiated equation, and the `L∞_t H²_x` bound from the global `H²`
solution operator applied to `f - uₜ` at almost every time, as in step 3 of Evans's proof of part
(i) (`exists_second_time_derivative_and_spatial_h2_lift`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, (15)-(16), p. 375; §7.1.3, (45), p. 381, Theorem 5
  (Improved regularity), (46)-(47), p. 382, and steps 3-7 of its proof, (49)-(54), pp. 384-386.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set

namespace PDE.Parabolic.DivergenceFormHeat

open PDE.Analysis.Evolution
open AutonomousRegularity
open SobolevSpace
open SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal InnerProductSpace

variable {n : ℕ} [Fact (0 < n)]
variable {Ω : Set (ℝ^n)}

attribute [local instance 101] secondCountableTopologyEither_of_left

/--
The principal-part case of Evans's §7.1.3, Theorem 5(ii).

On a domain with a `C2BoundaryAtlas`, assume autonomous
`W¹,∞` principal coefficients with globally `C¹` representatives that are
symmetric and uniformly elliptic on the domain. For initial data in
`H²(Ω) ∩ H¹₀(Ω)` and forcing in `H¹(t₀, t₁; L²(Ω))`, there is a weak solution
such that

* `u ∈ L∞(t₀, t₁; H²(Ω))`;
* `uₜ ∈ L∞(t₀, t₁; L²(Ω)) ∩ L²(t₀, t₁; H¹₀(Ω))`;
* `uₜₜ ∈ L²(t₀, t₁; H⁻¹(Ω))`.

The initial witnesses `G : H²(Ω)` and `g : H¹₀(Ω)` agree in `H¹` by `hG`;
`hfIsH1` identifies `ft` as the weak time derivative of the forcing.
The initial condition is part of the integrated weak equation. Restricting
`h2Lift` to `H¹` agrees almost everywhere with the energy-space solution `u`.
The first time derivative has the continuous `L²(Ω)` representative `utRep`
on the closed time interval.
-/
theorem exists_weak_solution_with_higher_regularity
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
    (f ft : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (hfIsH1 :
      HasGelfandWeakTimeDerivativeOn
        (GelfandTriple.identity (DerivLp n 2 Ω)) f
        ((GelfandTriple.identity (DerivLp n 2 Ω)).energyToDual.compLpL
          2 (volume.restrict (Set.Ioc t₀ t₁)) ft))
    (G : W^{2,2}(Ω))
    (g : H¹₀(Ω))
    (hG :
      lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
          (by omega) G =
        h10SubtypeL (n := n) (Ω := Ω) g)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    let μ := volume.restrict (Set.Ioc t₀ t₁)
    let V := H¹₀(Ω)
    let H := DerivLp n 2 Ω
    let T := _root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
      hΩ.toC1ExtensionAtlas.isOpen
    ∃ (u ut : Lp V 2 μ)
        (h2Lift : Lp (W^{2,2}(Ω)) 2 μ)
        (utt : Lp (StrongDual ℝ V) 2 μ)
        (utRep : ℝ → H),
      let utH : Lp H 2 μ := T.inclusion.compLpL 2 μ ut
      IsGelfandIntegratedWeakSolution
          T (fun _ ↦ autonomousDivergenceFormOperator A)
          (fun t ↦ T.pivotToDual (f t)) u (T.inclusion g) ∧
        HasGelfandWeakTimeDerivativeOn
          T u (T.pivotToDual.compLpL 2 μ utH) ∧
        HasGelfandWeakTimeDerivativeOn T ut utt ∧
        ContinuousOn utRep (Set.Icc t₀ t₁) ∧
        (utRep =ᵐ[μ] fun t ↦ utH t) ∧
        MemLp (fun t ↦ utH t) (⊤ : ℝ≥0∞) μ ∧
        ((fun t ↦
            lowerOrderCLM
              (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
              (by omega)
              ((h2Lift : ℝ → W^{2,2}(Ω)) t))
          =ᵐ[μ] fun t ↦
            h10SubtypeL (n := n) (Ω := Ω)
              ((u : ℝ → V) t)) ∧
    MemLp (fun t ↦ h2Lift t) (⊤ : ℝ≥0∞) μ := by
  intro μ V H T
  have hRegularity := exists_differentiated_weak_trajectory_with_higher_regularity t₀ t₁ ht hΩ A
    a haRep haC1 haSymm f ft hfIsH1 G g hG alpha halpha hElliptic
  rcases hRegularity with ⟨trajectory, _, utt, utRep, h2Lift, hProperties⟩
  dsimp only at hProperties
  obtain ⟨-, huttWeak, hutRepContinuous, hutRepEq, -, -, hutHMemLp, -, -, h2LiftOrderOne,
    h2LiftMemLp, -⟩ := hProperties
  refine ⟨trajectory.u, trajectory.ut, h2Lift, utt, utRep, ?_⟩
  dsimp only
  exact ⟨trajectory.weak_solution, trajectory.weak_time_derivative, huttWeak, hutRepContinuous,
    hutRepEq, hutHMemLp, h2LiftOrderOne, h2LiftMemLp⟩

/--
The principal-part case of Evans's §7.1.3, Theorem 5(ii), estimate (47).

This is the quantitative form of
`exists_weak_solution_with_higher_regularity`, under the same hypotheses.
The positive constant `C` comes from the coercivity estimate.
With the domain, coefficients and time interval fixed,
`differentiatedEnergyDataBound hΩ A f ft G C` is computed from `f`, `ft`, `G`
and `C`, using the forcing trace bound, the initial load `strongLoad A G`,
and the pivot-to-dual operator norm.

This bound controls the continuous and essential `L∞(L²)` representatives
of `uₜ` and its `L²(H¹₀)` energy. The `L²(H⁻¹)` estimate for `uₜₜ` also uses
the forcing derivative and the pivot-to-dual and spatial form operator norms.
The essential `L∞(H²)` estimate for `u` uses the elliptic solution-operator
norm and the forcing trace bound. Restricting the spatial lift to `H¹`
agrees almost everywhere with the energy-space solution.
-/
theorem exists_weak_solution_with_higher_regularity_estimates
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
    (f ft : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (hfIsH1 :
      HasGelfandWeakTimeDerivativeOn
        (GelfandTriple.identity (DerivLp n 2 Ω)) f
        ((GelfandTriple.identity (DerivLp n 2 Ω)).energyToDual.compLpL
          2 (volume.restrict (Set.Ioc t₀ t₁)) ft))
    (G : W^{2,2}(Ω))
    (g : H¹₀(Ω))
    (hG :
      lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
          (by omega) G =
        h10SubtypeL (n := n) (Ω := Ω) g)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    let μ := volume.restrict (Set.Ioc t₀ t₁)
    let V := H¹₀(Ω)
    let H := DerivLp n 2 Ω
    let T := _root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
      hΩ.toC1ExtensionAtlas.isOpen
    ∃ (u ut : Lp V 2 μ)
        (h2Lift : Lp (W^{2,2}(Ω)) 2 μ)
        (utt : Lp (StrongDual ℝ V) 2 μ)
        (utRep : ℝ → H)
        (C : ℝ),
      let utH : Lp H 2 μ := T.inclusion.compLpL 2 μ ut
      let dataBound :=
        differentiatedEnergyDataBound hΩ A f ft G C
      0 < C ∧
        IsGelfandIntegratedWeakSolution
          T (fun _ ↦ autonomousDivergenceFormOperator A)
          (fun t ↦ T.pivotToDual (f t)) u (T.inclusion g) ∧
        HasGelfandWeakTimeDerivativeOn
          T u (T.pivotToDual.compLpL 2 μ utH) ∧
        HasGelfandWeakTimeDerivativeOn T ut utt ∧
        ContinuousOn utRep (Set.Icc t₀ t₁) ∧
        (utRep =ᵐ[μ] fun t ↦ utH t) ∧
        (∀ t ∈ Set.Icc t₀ t₁,
          ‖utRep t‖ ≤ Real.sqrt dataBound) ∧
        (∀ᵐ t ∂μ, ‖utH t‖ ≤ Real.sqrt dataBound) ∧
        MemLp (fun t ↦ utH t) (⊤ : ℝ≥0∞) μ ∧
        (∫ t, ‖(ut : ℝ → V) t‖ ^ 2 ∂μ) ≤ dataBound / C ∧
        ‖utt‖ ≤
          ‖T.pivotToDual‖ * ‖ft‖ +
            ‖autonomousDivergenceFormOperator A‖ *
              Real.sqrt (dataBound / C) ∧
        ((fun t ↦
            lowerOrderCLM
              (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
              (by omega)
              ((h2Lift : ℝ → W^{2,2}(Ω)) t))
          =ᵐ[μ] fun t ↦
            h10SubtypeL (n := n) (Ω := Ω)
              ((u : ℝ → V) t)) ∧
        MemLp (fun t ↦ h2Lift t) (⊤ : ℝ≥0∞) μ ∧
        ∀ᵐ t ∂μ,
          ‖h2Lift t‖ ≤
            ‖globalH2SolveCLM hΩ A a haRep haC1
              alpha halpha hElliptic‖ *
            (timeSobolevBound f ft + Real.sqrt dataBound) := by
  intro μ V H T
  have hRegularity := exists_differentiated_weak_trajectory_with_higher_regularity t₀ t₁ ht hΩ A
    a haRep haC1 haSymm f ft hfIsH1 G g hG alpha halpha hElliptic
  rcases hRegularity with ⟨trajectory, C, utt, utRep, h2Lift, hProperties⟩
  dsimp only at hProperties
  obtain ⟨hC, huttWeak, hutRepContinuous, hutRepEq, hutRepBound, hutHBound, hutHMemLp,
    hutEnergyBound, huttBound, h2LiftOrderOne, h2LiftMemLp, h2LiftBound⟩ := hProperties
  refine ⟨trajectory.u, trajectory.ut, h2Lift, utt, utRep, C, ?_⟩
  dsimp only
  exact ⟨hC, trajectory.weak_solution, trajectory.weak_time_derivative, huttWeak,
    hutRepContinuous, hutRepEq, hutRepBound, hutHBound, hutHMemLp, hutEnergyBound, huttBound,
    h2LiftOrderOne, h2LiftMemLp, h2LiftBound⟩

end PDE.Parabolic.DivergenceFormHeat
