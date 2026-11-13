/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.TimeSobolev
public import PDE.Parabolic.Regularity.Autonomous.Higher.Form
public import PDE.Analysis.Evolution.Integrated.Solution
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2
import PDE.Analysis.Evolution.Galerkin.PairedL2Differentiation.Ritz
import PDE.Analysis.Evolution.Integrated.Regularity
import PDE.Spaces.Sobolev.Variational.Galerkin.SpectralTrial

/-!
# Differentiated weak trajectories for autonomous parabolic equations

We construct the original and time-differentiated Galerkin trajectories for
the symmetric principal-part case of Evans's §7.1.3, Theorem 5(ii)
(`nonempty_differentiated_weak_trajectory`). Both come from one compactness
subnet, so the pivot-valued derivative of the original solution is the
energy-space differentiated trajectory.

The strong initial load gives the Ritz compatibility identity
`uₜ(t₀) = f(t₀) - strongLoad A G`. An absolutely continuous representative
of the forcing lets us differentiate the finite-dimensional autonomous
equation. Evans starts from the `L²` projections of `g` onto spans of eigenfunctions of
`-Δ`, (15), and bounds `u_m'(0)` through `‖u_m(0)‖_{H²} ≤ C ‖g‖_{H²}` (steps 4-5 of his
proof); the Ritz start replaces that bound.

The pivot-valued derivative and the dual-valued forcing are written with the
maps `inclusion.compLpL` and `pivotToDual.compLpL` rather than as separate
witnesses.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, (15)-(16), p. 375; §7.1.3, (45), p. 381, and steps
  4-5 of the proof of Theorem 5 (Improved regularity), (50)-(52), pp. 384-385.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set

namespace PDE.Parabolic.DivergenceFormHeat
namespace AutonomousRegularity

open PDE.Analysis.Evolution
open SobolevSpace
open SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal InnerProductSpace

variable {n : ℕ} [Fact (0 < n)]
variable {Ω : Set (ℝ^n)}

attribute [local instance 101] secondCountableTopologyEither_of_left

/--
The original weak trajectory and its energy-space time derivative produced
by one Galerkin compactness subnet.

The fields `u`, `ut`, and `utInit` come from the same limiting subnet, so
they are bundled. The weak derivative is stated through the inclusion and
pivot-to-dual maps, and the differentiated equation uses the pivot-to-dual
lift of `fₜ`.
-/
structure DifferentiatedWeakTrajectory
    (t₀ t₁ : ℝ)
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (f ft : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (G : W^{2,2}(Ω))
    (g : H¹₀(Ω)) where
  /-- The original weak solution in `L²(t₀,t₁; H¹₀(Ω))`. -/
  u : Lp
    (H¹₀(Ω)) 2
    (volume.restrict (Set.Ioc t₀ t₁))
  /-- The energy-space representative of the first weak time derivative of
  `u`, produced by the same Galerkin subnet. -/
  ut : Lp
    (H¹₀(Ω)) 2
    (volume.restrict (Set.Ioc t₀ t₁))
  /-- The `L²(Ω)` initial datum for the differentiated equation, represented
  by the initial forcing minus the elliptic load of `G`. -/
  utInit : DerivLp n 2 Ω
  /-- The original trajectory solves the integrated equation with forcing `f` and datum `g`. -/
  weak_solution :
    IsGelfandIntegratedWeakSolution
      (_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
        hΩ.toC1ExtensionAtlas.isOpen)
      (fun _ ↦ autonomousDivergenceFormOperator A)
      (fun t ↦
        (_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
          hΩ.toC1ExtensionAtlas.isOpen).pivotToDual (f t))
      u
      ((_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
        hΩ.toC1ExtensionAtlas.isOpen).inclusion g)
  /-- Lifting `ut` to the dual space gives the weak time derivative of `u`. -/
  weak_time_derivative :
    HasGelfandWeakTimeDerivativeOn
      (_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
        hΩ.toC1ExtensionAtlas.isOpen)
      u
      ((_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
        hΩ.toC1ExtensionAtlas.isOpen).pivotToDual.compLpL
          2 (volume.restrict (Set.Ioc t₀ t₁))
          ((_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
            hΩ.toC1ExtensionAtlas.isOpen).inclusion.compLpL
              2 (volume.restrict (Set.Ioc t₀ t₁)) ut))
  /-- The derivative trajectory solves the same spatial equation with forcing `ft`
  and initial value `utInit`. -/
  time_derivative_solution :
    IsGelfandIntegratedWeakSolution
      (_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
        hΩ.toC1ExtensionAtlas.isOpen)
      (fun _ ↦ autonomousDivergenceFormOperator A)
      (fun t ↦
        ((_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
          hΩ.toC1ExtensionAtlas.isOpen).pivotToDual.compLpL
            2 (volume.restrict (Set.Ioc t₀ t₁)) ft) t)
      ut utInit
  /-- The initial derivative is bounded by the forcing trace bound plus the initial
  elliptic load. -/
  initial_derivative_bound :
    ‖utInit‖ ≤ timeSobolevBound f ft + ‖strongLoad A G‖

namespace DifferentiatedWeakTrajectory

/--
The integrated weak solution and its identified weak time derivative satisfy
the parabolic equation almost everywhere.

The integrated equation gives the residual derivative `f - A u`, and
uniqueness of weak time derivatives identifies it with the pivot lift of
`uₜ`.
-/
theorem ae_weak_equation
    {t₀ t₁ : ℝ}
    {hΩ : SobolevSpace.C2BoundaryAtlas n Ω}
    {A : Fin n → Fin n → W^{1,∞}(Ω)}
    {f ft : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁))}
    {G : W^{2,2}(Ω)}
    {g : H¹₀(Ω)}
    (trajectory : DifferentiatedWeakTrajectory t₀ t₁ hΩ A f ft G g) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc t₀ t₁)),
      ∀ v : H¹₀(Ω),
        ((_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
              hΩ.toC1ExtensionAtlas.isOpen).pivotToDual
            (((_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
                  hΩ.toC1ExtensionAtlas.isOpen).inclusion.compLpL
                2 (volume.restrict (Set.Ioc t₀ t₁)) trajectory.ut) t)) v
            + autonomousDivergenceFormOperator A
                ((trajectory.u : ℝ → H¹₀(Ω)) t) v =
          ((_root_.SobolevSpace.GraphSpace.h10L2GelfandTriple
            hΩ.toC1ExtensionAtlas.isOpen).pivotToDual (f t)) v := by
  let μ := volume.restrict (Set.Ioc t₀ t₁)
  let V := H¹₀(Ω)
  let H := DerivLp n 2 Ω
  let hVInner : InnerProductSpace ℝ V := inferInstance
  let hVComplete : CompleteSpace V := inferInstance
  let T : GelfandTriple (V := V) (H := H) :=
    _root_.SobolevSpace.GraphSpace.h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen
  let Aop : V →L[ℝ] StrongDual ℝ V := autonomousDivergenceFormOperator A
  let ell : Lp (StrongDual ℝ V) 2 μ := T.pivotToDual.compLpL 2 μ f
  -- These aliases keep both proof-indexed presentations of `H₀¹(Ω)` in the
  -- same explicit dual type before the weak equation forms their sum.
  let utDual : Lp (StrongDual ℝ V) 2 μ :=
    T.pivotToDual.compLpL 2 μ (T.inclusion.compLpL 2 μ trajectory.ut)
  have hDualEquation : ∀ᵐ t ∂μ, utDual t + Aop ((trajectory.u : ℝ → V) t) = ell t :=
    @IsGelfandIntegratedWeakSolution.ae_weak_equation
      V H (inferInstance : NormedAddCommGroup V) hVInner hVComplete
      (inferInstance : NormedAddCommGroup H) (inferInstance : InnerProductSpace ℝ H)
      t₀ t₁ T (fun _ ↦ Aop) ell trajectory.u (T.inclusion g) utDual
      (fun v ↦ aestronglyMeasurable_const.apply_continuousLinearMap v) ‖Aop‖
      (.of_forall fun _ ↦ le_rfl)
      (trajectory.weak_solution.congr_forcing_ae (T.pivotToDual.coeFn_compLpL f).symm)
      trajectory.weak_time_derivative
  filter_upwards [hDualEquation,
    T.pivotToDual.coeFn_compLpL (T.inclusion.compLpL 2 μ trajectory.ut),
    T.pivotToDual.coeFn_compLpL f] with t hEq hut hf v
  exact (congrArg (· v + Aop ((trajectory.u : ℝ → V) t) v) hut).symm.trans
    ((congrArg (fun q : StrongDual ℝ V ↦ q v) hEq).trans (congrArg (· v) hf))

end DifferentiatedWeakTrajectory

/--
Construct a differentiated weak trajectory from a strong absolutely
continuous representative of the forcing.

The representative fixes the initial differentiated state
`f(t₀) - strongLoad A G`. Symmetry gives the uniform `L²_t L²_x` bound on the
Galerkin velocities, and ellipticity gives the coercive estimate needed to pass
to one compactness subnet. `nonempty_differentiated_weak_trajectory` obtains
the representative from Hilbert-valued time-Sobolev regularity.
-/
theorem nonempty_differentiated_weak_trajectory_of_representative
    (t₀ t₁ : ℝ) (ht : t₀ < t₁)
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Ω)
          (baseIndex n 1) : DerivLp n ∞ Ω)
        =ᵐ[domainMeasure n Ω] fun x ↦ a x i j)
    (haSymm : ∀ x ∈ Ω, ∀ i j, a x i j = a x j i)
    (f ft : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (fRep : ℝ → DerivLp n 2 Ω)
    (hfRepAC : AbsolutelyContinuousOnInterval fRep t₀ t₁)
    (hfRepEq : fRep =ᵐ[volume.restrict (Set.Ioc t₀ t₁)]
      fun t ↦ f t)
    (hfRepDeriv : ∀ᵐ t ∂volume.restrict (Set.Ioc t₀ t₁),
      HasDerivAt fRep (ft t) t)
    (hfRepBound : ∀ t ∈ Set.Icc t₀ t₁,
      ‖fRep t‖ ≤ timeSobolevBound f ft)
    (G : W^{2,2}(Ω))
    (g : H¹₀(Ω))
    (hG :
      lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
          (by omega) G =
        h10SubtypeL (n := n) (Ω := Ω) g)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    Nonempty (DifferentiatedWeakTrajectory t₀ t₁ hΩ A f ft G g) := by
  let hΩopen : IsOpen Ω := hΩ.toC1ExtensionAtlas.isOpen
  let μ := volume.restrict (Set.Ioc t₀ t₁)
  let V := H¹₀(Ω)
  let H := DerivLp n 2 Ω
  let h10InnerProductSpace : InnerProductSpace ℝ V := inferInstance
  let h10CompleteSpace : CompleteSpace V := inferInstance
  let T := _root_.SobolevSpace.GraphSpace.h10L2GelfandTriple hΩopen
  let Aop : V →L[ℝ] StrongDual ℝ V := autonomousDivergenceFormOperator A
  let trials := _root_.SobolevSpace.GraphSpace.h10L2SpectralTrialSystem
    hΩopen hΩ.toC1ExtensionAtlas.bounded
  let trialFiniteDimensional (k : ℕ) : FiniteDimensional ℝ (trials.space k) :=
    trials.finiteDimensional k
  let trialCompleteSpace (k : ℕ) : CompleteSpace (trials.space k) :=
    FiniteDimensional.complete ℝ (trials.space k)
  let ell : ℝ → StrongDual ℝ V := fun t ↦ T.pivotToDual (fRep t)
  let ellDot : ℝ → StrongDual ℝ V := fun t ↦ T.pivotToDual (ft t)
  have hellRep : ell =ᵐ[μ] fun t ↦ T.pivotToDual (f t) := by
    filter_upwards [hfRepEq] with t ht
    simp only [ell, ht]
  have hellDotMem : MemLp ellDot 2 μ :=
    @MemLp.continuousLinearMap_comp
      ℝ ℝ H (StrongDual ℝ V) inferInstance
      2 μ inferInstance inferInstance inferInstance
      inferInstance inferInstance
      (fun t ↦ ft t) (Lp.memLp ft) T.pivotToDual
  obtain ⟨C, hC, hcoercive⟩ :=
    exists_autonomous_coercivity_constant hΩ A a haRep alpha halpha hElliptic
  let utInit : H := fRep t₀ - strongLoad A G
  have hweak := (isWeakSolution_iff_isWeakDivergenceSolution hΩopen (coefficientBase A)
    (strongLoad A G) g).2 (strongLoad_isWeakDivergenceSolution hΩopen A G g hG)
  have hcompat (v : V) : ell t₀ v = inner ℝ utInit (T.inclusion v) + Aop g v := by
    have hgv : Aop g v = inner ℝ (strongLoad A G) (T.inclusion v) := hweak v
    change inner ℝ (fRep t₀) (T.inclusion v) =
      inner ℝ (fRep t₀ - strongLoad A G) (T.inclusion v) + Aop g v
    rw [hgv, inner_sub_left]
    ring
  obtain ⟨u, utH, ut, -, hsolutionRep, huWeak, hutEvolutionRep, -, hutLink, -⟩ :=
    IsGelfandIntegratedWeakSolution.exists_of_autonomous_ritz_l2_galerkin
      T trials.space trials.projection trials.denseEnergy Aop f ell ellDot ht hC
      (autonomous_divergence_form_operator_symmetric hΩ A a haRep haSymm) hcoercive hellRep
      (T.pivotToDual.lipschitzWith.comp_absolutelyContinuousOnInterval hfRepAC) hellDotMem
      (by
        filter_upwards [hfRepDeriv] with t ht
        exact T.pivotToDual.hasFDerivAt.comp_hasDerivAt t ht)
      g utInit hcompat
  subst utH
  exact ⟨{
    u := u
    ut := ut
    utInit := utInit
    weak_solution := hsolutionRep.congr_forcing_ae hellRep
    weak_time_derivative := huWeak
    time_derivative_solution :=
      hutEvolutionRep.congr_forcing_ae (T.pivotToDual.coeFn_compLpL ft).symm
    initial_derivative_bound :=
      (norm_sub_le _ _).trans (add_le_add_left (hfRepBound t₀ ⟨le_rfl, ht.le⟩) _) }⟩

/--
Construct the original weak trajectory and its differentiated equation from
the data of the principal-part case of Evans's §7.1.3, Theorem 5(ii).

The time-Sobolev theorem gives an absolutely continuous representative of
`f`, and the strong initial load gives the Ritz compatibility condition for
the Galerkin construction.
-/
theorem nonempty_differentiated_weak_trajectory
    (t₀ t₁ : ℝ) (ht : t₀ < t₁)
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Ω)
          (baseIndex n 1) : DerivLp n ∞ Ω)
        =ᵐ[domainMeasure n Ω] fun x ↦ a x i j)
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
    Nonempty (DifferentiatedWeakTrajectory t₀ t₁ hΩ A f ft G g) := by
  borelize (DerivLp n 2 Ω) (StrongDual ℝ (DerivLp n 2 Ω))
  obtain
      ⟨fRep, hfRepAC, hfRepEq, hfRepDeriv, hfRepBound, _hfBound⟩ :=
    hfIsH1.exists_absolutelyContinuousRepresentative_norm_le_of_identity ht
  exact nonempty_differentiated_weak_trajectory_of_representative
    t₀ t₁ ht hΩ A a haRep haSymm f ft
    fRep hfRepAC hfRepEq hfRepDeriv hfRepBound
    G g hG alpha halpha hElliptic

end AutonomousRegularity
end PDE.Parabolic.DivergenceFormHeat
