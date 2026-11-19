/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.LaxMilgram
public import PDE.Elliptic.Regularity.SolutionOperator.Lift
public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic
public import PDE.Hyperbolic.HigherRegularity.Data.SobolevTimeJet

/-!
# Elliptic spatial lift for higher-order wave regularity

This is the spatial part of Evans's higher-order wave induction.
We identify the weak-wave displacement with the coercive Dirichlet solution
for the residual `f - u_tt`, then apply the higher-order elliptic solution
operator to construct the missing top Sobolev trajectory.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, proof of Theorem 6, step 3, and §6.3.2, Theorem 5.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory

namespace Hyperbolic

namespace HigherRegularity

open SobolevSpace
open SobolevSpace.GraphSpace
open PDE.Analysis.Evolution
open PDE.Analysis.Variational
open scoped ENNReal

variable {n m : ℕ} {Omega : Set (ℝ^n)} {t0 t1 : ℝ}

/--
The coercive Dirichlet weak-solution operator associated with a spatial
bilinear form.

The first map sends an `L²(Omega)` right-hand side to its canonical
`H⁻¹(Omega)` load.  Lax-Milgram then solves the coercive variational
problem in `H¹₀(Omega)`.  Naming this composition makes the elliptic
operator used by the higher-order lift literally the same operator that is
identified from the weak-wave equation below.
-/
noncomputable def coerciveDirichletSolutionOperator
    (A : H¹₀(Omega) →L[ℝ] StrongDual ℝ (H¹₀(Omega)))
    (hA : @IsCoercive (H¹₀(Omega)) inferInstance inferInstance A) :
    DerivLp n 2 Omega →L[ℝ] H¹₀(Omega) :=
  (solveCLM (V := H¹₀(Omega)) A hA).comp (loadFunctionalCLM (n := n) (Ω := Omega))

/--
The almost-everywhere weak-wave equation selects the coercive elliptic
solution for the residual `f-u_tt`.

Here `f` is allowed one more spatial Sobolev derivative than `u_tt`, exactly
as in the successor step of Evans, §7.2.3.  Both are embedded into
`H⁻¹(Omega)` by their `L²` base coordinates.  The `V*` identity from
`IsGelfandWeakWaveSolution`,

`load(u_tt(t)) + A(u(t)) = load(f(t))`,

therefore says that `u(t)` is a weak solution with load
`load(f(t)-u_tt(t))`.  Lax-Milgram uniqueness identifies it with
`coerciveDirichletSolutionOperator`.  Applying the base-coordinate map
then gives the hypothesis of
`spatialHigherTop.exists_of_ae_wave`.
-/
theorem higherWeakSolutionBase_ae_eq_of_weakWave
    (hOmegaOpen : IsOpen Omega) (A : H¹₀(Omega) →L[ℝ] StrongDual ℝ (H¹₀(Omega)))
    (hA : @IsCoercive (H¹₀(Omega)) inferInstance inferInstance A)
    (f : Lp (W^{(m + 1),2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (utt : Lp (W^{m,2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (u : Lp (H¹₀(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (velocity : Lp (DerivLp n 2 Omega) 2 (volume.restrict (Set.Ioc t0 t1)))
    (q0 : H¹₀(Omega)) (p0 : DerivLp n 2 Omega)
    (hWave : Hyperbolic.Variational.IsGelfandWeakWaveSolution
      (SobolevSpace.GraphSpace.h10L2GelfandTriple hOmegaOpen) (fun _ ↦ A)
      (dirichletLoadTimeLp hOmegaOpen f) u velocity (dirichletLoadTimeLp hOmegaOpen utt) q0 p0) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc t0 t1)),
      higherWeakSolutionBaseCLM (coerciveDirichletSolutionOperator A hA)
          (lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m) (f t) - utt t) =
        wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Omega)
          (h10SubtypeL (n := n) (Ω := Omega) ((u : ℝ → H¹₀(Omega)) t)) := by
  filter_upwards [hWave.equationAE, dirichletLoadTimeLp_apply_ae hOmegaOpen f,
    dirichletLoadTimeLp_apply_ae hOmegaOpen utt] with t heq hf hutt
  rw [hutt, hf] at heq
  let r : W^{m,2}(Omega) :=
    lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m) (f t) - utt t
  have hrBase : wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega) r =
      wkpBaseCoordinateCLM (n := n) (m := m + 1) (p := 2) (Ω := Omega) (f t) -
        wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega) (utt t) := by
    simp only [r, map_sub, wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply,
      DerivIndex.castOrder_baseIndex]
  -- All variational statements here use the canonical norm on the
  -- zero-trace closed submodule.
  have hselected : coerciveDirichletSolutionOperator A hA
      (wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega) r) = (u : ℝ → H¹₀(Omega)) t :=
    @IsWeakSolution.unique (H¹₀(Omega)) inferInstance inferInstance A hA _ _ _
      (solveCLM.isWeakSolution (V := H¹₀(Omega)) A hA (loadFunctional (n := n) (Ω := Omega)
        (wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega) r))) fun v ↦ by
        have hev := DFunLike.congr_fun heq v
        simp only [hrBase, loadFunctional_sub, add_apply, sub_apply] at hev ⊢
        linarith
  exact congrArg (fun w ↦ wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Omega)
    (h10SubtypeL (n := n) (Ω := Omega) w)) hselected

/--
Evans, §7.2.3, Theorem 6: proof step 3.

Assume the time-differentiated induction has supplied

`u_tt ∈ L∞(t0,t1; H^m(Omega))`

and the forcing head belongs pointwise to `H^{m+1}(Omega)`.  Restricting the
forcing by one Sobolev order gives the elliptic right-hand side

`r(t) = f(t) - u_tt(t) ∈ H^m(Omega)`.

If the weak wave identity identifies `u(t)` with the homogeneous Dirichlet
weak solution of `L u(t) = r(t)`, the higher-order elliptic solution operator
constructs a representative in

`L∞(t0,t1; H^{m+2}(Omega))`

and proves the uniform estimate used to close Evans's induction. The qualitative hypothesis `hreg`
is the conclusion of the higher boundary regularity theorem (Evans, §6.3.2, Theorem 5) for the
chosen operator.
-/
theorem spatialHigherTop.exists_of_ae_wave (hOmegaOpen : IsOpen Omega)
    (S : DerivLp n 2 Omega →L[ℝ] H¹₀(Omega)) (hreg : HasHigherSolutionLift m S)
    (f : Lp (W^{(m + 1),2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (utt : Lp (W^{m,2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (u : Lp (H¹₀(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (hweak : ∀ᵐ t ∂(volume.restrict (Set.Ioc t0 t1)), higherWeakSolutionBaseCLM S
      (lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m) (f t) - utt t) =
      wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Omega)
      (h10SubtypeL (n := n) (Ω := Omega) ((u : ℝ → H¹₀(Omega)) t)))
    (Cf Ctt : ℝ)
    (hfBound : ∀ᵐ t ∂(volume.restrict (Set.Ioc t0 t1)),
      ‖lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m) (f t)‖ ≤ Cf)
    (huttBound : ∀ᵐ t ∂(volume.restrict (Set.Ioc t0 t1)), ‖utt t‖ ≤ Ctt) :
    ∃ U : Lp (W^{(m + 2),2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)),
      ((fun t ↦ wkpBaseCoordinateCLM (n := n) (m := m + 2) (p := 2) (Ω := Omega)
            ((U : ℝ → W^{(m + 2),2}(Omega)) t))
        =ᵐ[volume.restrict (Set.Ioc t0 t1)]
        fun t ↦ wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Omega)
          (h10SubtypeL (n := n) (Ω := Omega) ((u : ℝ → H¹₀(Omega)) t))) ∧
      MemLp (fun t ↦ (U : ℝ → W^{(m + 2),2}(Omega)) t) (⊤ : ℝ≥0∞)
        (volume.restrict (Set.Ioc t0 t1)) ∧
      ∀ᵐ t ∂(volume.restrict (Set.Ioc t0 t1)),
        ‖(U : ℝ → W^{(m + 2),2}(Omega)) t‖ ≤
          ‖higherSolutionOperator hOmegaOpen S hreg‖ * (Cf + Ctt) := by
  have hrhs : ((lowerOrderTimeLp f - utt : Lp (W^{m,2}(Omega)) 2 _) : ℝ → W^{m,2}(Omega))
      =ᵐ[(volume.restrict (Set.Ioc t0 t1))]
        fun t ↦ lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m) (f t) - utt t := by
    filter_upwards [lowerOrderTimeLp_apply_ae f,
      MeasureTheory.Lp.coeFn_sub (lowerOrderTimeLp f) utt] with t hf hsub
    rw [hsub, Pi.sub_apply, hf]
  exact SobolevSpace.GraphSpace.exists_higherSolutionTrajectory_of_weak_solution hOmegaOpen _ S
    hreg _ u (by filter_upwards [hrhs, hweak] with t hr ht; rwa [hr]) (Cf + Ctt) (by
      filter_upwards [hrhs, hfBound, huttBound] with t hr hf hutt
      rw [hr]
      exact (norm_sub_le _ _).trans (add_le_add hf hutt))

end HigherRegularity

end Hyperbolic
