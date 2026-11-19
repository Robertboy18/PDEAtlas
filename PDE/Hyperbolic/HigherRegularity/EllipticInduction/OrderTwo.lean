/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.EllipticInduction.SpatialLift
import PDE.Hyperbolic.HigherRegularity.EllipticInduction.InductionStep
import PDE.Hyperbolic.HigherRegularity.EllipticInduction.OrderOneTimeJet

/-!
# Order-two assembly from paired weak waves

We assemble an order-two Sobolev time jet from an autonomous weak
wave and its first time-differentiated weak wave.  It is the base case
of the general elliptic induction, and it is the
order-two case of Evans's regularity theorems for second-order hyperbolic
equations (Evans, §7.2.3): from `u_t ∈ L∞_t H¹₀`, `u_tt ∈ L∞_t L²` and
the elliptic problem `Au = f - u_tt`, conclude `u ∈ L∞_t H²`. The bound on `u` itself is recovered
from the jet.

## Main results

* `exists_orderTwoSobolevTimeJet_of_pairedWeakWaves`: given the original weak
  wave, the differentiated weak wave with `L∞` bounds on its displacement and
  velocity, and the identifications `du = u_t` and `dvelocity = u_tt`, produce
  an essentially bounded `SobolevTimeJet n 2` with head `u`, together with the
  explicit bound `‖u(t)‖_{H²} ≤ ‖S‖ (C_f + C_tt)` almost everywhere, where `S`
  is the `H⁰ → H²` solution operator and `C_f`, `C_tt` are essential bounds on
  `f` and `u_tt` in `L²`.

## Implementation notes

The differentiated wave is first made into an order-one jet by
`exists_orderOneSobolevTimeJet_of_weakWave`; its coordinate identities
rewrite the original weak wave in the form required by
`exists_spatialHigherTop_of_weakWave_induction` at `m = 0`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 5(ii) and step 3 of its proof,
  equations (56)-(61), and Theorem 6.
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

variable {n : ℕ} {Omega : Set (ℝ^n)} {t0 t1 : ℝ}

/--
Evans, §7.2.3, Theorem 6: order-two time-induction base.

Suppose the original autonomous weak wave and its time-differentiated weak
wave have already been obtained on the Dirichlet Gelfand triple.  Assume the
differentiated displacement and velocity satisfy the `L∞` bounds supplied by
paired Galerkin compactness, and identify them almost everywhere with the
original velocity and acceleration.

The differentiated weak wave first produces an order-one Sobolev time jet.
Its coordinate identities rewrite the original weak wave in the form
used by `exists_spatialHigherTop_of_weakWave_induction` at `m = 0`.
The resulting order-two jet therefore represents

`u ∈ L∞_t H²_x`, `u_t ∈ L∞_t H¹_x`, and `u_tt ∈ L∞_t L²_x`,

with all adjacent entries proved to be weak time derivatives.
-/
theorem exists_orderTwoSobolevTimeJet_of_pairedWeakWaves (ht : t0 < t1) (hOmegaOpen : IsOpen Omega)
    (A : H¹₀(Omega) →L[ℝ] StrongDual ℝ (H¹₀(Omega)))
    (hA : @IsCoercive (H¹₀(Omega)) inferInstance inferInstance A)
    (hreg : HasHigherSolutionLift (n := n) (Omega := Omega) 0
      (coerciveDirichletSolutionOperator (n := n) (Omega := Omega) A hA))
    (forcing : SobolevTimeJet n 1 Omega t0 t1)
    (u du : Lp (H¹₀(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (velocity dvelocity : Lp (DerivLp n 2 Omega) 2 (volume.restrict (Set.Ioc t0 t1)))
    (acceleration dacceleration :
      Lp (StrongDual ℝ (H¹₀(Omega))) 2 (volume.restrict (Set.Ioc t0 t1)))
    (q0 dq0 : H¹₀(Omega)) (p0 dp0 : DerivLp n 2 Omega)
    (hOriginal : Hyperbolic.Variational.IsGelfandWeakWaveSolution
      (SobolevSpace.GraphSpace.h10L2GelfandTriple hOmegaOpen) (fun _ ↦ A)
      (dirichletLoadTimeLp hOmegaOpen forcing.head) u velocity acceleration q0 p0)
    (hDifferentiated : Hyperbolic.Variational.IsGelfandWeakWaveSolution
      (SobolevSpace.GraphSpace.h10L2GelfandTriple hOmegaOpen) (fun _ ↦ A)
      (dirichletLoadTimeLp hOmegaOpen forcing.timeDerivative.head) du dvelocity dacceleration dq0
      dp0)
    (hvelocityLink : (fun t ↦ (SobolevSpace.GraphSpace.h10L2GelfandTriple hOmegaOpen).inclusion
      ((du : ℝ → H¹₀(Omega)) t)) =ᵐ[(volume.restrict (Set.Ioc t0 t1))] fun t ↦
      (velocity : ℝ → DerivLp n 2 Omega) t)
    (haccelerationLink : (fun t ↦ (SobolevSpace.GraphSpace.h10L2GelfandTriple
      hOmegaOpen).pivotToDual ((dvelocity : ℝ → DerivLp n 2 Omega) t))
      =ᵐ[(volume.restrict (Set.Ioc t0 t1))] fun t ↦
      (acceleration : ℝ → StrongDual ℝ (H¹₀(Omega))) t)
    (hduTop : MemLp (fun t ↦ (du : ℝ → H¹₀(Omega)) t) (⊤ : ℝ≥0∞) (volume.restrict (Set.Ioc t0 t1)))
    (hdvelocityTop : MemLp (fun t ↦ (dvelocity : ℝ → DerivLp n 2 Omega) t) (⊤ : ℝ≥0∞)
      (volume.restrict (Set.Ioc t0 t1))) :
    ∃ (Cf Ctt : ℝ) (solution : SobolevTimeJet n 2 Omega t0 t1),
      baseCoordinateTimeLp (n := n) (m := 1) (Omega := Omega)
          (t0 := t0) (t1 := t1) solution.timeDerivative.head = velocity ∧
      baseCoordinateTimeLp (n := n) (m := 0) (Omega := Omega) (t0 := t0) (t1 := t1)
          solution.timeDerivative.timeDerivative.head = dvelocity ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc t0 t1)),
        ‖lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ 0) (forcing.head t)‖ ≤ Cf) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc t0 t1)),
        ‖solution.timeDerivative.timeDerivative.head t‖ ≤ Ctt) ∧
      ((fun t ↦ wkpBaseCoordinateCLM (n := n) (m := 2) (p := 2) (Ω := Omega)
            ((solution.head : ℝ → W^{2,2}(Omega)) t))
        =ᵐ[(volume.restrict (Set.Ioc t0 t1))]
        fun t ↦ wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Omega)
          (h10SubtypeL (n := n) (Ω := Omega) ((u : ℝ → H¹₀(Omega)) t))) ∧
      solution.IsEssentiallyBounded ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc t0 t1)),
        ‖solution.head t‖ ≤
          ‖higherSolutionOperator (n := n) (m := 0) (Omega := Omega) hOmegaOpen
            (coerciveDirichletSolutionOperator (n := n) (Omega := Omega) A hA) hreg‖ *
              (Cf + Ctt)) := by
  obtain ⟨duJet, hduBase, hdvelocityBase, hduJetTop⟩ :=
    exists_orderOneSobolevTimeJet_of_weakWave hOmegaOpen (fun _ ↦ A)
      (dirichletLoadTimeLp hOmegaOpen forcing.timeDerivative.head) du dvelocity dacceleration
      dq0 dp0 hDifferentiated hduTop hdvelocityTop
  have hvelocityEq : baseCoordinateTimeLp duJet.head = velocity := by
    refine Lp.ext ?_
    filter_upwards [baseCoordinateTimeLp_apply_ae duJet.head, hduBase, hvelocityLink] with
      t hbase hdu hvelocity
    rw [hbase, hdu]
    exact hvelocity
  have haccelerationEq :
      dirichletLoadTimeLp hOmegaOpen duJet.timeDerivative.head = acceleration := by
    refine Lp.ext ?_
    filter_upwards [dirichletLoadTimeLp_apply_ae hOmegaOpen duJet.timeDerivative.head,
      baseCoordinateTimeLp_apply_ae duJet.timeDerivative.head, haccelerationLink] with
      t hload hbase hacceleration
    rw [hload]
    change (SobolevSpace.GraphSpace.h10L2GelfandTriple hOmegaOpen).pivotToDual
        (wkpBaseCoordinateCLM (n := n) (m := 0) (p := 2) (Ω := Omega)
          (duJet.timeDerivative.head t)) = acceleration t
    rw [← hbase, hdvelocityBase]
    exact hacceleration
  rw [← hvelocityEq, ← haccelerationEq] at hOriginal
  obtain ⟨Cf, Ctt, solution, hsolutionDerivative, hf, hutt, hsolutionBase, hsolutionRegularity,
    hsolutionBound⟩ := exists_spatialHigherTop_of_weakWave_induction (m := 0) ht hOmegaOpen A
      hA hreg forcing duJet hduJetTop u q0 p0 hOriginal
  subst hsolutionDerivative
  exact ⟨Cf, Ctt, solution, hvelocityEq, hdvelocityBase, hf, hutt, hsolutionBase,
    hsolutionRegularity, hsolutionBound⟩

end HigherRegularity

end Hyperbolic
