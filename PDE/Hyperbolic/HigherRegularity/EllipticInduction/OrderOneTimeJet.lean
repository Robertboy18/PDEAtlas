/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Hyperbolic.HigherRegularity.EllipticInduction.WeakTimeDerivative
public import PDE.Hyperbolic.HigherRegularity.Data.SobolevTimeJet
public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic
public import PDE.Elliptic.Regularity.SolutionOperator.Lift

/-!
# Order-one Sobolev time jet for a weak wave

We construct the base Sobolev time jet used by the higher-order
wave induction.  It combines the weak-wave displacement and pivot velocity
as an `H¹` trajectory with an `H⁰` weak time derivative.

In Evans's regularity argument for second-order hyperbolic equations (Evans,
PDE, §7.2.3) the starting point is the weak solution itself: `u ∈ L∞_t H¹₀`
with `u_t ∈ L∞_t L²`.  Here these two `L∞` bounds are hypotheses, inherited
from the Galerkin energy estimates, and the weak wave
already contains the derivative relation between them.  The order-one jet
therefore needs no independently postulated weak time derivative.

## Main results

* `exists_orderOneSobolevTimeJet_of_weakWave`: a weak wave on the Dirichlet
  Gelfand triple with essentially bounded displacement and velocity yields an
  essentially bounded `SobolevTimeJet n 1` whose head is the displacement,
  viewed in `H¹`, and whose derivative is the velocity, viewed in `H⁰`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 5(i), and step 1 of the proof of Theorem 6.
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
open scoped ENNReal

variable {n : ℕ} {Omega : Set (ℝ^n)} {t0 t1 : ℝ}

/--
Construct the order-one Sobolev time jet carried by a weak wave.

The displacement is embedded canonically from `H¹₀(Omega)` into
`H¹(Omega)`, while the pivot-space velocity is placed as the unique
coordinate of `H⁰(Omega)`.  The weak-wave displacement identity proves that
these two trajectories are successive weak time derivatives.  Thus
the base case for higher regularity needs no independently postulated
derivative relation.
-/
theorem exists_orderOneSobolevTimeJet_of_weakWave (hOmegaOpen : IsOpen Omega)
    (B : ℝ → H¹₀(Omega) →L[ℝ] StrongDual ℝ (H¹₀(Omega)))
    (ell : Lp (StrongDual ℝ (H¹₀(Omega))) 2 (volume.restrict (Set.Ioc t0 t1)))
    (u : Lp (H¹₀(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (velocity : Lp (DerivLp n 2 Omega) 2 (volume.restrict (Set.Ioc t0 t1)))
    (acceleration : Lp (StrongDual ℝ (H¹₀(Omega))) 2 (volume.restrict (Set.Ioc t0 t1)))
    (q0 : H¹₀(Omega)) (p0 : DerivLp n 2 Omega)
    (hWave : Hyperbolic.Variational.IsGelfandWeakWaveSolution
      (SobolevSpace.GraphSpace.h10L2GelfandTriple hOmegaOpen) B ell u velocity acceleration q0 p0)
    (huTop : MemLp (fun t ↦ (u : ℝ → H¹₀(Omega)) t) (⊤ : ℝ≥0∞) (volume.restrict (Set.Ioc t0 t1)))
    (hvelocityTop : MemLp (fun t ↦ (velocity : ℝ → DerivLp n 2 Omega) t) (⊤ : ℝ≥0∞)
      (volume.restrict (Set.Ioc t0 t1))) :
    ∃ solution : SobolevTimeJet n 1 Omega t0 t1,
      ((fun t ↦ wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Omega)
          ((solution.head : ℝ → W^{1,2}(Omega)) t))
        =ᵐ[(volume.restrict (Set.Ioc t0 t1))]
      fun t ↦ wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Omega)
        (h10SubtypeL (n := n) (Ω := Omega) ((u : ℝ → H¹₀(Omega)) t))) ∧
      baseCoordinateTimeLp solution.timeDerivative.head = velocity ∧
      solution.IsEssentiallyBounded := by
  let μ := volume.restrict (Set.Ioc t0 t1)
  let J : H¹₀(Omega) →L[ℝ] W^{1,2}(Omega) := h10SubtypeL (n := n) (Ω := Omega)
  let Z := orderZeroSobolevCLM (n := n) (p := 2) (Omega := Omega)
  let U : Lp (W^{1,2}(Omega)) 2 μ := J.compLpL 2 μ u
  let dU : Lp (W^{0,2}(Omega)) 2 μ := Z.compLpL 2 μ velocity
  have hUcoe := J.coeFn_compLpL (p := 2) (μ := μ) u
  have hdUcoe := Z.coeFn_compLpL (p := 2) (μ := μ) velocity
  have hdUbase : baseCoordinateTimeLp dU = velocity := by
    refine Lp.ext ?_
    filter_upwards [baseCoordinateTimeLp_apply_ae dU, hdUcoe] with t hbase hdU
    rw [hbase, hdU, orderZeroSobolevCLM_base]
  have hUbase : (fun t ↦ wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Omega)
      ((U : ℝ → W^{1,2}(Omega)) t)) =ᵐ[μ] fun t ↦ wkpBaseCoordinateCLM (n := n) (m := 1)
        (p := 2) (Ω := Omega) (h10SubtypeL (n := n) (Ω := Omega) ((u : ℝ → H¹₀(Omega)) t)) := by
    filter_upwards [hUcoe] with t ht
    rw [ht]
  have hderiv := higherWeakTimeDerivative_of_weakWave (m := 0) hOmegaOpen B ell U dU u acceleration
    q0 p0 (hdUbase ▸ hWave) hUbase
  exact ⟨SobolevTimeJet.succ U (SobolevTimeJet.zero dU) hderiv, hUbase, hdUbase,
    SobolevTimeJet.succ_isEssentiallyBounded U (SobolevTimeJet.zero dU) hderiv
      ((memLp_congr_ae hUcoe).2 (huTop.continuousLinearMap_comp J))
      ((memLp_congr_ae hdUcoe).2 (hvelocityTop.continuousLinearMap_comp Z))⟩

end HigherRegularity

end Hyperbolic
