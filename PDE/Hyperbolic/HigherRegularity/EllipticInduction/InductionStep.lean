/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.EllipticInduction.SpatialLift
import PDE.Hyperbolic.HigherRegularity.EllipticInduction.WeakTimeDerivative
import PDE.Hyperbolic.HigherRegularity.Data.InitialTrace

/-!
# Successor step for higher-order wave regularity

One step of Evans's higher-regularity induction. We use
the weak-wave equation to construct the missing top spatial trajectory and
then prove that its weak time derivative is the head of the differentiated
solution jet.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, proof of Theorem 6, steps 2 and 3.
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
Evans, §7.2.3, Theorem 6: quantitative spatial induction step.

Suppose the order-`m` induction hypothesis has been applied to the
time-differentiated equation.  The resulting jet `du` represents

`u_t, u_tt, ..., ∂ₜ^{m+2}u`

in `H^{m+1}, H^m, ..., L²`, and `hdu` gives the required `L∞` bound at
every level.  The original forcing jet `forcing` stores one weak time
derivative in addition to its `H^{m+1}` head.  Hence:

* `forcing.exists_lowerOrder_head_bound` gives
  `f ∈ L∞_t H^m_x`;
* `hdu.timeDerivative.exists_head_bound` gives
  `u_tt ∈ L∞_t H^m_x`;
* `higherWeakSolutionBase_ae_eq_of_weakWave` rewrites the original weak
  wave equation as the elliptic problem `A u = f-u_tt`;
* `spatialHigherTop.exists_of_ae_wave` applies the bounded
  `H^m → H^{m+2}` solution operator;
* `higherWeakTimeDerivative_of_weakWave` proves that the lifted trajectory
  has weak time derivative `du.head` in `H^{m+1}`.

Thus the theorem constructs the missing top spatial trajectory
`U ∈ L∞_t H^{m+2}_x`, proves that its base function is the original weak
wave displacement, identifies `U_t` with `du.head`, and assembles the result
into the successor Sobolev jet.  The constants `Cf` and `Ctt` are conclusions
extracted from the two input jets, not additional hypotheses.
-/
theorem exists_spatialHigherTop_of_weakWave_induction (ht : t0 < t1) (hOmegaOpen : IsOpen Omega)
    (A : H¹₀(Omega) →L[ℝ] StrongDual ℝ (H¹₀(Omega)))
    (hA : @IsCoercive (H¹₀(Omega)) inferInstance inferInstance A)
    (hreg : HasHigherSolutionLift m (coerciveDirichletSolutionOperator A hA))
    (forcing : SobolevTimeJet n (m + 1) Omega t0 t1) (du : SobolevTimeJet n (m + 1) Omega t0 t1)
    (hdu : du.IsEssentiallyBounded) (u : Lp (H¹₀(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (q0 : H¹₀(Omega)) (p0 : DerivLp n 2 Omega)
    (hWave : Hyperbolic.Variational.IsGelfandWeakWaveSolution
      (SobolevSpace.GraphSpace.h10L2GelfandTriple hOmegaOpen) (fun _ ↦ A)
      (dirichletLoadTimeLp hOmegaOpen forcing.head) u (baseCoordinateTimeLp du.head)
      (dirichletLoadTimeLp hOmegaOpen du.timeDerivative.head) q0 p0) :
    ∃ (Cf Ctt : ℝ) (solution : SobolevTimeJet n (m + 2) Omega t0 t1), solution.timeDerivative = du ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc t0 t1)),
        ‖lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m) (forcing.head t)‖ ≤ Cf) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc t0 t1)), ‖du.timeDerivative.head t‖ ≤ Ctt) ∧
      ((fun t ↦
          wkpBaseCoordinateCLM (n := n) (m := m + 2) (p := 2) (Ω := Omega)
            ((solution.head : ℝ → W^{(m + 2),2}(Omega)) t))
        =ᵐ[(volume.restrict (Set.Ioc t0 t1))]
        fun t ↦
          wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Omega)
            (h10SubtypeL (n := n) (Ω := Omega) ((u : ℝ → H¹₀(Omega)) t))) ∧
      solution.IsEssentiallyBounded ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc t0 t1)),
        ‖solution.head t‖ ≤
          ‖higherSolutionOperator hOmegaOpen
            (coerciveDirichletSolutionOperator A hA) hreg‖ * (Cf + Ctt)) := by
  obtain ⟨Cf, hfBound⟩ := forcing.exists_lowerOrder_head_bound ht
  obtain ⟨Ctt, huttBound⟩ := hdu.timeDerivative.exists_head_bound
  obtain ⟨U, hUbase, hUtop, hUnorm⟩ := spatialHigherTop.exists_of_ae_wave hOmegaOpen
    (coerciveDirichletSolutionOperator A hA) hreg forcing.head du.timeDerivative.head u
    (higherWeakSolutionBase_ae_eq_of_weakWave hOmegaOpen A hA forcing.head
      du.timeDerivative.head u (baseCoordinateTimeLp du.head) q0 p0 hWave) Cf Ctt hfBound huttBound
  have hUderiv := higherWeakTimeDerivative_of_weakWave (m := m + 1) hOmegaOpen (fun _ ↦ A)
    (dirichletLoadTimeLp hOmegaOpen forcing.head) U du.head u
    (dirichletLoadTimeLp hOmegaOpen du.timeDerivative.head) q0 p0 hWave hUbase
  exact ⟨Cf, Ctt, .succ U du hUderiv, rfl, hfBound, huttBound, hUbase,
    SobolevTimeJet.succ_isEssentiallyBounded U du hUderiv hUtop hdu, hUnorm⟩

end HigherRegularity

end Hyperbolic
