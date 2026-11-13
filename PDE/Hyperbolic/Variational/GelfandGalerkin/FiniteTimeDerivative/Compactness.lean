/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.Galerkin.BochnerRealization
public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic
import PDE.Hyperbolic.HigherRegularity.Galerkin.WeakLimit
import PDE.Hyperbolic.WeakWave.Galerkin.IntegratedIdentities

/-!
# Compactness for finite differentiated Galerkin families

The weak-limit step of the higher-regularity argument for the abstract wave equation on a
Gelfand triple `V ↪ H ↪ V'`. Given, for each trial space `Sseq n`, a chain
`U n 0, …, U n m` of Galerkin trajectories in which `U n r.castSucc` is the time derivative
of `U n r.succ` (so `U n m` is the approximate solution and `U n 0` its `m`-th time derivative),
and given bounds on all displacements, velocities and accelerations in `L²` that are uniform in
`n`, we extract an ambient chain `u 0, …, u m` of Gelfand weak wave solutions with
`u r.castSucc` again the derivative of `u r.succ`, together with essential bounds on the top
level. This is the time-differentiated Galerkin scheme used for improved regularity of weak
solutions of second-order hyperbolic equations in Evans, §7.2.3, in a basis-free form.

## Main results

* `exists_finiteWeakWaveChain_of_bounded_finiteTimeDerivativeFamily`: from a bounded sequence
  of finite differentiated Galerkin families, produce weak-wave solutions at every level,
  the adjacent identities `J u_{r} = u'_{r+1}` and `J* u'_r = u''_{r+1}` in `L²`, membership
  of the top displacement and velocity in `L^∞`, and the stated essential bounds `Cu`, `Cv`.

## Implementation notes

The finite-dimensional weak identities (the two integrated time identities and the projected
residual equation) are not hypotheses: they come from the canonical Bochner realizations
`displacementLp`, `velocityLp`, `accelerationLp` of a `SecondOrderSolutionOn`. The hypotheses
are only the pointwise chain relations `hdisplacementLink`, `hvelocityLink` and the uniform bounds;
the theorem converts the pointwise relations into the almost-everywhere `Lp` identities the
common-filter compactness theorem
`HigherRegularity.exists_finiteWeakWaveChain_of_bounded_projected_galerkin_family` expects.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, proofs of Theorems 5 and 6.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Hyperbolic.Variational.GelfandGalerkin

open PDE.Analysis.Evolution
open scoped ENNReal

/--
Pass a bounded sequence of finite differentiated Galerkin trajectories to a
finite chain of ambient weak-wave solutions.

For each trajectory, displacement, velocity, and acceleration are realized
by the canonical Bochner classes from `SecondOrderSolutionOn`.  Their two
integrated time identities and projected residual equation are therefore
not assumptions of this theorem.  The adjacent pointwise relations in the
finite differentiated family induce the exact adjacent Bochner identities
required by the common-filter compactness theorem.
-/
theorem exists_finiteWeakWaveChain_of_bounded_finiteTimeDerivativeFamily {m : ℕ} {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {a b : ℝ} (T : GelfandTriple (V := V) (H := H))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (hBmeas : AEStronglyMeasurable B (volume.restrict (Set.Ioc a b))) (MB : ℝ) (hMB : 0 ≤ MB)
    (hBbound : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖B t‖ ≤ MB) {Sseq : ℕ → Submodule ℝ V}
    [∀ n, FiniteDimensional ℝ (Sseq n)] {K : NNReal}
    (P : ∀ n, StableTrialProjection T (Sseq n) K)
    (hP : ∀ v : V, Filter.Tendsto (fun n ↦ ((P n).energyProjection v : V)) Filter.atTop (nhds v))
    (forcing : Fin (m + 1) → ℝ → StrongDual ℝ V)
    (ell : Fin (m + 1) → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (hEll : ∀ r : Fin (m + 1),
      (ell r : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Set.Ioc a b)] forcing r)
    (q0 p0 : (n : ℕ) → Fin (m + 1) → Sseq n)
    (U : (n : ℕ) → (r : Fin (m + 1)) → SecondOrderSolutionOn
      (fun t ↦ gelfandGalerkinOperator T (Sseq n) (B t))
      (gelfandGalerkinForcing T (Sseq n) (forcing r)) a b (q0 n r) (p0 n r))
    (hab : a < b) (q : Fin (m + 1) → V) (p : Fin (m + 1) → H)
    (hq0 : ∀ r : Fin (m + 1), Filter.Tendsto (fun n ↦ (q0 n r : V)) Filter.atTop (nhds (q r)))
    (hp0 : ∀ r : Fin (m + 1),
      Filter.Tendsto (fun n ↦ T.inclusion (p0 n r : V)) Filter.atTop (nhds (p r)))
    (huBounded : ∀ r : Fin (m + 1),
      Bornology.IsBounded (Set.range fun n ↦ (U n r).displacementLp hab.le))
    (hvelocityBounded : ∀ r : Fin (m + 1),
      Bornology.IsBounded (Set.range fun n ↦ (U n r).velocityLp hab.le))
    (haccelerationBounded : ∀ r : Fin (m + 1), Bornology.IsBounded
      (Set.range fun n ↦ (U n r).accelerationLp (P n) hab.le (ell r) hBmeas hBbound))
    (Ru : Fin (m + 1) → ℝ) (huNorm : ∀ (r : Fin (m + 1)) n, ‖(U n r).displacementLp hab.le‖ ≤ Ru r)
    (Cu Cv : ℝ)
    (huTopEssential : ∀ n, ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      ‖(U n (0 : Fin (m + 1))).displacementLp hab.le t‖ ≤ Cu)
    (hvelocityTopEssential : ∀ n, ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      ‖(U n (0 : Fin (m + 1))).velocityLp hab.le t‖ ≤ Cv)
    (hdisplacementLink : ∀ (r : Fin m) n, (U n r.castSucc).displacement = (U n r.succ).velocity)
    (hvelocityLink : ∀ (r : Fin m) n, (U n r.castSucc).velocity =
      (U n r.succ).coefficientAcceleration) :
    ∃ (u : Fin (m + 1) → Lp V 2 (volume.restrict (Set.Ioc a b)))
        (velocity : Fin (m + 1) → Lp H 2 (volume.restrict (Set.Ioc a b)))
        (acceleration : Fin (m + 1) → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))),
      (∀ r : Fin (m + 1), Hyperbolic.Variational.IsGelfandWeakWaveSolution
        T B (ell r) (u r) (velocity r) (acceleration r) (q r) (p r)) ∧
      (∀ r : Fin m,
        T.inclusion.compLpL 2 (volume.restrict (Set.Ioc a b)) (u r.castSucc) = velocity r.succ) ∧
      (∀ r : Fin m, T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) (velocity r.castSucc) =
        acceleration r.succ) ∧
      MemLp (fun t ↦ u (0 : Fin (m + 1)) t) (⊤ : ENNReal) (volume.restrict (Set.Ioc a b)) ∧
      MemLp (fun t ↦ velocity (0 : Fin (m + 1)) t) (⊤ : ENNReal)
        (volume.restrict (Set.Ioc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖u (0 : Fin (m + 1)) t‖ ≤ Cu) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖velocity (0 : Fin (m + 1)) t‖ ≤ Cv) :=
  Hyperbolic.HigherRegularity.exists_finiteWeakWaveChain_of_bounded_projected_galerkin_family
    T B hab hBmeas MB hMB hBbound P hP ell (fun r n ↦ (U n r).displacementLp hab.le)
    (fun r n ↦ (U n r).velocityLp hab.le)
    (fun r n ↦ (U n r).accelerationLp (P n) hab.le (ell r) hBmeas hBbound) q p
    (fun r n ↦ (q0 n r : V)) (fun r n ↦ T.inclusion (p0 n r : V)) hq0 hp0 huBounded
    hvelocityBounded haccelerationBounded Ru huNorm Cu Cv huTopEssential hvelocityTopEssential
    (fun r n ↦ (U n r).displacementIdentity hab)
    (fun r n w τ ↦ (U n r).velocityIdentity (P n) hab.le (ell r) (hEll r) hBmeas hBbound w τ)
    (fun _ _ ↦ rfl)
    (fun r n ↦ Lp.ext (by
      filter_upwards [T.inclusion.coeFn_compLpL ((U n r.castSucc).displacementLp hab.le),
        (U n r.castSucc).displacementLp_apply_ae hab.le,
        (U n r.succ).velocityLp_apply_ae hab.le] with t hinclusion hu hvelocity
      rw [hinclusion, hu, hvelocity]
      exact congrArg (fun z : Sseq n ↦ T.inclusion (z : V)) (congrFun (hdisplacementLink r n) t)))
    (fun r n ↦ Lp.ext (by
      filter_upwards [T.pivotToDual.coeFn_compLpL ((U n r.castSucc).velocityLp hab.le),
        (U n r.castSucc).velocityLp_apply_ae hab.le, (U n r.succ).accelerationLp_apply_ae
          (P n) hab.le (ell r.succ) (hEll r.succ) hBmeas hBbound] with t hpivot hvelocity hacc
      rw [hpivot, hvelocity, hacc]
      exact congrArg (fun z : Sseq n ↦ T.pivotToDual (T.inclusion (z : V)))
        (congrFun (hvelocityLink r n) t)))

end Hyperbolic.Variational.GelfandGalerkin
