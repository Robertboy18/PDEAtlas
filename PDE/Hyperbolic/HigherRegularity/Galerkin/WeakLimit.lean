/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.Galerkin.BochnerRealization
import Mathlib.Analysis.LocallyConvex.WeakSpace
import PDE.Analysis.Evolution.Compactness.Lp.Ultrafilter
import PDE.Hyperbolic.WeakWave.Compactness.ProjectedGalerkin
import PDE.Hyperbolic.WeakWave.Compactness.WeakLimits
public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic

/-!
# Weak-limit closure for Evans's finite differentiated Galerkin chain

In the proof of Theorem 5(ii) in Evans, §7.2.3, the differentiated wave comes from the same
Galerkin family, by differentiating the Galerkin identity. We obtain every time-differentiated
weak wave of the chain from one Galerkin family in this way, so the exact identities between
adjacent Galerkin levels must survive passage to weak limits along the same filter. We prove
that finite-family closure step.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, proof of Theorem 5, step 2, equation (53), and proof
  of Theorem 6.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Hyperbolic.HigherRegularity

open PDE.Analysis.Evolution
open Hyperbolic.Variational
open scoped ENNReal

variable {m : ℕ}

/--
Every adjacent identity in a finite differentiated Galerkin chain survives
weak convergence along one common filter.

At Galerkin level `i`, index `r.castSucc` is the differentiated wave and
index `r.succ` is the preceding wave. Thus its displacement maps to the
preceding velocity, while its velocity maps to the preceding acceleration.
The acceleration limits are stated after Riesz transport, as in
`PDE.Hyperbolic.WeakWave.Compactness`.
-/
theorem finiteWeakWaveChain_links_of_common_weak_limits {α ι V H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {μ : Measure α} {l : Filter ι} [l.NeBot]
    (T : GelfandTriple (V := V) (H := H)) (uApprox : Fin (m + 1) → ι → Lp V 2 μ)
    (velocityApprox : Fin (m + 1) → ι → Lp H 2 μ)
    (accelerationApprox : Fin (m + 1) → ι → Lp (StrongDual ℝ V) 2 μ) (u : Fin (m + 1) → Lp V 2 μ)
    (velocity : Fin (m + 1) → Lp H 2 μ) (acceleration : Fin (m + 1) → Lp (StrongDual ℝ V) 2 μ)
    (huWeak : ∀ r : Fin (m + 1),
      Filter.Tendsto (fun i ↦ toWeakSpace ℝ _ (uApprox r i)) l (nhds (toWeakSpace ℝ _ (u r))))
    (hvelocityWeak : ∀ r : Fin (m + 1), Filter.Tendsto
      (fun i ↦ toWeakSpace ℝ _ (velocityApprox r i)) l (nhds (toWeakSpace ℝ _ (velocity r))))
    (haccelerationWeak : ∀ r : Fin (m + 1), Filter.Tendsto (fun i ↦
      toWeakSpace ℝ _ (rieszFromDualLp (accelerationApprox r i))) l
      (nhds (toWeakSpace ℝ _ (rieszFromDualLp (acceleration r)))))
    (hvelocityApproxLink : ∀ r : Fin m, ∀ i, T.inclusion.compLpL 2 μ (uApprox r.castSucc i) =
      velocityApprox r.succ i)
    (haccelerationApproxLink : ∀ r : Fin m, ∀ i,
      T.pivotToDual.compLpL 2 μ (velocityApprox r.castSucc i) = accelerationApprox r.succ i) :
    (∀ r : Fin m, T.inclusion.compLpL 2 μ (u r.castSucc) = velocity r.succ) ∧
    (∀ r : Fin m, T.pivotToDual.compLpL 2 μ (velocity r.castSucc) = acceleration r.succ) := by
  refine ⟨fun r ↦ compLpL_eq_of_tendsto_weak T.inclusion _ _ _ _ (huWeak r.castSucc)
    (hvelocityWeak r.succ) (hvelocityApproxLink r), fun r ↦ ?_⟩
  let P : Lp H 2 μ →L[ℝ] Lp V 2 μ := rieszFromDualLp.comp (T.pivotToDual.compLpL 2 μ)
  have hriesz : rieszFromDualLp (acceleration r.succ) = P (velocity r.castSucc) :=
    (toWeakSpace ℝ _).injective <| tendsto_nhds_unique (haccelerationWeak r.succ) <|
      (((WeakSpace.map P).continuous.tendsto _).comp (hvelocityWeak r.castSucc)).congr fun i ↦
        congrArg (fun z ↦ toWeakSpace ℝ _ (rieszFromDualLp z)) (haccelerationApproxLink r i)
  rw [← rieszToDualLp_rieszFromDualLp (acceleration r.succ), hriesz]
  exact (rieszToDualLp_rieszFromDualLp _).symm

/--
Evans, §7.2.3: finite differentiated Galerkin limit passage.

Suppose every level of a finite differentiated Galerkin family uses the same
trial spaces, stable projections, and filter refining `atTop`.  At each level
the two integrated time identities and the projected residual equation are
the finite-dimensional equations supplied by the Galerkin trajectory.
Assume all three Bochner components at every level converge weakly along this
one filter.

Then every level is an ambient weak-wave solution.  Moreover, the
exact adjacent differentiated-trajectory identities survive the same limit:
the more differentiated displacement is the preceding pivot velocity, and
its pivot velocity is the preceding dual acceleration.  The conclusion uses
exact equalities of Bochner classes, which are stronger than representative
almost-everywhere identities.
-/
theorem finiteWeakWaveChain_of_projected_galerkin_weak_limits {V H : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} (T : GelfandTriple (V := V) (H := H)) (B : ℝ → V →L[ℝ] StrongDual ℝ V) (hab : a < b)
    (hBmeas : AEStronglyMeasurable B (volume.restrict (Set.Ioc a b))) (MB : ℝ) (hMB : 0 ≤ MB)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB) {Sseq : ℕ → Submodule ℝ V}
    {K : NNReal} (P : ∀ n, StableTrialProjection T (Sseq n) K)
    (hP : ∀ v : V, Filter.Tendsto (fun n ↦ ((P n).energyProjection v : V)) Filter.atTop (nhds v))
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ Filter.atTop)
    (ell : Fin (m + 1) → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (uApprox : Fin (m + 1) → ℕ → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (velocityApprox : Fin (m + 1) → ℕ → Lp H 2 (volume.restrict (Set.Ioc a b)))
    (accelerationApprox : Fin (m + 1) → ℕ → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (u : Fin (m + 1) → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (velocity : Fin (m + 1) → Lp H 2 (volume.restrict (Set.Ioc a b)))
    (acceleration : Fin (m + 1) → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (q0 : Fin (m + 1) → V) (p0 : Fin (m + 1) → H) (q0Approx : Fin (m + 1) → ℕ → V)
    (p0Approx : Fin (m + 1) → ℕ → H)
    (hq0 : ∀ r : Fin (m + 1), Filter.Tendsto (q0Approx r) Filter.atTop (nhds (q0 r)))
    (hp0 : ∀ r : Fin (m + 1), Filter.Tendsto (p0Approx r) Filter.atTop (nhds (p0 r)))
    (huWeak : ∀ r : Fin (m + 1),
      Filter.Tendsto (fun n ↦ toWeakSpace ℝ _ (uApprox r n)) l (nhds (toWeakSpace ℝ _ (u r))))
    (hvelocityWeak : ∀ r : Fin (m + 1), Filter.Tendsto
      (fun n ↦ toWeakSpace ℝ _ (velocityApprox r n)) l (nhds (toWeakSpace ℝ _ (velocity r))))
    (haccelerationWeak : ∀ r : Fin (m + 1), Filter.Tendsto (fun n ↦
      toWeakSpace ℝ _ (rieszFromDualLp (accelerationApprox r n))) l
      (nhds (toWeakSpace ℝ _ (rieszFromDualLp (acceleration r)))))
    (Ru : Fin (m + 1) → ℝ) (huNorm : ∀ (r : Fin (m + 1)) n, ‖uApprox r n‖ ≤ Ru r)
    (hdisplacementApprox : ∀ (r : Fin (m + 1)) n, IsGelfandIntegratedWeakSolution T (fun _ ↦ 0)
      (fun t ↦ T.pivotToDual (velocityApprox r n t)) (uApprox r n) (T.inclusion (q0Approx r n)))
    (hvelocityApprox : ∀ (r : Fin (m + 1)) n (w : V) (τ : TimeTest a b),
      -(∫ t, inner ℝ (velocityApprox r n t) (T.inclusion w) *
      τ.derivToLp t ∂(volume.restrict (Set.Ioc a b))) = (∫ t,
      accelerationApprox r n t w * τ.toLp t ∂(volume.restrict (Set.Ioc a b))) +
      inner ℝ (p0Approx r n) (T.inclusion w) * τ.toFun a)
    (hprojected : ∀ (r : Fin (m + 1)) n, accelerationApprox r n =
      (Hyperbolic.Variational.SecondOrderSolutionOn.projectedDual (P n)).compLpL 2
      (volume.restrict (Set.Ioc a b)) (gelfandResidualLp B (ell r) (uApprox r n)
      (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound))
    (hvelocityApproxLink : ∀ (r : Fin m) n, T.inclusion.compLpL 2 (volume.restrict (Set.Ioc a b))
      (uApprox r.castSucc n) = velocityApprox r.succ n)
    (haccelerationApproxLink : ∀ (r : Fin m) n, T.pivotToDual.compLpL 2
      (volume.restrict (Set.Ioc a b)) (velocityApprox r.castSucc n) = accelerationApprox r.succ n) :
    (∀ r : Fin (m + 1), Hyperbolic.Variational.IsGelfandWeakWaveSolution
        T B (ell r) (u r) (velocity r) (acceleration r) (q0 r) (p0 r)) ∧
    (∀ r : Fin m,
        T.inclusion.compLpL 2 (volume.restrict (Set.Ioc a b)) (u r.castSucc) = velocity r.succ) ∧
    (∀ r : Fin m, T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) (velocity r.castSucc) =
        acceleration r.succ) :=
  ⟨fun r ↦ IsGelfandWeakWaveSolution.of_projected_galerkin_weak_limits_of_initial_tendsto
      hab hBmeas MB hMB hBbound P hP hl (uApprox r) (velocityApprox r) (accelerationApprox r)
      (huWeak r) (hvelocityWeak r) (haccelerationWeak r) (Ru r) (huNorm r) (q0Approx r)
      (p0Approx r) (hq0 r) (hp0 r) (hdisplacementApprox r) (hvelocityApprox r) (hprojected r),
    finiteWeakWaveChain_links_of_common_weak_limits T uApprox velocityApprox accelerationApprox
      u velocity acceleration huWeak hvelocityWeak haccelerationWeak hvelocityApproxLink
      haccelerationApproxLink⟩

/--
Evans, §7.2.3: finite differentiated Galerkin compactness.

Uniformly bounded displacement, velocity, and acceleration families at every
level of a finite differentiated Galerkin chain have one common weakly
convergent refinement. The limits are weak waves, and every exact
adjacent time-derivative identity survives in the limit. Essential bounds at
the most differentiated level pass to its displacement and velocity limits,
which are the starting bounds in Evans's higher-regularity induction.
-/
theorem exists_finiteWeakWaveChain_of_bounded_projected_galerkin_family {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {a b : ℝ} (T : GelfandTriple (V := V) (H := H))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) (hab : a < b)
    (hBmeas : AEStronglyMeasurable B (volume.restrict (Set.Ioc a b))) (MB : ℝ) (hMB : 0 ≤ MB)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB) {Sseq : ℕ → Submodule ℝ V}
    {K : NNReal} (P : ∀ n, StableTrialProjection T (Sseq n) K)
    (hP : ∀ v : V, Filter.Tendsto (fun n ↦ ((P n).energyProjection v : V)) Filter.atTop (nhds v))
    (ell : Fin (m + 1) → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (uApprox : Fin (m + 1) → ℕ → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (velocityApprox : Fin (m + 1) → ℕ → Lp H 2 (volume.restrict (Set.Ioc a b)))
    (accelerationApprox : Fin (m + 1) → ℕ → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (q0 : Fin (m + 1) → V) (p0 : Fin (m + 1) → H) (q0Approx : Fin (m + 1) → ℕ → V)
    (p0Approx : Fin (m + 1) → ℕ → H)
    (hq0 : ∀ r : Fin (m + 1), Filter.Tendsto (q0Approx r) Filter.atTop (nhds (q0 r)))
    (hp0 : ∀ r : Fin (m + 1), Filter.Tendsto (p0Approx r) Filter.atTop (nhds (p0 r)))
    (huBounded : ∀ r : Fin (m + 1), Bornology.IsBounded (Set.range (uApprox r)))
    (hvelocityBounded : ∀ r : Fin (m + 1), Bornology.IsBounded (Set.range (velocityApprox r)))
    (haccelerationBounded : ∀ r : Fin (m + 1),
      Bornology.IsBounded (Set.range (accelerationApprox r)))
    (Ru : Fin (m + 1) → ℝ) (huNorm : ∀ (r : Fin (m + 1)) n, ‖uApprox r n‖ ≤ Ru r) (Cu Cv : ℝ)
    (huTopEssential : ∀ n, ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      ‖uApprox (0 : Fin (m + 1)) n t‖ ≤ Cu)
    (hvelocityTopEssential : ∀ n, ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      ‖velocityApprox (0 : Fin (m + 1)) n t‖ ≤ Cv)
    (hdisplacementApprox : ∀ (r : Fin (m + 1)) n, IsGelfandIntegratedWeakSolution T (fun _ ↦ 0)
      (fun t ↦ T.pivotToDual (velocityApprox r n t)) (uApprox r n) (T.inclusion (q0Approx r n)))
    (hvelocityApprox : ∀ (r : Fin (m + 1)) n (w : V) (τ : TimeTest a b),
      -(∫ t, inner ℝ (velocityApprox r n t) (T.inclusion w) *
      τ.derivToLp t ∂(volume.restrict (Set.Ioc a b))) = (∫ t,
      accelerationApprox r n t w * τ.toLp t ∂(volume.restrict (Set.Ioc a b))) +
      inner ℝ (p0Approx r n) (T.inclusion w) * τ.toFun a)
    (hprojected : ∀ (r : Fin (m + 1)) n, accelerationApprox r n =
      (Hyperbolic.Variational.SecondOrderSolutionOn.projectedDual (P n)).compLpL 2
      (volume.restrict (Set.Ioc a b)) (gelfandResidualLp B (ell r) (uApprox r n)
      (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound))
    (hvelocityApproxLink : ∀ (r : Fin m) n, T.inclusion.compLpL 2 (volume.restrict (Set.Ioc a b))
      (uApprox r.castSucc n) = velocityApprox r.succ n)
    (haccelerationApproxLink : ∀ (r : Fin m) n, T.pivotToDual.compLpL 2
      (volume.restrict (Set.Ioc a b)) (velocityApprox r.castSucc n) = accelerationApprox r.succ n) :
    ∃ (u : Fin (m + 1) → Lp V 2 (volume.restrict (Set.Ioc a b)))
        (velocity : Fin (m + 1) → Lp H 2 (volume.restrict (Set.Ioc a b)))
        (acceleration : Fin (m + 1) → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))),
      (∀ r : Fin (m + 1), Hyperbolic.Variational.IsGelfandWeakWaveSolution
        T B (ell r) (u r) (velocity r) (acceleration r) (q0 r) (p0 r)) ∧
      (∀ r : Fin m,
        T.inclusion.compLpL 2 (volume.restrict (Set.Ioc a b)) (u r.castSucc) = velocity r.succ) ∧
      (∀ r : Fin m, T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) (velocity r.castSucc) =
        acceleration r.succ) ∧
      MemLp (fun t ↦ u (0 : Fin (m + 1)) t) (⊤ : ENNReal) (volume.restrict (Set.Ioc a b)) ∧
      MemLp (fun t ↦ velocity (0 : Fin (m + 1)) t) (⊤ : ENNReal)
        (volume.restrict (Set.Ioc a b)) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖u (0 : Fin (m + 1)) t‖ ≤ Cu) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖velocity (0 : Fin (m + 1)) t‖ ≤ Cv) := by
  obtain ⟨u, Uu, hUu, huWeak⟩ := exists_ultrafilter_weak_limits_finite .atTop uApprox huBounded
  obtain ⟨velocity, Uv, hUv, hvelocityWeak⟩ :=
    exists_ultrafilter_weak_limits_finite (Uu : Filter ℕ) velocityApprox hvelocityBounded
  obtain ⟨accelerationRiesz, Ua, hUa, haccelerationRieszWeak⟩ :=
    exists_ultrafilter_weak_limits_finite (Uv : Filter ℕ)
      (fun r n ↦ rieszFromDualLp (accelerationApprox r n)) fun r ↦ by
        simpa only [← Set.range_comp, Function.comp_def] using
          (haccelerationBounded r).image rieszFromDualLp
  have huWeak' r := (huWeak r).mono_left (hUa.trans hUv)
  have hvelocityWeak' r := (hvelocityWeak r).mono_left hUa
  obtain ⟨h1, h2, h3, h4⟩ :=
    IsGelfandWeakWaveSolution.improvedRegularity_of_weak_L2_limits _ _ (huWeak' 0)
      (hvelocityWeak' 0) Cu Cv (.of_forall huTopEssential) (.of_forall hvelocityTopEssential)
  let acceleration r := rieszToDualLp (accelerationRiesz r)
  obtain ⟨c1, c2, c3⟩ := finiteWeakWaveChain_of_projected_galerkin_weak_limits T B hab hBmeas
    MB hMB hBbound P hP ((hUa.trans hUv).trans hUu) ell uApprox velocityApprox
    accelerationApprox u velocity acceleration q0 p0 q0Approx p0Approx hq0 hp0 huWeak'
    hvelocityWeak' (fun r ↦ by
      simpa only [acceleration, rieszFromDualLp_rieszToDualLp] using haccelerationRieszWeak r)
    Ru huNorm hdisplacementApprox hvelocityApprox hprojected hvelocityApproxLink
    haccelerationApproxLink
  exact ⟨u, velocity, acceleration, c1, c2, c3, h1, h2, h3, h4⟩

end Hyperbolic.HigherRegularity
