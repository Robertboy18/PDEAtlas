/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.RitzInitialCompatibility
public import PDE.Analysis.Evolution.Galerkin.ImprovedRegularity.PivotDerivative
public import PDE.Analysis.Evolution.Integrated.Solution
import PDE.Analysis.Evolution.Galerkin.ImprovedRegularity.AutonomousEnergy
import PDE.Analysis.Evolution.Galerkin.Measurable.Caratheodory
import PDE.Analysis.Evolution.Galerkin.PairedL2Differentiation.Compactness
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Ritz-initialized differentiated Galerkin limits

We specialize the paired `L²` compactness theorem to autonomous Galerkin
families initialized by Ritz projections. The first theorem takes a
Ritz-initialized family as input; the second constructs that family from a
pivot-valued forcing class and an absolutely continuous dual representative.
In both the differentiated load is only Bochner `L²`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.3, Theorem 5(ii) and steps 4-7 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/--
Common-subnet limit for a Ritz-initialized autonomous Galerkin family and
its time derivative.

This is the limit step of the proof of Evans §7.1.3, Theorem 5(ii), except that
the original initial values are the Ritz projections of `g`. The
compatibility identity

`ell(a)(v) = ⟪duInit, Jv⟫ + B(g,v)`

identifies each mass-inverted initial velocity with the pivot projection of
`duInit`. The differentiated family is the family of velocities of the original one, with
load `ellDot ∈ L²(a, b; V*)`.
-/
theorem IsGelfandIntegratedWeakSolution.exists_of_autonomous_ritz_l2_galerkin_families
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V)
    [hfinite : ∀ n, FiniteDimensional ℝ (S n)]
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (B : V →L[ℝ] StrongDual ℝ V)
    (ell ellDot : ℝ → StrongDual ℝ V)
    {a b C M MB : ℝ}
    (hab : a < b) (hC : 0 < C) (hMB : 0 ≤ MB)
    (hBbound : ∀ᵐ _t ∂(volume.restrict (Set.Ioc a b)), ‖B‖ ≤ MB)
    (hcoercive : ∀ w : V, C * ‖w‖ ^ 2 ≤ B w w)
    (hell : MemLp ell 2 (volume.restrict (Set.Ioc a b)))
    (hellDot : MemLp ellDot 2 (volume.restrict (Set.Ioc a b)))
    (hellAC : AbsolutelyContinuousOnInterval ell a b)
    (hellDeriv :
      ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
        HasDerivAt ell (ellDot t) t)
    (g : V) (duInit : H)
    (hcompat : ∀ v : V,
      ell a v = inner ℝ duInit (T.inclusion v) + B g v)
    (G : ∀ n, AEGelfandGalerkinApproximation T (S n)
      (fun _ ↦ B) ell a b C M
        (RitzInitialCompatibility.projection
          (S n) B hC hcoercive g))
    (velocityBoundSq : ℝ)
    (hVelocityBoundSq : 0 ≤ velocityBoundSq)
    (hvelocity : ∀ n,
      ‖(G n).pivotDerivativeLp T (S n)‖ ^ 2 ≤ velocityBoundSq) :
    ∃ (u : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (duH : Lp H 2 (volume.restrict (Set.Ioc a b)))
        (du : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (ddu : Lp (StrongDual ℝ V) 2
          (volume.restrict (Set.Ioc a b))),
      IsGelfandIntegratedWeakSolution T (fun _ ↦ B) ell u
          (T.inclusion g) ∧
      HasGelfandWeakTimeDerivativeOn T u
        (T.pivotToDual.compLpL 2
          (volume.restrict (Set.Ioc a b)) duH) ∧
      IsGelfandIntegratedWeakSolution T (fun _ ↦ B) ellDot du duInit ∧
      HasGelfandWeakTimeDerivativeOn T du ddu ∧
      T.inclusion.compLpL 2 (volume.restrict (Set.Ioc a b)) du = duH ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        T.pivotToDual (duH t) + B (u t) = ell t) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        ddu t + B (du t) = ellDot t) ∧
      ‖du‖ ^ 2 ≤
        (2 / C) *
          ((1 / 2 : ℝ) * ‖duInit‖ ^ 2 +
            (1 / (2 * C)) * ‖hellDot.toLp ellDot‖ ^ 2) := by
  have hBmeas : AEStronglyMeasurable (fun _ : ℝ ↦ B) (volume.restrict (Set.Ioc a b)) := by fun_prop
  classical
  let u₀ : ∀ n, S n := fun n ↦ RitzInitialCompatibility.projection (S n) B hC hcoercive g
  let du₀ : ∀ n, S n := fun n ↦ gelfandGalerkinVectorField T (S n) (fun _ ↦ B) ell a (u₀ n)
  have hdu₀_eq (n : ℕ) : du₀ n = (P n).projection duInit :=
    RitzInitialCompatibility.initialVelocity_eq_pivotProjection T (S n) B hC hcoercive (P n) ell a
      g duInit hcompat
  have hu₀ : Filter.Tendsto (fun n ↦ T.inclusion (u₀ n : V)) Filter.atTop
      (nhds (T.inclusion g)) :=
    (T.inclusion.continuous.tendsto g).comp
      (RitzInitialCompatibility.tendsto_projection_of_eventually_approximable B hC hcoercive
        hdenseEnergy g)
  have hdu₀ : Filter.Tendsto (fun n ↦ T.inclusion (du₀ n : V)) Filter.atTop (nhds duInit) := by
    simpa only [hdu₀_eq] using
      StableTrialProjection.tendsto_inclusion_projection_of_eventually_approximable P
        (eventually_approximable_pivot_of_energy T S hdenseEnergy) duInit
  have hu₀Bound (n : ℕ) :
      ‖T.inclusion (u₀ n : V)‖ ^ 2 ≤ (‖T.inclusion‖ * ((‖B‖ / C) * ‖g‖)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (T.inclusion.le_of_opNorm_le_of_le le_rfl
      (RitzInitialCompatibility.norm_projection_le (S n) B hC hcoercive g)) 2
  have hdu₀Bound (n : ℕ) : ‖T.inclusion (du₀ n : V)‖ ^ 2 ≤ ‖duInit‖ ^ 2 := by
    rw [hdu₀_eq]
    exact pow_le_pow_left₀ (norm_nonneg _) ((P n).norm_inclusion_projection_le duInit) 2
  have hDG (n : ℕ) :
      ∃ DG : L2DifferentiatedGalerkinApproximation T (S n) B ellDot a b (du₀ n),
        DG.trajectory =ᵐ[volume.restrict (Set.Ioc a b)] (G n).coefficientDerivative ∧
        T.inclusion.compLpL 2 (volume.restrict (Set.Ioc a b)) (DG.ambientTrajectoryLp hab.le) =
          (G n).pivotDerivativeLp T (S n) := by
    simpa only [du₀, u₀] using
      L2DifferentiatedGalerkinApproximation.exists_of_autonomous (G n) hab.le hellAC hellDeriv
        hellDot
  choose DG _ htrajectoryLink using hDG
  exact IsGelfandIntegratedWeakSolution.exists_of_paired_l2_differentiated_galerkin_families
    T S P hdenseEnergy B ell ellDot hab hC hMB hBbound hcoercive hell hellDot u₀ du₀
    (T.inclusion g) duInit hu₀ hdu₀ _ _ (by positivity) (by positivity) hu₀Bound hdu₀Bound G DG
    velocityBoundSq hVelocityBoundSq hvelocity htrajectoryLink

omit [CompleteSpace V] [CompleteSpace H] in
/-- The Ritz projection bounds the initial principal energy in the autonomous
velocity estimate, uniformly over the trial space. -/
private theorem norm_pivotDerivativeLp_sq_le_ritz
    (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V) [FiniteDimensional ℝ S]
    (B : V →L[ℝ] StrongDual ℝ V) {a b C M : ℝ}
    (f : Lp H 2 (volume.restrict (Ioc a b)))
    (hab : a ≤ b) (hC : 0 < C)
    (hBsymm : ∀ u v : V, B u v = B v u)
    (hcoercive : ∀ w : V, C * ‖w‖ ^ 2 ≤ B w w) (g : V)
    (G : AEGelfandGalerkinApproximation T S
      (fun _ ↦ B) (fun t ↦ T.pivotToDual (f t)) a b C M
      (RitzInitialCompatibility.projection S B hC hcoercive g)) :
    ‖G.pivotDerivativeLp T S‖ ^ 2 ≤
      ‖B‖ * ((‖B‖ / C) * ‖g‖) ^ 2 + 2 * ‖f‖ ^ 2 := by
  let u₀ := RitzInitialCompatibility.projection S B hC hcoercive g
  have hBnonneg (w : V) : 0 ≤ B w w := (mul_nonneg hC.le (sq_nonneg ‖w‖)).trans (hcoercive w)
  -- The principal-energy estimate is stated for `B + R`; transport the
  -- constant form to the equivalent decomposition `B + 0`.
  let Gzero : AEGelfandGalerkinApproximation T S
      (fun _ ↦ B + 0) (fun t ↦ T.pivotToDual (f t)) a b C M u₀ :=
    G.congrOperatorAE (.of_forall fun _ ↦ by ext v w; simp)
  have hpivot : Gzero.pivotDerivativeLp T S = G.pivotDerivativeLp T S := by
    dsimp only [Gzero, AEGelfandGalerkinApproximation.pivotDerivativeLp,
      AEGelfandGalerkinApproximation.coefficientDerivativeLp,
      AEGelfandGalerkinApproximation.congrOperatorAE]
  have hmain : ‖G.pivotDerivativeLp T S‖ ^ 2 ≤
      B (u₀ : V) (u₀ : V) + 2 * ∫ t in a..b, ‖f t‖ ^ 2 := by
    simpa [hpivot] using AEGelfandGalerkinApproximation.norm_pivotDerivativeLp_sq_le
      (L := 0) T S B (fun _ ↦ 0) f Gzero hab hBsymm hBnonneg (by simp)
  have hBinitial : B (u₀ : V) (u₀ : V) ≤ ‖B‖ * ((‖B‖ / C) * ‖g‖) ^ 2 :=
    calc B (u₀ : V) (u₀ : V) ≤ ‖B‖ * ‖(u₀ : V)‖ * ‖(u₀ : V)‖ :=
          (Real.le_norm_self _).trans (B.le_opNorm₂ _ _)
      _ ≤ ‖B‖ * ((‖B‖ / C) * ‖g‖) ^ 2 := by
        rw [mul_assoc, ← sq]
        gcongr
        exact RitzInitialCompatibility.norm_projection_le S B hC hcoercive g
  rw [intervalIntegral.integral_of_le hab, ← Lp.norm_sq_eq_integral_norm_sq] at hmain
  linarith

/--
Construct the Ritz-initialized autonomous Galerkin family and pass it,
together with its differentiated family, through one compactness subnet.

This is the abstract counterpart of the existence step in the proof of Evans §7.1.3,
Theorem 5(ii).
The load is supplied both as an `L²(H)` class `f` and as an absolutely
continuous dual-valued representative `ell`. The former gives the sharp
velocity estimate, while the latter is the representative that can be
differentiated in the finite-dimensional equations.

Continuity of `ell` on the compact interval supplies the pointwise bound used by the
Carathéodory construction.
-/
theorem IsGelfandIntegratedWeakSolution.exists_of_autonomous_ritz_l2_galerkin
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V)
    [hfinite : ∀ n, FiniteDimensional ℝ (S n)]
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (B : V →L[ℝ] StrongDual ℝ V)
    {a b C : ℝ}
    (f : Lp H 2 (volume.restrict (Set.Ioc a b)))
    (ell ellDot : ℝ → StrongDual ℝ V)
    (hab : a < b) (hC : 0 < C)
    (hBsymm : ∀ u v : V, B u v = B v u)
    (hcoercive : ∀ w : V, C * ‖w‖ ^ 2 ≤ B w w)
    (hellRep : ell =ᵐ[volume.restrict (Set.Ioc a b)]
      fun t ↦ T.pivotToDual (f t))
    (hellAC : AbsolutelyContinuousOnInterval ell a b)
    (hellDot : MemLp ellDot 2 (volume.restrict (Set.Ioc a b)))
    (hellDeriv :
      ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
        HasDerivAt ell (ellDot t) t)
    (g : V) (duInit : H)
    (hcompat : ∀ v : V,
      ell a v = inner ℝ duInit (T.inclusion v) + B g v) :
    ∃ (u : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (duH : Lp H 2 (volume.restrict (Set.Ioc a b)))
        (du : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (ddu : Lp (StrongDual ℝ V) 2
          (volume.restrict (Set.Ioc a b))),
      IsGelfandIntegratedWeakSolution T (fun _ ↦ B) ell u
          (T.inclusion g) ∧
      HasGelfandWeakTimeDerivativeOn T u
        (T.pivotToDual.compLpL 2
          (volume.restrict (Set.Ioc a b)) duH) ∧
      IsGelfandIntegratedWeakSolution T (fun _ ↦ B) ellDot du duInit ∧
      HasGelfandWeakTimeDerivativeOn T du ddu ∧
      T.inclusion.compLpL 2 (volume.restrict (Set.Ioc a b)) du = duH ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        T.pivotToDual (duH t) + B (u t) = ell t) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        ddu t + B (du t) = ellDot t) ∧
      ‖du‖ ^ 2 ≤
        (2 / C) *
          ((1 / 2 : ℝ) * ‖duInit‖ ^ 2 +
            (1 / (2 * C)) * ‖hellDot.toLp ellDot‖ ^ 2) := by
  classical
  let operatorSeminormedAddCommGroup :
      SeminormedAddCommGroup (V →L[ℝ] StrongDual ℝ V) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
      (E := V) (F := StrongDual ℝ V) (σ₁₂ := RingHom.id ℝ)
  have hellContinuous : ContinuousOn ell (Set.Icc a b) := by
    simpa only [Set.uIcc_of_le hab.le] using hellAC.continuousOn
  obtain ⟨Rell, hRell⟩ := isCompact_Icc.exists_bound_of_continuousOn hellContinuous
  let MB : NNReal := ⟨‖B‖, norm_nonneg B⟩
  let Mell : NNReal := ⟨Rell, (norm_nonneg (ell a)).trans (hRell a ⟨le_rfl, hab.le⟩)⟩
  let u₀ : ∀ n, S n := fun n ↦ RitzInitialCompatibility.projection (S n) B hC hcoercive g
  have hBmeasIcc : AEStronglyMeasurable (fun _ : ℝ ↦ B) (volume.restrict (Set.Icc a b)) :=
    aestronglyMeasurable_const
  obtain ⟨G⟩ := AEGelfandGalerkinApproximation.exists_sequence T S (fun n ↦ hfinite n)
    (fun _ ↦ B) ell hab.le hC (fun v ↦ hBmeasIcc.apply_continuousLinearMap v)
    (hellContinuous.aestronglyMeasurable measurableSet_Icc) MB Mell (fun _ _ ↦ le_rfl) hRell
    (fun _ _ w ↦ hcoercive w) u₀
  have hellMem : MemLp ell 2 (volume.restrict (Set.Ioc a b)) :=
    (memLp_congr_ae hellRep).2 ((Lp.memLp f).continuousLinearMap_comp T.pivotToDual)
  have hvelocity (n : ℕ) : ‖(G n).pivotDerivativeLp T (S n)‖ ^ 2 ≤
      ‖B‖ * ((‖B‖ / C) * ‖g‖) ^ 2 + 2 * ‖f‖ ^ 2 :=
    norm_pivotDerivativeLp_sq_le_ritz T (S n) B f hab.le hC hBsymm hcoercive g
      ((G n).congrForcingAE hellRep)
  exact IsGelfandIntegratedWeakSolution.exists_of_autonomous_ritz_l2_galerkin_families
    T S P hdenseEnergy B ell ellDot hab hC (norm_nonneg B)
    (.of_forall fun _ ↦ le_rfl) hcoercive hellMem hellDot hellAC hellDeriv g duInit hcompat G _
    (by positivity) hvelocity

end PDE.Analysis.Evolution
