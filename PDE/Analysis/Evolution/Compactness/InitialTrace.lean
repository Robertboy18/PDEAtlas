/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.Regularity
public import PDE.Analysis.Evolution.Compactness.Lp.TimeTesting
public import PDE.Analysis.Evolution.Compactness.WeakLimitTesting

/-!
# Initial traces under weak Bochner convergence

An absolutely continuous approximating trajectory satisfies the integrated
identity including its initial value. Weak convergence of both the states and
their L² velocities preserves this identity. The Lions–Magenes theorem
for the identity Gelfand triple then gives a continuous representative with the
same initial value.

The state may first be projected from an H¹ space to L². No pointwise convergence
of approximating trajectories or spatial compact embedding is required.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace PDE.Analysis.Evolution

section InitialIdentity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {a b : ℝ}

/-- Integration by parts for an absolutely continuous representative,
written in the Bochner classes used by weak compactness. -/
theorem integrated_initial_identity_of_absolutelyContinuous
    (hab : a ≤ b) (z : ℝ → H)
    (u g : Lp H 2 (volume.restrict (Ioc a b))) (u₀ : H)
    (hz : AbsolutelyContinuousOnInterval z a b)
    (hzu : z =ᵐ[volume.restrict (Ioc a b)] (u : ℝ → H))
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt z (g t) t)
    (hinit : z a = u₀) (v : H) (τ : TimeTest a b) :
    -(∫ t, inner ℝ (u t) v * τ.derivToLp t ∂volume.restrict (Ioc a b)) =
      (∫ t, inner ℝ (g t) v * τ.toLp t ∂volume.restrict (Ioc a b)) +
        inner ℝ u₀ v * τ.toFun a := by
  have hid := τ.integrationByParts_inner hab v hz hderiv
  rw [hinit] at hid
  simp only [intervalIntegral.integral_of_le hab] at hid
  have htime :
      (∫ t, inner ℝ (z t) v * τ.derivFun t ∂volume.restrict (Ioc a b)) =
        ∫ t, inner ℝ (u t) v * τ.derivToLp t ∂volume.restrict (Ioc a b) := by
    apply integral_congr_ae
    filter_upwards [hzu, τ.derivMemLp.coeFn_toLp] with t ht hτt
    rw [ht, TimeTest.derivToLp, hτt]
  have hvelocity :
      (∫ t, inner ℝ (g t) v * τ.toFun t ∂volume.restrict (Ioc a b)) =
        ∫ t, inner ℝ (g t) v * τ.toLp t ∂volume.restrict (Ioc a b) := by
    apply integral_congr_ae
    filter_upwards [τ.memLp.coeFn_toLp] with t hτt
    rw [TimeTest.toLp, hτt]
  rwa [htime, hvelocity] at hid

/-- Weak Bochner convergence of state and velocity preserves the full initial
identity, including tests that do not vanish at the initial time. -/
theorem integrated_initial_identity_of_weak_state_velocity_limits
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {u g : ι → Lp H 2 (volume.restrict (Ioc a b))}
    {uLimit gLimit : Lp H 2 (volume.restrict (Ioc a b))} (u₀ : H)
    (hu : Tendsto (fun k ↦ toWeakSpace ℝ _ (u k)) l
      (𝓝 (toWeakSpace ℝ _ uLimit)))
    (hg : Tendsto (fun k ↦ toWeakSpace ℝ _ (g k)) l
      (𝓝 (toWeakSpace ℝ _ gLimit)))
    (heq : ∀ k (v : H) (τ : TimeTest a b),
      -(∫ t, inner ℝ (u k t) v * τ.derivToLp t ∂volume.restrict (Ioc a b)) =
        (∫ t, inner ℝ (g k t) v * τ.toLp t ∂volume.restrict (Ioc a b)) +
          inner ℝ u₀ v * τ.toFun a)
    (v : H) (τ : TimeTest a b) :
    -(∫ t, inner ℝ (uLimit t) v * τ.derivToLp t ∂volume.restrict (Ioc a b)) =
      (∫ t, inner ℝ (gLimit t) v * τ.toLp t ∂volume.restrict (Ioc a b)) +
        inner ℝ u₀ v * τ.toFun a := by
  have hleft := (tendsto_timeTest_of_tendsto_weak hu v τ.derivToLp).neg
  have hright := (tendsto_timeTest_of_tendsto_weak hg v τ.toLp).add_const
    (inner ℝ u₀ v * τ.toFun a)
  simp only [LinearEquiv.symm_apply_apply] at hleft hright
  have hright' :
      Tendsto (fun k ↦
        -(∫ t, inner ℝ (u k t) v * τ.derivToLp t ∂volume.restrict (Ioc a b))) l
        (𝓝 ((∫ t, inner ℝ (gLimit t) v * τ.toLp t ∂volume.restrict (Ioc a b)) +
          inner ℝ u₀ v * τ.toFun a)) := by
    simpa only [← heq] using hright
  exact tendsto_nhds_unique hleft hright'

end InitialIdentity

section Trace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (StrongDual ℝ H)] [BorelSpace (StrongDual ℝ H)]
  {a b : ℝ}

/-- The integrated initial identity with an L² velocity produces a
continuous representative and identifies its initial value. The derivative
is the canonical Riesz image of the supplied L² velocity. -/
theorem exists_continuousPivotEvolutionOn_of_integrated_initial_identity
    (hab : a < b) (u g : Lp H 2 (volume.restrict (Ioc a b))) (u₀ : H)
    (heq : ∀ (v : H) (τ : TimeTest a b),
      -(∫ t, inner ℝ (u t) v * τ.derivToLp t ∂volume.restrict (Ioc a b)) =
        (∫ t, inner ℝ (g t) v * τ.toLp t ∂volume.restrict (Ioc a b)) +
          inner ℝ u₀ v * τ.toFun a) :
    ∃ E : ContinuousPivotEvolutionOn (GelfandTriple.identity H) (fun t ↦ u t)
        (fun t ↦ (GelfandTriple.identity H).pivotToDual.compLpL
          2 (volume.restrict (Ioc a b)) g t) a b,
      HasGelfandWeakTimeDerivativeOn (GelfandTriple.identity H) u
        ((GelfandTriple.identity H).pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) g) ∧
      E.representative a = u₀ := by
  let T := GelfandTriple.identity H
  let ell := T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) g
  have hell :
      (ell : ℝ → StrongDual ℝ H) =ᵐ[volume.restrict (Ioc a b)]
        fun t ↦ T.pivotToDual (g t) :=
    T.pivotToDual.coeFn_compLpL g
  have hsol : IsGelfandIntegratedWeakSolution T (fun _ ↦ 0) (fun t ↦ ell t) u u₀ := by
    refine ⟨hab, ?_, ?_, ?_⟩
    · intro v τ
      simp only [zero_apply, zero_mul]
      exact integrable_zero _ _ _
    · intro v τ
      exact integrable_dualTimeTest v τ.toLp ell
    · intro v τ
      have hforce :
          (∫ t, ell t v * τ.toLp t ∂volume.restrict (Ioc a b)) =
            ∫ t, inner ℝ (g t) v * τ.toLp t ∂volume.restrict (Ioc a b) := by
        apply integral_congr_ae
        filter_upwards [hell] with t ht
        simp only [ht, GelfandTriple.pivotToDual_apply,
          T, GelfandTriple.identity_inclusion_apply]
      simpa only [zero_apply, zero_mul, integral_zero, add_zero,
        T, GelfandTriple.identity_inclusion_apply, hforce] using heq v τ
  obtain ⟨ell', E, hweak, hinit, hae⟩ :=
    hsol.exists_continuousPivotEvolutionOn_initial_L2
      (B := fun _ : ℝ ↦ (0 : H →L[ℝ] StrongDual ℝ H))
      (fun _ ↦ aestronglyMeasurable_const) 0
      (Filter.Eventually.of_forall fun _ ↦
        le_of_eq (ContinuousLinearMap.opNorm_zero (E := H) (F := StrongDual ℝ H)
          (σ₁₂ := RingHom.id ℝ))) hab
  have hell' : ell' = ell := by
    apply Lp.ext
    filter_upwards [hae] with t ht
    simpa only [zero_apply, sub_zero] using ht
  subst ell'
  exact ⟨E, hweak, hinit⟩

/-- A projected weak energy-space limit has the correct strong L² initial trace
when its approximations are absolutely continuous trajectories with
weakly convergent L² velocities. -/
theorem exists_continuousPivotEvolutionOn_of_weak_projected_trajectories
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (hab : a < b) (P : V →L[ℝ] H)
    (u : ι → Lp V 2 (volume.restrict (Ioc a b)))
    (g : ι → Lp H 2 (volume.restrict (Ioc a b)))
    (uLimit : Lp V 2 (volume.restrict (Ioc a b)))
    (gLimit : Lp H 2 (volume.restrict (Ioc a b))) (u₀ : H)
    (hu : Tendsto (fun k ↦ toWeakSpace ℝ _ (u k)) l
      (𝓝 (toWeakSpace ℝ _ uLimit)))
    (hg : Tendsto (fun k ↦ toWeakSpace ℝ _ (g k)) l
      (𝓝 (toWeakSpace ℝ _ gLimit)))
    (z : ι → ℝ → H)
    (hz : ∀ k, AbsolutelyContinuousOnInterval (z k) a b)
    (hzu : ∀ k, z k =ᵐ[volume.restrict (Ioc a b)]
      (P.compLpL 2 (volume.restrict (Ioc a b)) (u k) : ℝ → H))
    (hderiv : ∀ k, ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt (z k) (g k t) t)
    (hinit : ∀ k, z k a = u₀) :
    ∃ E : ContinuousPivotEvolutionOn (GelfandTriple.identity H)
        (fun t ↦ P.compLpL 2 (volume.restrict (Ioc a b)) uLimit t)
        (fun t ↦ (GelfandTriple.identity H).pivotToDual.compLpL
          2 (volume.restrict (Ioc a b)) gLimit t) a b,
      HasGelfandWeakTimeDerivativeOn (GelfandTriple.identity H)
        (P.compLpL 2 (volume.restrict (Ioc a b)) uLimit)
        ((GelfandTriple.identity H).pivotToDual.compLpL
          2 (volume.restrict (Ioc a b)) gLimit) ∧
      E.representative a = u₀ := by
  have hPweak :
      Tendsto (fun k ↦ toWeakSpace ℝ _
        (P.compLpL 2 (volume.restrict (Ioc a b)) (u k))) l
        (𝓝 (toWeakSpace ℝ _ (P.compLpL 2 (volume.restrict (Ioc a b)) uLimit))) :=
    (WeakSpace.map (P.compLpL 2 (volume.restrict (Ioc a b)))).continuous.continuousAt.tendsto.comp
      hu
  apply exists_continuousPivotEvolutionOn_of_integrated_initial_identity hab _ gLimit u₀
  apply integrated_initial_identity_of_weak_state_velocity_limits u₀ hPweak hg
  intro k v τ
  exact integrated_initial_identity_of_absolutelyContinuous hab.le (z k) _ (g k) u₀
    (hz k) (hzu k) (hderiv k) (hinit k) v τ

end Trace

end PDE.Analysis.Evolution
