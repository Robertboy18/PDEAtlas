/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.VelocityLimit
import PDE.Analysis.MeasureTheory.StronglyMeasurable.Weak

/-!
# The displacement equation for the limiting velocity

The weakly continuous, bounded L² velocity is Bochner integrable on every
finite interval. Uniform scalar convergence passes the integrated displacement
equation to the limit, identifying this velocity as the L² time derivative.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution
open scoped ENNReal Topology InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- A bounded weakly continuous separable-space curve is Bochner integrable
on each finite interval of the half-line. -/
theorem intervalIntegrable_IciExtend_of_weakly_continuous {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [TopologicalSpace.SeparableSpace H] {v : Ici (0 : ℝ) → H} {M : ℝ}
    (hv : Continuous (fun t ↦ toWeakSpace ℝ H (v t))) (hb : ∀ t, ‖v t‖ ≤ M) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (IciExtend v) volume 0 T := by
  have hp : Continuous (projIci (0 : ℝ)) := (continuous_const.max continuous_id).subtype_mk _
  have hvm : AEStronglyMeasurable (IciExtend v) (volume.restrict (Ioc 0 T)) :=
    aestronglyMeasurable_of_continuous_weakSpace (hv.comp hp) _
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
  exact (integrable_const M).mono' hvm (Eventually.of_forall fun t ↦ hb (projIci 0 t))

/-- Weak convergence of both trajectories passes the integrated
identity uₜ = v to their limits. The limit velocity is integrated in L². -/
theorem displacement_integral_eq_of_weak_limits {n : ℕ} {g : ℕ → ℝ → ℝ} {K : ℕ → NNReal}
    {hg : ∀ i, LipschitzWith (K i) (g i)} {hg0 : ∀ i, g i 0 = 0} {x : H¹(ℝ^n) × DerivLp n 2 univ}
    {u : ℕ → C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (hu : ∀ i, Cauchy.IsEnergySolution (hg i) (hg0 i) x (u i)) {q : ℝ → H¹(ℝ^n)}
    {v : ℝ → DerivLp n 2 univ} {T : ℝ} (hT : 0 ≤ T)
    (hq : ∀ ell : StrongDual ℝ H¹(ℝ^n),
      TendstoUniformlyOn (fun i t ↦ ell (u i t).1) (fun t ↦ ell (q t)) atTop (Icc 0 T))
    (hv : ∀ w : DerivLp n 2 univ, TendstoUniformlyOn (fun i t ↦ inner ℝ w (u i t).2)
      (fun t ↦ inner ℝ w (v t)) atTop (Icc 0 T))
    (hvi : IntervalIntegrable v volume 0 T) :
    (∫ t in (0 : ℝ)..T, v t) =
      (energyTriple n).inclusion (q T) - (energyTriple n).inclusion x.1 := by
  refine ext_inner_left ℝ fun w ↦ ?_
  have hvi' : TendstoUniformlyOn (fun i t ↦ inner ℝ w (u i t).2)
      (fun t ↦ inner ℝ w (v t)) atTop (uIcc 0 T) := by
    simpa only [uIcc_of_le hT] using hv w
  have hint := hvi'.tendsto_intervalIntegral_of_continuousOn (μ := volume)
    (Eventually.of_forall fun i ↦
      (by fun_prop : Continuous (fun t ↦ inner ℝ w (u i t).2)).continuousOn)
  have hqT := (hq ((innerSL ℝ w).comp (energyTriple n).inclusion)).tendsto_at ⟨hT, le_rfl⟩
  have heq (i : ℕ) : (∫ t in (0 : ℝ)..T, inner ℝ w (u i t).2) =
        inner ℝ w ((energyTriple n).inclusion (u i T).1) -
          inner ℝ w ((energyTriple n).inclusion x.1) := by
    have h := congrArg (innerSL ℝ w) ((hu i).displacement T hT)
    rw [← (innerSL ℝ w).intervalIntegral_comp_comm
      ((u i).continuous.snd.intervalIntegrable (μ := volume) 0 T)] at h
    simpa only [innerSL_apply_apply, inner_sub_right] using h
  have hlim := tendsto_nhds_unique (hint.congr (fun i ↦ heq i))
    (hqT.sub_const (inner ℝ w ((energyTriple n).inclusion x.1)))
  rw [inner_sub_right]
  change (innerSL ℝ w) (∫ t in (0 : ℝ)..T, v t) = _
  rw [← (innerSL ℝ w).intervalIntegral_comp_comm hvi]
  exact hlim

/-- The weak velocity limit satisfies the original tested integral equation
whenever the reaction pairings converge in L¹. -/
theorem velocity_pairing_eq_of_weak_limits {n : ℕ} {g : ℕ → ℝ → ℝ} {K : ℕ → NNReal}
    {hg : ∀ i, LipschitzWith (K i) (g i)} {hg0 : ∀ i, g i 0 = 0} {x : H¹(ℝ^n) × DerivLp n 2 univ}
    {u : ℕ → C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (hu : ∀ i, Cauchy.IsEnergySolution (hg i) (hg0 i) x (u i)) {q : ℝ → H¹(ℝ^n)}
    {v : ℝ → DerivLp n 2 univ} {T : ℝ}
    (hq : ∀ ell : StrongDual ℝ H¹(ℝ^n),
      TendstoUniformlyOn (fun i t ↦ ell (u i t).1) (fun t ↦ ell (q t)) atTop (Icc 0 T))
    (hv : ∀ w : DerivLp n 2 univ, TendstoUniformlyOn (fun i t ↦ inner ℝ w (u i t).2)
      (fun t ↦ inner ℝ w (v t)) atTop (Icc 0 T))
    (w : H¹(ℝ^n)) {R : ℝ → ℝ} (hR : Integrable R (volume.restrict (Ioc 0 T)))
    (hreact : Tendsto (fun i ↦ eLpNorm ((fun t ↦ ⟪(hg i).compLp (hg0 i)
      ((energyTriple n).inclusion (u i t).1), (energyTriple n).inclusion w⟫_ℝ) - R) 1
      (volume.restrict (Ioc 0 T))) atTop (𝓝 0))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ⟪v t, (energyTriple n).inclusion w⟫_ℝ = ⟪x.2, (energyTriple n).inclusion w⟫_ℝ -
      (∫ s in (0 : ℝ)..t, gradientForm n (q s) w) - ∫ s in (0 : ℝ)..t, R s := by
  have hpair := (tendstoUniformlyOn_velocity_pairing hu hq w hR hreact).tendsto_at ht
  have hv' := ((hv ((energyTriple n).inclusion w)).tendsto_at ht).congr
    (fun i ↦ (real_inner_comm ((energyTriple n).inclusion w) (u i t).2).symm)
  exact (real_inner_comm ((energyTriple n).inclusion w) (v t)).trans (tendsto_nhds_unique hv' hpair)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
