/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.LipschitzEnergy
public import PDE.Analysis.Calculus.StrongOperator

/-!
# The displacement-velocity identity for energy waves

Differentiating the pairing of velocity and displacement uses the displacement derivative in L² and
the velocity derivative in H⁻¹. The operator-action product rule only differentiates the velocity
against a fixed H¹ test. Integration yields control of the nonnegative reaction density u f(u) on
finite time intervals. This is the identity of step 3 of the proof of Theorem 1 of Evans, §12.3.1,
obtained there by multiplying (4) by `uᵏ` and integrating, and the resulting bound (8).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.1, step 3 of the proof of Theorem 1, equation (8).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert InnerProductSpace Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

open PDE.Analysis.Evolution

variable {n : ℕ} {N : General.Nonlinearity n}
  {x : H¹(ℝ^n) × DerivLp n 2 univ}
  {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}

/-- Differentiate the mixed L² pairing directly from the two integrated PDE
identities. Only a fixed H¹ test is applied to the dual-valued acceleration. -/
theorem hasDerivWithinAt_velocity_displacement (hu : N.IsEnergySolution x u) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s ↦ ⟪(u s).2, (energyTriple n).inclusion (u s).1⟫_ℝ)
      (‖(u t).2‖ ^ 2 - gradientForm n (u t).1 (u t).1 -
        ⟪N.source (u t).1, (energyTriple n).inclusion (u t).1⟫_ℝ) (Ici 0) t := by
  have hfixed : HasDerivWithinAt (fun s ↦ ⟪(u s).2, (energyTriple n).inclusion (u t).1⟫_ℝ)
      (N.acceleration (u t).1 (u t).1) (Ici 0) t := by
    simpa! only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      GelfandTriple.pivotToDual_apply] using
      (ContinuousLinearMap.apply ℝ ℝ (u t).1).hasFDerivAt.comp_hasDerivWithinAt t
        (hu.hasDerivWithinAt_velocity ht)
  have hA : ContinuousAt (fun p : ℝ × DerivLp n 2 univ ↦ ⟪(u p.1).2, p.2⟫_ℝ) (t, (u t).2) :=
    ((u.continuous.snd.comp continuous_fst).inner continuous_snd).continuousAt
  have hd := PDE.Analysis.hasDerivWithinAt_clm_apply_of_continuousAt
    (A := fun s ↦ innerSL ℝ (u s).2) hA hfixed (hu.hasDerivWithinAt_displacement ht)
  convert! hd using 1
  change ‖(u t).2‖ ^ 2 - gradientForm n (u t).1 (u t).1 -
    ⟪N.source (u t).1, (energyTriple n).inclusion (u t).1⟫_ℝ =
      -⟪N.source (u t).1, (energyTriple n).inclusion (u t).1⟫_ℝ -
        gradientForm n (u t).1 (u t).1 + ⟪(u t).2, (u t).2⟫_ℝ
  rw [real_inner_self_eq_norm_sq]
  ring

/-- Testing the wave equation with its own displacement gives the exact integrated
reaction pairing, for energy data and every finite forward interval. -/
theorem integral_source_pairing (hu : N.IsEnergySolution x u) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ⟪N.source (u t).1, (energyTriple n).inclusion (u t).1⟫_ℝ) =
      ⟪x.2, (energyTriple n).inclusion x.1⟫_ℝ -
        ⟪(u T).2, (energyTriple n).inclusion (u T).1⟫_ℝ +
        ∫ t in (0 : ℝ)..T, ‖(u t).2‖ ^ 2 - gradientForm n (u t).1 (u t).1 := by
  have hp : Continuous (fun t ↦ ⟪(u t).2, (energyTriple n).inclusion (u t).1⟫_ℝ) := by
    fun_prop
  have hq : Continuous
      (fun t ↦ ‖(u t).2‖ ^ 2 - gradientForm n (u t).1 (u t).1) := by fun_prop
  have hr : Continuous
      (fun t ↦ ⟪N.source (u t).1, (energyTriple n).inclusion (u t).1⟫_ℝ) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hp.continuousOn
    (fun t ht ↦ (hasDerivWithinAt_velocity_displacement hu ht.1.le).hasDerivAt
      (Ici_mem_nhds ht.1)) ((hq.sub hr).intervalIntegrable 0 T)
  rw [intervalIntegral.integral_sub (hq.intervalIntegrable 0 T)
    (hr.intervalIntegrable 0 T), hu.initial] at h
  linarith

/-- Uniform velocity and L² displacement bounds control the integrated source
pairing. The estimate requires no norm bound for the source itself. -/
theorem integral_source_pairing_le (hu : N.IsEnergySolution x u) {T A C : ℝ} (hT : 0 ≤ T)
    (hv : ∀ t ∈ Icc 0 T, ‖(u t).2‖ ≤ C)
    (hq : ∀ t ∈ Icc 0 T, ‖(energyTriple n).inclusion (u t).1‖ ≤ A) :
    (∫ t in (0 : ℝ)..T, ⟪N.source (u t).1, (energyTriple n).inclusion (u t).1⟫_ℝ) ≤
      2 * C * A + T * C ^ 2 := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hv 0 ⟨le_rfl, hT⟩)
  have hp (t : ℝ) (ht : t ∈ Icc 0 T) :
      |⟪(u t).2, (energyTriple n).inclusion (u t).1⟫_ℝ| ≤ C * A :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hv t ht) (hq t ht) (norm_nonneg _) hC)
  have h0 := hp 0 ⟨le_rfl, hT⟩
  rw [hu.initial] at h0
  have h1 := hp T ⟨hT, le_rfl⟩
  have hi : Continuous
      (fun t ↦ ‖(u t).2‖ ^ 2 - gradientForm n (u t).1 (u t).1) := by fun_prop
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖(u t).2‖ ^ 2 - gradientForm n (u t).1 (u t).1 ≤ C ^ 2 := by
    have hn := pow_le_pow_left₀ (norm_nonneg _) (hv t ht) 2
    have hg := General.Nonlinearity.gradientForm_nonneg (u t).1
    linarith
  have hint := intervalIntegral.integral_mono_on hT (hi.intervalIntegrable 0 T)
    (intervalIntegrable_const (μ := volume) (c := C ^ 2)) hbound
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hint
  rw [integral_source_pairing hu hT]
  have hl := (abs_le.mp h0).2
  have hr := (abs_le.mp h1).1
  nlinarith

/-- The Lipschitz source pairing is the integral of the reaction density. -/
theorem inner_reaction_self {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hf0 : f 0 = 0) (q : H¹(ℝ^n)) :
    ⟪hf.compLp hf0 ((energyTriple n).inclusion q), (energyTriple n).inclusion q⟫_ℝ =
      ∫ y, (energyTriple n).inclusion q y * f ((energyTriple n).inclusion q y)
        ∂domainMeasure n univ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_compLp hf0 ((energyTriple n).inclusion q)] with y hy
  simp only [hy, Function.comp_apply, Real.inner_apply]
  exact mul_comm _ _

/-- The reaction product is integrable at every time of a Lipschitz energy wave. -/
theorem integrable_reaction_self {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hf0 : f 0 = 0) (q : H¹(ℝ^n)) :
    Integrable (fun y ↦ (energyTriple n).inclusion q y *
      f ((energyTriple n).inclusion q y)) (domainMeasure n univ) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.compLp hf0 ((energyTriple n).inclusion q))
    ((energyTriple n).inclusion q)).congr
  filter_upwards [hf.coeFn_compLp hf0 ((energyTriple n).inclusion q)] with y hy
  simp only [hy, Function.comp_apply, Real.inner_apply]
  exact mul_comm _ _

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
