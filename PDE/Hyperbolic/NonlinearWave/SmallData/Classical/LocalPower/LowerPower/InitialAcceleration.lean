/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import
  PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.InitialTrace
public import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import CAS.ExactTactic

/-!
# The ordinary initial acceleration of the integral solution

The first derivative of `t² a(t)` is differentiable at zero when `a` is
merely C¹ there. Thus the regular normalized remainder determines the
initial acceleration without a C² neighborhood. For a reaction fixing
zero and zero displacement, this acceleration is zero.
-/

@[expose] public noncomputable section

open Set Filter Asymptotics MeasureTheory BoundedContinuousFunction PDE.Analysis
open scoped Topology unitInterval

namespace WaveEquation.SmallData.Classical.LocalPower.LowerPower

/-- Multiplication by time differentiates a coefficient continuous at zero.
No derivative of the coefficient is required. -/
theorem hasDerivAt_time_mul_of_continuousAt {g : ℝ → ℝ} (hg : ContinuousAt g 0) :
    HasDerivAt (fun t ↦ t * g t) (g 0) 0 := by
  have hsmall : (fun t ↦ g t - g 0) =o[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    (isLittleO_one_iff _).mpr (by
      simpa only [sub_self] using Filter.Tendsto.sub hg
        (show Tendsto (fun _ : ℝ ↦ g 0) (𝓝 0) (𝓝 (g 0)) from tendsto_const_nhds))
  have hprod := (isBigO_refl (fun t : ℝ ↦ t) (𝓝 0)).mul_isLittleO hsmall
  apply HasDerivAt.of_isLittleO
  simpa only [zero_mul, sub_zero, smul_eq_mul, ← mul_sub, mul_one] using hprod

/-- A second time derivative at zero needs only C¹ coefficients in the
normalized Kirchhoff expression. -/
theorem hasDerivAt_deriv_time_remainder {a b : ℝ → ℝ}
    (ha : ContDiffAt ℝ 1 a 0) (hb : ContDiffAt ℝ 1 b 0) :
    HasDerivAt (deriv (fun t ↦ t * b t + t ^ 2 * a t)) (2 * deriv b 0 + 2 * a 0) 0 := by
  have hda : ContinuousAt (deriv a) 0 :=
    (ha.derivWithin (m := 0) (by simp)).continuousAt
  have hdb : ContinuousAt (deriv b) 0 :=
    (hb.derivWithin (m := 0) (by simp)).continuousAt
  have hd₁ := (hb.differentiableAt one_ne_zero).hasDerivAt.fun_add
    (hasDerivAt_time_mul_of_continuousAt hdb)
  have hd₂ := (hasDerivAt_time_mul_of_continuousAt ha.continuousAt).const_mul 2
  have hd₃ : HasDerivAt (fun t ↦ t ^ 2 * deriv a t) 0 0 := by
    simpa only [Pi.mul_apply, id_eq, zero_mul, pow_two, mul_assoc] using
      hasDerivAt_time_mul_of_continuousAt (continuousAt_id.mul hda)
  have hd : HasDerivAt (fun t ↦ b t + t * deriv b t + (2 * (t * a t) + t ^ 2 * deriv a t))
      (2 * deriv b 0 + 2 * a 0) 0 := by
    convert hd₁.fun_add (hd₂.fun_add hd₃) using 1
    cas
  apply hd.congr_of_eventuallyEq
  filter_upwards [ha.eventually (by simp), hb.eventually (by simp)] with t hat hbt
  have ht := ((hasDerivAt_id t).fun_mul (hbt.differentiableAt one_ne_zero).hasDerivAt).fun_add
    (((hasDerivAt_id t).fun_pow 2).fun_mul (hat.differentiableAt one_ne_zero).hasDerivAt)
  simp only [id_eq] at ht
  rw [ht.deriv]
  cas

/-- The normalized C¹ remainder gives zero ordinary initial acceleration
when it vanishes initially. This is a statement at the initial slice,
not a C² regularity assertion on an open strip. -/
theorem initial_acceleration_of_remainder {h : ℝ^3 → ℝ} (hh : ContDiff ℝ 1 h) {T : ℝ} (hT : 0 < T)
    {v a : ℝ × ℝ^3 → ℝ} (ha : ContDiffOn ℝ 1 a {p | |p.1| < T}) (ha₀ : ∀ x, a (0, x) = 0)
    (heq : ∀ p : ℝ × ℝ^3, |p.1| < T → v p = p.1 * unitSphereAverage 3 h p.2 p.1 + p.1 ^ 2 * a p) :
    ∀ x, HasDerivAt (deriv (fun t ↦ v (t, x))) 0 0 := by
  intro x
  have hnear : {p : ℝ × ℝ^3 | |p.1| < T} ∈ 𝓝 (0, x) :=
    (isOpen_lt continuous_fst.abs continuous_const).mem_nhds (by simpa using hT)
  have hac : ContDiffAt ℝ 1 (fun t : ℝ ↦ a (t, x)) 0 :=
    (ha.contDiffAt hnear).comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  have hbc : ContDiffAt ℝ 1 (unitSphereAverage 3 h x) 0 :=
    ((contDiff_unitSphereAverage hh).comp (contDiff_const.prodMk contDiff_id)).contDiffAt
  have hd := hasDerivAt_deriv_time_remainder hac hbc
  rw [deriv_unitSphereAverage_zero h x hh, ha₀ x] at hd
  have he : (fun t ↦ v (t, x)) =ᶠ[𝓝 0]
      (fun t ↦ t * unitSphereAverage 3 h x t + t ^ 2 * a (t, x)) := by
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.eventually hnear] with t ht
    exact heq (t, x) ht
  simpa only [mul_zero, add_zero] using hd.congr_of_eventuallyEq he.deriv

/-- For every `p > 1`, compactly supported C¹ velocity constructs a C¹
Kirchhoff integral solution whose ordinary initial displacement, velocity,
and acceleration are respectively zero, the datum, and zero. -/
theorem exists_mild_abs_rpow_three_with_initial_acceleration {p : ℝ} (hp : 1 < p)
    {h : ℝ^3 → ℝ} (hh : ContDiff ℝ 1 h) (hhc : HasCompactSupport h) :
    ∃ T : ℝ, 0 < T ∧ ∃ v : ℝ × ℝ^3 → ℝ,
      ContDiffOn ℝ 1 v {q | |q.1| < T} ∧
      (∀ q : ℝ × ℝ^3, |q.1| < T →
        v q = q.1 * unitSphereAverage 3 h q.2 q.1 +
          q.1 ^ 2 * ∫ s : I, (1 - (s : ℝ)) *
            ((∫ ω : Direction,
              |v (q.1 * (s : ℝ), q.2 + q.1 • ((1 - (s : ℝ)) • (ω : ℝ^3)))| ^ p
                ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3)) ∧
      (∀ x, v (0, x) = 0) ∧
      (∀ x, HasDerivAt (fun t ↦ v (t, x)) (h x) 0) ∧
      ∀ x, HasDerivAt (deriv (fun t ↦ v (t, x))) 0 0 := by
  have hf : ContDiff ℝ 1 (fun x : ℝ ↦ |x| ^ p) := by
    simpa only [Real.norm_eq_abs] using (contDiff_norm_rpow hp : ContDiff ℝ 1 (fun x : ℝ ↦ ‖x‖ ^ p))
  obtain ⟨T, hT, v, a, hv, ha, heq, hint⟩ := exists_cone_solution_with_remainder (k := 0) hf
      (ofCompactSupport h hh.continuous hhc) hh
  obtain ⟨hzero, htrace⟩ := cauchy_traces_of_remainder hh hT ha heq
  have ha₀ : ∀ x, a (0, x) = 0 := remainder_initial_zero (f := fun x : ℝ ↦ |x| ^ p)
      (by simp [Real.zero_rpow (by linarith : p ≠ 0)]) hT hzero hint
  refine ⟨T, hT, v, hv, ?_, hzero, htrace, initial_acceleration_of_remainder hh hT ha ha₀ heq⟩
  intro q hq
  rw [heq q hq, hint q hq]
  rfl

end WaveEquation.SmallData.Classical.LocalPower.LowerPower
