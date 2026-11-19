/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Primitive.CompactConvergence
public import PDE.Analysis.MeasureTheory.Lp.MultiplierPairing
public import PDE.Analysis.Evolution.Compactness.Lp.Basic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Passing a transport equation through weak L² convergence

The transport factor may converge only weakly in L². Its coefficient contains
the normalized primitive of a strongly convergent L² field. On the support of
a smooth test function, that primitive converges strongly in L², so the
transport pairing passes to the limit. The quadratic source term uses strong
convergence in both factors.

The result is an almost-everywhere stationary equation for arbitrary L² classes
`F`, `G`, `H`. The derivative and Hilbert relations between them come from the
Sobolev limit theorems in `PDE.Fluid.DeGregorio.DynamicRescaling.Limit`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace PDE.Analysis.Evolution

private theorem integral_test_transport_residual
    (f h g w : Lp ℝ 2 (volume : Measure ℝ)) (cl cw a : ℝ)
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    (∫ x, φ x * (w x + (cl * x + a * l2Primitive h x) * g x -
      (cw + h x) * f x)) =
      (∫ x, φ x * w x) + cl * (∫ x, (x * φ x) * g x) +
        a * (∫ x, (l2Primitive h x * φ x) * g x) -
          (cw * (∫ x, φ x * f x) + ∫ x, φ x * h x * f x) := by
  have hφ2 : MemLp φ 2 volume := hφ.memLp_of_hasCompactSupport hcφ
  have hφTop : MemLp φ ∞ volume := hφ.memLp_of_hasCompactSupport hcφ
  have hxφ : MemLp (fun x ↦ x * φ x) 2 volume :=
    (continuous_id.mul hφ).memLp_of_hasCompactSupport hcφ.mul_left
  have hw : Integrable (fun x ↦ φ x * w x) volume := by
    simpa only [Pi.mul_def] using hφ2.integrable_mul (Lp.memLp w)
  have hg : Integrable (fun x ↦ cl * ((x * φ x) * g x)) volume := by
    simpa only [Pi.mul_apply] using (hxφ.integrable_mul (Lp.memLp g)).const_mul cl
  have hpg : Integrable (fun x ↦ a * ((l2Primitive h x * φ x) * g x)) volume := by
    simpa only [Pi.mul_apply] using
      ((memLp_l2Primitive_mul h hφ hcφ).integrable_mul (Lp.memLp g)).const_mul a
  have hf : Integrable (fun x ↦ cw * (φ x * f x)) volume := by
    simpa only [Pi.mul_apply] using (hφ2.integrable_mul (Lp.memLp f)).const_mul cw
  have hh : Integrable (fun x ↦ φ x * h x * f x) volume :=
    (hφTop.mul (Lp.memLp h) : MemLp (fun x ↦ φ x * h x) 2 volume).integrable_mul
      (Lp.memLp f)
  calc
    _ = ∫ x, (φ x * w x + cl * ((x * φ x) * g x) +
        a * ((l2Primitive h x * φ x) * g x)) -
          (cw * (φ x * f x) + φ x * h x * f x) := by
      exact integral_congr_ae (.of_forall fun x ↦ by ring)
    _ = _ := by
      rw [integral_sub ((hw.fun_add hg).fun_add hpg) (hf.fun_add hh),
        integral_add (hw.fun_add hg) hpg, integral_add hw hg, integral_add hf hh,
        integral_const_mul, integral_const_mul, integral_const_mul]

/-- Strong L² limits of the base, primitive integrand, and vanishing time
term, together with a uniformly bounded weak L² limit of the transport
factor, satisfy the stationary equation almost everywhere.

The spatial and amplitude rates may have different limits, and the
transport parameter `a` is arbitrary. Local integrability of the limiting
equation follows from these hypotheses. -/
theorem ae_stationary_transport_of_strong_weak_L2_limits
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {f h w g : ι → Lp ℝ 2 (volume : Measure ℝ)}
    {F H G : Lp ℝ 2 (volume : Measure ℝ)}
    {cl cw : ι → ℝ} {CL CW a R : ℝ}
    (hf : Tendsto f l (𝓝 F))
    (hh : Tendsto h l (𝓝 H))
    (hw : Tendsto w l (𝓝 0))
    (hg : Tendsto (fun i ↦ toWeakSpace ℝ (Lp ℝ 2 volume) (g i)) l
      (𝓝 (toWeakSpace ℝ (Lp ℝ 2 volume) G)))
    (hbound : ∀ i, ‖g i‖ ≤ R)
    (hcl : Tendsto cl l (𝓝 CL))
    (hcw : Tendsto cw l (𝓝 CW))
    (heq : ∀ i, ∀ᵐ x ∂volume,
      w i x + (cl i * x + a * l2Primitive (h i) x) * g i x =
        (cw i + h i x) * f i x) :
    ∀ᵐ x ∂volume,
      (CL * x + a * l2Primitive H x) * G x = (CW + H x) * F x := by
  have htransport : LocallyIntegrable
      (fun x ↦ (CL * x + a * l2Primitive H x) * G x) volume :=
    LocallyIntegrable.continuous_mul
      ((continuous_const.mul continuous_id).add
        (continuous_const.mul (continuous_l2Primitive H)))
      ((Lp.memLp G).locallyIntegrable (by norm_num))
  have hsource : LocallyIntegrable (fun x ↦ (CW + H x) * F x) volume := by
    have hlinear := LocallyIntegrable.continuous_mul (continuous_const (y := CW))
      ((Lp.memLp F).locallyIntegrable (by norm_num))
    have hquadratic := ((Lp.memLp H).integrable_mul (Lp.memLp F)).locallyIntegrable
    simpa only [Pi.add_def, Pi.mul_def, add_mul] using hlinear.add hquadratic
  have hzero : ∀ᵐ x ∂volume,
      (CL * x + a * l2Primitive H x) * G x - (CW + H x) * F x = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero (htransport.sub hsource)
    intro φ hφ hcφ
    have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hcφ
    have hφTop : MemLp φ ∞ volume := hφ.continuous.memLp_of_hasCompactSupport hcφ
    have hxφ2 : MemLp (fun x ↦ x * φ x) 2 volume :=
      (continuous_id.mul hφ.continuous).memLp_of_hasCompactSupport hcφ.mul_left
    have hinner (ψ : ℝ → ℝ) (hψ : MemLp ψ 2 volume) (v : Lp ℝ 2 volume) :
        inner ℝ (hψ.toLp ψ) v = ∫ x, ψ x * v x := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hψ.coeFn_toLp] with x hx
      simp only [RCLike.inner_apply, conj_trivial, hx]
      ring
    have htime : Tendsto (fun i ↦ ∫ x, φ x * w i x) l (𝓝 0) := by
      have ht := (tendsto_const_nhds (x := hφ2.toLp φ)).inner (𝕜 := ℝ) hw
      rw [inner_zero_right] at ht
      simpa only [hinner] using ht
    have hlinear : Tendsto (fun i ↦ ∫ x, (x * φ x) * g i x) l (𝓝 (∫ x, (x * φ x) * G x)) := by
      simpa only [hinner] using tendsto_inner_of_tendsto_weak_of_tendsto_strong hg
        (tendsto_const_nhds (x := hxφ2.toLp (fun x ↦ x * φ x))) R hbound
    have hprimitive : Tendsto (fun i ↦ ∫ x, (l2Primitive (h i) x * φ x) * g i x) l
        (𝓝 (∫ x, (l2Primitive H x * φ x) * G x)) := by
      simpa only [hinner] using tendsto_inner_of_tendsto_weak_of_tendsto_strong hg
        (tendsto_toLp_l2Primitive_mul hh hφ.continuous hcφ) R hbound
    have hbase : Tendsto (fun i ↦ ∫ x, φ x * f i x) l (𝓝 (∫ x, φ x * F x)) := by
      simpa only [hinner] using (tendsto_const_nhds (x := hφ2.toLp φ)).inner (𝕜 := ℝ) hf
    have hquadratic := tendsto_integral_weighted_mul_of_tendsto_L2 hφTop hh hf
    have hlimit := ((htime.add (hcl.mul hlinear)).add
      (hprimitive.const_mul a)).sub ((hcw.mul hbase).add hquadratic)
    have heqTest (i : ι) :
        (∫ x, φ x * w i x) + cl i * (∫ x, (x * φ x) * g i x) +
          a * (∫ x, (l2Primitive (h i) x * φ x) * g i x) -
            (cw i * (∫ x, φ x * f i x) + ∫ x, φ x * h i x * f i x) = 0 := by
      rw [← integral_test_transport_residual (f i) (h i) (g i) (w i) (cl i) (cw i) a
        hφ.continuous hcφ]
      exact integral_eq_zero_of_ae ((heq i).mono fun x hx ↦ by
        simp only [hx, sub_self, mul_zero, Pi.zero_apply])
    have htest :
        CL * (∫ x, (x * φ x) * G x) +
          a * (∫ x, (l2Primitive H x * φ x) * G x) -
            (CW * (∫ x, φ x * F x) + ∫ x, φ x * H x * F x) = 0 := by
      simpa only [zero_add] using
        tendsto_nhds_unique hlimit (tendsto_const_nhds.congr fun i ↦ (heqTest i).symm)
    calc
      _ = ∫ x, φ x * ((0 : Lp ℝ 2 volume) x +
          (CL * x + a * l2Primitive H x) * G x - (CW + H x) * F x) := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := (volume : Measure ℝ))]
          with x hx
        simp only [Pi.sub_apply, smul_eq_mul, hx, Pi.zero_apply, zero_add]
      _ = _ := integral_test_transport_residual F H G 0 CL CW a hφ.continuous hcφ
      _ = 0 := by
        rw [← hinner φ hφ2 0, inner_zero_right, zero_add]
        exact htest
  exact hzero.mono fun x hx ↦ sub_eq_zero.mp hx

end PDE.Analysis.Evolution
