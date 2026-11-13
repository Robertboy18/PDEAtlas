/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.IntegralKernel
public import PDE.Analysis.Operator.Schur
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Integral kernels as operators on L² classes

Square integrability of the kernel, or Schur's row and column bounds, produces
a continuous linear map between L² spaces. Both constructions have the totalized
Bochner integral as an almost-everywhere representative. They agree whenever
both estimates apply.

The real and `RCLike` scalar structures must be compatible for linearity.
Both constructions allow incomplete targets, where mathlib defines the Bochner
integral to be zero, so both operators are zero. For complete targets, the proved
row integrability gives the usual Bochner integral operators on L² classes.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {X Y 𝕜 E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    [IsScalarTower ℝ 𝕜 E]

private noncomputable def integralKernelLinearMap (K : X × Y → 𝕜)
    (hrows : ∀ f : Lp E 2 ν, ∀ᵐ x ∂μ, Integrable (fun y ↦ K (x, y) • f y) ν)
    (hout : ∀ f : Lp E 2 ν, MemLp (fun x ↦ ∫ y, K (x, y) • f y ∂ν) 2 μ) :
    Lp E 2 ν →ₗ[𝕜] Lp E 2 μ where
  toFun f := (hout f).toLp (fun x ↦ ∫ y, K (x, y) • f y ∂ν)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (hout (f + g)),
      Lp.coeFn_add ((hout f).toLp _) ((hout g).toLp _),
      MemLp.coeFn_toLp (hout f), MemLp.coeFn_toLp (hout g),
      hrows f, hrows g] with x hsum hadd hf hg hif hig
    simp only [Pi.add_apply] at hadd
    rw [hsum, hadd, hf, hg]
    calc
      (∫ y, K (x, y) • (f + g) y ∂ν) =
          ∫ y, K (x, y) • f y + K (x, y) • g y ∂ν := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f g] with y hy
        change (f + g) y = f y + g y at hy
        rw [hy, smul_add]
      _ = _ := integral_add hif hig
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (hout (c • f)),
      Lp.coeFn_smul c ((hout f).toLp _), MemLp.coeFn_toLp (hout f)] with x hcf hc hf
    simp only [Pi.smul_apply] at hc
    simp only [RingHom.id_apply]
    rw [hcf, hc, hf]
    calc
      (∫ y, K (x, y) • (c • f) y ∂ν) =
          ∫ y, c • (K (x, y) • f y) ∂ν := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with y hy
        change (c • f) y = c • f y at hy
        rw [hy, smul_comm]
      _ = _ := integral_smul c _

omit [SFinite μ] [SFinite ν] in
private theorem norm_integralKernelLinearMap_le
    (K : X × Y → 𝕜)
    (hrows : ∀ f : Lp E 2 ν, ∀ᵐ x ∂μ, Integrable (fun y ↦ K (x, y) • f y) ν)
    (hout : ∀ f : Lp E 2 ν, MemLp (fun x ↦ ∫ y, K (x, y) • f y ∂ν) 2 μ)
    (C : ℝ)
    (hbound : ∀ f : Lp E 2 ν,
      lpNorm (fun x ↦ ∫ y, K (x, y) • f y ∂ν) 2 μ ≤ C * lpNorm f 2 ν)
    (f : Lp E 2 ν) :
    ‖integralKernelLinearMap K hrows hout f‖ ≤ C * ‖f‖ := by
  change ‖(hout f).toLp _‖ ≤ _
  rw [Lp.norm_toLp, toReal_eLpNorm, Lp.norm_def, toReal_eLpNorm]
  exact hbound f

omit [IsScalarTower ℝ 𝕜 E] in
private theorem lpNorm_integral_kernel_smul_le_of_memLp
    {K : X × Y → 𝕜} (hK : MemLp K 2 (μ.prod ν)) (f : Lp E 2 ν) :
    lpNorm (fun x ↦ ∫ y, K (x, y) • f y ∂ν) 2 μ ≤
      lpNorm K 2 (μ.prod ν) * lpNorm f 2 ν := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hK.eLpNorm_ne_top (Lp.memLp f).eLpNorm_ne_top)
    (eLpNorm_integral_kernel_smul_le hK (Lp.memLp f))
  simpa only [ENNReal.toReal_mul, toReal_eLpNorm] using h

/-- The integral operator defined by a square-integrable kernel, on L² classes.
The norm bound is the L² norm of the kernel on the product measure. For an
incomplete target, Bochner totalization makes this the zero operator. -/
@[no_expose]
noncomputable def integralKernelL2 {K : X × Y → 𝕜} (hK : MemLp K 2 (μ.prod ν)) :
    Lp E 2 ν →L[𝕜] Lp E 2 μ :=
  have hrows : ∀ f : Lp E 2 ν, ∀ᵐ x ∂μ,
      Integrable (fun y ↦ K (x, y) • f y) ν :=
    fun f ↦ hK.ae_integrable_kernel_smul (Lp.memLp f)
  have hout : ∀ f : Lp E 2 ν,
      MemLp (fun x ↦ ∫ y, K (x, y) • f y ∂ν) 2 μ :=
    fun f ↦ hK.integral_kernel_smul (Lp.memLp f)
  let T : Lp E 2 ν →ₗ[𝕜] Lp E 2 μ := integralKernelLinearMap K hrows hout
  have hbound : ∀ f : Lp E 2 ν, ‖T f‖ ≤ lpNorm K 2 (μ.prod ν) * ‖f‖ :=
    norm_integralKernelLinearMap_le K hrows hout (lpNorm K 2 (μ.prod ν))
      (lpNorm_integral_kernel_smul_le_of_memLp hK)
  T.mkContinuous (lpNorm K 2 (μ.prod ν)) hbound

/-- The L²-class operator is represented almost everywhere by the totalized integral.
The kernel and input membership give integrable rows independently of this identity. -/
theorem integralKernelL2_apply_ae {K : X × Y → 𝕜} (hK : MemLp K 2 (μ.prod ν))
    (f : Lp E 2 ν) :
    (integralKernelL2 hK f : X → E) =ᵐ[μ] fun x ↦ ∫ y, K (x, y) • f y ∂ν :=
  MemLp.coeFn_toLp (hK.integral_kernel_smul (Lp.memLp f))

/-- Changing the measurable L² representative of the input leaves the integral
operator unchanged almost everywhere. -/
theorem integralKernelL2_toLp_ae {K : X × Y → 𝕜} (hK : MemLp K 2 (μ.prod ν))
    {f : Y → E} (hf : MemLp f 2 ν) :
    (integralKernelL2 hK (hf.toLp f) : X → E) =ᵐ[μ]
      fun x ↦ ∫ y, K (x, y) • f y ∂ν := by
  refine (integralKernelL2_apply_ae hK (hf.toLp f)).trans ?_
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with y hy
  rw [hy]

/-- The norm of a square-kernel integral operator is at most its product L² norm. -/
theorem norm_integralKernelL2_le {K : X × Y → 𝕜} (hK : MemLp K 2 (μ.prod ν)) :
    ‖integralKernelL2 (E := E) hK‖ ≤ lpNorm K 2 (μ.prod ν) := by
  apply (integralKernelL2 (E := E) hK).opNorm_le_bound lpNorm_nonneg
  intro f
  let u : Lp E 2 μ := integralKernelL2 hK f
  have hu : (u : X → E) =ᵐ[μ] fun x ↦ ∫ y, K (x, y) • f y ∂ν :=
    integralKernelL2_apply_ae hK f
  change ‖u‖ ≤ lpNorm K 2 (μ.prod ν) * ‖f‖
  rw [Lp.norm_def, eLpNorm_congr_ae hu, toReal_eLpNorm, Lp.norm_def, toReal_eLpNorm]
  exact lpNorm_integral_kernel_smul_le_of_memLp hK f

section Schur

variable {K : X × Y → 𝕜} {A B : ℝ}
    (hK : AEStronglyMeasurable K (μ.prod ν)) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrow : ∀ᵐ x ∂μ,
      (∫⁻ y, ENNReal.ofReal ‖K (x, y)‖ ∂ν) ≤ ENNReal.ofReal A)
    (hcolumn : ∀ᵐ y ∂ν,
      (∫⁻ x, ENNReal.ofReal ‖K (x, y)‖ ∂μ) ≤ ENNReal.ofReal B)

/-- Schur's absolute row and column bounds define a continuous linear integral
operator on L² classes, including the cases where either bound is zero. -/
@[no_expose]
noncomputable def integralKernelL2OfSchur : Lp E 2 ν →L[𝕜] Lp E 2 μ :=
  have hrows : ∀ f : Lp E 2 ν, ∀ᵐ x ∂μ,
      Integrable (fun y ↦ K (x, y) • f y) ν :=
    fun f ↦ ae_integrable_kernel_smul_of_schur hK (Lp.memLp f) hA hB hrow hcolumn
  have hout : ∀ f : Lp E 2 ν,
      MemLp (fun x ↦ ∫ y, K (x, y) • f y ∂ν) 2 μ :=
    fun f ↦ MemLp.integral_kernel_smul_of_schur hK (Lp.memLp f) hA hB hrow hcolumn
  let T : Lp E 2 ν →ₗ[𝕜] Lp E 2 μ := integralKernelLinearMap K hrows hout
  have hbound : ∀ f : Lp E 2 ν, ‖T f‖ ≤ √(A * B) * ‖f‖ :=
    norm_integralKernelLinearMap_le K hrows hout (√(A * B))
      (fun f ↦ lpNorm_integral_kernel_smul_le_of_schur
        hK (Lp.memLp f) hA hB hrow hcolumn)
  T.mkContinuous (√(A * B)) hbound

/-- The Schur operator is represented almost everywhere by the totalized integral.
The row and column bounds give integrable rows independently of this identity. -/
theorem integralKernelL2OfSchur_apply_ae (f : Lp E 2 ν) :
    (integralKernelL2OfSchur hK hA hB hrow hcolumn f : X → E) =ᵐ[μ]
      fun x ↦ ∫ y, K (x, y) • f y ∂ν :=
  MemLp.coeFn_toLp
    (MemLp.integral_kernel_smul_of_schur hK (Lp.memLp f) hA hB hrow hcolumn)

/-- Any measurable L² representative of the input gives the same Schur integral. -/
theorem integralKernelL2OfSchur_toLp_ae {f : Y → E} (hf : MemLp f 2 ν) :
    (integralKernelL2OfSchur hK hA hB hrow hcolumn (hf.toLp f) : X → E) =ᵐ[μ]
      fun x ↦ ∫ y, K (x, y) • f y ∂ν := by
  refine (integralKernelL2OfSchur_apply_ae hK hA hB hrow hcolumn (hf.toLp f)).trans ?_
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with y hy
  rw [hy]

/-- Schur's operator norm bound is √(AB), with no strict positivity premise. -/
theorem norm_integralKernelL2OfSchur_le :
    ‖integralKernelL2OfSchur (E := E) hK hA hB hrow hcolumn‖ ≤ √(A * B) := by
  apply (integralKernelL2OfSchur (E := E) hK hA hB hrow hcolumn).opNorm_le_bound
    (Real.sqrt_nonneg _)
  intro f
  let u : Lp E 2 μ := integralKernelL2OfSchur hK hA hB hrow hcolumn f
  have hu : (u : X → E) =ᵐ[μ] fun x ↦ ∫ y, K (x, y) • f y ∂ν :=
    integralKernelL2OfSchur_apply_ae hK hA hB hrow hcolumn f
  change ‖u‖ ≤ √(A * B) * ‖f‖
  rw [Lp.norm_def, eLpNorm_congr_ae hu, toReal_eLpNorm, Lp.norm_def, toReal_eLpNorm]
  exact lpNorm_integral_kernel_smul_le_of_schur hK (Lp.memLp f) hA hB hrow hcolumn

/-- The square-kernel and Schur constructions define the same operator whenever
both hypotheses hold, since their integral representatives agree. -/
theorem integralKernelL2_eq_of_schur (hKtwo : MemLp K 2 (μ.prod ν)) :
    integralKernelL2 (E := E) hKtwo = integralKernelL2OfSchur hK hA hB hrow hcolumn := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  exact (integralKernelL2_apply_ae hKtwo f).trans
    (integralKernelL2OfSchur_apply_ae hK hA hB hrow hcolumn f).symm

end Schur

end MeasureTheory
