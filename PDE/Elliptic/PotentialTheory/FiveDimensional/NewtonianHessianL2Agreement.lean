/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianHessianCompactC1
public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianHessianCutoff
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# The noncompact C¹ Hessian agrees with the bounded L² operator

Expanding compact cutoffs converge in L². Their Hessians converge
pointwise by the centered near and exterior formula, while boundedness gives
L² convergence of the operator outputs. An almost-everywhere subsequence
identifies the two limits.

The source needs C¹ regularity, ambient L² membership, and an absolutely
convergent Newtonian pairing at one anchor. Hessian L² membership
follows from the agreement; no Hessian representation or Hessian norm is
assumed.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Filter
open scoped Topology

namespace PotentialTheory

/-- Expanding bounded cutoffs converge in L² for any measure. The
membership proofs only choose representatives for `toLp`; the convergence
comes from domination by the square of the uncut source. -/
private theorem tendsto_toLp_bump_mul
    {μ : Measure (ℝ^5)} (f : ℝ^5 → ℝ) (hf : MemLp f 2 μ)
    (χ : ℕ → ContDiffBump (0 : ℝ^5))
    (hχ : Tendsto (fun n ↦ (χ n).rIn) atTop atTop)
    (hF : ∀ n, MemLp (fun Y ↦ χ n Y * f Y) 2 μ) :
    Tendsto (fun n ↦ (hF n).toLp (fun Y ↦ χ n Y * f Y))
      atTop (𝓝 (hf.toLp f)) := by
  let u : ℕ → Lp ℝ 2 μ := fun n ↦ (hF n).toLp (fun Y ↦ χ n Y * f Y)
  let u₀ : Lp ℝ 2 μ := hf.toLp f
  have hnorm (n : ℕ) :
      ‖u n - u₀‖ ^ 2 = ∫ Y, (χ n Y * f Y - f Y) ^ 2 ∂μ := by
    refine (Lp.norm_sq_eq_integral_sq _).trans (integral_congr_ae ?_)
    filter_upwards [Lp.coeFn_sub (u n) u₀, (hF n).coeFn_toLp, hf.coeFn_toLp]
      with Y hsub hcut hsource
    rw [hsub]
    change (((hF n).toLp (fun Z ↦ χ n Z * f Z)) Y - hf.toLp f Y) ^ 2 =
      (χ n Y * f Y - f Y) ^ 2
    rw [hcut, hsource]
  have hint : Tendsto (fun n ↦ ∫ Y, (χ n Y * f Y - f Y) ^ 2 ∂μ)
      atTop (𝓝 0) := by
    have hbound (n : ℕ) : ∀ᵐ Y ∂μ, ‖(χ n Y * f Y - f Y) ^ 2‖ ≤ f Y ^ 2 := .of_forall fun Y ↦ by
      have h0 := (χ n).nonneg (x := Y)
      have h1 := (χ n).le_one (x := Y)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [mul_nonneg (mul_nonneg h0 (by linarith : 0 ≤ 2 - χ n Y)) (sq_nonneg (f Y))]
    have hzero : ∀ᵐ Y ∂μ, Tendsto (fun n ↦ (χ n Y * f Y - f Y) ^ 2) atTop (𝓝 (0 : ℝ)) :=
      .of_forall fun Y ↦ tendsto_const_nhds.congr' <| by
        filter_upwards [hχ.eventually (eventually_ge_atTop ‖Y‖)] with n hn
        rw [(χ n).one_of_mem_closedBall (by simpa using hn), one_mul, sub_self]
        norm_num
    have hdom := tendsto_integral_of_dominated_convergence
      (μ := μ) (F := fun n Y ↦ (χ n Y * f Y - f Y) ^ 2)
      (f := fun _ ↦ (0 : ℝ)) (fun Y ↦ f Y ^ 2)
      (fun n ↦ ((hF n).aestronglyMeasurable.sub hf.aestronglyMeasurable).pow 2)
      hf.integrable_sq hbound hzero
    simpa only [integral_zero] using hdom
  have hsq : Tendsto (fun n ↦ ‖u n - u₀‖ ^ 2) atTop (𝓝 0) := by simpa only [hnorm] using hint
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsq.sqrt

/-- The bounded Newtonian Hessian agrees almost everywhere with the
Hessian of a noncompact C¹ L² source whose Newtonian pairing converges at one
anchor. Compact cutoffs converge both in L² and pointwise after applying the
Hessian. An almost-everywhere subsequence of the operator outputs
identifies those two limits. No Hessian representation is assumed. -/
theorem newtonianHessianL2_apply_ae_eq_of_contDiff_one_of_integrable_at_anchor
    (i j : Fin 5) (S : Lp ℝ 2 (volume : Measure (ℝ^5)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (ℝ^5)))
    (hS : ∀ (g : ℝ^5 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g),
      S ((hg.continuous.memLp_of_hasCompactSupport hgc).toLp g) =ᵐ[volume]
        fun X ↦ (∂[i] (∂[j]
          (convolution (fundamentalSolution 5) g (ContinuousLinearMap.mul ℝ ℝ) volume))) X)
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f) (hLp : MemLp f 2 volume) (A : ℝ^5)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (A - Y) * f Y)) :
    S (hLp.toLp f) =ᵐ[volume] fun X ↦ iteratedPartialDeriv [i, j]
      (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y) X := by
  let χ : ℕ → ContDiffBump (0 : ℝ^5) := fun n ↦
    ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩
  have hχ : Tendsto (fun n ↦ (χ n).rIn) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  let F : ℕ → ℝ^5 → ℝ := fun n Y ↦ χ n Y * f Y
  have hF (n : ℕ) : ContDiff ℝ 1 (F n) := (χ n).contDiff.mul hf
  have hFc (n : ℕ) : HasCompactSupport (F n) := (χ n).hasCompactSupport.mul_right
  have hFLp (n : ℕ) : MemLp (F n) 2 volume :=
    (hF n).continuous.memLp_of_hasCompactSupport (hFc n)
  have hinput : Tendsto (fun n ↦ (hFLp n).toLp (F n)) atTop (𝓝 (hLp.toLp f)) :=
    tendsto_toLp_bump_mul f hLp χ hχ hFLp
  have houtput := (S.continuous.tendsto (hLp.toLp f)).comp hinput
  obtain ⟨ns, hns, hlimit⟩ :=
    (tendstoInMeasure_of_tendsto_Lp houtput).exists_seq_tendsto_ae
  have hcompact (n : ℕ) :
      S ((hFLp n).toLp (F n)) =ᵐ[volume] fun X ↦
        iteratedPartialDeriv [i, j]
          (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * F n Y) X := by
    simpa only [show convolution (fundamentalSolution 5) (F n) (ContinuousLinearMap.mul ℝ ℝ)
        volume = fun Z ↦ ∫ Y, fundamentalSolution 5 (Z - Y) * F n Y from
          funext fun Z ↦ convolution_mul_swap, iteratedPartialDeriv] using
      newtonianHessianL2_apply_ae_eq_of_contDiff_one i j S hS (F n) (hF n) (hFc n)
  filter_upwards [hlimit, ae_all_iff.2 hcompact] with X hlimitX hcompactX
  have hpointwise :=
    (tendsto_fundamentalSolution_five_integral_hessian_bump_mul
      f hf A hInt χ hχ i j X).comp hns.tendsto_atTop
  have hoperator : Tendsto (fun k ↦ iteratedPartialDeriv [i, j]
      (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * F (ns k) Y) X)
      atTop (𝓝 (S (hLp.toLp f) X)) :=
    hlimitX.congr' (Eventually.of_forall fun k ↦ hcompactX (ns k))
  exact tendsto_nhds_unique hoperator hpointwise

/-- The Hessian of a noncompact C¹ L² Newtonian source belongs to
L² whenever its Newtonian pairing converges absolutely at one anchor. -/
theorem fundamentalSolution_five_integral_hessian_memLp_of_contDiff_one
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f) (hLp : MemLp f 2 volume) (A : ℝ^5)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (A - Y) * f Y))
    (i j : Fin 5) :
    MemLp (fun X ↦ iteratedPartialDeriv [i, j]
      (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y) X) 2 volume := by
  obtain ⟨T, hT, _⟩ := exists_newtonianHessianL2
  have hagree :=
    newtonianHessianL2_apply_ae_eq_of_contDiff_one_of_integrable_at_anchor
      i j (T i j) (fun g hg hgc ↦ hT.1 g hg hgc i j) f hf hLp A hInt
  exact (memLp_congr_ae hagree).mp (Lp.memLp (T i j (hLp.toLp f)))

end PotentialTheory
