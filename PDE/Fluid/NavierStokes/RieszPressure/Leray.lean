/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.RieszPressure
public import PDE.Fluid.Incompressible.LerayProjection
public import PDE.Fluid.NavierStokes.Stationary.SolenoidalDensity
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder.Classical
import PDE.DistributionTheory.TestFunction.IntegrationByParts
import PDE.Analysis.Integration.CompactByPartsCoordinates

/-!
# The Riesz pressure and the Leray projection of the convection

For a divergence-free `C¹` velocity `u` on `ℝⁿ` with `u ∈ L⁴ ∩ L^∞` and `Du ∈ L²`, the convection
`(u·∇)u` is square integrable, the Riesz pressure `P = Σᵢⱼ RᵢRⱼ(uᵢuⱼ)` lies in `H¹(ℝⁿ)`, and
`(u·∇)u + ∇P` is the Leray projection of `(u·∇)u` (`advective_add_gradient_rieszPressure`, with the
pointwise form `lerayProjection_advective_ae_eq`).

## How it works

The products `uᵢuⱼ` lie in `H¹` (`exists_wkpSpace_one_velocityProduct`), so the Riesz pressure does
(`exists_wkpSpace_rieszPressureL2`). Its gradient `∇P` is a weak gradient and is annihilated by the
projection (`lerayProjection_wkpGradient_eq_zero`), so it remains to show that `(u·∇)u + ∇P` is
weakly divergence free, that is orthogonal to the gradients of test functions `χ`, which makes it
its own projection (`lerayProjection_eq_self`). This holds because `∫ (u·∇)u·∇χ = -Σᵢⱼ ∫ uᵢuⱼ ∂ᵢ∂ⱼχ`
by integration by parts and `div u = 0` (`integral_advective_inner_gradient`), while
`∫ ∇P·∇χ = -∫ P Δχ = Σᵢⱼ ∫ uᵢuⱼ ∂ᵢ∂ⱼχ` by the Poisson equation of `P`
(`integral_rieszPressure_mul_laplacian`).
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace NavierStokes

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional
  IncompressibleFlow Set
open scoped ENNReal Sobolev RealInnerProductSpace

variable {n : ℕ}

/-- Products of components of a `C¹` field in `L⁴`, essentially bounded, with
square-integrable derivative, lie in `H¹(ℝⁿ)`. -/
theorem exists_wkpSpace_one_velocityProduct {u : ℝ^n → ℝ^n} (hu : ContDiff ℝ 1 u)
    (hu4 : MemLp u 4 volume) {C : ℝ} (hC : ∀ᵐ x ∂volume, ‖u x‖ ≤ C)
    (hgrad : MemLp (fderiv ℝ u) 2 volume) (k l : Fin n) :
    ∃ U : W^{1,2}(ℝ^n), baseL2 U = velocityProductL2 u k l := by
  have hbL2 {m : ℕ} (U : W^{m,2}(ℝ^n)) : (baseL2 U : ℝ^n → ℂ) =ᵐ[volume]
      fun x ↦ (baseRepresentative U x : ℂ) :=
    MemLp.coeFn_toLp (SobolevSpace.Fractional.memLp_coordFun U (baseIndex n m)).ofReal
  have hcomp (i : Fin n) : ContDiff ℝ 1 (fun x ↦ u x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hu
  have hf : ContDiff ℝ 1 (fun x ↦ u x k * u x l) := (hcomp k).mul (hcomp l)
  have hbase : MemLp (fun x ↦ u x k * u x l) 2 (domainMeasure n univ) := by
    simpa [domainMeasure] using memLp_two_mul_of_memLp_four hu4 k l
  have hd (x : ℝ^n) : DifferentiableAt ℝ u x := (hu.differentiable one_ne_zero) x
  have hpart (j : Fin n) : MemLp (PDE.partialDeriv j (fun x ↦ u x k * u x l)) 2
      (domainMeasure n univ) := by
    have hmeas : AEStronglyMeasurable (PDE.partialDeriv j (fun x ↦ u x k * u x l)) volume :=
      ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
    have h := (hgrad.norm.const_mul (2 * |C|)).of_le hmeas ?_
    · simpa [domainMeasure] using h
    filter_upwards [hC] with x hx
    have hx' : ‖u x‖ ≤ |C| := hx.trans (le_abs_self C)
    have hp : PDE.partialDeriv j (fun y ↦ u y k * u y l) x =
        PDE.partialDeriv j (fun y ↦ u y k) x * u x l +
          u x k * PDE.partialDeriv j (fun y ↦ u y l) x :=
      PDE.partialDeriv_mul ((hcomp k).differentiable one_ne_zero x)
        ((hcomp l).differentiable one_ne_zero x)
    rw [hp, Real.norm_of_nonneg (show (0 : ℝ) ≤ 2 * |C| * ‖fderiv ℝ u x‖ by positivity)]
    have h1 := PDE.norm_partialDeriv_component_le (hd x) j k
    have h2 := PDE.norm_partialDeriv_component_le (hd x) j l
    have h3 : ‖u x l‖ ≤ |C| := (PiLp.norm_apply_le _ l).trans hx'
    have h4 : ‖u x k‖ ≤ |C| := (PiLp.norm_apply_le _ k).trans hx'
    calc _ ≤ ‖fderiv ℝ u x‖ * |C| + |C| * ‖fderiv ℝ u x‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
          gcongr
      _ = 2 * |C| * ‖fderiv ℝ u x‖ := by ring
  obtain ⟨U, ⟨hU0, -⟩, -⟩ := existsUnique_firstOrder_of_contDiffOn_memLp isOpen_univ
    hf.contDiffOn hbase hpart
  refine ⟨U, Lp.ext ?_⟩
  have hU0' : baseRepresentative U =ᵐ[volume] fun x ↦ u x k * u x l := by
    simp only [domainMeasure, Measure.restrict_univ, wkpBaseCoordinateCLM_apply] at hU0
    exact hU0
  filter_upwards [hbL2 U, hU0', coeFn_velocityProductL2
    (memLp_two_mul_of_memLp_four hu4 k l)] with x h1 h2 h3
  rw [h1, h2, h3]

/-- Weak divergence identity for the convection of a divergence-free `C¹` field:
`∫ (u·∇)u · ∇ψ = -Σₖ Σⱼ ∫ uⱼ uₖ ∂ⱼ∂ₖψ` for smooth compactly supported `ψ`. -/
theorem integral_advective_inner_gradient {u : ℝ^n → ℝ^n} (hu : ContDiff ℝ 1 u)
    (hdiv : ∀ x, PDE.divergence u x = 0) {ψ : ℝ^n → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x, ∑ k, PDE.advectiveDerivative u u x k * PDE.partialDeriv k ψ x =
      -∑ k, ∑ j, ∫ x, u x j * u x k * iteratedPartialDeriv [j, k] ψ x := by
  have hcomp (i : Fin n) : ContDiff ℝ 1 (fun x ↦ u x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hu
  have hdψ1 (k : Fin n) : ContDiff ℝ 1 (fun x ↦ PDE.partialDeriv k ψ x) :=
    (PDE.contDiff_top_partialDeriv hψ).of_le (by exact_mod_cast le_top)
  set g : Fin n → Fin n → ℝ^n → ℝ := fun j k y ↦ u y j * u y k * PDE.partialDeriv k ψ y
    with hgdef
  have hg (j k : Fin n) : ContDiff ℝ 1 (g j k) := ((hcomp j).mul (hcomp k)).mul (hdψ1 k)
  have hgc (j k : Fin n) : HasCompactSupport (g j k) := (hψc.partialDeriv k).mul_left
  have hdg (j k : Fin n) (x : ℝ^n) : PDE.partialDeriv j (g j k) x =
      PDE.partialDeriv j (fun y ↦ u y j) x * u x k * PDE.partialDeriv k ψ x +
        u x j * PDE.partialDeriv j (fun y ↦ u y k) x * PDE.partialDeriv k ψ x +
        u x j * u x k * iteratedPartialDeriv [j, k] ψ x := by
    have h1 := PDE.partialDeriv_mul (i := j) (x := x)
      (((hcomp j).mul (hcomp k)).differentiable one_ne_zero x)
      ((hdψ1 k).differentiable one_ne_zero x)
    have h2 := PDE.partialDeriv_mul (i := j) (x := x) ((hcomp j).differentiable one_ne_zero x)
      ((hcomp k).differentiable one_ne_zero x)
    simp only [hgdef]
    rw [h1, h2]
    simp only [iteratedPartialDeriv]
    ring
  have hadv (x : ℝ^n) (k : Fin n) : PDE.advectiveDerivative u u x k =
      ∑ j, u x j * PDE.partialDeriv j (fun y ↦ u y k) x :=
    PDE.Analysis.fderiv_apply_component ((hu.differentiable one_ne_zero) x) (u x) k
  have hpt (x : ℝ^n) : ∑ k, PDE.advectiveDerivative u u x k * PDE.partialDeriv k ψ x =
      ∑ k, ∑ j, PDE.partialDeriv j (g j k) x -
        ∑ k, ∑ j, u x j * u x k * iteratedPartialDeriv [j, k] ψ x := by
    have hd0 : ∑ j, PDE.partialDeriv j (fun y ↦ u y j) x = 0 := hdiv x
    simp only [hdg, hadv]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_mul, hd0, Finset.sum_mul]
    ring
  have iD (j k : Fin n) : Integrable (fun x ↦ PDE.partialDeriv j (g j k) x) volume :=
    (((hg j k).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport ((hgc j k).partialDeriv j)
  have iU (j k : Fin n) : Integrable (fun x ↦ u x j * u x k * iteratedPartialDeriv [j, k] ψ x)
      volume :=
    (((hcomp j).continuous.mul (hcomp k).continuous).mul
      (PDE.contDiff_top_iteratedPartialDeriv hψ [j, k]).continuous).integrable_of_hasCompactSupport
      (hψc.iteratedPartialDeriv [j, k]).mul_left
  -- the divergence terms integrate to zero
  have hz (k : Fin n) : ∫ x, ∑ j, PDE.partialDeriv j (g j k) x = 0 := by
    rw [integral_finsetSum _ fun j _ ↦ iD j k]
    exact Finset.sum_eq_zero fun j _ ↦
      PDE.DistributionTheory.integral_partialDeriv_eq_zero_of_hasCompactSupport j (hg j k)
        (hgc j k)
  rw [integral_congr_ae (.of_forall hpt),
    integral_sub (integrable_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun j _ ↦ iD j k)
      (integrable_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun j _ ↦ iU j k),
    integral_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun j _ ↦ iD j k,
    integral_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun j _ ↦ iU j k,
    Finset.sum_eq_zero fun k _ ↦ hz k, zero_sub]
  exact congrArg Neg.neg (Finset.sum_congr rfl fun k _ ↦ integral_finsetSum _ fun j _ ↦ iU j k)

/-- **The Riesz pressure completes the Leray projection of the convection.** For a
divergence-free `C¹` velocity `u` on `ℝⁿ` with `u ∈ L⁴ ∩ L^∞` and `Du ∈ L²`, the Riesz
pressure `P = rieszPressure u` is (almost everywhere) an `H¹(ℝⁿ)` function `p`, the convection
`(u·∇)u` is square integrable, and `Π((u·∇)u) = (u·∇)u + ∇p` in `L²`. The `C¹` hypothesis makes
`(u·∇)u` the classical convection and allows the integration by parts
`∫ (u·∇)u·∇χ = -Σᵢⱼ ∫ uᵢuⱼ ∂ᵢ∂ⱼχ`. -/
theorem advective_add_gradient_rieszPressure {u : ℝ^n → ℝ^n} (hu : ContDiff ℝ 1 u)
    (hu4 : MemLp u 4 volume) (hinf : MemLp u ⊤ volume) (hgrad : MemLp (fderiv ℝ u) 2 volume)
    (hdiv : ∀ x, PDE.divergence u x = 0) :
    ∃ p : H¹(ℝ^n), baseRepresentative p =ᵐ[volume] rieszPressure u ∧
      ∃ ha : MemLp (fun x ↦ PDE.advectiveDerivative u u x) 2 (domainMeasure n univ),
        lerayProjection n (ha.toLp _) = ha.toLp _ + wkpGradientCLM p := by
  have hbL2 {m : ℕ} (U : W^{m,2}(ℝ^n)) : (baseL2 U : ℝ^n → ℂ) =ᵐ[volume]
      fun x ↦ (baseRepresentative U x : ℂ) :=
    MemLp.coeFn_toLp (SobolevSpace.Fractional.memLp_coordFun U (baseIndex n m)).ofReal
  set C := (eLpNormEssSup u volume).toReal with hCdef
  have hfin : eLpNormEssSup u volume ≠ ⊤ :=
    eLpNorm_exponent_top hinf.aestronglyMeasurable ▸ hinf.eLpNorm_ne_top
  have hC : ∀ᵐ x ∂volume, ‖u x‖ ≤ C := by
    filter_upwards [enorm_ae_le_eLpNormEssSup u volume] with x hx
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 (by rwa [ofReal_norm])
  choose F hF using exists_wkpSpace_one_velocityProduct hu hu4 hC hgrad
  obtain ⟨p, hp⟩ := exists_wkpSpace_rieszPressureL2 F hF
  have hpP : baseRepresentative p =ᵐ[volume] rieszPressure u := by
    filter_upwards [hbL2 p, rieszPressure_ae_eq u] with x h1 h2
    rw [h2, ← hp, h1, Complex.ofReal_re]
  refine ⟨p, hpP, ?_⟩
  have hd (x : ℝ^n) : DifferentiableAt ℝ u x := (hu.differentiable one_ne_zero) x
  have ha : MemLp (fun x ↦ PDE.advectiveDerivative u u x) 2 (domainMeasure n univ) := by
    have hmeas : AEStronglyMeasurable (fun x ↦ PDE.advectiveDerivative u u x) volume :=
      ((hu.continuous_fderiv one_ne_zero).clm_apply hu.continuous).aestronglyMeasurable
    have h := (hgrad.norm.const_mul |C|).of_le hmeas ?_
    · simpa [domainMeasure] using h
    filter_upwards [hC] with x hx
    rw [norm_mul, norm_norm, Real.norm_of_nonneg (abs_nonneg C), mul_comm]
    exact ((fderiv ℝ u x).le_opNorm (u x)).trans
      (mul_le_mul_of_nonneg_left (hx.trans (le_abs_self C)) (norm_nonneg _))
  refine ⟨ha, ?_⟩
  set A : WholeSpaceL2 n := ha.toLp _ with hAdef
  set G : WholeSpaceL2 n := wkpGradientCLM p with hGdef
  have hUU (i j : Fin n) := memLp_two_mul_of_memLp_four hu4 i j
  have hsol : A + G ∈ l2Solenoidal n := by
    rw [mem_l2Solenoidal_iff_inner]
    intro φ
    set ψ : ℝ^n → ℝ := φ.1.toFun with hψdef
    have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := φ.1.contDiff
    have hψc : HasCompactSupport ψ := φ.1.hasCompactSupport
    have hgradφ := l2TestGradient_apply_ae φ
    simp only [domainMeasure, Measure.restrict_univ] at hgradφ
    -- the convection term
    have hA : inner ℝ A (l2TestGradient φ) =
        -∑ k, ∑ j, ∫ x, u x j * u x k * iteratedPartialDeriv [j, k] ψ x := by
      rw [← integral_advective_inner_gradient hu hdiv hψ hψc, L2.inner_def]
      simp only [domainMeasure, Measure.restrict_univ]
      apply integral_congr_ae
      have hAe := ha.coeFn_toLp
      simp only [domainMeasure, Measure.restrict_univ] at hAe
      filter_upwards [hAe, hgradφ] with x h1 h2
      rw [h1, PiLp.inner_apply]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [h2 k, real_inner_eq_re_inner, RCLike.inner_apply,
        conj_trivial, RCLike.re_to_real, mul_comm]
    -- the pressure term
    have hG : inner ℝ G (l2TestGradient φ) =
        ∑ i, ∑ j, ∫ x, u x i * u x j * iteratedPartialDeriv [i, j] ψ x := by
      have hGe := wkpGradientCLM_apply_ae (n := n) (p := 2) (Ω := univ) p
      simp only [domainMeasure, Measure.restrict_univ] at hGe
      have hcoord (k : Fin n) : MemLp
          (fun x ↦ (wkpCoordinateCLM (singleDerivIndex n k) p : ℝ^n → ℝ) x) 2 volume := by
        simpa [domainMeasure] using Lp.memLp (wkpCoordinateCLM (singleDerivIndex n k) p)
      have hbase : MemLp (fun x ↦ (wkpBaseCoordinateCLM p : ℝ^n → ℝ) x) 2 volume := by
        simpa [domainMeasure] using Lp.memLp (wkpBaseCoordinateCLM p)
      have hdψ (k : Fin n) : MemLp (fun x ↦ PDE.partialDeriv k ψ x) 2 volume :=
        (PDE.contDiff_top_partialDeriv hψ).continuous.memLp_of_hasCompactSupport
          (hψc.partialDeriv k)
      have hddψ (k : Fin n) : MemLp
          (fun x ↦ PDE.partialDeriv k (fun y ↦ PDE.partialDeriv k ψ y) x) 2 volume :=
        (PDE.contDiff_top_partialDeriv
          (PDE.contDiff_top_partialDeriv hψ)).continuous.memLp_of_hasCompactSupport
          ((hψc.partialDeriv k).partialDeriv k)
      have iC (k : Fin n) : Integrable (fun x ↦
          (wkpCoordinateCLM (singleDerivIndex n k) p : ℝ^n → ℝ) x * PDE.partialDeriv k ψ x)
          volume := (hcoord k).integrable_mul (hdψ k)
      have iB (k : Fin n) : Integrable (fun x ↦ (wkpBaseCoordinateCLM p : ℝ^n → ℝ) x *
          PDE.partialDeriv k (fun y ↦ PDE.partialDeriv k ψ y) x) volume :=
        hbase.integrable_mul (hddψ k)
      have hstep1 : inner ℝ G (l2TestGradient φ) =
          ∑ k, ∫ x, (wkpCoordinateCLM (singleDerivIndex n k) p : ℝ^n → ℝ) x *
            PDE.partialDeriv k ψ x := by
        rw [← integral_finsetSum _ fun k _ ↦ iC k, L2.inner_def]
        simp only [domainMeasure, Measure.restrict_univ]
        apply integral_congr_ae
        filter_upwards [hGe, hgradφ] with x h1 h2
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [hGdef, h1 k, h2 k, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial,
          RCLike.re_to_real, mul_comm, wkpCoordinateCLM_apply]
      have hstep2 (k : Fin n) : ∫ x, (wkpCoordinateCLM (singleDerivIndex n k) p : ℝ^n → ℝ) x *
          PDE.partialDeriv k ψ x = -∫ x, (wkpBaseCoordinateCLM p : ℝ^n → ℝ) x *
            PDE.partialDeriv k (fun y ↦ PDE.partialDeriv k ψ y) x := by
        rw [Stationary.integral_base_mul_partialDeriv p k (PDE.contDiff_top_partialDeriv hψ)
          (hψc.partialDeriv k), neg_neg]
      have hstep3 : ∑ k, ∫ x, (wkpBaseCoordinateCLM p : ℝ^n → ℝ) x *
          PDE.partialDeriv k (fun y ↦ PDE.partialDeriv k ψ y) x =
          ∫ x, rieszPressure u x * PDE.laplacian ψ x := by
        rw [← integral_finsetSum _ fun k _ ↦ iB k]
        apply integral_congr_ae
        filter_upwards [hpP] with x hx
        rw [PDE.laplacian, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [wkpBaseCoordinateCLM_apply]
        change baseRepresentative p x * _ = _
        rw [hx]
      rw [hstep1, Finset.sum_congr rfl fun k _ ↦ hstep2 k, Finset.sum_neg_distrib, hstep3,
        integral_rieszPressure_mul_laplacian hUU hψ hψc, neg_neg]
    rw [inner_add_left, hA, hG, Finset.sum_comm]
    ring
  calc lerayProjection n A = lerayProjection n (A + G) - lerayProjection n G := by
        rw [map_add]; abel
    _ = A + G := by
        rw [lerayProjection_eq_self hsol, hGdef, lerayProjection_wkpGradient_eq_zero, sub_zero]

/-- Pointwise form of `advective_add_gradient_rieszPressure` for a `C¹` Riesz pressure: almost
everywhere, `Π((u·∇)u) = (u·∇)u + ∇P` with the classical gradient of `P = rieszPressure u`. -/
theorem lerayProjection_advective_ae_eq {u : ℝ^n → ℝ^n} (hu : ContDiff ℝ 1 u)
    (hu4 : MemLp u 4 volume) (hinf : MemLp u ⊤ volume) (hgrad : MemLp (fderiv ℝ u) 2 volume)
    (hdiv : ∀ x, PDE.divergence u x = 0) (hP : ContDiff ℝ 1 (rieszPressure u)) :
    ∃ ha : MemLp (fun x ↦ PDE.advectiveDerivative u u x) 2 (domainMeasure n univ),
      ∀ᵐ x ∂volume, ∀ i : Fin n, (lerayProjection n (ha.toLp _) x) i =
        PDE.advectiveDerivative u u x i + PDE.partialDeriv i (rieszPressure u) x := by
  obtain ⟨p, hpP, ha, hproj⟩ := advective_add_gradient_rieszPressure hu hu4 hinf hgrad hdiv
  refine ⟨ha, ?_⟩
  have hg := wkpGradientCLM_ae_eq_partialDeriv p hP hpP.symm
  have hA := ha.coeFn_toLp
  have hsum := Lp.coeFn_add (ha.toLp _) (wkpGradientCLM p)
  simp only [domainMeasure, Measure.restrict_univ] at hA hsum
  filter_upwards [hg, hA, hsum] with x h1 h2 h3 i
  rw [hproj, h3, Pi.add_apply, PiLp.add_apply, h2, h1 i]

end NavierStokes
