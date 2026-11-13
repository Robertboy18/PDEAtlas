/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.GaussianFlow
public import PDE.Spaces.Sobolev.Approximation.Density.SmoothFieldsContinuity
public import PDE.Analysis.MeasureTheory.Lp.Products
public import PDE.Analysis.Integration.Convolution.Young
import PDE.Analysis.MeasureTheory.Lp.Composition.DilationOrbit

/-!
# Continuity of the time-one heat flow of dilated data

For `f ∈ Lᵖ(ℝ^n)`, `1 ≤ p < ∞`, and `τ ∈ ℝ` let `f_τ x = e^{τ/2} f(e^{τ/2} x)`, the rescaling of
degree `-1`. Dilations are strongly continuous on `Lᵖ`, so `τ ↦ f_τ` is continuous in `Lᵖ`. The
time-one heat flow maps `Lᵖ` boundedly into every `W^{k,r}`, `p ≤ r ≤ ∞`, since
`Dᵏ (G₁ * g) = Dᵏ G₁ * g` and `Dᵏ G₁ ∈ Lᵠ` for every `q ≥ 1`. Hence `τ ↦ G₁ * f_τ` is continuous
into `W^{k,r}(ℝ^n)` for every `k` and every `r ∈ [p, ∞]`, in particular into `W^{k,4} ∩ W^{k,∞}`
for `f ∈ L⁴`.

In self-similar variables this is the cutoff field `U_cut(τ) = -(G₁ * w_τ)` of the far-field part
`w` of the datum, equations (2.7)-(2.10) of Hou, Wang and Yang, *Nonuniqueness of Leray–Hopf
solutions to the unforced incompressible 3D Navier–Stokes Equation*, arXiv:2509.25116v2: the
dilation is only strongly continuous, and the smoothing of `G₁` turns it into continuity in the
norms of `W^{k,∞}`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter SchwartzMap
open scoped ENNReal Topology Sobolev

namespace HeatEquation.WholeSpace

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ^n → E}
  {p r : ℝ≥0∞}

/-- The derivatives of the time-one heat flow of the rescaled data depend continuously on `τ`
in `Lʳ`, for `f ∈ Lᵖ`, `1 ≤ p < ∞`, `p ≤ r ≤ ∞`. -/
theorem tendsto_eLpNorm_iteratedFDeriv_gaussianFlow_one_dilate_sub (hf : MemLp f p volume)
    (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hpr : p ≤ r) (k : ℕ) (τ₀ : ℝ) :
    Tendsto (fun τ ↦ eLpNorm
      (iteratedFDeriv ℝ k (gaussianFlow 1 fun x ↦ Real.exp (τ / 2) • f (Real.exp (τ / 2) • x)) -
        iteratedFDeriv ℝ k
          (gaussianFlow 1 fun x ↦ Real.exp (τ₀ / 2) • f (Real.exp (τ₀ / 2) • x))) r volume)
      (𝓝 τ₀) (𝓝 0) := by
  set g : ℝ → ℝ^n → E := fun τ x ↦ Real.exp (τ / 2) • f (Real.exp (τ / 2) • x)
  have hg (τ : ℝ) : MemLp (g τ) p volume := memLp_dilate hf τ
  have hw (τ : ℝ) := PDE.integrable_polynomialWeight_smul_of_memLp hp1 (hg τ)
  set q := ENNReal.youngExponent p r
  set C := eLpNorm (iteratedFDeriv ℝ k (heatKernelSchwartz n)) q volume
  have hC : C ≠ ∞ := (memLp_iteratedFDeriv _ k _).eLpNorm_ne_top
  have hbound (τ : ℝ) : eLpNorm (iteratedFDeriv ℝ k (gaussianFlow 1 (g τ)) -
      iteratedFDeriv ℝ k (gaussianFlow 1 (g τ₀))) r volume ≤
      C * eLpNorm (g τ - g τ₀) p volume := by
    rw [← iteratedFDeriv_sub ((contDiff_gaussianFlow_one (hw τ)).of_le
      (by exact_mod_cast le_top)) ((contDiff_gaussianFlow_one (hw τ₀)).of_le
      (by exact_mod_cast le_top)), ← gaussianFlow_one_sub (hw τ) (hw τ₀)]
    exact eLpNorm_iteratedFDeriv_gaussianFlow_one_le hp1 (ENNReal.one_le_youngExponent hpr)
      (ENNReal.inv_add_inv_youngExponent r hp1) ((hg τ).sub (hg τ₀)) k
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun _ ↦ zero_le) hbound
  rw [show (0 : ℝ≥0∞) = C * 0 by simp]
  exact ENNReal.Tendsto.const_mul (tendsto_eLpNorm_dilate_sub hf hp1 hp τ₀) (Or.inr hC)

/-- The time-one heat flow of the rescaled data is smooth. -/
theorem contDiff_gaussianFlow_one_dilate (hf : MemLp f p volume) (hp1 : 1 ≤ p) (τ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (gaussianFlow 1 fun x ↦ Real.exp (τ / 2) • f (Real.exp (τ / 2) • x)) :=
  contDiff_gaussianFlow_one (PDE.integrable_polynomialWeight_smul_of_memLp hp1 (memLp_dilate hf τ))

/-- Every derivative of the time-one heat flow of the rescaled data lies in `Lʳ`, `p ≤ r`. -/
theorem memLp_iteratedFDeriv_gaussianFlow_one_dilate (hf : MemLp f p volume) (hp1 : 1 ≤ p)
    (hpr : p ≤ r) (τ : ℝ) (m : ℕ) :
    MemLp (iteratedFDeriv ℝ m
      (gaussianFlow 1 fun x ↦ Real.exp (τ / 2) • f (Real.exp (τ / 2) • x))) r volume :=
  memLp_iteratedFDeriv_gaussianFlow one_pos hp1 hpr (memLp_dilate hf τ) m

/-- The components of the time-one heat flow of the rescaled vector field `f_τ`, as elements of
`W^{k,r}(ℝ^n)`. -/
def gaussianFlowOneDilateWkp (f : ℝ^n → ℝ^n) (hf : MemLp f p volume) (hp1 : 1 ≤ p)
    (hpr : p ≤ r) (k : ℕ) (τ : ℝ) : Fin n → W^{k,r}(ℝ^n) :=
  SobolevSpace.GraphSpace.vectorWkpOfContDiff
    (gaussianFlow 1 fun x ↦ Real.exp (τ / 2) • f (Real.exp (τ / 2) • x))
    (contDiff_gaussianFlow_one_dilate hf hp1 τ)
    (fun m _ ↦ memLp_iteratedFDeriv_gaussianFlow_one_dilate hf hp1 hpr τ m)

/-- The base representatives of `gaussianFlowOneDilateWkp` are the components of the flow. -/
theorem baseRepresentative_gaussianFlowOneDilateWkp (f : ℝ^n → ℝ^n) (hf : MemLp f p volume)
    (hp1 : 1 ≤ p) (hpr : p ≤ r) (k : ℕ) (τ : ℝ) (i : Fin n) :
    SobolevSpace.GraphSpace.baseRepresentative (gaussianFlowOneDilateWkp f hf hp1 hpr k τ i)
      =ᵐ[volume] fun x ↦
        gaussianFlow 1 (fun x ↦ Real.exp (τ / 2) • f (Real.exp (τ / 2) • x)) x i :=
  SobolevSpace.GraphSpace.baseRepresentative_vectorWkpOfContDiff _ _ _ i

/-- For a vector field `f ∈ Lᵖ`, `1 ≤ p < ∞`, the time-one heat flow of
`x ↦ e^{τ/2} f(e^{τ/2} x)` is a continuous path in `W^{k,r}(ℝ^n)` for every `k` and
every `r ∈ [p, ∞]`. -/
theorem continuous_gaussianFlowOneDilateWkp [Fact (1 ≤ r)] (f : ℝ^n → ℝ^n)
    (hf : MemLp f p volume) (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hpr : p ≤ r) (k : ℕ) :
    Continuous (gaussianFlowOneDilateWkp f hf hp1 hpr k) :=
  SobolevSpace.GraphSpace.continuous_vectorWkpOfContDiff _ _ fun τ₀ m _ ↦
    tendsto_eLpNorm_iteratedFDeriv_gaussianFlow_one_dilate_sub hf hp1 hp hpr m τ₀

/-- For a vector field `f ∈ L⁴(ℝ^n)`, the time-one heat flow of `x ↦ e^{τ/2} f(e^{τ/2} x)` is
continuous in `τ` into `W^{k,4} ∩ W^{k,∞}` for every `k`. -/
theorem continuous_gaussianFlow_one_dilate (f : ℝ^n → ℝ^n) (hf : MemLp f 4 volume) (k : ℕ) :
    Continuous (gaussianFlowOneDilateWkp f hf (by norm_num) le_rfl k) ∧
      Continuous (gaussianFlowOneDilateWkp f hf (by norm_num) le_top k) :=
  ⟨continuous_gaussianFlowOneDilateWkp f hf _ (by norm_num) _ k,
    continuous_gaussianFlowOneDilateWkp f hf _ (by norm_num) _ k⟩

/-- The `W^{k,r}` norms of the components of `gaussianFlowOneDilateWkp` grow like
`e^{(τ/2)(1 - n/p)}`, with the constant the sum of the `Lᵠ` norms of the derivatives of `G₁`. -/
theorem norm_gaussianFlowOneDilateWkp_le [Fact (1 ≤ r)] (f : ℝ^n → ℝ^n)
    (hf : MemLp f p volume) (hp1 : 1 ≤ p) (hpr : p ≤ r) (k : ℕ) (τ : ℝ) (i : Fin n) :
    ‖gaussianFlowOneDilateWkp f hf hp1 hpr k τ i‖ ≤
      (∑ a : SobolevSpace.GraphSpace.DerivIndex n k,
        (eLpNorm (iteratedFDeriv ℝ a.toList.length (heatKernelSchwartz n))
          (ENNReal.youngExponent p r) volume).toReal) *
        Real.exp (τ / 2 * (1 - n * p⁻¹.toReal)) * (eLpNorm f p volume).toReal := by
  set U := gaussianFlow 1 fun x ↦ Real.exp (τ / 2) • f (Real.exp (τ / 2) • x)
  have hU := contDiff_gaussianFlow_one_dilate hf hp1 τ
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ U x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hU
  have hmemc : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m (fun x ↦ U x i)) r volume := fun m _ ↦
    (memLp_iteratedFDeriv_gaussianFlow_one_dilate hf hp1 hpr τ m).of_le
      (hc.continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ PDE.norm_iteratedFDeriv_component_le hU i m x)
  have heq : gaussianFlowOneDilateWkp f hf hp1 hpr k τ i =
      SobolevSpace.GraphSpace.wkpOfContDiff (fun x ↦ U x i) hc hmemc := rfl
  rw [heq]
  refine (SobolevSpace.GraphSpace.norm_wkpOfContDiff_le _ _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  set m := a.toList.length
  have hcomp : eLpNorm (iteratedFDeriv ℝ m (fun x ↦ U x i)) r volume ≤
      eLpNorm (iteratedFDeriv ℝ m U) r volume :=
    eLpNorm_mono (hc.continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable
      fun x ↦ PDE.norm_iteratedFDeriv_component_le hU i m x
  have hyoung := eLpNorm_iteratedFDeriv_gaussianFlow_one_le hp1
    (ENNReal.one_le_youngExponent hpr) (ENNReal.inv_add_inv_youngExponent r hp1)
    (memLp_dilate hf τ) m
  rw [eLpNorm_dilate hf.aestronglyMeasurable τ, finrank_euclideanSpace_fin] at hyoung
  have hC := (memLp_iteratedFDeriv (heatKernelSchwartz n) m
    (ENNReal.youngExponent p r)).eLpNorm_ne_top
  have hfin : eLpNorm (iteratedFDeriv ℝ m (heatKernelSchwartz n)) (ENNReal.youngExponent p r)
      volume * (ENNReal.ofReal (Real.exp (τ / 2 * (1 - n * p⁻¹.toReal))) *
        eLpNorm f p volume) ≠ ∞ :=
    ENNReal.mul_ne_top hC (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top)
  calc
    _ ≤ (eLpNorm (iteratedFDeriv ℝ m (heatKernelSchwartz n)) (ENNReal.youngExponent p r)
          volume * (ENNReal.ofReal (Real.exp (τ / 2 * (1 - n * p⁻¹.toReal))) *
            eLpNorm f p volume)).toReal :=
      ENNReal.toReal_mono hfin (hcomp.trans hyoung)
    _ = _ := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
      ring

end HeatEquation.WholeSpace
