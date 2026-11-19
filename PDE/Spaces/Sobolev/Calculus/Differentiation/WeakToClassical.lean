/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import PDE.DistributionTheory.TestFunction.CompactCutoff
import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra
import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport

/-!
# Continuous weak derivatives are classical derivatives

We prove the local analytic step behind Sobolev-Morrey
reconstruction. If a continuous function on Euclidean space has continuous
weak coordinate derivatives, then those derivatives assemble into its
ordinary Fréchet derivative.

The proof mollifies the function and its weak gradient. Weak differentiation
commutes with mollification, while the continuous weak gradient is recovered
locally uniformly by the approximate identity. Mathlib's uniform limit
theorem for derivatives, `hasFDerivAt_of_tendstoLocallyUniformlyOn`, then identifies the
derivative of the original function.

The identity `∂ᵢ(η_ε * u) = η_ε * ∂ᵢu` for the mollified function is the one
used in the interior approximation theorem of Evans, PDE, §5.3.1; combined
with locally uniform convergence of `η_ε * ∂ᵢu` to the continuous `∂ᵢu`, it
shows that a continuous function with continuous weak gradient is `C¹` with
that gradient. This is the step that upgrades the Hölder representative
produced by Morrey's inequality (Evans, PDE, §5.6.2) to a `C¹` function
when the weak derivatives are known to be continuous.

## Main results

* `hasFDerivAt_of_continuous_weakPartialDerivatives`: on `ℝ^n`, a continuous function with
  continuous weak coordinate derivatives `gᵢ` is Fréchet differentiable everywhere, with
  derivative `v ↦ ∑ᵢ gᵢ(x) vᵢ`.
* `hasFDerivAt_of_continuous_weakPartialDerivativesOn`: the same at every point of an open set
  on which the weak derivative identities hold; `f` and the `gᵢ` are still assumed continuous
  on all of `ℝ^n`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.3.1, Theorem 1, pp. 264-265, step 1 of the proof, for
  `D^α(η_ε * u) = η_ε * D^α u`; and §5.6.2, Theorems 4 and 5, pp. 280-284, for the Hölder continuous
  version given by Morrey's inequality.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace Topology

namespace SobolevSpace
namespace Approximation

variable {n : ℕ}

private theorem mollifyVector_apply
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (G : ℝ^n → ℝ^n) (hG : Continuous G) (i : Fin n) (x : ℝ^n) :
    mollifyVector μ ε G x i =
      mollify μ ε (fun y ↦ G y i) x := by
  rw [mollifyVector, mollify]
  simp only [MeasureTheory.convolution]
  change
    (∫ y, scaled μ ε y • G (x - y)) i =
      ∫ y, scaled μ ε y * G (x - y) i
  rw [← PiLp.proj_apply (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i
      (∫ y, scaled μ ε y • G (x - y)),
    ← ContinuousLinearMap.integral_comp_comm]
  · rfl
  apply Continuous.integrable_of_hasCompactSupport
  · exact (scaled_contDiff μ).continuous.smul
      (hG.comp (continuous_const.sub continuous_id))
  · exact (scaled_hasCompactSupport μ hε).smul_right

/-- Continuous weak coordinate derivatives assemble into the classical
Fréchet derivative.

This global form is the approximate-identity theorem used by local
reconstruction results. The vector in the conclusion is the continuous weak
gradient at `x`. -/
theorem hasFDerivAt_of_continuous_weakPartialDerivatives
    {f : ℝ^n → ℝ} {g : Fin n → ℝ^n → ℝ}
    (hf : Continuous f) (hg : ∀ i, Continuous (g i))
    (hweak : ∀ i, HasWeakDerivativeOn (n := n) Set.univ [i] f (g i))
    (x : ℝ^n) :
    HasFDerivAt f
      (innerSL ℝ (WithLp.toLp 2 fun i ↦ g i x)) x := by
  let μ : Mollifier n := standardMollifier n
  let ε : ℕ → ℝ := fun m ↦ ((m + 1 : ℕ) : ℝ)⁻¹
  let G : ℝ^n → ℝ^n := fun y ↦ WithLp.toLp 2 fun i ↦ g i y
  have hεpos (m : ℕ) : 0 < ε m := by positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    simpa [ε, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hG : Continuous G := by fun_prop
  have hderiv : TendstoLocallyUniformly (fun m y ↦ innerSL ℝ (mollifyVector μ (ε m) G y))
      (fun y ↦ innerSL ℝ (G y)) atTop :=
    (innerSL ℝ).uniformContinuous.comp_tendstoLocallyUniformly
      (mollifyVector_tendstoLocallyUniformly_of_continuous μ hG ε hεpos hε0)
  have hresult : HasFDerivAt f (innerSL ℝ (G x)) x := by
    refine hasFDerivAt_of_tendstoLocallyUniformlyOn (f := fun m ↦ mollify μ (ε m) f) (g := f)
      (s := Set.univ) isOpen_univ hderiv.tendstoLocallyUniformlyOn (fun m y _ ↦ ?_)
      (fun y _ ↦ mollify_tendsto_of_continuous μ hf ε hεpos hε0 y) (Set.mem_univ x)
    have hcomm (i : Fin n) : (∂[i] (mollify μ (ε m) f)) y = mollify μ (ε m) (g i) y :=
      congrFun (iteratedPartialDeriv_mollify_eq_mollify_of_hasWeakDerivative_univ μ (hεpos m)
        (α := [i]) (by simp) hf.locallyIntegrable (hweak i)) y
    have hderiv_eq :
        innerSL ℝ (mollifyVector μ (ε m) G y) = fderiv ℝ (mollify μ (ε m) f) y := by
      ext v
      rw [PDE.fderiv_apply_eq_sum_partialDeriv_mul]
      simp only [hcomm, innerSL_apply_apply, PiLp.inner_apply, mollifyVector_apply μ (hεpos m) G hG]
      simp [G, RCLike.inner_apply, mul_comm]
    exact hderiv_eq ▸ ((mollify_contDiff_of_pos μ (hεpos m) f hf.locallyIntegrable).differentiable
      (by simp)).differentiableAt.hasFDerivAt
  simpa [G] using hresult

/-- Continuous weak coordinate derivatives on an open set assemble into the
classical Fréchet derivative at every interior point.

The proof localizes around the point by a compactly supported cutoff and
applies the global reconstruction theorem. No assertion is made at boundary
points. -/
theorem hasFDerivAt_of_continuous_weakPartialDerivativesOn
    {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω)
    {f : ℝ^n → ℝ} {g : Fin n → ℝ^n → ℝ}
    (hf : Continuous f) (hg : ∀ i, Continuous (g i))
    (hweak : ∀ i, HasWeakDerivativeOn (n := n) Ω [i] f (g i))
    {x : ℝ^n} (hx : x ∈ Ω) :
    HasFDerivAt f
      (innerSL ℝ (WithLp.toLp 2 fun i ↦ g i x)) x := by
  classical
  obtain ⟨V, hVopen, hxV, hclVΩ, hclV⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton hΩ (singleton_subset_iff.2 hx)
  have hLpV {h : ℝ^n → ℝ} (hh : Continuous h) : MemLp h 1 (domainMeasure n V) :=
    memLp_one_iff_integrable.mpr
      ((hh.locallyIntegrable.integrableOn_isCompact hclV).mono_set subset_closure)
  obtain ⟨ψ, hψV, hψ1, hψnhds, _hψRange⟩ := TestFunction.exists_eq_one_on_compact hVopen
    isCompact_singleton hxV
  let F : ℝ^n → ℝ := fun y ↦ ψ.toFun y * f y
  let G : Fin n → ℝ^n → ℝ := fun i y ↦
    ψ.toFun y * g i y + iteratedPartialDeriv (n := n) [i] ψ.toFun y * f y
  have hdψ (i : Fin n) {y : ℝ^n} (h : fderiv ℝ ψ.toFun y = 0) :
      iteratedPartialDeriv (n := n) [i] ψ.toFun y = 0 := by
    change fderiv ℝ ψ.toFun y (EuclideanSpace.single i (1 : ℝ)) = 0
    rw [h]
    rfl
  have hsuppG (i : Fin n) : Function.support (G i) ⊆ tsupport ψ.toFun := fun y hy ↦ by
    by_contra hyt
    exact hy (by simp only [G, image_eq_zero_of_notMem_tsupport hyt,
      hdψ i (fderiv_of_notMem_tsupport (𝕜 := ℝ) hyt), zero_mul, add_zero])
  obtain ⟨χ, hχV, _hχ1, hχnhds, _hχRange⟩ :=
    TestFunction.exists_eq_one_on_compact hVopen ψ.hasCompactSupport hψV
  have hweakFG (i : Fin n) : HasWeakDerivativeOn (n := n) V [i] F (G i) := by
    simpa [F, G] using hasWeakDerivativeOn_mul_testFunction_first (n := n) (p := (1 : ℝ≥0∞))
      (hLpV hf) (hLpV (hg i)) ((hweak i).mono hVopen.measurableSet (subset_closure.trans hclVΩ)) ψ
  have hweakGlobal (i : Fin n) : HasWeakDerivativeOn (n := n) Set.univ [i] F (G i) :=
    CompactSupportLocalization.hasWeakDerivativeOn_univ_of_support_subset_of_cutoff_one_nhds
      hVopen hψV ((Function.support_mul_subset_left _ _).trans (subset_tsupport _)) (hsuppG i)
      χ hχV hχnhds (hweakFG i)
  have hGcont (i : Fin n) : Continuous (G i) :=
    (ψ.contDiff.continuous.mul (hg i)).add
      ((PDE.contDiff_top_iteratedPartialDeriv (n := n) ψ.contDiff [i]).continuous.mul hf)
  have hevent : ψ.toFun =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ) := hψnhds x rfl
  have hGx (i : Fin n) : G i x = g i x := by
    simp only [G, hψ1 x rfl, hdψ i (by simpa using hevent.fderiv_eq), one_mul, zero_mul, add_zero]
  have hFeq : F =ᶠ[𝓝 x] f := hevent.mono fun y (hy : ψ.toFun y = 1) ↦ by simp only [F, hy, one_mul]
  simpa [hGx] using (hasFDerivAt_of_continuous_weakPartialDerivatives
    (ψ.contDiff.continuous.mul hf) hGcont hweakGlobal x).congr_of_eventuallyEq hFeq.symm

end Approximation
end SobolevSpace
