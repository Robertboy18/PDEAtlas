/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.VectorValued.Classical
public import PDE.Spaces.Sobolev.Calculus.Composition.VectorValued.Integrands
import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.OpenDomain

/-!
# The Banach-valued weak chain rule by smooth approximation

For finite exponents, smooth density gives convergence of the value and each
weak derivative in `Lp`. Continuous superposition then passes the classical
chain rule to the limit. Only continuity and boundedness of the first derivative
of the composing map are needed.
-/

@[expose] public noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Sobolev Topology

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {Ω : Opens ℝ^n} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {Φ : E → F} {C : ℝ≥0}

/-- The weak chain rule for finite normed exponents on arbitrary open domains.
The zero-preserving condition supplies global `Lp` membership on infinite-volume domains. -/
theorem hasWeakDerivativeOn_comp_of_ne_top (hp : p ≠ ∞)
    (hΦ : ContDiff ℝ 1 Φ) (hzero : Φ 0 = 0)
    (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C) (U : W^{1,p}(Ω; E)) (i : Fin n) :
    HasWeakDerivativeOn Ω [i] (fun x ↦ Φ (U.val (baseIndex n 1) x))
      (fun x ↦ fderiv ℝ Φ (U.val (baseIndex n 1) x)
        (U.val (singleDerivIndex n i) x)) := by
  obtain ⟨V, f, hf, hbase, hnorm⟩ := meyers_serrin hp U
  have hV : Tendsto V atTop (𝓝 U) := tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  let B : W^{1,p}(Ω; E) →L[ℝ] Lp E p (domainMeasure n Ω) :=
    coordinateCLM (baseIndex n 1)
  let J : W^{1,p}(Ω; E) →L[ℝ] Lp (E × E) p (domainMeasure n Ω) :=
    valueDerivativeCLM i
  have hB := B.continuous.continuousAt.tendsto.comp hV
  have hJ := J.continuous.continuousAt.tendsto.comp hV
  have hvmem (u : Lp E p (domainMeasure n Ω)) :
      MemLp (Φ ∘ u) p (domainMeasure n Ω) :=
    memLp_comp_of_bounded_fderiv hΦ hzero hbound (Lp.memLp u)
  have hdmem := memLp_chainIntegrand (p := p) (μ := domainMeasure n Ω) hΦ hbound
  have hvconv :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun j ↦ hvmem (B (V j))) _
      (hvmem (B U))).mp
        ((continuous_valueSuperposition hp hΦ hzero hbound).continuousAt.tendsto.comp hB)
  have hdconv :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun j ↦ hdmem (J (V j))) _
      (hdmem (J U))).mp
        ((continuous_chainSuperposition hp hΦ hbound).continuousAt.tendsto.comp hJ)
  have hweak (j : ℕ) :
      HasWeakDerivativeOn Ω [i] (Φ ∘ B (V j))
        (fun x ↦ chainIntegrand Φ (J (V j) x)) := by
    have hfj : ContDiffOn ℝ 1 (f j) Ω := (hf j).of_le (by simp)
    have hd := coordinate_ae_partialDeriv_of_contDiffOn (V j) hfj (hbase j) i
    apply (hasWeakDerivativeOn_comp_of_contDiffOn hΦ hfj i).congr_ae
    · exact ((hbase j).fun_comp Φ).symm
    · filter_upwards [valueDerivativeCLM_apply_ae (V j) i, hbase j, hd]
        with x hpair hb hd'
      change fderiv ℝ Φ (f j x) ((∂[i] (f j)) x) =
        chainIntegrand Φ (valueDerivativeCLM i (V j) x)
      rw [hpair]
      exact congrArg₂ (fun z v ↦ fderiv ℝ Φ z v) hb.symm hd'.symm
  have hclosed := hasWeakDerivativeOn_of_tendsto_eLpNorm
    (fun j ↦ hvmem (B (V j))) (fun j ↦ hdmem (J (V j)))
    (hvmem (B U)) (hdmem (J U)) hweak hvconv hdconv
  apply hclosed.congr_ae Filter.EventuallyEq.rfl
  filter_upwards [valueDerivativeCLM_apply_ae U i] with x hx
  exact congrArg (chainIntegrand Φ) hx

end SobolevSpace.VectorValued
