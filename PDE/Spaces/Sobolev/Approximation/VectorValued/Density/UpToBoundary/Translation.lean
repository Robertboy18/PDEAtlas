/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.Mollification.Graph
public import PDE.Spaces.Sobolev.Compactness.Rellich.Translation
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import PDE.Spaces.Sobolev.Approximation.Mollification.LpApproximation

/-!
# Translated Banach-valued mollification in finite `Lᵖ`

Mollification followed by a translation tending to zero still converges in `Lᵖ`.
This is the analytic step in Evans §5.3.3: the translation makes room for the
mollifier near the boundary. Continuity of measure-preserving composition in `Lp`
combines the two limits. The codomain may be any real Banach space, and the
dimension may be zero.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.3.3, Theorem 3, pp. 266-268, for approximation by
  functions smooth up to a C¹ boundary.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SobolevSpace.VectorValued.UpToBoundary

open Approximation GraphSpace.Rellich

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- If the scale and the translation tend to zero, translated mollification converges
in `Lᵖ`. The original function need not have any weak derivatives. -/
theorem mollifyVector_translate_converges_Lp (μ : Mollifier n) (hp : p ≠ ∞)
    {f : ℝ^n → F} (hf : MemLp f p volume)
    (ε : ℕ → ℝ) (hε : ∀ m, 0 < ε m) (hε0 : Tendsto ε atTop (𝓝 0))
    (a : ℕ → ℝ^n) (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun m ↦ eLpNorm (fun x ↦ mollifyVector μ (ε m) f (x + a m) - f x)
      p volume) atTop (𝓝 0) := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let M (m : ℕ) : Lp F p volume := (memLp_mollifyVector μ (hε m) hp hf).toLp _
  let U : Lp F p volume := hf.toLp f
  have hnorm (m : ℕ) :
      ‖M m - U‖ = (eLpNorm (fun x ↦ mollifyVector μ (ε m) f x - f x) p volume).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae
      ((Lp.coeFn_sub (M m) U).trans
        ((memLp_mollifyVector μ (hε m) hp hf).coeFn_toLp.sub hf.coeFn_toLp))]
    rfl
  have hF : Tendsto M atTop (𝓝 U) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp_rw [hnorm]
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (mollifyVector_converges_Lp μ p hp ε hε hε0 hf)
  have hmaps := continuous_translationContinuousMap.continuousAt.tendsto.comp ha
  have hpres (v : ℝ^n) :
      MeasurePreserving (translationContinuousMap v) volume volume := by
    simpa only [domainMeasure, Measure.restrict_univ] using translationMeasurePreserving v
  have hT := hF.compMeasurePreservingLp hmaps (fun m ↦ hpres (a m)) (hpres 0) hp
  let T (m : ℕ) := Lp.compMeasurePreserving (translationContinuousMap (a m))
    (hpres (a m)) (M m)
  have hzero : Lp.compMeasurePreserving (translationContinuousMap 0) (hpres 0) U = U := by
    apply Lp.ext
    simpa only [Function.comp_def, translationContinuousMap_apply, add_zero] using
      Lp.coeFn_compMeasurePreserving U (hpres 0)
  have hT0 : Tendsto T atTop (𝓝 U) := by
    simpa only [hzero, T, Function.comp_def] using hT
  have herror := (hT0.sub (tendsto_const_nhds (x := U))).enorm
  have hrep (m : ℕ) :
      ((T m - U : Lp F p volume) : ℝ^n → F) =ᵐ[volume]
        fun x ↦ mollifyVector μ (ε m) f (x + a m) - f x := by
    have hshift := (hpres (a m)).quasiMeasurePreserving.ae_eq_comp
      (memLp_mollifyVector μ (hε m) hp hf).coeFn_toLp
    filter_upwards [Lp.coeFn_sub (T m) U,
      Lp.coeFn_compMeasurePreserving (M m) (hpres (a m)), hshift, hf.coeFn_toLp]
      with x hx ht hs hu
    change T m x = M m (x + a m) at ht
    change M m (x + a m) = mollifyVector μ (ε m) f (x + a m) at hs
    exact hx.trans (congrArg₂ (· - ·) (ht.trans hs) hu)
  simpa only [sub_self, enorm_zero, Lp.enorm_def, eLpNorm_congr_ae (hrep _)] using herror

end SobolevSpace.VectorValued.UpToBoundary
