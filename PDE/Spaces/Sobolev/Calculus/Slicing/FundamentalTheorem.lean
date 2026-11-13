/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import PDE.DistributionTheory.TestFunction.CompactCutoff
import PDE.Spaces.Sobolev.Approximation.Mollification.LpApproximation
import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra
import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport

/-!
# One-dimensional weak fundamental theorem of calculus

We prove the fundamental-theorem identity for a supplied continuous
representative of one-dimensional `W^{1,1}` data. The proof mollifies the weak
derivative, applies the classical FTC to every smooth mollification, and passes
to the limit in `L¹`.

The existence of an absolutely continuous representative for arbitrary one-dimensional `W^{1,1}`
data is a separate theorem, in `Slicing.AbsolutelyContinuousRepresentative`. Classically both
statements are part of the characterization of `W^{1,p}` on an interval (Brezis,
*Functional Analysis, Sobolev Spaces and PDE*, Chapter 8): the identity `∫_a^b u' = ū(b) - ū(a)` for
the continuous representative `ū`.

## Main results

* `intervalIntegral_weakDerivative_eq_sub`: if `f : ℝ^1 → ℝ` is continuous,
  `g ∈ L¹`, and `g` is the weak derivative of `f` on `ℝ^1`, then
  `∫_a^b g = f(b) - f(a)` in the real coordinate.
* `intervalIntegral_weakDerivative_eq_sub_on`: the same on an open set
  `U ⊆ ℝ^1` containing the interval, with `L¹` hypotheses only on `U`;
  a smooth cutoff reduces it to the global statement.

## Implementation notes

Points of `ℝ^1` are written through `(PiLp.equivOfUnique 2 ℝ _).symm t`, the
identification of `ℝ^1` with `ℝ`, so that Mathlib's interval integral applies
directly. The mollifier `Approximation.standardMollifier 1` is fixed inside the
proof and does not appear in the statement.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 8, for the absolutely continuous representative of a `W^{1,p}` function on
  an interval and the identity `ū(b) - ū(a) = ∫_a^b u'`.
  <https://doi.org/10.1007/978-0-387-70914-7>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.2, p. 259, which states that on an interval
  `u ∈ W^{1,p}` exactly when `u` agrees a.e. with an absolutely continuous function whose derivative
  lies in `L^p`, and leaves the proof to the exercises.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace

open Filter MeasureTheory PDE.Common Set
open scoped ENNReal Topology

namespace FundamentalTheorem

/-- A continuous global representative with an `L¹` weak derivative obeys
the literal interval fundamental theorem of calculus. -/
theorem intervalIntegral_weakDerivative_eq_sub
    (f g : ℝ^1 → ℝ)
    (hf : Continuous f)
    (hg : MemLp g 1 (volume : Measure (ℝ^1)))
    (hweak : HasWeakDerivativeOn (n := 1) Set.univ [0] f g)
    (a b : ℝ) :
    (∫ t in a..b, g ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t)) =
      f ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm b) -
        f ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm a) := by
  set e := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  have he : MeasurePreserving e volume volume := (PiLp.volume_preserving_toLp (Fin 1)).comp
    ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _)
  let μ := Approximation.standardMollifier 1
  let ε : ℕ → ℝ := fun m ↦ (1 : ℝ) / ((m : ℝ) + 1)
  have hεpos (m : ℕ) : 0 < ε m := Nat.one_div_pos_of_nat
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hfLoc : LocallyIntegrable f (volume : Measure (ℝ^1)) :=
    locallyIntegrableOn_univ.mp hweak.locallyIntegrable_f
  let fm : ℕ → ℝ^1 → ℝ := fun m ↦ Approximation.mollify μ (ε m) f
  let gm : ℕ → ℝ^1 → ℝ := fun m ↦ Approximation.mollify μ (ε m) g
  -- the classical FTC for every mollification, whose derivative is the mollified `g`
  have hFTC (m : ℕ) : ∫ t in a..b, gm m (e t) = fm m (e b) - fm m (e a) := by
    have hfm : ContDiff ℝ (⊤ : ℕ∞) (fm m) :=
      Approximation.mollify_contDiff_of_pos μ (hεpos m) f hfLoc
    have hderiv : (fun x ↦ (∂[0] (fm m)) x) = gm m := by
      simpa [fm, gm, iteratedPartialDeriv] using
        (Approximation.iteratedPartialDeriv_mollify_eq_mollify_of_hasWeakDerivative_univ
          μ (hεpos m) (α := ([0] : List (Fin 1))) (by simp) hfLoc hweak)
    have hd (t : ℝ) : HasDerivAt (fm m ∘ e) (gm m (e t)) t :=
      (((hfm.comp e.contDiff).differentiable (by simp)) t).hasDerivAt.congr_deriv
        ((PDE.deriv_comp_equivOfUnique_symm (fm m) t
          ((hfm.differentiable (by simp)).differentiableAt)).trans (congrFun hderiv _))
    have hgm : Continuous fun t ↦ gm m (e t) :=
      ((Approximation.mollify_contDiff_of_pos μ (hεpos m) g
        (hg.locallyIntegrable (by norm_num))).continuous).comp e.continuous
    simpa [Function.comp_def] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t) (hgm.intervalIntegrable a b)
  -- the mollified `g` converge to `g` in `L¹(ℝ^1)`, hence in `L¹(ℝ)`
  have hgmLp (m : ℕ) : MemLp (gm m) 1 (volume : Measure (ℝ^1)) :=
    lt_of_le_of_lt (Approximation.MollifyLp.eLpNorm_mollify_le (n := 1) (p := (1 : ℝ≥0∞))
      (μ := μ) (ε := ε m) (hεpos m) (by norm_num) hg) hg
  have hconv : Tendsto (fun m ↦ eLpNorm ((fun t ↦ gm m (e t)) - fun t ↦ g (e t)) 1
      (volume : Measure ℝ)) atTop (𝓝 0) :=
    (Approximation.mollify_converges_Lp μ 1 (by norm_num) ε hεpos hε0 hg).congr fun m ↦
      (eLpNorm_comp_measurePreserving
        ((hgmLp m).aestronglyMeasurable.sub hg.aestronglyMeasurable) he).symm
  have hset := tendsto_setIntegral_of_L1' (μ := (volume : Measure ℝ)) (f := fun t ↦ g (e t))
    (F := fun m t ↦ gm m (e t))
    (Eventually.of_forall fun m ↦ memLp_one_iff_integrable.mp ((hgmLp m).comp_measurePreserving he))
    hconv (Set.uIoc a b)
  have hint : Tendsto (fun m ↦ ∫ t in a..b, gm m (e t)) atTop (𝓝 (∫ t in a..b, g (e t))) := by
    simpa only [intervalIntegral.intervalIntegral_eq_integral_uIoc] using
      tendsto_const_nhds.smul hset
  exact tendsto_nhds_unique (by simpa only [hFTC] using hint)
    ((Approximation.mollify_tendsto_of_continuous μ hf ε hεpos hε0 (e b)).sub
      (Approximation.mollify_tendsto_of_continuous μ hf ε hεpos hε0 (e a)))

/-- Local weak FTC on an open subset of the line.  The `L¹` assumptions are
only imposed on the open domain; smooth cutoffs turn them into the compactly
supported global data consumed by `intervalIntegral_weakDerivative_eq_sub`.
-/
theorem intervalIntegral_weakDerivative_eq_sub_on
    (U : Set (ℝ^1)) (hU : IsOpen U)
    (f g : ℝ^1 → ℝ)
    (hf : Continuous f)
    (hfLp : MemLp f 1 (domainMeasure 1 U))
    (hgLp : MemLp g 1 (domainMeasure 1 U))
    (hweak : HasWeakDerivativeOn (n := 1) U [0] f g)
    (a b : ℝ)
    (hab : (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm '' Set.uIcc a b ⊆ U) :
    (∫ t in a..b, g ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t)) =
      f ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm b) -
        f ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm a) := by
  set e := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  obtain ⟨ψ, hψU, hψ1, hψnhds, -⟩ :=
    TestFunction.exists_eq_one_on_compact hU (isCompact_uIcc.image e.continuous) hab
  -- `F = ψ f` has the weak derivative `G = ψ g + ∂ψ f` and both vanish off `tsupport ψ`
  let F : ℝ^1 → ℝ := fun x ↦ ψ.toFun x * f x
  let G : ℝ^1 → ℝ := fun x ↦
    ψ.toFun x * g x + iteratedPartialDeriv (n := 1) [0] ψ.toFun x * f x
  have hweakFG : HasWeakDerivativeOn (n := 1) U [0] F G :=
    hasWeakDerivativeOn_mul_testFunction_first (n := 1) (p := (1 : ℝ≥0∞)) hfLp hgLp hweak ψ
  have hsuppF : Function.support F ⊆ tsupport ψ.toFun :=
    (Function.support_mul_subset_left _ _).trans (subset_tsupport _)
  have hsuppG : Function.support G ⊆ tsupport ψ.toFun :=
    (Function.support_add _ _).trans (union_subset
      ((Function.support_mul_subset_left _ _).trans (subset_tsupport _))
      ((Function.support_mul_subset_left _ _).trans ((subset_tsupport _).trans
        (tsupport_iteratedPartialDeriv_subset_tsupport [0] _))))
  obtain ⟨χ, hχU, -, hχnhds, -⟩ :=
    TestFunction.exists_eq_one_on_compact hU ψ.hasCompactSupport hψU
  have hweakGlobal : HasWeakDerivativeOn (n := 1) Set.univ [0] F G :=
    CompactSupportLocalization.hasWeakDerivativeOn_univ_of_support_subset_of_cutoff_one_nhds
      hU hψU hsuppF hsuppG χ hχU hχnhds hweakFG
  have hGint : Integrable G (volume : Measure (ℝ^1)) :=
    (integrableOn_iff_integrable_of_support_subset hsuppG).mp
      ((locallyIntegrableOn_univ.mp hweakGlobal.locallyIntegrable_g).integrableOn_isCompact
        ψ.hasCompactSupport)
  -- on the interval `ψ = 1` and `∂ψ = 0`, so `F = f` and `G = g` there
  have hpoint (t : ℝ) (ht : t ∈ Set.uIcc a b) : F (e t) = f (e t) ∧ G (e t) = g (e t) := by
    have hEt : e t ∈ e '' Set.uIcc a b := ⟨t, ht, rfl⟩
    have hdψ : iteratedPartialDeriv (n := 1) [0] ψ.toFun (e t) = 0 := by
      change fderiv ℝ ψ.toFun (e t) (EuclideanSpace.single 0 1) = 0
      rw [(hψnhds _ hEt).fderiv_eq]
      simp
    simp only [F, G, hψ1 _ hEt, hdψ, one_mul, zero_mul, add_zero, and_self]
  calc ∫ t in a..b, g (e t) = ∫ t in a..b, G (e t) :=
        intervalIntegral.integral_congr fun t ht ↦ (hpoint t ht).2.symm
    _ = F (e b) - F (e a) := intervalIntegral_weakDerivative_eq_sub F G
        (ψ.contDiff.continuous.mul hf) (memLp_one_iff_integrable.mpr hGint) hweakGlobal a b
    _ = f (e b) - f (e a) := by
      rw [(hpoint a left_mem_uIcc).1, (hpoint b right_mem_uIcc).1]

end FundamentalTheorem
end SobolevSpace
