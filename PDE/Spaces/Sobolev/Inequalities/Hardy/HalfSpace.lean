/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.Normal
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import PDE.Spaces.Sobolev.Calculus.Slicing.NormalIntegral
import PDE.Spaces.Sobolev.Inequalities.Hardy.Lp
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Support

/-!
# Hardy inequality on the upper half-space

For `p > 1` and a `C¹` function `f` with compact support inside the upper half-space
`{x : xₙ > 0}`,

`∫ |f(x)|^p xₙ^{-p} dx ≤ (p/(p-1))^p ∫ |∂ₙ f(x)|^p dx`,

with the same constant as in one dimension. The proof is Fubini: freeze the tangential
variables `x'`, apply the one-dimensional inequality of `Hardy.Lp` to `t ↦ f(x', t)`, which is
`C¹` with compact support in `(0, ∞)`, and integrate in `x'`. Since the distance from `x` to the
boundary of the half-space is `xₙ`, the inequality also holds with the weight
`dist(x, ∂)^{-p}`, which is the form used by the chart-local estimates on `C¹` domains.

The dimension is written both as `n + 1` (tangential dimension `n`, convenient for the slicing)
and as an arbitrary `n` with `[Fact (0 < n)]` (the form used on domains).

## Main results

* `memLp_div_last_of_hasCompactSupport`: `f / xₙ ∈ Lᵖ` for continuous compactly supported `f`
  with support in the half-space.
* `hardy_upperHalfSpace_lp_of_hasCompactSupport`,
  `hardy_upperHalfSpace_infDist_lp_of_hasCompactSupport`: the inequality on `ℝ^{n+1}`, with
  the normal-coordinate weight and with the distance-to-boundary weight.
* `hardy_upperHalfSpace_lp_of_hasCompactSupport_of_posDim`,
  `hardy_upperHalfSpace_infDist_lp_of_hasCompactSupport_of_posDim`: the same in an arbitrary
  positive dimension, indexed through `PDE.Common.lastIndex`.

## References

* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, 2nd ed., Cambridge Mathematical
  Library, Cambridge University Press, 1988, Chapter IX, for the one-dimensional Hardy inequality.
-/

@[expose] public section

open PDE (partialDeriv)

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace.Hardy

open MeasureTheory Set
open SobolevSpace.Trace.HalfSpace

variable {n : ℕ}

/--
Division by the positive normal coordinate preserves `Lᵖ` integrability for a
continuous compactly supported function whose support lies in the upper
half-space.
-/
theorem memLp_div_last_of_hasCompactSupport
    [Fact (0 < n)] {f : ℝ^n → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : Continuous f) (hcompact : HasCompactSupport f)
    (hsupport : tsupport f ⊆ HalfSpace.upper n) :
    MemLp
      (fun x ↦ f x / x (PDE.Common.lastIndex (n := n)))
      (ENNReal.ofReal p) volume := by
  have hlast : Continuous fun x : ℝ^n ↦ x (PDE.Common.lastIndex (n := n)) :=
    (EuclideanSpace.proj _).continuous
  have hpowsupp : Function.support (fun x ↦ |f x / x (PDE.Common.lastIndex (n := n))| ^ p) ⊆
      tsupport f := fun x hx ↦
    subset_tsupport f fun hfx ↦ hx (by simp [hfx, Real.zero_rpow hp.ne'])
  have hqm : AEStronglyMeasurable (fun x ↦ f x / x (PDE.Common.lastIndex (n := n))) volume :=
    (hf.measurable.div hlast.measurable).aestronglyMeasurable
  have hpowint : Integrable fun x ↦ |f x / x (PDE.Common.lastIndex (n := n))| ^ p :=
    (integrableOn_iff_integrable_of_support_subset hpowsupp).1 <|
      ((hf.continuousOn.div hlast.continuousOn fun x hx ↦ (hsupport hx).ne').abs.rpow_const
        fun _ _ ↦ Or.inr hp.le).integrableOn_compact hcompact
  refine (integrable_norm_rpow_iff hqm
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top).1 ?_
  simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using hpowint

/--
The `Lᵖ` Hardy inequality on the upper half-space for smooth compactly
supported functions, written using the positive normal coordinate.
-/
theorem hardy_upperHalfSpace_lp_of_hasCompactSupport
    {f : ℝ^(n + 1) → ℝ} {p : ℝ} (hp : 1 < p)
    (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f)
    (hsupport :
      tsupport f ⊆
        (@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩)) :
    (∫ x in (@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩),
        |f x| ^ p * (x (Fin.last n)) ^ (-p)) ≤
      (p / (p - 1)) ^ p *
        ∫ x in (@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩),
          |(∂[Fin.last n] f) x| ^ p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  set F : ℝ^(n + 1) → ℝ := fun x ↦ |f x| ^ p * (x (Fin.last n)) ^ (-p)
  set G : ℝ^(n + 1) → ℝ := fun x ↦ |(∂[Fin.last n] f) x| ^ p
  have hFcont : ContinuousOn F (tsupport f) :=
    (hf.continuous.abs.rpow_const fun _ ↦ Or.inr hp0.le).continuousOn.mul <|
      (EuclideanSpace.proj (Fin.last n)).continuous.continuousOn.rpow_const fun x hx ↦
        Or.inl (hsupport hx).ne'
  have hFsupp : Function.support F ⊆ tsupport f := fun x hx ↦
    subset_tsupport f fun hfx ↦ hx (by simp [F, hfx, Real.zero_rpow hp0.ne'])
  have hFprod := (integrable_comp_joinTangentialNormal_iff_integrableOn_upper F).2
    ((integrableOn_iff_integrable_of_support_subset hFsupp).1
      (hFcont.integrableOn_compact hcompact)).integrableOn
  have hGint : Integrable G := Continuous.integrable_of_hasCompactSupport
    ((hf.continuous_partialDeriv _).abs.rpow_const fun _ ↦ Or.inr hp0.le)
    ((hcompact.partialDeriv _).abs.rpow_const hp0.ne')
  have hGprod :=
    (integrable_comp_joinTangentialNormal_iff_integrableOn_upper G).2 hGint.integrableOn
  -- the one-dimensional inequality on each normal line
  have hslice (y : ℝ^n) : ∫ t, F (joinTangentialNormal (y, t)) ∂positiveNormalMeasure ≤
      (p / (p - 1)) ^ p * ∫ t, G (joinTangentialNormal (y, t)) ∂positiveNormalMeasure := by
    have hline : Continuous fun s : ℝ ↦ joinTangentialNormal (y, s) := by
      rw [funext (joinTangentialNormal_eq_base_add_normal y)]
      exact continuous_const.add (normalAxisContinuousLinearMap (n := n)).continuous
    have h := hardy_Ioi_lp_of_hasCompactSupport hp (normalSlice_contDiff hf y)
      (normalSlice_hasCompactSupport hcompact y) fun t ht ↦ by
        have h : 0 < joinTangentialNormal (y, t) (Fin.last n) :=
          hsupport (tsupport_comp_subset_preimage f hline ht)
        simpa using h
    simp_rw [deriv_normalSlice hf y] at h
    simpa [positiveNormalMeasure, F, G, normalSlice, normalDerivativeInSplit] using h
  rw [← integral_joinTangentialNormal_eq_integral_upper F,
    ← integral_joinTangentialNormal_eq_integral_upper G, integral_prod _ hFprod,
    integral_prod _ hGprod, ← integral_const_mul]
  exact integral_mono hFprod.integral_prod_left (hGprod.integral_prod_left.const_mul _) hslice

/--
The `Lᵖ` Hardy inequality on the upper half-space, written using the
exact distance to its topological boundary.
-/
theorem hardy_upperHalfSpace_infDist_lp_of_hasCompactSupport
    {f : ℝ^(n + 1) → ℝ} {p : ℝ} (hp : 1 < p)
    (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f)
    (hsupport :
      tsupport f ⊆
        (@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩)) :
    (∫ x in (@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩),
        |f x| ^ p *
          Metric.infDist x
            (frontier
              (@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩)) ^ (-p)) ≤
      (p / (p - 1)) ^ p *
        ∫ x in (@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩),
          |(∂[Fin.last n] f) x| ^ p := by
  refine (le_of_eq (setIntegral_congr_fun (@HalfSpace.measurableSet_upper (n + 1) _)
    fun x hx ↦ ?_)).trans (hardy_upperHalfSpace_lp_of_hasCompactSupport hp hf hcompact hsupport)
  simp only [@HalfSpace.infDist_frontier_upper_eq_last (n + 1) _ x hx]
  rfl

/--
The smooth upper-half-space Hardy inequality in an arbitrary positive
ambient dimension, written using the canonical last coordinate.
-/
theorem hardy_upperHalfSpace_lp_of_hasCompactSupport_of_posDim
    {n : ℕ} [Fact (0 < n)] {f : ℝ^n → ℝ} {p : ℝ} (hp : 1 < p)
    (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f)
    (hsupport : tsupport f ⊆ HalfSpace.upper n) :
    (∫ x in HalfSpace.upper n,
        |f x| ^ p *
          (x (PDE.Common.lastIndex (n := n))) ^ (-p)) ≤
      (p / (p - 1)) ^ p *
        ∫ x in HalfSpace.upper n,
          |(∂[PDE.Common.lastIndex (n := n)] f) x| ^ p := by
  cases n with
  | zero =>
      exact (Nat.not_lt_zero 0 Fact.out).elim
  | succ m =>
      have hlast :
          PDE.Common.lastIndex (n := m + 1) = Fin.last m := by
        apply Fin.ext
        simp [PDE.Common.lastIndex]
      rw [hlast]
      exact
        hardy_upperHalfSpace_lp_of_hasCompactSupport
          (n := m) hp hf hcompact hsupport

/--
The distance-to-boundary form of the smooth upper-half-space Hardy
inequality in an arbitrary positive ambient dimension.
-/
theorem hardy_upperHalfSpace_infDist_lp_of_hasCompactSupport_of_posDim
    {n : ℕ} [Fact (0 < n)] {f : ℝ^n → ℝ} {p : ℝ} (hp : 1 < p)
    (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f)
    (hsupport : tsupport f ⊆ HalfSpace.upper n) :
    (∫ x in HalfSpace.upper n,
        |f x| ^ p *
          Metric.infDist x (frontier (HalfSpace.upper n)) ^ (-p)) ≤
      (p / (p - 1)) ^ p *
        ∫ x in HalfSpace.upper n,
          |(∂[PDE.Common.lastIndex (n := n)] f) x| ^ p := by
  cases n with
  | zero =>
      exact (Nat.not_lt_zero 0 Fact.out).elim
  | succ m =>
      have hlast :
          PDE.Common.lastIndex (n := m + 1) = Fin.last m := by
        apply Fin.ext
        simp [PDE.Common.lastIndex]
      rw [hlast]
      exact
        hardy_upperHalfSpace_infDist_lp_of_hasCompactSupport
          (n := m) hp hf hcompact hsupport

end SobolevSpace.Hardy
