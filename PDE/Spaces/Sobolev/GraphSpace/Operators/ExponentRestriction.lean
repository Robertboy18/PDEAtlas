/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
import PDE.Analysis.MeasureTheory.Lp.CompareExp
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Exponent restriction for Sobolev data with finite-measure support

On a set `s` of finite measure, `L^p(s) ⊆ L^q(s)` for `q ≤ p`, with `‖f‖_q ≤ μ(s)^{1/q - 1/p} ‖f‖_p`
by Hölder's inequality; we take this bound from Mathlib's
`eLpNorm_le_eLpNorm_mul_rpow_measure_univ`, applied to the measure restricted to the measurable hull
of `s`. Applied to every derivative coordinate at once, this says that Sobolev graph-space data in
`WkpSpaceOn n k p Ω` whose coordinates all vanish a.e. outside one finite-measure set `s` may be
viewed in `WkpSpaceOn n k q Ω`; the weak-derivative identities survive because they are a.e.
statements. This is the local exponent-change operation used by cutoff arguments on infinite-measure
domains, where a cutoff function supplies the common finite-measure support.

The construction is bundled for linear and continuous linear operators whose
outputs share one finite-measure support, and specialised to finite-measure
domains, where all of `Ω` is taken as the support and the resulting operator
`lowerExponentOfFiniteMeasureCLM` carries the explicit norm bound
`card (DerivIndex n k)^{1/q - 1/p} · μ(Ω)^{1/q - 1/p}`.  The first factor comes
from comparing the `ℓ^p` and `ℓ^q` norms on the finite product of coordinates.

## Main definitions

* `SobolevSpace.GraphSpace.HasCoordinateSupportIn`: all coordinates vanish a.e.
  outside `s`.
* `SobolevSpace.GraphSpace.lowerExponentOfFiniteMeasureSupport`: the
  exponent-lowering map on data supported in `s`.
* `SobolevSpace.GraphSpace.lowerExponentOfFiniteMeasureSupportCLM`: the same after
  a bounded operator whose outputs share a finite-measure support.
* `SobolevSpace.GraphSpace.lowerExponentOfFiniteMeasureCLM`: continuous exponent
  restriction on a finite-measure domain.

## Main results

* `SobolevSpace.GraphSpace.lowerExponentOfFiniteMeasureSupport_apply_ae`: every
  coordinate is preserved a.e.
* `SobolevSpace.GraphSpace.norm_lowerExponentOfFiniteMeasureSupport_le`,
  `SobolevSpace.GraphSpace.norm_lowerExponentOfFiniteMeasureCLM_le`: the explicit
  norm bounds.
* `SobolevSpace.GraphSpace.lowerExponentOfFiniteMeasureCLM_refl`,
  `SobolevSpace.GraphSpace.lowerExponentOfFiniteMeasureCLM_trans`,
  `SobolevSpace.GraphSpace.lowerOrderCLM_comp_lowerExponentOfFiniteMeasureCLM`:
  functoriality in the exponent and compatibility with lowering the order.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  for Hölder's inequality and the resulting inclusion `L^p ⊆ L^q`, `q ≤ p`, on a finite measure
  space.
  <https://www.wiley.com/en-us/Real+Analysis%3A+Modern+Techniques+and+Their+Applications%2C+2nd+Edition-p-9780471317166>
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Pure and Applied Mathematics 140,
  Academic Press, 2003, Chapter 2, The Lebesgue Spaces Lp(Ω), pp. 23-58, for the inclusion
  `L^p(Ω) ⊆ L^q(Ω)`, `q ≤ p`, on domains of finite volume.
  <https://shop.elsevier.com/books/sobolev-spaces/adams/978-0-12-044143-3>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal Sobolev

/-- Canonical continuous linear identification of Sobolev graph spaces whose
exponents are equal. -/
noncomputable def WkpSpaceOn.congrExponent
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (h : p = q) (n k : ℕ) (Ω : Set (ℝ^n)) :
    W^{k,p}(Ω) ≃L[ℝ] W^{k,q}(Ω) := by
  subst q
  exact ContinuousLinearEquiv.refl ℝ (W^{k,p}(Ω))

/-- Applying `WkpSpaceOn.congrExponent` only changes the dependent exponent
index. -/
theorem WkpSpaceOn.congrExponent_apply_heq
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (h : p = q) (n k : ℕ) (Ω : Set (ℝ^n))
    (u : W^{k,p}(Ω)) :
    HEq (WkpSpaceOn.congrExponent h n k Ω u) u := by
  subst q
  rfl

/-- Changing an equal exponent preserves each Sobolev coordinate representative. -/
theorem WkpSpaceOn.coordinate_congrExponent
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (h : p = q) {n k : ℕ} {Ω : Set ℝ^n}
    (u : W^{k,p}(Ω)) (a : DerivIndex n k) :
    (wkpCoordinateCLM a (WkpSpaceOn.congrExponent h n k Ω u) : ℝ^n → ℝ) =
      (wkpCoordinateCLM a u : ℝ^n → ℝ) := by
  subst q
  rfl

/-- Transport between equal exponents preserves the graph norm exactly. -/
theorem WkpSpaceOn.norm_congrExponent
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (h : p = q) {n k : ℕ} {Ω : Set (ℝ^n)} (U : W^{k,p}(Ω)) :
    ‖WkpSpaceOn.congrExponent h n k Ω U‖ = ‖U‖ := by
  subst q
  rfl

/-- Smooth compactly supported Sobolev constructors at equal exponents are
heterogeneously equal. -/
theorem mkWkpSpaceOnOfContDiff_congrExponent
    {p q : ℝ≥0∞}
    (h : p = q) {n k : ℕ} {Ω : Set (ℝ^n)}
    (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcs : HasCompactSupport f) :
    HEq
      (mkWkpSpaceOnOfContDiff
        (n := n) (k := k) (p := p) (Ω := Ω) f hf hcs)
      (mkWkpSpaceOnOfContDiff
        (n := n) (k := k) (p := q) (Ω := Ω) f hf hcs) := by
  subst q
  rfl

variable {n k : ℕ} {p q : ℝ≥0∞} {Ω : Set (ℝ^n)}

/-- Every Sobolev graph coordinate of `U` vanishes almost everywhere outside
`s`, expressed in a representative-independent form by invariance under the
indicator of `s`. -/
def HasCoordinateSupportIn
    (s : Set (ℝ^n)) (U : W^{k,p}(Ω)) : Prop :=
  ∀ a : DerivIndex n k,
    s.indicator
        ((((U : WkpAmbientOn n k p Ω) a :
          DerivLp n p Ω) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n Ω]
        (((U : WkpAmbientOn n k p Ω) a :
          DerivLp n p Ω) : ℝ^n → ℝ)

/-- Every Sobolev graph-space value is supported in the whole ambient
space. -/
theorem hasCoordinateSupportIn_univ
    (U : W^{k,p}(Ω)) :
    HasCoordinateSupportIn Set.univ U := by
  intro a
  simp

/-- The coordinate of a Sobolev graph-space element cut off outside the set
`s`, as a plain function. -/
abbrev supportedRow
    (s : Set (ℝ^n)) (U : W^{k,p}(Ω))
    (a : DerivIndex n k) :
    ℝ^n → ℝ :=
  s.indicator
    (((U : WkpAmbientOn n k p Ω) a : DerivLp n p Ω) :
      ℝ^n → ℝ)

/-- A coordinate supported in a finite-measure set lies in every lower `Lᵠ`
space. -/
theorem supportedRow_memLp
    (hpq : q ≤ p) (s : Set (ℝ^n))
    (hs : domainMeasure n Ω s ≠ ∞)
    (U : W^{k,p}(Ω))
    (hsupp : HasCoordinateSupportIn s U)
    (a : DerivIndex n k) :
    MemLp (supportedRow s U a) q (domainMeasure n Ω) := by
  have hp :
      MemLp (supportedRow s U a) p (domainMeasure n Ω) := by
    exact
      (memLp_congr_ae (hsupp a)).mpr
        (MeasureTheory.Lp.memLp
          ((U : WkpAmbientOn n k p Ω) a))
  exact hp.mono_exponent_of_measure_support_ne_top
    (s := s) (by intro x hx; simp [supportedRow, hx]) hs hpq

/-- Lower the exponent of Sobolev graph-space data whose coordinates are
supported almost everywhere in one finite-measure set. -/
noncomputable def lowerExponentOfFiniteMeasureSupport
    (hpq : q ≤ p) (s : Set (ℝ^n))
    (hs : domainMeasure n Ω s ≠ ∞)
    (U : W^{k,p}(Ω))
    (hsupp : HasCoordinateSupportIn s U) :
    W^{k,q}(Ω) := by
  classical
  let d : DerivIndex n k → ℝ^n → ℝ :=
    fun a ↦ supportedRow s U a
  exact mkWkpSpaceOnOfWeakDerivatives
    (n := n) (k := k) (p := q) (Ω := Ω)
    (d (baseIndex n k)) d rfl
    (fun a ↦ supportedRow_memLp hpq s hs U hsupp a)
    (fun a ↦
      (hasWeakDerivativeOn_congr_ae
        (hsupp (baseIndex n k)) (hsupp a)).mpr (U.property a))

/-- Exponent restriction preserves every Sobolev graph coordinate almost
everywhere. -/
theorem lowerExponentOfFiniteMeasureSupport_apply_ae
    (hpq : q ≤ p) (s : Set (ℝ^n))
    (hs : domainMeasure n Ω s ≠ ∞)
    (U : W^{k,p}(Ω))
    (hsupp : HasCoordinateSupportIn s U)
    (a : DerivIndex n k) :
    ((((lowerExponentOfFiniteMeasureSupport hpq s hs U hsupp :
        WkpAmbientOn n k q Ω) a : DerivLp n q Ω) :
          ℝ^n → ℝ))
      =ᵐ[domainMeasure n Ω]
        (((U : WkpAmbientOn n k p Ω) a :
          DerivLp n p Ω) : ℝ^n → ℝ) := by
  exact
    (mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := k) (p := q) (Ω := Ω)
      (supportedRow s U (baseIndex n k))
      (supportedRow s U) rfl
      (fun b ↦ supportedRow_memLp hpq s hs U hsupp b)
      (fun b ↦
        (hasWeakDerivativeOn_congr_ae
          (hsupp (baseIndex n k)) (hsupp b)).mpr (U.property b))
      a).trans (hsupp a)

/-- The explicit norm bound for lowering the exponent of Sobolev graph-space
data supported in a common finite-measure set. -/
noncomputable def finiteMeasureSupportExponentRestrictionNormBound
    (n k : ℕ) (p q : ℝ≥0∞) (Ω s : Set (ℝ^n)) : ℝ :=
  ((Fintype.card (DerivIndex n k) : ℝ≥0∞) ^
      (1 / q.toReal - 1 / p.toReal)).toReal *
    (domainMeasure n Ω s ^
      (1 / q.toReal - 1 / p.toReal)).toReal

/-- The finite-measure-support exponent-restriction bound is nonnegative. -/
theorem finiteMeasureSupportExponentRestrictionNormBound_nonneg
    {s : Set (ℝ^n)} :
    0 ≤ finiteMeasureSupportExponentRestrictionNormBound n k p q Ω s :=
  mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- At equal exponents, the explicit finite-support bound is one. -/
@[simp]
theorem finiteMeasureSupportExponentRestrictionNormBound_self
    {s : Set (ℝ^n)} :
    finiteMeasureSupportExponentRestrictionNormBound n k p p Ω s = 1 := by
  simp [finiteMeasureSupportExponentRestrictionNormBound]

variable [Fact (1 ≤ p)] [Fact (1 ≤ q)]

omit [Fact (1 ≤ p)] in
private theorem norm_lowerExponentCoordinateOfFiniteMeasureSupport_le
    (hpq : q ≤ p) (s : Set (ℝ^n))
    (hs : domainMeasure n Ω s ≠ ∞)
    (U : W^{k,p}(Ω))
    (hsupp : HasCoordinateSupportIn s U)
    (a : DerivIndex n k) :
    ‖((lowerExponentOfFiniteMeasureSupport hpq s hs U hsupp :
        WkpAmbientOn n k q Ω) a)‖ ≤
      (domainMeasure n Ω s ^
        (1 / q.toReal - 1 / p.toReal)).toReal *
        ‖((U : WkpAmbientOn n k p Ω) a)‖ := by
  let u : DerivLp n p Ω := (U : WkpAmbientOn n k p Ω) a
  let v : DerivLp n q Ω :=
    (lowerExponentOfFiniteMeasureSupport hpq s hs U hsupp : WkpAmbientOn n k q Ω) a
  have hvRow : (v : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] supportedRow s U a :=
    (lowerExponentOfFiniteMeasureSupport_apply_ae hpq s hs U hsupp a).trans (hsupp a).symm
  have hraw : eLpNorm (v : ℝ^n → ℝ) q (domainMeasure n Ω) ≤
      eLpNorm (u : ℝ^n → ℝ) p (domainMeasure n Ω) *
        domainMeasure n Ω s ^ (1 / q.toReal - 1 / p.toReal) := by
    rw [eLpNorm_congr_ae hvRow, ← eLpNorm_congr_ae (hsupp a)]
    refine eLpNorm_le_eLpNorm_mul_rpow_measure_of_support_subset hpq
      (supportedRow_memLp hpq s hs U hsupp a).aestronglyMeasurable fun x hx ↦ ?_
    by_contra hxs
    exact hx (by simp [supportedRow, hxs])
  have hfinite : eLpNorm (u : ℝ^n → ℝ) p (domainMeasure n Ω) *
      domainMeasure n Ω s ^ (1 / q.toReal - 1 / p.toReal) ≠ ∞ :=
    ENNReal.mul_ne_top (MeasureTheory.Lp.eLpNorm_ne_top u)
      (ENNReal.rpow_ne_top_of_nonneg (PiLp.exponentGap_nonneg hpq) hs)
  simpa [u, v, MeasureTheory.Lp.norm_def, ENNReal.toReal_mul, mul_comm] using
    ENNReal.toReal_mono hfinite hraw

/-- Quantitative estimate for lowering the exponent of Sobolev graph-space
data supported in a common finite-measure set. -/
theorem norm_lowerExponentOfFiniteMeasureSupport_le
    (hpq : q ≤ p) (s : Set (ℝ^n))
    (hs : domainMeasure n Ω s ≠ ∞)
    (U : W^{k,p}(Ω))
    (hsupp : HasCoordinateSupportIn s U) :
    ‖lowerExponentOfFiniteMeasureSupport hpq s hs U hsupp‖ ≤
      finiteMeasureSupportExponentRestrictionNormBound n k p q Ω s * ‖U‖ := by
  let _ : MeasurableSpace (DerivIndex n k) := ⊤
  exact
    PiLp.norm_le_card_rpow_mul_of_coordinate_norm_le
      (ι := DerivIndex n k)
      (β := fun _ ↦ DerivLp n p Ω)
      (γ := fun _ ↦ DerivLp n q Ω)
      hpq
      (domainMeasure n Ω s ^
        (1 / q.toReal - 1 / p.toReal)).toReal
      ENNReal.toReal_nonneg
      (U : WkpAmbientOn n k p Ω)
      (lowerExponentOfFiniteMeasureSupport hpq s hs U hsupp :
        WkpAmbientOn n k q Ω)
      (norm_lowerExponentCoordinateOfFiniteMeasureSupport_le
        hpq s hs U hsupp)

/-! ## Operators with a common finite-measure support -/

section FiniteMeasureSupportOperator

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Lower the exponent after applying a linear operator whose outputs have
all Sobolev coordinates supported almost everywhere in one finite-measure
set. -/
noncomputable def lowerExponentOfFiniteMeasureSupportLinearMap
    (hpq : q ≤ p) (s : Set (ℝ^n))
    (hs : domainMeasure n Ω s ≠ ∞)
    (T : X →ₗ[ℝ] W^{k,p}(Ω))
    (hsupp : ∀ U, HasCoordinateSupportIn s (T U)) :
    X →ₗ[ℝ] W^{k,q}(Ω) where
  toFun U := lowerExponentOfFiniteMeasureSupport hpq s hs (T U) (hsupp U)
  map_add' U V := by
    refine Subtype.ext <| PiLp.ext fun a ↦ MeasureTheory.Lp.ext ?_
    have huv : ((((lowerExponentOfFiniteMeasureSupport hpq s hs (T (U + V)) (hsupp (U + V)) :
        WkpAmbientOn n k q Ω) a : DerivLp n q Ω) : ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω]
          ((((T U + T V : W^{k,p}(Ω)) : WkpAmbientOn n k p Ω) a : DerivLp n p Ω) : ℝ^n → ℝ) := by
      simpa only [map_add] using
        lowerExponentOfFiniteMeasureSupport_apply_ae hpq s hs (T (U + V)) (hsupp (U + V)) a
    filter_upwards [huv, lowerExponentOfFiniteMeasureSupport_apply_ae hpq s hs _ (hsupp U) a,
      lowerExponentOfFiniteMeasureSupport_apply_ae hpq s hs _ (hsupp V) a,
      MeasureTheory.Lp.coeFn_add ((T U : WkpAmbientOn n k p Ω) a) ((T V : WkpAmbientOn n k p Ω) a),
      MeasureTheory.Lp.coeFn_add
        ((lowerExponentOfFiniteMeasureSupport hpq s hs (T U) (hsupp U) : WkpAmbientOn n k q Ω) a)
        ((lowerExponentOfFiniteMeasureSupport hpq s hs (T V) (hsupp V) : WkpAmbientOn n k q Ω) a)]
      with x huvx hux hvx hsource htarget
    rw [huvx]
    change (((T U : WkpAmbientOn n k p Ω) a + (T V : WkpAmbientOn n k p Ω) a : DerivLp n p Ω) :
        ℝ^n → ℝ) x = (((lowerExponentOfFiniteMeasureSupport hpq s hs (T U) (hsupp U) :
          WkpAmbientOn n k q Ω) a + (lowerExponentOfFiniteMeasureSupport hpq s hs (T V)
            (hsupp V) : WkpAmbientOn n k q Ω) a : DerivLp n q Ω) : ℝ^n → ℝ) x
    rw [hsource, htarget, Pi.add_apply, Pi.add_apply, hux, hvx]
  map_smul' c U := by
    refine Subtype.ext <| PiLp.ext fun a ↦ MeasureTheory.Lp.ext ?_
    have hcu : ((((lowerExponentOfFiniteMeasureSupport hpq s hs (T (c • U)) (hsupp (c • U)) :
        WkpAmbientOn n k q Ω) a : DerivLp n q Ω) : ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω]
          ((((c • T U : W^{k,p}(Ω)) : WkpAmbientOn n k p Ω) a : DerivLp n p Ω) : ℝ^n → ℝ) := by
      simpa only [map_smul] using
        lowerExponentOfFiniteMeasureSupport_apply_ae hpq s hs (T (c • U)) (hsupp (c • U)) a
    filter_upwards [hcu, lowerExponentOfFiniteMeasureSupport_apply_ae hpq s hs _ (hsupp U) a,
      MeasureTheory.Lp.coeFn_smul c ((T U : WkpAmbientOn n k p Ω) a),
      MeasureTheory.Lp.coeFn_smul c
        ((lowerExponentOfFiniteMeasureSupport hpq s hs (T U) (hsupp U) : WkpAmbientOn n k q Ω) a)]
      with x hcux hux hsource htarget
    rw [hcux]
    change ((c • (T U : WkpAmbientOn n k p Ω) a : DerivLp n p Ω) : ℝ^n → ℝ) x =
      ((c • (lowerExponentOfFiniteMeasureSupport hpq s hs (T U) (hsupp U) :
        WkpAmbientOn n k q Ω) a : DerivLp n q Ω) : ℝ^n → ℝ) x
    rw [hsource, htarget, Pi.smul_apply, Pi.smul_apply, hux]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- `lowerExponentOfFiniteMeasureSupportLinearMap` evaluates to the exponent restriction of
`T U`. -/
@[simp]
theorem lowerExponentOfFiniteMeasureSupportLinearMap_apply
    (hpq : q ≤ p) (s : Set (ℝ^n))
    (hs : domainMeasure n Ω s ≠ ∞)
    (T : X →ₗ[ℝ] W^{k,p}(Ω))
    (hsupp : ∀ U, HasCoordinateSupportIn s (T U))
    (U : X) :
    lowerExponentOfFiniteMeasureSupportLinearMap hpq s hs T hsupp U =
      lowerExponentOfFiniteMeasureSupport hpq s hs (T U) (hsupp U) :=
  rfl

/-- Lower the exponent after a bounded linear operator whose outputs share
one finite-measure support. The operator norm is controlled by the
finite-measure-support exponent-restriction bound times the norm of the original
operator. -/
noncomputable def lowerExponentOfFiniteMeasureSupportCLM
    (hpq : q ≤ p) (s : Set (ℝ^n))
    (hs : domainMeasure n Ω s ≠ ∞)
    (T : X →L[ℝ] W^{k,p}(Ω))
    (hsupp : ∀ U, HasCoordinateSupportIn s (T U)) :
    X →L[ℝ] W^{k,q}(Ω) :=
  (lowerExponentOfFiniteMeasureSupportLinearMap
      hpq s hs T.toLinearMap hsupp).mkContinuous
    (finiteMeasureSupportExponentRestrictionNormBound n k p q Ω s * ‖T‖)
    (fun U ↦ by
      calc
        ‖lowerExponentOfFiniteMeasureSupport hpq s hs (T U) (hsupp U)‖
            ≤ finiteMeasureSupportExponentRestrictionNormBound n k p q Ω s *
                ‖T U‖ :=
          norm_lowerExponentOfFiniteMeasureSupport_le
            hpq s hs (T U) (hsupp U)
        _ ≤ finiteMeasureSupportExponentRestrictionNormBound n k p q Ω s *
              (‖T‖ * ‖U‖) := by
          exact mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.le_opNorm T U)
            finiteMeasureSupportExponentRestrictionNormBound_nonneg
        _ = (finiteMeasureSupportExponentRestrictionNormBound n k p q Ω s *
              ‖T‖) * ‖U‖ := by ring)

/-- `lowerExponentOfFiniteMeasureSupportCLM` evaluates to the exponent restriction of `T U`. -/
@[simp]
theorem lowerExponentOfFiniteMeasureSupportCLM_apply
    (hpq : q ≤ p) (s : Set (ℝ^n))
    (hs : domainMeasure n Ω s ≠ ∞)
    (T : X →L[ℝ] W^{k,p}(Ω))
    (hsupp : ∀ U, HasCoordinateSupportIn s (T U))
    (U : X) :
    lowerExponentOfFiniteMeasureSupportCLM hpq s hs T hsupp U =
      lowerExponentOfFiniteMeasureSupport hpq s hs (T U) (hsupp U) :=
  rfl

/-- Pointwise norm bound for exponent restriction after a bounded operator
with common finite-measure support. -/
theorem norm_lowerExponentOfFiniteMeasureSupportCLM_apply_le
    (hpq : q ≤ p) (s : Set (ℝ^n))
    (hs : domainMeasure n Ω s ≠ ∞)
    (T : X →L[ℝ] W^{k,p}(Ω))
    (hsupp : ∀ U, HasCoordinateSupportIn s (T U))
    (U : X) :
    ‖lowerExponentOfFiniteMeasureSupportCLM hpq s hs T hsupp U‖ ≤
      (finiteMeasureSupportExponentRestrictionNormBound n k p q Ω s * ‖T‖) *
        ‖U‖ := by
  calc
    ‖lowerExponentOfFiniteMeasureSupportCLM hpq s hs T hsupp U‖
        = ‖lowerExponentOfFiniteMeasureSupport hpq s hs (T U) (hsupp U)‖ := by
          rw [lowerExponentOfFiniteMeasureSupportCLM_apply]
    _ ≤ finiteMeasureSupportExponentRestrictionNormBound n k p q Ω s *
          ‖T U‖ :=
      norm_lowerExponentOfFiniteMeasureSupport_le hpq s hs (T U) (hsupp U)
    _ ≤ finiteMeasureSupportExponentRestrictionNormBound n k p q Ω s *
          (‖T‖ * ‖U‖) := by
      exact mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.le_opNorm T U)
        finiteMeasureSupportExponentRestrictionNormBound_nonneg
    _ = (finiteMeasureSupportExponentRestrictionNormBound n k p q Ω s * ‖T‖) *
          ‖U‖ := by ring

/-- Operator-norm bound for exponent restriction after a bounded operator
with common finite-measure support. -/
theorem norm_lowerExponentOfFiniteMeasureSupportCLM_le
    (hpq : q ≤ p) (s : Set (ℝ^n))
    (hs : domainMeasure n Ω s ≠ ∞)
    (T : X →L[ℝ] W^{k,p}(Ω))
    (hsupp : ∀ U, HasCoordinateSupportIn s (T U)) :
    ‖lowerExponentOfFiniteMeasureSupportCLM hpq s hs T hsupp‖ ≤
      finiteMeasureSupportExponentRestrictionNormBound n k p q Ω s * ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg finiteMeasureSupportExponentRestrictionNormBound_nonneg
      (norm_nonneg T))
    (norm_lowerExponentOfFiniteMeasureSupportCLM_apply_le hpq s hs T hsupp)

end FiniteMeasureSupportOperator

/-! ## Finite-measure domains -/

variable [IsFiniteMeasure (domainMeasure n Ω)]

/-- The explicit finite-volume bound for lowering the exponent on
`WkpSpaceOn n k p Ω`. -/
noncomputable def finiteMeasureExponentRestrictionNormBound
    (n k : ℕ) (p q : ℝ≥0∞) (Ω : Set (ℝ^n)) : ℝ :=
  finiteMeasureSupportExponentRestrictionNormBound
    n k p q Ω Set.univ

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [IsFiniteMeasure (domainMeasure n Ω)] in
/-- The finite-measure exponent-restriction bound is nonnegative. -/
theorem finiteMeasureExponentRestrictionNormBound_nonneg :
    0 ≤ finiteMeasureExponentRestrictionNormBound n k p q Ω :=
  finiteMeasureSupportExponentRestrictionNormBound_nonneg

omit [Fact (1 ≤ p)] [IsFiniteMeasure (domainMeasure n Ω)] in
/-- At equal exponents, the explicit exponent-restriction bound is one. -/
@[simp]
theorem finiteMeasureExponentRestrictionNormBound_self :
    finiteMeasureExponentRestrictionNormBound n k p p Ω = 1 := by
  exact finiteMeasureSupportExponentRestrictionNormBound_self

/-- Lower the exponent of Sobolev graph-space data on a finite-measure
domain. This is the domain-level specialization of
`lowerExponentOfFiniteMeasureSupport`, with the whole ambient space as the common
finite-measure support. -/
noncomputable def lowerExponentOfFiniteMeasure
    (hpq : q ≤ p) (U : W^{k,p}(Ω)) :
    W^{k,q}(Ω) :=
  lowerExponentOfFiniteMeasureSupport hpq Set.univ
    (measure_ne_top (domainMeasure n Ω) Set.univ) U
    (hasCoordinateSupportIn_univ U)

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- Exponent restriction on a finite-measure domain preserves every Sobolev
graph coordinate almost everywhere. -/
theorem lowerExponentOfFiniteMeasure_apply_ae
    (hpq : q ≤ p) (U : W^{k,p}(Ω))
    (a : DerivIndex n k) :
    ((((lowerExponentOfFiniteMeasure hpq U :
        WkpAmbientOn n k q Ω) a : DerivLp n q Ω) :
          ℝ^n → ℝ))
      =ᵐ[domainMeasure n Ω]
        (((U : WkpAmbientOn n k p Ω) a :
          DerivLp n p Ω) : ℝ^n → ℝ) := by
  exact lowerExponentOfFiniteMeasureSupport_apply_ae hpq Set.univ
    (measure_ne_top (domainMeasure n Ω) Set.univ) U
    (hasCoordinateSupportIn_univ U) a

/-- Quantitative finite-volume estimate for exponent restriction on Sobolev
graph spaces. -/
theorem norm_lowerExponentOfFiniteMeasure_le
    (hpq : q ≤ p) (U : W^{k,p}(Ω)) :
    ‖lowerExponentOfFiniteMeasure hpq U‖ ≤
      finiteMeasureExponentRestrictionNormBound n k p q Ω * ‖U‖ := by
  simpa [lowerExponentOfFiniteMeasure,
    finiteMeasureExponentRestrictionNormBound] using
      norm_lowerExponentOfFiniteMeasureSupport_le
        hpq Set.univ
        (measure_ne_top (domainMeasure n Ω) Set.univ) U
        (hasCoordinateSupportIn_univ U)

/-- Continuous exponent restriction on any finite-measure domain, with the
explicit finite-volume bound `finiteMeasureExponentRestrictionNormBound`. -/
noncomputable def lowerExponentOfFiniteMeasureCLM
    (hpq : q ≤ p) :
    W^{k,p}(Ω) →L[ℝ] W^{k,q}(Ω) :=
  lowerExponentOfFiniteMeasureSupportCLM hpq Set.univ
    (measure_ne_top (domainMeasure n Ω) Set.univ)
    (ContinuousLinearMap.id ℝ (W^{k,p}(Ω)))
    hasCoordinateSupportIn_univ

/-- `lowerExponentOfFiniteMeasureCLM` evaluates to `lowerExponentOfFiniteMeasure`. -/
@[simp]
theorem lowerExponentOfFiniteMeasureCLM_apply
    (hpq : q ≤ p) (U : W^{k,p}(Ω)) :
    lowerExponentOfFiniteMeasureCLM hpq U =
      lowerExponentOfFiniteMeasure hpq U :=
  rfl

/-- The continuous exponent-restriction operator satisfies the explicit
finite-volume bound pointwise. -/
theorem norm_lowerExponentOfFiniteMeasureCLM_apply_le
    (hpq : q ≤ p) (U : W^{k,p}(Ω)) :
    ‖lowerExponentOfFiniteMeasureCLM hpq U‖ ≤
      finiteMeasureExponentRestrictionNormBound n k p q Ω * ‖U‖ := by
  simpa only [lowerExponentOfFiniteMeasureCLM_apply] using
    norm_lowerExponentOfFiniteMeasure_le hpq U

/-- Operator-norm bound for finite-measure exponent restriction. -/
theorem norm_lowerExponentOfFiniteMeasureCLM_le
    (hpq : q ≤ p) :
    ‖lowerExponentOfFiniteMeasureCLM
        (n := n) (k := k) (Ω := Ω) hpq‖ ≤
      finiteMeasureExponentRestrictionNormBound n k p q Ω :=
  ContinuousLinearMap.opNorm_le_bound _
    finiteMeasureExponentRestrictionNormBound_nonneg
    (norm_lowerExponentOfFiniteMeasureCLM_apply_le hpq)

/-- Restriction to the same exponent is the identity operator. -/
@[simp]
theorem lowerExponentOfFiniteMeasureCLM_refl :
    lowerExponentOfFiniteMeasureCLM
        (n := n) (k := k) (Ω := Ω) (p := p) (q := p) le_rfl =
      ContinuousLinearMap.id ℝ (W^{k,p}(Ω)) := by
  apply ContinuousLinearMap.ext
  intro U
  apply Subtype.ext
  refine PiLp.ext fun a ↦ MeasureTheory.Lp.ext ?_
  simpa only [lowerExponentOfFiniteMeasureCLM_apply,
    ContinuousLinearMap.id_apply] using
      lowerExponentOfFiniteMeasure_apply_ae (le_refl p) U a

/-- Lowering the exponent in two stages is the direct exponent-restriction operator. -/
theorem lowerExponentOfFiniteMeasureCLM_trans
    {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hrq : r ≤ q) (hqp : q ≤ p) :
    (lowerExponentOfFiniteMeasureCLM
        (n := n) (k := k) (Ω := Ω) (p := q) (q := r) hrq).comp
        (lowerExponentOfFiniteMeasureCLM
          (n := n) (k := k) (Ω := Ω) (p := p) (q := q) hqp) =
      lowerExponentOfFiniteMeasureCLM
        (n := n) (k := k) (Ω := Ω) (p := p) (q := r)
        (hrq.trans hqp) := by
  apply ContinuousLinearMap.ext
  intro U
  apply Subtype.ext
  refine PiLp.ext fun a ↦ MeasureTheory.Lp.ext ?_
  have hqr :=
    lowerExponentOfFiniteMeasure_apply_ae hrq
      (lowerExponentOfFiniteMeasure hqp U) a
  have hpq := lowerExponentOfFiniteMeasure_apply_ae hqp U a
  have hpr :=
    lowerExponentOfFiniteMeasure_apply_ae (hrq.trans hqp) U a
  simpa only [ContinuousLinearMap.comp_apply,
    lowerExponentOfFiniteMeasureCLM_apply] using
      hqr.trans (hpq.trans hpr.symm)

/-- Lowering Sobolev order commutes with finite-measure exponent restriction. -/
theorem lowerOrderCLM_comp_lowerExponentOfFiniteMeasureCLM
    {m : ℕ} (hkm : k ≤ m) (hpq : q ≤ p) :
    (lowerOrderCLM
        (n := n) (p := q) (Ω := Ω) hkm).comp
        (lowerExponentOfFiniteMeasureCLM
          (n := n) (k := m) (Ω := Ω) hpq) =
      (lowerExponentOfFiniteMeasureCLM
        (n := n) (k := k) (Ω := Ω) hpq).comp
        (lowerOrderCLM
          (n := n) (p := p) (Ω := Ω) hkm) := by
  apply ContinuousLinearMap.ext
  intro U
  apply Subtype.ext
  refine PiLp.ext fun a ↦ MeasureTheory.Lp.ext ?_
  have hleft :=
    lowerExponentOfFiniteMeasure_apply_ae hpq U (a.castOrder hkm)
  have hright :=
    lowerExponentOfFiniteMeasure_apply_ae hpq
      (lowerOrderCLM
        (n := n) (p := p) (Ω := Ω) hkm U) a
  simpa only [ContinuousLinearMap.comp_apply,
    lowerExponentOfFiniteMeasureCLM_apply, lowerOrderCLM_apply] using
      hleft.trans hright.symm

end SobolevSpace.GraphSpace
