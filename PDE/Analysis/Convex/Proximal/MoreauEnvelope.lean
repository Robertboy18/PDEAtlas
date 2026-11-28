/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Convex.Differentiable.ContinuousSupport
public import PDE.Analysis.Convex.Extended.Separation
public import PDE.Analysis.Convex.Proximal.Yosida.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Sequences

/-!
# The Moreau envelope of a convex function

## Motivation

How can a convex function that is not differentiable be approximated from below by convex
functions that are, with a formula for the gradient?

## The idea

For `lambda > 0` put `M(w) = inf_u (f(u) + ‖u - w‖² / (2 lambda))`. When `f` is convex and lower
semicontinuous on a Hilbert space the infimum is attained at one point, the proximal point
`J(w)`, and `A(w) = (w - J(w)) / lambda` is a subgradient of `f` at `J(w)`. Comparing the values
at two points with this subgradient gives `M(y) ≥ M(x) + ⟪A(x), y - x⟫`: the envelope has a
supporting plane at every point, with a slope `A(x)` that is Lipschitz in `x`. A function with a
continuous field of supporting planes is differentiable, so `M` is convex and differentiable with
gradient `A`. Taking `u = w` in the infimum gives `M ≤ f`, a larger `lambda` gives a smaller
envelope, and `M(w) → f(w)` as `lambda → 0` because the proximal point tends to `w`.

In finite dimensions the proximal point also depends continuously on the function: for a jointly
continuous family `G(s, u)`, convex in `u` and bounded below, the proximal points at a fixed `w`
stay bounded, every limit point minimizes the limiting problem, and the minimizer is unique.

## Main results

All results are for all convex lower semicontinuous `f : H → ℝ` on a real Hilbert space `H`,
all `lambda > 0` and all points.

* `moreauEnvelope_eq`, `moreauEnvelope_le_self`, `le_moreauEnvelope`: the infimum is attained at
  the proximal point, `M ≤ f`, and a lower bound of `f` is a lower bound of `M`.
* `moreauEnvelope_add_inner_le`: the supporting inequality `M(x) + ⟪A(x), y - x⟫ ≤ M(y)`.
* `hasFDerivAt_moreauEnvelope`, `convexOn_moreauEnvelope`: `M` is differentiable with gradient
  `A`, and convex.
* `moreauEnvelope_antitone`, `tendsto_moreauEnvelope`: `M` decreases in `lambda` and tends to `f`
  as `lambda → 0`.
* `continuous_proximalPoint_param`, `continuous_moreauEnvelope_param`,
  `continuous_moreauGradient_param` (all jointly continuous families that are convex in the
  second variable and bounded below, on a finite-dimensional space): continuity in the parameter.
* `moreauEnvelope_eq_iInf_of_denseRange` (all continuous `f` with the infimum finite): the
  infimum may be taken over a dense family.

## Relations

* `proximalPoint` is `PDE.Analysis.Convex.resolvent` and `moreauGradient` is
  `PDE.Analysis.Convex.yosidaApproximation` for the real function seen as an extended one; the
  proofs here use `resolvent_residual_mem_subdifferential`, `minimizes_proximalEnergy_iff`,
  `existsUnique_minimizer_proximalEnergy` and `lipschitzWith_yosidaApproximation`.
* `hasFDerivAt_moreauEnvelope` is `PDE.Analysis.hasFDerivAt_of_continuous_support` applied to
  `moreauEnvelope_add_inner_le`, and `convexOn_moreauEnvelope` follows from the same inequality.
* `PDE.Elliptic.Semilinear.convexGradientMoreauEnvelope` is the envelope of a differentiable
  convex function, written with its gradient resolvent.
* `PDE.CalculusOfVariations.lintegral_le_liminf_of_tendsto_ae_weak_of_continuous_convex_gradient`
  uses the envelope in the gradient variable to drop differentiability from the lower
  semicontinuity theorem for integrals.

## What stays open

Continuity in the parameter in infinite dimensions, where bounded sequences need not have
convergent subsequences.

## References

* J.-J. Moreau, *Proximité et dualité dans un espace hilbertien*, Bull. Soc. Math. France 93
  (1965), 273-299: 3.a (the minimum is attained at one point), 7.c (the envelope as an
  infimal convolution) and 7.d (Fréchet differentiability, with the gradient `w - J(w)` for the
  parameter one). <https://doi.org/10.24033/bsmf.1625>
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Analysis.Convex

/-- A lower semicontinuous real function is lower semicontinuous as an extended function. -/
theorem lowerSemicontinuous_coeReal {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hlsc : LowerSemicontinuous f) : LowerSemicontinuous (fun u ↦ (f u : EReal)) :=
  continuous_coe_real_ereal.comp_lowerSemicontinuous hlsc EReal.coe_strictMono.monotone

section Normed

variable {H : Type*} [NormedAddCommGroup H]

/-- The Moreau envelope of `f` with parameter `lambda` at `w`:
`inf_u (f(u) + ‖u - w‖² / (2 lambda))`. -/
def moreauEnvelope (f : H → ℝ) (lambda : ℝ) (w : H) : ℝ :=
  ⨅ u, f u + quadraticPenalty lambda w u

/-- For a continuous function whose penalized values are bounded below, the infimum that defines
the Moreau envelope may be taken over a dense family. No convexity is needed. -/
theorem moreauEnvelope_eq_iInf_of_denseRange {f : H → ℝ} {lambda : ℝ} {w : H} {ι : Type*}
    {d : ι → H} (hd : DenseRange d) (hfc : Continuous f)
    (hbdd : BddBelow (range fun u ↦ f u + quadraticPenalty lambda w u)) :
    moreauEnvelope f lambda w = ⨅ i, f (d i) + quadraticPenalty lambda w (d i) := by
  have : Nonempty ι := hd.nonempty
  have hbdd' : BddBelow (range fun i ↦ f (d i) + quadraticPenalty lambda w (d i)) :=
    hbdd.mono (by rintro _ ⟨i, rfl⟩; exact ⟨d i, rfl⟩)
  apply le_antisymm
  · exact le_ciInf fun i ↦ ciInf_le hbdd (d i)
  · refine le_ciInf fun u ↦ le_of_forall_pos_lt_add fun ε hε ↦ ?_
    -- a point of the dense family has a penalized value within `ε` of the one at `u`
    have hopen : IsOpen {v | f v + quadraticPenalty lambda w v <
        f u + quadraticPenalty lambda w u + ε} :=
      isOpen_lt (hfc.add (continuous_quadraticPenalty lambda w)) continuous_const
    obtain ⟨i, hi⟩ := hd.exists_mem_open hopen ⟨u, by simpa using hε⟩
    exact (ciInf_le hbdd' i).trans_lt hi

end Normed

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section Complete

variable [CompleteSpace H]

/-- The proximal point of a convex lower semicontinuous real function: the resolvent of its
subdifferential at `w`, which is the minimizer of `u ↦ f(u) + ‖u - w‖² / (2 lambda)`. -/
def proximalPoint (f : H → ℝ) (hf : ConvexOn ℝ univ f) (hlsc : LowerSemicontinuous f)
    (lambda : ℝ) (hlambda : 0 < lambda) (w : H) : H :=
  resolvent (fun u ↦ (f u : EReal)) (isProper_coeReal f) (convex_realEpigraph_coeReal hf)
    (lowerSemicontinuous_coeReal hlsc) lambda hlambda w

/-- The gradient of the Moreau envelope: `(w - J(w)) / lambda` for the proximal point `J(w)`.
It is the Yosida approximation of the subdifferential of `f`. -/
def moreauGradient (f : H → ℝ) (hf : ConvexOn ℝ univ f) (hlsc : LowerSemicontinuous f)
    (lambda : ℝ) (hlambda : 0 < lambda) (w : H) : H :=
  lambda⁻¹ • (w - proximalPoint f hf hlsc lambda hlambda w)

variable {f : H → ℝ} (hf : ConvexOn ℝ univ f) (hlsc : LowerSemicontinuous f)
  {lambda : ℝ} (hlambda : 0 < lambda)

/-- The proximal point minimizes the penalized function. -/
theorem proximalPoint_isMin (w u : H) :
    f (proximalPoint f hf hlsc lambda hlambda w) +
        quadraticPenalty lambda w (proximalPoint f hf hlsc lambda hlambda w) ≤
      f u + quadraticPenalty lambda w u := by
  have h := (minimizes_proximalEnergy_iff (isProper_coeReal f)
    (convex_realEpigraph_coeReal hf) hlambda).2
    (resolvent_residual_mem_subdifferential (isProper_coeReal f)
      (convex_realEpigraph_coeReal hf) (lowerSemicontinuous_coeReal hlsc) hlambda w) u
  simp only [proximalEnergy, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  exact h

/-- A minimizer of the penalized function is the proximal point. -/
theorem eq_proximalPoint_of_isMin {a w : H}
    (ha : ∀ u, f a + quadraticPenalty lambda w a ≤ f u + quadraticPenalty lambda w u) :
    a = proximalPoint f hf hlsc lambda hlambda w := by
  obtain ⟨u₀, -, huniq⟩ := existsUnique_minimizer_proximalEnergy (isProper_coeReal f)
    (convex_realEpigraph_coeReal hf) (lowerSemicontinuous_coeReal hlsc) hlambda w
  have h1 := huniq a fun z ↦ by
    simp only [proximalEnergy, ← EReal.coe_add, EReal.coe_le_coe_iff]
    exact ha z
  have h2 := huniq (proximalPoint f hf hlsc lambda hlambda w) fun z ↦ by
    simp only [proximalEnergy, ← EReal.coe_add, EReal.coe_le_coe_iff]
    exact proximalPoint_isMin hf hlsc hlambda w z
  exact h1.trans h2.symm

/-- The gradient of the envelope at `w` is a subgradient of `f` at the proximal point. -/
theorem proximalPoint_add_inner_le (w u : H) :
    f (proximalPoint f hf hlsc lambda hlambda w) +
        inner ℝ (moreauGradient f hf hlsc lambda hlambda w)
          (u - proximalPoint f hf hlsc lambda hlambda w) ≤ f u := by
  have h := resolvent_residual_mem_subdifferential (isProper_coeReal f)
    (convex_realEpigraph_coeReal hf) (lowerSemicontinuous_coeReal hlsc) hlambda w u
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h
  exact h

/-- The proximal point and the gradient of the envelope decompose the identity. This is
`resolvent_add_smul_yosidaApproximation` for a real-valued function. -/
theorem proximalPoint_add_smul_moreauGradient (w : H) :
    proximalPoint f hf hlsc lambda hlambda w +
      lambda • moreauGradient f hf hlsc lambda hlambda w = w :=
  resolvent_add_smul_yosidaApproximation (isProper_coeReal f) (convex_realEpigraph_coeReal hf)
    (lowerSemicontinuous_coeReal hlsc) hlambda w

/-- The gradient of the envelope is continuous: it is Lipschitz with constant `1 / lambda`. -/
theorem continuous_moreauGradient :
    Continuous (moreauGradient f hf hlsc lambda hlambda) :=
  (lipschitzWith_yosidaApproximation (isProper_coeReal f) (convex_realEpigraph_coeReal hf)
    (lowerSemicontinuous_coeReal hlsc) hlambda).continuous

include hf hlsc hlambda in
/-- The penalized values are bounded below, by the value at the proximal point. -/
theorem bddBelow_range_add_quadraticPenalty (w : H) :
    BddBelow (range fun u ↦ f u + quadraticPenalty lambda w u) :=
  ⟨_, by rintro _ ⟨u, rfl⟩; exact proximalPoint_isMin hf hlsc hlambda w u⟩

/-- The Moreau envelope is the penalized value at the proximal point. -/
theorem moreauEnvelope_eq (w : H) :
    moreauEnvelope f lambda w = f (proximalPoint f hf hlsc lambda hlambda w) +
      quadraticPenalty lambda w (proximalPoint f hf hlsc lambda hlambda w) :=
  le_antisymm (ciInf_le (bddBelow_range_add_quadraticPenalty hf hlsc hlambda w) _)
    (le_ciInf fun u ↦ proximalPoint_isMin hf hlsc hlambda w u)

include hf hlsc hlambda in
/-- The Moreau envelope lies below every penalized value. -/
theorem moreauEnvelope_le (w u : H) :
    moreauEnvelope f lambda w ≤ f u + quadraticPenalty lambda w u :=
  ciInf_le (bddBelow_range_add_quadraticPenalty hf hlsc hlambda w) u

include hf hlsc hlambda in
/-- The Moreau envelope lies below the function. -/
theorem moreauEnvelope_le_self (w : H) : moreauEnvelope f lambda w ≤ f w := by
  simpa [quadraticPenalty] using moreauEnvelope_le hf hlsc hlambda w w

include hf hlsc hlambda in
/-- A lower bound of the function is a lower bound of its Moreau envelope. -/
theorem le_moreauEnvelope {c : ℝ} (hc : ∀ u, c ≤ f u) (w : H) :
    c ≤ moreauEnvelope f lambda w := by
  rw [moreauEnvelope_eq hf hlsc hlambda w]
  have h1 := hc (proximalPoint f hf hlsc lambda hlambda w)
  have h2 : 0 ≤ quadraticPenalty lambda w (proximalPoint f hf hlsc lambda hlambda w) := by
    unfold quadraticPenalty
    positivity
  linarith

/-- The penalty at the proximal point is `lambda / 2` times the squared norm of the gradient
of the envelope. -/
theorem quadraticPenalty_proximalPoint (w : H) :
    quadraticPenalty lambda w (proximalPoint f hf hlsc lambda hlambda w) =
      lambda / 2 * ‖moreauGradient f hf hlsc lambda hlambda w‖ ^ 2 := by
  have h : proximalPoint f hf hlsc lambda hlambda w - w =
      -(lambda • moreauGradient f hf hlsc lambda hlambda w) := by
    rw [moreauGradient, smul_inv_smul₀ hlambda.ne']
    abel
  rw [quadraticPenalty, h, norm_neg, norm_smul, Real.norm_of_nonneg hlambda.le, mul_pow]
  field_simp

/-- The supporting inequality of the Moreau envelope: `M(x) + ⟪A(x), y - x⟫ ≤ M(y)`, where
`A(x)` is the gradient of the envelope at `x`. The subgradient inequality of `f` at the proximal
point of `x`, tested at the proximal point of `y`, leaves the remainder
`lambda / 2 * ‖A(y) - A(x)‖²`. -/
theorem moreauEnvelope_add_inner_le (x y : H) :
    moreauEnvelope f lambda x + inner ℝ (moreauGradient f hf hlsc lambda hlambda x) (y - x) ≤
      moreauEnvelope f lambda y := by
  set a := moreauGradient f hf hlsc lambda hlambda x with ha
  set b := moreauGradient f hf hlsc lambda hlambda y with hb
  have hsub := proximalPoint_add_inner_le hf hlsc hlambda x
    (proximalPoint f hf hlsc lambda hlambda y)
  rw [← ha] at hsub
  have hdiff : proximalPoint f hf hlsc lambda hlambda y -
      proximalPoint f hf hlsc lambda hlambda x = (y - x) - lambda • (b - a) := by
    have hx := proximalPoint_add_smul_moreauGradient hf hlsc hlambda x
    have hy := proximalPoint_add_smul_moreauGradient hf hlsc hlambda y
    rw [← ha] at hx
    rw [← hb] at hy
    have h0 : proximalPoint f hf hlsc lambda hlambda y -
        proximalPoint f hf hlsc lambda hlambda x =
        (proximalPoint f hf hlsc lambda hlambda y + lambda • b) -
          (proximalPoint f hf hlsc lambda hlambda x + lambda • a) - lambda • (b - a) := by
      rw [smul_sub]
      abel
    rw [hy, hx] at h0
    exact h0
  rw [hdiff] at hsub
  simp only [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at hsub
  have hsq : 0 ≤ lambda * (‖b‖ ^ 2 - 2 * inner ℝ b a + ‖a‖ ^ 2) := by
    rw [← norm_sub_sq_real]
    positivity
  rw [moreauEnvelope_eq hf hlsc hlambda x, moreauEnvelope_eq hf hlsc hlambda y,
    quadraticPenalty_proximalPoint hf hlsc hlambda x,
    quadraticPenalty_proximalPoint hf hlsc hlambda y, ← ha, ← hb]
  rw [real_inner_comm a b] at hsq
  rw [inner_sub_right]
  nlinarith

/-- The Moreau envelope of a convex lower semicontinuous function is differentiable, and its
gradient is `(w - J(w)) / lambda` for the proximal point `J(w)`. The envelope has a supporting
plane with this slope at every point, and the slope is continuous. -/
theorem hasFDerivAt_moreauEnvelope (w : H) :
    HasFDerivAt (moreauEnvelope f lambda)
      (innerSL ℝ (moreauGradient f hf hlsc lambda hlambda w)) w := by
  refine PDE.Analysis.hasFDerivAt_of_continuous_support
    (A := fun u ↦ innerSL ℝ (moreauGradient f hf hlsc lambda hlambda u)) (fun u v ↦ ?_) ?_
  · rw [innerSL_apply_apply]
    linarith [moreauEnvelope_add_inner_le hf hlsc hlambda u v]
  · exact ((innerSL ℝ).continuous.comp
      (continuous_moreauGradient hf hlsc hlambda)).continuousAt

include hf hlsc hlambda in
/-- The Moreau envelope of a convex lower semicontinuous function is convex. -/
theorem convexOn_moreauEnvelope : ConvexOn ℝ univ (moreauEnvelope f lambda) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  have hx := moreauEnvelope_add_inner_le hf hlsc hlambda (a • x + b • y) x
  have hy := moreauEnvelope_add_inner_le hf hlsc hlambda (a • x + b • y) y
  have hzero : a • (x - (a • x + b • y)) + b • (y - (a • x + b • y)) = 0 := by
    have h1 : a • (a • x + b • y) + b • (a • x + b • y) = a • x + b • y := by
      rw [← add_smul, hab, one_smul]
    rw [smul_sub, smul_sub, sub_add_sub_comm, h1, sub_self]
  have hin : a * inner ℝ (moreauGradient f hf hlsc lambda hlambda (a • x + b • y))
        (x - (a • x + b • y)) +
      b * inner ℝ (moreauGradient f hf hlsc lambda hlambda (a • x + b • y))
        (y - (a • x + b • y)) = 0 := by
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right, hzero, inner_zero_right]
  have hone : a * moreauEnvelope f lambda (a • x + b • y) +
      b * moreauEnvelope f lambda (a • x + b • y) = moreauEnvelope f lambda (a • x + b • y) := by
    rw [← add_mul, hab, one_mul]
  have hx' := mul_le_mul_of_nonneg_left hx ha
  have hy' := mul_le_mul_of_nonneg_left hy hb
  simp only [smul_eq_mul]
  linarith

include hf hlsc hlambda in
/-- The Moreau envelope decreases when the parameter grows. -/
theorem moreauEnvelope_antitone {mu : ℝ} (hmu : 0 < mu) (hle : mu ≤ lambda) (w : H) :
    moreauEnvelope f lambda w ≤ moreauEnvelope f mu w := by
  rw [moreauEnvelope_eq hf hlsc hmu w]
  refine (moreauEnvelope_le hf hlsc hlambda w (proximalPoint f hf hlsc mu hmu w)).trans ?_
  have h : quadraticPenalty lambda w (proximalPoint f hf hlsc mu hmu w) ≤
      quadraticPenalty mu w (proximalPoint f hf hlsc mu hmu w) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  linarith

/-- The proximal point tends to the point itself as the parameter tends to zero. An affine
minorant of `f` bounds the distance by `2 lambda ‖L‖ + √(2 lambda K)`. -/
theorem tendsto_proximalPoint {ι : Type*} {l : Filter ι} {lam : ι → ℝ} (hpos : ∀ i, 0 < lam i)
    (hzero : Tendsto lam l (𝓝 0)) (w : H) :
    Tendsto (fun i ↦ proximalPoint f hf hlsc (lam i) (hpos i) w) l (𝓝 w) := by
  obtain ⟨L, b, hLb⟩ := exists_affine_minorant (isProper_coeReal f)
    (convex_realEpigraph_coeReal hf) (lowerSemicontinuous_coeReal hlsc)
  have hminor (u : H) : L u + b ≤ f u := EReal.coe_le_coe_iff.1 (hLb u)
  set K := f w - (L w + b) with hK
  have hK0 : 0 ≤ K := sub_nonneg.2 (hminor w)
  have hbound (i : ι) : ‖proximalPoint f hf hlsc (lam i) (hpos i) w - w‖ ≤
      2 * lam i * ‖L‖ + √(2 * lam i * K) := by
    set J := proximalPoint f hf hlsc (lam i) (hpos i) w
    set r := ‖J - w‖ with hr
    have hr0 : 0 ≤ r := norm_nonneg _
    have h1 := proximalPoint_isMin hf hlsc (hpos i) w w
    have h2 := hminor J
    have h3 : L J = L w + L (J - w) := by rw [map_sub]; ring
    have h4 : -(‖L‖ * r) ≤ L (J - w) := by
      have := L.le_opNorm (J - w)
      rw [Real.norm_eq_abs] at this
      linarith [neg_abs_le (L (J - w))]
    have h5 : r ^ 2 ≤ 2 * lam i * K + 2 * lam i * ‖L‖ * r := by
      have hpen : quadraticPenalty (lam i) w J = r ^ 2 / (2 * lam i) := rfl
      have hpen0 : quadraticPenalty (lam i) w w = 0 := by simp [quadraticPenalty]
      rw [hpen, hpen0, add_zero] at h1
      have h6 : r ^ 2 / (2 * lam i) ≤ K + ‖L‖ * r := by linarith
      have h7 := (div_le_iff₀ (by have := hpos i; positivity)).1 h6
      linarith
    by_contra hcon
    push Not at hcon
    have hs := Real.sqrt_nonneg (2 * lam i * K)
    have hs2 : √(2 * lam i * K) ^ 2 = 2 * lam i * K :=
      Real.sq_sqrt (by have := hpos i; positivity)
    have hL0 : 0 ≤ 2 * lam i * ‖L‖ := by have := hpos i; positivity
    nlinarith
  have hg : Tendsto (fun i ↦ 2 * lam i * ‖L‖ + √(2 * lam i * K)) l (𝓝 0) := by
    have hc : Continuous fun t : ℝ ↦ 2 * t * ‖L‖ + √(2 * t * K) := by fun_prop
    have h0 := (hc.tendsto 0).comp hzero
    simpa [Function.comp_def] using h0
  exact tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun i ↦ norm_nonneg _) hbound hg)

include hf hlsc in
/-- The Moreau envelope of a convex lower semicontinuous function tends to the function as the
parameter tends to zero: it lies below `f(w)`, and above the value of `f` at the proximal
point, which tends to `w`. -/
theorem tendsto_moreauEnvelope {ι : Type*} {l : Filter ι} {lam : ι → ℝ} (hpos : ∀ i, 0 < lam i)
    (hzero : Tendsto lam l (𝓝 0)) (w : H) :
    Tendsto (fun i ↦ moreauEnvelope f (lam i) w) l (𝓝 (f w)) := by
  have hJ := tendsto_proximalPoint hf hlsc hpos hzero w
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ Eventually.of_forall fun i ↦
    (moreauEnvelope_le_self hf hlsc (hpos i) w).trans_lt ha⟩
  filter_upwards [hJ.eventually (hlsc w a ha)] with i hi
  rw [moreauEnvelope_eq hf hlsc (hpos i) w]
  have h2 : 0 ≤ quadraticPenalty (lam i) w (proximalPoint f hf hlsc (lam i) (hpos i) w) := by
    unfold quadraticPenalty
    have := hpos i
    positivity
  linarith

end Complete

/-- A slice of a jointly continuous family is lower semicontinuous. -/
theorem lowerSemicontinuous_slice {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]
    {G : S → X → ℝ} (hG : Continuous (Function.uncurry G)) (s : S) :
    LowerSemicontinuous (G s) :=
  (hG.comp (Continuous.prodMk_right s)).lowerSemicontinuous

section Parameter

variable [FiniteDimensional ℝ H] {S : Type*} [TopologicalSpace S] [FirstCountableTopology S]
  {G : S → H → ℝ} {lambda : ℝ}

/-- In finite dimensions the proximal point depends continuously on a parameter in a first
countable space: for a jointly continuous family `G(s, u)` that is convex in `u` and bounded
below by one constant for all `s` and `u`, `s ↦ J_s(w)` is continuous. Along a convergent
sequence of parameters the proximal points stay in a ball, every limit point of them minimizes
the penalized limit function, and that minimizer is unique. -/
theorem continuous_proximalPoint_param (hG : Continuous (Function.uncurry G))
    (hconv : ∀ s, ConvexOn ℝ univ (G s)) {c : ℝ} (hc : ∀ s u, c ≤ G s u)
    (hlambda : 0 < lambda) (w : H) :
    Continuous fun s ↦ proximalPoint (G s) (hconv s) (lowerSemicontinuous_slice hG s)
      lambda hlambda w := by
  refine continuous_iff_continuousAt.2 fun s₀ ↦ tendsto_of_seq_tendsto fun s hs ↦
    tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  have ht : Tendsto (fun k ↦ s (ns k)) atTop (𝓝 s₀) := hs.comp hns
  have hGw : Tendsto (fun k ↦ G (s (ns k)) w) atTop (𝓝 (G s₀ w)) :=
    (hG.tendsto (s₀, w)).comp (ht.prodMk_nhds tendsto_const_nhds)
  obtain ⟨C, hC⟩ := hGw.bddAbove_range
  -- the proximal points along the sequence lie in a closed ball around `w`
  have hball (k : ℕ) : proximalPoint (G (s (ns k))) (hconv _) (lowerSemicontinuous_slice hG _)
      lambda hlambda w ∈ Metric.closedBall w √(2 * lambda * (C - c)) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 := proximalPoint_isMin (hconv (s (ns k))) (lowerSemicontinuous_slice hG _)
      hlambda w w
    have hpen0 : quadraticPenalty lambda w w = 0 := by simp [quadraticPenalty]
    rw [hpen0, add_zero, quadraticPenalty] at h1
    have h2 := hc (s (ns k)) (proximalPoint (G (s (ns k))) (hconv _)
      (lowerSemicontinuous_slice hG _) lambda hlambda w)
    have h3 : G (s (ns k)) w ≤ C := hC ⟨k, rfl⟩
    have h4 := (div_le_iff₀ (show (0 : ℝ) < 2 * lambda by positivity)).1
      (show ‖proximalPoint (G (s (ns k))) (hconv _) (lowerSemicontinuous_slice hG _)
        lambda hlambda w - w‖ ^ 2 / (2 * lambda) ≤ C - c by linarith)
    exact (le_abs_self _).trans (Real.abs_le_sqrt (by linarith))
  obtain ⟨a, -, φ, hφ, ha⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hball
  refine ⟨φ, ?_⟩
  -- the limit point minimizes the penalized limit function
  have hmin (u : H) : G s₀ a + quadraticPenalty lambda w a ≤
      G s₀ u + quadraticPenalty lambda w u := by
    have htφ : Tendsto (fun j ↦ s (ns (φ j))) atTop (𝓝 s₀) := ht.comp hφ.tendsto_atTop
    have hL : Tendsto (fun j ↦ G (s (ns (φ j)))
        (proximalPoint (G (s (ns (φ j)))) (hconv _) (lowerSemicontinuous_slice hG _)
          lambda hlambda w) +
        quadraticPenalty lambda w (proximalPoint (G (s (ns (φ j)))) (hconv _)
          (lowerSemicontinuous_slice hG _) lambda hlambda w)) atTop
        (𝓝 (G s₀ a + quadraticPenalty lambda w a)) :=
      ((hG.tendsto (s₀, a)).comp (htφ.prodMk_nhds ha)).add
        (((continuous_quadraticPenalty lambda w).tendsto a).comp ha)
    have hR : Tendsto (fun j ↦ G (s (ns (φ j))) u + quadraticPenalty lambda w u) atTop
        (𝓝 (G s₀ u + quadraticPenalty lambda w u)) :=
      ((hG.tendsto (s₀, u)).comp (htφ.prodMk_nhds tendsto_const_nhds)).add tendsto_const_nhds
    exact le_of_tendsto_of_tendsto' hL hR fun j ↦
      proximalPoint_isMin (hconv _) (lowerSemicontinuous_slice hG _) hlambda w u
  have heq := eq_proximalPoint_of_isMin (hconv s₀) (lowerSemicontinuous_slice hG s₀) hlambda hmin
  have ha' : Tendsto (fun n ↦ proximalPoint (G (s (ns (φ n)))) (hconv _)
      (lowerSemicontinuous_slice hG _) lambda hlambda w) atTop
      (𝓝 (proximalPoint (G s₀) (hconv s₀) (lowerSemicontinuous_slice hG s₀)
        lambda hlambda w)) := by
    rw [← heq]
    exact ha
  exact ha'

/-- In finite dimensions the Moreau envelope at a fixed point depends continuously on a
parameter, for a jointly continuous family that is convex in the second variable and bounded
below. -/
theorem continuous_moreauEnvelope_param (hG : Continuous (Function.uncurry G))
    (hconv : ∀ s, ConvexOn ℝ univ (G s)) {c : ℝ} (hc : ∀ s u, c ≤ G s u)
    (hlambda : 0 < lambda) (w : H) :
    Continuous fun s ↦ moreauEnvelope (G s) lambda w := by
  have hJ := continuous_proximalPoint_param hG hconv hc hlambda w
  have h : Continuous fun s ↦ G s (proximalPoint (G s) (hconv s)
      (lowerSemicontinuous_slice hG s) lambda hlambda w) +
      quadraticPenalty lambda w (proximalPoint (G s) (hconv s)
        (lowerSemicontinuous_slice hG s) lambda hlambda w) :=
    (hG.comp (continuous_id.prodMk hJ)).add ((continuous_quadraticPenalty lambda w).comp hJ)
  exact h.congr fun s ↦
    (moreauEnvelope_eq (hconv s) (lowerSemicontinuous_slice hG s) hlambda w).symm

/-- In finite dimensions the gradient of the Moreau envelope at a fixed point depends
continuously on a parameter, for a jointly continuous family that is convex in the second
variable and bounded below. -/
theorem continuous_moreauGradient_param (hG : Continuous (Function.uncurry G))
    (hconv : ∀ s, ConvexOn ℝ univ (G s)) {c : ℝ} (hc : ∀ s u, c ≤ G s u)
    (hlambda : 0 < lambda) (w : H) :
    Continuous fun s ↦ moreauGradient (G s) (hconv s) (lowerSemicontinuous_slice hG s)
      lambda hlambda w :=
  (continuous_const.sub (continuous_proximalPoint_param hG hconv hc hlambda w)).const_smul _

end Parameter

end PDE.Analysis.Convex
