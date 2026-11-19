/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Integer.Reverse
import PDE.Spaces.Sobolev.Fractional.WholeSpace.FourierWeight
import PDE.Spaces.Sobolev.Fractional.WholeSpace.OperatorBounds

/-!
# The two scales are topologically isomorphic

`Fractional.Integer.Reverse` produces a linear isomorphism `toWkpSpaceEquiv` between the
real part of `H^k(ℝ^n)` and the integer-order graph space `W^{k,2}(ℝ^n)`.  We
prove two-sided norm bounds and upgrade it to a continuous linear
equivalence.

* `norm_toWkpSpace_le` : `‖toWkpSpace u‖ ≤ √(card (DerivIndex n k)) · (2π)^k · ‖u‖`
* `norm_ofWkpSpace_le` : `‖ofWkpSpace U‖ ≤ 2^(k-1)(1 + n^(k-1))(n+1) · ‖U‖`, where `k - 1`
  is truncated natural subtraction, so the factor is `2 (n + 1)` at `k = 0`
* `norm_le_base_add_sum_top` : the base and pure top derivatives control the full graph norm.
* `toWkpSpaceCLE` : the resulting `≃L[ℝ]`.

## The two arguments

Forward: the graph norm is the `ℓ²` norm over the finitely many derivative
coordinates; each coordinate is bounded by iterating `norm_lineDerivLinear_le`
along its word, and summing gives the `√card · (2π)^k` factor.

Reverse: the pointwise majorisation `norm_besselWeight_mul_fourier_le` from
`Fractional.Integer.Reverse`, integrated against `L²` and transported by Plancherel,
bounds the Bessel weight by the base coordinate plus the pure derivatives, each
of which is at most `‖U‖` by `PiLp.norm_apply_le`.

## Constants are not sharp

The forward estimate bounds every derivative coordinate by the same
worst-case bound before summing their squares. The reverse estimate discards
a factor `(2π)^{-k} ≤ 1` and uses the triangle inequality for a finite sum in
`L²`. We do not optimize either constant.

The natural equivalence is not generally isometric: at positive order, the
Fourier norm and the derivative graph norm use different weights. At order
zero it is isometric, since both norms are exactly the `L²` norm.

This completes the identification `H^k(ℝ^n) = W^{k,2}(ℝ^n)` with equivalent norms for integer
`k`, with explicit constants. Evans, PDE, §5.8.5, Theorem 8(ii), states the norm equivalence
with the weight `1 + |y|^k` and an unspecified constant.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.5, Theorem 8, pp. 297-298; the two-sided bound is (20),
  p. 297.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

/-! ## Boundedness of the forward map `H^k → W^{k,2}` -/

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped BesselPotentialSpace ENNReal Real

namespace SobolevSpace.Fractional

variable {n k : ℕ}

open BesselPotentialSpace

private theorem domainMeasure_univ_eq :
    domainMeasure n (Set.univ : Set (ℝ^n)) = (volume : Measure (ℝ^n)) := by
  simp [domainMeasure]

/-- Taking a real part does not increase the `L²` norm. -/
private theorem norm_toDerivLp_le (g : Lp ℂ 2 (volume : Measure (ℝ^n))) : ‖toDerivLp g‖ ≤ ‖g‖ := by
  rw [toDerivLp, MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_def,
    domainMeasure_univ_eq]
  refine ENNReal.toReal_mono (MeasureTheory.Lp.eLpNorm_ne_top g) ?_
  refine MeasureTheory.eLpNorm_mono_ae (Lp.memLp g).re.aestronglyMeasurable ?_
  filter_upwards with x
  exact RCLike.abs_re_le_norm ((g : ℝ^n → ℂ) x)

/-- `2π ≥ 1`, used to compare powers. -/
private theorem one_le_two_pi : (1 : ℝ) ≤ 2 * π := by
  have := Real.two_le_pi
  linarith

/-- Weak derivatives along an arbitrary word, with a norm bound.

A quantitative refinement of `exists_hasWeakDerivativeOn_list`: the element of
`H^{s-|α|}` realizing the `α`-th weak derivative can be chosen with
`‖v‖ ≤ (2π)^{|α|} ‖u‖`. -/
private theorem exists_hasWeakDerivativeOn_list_norm_le :
    ∀ (α : List (Fin n)) {s : ℝ} (h0 : (0 : ℝ) ≤ s), (α.length : ℝ) ≤ s →
      ∀ (u : H^{s}(ℝ^n)), IsRealL2 (toL2Fun h0 u) →
      ∃ (t : ℝ) (ht : (0 : ℝ) ≤ t) (v : H^{t}(ℝ^n)),
        t = s - α.length ∧ IsRealL2 (toL2Fun ht v) ∧
          HasWeakDerivativeOn (n := n) Set.univ α
            (reOfL2 (toL2Fun h0 u)) (reOfL2 (toL2Fun ht v)) ∧
          ‖v‖ ≤ (2 * π) ^ α.length * ‖u‖ := by
  intro α
  induction α using List.reverseRecOn with
  | nil =>
      intro s h0 _ u hu
      exact ⟨s, h0, u, by simp, hu, hasWeakDerivativeOn_nil _, by simp⟩
  | append_singleton β i ih =>
      intro s h0 hlen u hu
      have hlen' : (β.length : ℝ) + 1 ≤ s := by simpa using hlen
      have hβ : (β.length : ℝ) ≤ s := by linarith
      obtain ⟨t, ht, v, hteq, hvreal, hvweak, hvnorm⟩ := ih h0 hβ u hu
      have ht1 : (1 : ℝ) ≤ t := by rw [hteq]; linarith
      have hstep := hasWeakDerivativeOn_reOfL2 ht1 i v hvreal
      have hreal := isRealL2_lineDeriv_of_isRealL2 ht1 i v hvreal
      refine
        ⟨t - 1, by linarith, lineDerivLinear n t (EuclideanSpace.single i (1 : ℝ)) v,
          ?_, hreal, ?_, ?_⟩
      · have hlenβ : (((β ++ [i]).length : ℕ) : ℝ) = (β.length : ℝ) + 1 := by simp
        rw [hteq, hlenβ]; ring
      · exact HasWeakDerivativeOn.append_single i hvweak hstep
      · have hop := norm_lineDerivLinear_le (EuclideanSpace.single i (1 : ℝ)) v
        have hone : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
        rw [hone, mul_one] at hop
        have h2 : (0 : ℝ) ≤ 2 * π := by positivity
        have hlen2 : (β ++ [i]).length = β.length + 1 := by simp
        calc ‖lineDerivLinear n t (EuclideanSpace.single i (1 : ℝ)) v‖
            ≤ 2 * π * ‖v‖ := hop
          _ ≤ 2 * π * ((2 * π) ^ β.length * ‖u‖) :=
              mul_le_mul_of_nonneg_left hvnorm h2
          _ = (2 * π) ^ (β.length + 1) * ‖u‖ := by ring
          _ = (2 * π) ^ (β ++ [i]).length * ‖u‖ := by rw [hlen2]

/-- Every graph-space coordinate is bounded by `(2π)^k ‖u‖_{H^k}`. -/
theorem norm_graphTuple_apply_le (u : H^{(k : ℝ)}(ℝ^n))
    (hu : IsRealL2 (toL2Fun (Nat.cast_nonneg k) u)) (a : DerivIndex n k) :
    ‖graphTuple (Nat.cast_nonneg k) u hu a‖ ≤ (2 * π) ^ k * ‖u‖ := by
  obtain ⟨t, ht, v, -, -, hvweak, hvnorm⟩ :=
    exists_hasWeakDerivativeOn_list_norm_le a.toList (Nat.cast_nonneg k)
      (by exact_mod_cast a.toList_length_le) u hu
  rw [graphTuple_apply_of_hasWeakDerivativeOn (Nat.cast_nonneg k) u hu hvweak]
  calc ‖toDerivLp (toL2Fun ht v)‖
      ≤ ‖toL2Fun ht v‖ := norm_toDerivLp_le _
    _ ≤ ‖v‖ := norm_toL2Fun_le ht v
    _ ≤ (2 * π) ^ a.toList.length * ‖u‖ := hvnorm
    _ ≤ (2 * π) ^ k * ‖u‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ one_le_two_pi a.toList_length_le) (norm_nonneg u)

/-- The explicit operator-norm bound for the map `H^k(ℝ^n) → W^{k,2}(ℝ^n)`. -/
noncomputable def toWkpSpaceNormBound (n k : ℕ) : ℝ :=
  Real.sqrt (Fintype.card (DerivIndex n k)) * (2 * π) ^ k

/-- The forward constant `√(card (DerivIndex n k)) · (2π)^k` is nonnegative, as required by
`LinearMap.mkContinuous`. -/
theorem toWkpSpaceNormBound_nonneg : (0 : ℝ) ≤ toWkpSpaceNormBound n k := by
  unfold toWkpSpaceNormBound
  positivity

/-- The forward map into the integer-order graph space is bounded. -/
theorem norm_toWkpSpace_le (u : H^{(k : ℝ)}(ℝ^n))
    (hu : IsRealL2 (toL2Fun (Nat.cast_nonneg k) u)) :
    ‖toWkpSpace (Nat.cast_nonneg k) u hu‖ ≤ toWkpSpaceNormBound n k * ‖u‖ := by
  set M : ℝ := (2 * π) ^ k * ‖u‖ with hM
  have hM0 : (0 : ℝ) ≤ M := by rw [hM]; positivity
  have hsum : ∑ a : DerivIndex n k,
      ‖graphTuple (Nat.cast_nonneg k) u hu a‖ ^ 2
        ≤ (Fintype.card (DerivIndex n k) : ℝ) * M ^ 2 := by
    calc ∑ a : DerivIndex n k, ‖graphTuple (Nat.cast_nonneg k) u hu a‖ ^ 2
        ≤ ∑ _a : DerivIndex n k, M ^ 2 :=
          Finset.sum_le_sum fun a _ ↦
            pow_le_pow_left₀ (norm_nonneg _) (norm_graphTuple_apply_le u hu a) 2
      _ = (Fintype.card (DerivIndex n k) : ℝ) * M ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hnorm : ‖toWkpSpace (Nat.cast_nonneg k) u hu‖
      = ‖graphTuple (Nat.cast_nonneg k) u hu‖ := rfl
  rw [hnorm, PiLp.norm_eq_of_L2, toWkpSpaceNormBound, mul_assoc]
  calc Real.sqrt (∑ a : DerivIndex n k, ‖graphTuple (Nat.cast_nonneg k) u hu a‖ ^ 2)
      ≤ Real.sqrt ((Fintype.card (DerivIndex n k) : ℝ) * M ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (Fintype.card (DerivIndex n k)) * M := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM0]

/-- The bridge `H^k → W^{k,2}` as a continuous `ℝ`-linear map. -/
noncomputable def toWkpSpaceCLM (n k : ℕ) :
    HsSpaceReal n (k : ℝ)
      →L[ℝ] W^{k,2}((Set.univ : Set (ℝ^n))) :=
  LinearMap.mkContinuous (toWkpSpaceLinear n k) (toWkpSpaceNormBound n k)
    fun u ↦
      norm_toWkpSpace_le u.1
        (HsSpaceReal.isRealL2_toL2Fun (Nat.cast_nonneg k) u)

/-- The continuous bridge evaluates to `toWkpSpace` on the underlying `H^k` element. -/
@[simp] theorem toWkpSpaceCLM_apply (u : HsSpaceReal n (k : ℝ)) :
    toWkpSpaceCLM n k u =
      toWkpSpace (Nat.cast_nonneg k) u.1
        (HsSpaceReal.isRealL2_toL2Fun (Nat.cast_nonneg k) u) := rfl

/-- Operator-norm form of the forward bound: `‖toWkpSpaceCLM n k‖ ≤ √card · (2π)^k`. -/
theorem norm_toWkpSpaceCLM_le : ‖toWkpSpaceCLM n k‖ ≤ toWkpSpaceNormBound n k :=
  LinearMap.mkContinuous_norm_le _ toWkpSpaceNormBound_nonneg _

end SobolevSpace.Fractional

/-! ## Boundedness of the reverse map `W^{k,2}(ℝ^n) → H^k(ℝ^n)`

`Fractional.Integer.Reverse` builds `ofWkpSpace`, the
inverse of the map from the real part of `H^k(ℝ^n)` into the integer-order graph
space, and shows the two maps are mutually inverse and `ℝ`-linear. We prove one of
the two norm bounds:
`ofWkpSpace` is bounded, with an explicit constant depending only on `n` and `k`.
-/

open MeasureTheory TemperedDistribution BesselPotentialSpace
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal FourierTransform

namespace SobolevSpace.Fractional

variable {n k : ℕ}

/-! ## Pointwise norms as elements of real `L²` -/

/-- The pointwise norm of a complex `L²` function, as an element of real `L²`. -/
private noncomputable def normLp (w : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    Lp ℝ 2 (volume : Measure (ℝ^n)) :=
  (Lp.memLp w).norm.toLp _

private theorem coeFn_normLp (w : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    ((normLp w : Lp ℝ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℝ)
      =ᵐ[(volume : Measure (ℝ^n))] fun x ↦ ‖(w : ℝ^n → ℂ) x‖ :=
  MemLp.coeFn_toLp _

@[simp] private theorem norm_normLp (w : Lp ℂ 2 (volume : Measure (ℝ^n))) : ‖normLp w‖ = ‖w‖ := by
  rw [normLp, Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable w), Lp.norm_def]

/-! ## The Fourier representative of `ofWkpSpace U` -/

/-- The Fourier-side representative of `ofWkpSpace U` is the Bessel weight times the
Fourier transform of the base coordinate. -/
theorem coeFn_fourier_toLp_ofWkpSpace (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    ((𝓕 (toLp (ofWkpSpace U)) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ)
      =ᵐ[(volume : Measure (ℝ^n))]
        fun ξ ↦ besselSymbol n (k : ℝ) ξ * (𝓕 (baseL2 U)) ξ := by
  simpa only [toL2Fun_ofWkpSpace] using
    coeFn_fourier_toLp (Nat.cast_nonneg k) (ofWkpSpace U)

/-! ## The `L²` majorant -/

/-- The real `L²` majorant furnished by `norm_besselWeight_mul_fourier_le`. -/
private noncomputable def besselMajorant (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    Lp ℝ 2 (volume : Measure (ℝ^n)) :=
  besselWeightBound n k • (normLp (𝓕 (baseL2 U)) + ∑ i, normLp (𝓕 (pureDerivL2 U i)))

private theorem coeFn_besselMajorant (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    ((besselMajorant U : Lp ℝ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℝ)
      =ᵐ[(volume : Measure (ℝ^n))] fun ξ ↦ besselWeightBound n k *
        (‖(𝓕 (baseL2 U)) ξ‖
          + ∑ i, ‖((𝓕 (pureDerivL2 U i) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ‖) := by
  have hall : ∀ᵐ ξ ∂(volume : Measure (ℝ^n)), ∀ i : Fin n,
      ((normLp (𝓕 (pureDerivL2 U i)) : Lp ℝ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℝ) ξ
        = ‖((𝓕 (pureDerivL2 U i) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ‖ := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    exact coeFn_normLp _
  unfold besselMajorant
  filter_upwards [Lp.coeFn_smul (besselWeightBound n k)
      (normLp (𝓕 (baseL2 U)) + ∑ i, normLp (𝓕 (pureDerivL2 U i))),
    Lp.coeFn_add (normLp (𝓕 (baseL2 U))) (∑ i, normLp (𝓕 (pureDerivL2 U i))),
    coeFn_normLp (𝓕 (baseL2 U)),
    Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin n))
      (fun i ↦ normLp (𝓕 (pureDerivL2 U i))), hall] with ξ h1 h2 h3 h4 h5
  rw [h1]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h2]
  simp only [Pi.add_apply]
  rw [h3, h4]
  congr 2
  exact Finset.sum_congr rfl fun i _ ↦ h5 i

private theorem norm_besselMajorant_le (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    ‖besselMajorant U‖
      ≤ besselWeightBound n k * (‖baseL2 U‖ + ∑ i, ‖pureDerivL2 U i‖) := by
  have h1 : ‖besselMajorant U‖ ≤ besselWeightBound n k *
      (‖normLp (𝓕 (baseL2 U))‖ + ∑ i, ‖normLp (𝓕 (pureDerivL2 U i))‖) := by
    rw [besselMajorant, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (besselWeightBound_nonneg n k)]
    refine mul_le_mul_of_nonneg_left ?_ (besselWeightBound_nonneg n k)
    refine (norm_add_le _ _).trans ?_
    gcongr
    exact norm_sum_le _ _
  simpa only [norm_normLp, MeasureTheory.Lp.norm_fourier_eq] using h1

/-! ## Comparing coordinates with the graph-space norm -/

/-- The complexification of a real `L²` function has the same norm. -/
private theorem norm_cxL2 {f : ℝ^n → ℝ} (hf : MemLp f 2 (volume : Measure (ℝ^n))) :
    ‖cxL2 hf‖ = (eLpNorm f 2 (volume : Measure (ℝ^n))).toReal := by
  rw [cxL2, Lp.norm_toLp]
  congr 1
  refine eLpNorm_congr_norm_ae hf.ofReal.aestronglyMeasurable
    hf.aestronglyMeasurable ?_
  filter_upwards with x
  simp

/-- Each coordinate of a graph-space element has norm at most the norm of the
element: the ambient space is a `PiLp 2` bundle. -/
private theorem norm_coord_le (U : W^{k,2}((Set.univ : Set (ℝ^n)))) (a : DerivIndex n k) :
    ‖cxL2 (memLp_coordFun U a)‖ ≤ ‖U‖ := by
  have hcoord : ‖cxL2 (memLp_coordFun U a)‖
      = ‖(U : WkpAmbientOn n k 2 (Set.univ : Set (ℝ^n))) a‖ := by
    rw [norm_cxL2, Lp.norm_def]
    congr 1
    simp [coordFun, domainMeasure]
  rw [hcoord]
  exact PiLp.norm_apply_le _ a

private theorem norm_baseL2_le (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    ‖baseL2 U‖ ≤ ‖U‖ :=
  norm_coord_le U (baseIndex n k)

private theorem norm_pureDerivL2_le (U : W^{k,2}((Set.univ : Set (ℝ^n)))) (i : Fin n) :
    ‖pureDerivL2 U i‖ ≤ ‖U‖ :=
  norm_coord_le U (topPureDerivIndex n k i)

/-! ## The bound -/

/-- The base function and its pure order-`k` derivatives control the Fourier Sobolev norm.
Keeping these endpoint norms separate is useful when an energy omits intermediate derivatives. -/
theorem norm_ofWkpSpace_le_base_add_sum_top
    (U : W^{k,2}((Set.univ : Set (ℝ^n))))
    (hk : 1 ≤ k) :
    ‖ofWkpSpace U‖ ≤ besselWeightBound n k *
      (‖baseL2 U‖ + ∑ i, ‖pureDerivL2 U i‖) := by
  have hmaj : ‖𝓕 (toLp (ofWkpSpace U))‖ ≤ ‖besselMajorant U‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [coeFn_fourier_toLp_ofWkpSpace U, coeFn_besselMajorant U,
      pureSymbol_mul_fourier_ae U] with ξ h1 h2 h3
    have hnn : (0 : ℝ) ≤ besselWeightBound n k *
        (‖(𝓕 (baseL2 U)) ξ‖
          + ∑ i, ‖((𝓕 (pureDerivL2 U i) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ‖) :=
      mul_nonneg (besselWeightBound_nonneg n k)
        (by positivity)
    rw [h1, h2, Real.norm_eq_abs, abs_of_nonneg hnn]
    exact norm_besselWeight_mul_fourier_le U hk ξ h3
  calc
    ‖ofWkpSpace U‖ = ‖𝓕 (toLp (ofWkpSpace U))‖ := (norm_fourier_toLp_eq _).symm
    _ ≤ ‖besselMajorant U‖ := hmaj
    _ ≤ besselWeightBound n k * (‖baseL2 U‖ + ∑ i, ‖pureDerivL2 U i‖) :=
      norm_besselMajorant_le U

/-- On the whole space, the base function and the pure top derivatives bound the entire
Sobolev graph norm. Thus intermediate derivative norms need not be included in an energy
used to control this norm. The constant follows from the two Fourier-to-graph comparisons;
it is explicit but not sharp. -/
theorem norm_le_base_add_sum_top
    (U : W^{k,2}((Set.univ : Set (ℝ^n))))
    (hk : 1 ≤ k) :
    ‖U‖ ≤ toWkpSpaceNormBound n k * besselWeightBound n k *
      (‖(U : WkpAmbientOn n k 2 Set.univ) (baseIndex n k)‖ +
        ∑ i, ‖(U : WkpAmbientOn n k 2 Set.univ) (topPureDerivIndex n k i)‖) := by
  have hforward := norm_toWkpSpace_le (ofWkpSpace U)
    (isRealL2_toL2Fun_ofWkpSpace U)
  rw [toWkpSpace_ofWkpSpace] at hforward
  have hcoord (a : DerivIndex n k) :
      ‖cxL2 (memLp_coordFun U a)‖ = ‖(U : WkpAmbientOn n k 2 Set.univ) a‖ := by
    rw [norm_cxL2, Lp.norm_def]
    congr 1
    simp [coordFun, domainMeasure]
  calc
    ‖U‖ ≤ toWkpSpaceNormBound n k * ‖ofWkpSpace U‖ := hforward
    _ ≤ toWkpSpaceNormBound n k *
        (besselWeightBound n k * (‖baseL2 U‖ + ∑ i, ‖pureDerivL2 U i‖)) :=
      mul_le_mul_of_nonneg_left (norm_ofWkpSpace_le_base_add_sum_top U hk)
        toWkpSpaceNormBound_nonneg
    _ = _ := by simp only [baseL2, pureDerivL2, hcoord, mul_assoc]

/-- At order `0` the reverse map is a contraction: the `H^0` norm is the `L²` norm of
the base coordinate. -/
theorem norm_ofWkpSpace_le_order_zero (U : W^{0,2}((Set.univ : Set (ℝ^n)))) :
    ‖ofWkpSpace U‖ ≤ ‖U‖ := by
  have hmaj : ‖𝓕 (toLp (ofWkpSpace U))‖ ≤ ‖(𝓕 (baseL2 U) : Lp ℂ 2 volume)‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [coeFn_fourier_toLp_ofWkpSpace U] with ξ h1
    rw [h1, norm_mul]
    have hw : ‖besselSymbol n ((0 : ℕ) : ℝ) ξ‖ = 1 := by
      rw [besselSymbol]
      simp
    rw [hw, one_mul]
  calc ‖ofWkpSpace U‖ = ‖𝓕 (toLp (ofWkpSpace U))‖ := (norm_fourier_toLp_eq _).symm
    _ ≤ ‖(𝓕 (baseL2 U) : Lp ℂ 2 (volume : Measure (ℝ^n)))‖ := hmaj
    _ = ‖baseL2 U‖ := MeasureTheory.Lp.norm_fourier_eq _
    _ ≤ ‖U‖ := norm_baseL2_le U

/-- The reverse map is bounded with the constant `besselWeightBound n k * (n + 1)`. At `k = 0`
the map is a contraction and the constant is `2 (n + 1) ≥ 1`. -/
theorem norm_ofWkpSpace_le_of_one_le (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    ‖ofWkpSpace U‖ ≤ besselWeightBound n k * ((n : ℝ) + 1) * ‖U‖ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine (norm_ofWkpSpace_le_order_zero U).trans (le_mul_of_one_le_left (norm_nonneg _) ?_)
    simp only [besselWeightBound, Nat.zero_sub, pow_zero]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hsum : ∑ _i : Fin n, ‖U‖ = (n : ℝ) * ‖U‖ := by simp
  have hcoord : ‖baseL2 U‖ + ∑ i, ‖pureDerivL2 U i‖ ≤ ((n : ℝ) + 1) * ‖U‖ := by
    have h1 : ∑ i, ‖pureDerivL2 U i‖ ≤ ∑ _i : Fin n, ‖U‖ :=
      Finset.sum_le_sum fun i _ ↦ norm_pureDerivL2_le U i
    rw [hsum] at h1
    have h2 := norm_baseL2_le U
    linarith
  calc
    ‖ofWkpSpace U‖ ≤ besselWeightBound n k * (‖baseL2 U‖ + ∑ i, ‖pureDerivL2 U i‖) :=
      norm_ofWkpSpace_le_base_add_sum_top U hk
    _ ≤ besselWeightBound n k * (((n : ℝ) + 1) * ‖U‖) :=
        mul_le_mul_of_nonneg_left hcoord (besselWeightBound_nonneg n k)
    _ = besselWeightBound n k * ((n : ℝ) + 1) * ‖U‖ := by ring

/-- At order zero, the Fourier-to-graph bridge preserves the norm exactly. -/
theorem norm_toWkpSpace_order_zero (u : H^{((0 : ℕ) : ℝ)}(ℝ^n))
    (hu : IsRealL2 (toL2Fun (Nat.cast_nonneg 0) u)) :
    ‖toWkpSpace (n := n) (k := 0) (Nat.cast_nonneg 0) u hu‖ = ‖u‖ := by
  apply le_antisymm
  · have h := norm_toWkpSpace_le (n := n) (k := 0) u hu
    simpa [toWkpSpaceNormBound] using h
  · have h := norm_ofWkpSpace_le_order_zero (n := n)
      (toWkpSpace (n := n) (k := 0) (Nat.cast_nonneg 0) u hu)
    rw [ofWkpSpace_toWkpSpace (k := 0) u hu] at h
    exact h

/-- The reverse map `W^{k,2}(ℝ^n) → H^k(ℝ^n)` is bounded, with the explicit constant
`2^(k-1) (1 + n^(k-1)) (n + 1)`. The exponent `k - 1` is truncated natural subtraction, so at
`k = 0` the constant is `2 (n + 1)`.

The natural map is not generally isometric with these norm conventions.
At order zero, `norm_toWkpSpace_order_zero` gives exact norm preservation;
the uniform constant in this estimate is not sharp even in that case. -/
theorem norm_ofWkpSpace_le (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    ‖ofWkpSpace U‖
      ≤ (2 : ℝ) ^ (k - 1) * (1 + (n : ℝ) ^ (k - 1)) * ((n : ℝ) + 1) * ‖U‖ := by
  have := norm_ofWkpSpace_le_of_one_le U
  rwa [besselWeightBound] at this

/-- The reverse map as a bounded `ℝ`-linear map, of operator norm at most
`2^(k-1) (1 + n^(k-1)) (n + 1)`, where `k - 1` is truncated natural subtraction.  Linearity
is `ofWkpSpace_add`/`ofWkpSpace_smul` from `Fractional.Integer.Reverse`; the bound is
`norm_ofWkpSpace_le`. -/
noncomputable def ofWkpSpaceCLM (n k : ℕ) :
    W^{k,2}((Set.univ : Set (ℝ^n))) →L[ℝ] H^{(k : ℝ)}(ℝ^n) :=
  LinearMap.mkContinuous
    { toFun := ofWkpSpace
      map_add' := ofWkpSpace_add
      map_smul' := fun c U ↦ by simpa using ofWkpSpace_smul c U }
    ((2 : ℝ) ^ (k - 1) * (1 + (n : ℝ) ^ (k - 1)) * ((n : ℝ) + 1))
    (fun U ↦ by simpa using norm_ofWkpSpace_le U)

/-- The continuous reverse map evaluates to `ofWkpSpace`. -/
@[simp] theorem ofWkpSpaceCLM_apply (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    ofWkpSpaceCLM n k U = ofWkpSpace U := rfl

/-- The operator-norm form of the bound. -/
theorem norm_ofWkpSpaceCLM_le (n k : ℕ) :
    ‖ofWkpSpaceCLM n k‖
      ≤ (2 : ℝ) ^ (k - 1) * (1 + (n : ℝ) ^ (k - 1)) * ((n : ℝ) + 1) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun U ↦ ?_
  simpa using norm_ofWkpSpace_le U

/-- The reverse map, valued in the real subspace, as a CLM. -/
noncomputable def ofWkpSpaceRealCLM (n k : ℕ) :
    W^{k,2}((Set.univ : Set (ℝ^n)))
      →L[ℝ] HsSpaceReal n (k : ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun U ↦
        HsSpaceReal.ofPhysical (Nat.cast_nonneg k) (ofWkpSpace U)
          (isRealL2_toL2Fun_ofWkpSpace U)
      map_add' := fun U V ↦ Subtype.ext (ofWkpSpace_add U V)
      map_smul' := fun c U ↦ Subtype.ext (by simpa using ofWkpSpace_smul c U) }
    ((2 : ℝ) ^ (k - 1) * (1 + (n : ℝ) ^ (k - 1)) * ((n : ℝ) + 1))
    (fun U ↦ by simpa using norm_ofWkpSpace_le U)

/-- The linear equivalence upgrades to a continuous linear equivalence. -/
noncomputable def toWkpSpaceCLE (n k : ℕ) :
    HsSpaceReal n (k : ℝ)
      ≃L[ℝ] W^{k,2}((Set.univ : Set (ℝ^n))) where
  __ := toWkpSpaceEquiv n k
  continuous_toFun := (toWkpSpaceCLM n k).continuous
  continuous_invFun := (ofWkpSpaceRealCLM n k).continuous

end SobolevSpace.Fractional
