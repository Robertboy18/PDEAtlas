/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TemperedDistribution.Lp
public import PDE.Spaces.Sobolev.Fractional.Integer.GraphSpace
import Mathlib.Algebra.Order.Chebyshev
import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
import PDE.Spaces.Sobolev.Fractional.WholeSpace.FourierWeight
import PDE.Spaces.Sobolev.Fractional.WholeSpace.IntegrationByParts
import PDE.Spaces.Sobolev.GraphSpace.Representatives.Bridge

/-!
# The integer-order graph space embeds back into the fractional scale

`Fractional.Integer.GraphSpace` sends an element of `H^k(ℝ^n)` with a real representative
to a point of `SobolevSpace.GraphSpace.WkpSpaceOn n k 2 Set.univ`.  We
prove the converse, `ofWkpSpace`, and that the two maps are mutually
inverse.  So for natural `k` the real part of the fractional scale and the
integer-order graph space over `ℝ^n` are in bijection.

Together with `Fractional.Integer.GraphSpace` this is the classical identification of the
derivative-defined space `W^{k,2}(ℝ^n)` with the Fourier-defined space `H^k(ℝ^n)` (Evans §5.8.5,
Theorem 8). The inverse pair forms a linear equivalence, and `Fractional.Integer.NormComparison`
proves two-sided norm bounds and upgrades it to a continuous linear equivalence. The natural map is
not generally isometric, since the Fourier norm and derivative graph norm use different weights at
positive order. At order zero, both norms equal the `L²` norm; `Fractional.Integer.NormComparison`
proves exact norm preservation in that case.

## Main results

* `SobolevSpace.Fractional.ofWkpSpace`: the reverse map.
* `SobolevSpace.Fractional.toL2Fun_ofWkpSpace`, `reOfL2_toL2Fun_ofWkpSpace`:
  it recovers the base coordinate.
* `SobolevSpace.Fractional.toWkpSpace_ofWkpSpace`,
  `SobolevSpace.Fractional.ofWkpSpace_toWkpSpace`: the two round trips.
* `SobolevSpace.Fractional.toWkpSpaceEquiv`: the resulting linear equivalence.

## How it works

Given a tuple of real `L²` functions with the weak-derivative property, we show that its base
coordinate `u` satisfies `(1 + ‖ξ‖²)^{k/2} 𝓕u ∈ L²`. We follow step 1 of Evans's proof, the symbol
identity `(D^α u)^ = (iy)^α û`, applied to the pure derivatives of order `k`; with Mathlib's Fourier
convention the symbol of `∂ᵢ^k` is `(2πi ξᵢ)^k` (`pureSymbol`). For smooth compactly supported
functions, viewed as Schwartz functions, this is Mathlib's `SchwartzMap.fourier_lineDerivOp_eq`
iterated. The derivative coordinates are only known almost everywhere, so we pass to them along the
mollifier approximants of `Approximation.globalApproximation_Wkp`, using continuity of the `L²`
Fourier transform; the identity then holds as tempered distributions, and no density of `C_c^∞` in
`𝓢` is needed. Evans's weight is `1 + |y|^k`; Mathlib's is `(1 + ‖ξ‖²)^{k/2}`, which is at most
`besselWeightBound n k * (1 + Σᵢ |ξᵢ|^k)`. So the Bessel-weighted Fourier transform of `u` is
dominated by the Fourier transforms of `u` and of its pure derivatives
(`norm_besselWeight_mul_fourier_le`), all of which are in `L²`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.5, Theorem 8, pp. 297-298, and step 1 of its proof,
  p. 298.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

open MeasureTheory TopologicalSpace Real
open SobolevSpace SobolevSpace.GraphSpace TemperedDistribution
open scoped BesselPotentialSpace ContDiff Distributions ENNReal LineDeriv SchwartzMap
  FourierTransform Topology

namespace SobolevSpace.Fractional

variable {n k : ℕ}

/-! ## Supporting material

The supporting results establish the Fourier symbol of an iterated pure derivative
at the Schwartz level and the elementary weight inequalities.
Most declarations are private; the public domination lemmas and constants
are used by `Fractional.Integer.NormComparison`. -/

section Supporting

/-! ### Fourier symbol of an iterated pure derivative -/

/-- The complexified Schwartz function attached to a smooth compactly supported real
function. -/
private noncomputable def cxSchwartz (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcs : HasCompactSupport f) : 𝓢(ℝ^n, ℂ) :=
  testFunctionToSchwartz (_root_.TestFunction.mk f hf hcs (Set.subset_univ _))

@[simp] private theorem cxSchwartz_apply (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcs : HasCompactSupport f) (x : ℝ^n) : cxSchwartz f hf hcs x = ((f x : ℝ) : ℂ) := rfl

private theorem cxSchwartz_congr {f g : ℝ^n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcs : HasCompactSupport f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgcs : HasCompactSupport g)
    (h : ∀ x, f x = g x) : cxSchwartz f hf hcs = cxSchwartz g hg hgcs := by
  ext x
  simp [h x]

/-- Complexification turns one coordinate derivative into Mathlib's line derivative. -/
private theorem cxSchwartz_partialDeriv (i : Fin n) {g : ℝ^n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgcs : HasCompactSupport g)
    (hd : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ (∂[i] g) x))
    (hdcs : HasCompactSupport (fun x ↦ (∂[i] g) x)) :
    cxSchwartz (fun x ↦ (∂[i] g) x) hd hdcs
      = ∂_{EuclideanSpace.single i (1 : ℝ)} (cxSchwartz g hg hgcs) := by
  ext x
  rw [cxSchwartz_apply]
  exact (lineDerivOp_testFunctionToSchwartz
    (_root_.TestFunction.mk g hg hgcs (Set.subset_univ _)) i x).symm

/-- The Fourier symbol of a single pure coordinate derivative. -/
private theorem fourier_cxSchwartz_partialDeriv (i : Fin n) {g : ℝ^n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgcs : HasCompactSupport g)
    (hd : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ (∂[i] g) x))
    (hdcs : HasCompactSupport (fun x ↦ (∂[i] g) x)) (ξ : ℝ^n) :
    𝓕 (cxSchwartz (fun x ↦ (∂[i] g) x) hd hdcs) ξ
      = (2 * π * Complex.I) * ((ξ.ofLp i : ℝ) : ℂ) * 𝓕 (cxSchwartz g hg hgcs) ξ := by
  rw [cxSchwartz_partialDeriv i hg hgcs hd hdcs,
    SchwartzMap.fourier_lineDerivOp_eq]
  have hin : inner ℝ ξ (EuclideanSpace.single i (1 : ℝ)) = ξ.ofLp i := by
    simpa using (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) (v := ξ))
  have htg : (fun y : ℝ^n ↦ inner ℝ y (EuclideanSpace.single i (1 :
    ℝ))).HasTemperateGrowth :=
    ((innerSL ℝ).flip (EuclideanSpace.single i (1 : ℝ))).hasTemperateGrowth
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply htg, hin, Complex.real_smul,
    smul_eq_mul]
  ring

/-- Induction-friendly form of the iterated symbol identity. -/
private theorem fourier_cxSchwartz_iteratedPartialDeriv_replicate_aux (i : Fin n) {f
  : ℝ^n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcs : HasCompactSupport f) (k : ℕ)
    (hk : ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ iteratedPartialDeriv (n := n) (List.replicate k i) f x))
    (hkcs : HasCompactSupport
      (fun x ↦ iteratedPartialDeriv (n := n) (List.replicate k i) f x)) (ξ : ℝ^n) :
    𝓕 (cxSchwartz (fun x ↦ iteratedPartialDeriv (n := n) (List.replicate k i) f x) hk hkcs) ξ
      = ((2 * π * Complex.I) * ((ξ.ofLp i : ℝ) : ℂ)) ^ k * 𝓕 (cxSchwartz f hf hcs) ξ := by
  induction k with
  | zero =>
      rw [cxSchwartz_congr hk hkcs hf hcs (fun x ↦ rfl)]
      simp
  | succ k ih =>
      have hk' : ContDiff ℝ (⊤ : ℕ∞)
          (fun x ↦ iteratedPartialDeriv (n := n) (List.replicate k i) f x) :=
        PDE.contDiff_top_iteratedPartialDeriv hf _
      have hkcs' : HasCompactSupport
          (fun x ↦ iteratedPartialDeriv (n := n) (List.replicate k i) f x) :=
        hasCompactSupport_iteratedPartialDeriv hcs _
      have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ (∂[i]
          (fun y ↦ iteratedPartialDeriv (n := n) (List.replicate k i) f y)) x) :=
        PDE.contDiff_top_partialDeriv hk'
      have hdcs : HasCompactSupport (fun x ↦ (∂[i]
          (fun y ↦ iteratedPartialDeriv (n := n) (List.replicate k i) f y)) x) :=
        hkcs'.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ))
      rw [cxSchwartz_congr hk hkcs hd hdcs (fun x ↦ rfl),
        fourier_cxSchwartz_partialDeriv i hk' hkcs' hd hdcs ξ,
        ih hk' hkcs']
      ring

/-- Fourier symbol of an iterated pure derivative. -/
private theorem fourier_cxSchwartz_iteratedPartialDeriv_replicate (i : Fin n) {f : ℝ^n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcs : HasCompactSupport f) (k : ℕ) (ξ : ℝ^n) :
    𝓕 (cxSchwartz (fun x ↦ iteratedPartialDeriv (n := n) (List.replicate k i) f x)
        (PDE.contDiff_top_iteratedPartialDeriv hf _)
        (hasCompactSupport_iteratedPartialDeriv hcs _)) ξ
      = ((2 * π * Complex.I) * ((ξ.ofLp i : ℝ) : ℂ)) ^ k * 𝓕 (cxSchwartz f hf hcs) ξ :=
  fourier_cxSchwartz_iteratedPartialDeriv_replicate_aux i hf hcs k _ _ ξ

/-! ### Weight inequalities and the membership criterion -/

/-- The Bessel symbol of order `k` is dominated by the `k`-th power of `1 + ∑ i, |ξ i|`. -/
private theorem symbol_le (k : ℕ) (ξ : ℝ^n) :
    (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) ≤ (1 + ∑ i, |ξ.ofLp i|) ^ k := by
  have hsq : ‖ξ‖ ^ 2 = ∑ i, (ξ.ofLp i) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [Real.norm_eq_abs, sq_abs]
  have hb : (0 : ℝ) ≤ 1 + ∑ i, |ξ.ofLp i| := by positivity
  have hkey : 1 + ‖ξ‖ ^ 2 ≤ (1 + ∑ i, |ξ.ofLp i|) ^ 2 := by
    have h1 : ∑ i, (ξ.ofLp i) ^ 2 ≤ (∑ i, |ξ.ofLp i|) ^ 2 := by
      have := Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset (Fin n)))
        (f := fun i ↦ |ξ.ofLp i|) (fun i _ ↦ abs_nonneg _)
      simpa [sq_abs] using this
    have h2 : (0 : ℝ) ≤ ∑ i, |ξ.ofLp i| :=
      Finset.sum_nonneg (fun i _ ↦ abs_nonneg _)
    rw [hsq, add_sq, one_pow, mul_one]
    linarith
  calc (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2)
      ≤ ((1 + ∑ i, |ξ.ofLp i|) ^ 2) ^ ((k : ℝ) / 2) := by
        apply Real.rpow_le_rpow (by positivity) hkey (by positivity)
    _ = (1 + ∑ i, |ξ.ofLp i|) ^ k := by
        rw [← Real.rpow_natCast (1 + ∑ i, |ξ.ofLp i|) 2, ← Real.rpow_mul hb]
        rw [show ((2 : ℕ) : ℝ) * ((k : ℝ) / 2) = (k : ℝ) by ring, Real.rpow_natCast]

/-- Power-mean step: `(1 + ∑ i, |ξ i|) ^ k` is bounded by a constant multiple of
`1 + ∑ i, |ξ i| ^ k`, with the constant depending only on `n` and `k`. -/
private theorem sum_pow_le (k : ℕ) (hk : 1 ≤ k) (ξ : ℝ^n) :
    (1 + ∑ i, |ξ.ofLp i|) ^ k
      ≤ (2 : ℝ) ^ (k - 1) * (1 + (n : ℝ) ^ (k - 1) * ∑ i, |ξ.ofLp i| ^ k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h2 : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      (a + b) ^ (j + 1) ≤ (2 : ℝ) ^ j * (a ^ (j + 1) + b ^ (j + 1)) := by
    intro a b ha hb
    have := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset (Fin 2)))
      (f := ![a, b]) (by intro i _; fin_cases i <;> simpa) j
    simpa [Fin.sum_univ_two] using this
  have hn := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset (Fin n)))
    (f := fun i ↦ |ξ.ofLp i|) (fun i _ ↦ abs_nonneg _) j
  have hs : (0 : ℝ) ≤ ∑ i, |ξ.ofLp i| := Finset.sum_nonneg (fun i _ ↦ abs_nonneg _)
  calc (1 + ∑ i, |ξ.ofLp i|) ^ (j + 1)
      ≤ (2 : ℝ) ^ j * (1 + (∑ i, |ξ.ofLp i|) ^ (j + 1)) := by
        have := h2 1 (∑ i, |ξ.ofLp i|) zero_le_one hs
        simpa using this
    _ ≤ (2 : ℝ) ^ j * (1 + (n : ℝ) ^ j * ∑ i, |ξ.ofLp i| ^ (j + 1)) := by
        have : (∑ i, |ξ.ofLp i|) ^ (j + 1) ≤ (n : ℝ) ^ j * ∑ i, |ξ.ofLp i| ^ (j + 1) := by
          simpa using hn
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j]
    _ = (2 : ℝ) ^ (j + 1 - 1) * (1 + (n : ℝ) ^ (j + 1 - 1) * ∑ i, |ξ.ofLp i| ^ (j + 1)) := by
        simp

/-! ### Approximation plumbing and the multiplier identity -/

/-- Complexification of a real `L²` function, as an element of `Lp ℂ 2 (volume : Measure (ℝ^n))`. -/
noncomputable def cxL2 {f : ℝ^n → ℝ} (hf : MemLp f 2 (volume : Measure (ℝ^n))) :
    Lp ℂ 2 (volume : Measure (ℝ^n)) :=
  MemLp.toLp (fun x ↦ ((f x : ℝ) : ℂ)) hf.ofReal

private theorem coeFn_cxL2 {f : ℝ^n → ℝ} (hf : MemLp f 2 (volume : Measure (ℝ^n))) :
    ((cxL2 hf : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ)
      =ᵐ[(volume : Measure (ℝ^n))] fun x ↦ ((f x : ℝ) : ℂ) :=
  MemLp.coeFn_toLp _

/-- The `L²` distance between two complexifications is the real `L²` distance. -/
private theorem norm_cxL2_sub {f g : ℝ^n → ℝ} (hf : MemLp f 2 (volume : Measure (ℝ^n)))
    (hg : MemLp g 2 (volume : Measure (ℝ^n))) :
    ‖cxL2 hf - cxL2 hg‖
      = (eLpNorm (fun x ↦ f x - g x) 2 (volume : Measure (ℝ^n))).toReal := by
  rw [Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable (cxL2 hf - cxL2 hg))
    (hf.sub hg).aestronglyMeasurable ?_
  filter_upwards [Lp.coeFn_sub (cxL2 hf) (cxL2 hg), coeFn_cxL2 hf, coeFn_cxL2 hg]
    with x hx h1 h2
  rw [hx]
  simp [h1, h2, ← Complex.ofReal_sub]

/-- `eLpNorm`-convergence of real functions gives `L²`-convergence of their
complexifications. -/
private theorem tendsto_cxL2 {f : ℕ → ℝ^n → ℝ} {u : ℝ^n → ℝ}
    (hf : ∀ m, MemLp (f m) 2 (volume : Measure (ℝ^n)))
    (hu : MemLp u 2 (volume : Measure (ℝ^n)))
    (h : Filter.Tendsto
      (fun m ↦ eLpNorm (fun x ↦ f m x - u x) 2 (volume : Measure (ℝ^n)))
      Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun m ↦ cxL2 (hf m)) Filter.atTop (𝓝 (cxL2 hu)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [norm_cxL2_sub]
  simpa [Function.comp_def] using (ENNReal.tendsto_toReal (by simp)).comp h

/-- The complexified `L²` class of a smooth compactly supported function is the `L²` class of
its Schwartz complexification. -/
private theorem toLp_cxSchwartz {f : ℝ^n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcs : HasCompactSupport f) (h : MemLp f 2 (volume : Measure (ℝ^n))) :
    (cxSchwartz f hf hcs).toLp 2 (volume : Measure (ℝ^n)) = cxL2 h := by
  refine Lp.ext_iff.mpr ?_
  filter_upwards [SchwartzMap.coeFn_toLp (cxSchwartz f hf hcs) 2 (volume : Measure (ℝ^n)),
    coeFn_cxL2 h] with x h1 h2
  rw [h1, h2, cxSchwartz_apply]

/-- A coordinate of a graph-space element, read as a function on `ℝ^n`. -/
noncomputable def coordFun (U : W^{k,2}((Set.univ : Set (ℝ^n))))
    (a : DerivIndex n k) : ℝ^n → ℝ :=
  ((U : WkpAmbientOn n k 2 (Set.univ : Set (ℝ^n))) a : DerivLp n 2 (Set.univ : Set (ℝ^n)))

/-- Every coordinate of a graph-space element over `ℝ^n` is square integrable for Lebesgue
measure. This unwinds `DerivLp n 2 Set.univ` to plain `L²(ℝ^n)` so that the coordinates can be
complexified by `cxL2`. -/
theorem memLp_coordFun (U : W^{k,2}((Set.univ : Set (ℝ^n)))) (a : DerivIndex n k) :
    MemLp (coordFun U a) 2 (volume : Measure (ℝ^n)) := by
  simpa [coordFun, domainMeasure] using
    Lp.memLp ((U : WkpAmbientOn n k 2 (Set.univ : Set (ℝ^n))) a)

/-- The complexified base coordinate of a graph-space element. -/
noncomputable def baseL2 (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    Lp ℂ 2 (volume : Measure (ℝ^n)) :=
  cxL2 (memLp_coordFun U (baseIndex n k))

/-- The complexified `k`-fold pure derivative coordinate in direction `i`. -/
noncomputable def pureDerivL2 (U : W^{k,2}((Set.univ : Set (ℝ^n)))) (i : Fin n) :
    Lp ℂ 2 (volume : Measure (ℝ^n)) :=
  cxL2 (memLp_coordFun U (topPureDerivIndex n k i))

/-- Smooth compactly supported approximants for a graph-space element `U`, whose
`k`-fold pure derivative in direction `i` approximates the corresponding coordinate of `U`. -/
private theorem exists_globalApprox (U : W^{k,2}((Set.univ : Set (ℝ^n)))) (i : Fin n) :
    ∃ f : ℕ → (ℝ^n → ℝ),
      (∀ m, ContDiff ℝ (⊤ : ℕ∞) (f m)) ∧ (∀ m, HasCompactSupport (f m)) ∧
      Filter.Tendsto
        (fun m ↦ eLpNorm (fun x ↦ f m x - coordFun U (baseIndex n k) x) 2
          (volume : Measure (ℝ^n))) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto
        (fun m ↦ eLpNorm (fun x ↦
            iteratedPartialDeriv (n := n) (List.replicate k i) (f m) x
              - coordFun U (topPureDerivIndex n k i) x) 2
            (volume : Measure (ℝ^n)))
        Filter.atTop (𝓝 0) := by
  obtain ⟨f, hf, hcs, hbase, hderiv⟩ :=
    SobolevSpace.Approximation.globalApproximation_Wkp
      (SobolevSpace.Approximation.standardMollifier n) 2 (by simp) k
      (toRepresentative (n := n) (k := k) (p := 2) (Ω := (Set.univ : Set (ℝ^n))) U)
  refine ⟨f, hf, hcs, hbase, ?_⟩
  obtain ⟨g, _, hgweak, hgtend⟩ := hderiv (List.replicate k i) (by simp)
  have hcoord : HasWeakDerivativeOn (n := n) Set.univ (List.replicate k i)
      (coordFun U (baseIndex n k))
      (coordFun U (topPureDerivIndex n k i)) := by
    simpa [coordFun] using U.property (topPureDerivIndex n k i)
  have hae :
      g =ᵐ[(volume : Measure (ℝ^n))]
        coordFun U (topPureDerivIndex n k i) := by
    simpa [domainMeasure] using hgweak.unique_ae isOpen_univ hcoord
  refine hgtend.congr fun m ↦ ?_
  refine eLpNorm_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]

/-- The Fourier multiplier symbol `(2πi ξ_i)^k` of the `k`-fold pure derivative. -/
noncomputable def pureSymbol (n k : ℕ) (i : Fin n) : ℝ^n → ℂ :=
  fun ξ ↦ ((2 * π * Complex.I) * ((ξ.ofLp i : ℝ) : ℂ)) ^ k

/-- The complexified coordinate function has temperate growth. -/
private theorem hasTemperateGrowth_coord (i : Fin n) :
    (fun ξ : ℝ^n ↦ ((ξ.ofLp i : ℝ) : ℂ)).HasTemperateGrowth := by
  have hL := (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i)).hasTemperateGrowth
  have heq : ⇑(Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i))
      = fun ξ : ℝ^n ↦ ((ξ.ofLp i : ℝ) : ℂ) := by
    funext ξ
    simp [EuclideanSpace.proj]
  rwa [heq] at hL

/-- `fun_prop` cannot see through the `WithLp` coordinate projection, so temperate growth of
the symbol is assembled by hand from the projection and the ring operations. -/
private theorem hasTemperateGrowth_pureSymbol (i : Fin n) :
    (pureSymbol n k i).HasTemperateGrowth :=
  ((Function.HasTemperateGrowth.const (2 * π * Complex.I)).mul
    (hasTemperateGrowth_coord i)).pow k

/-- The multiplier identity on a single smooth compactly supported approximant. -/
private theorem smulLeftCLM_pureSymbol_fourier_cxSchwartz (i : Fin n) {f : ℝ^n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcs : HasCompactSupport f) :
    smulLeftCLM ℂ (pureSymbol n k i)
        ((𝓕 ((cxSchwartz f hf hcs).toLp 2 (volume : Measure (ℝ^n))) :
          Lp ℂ 2 (volume : Measure (ℝ^n))) : 𝓢'(ℝ^n, ℂ))
      = ((𝓕 ((cxSchwartz (fun x ↦ iteratedPartialDeriv (n := n) (List.replicate k i) f x)
            (PDE.contDiff_top_iteratedPartialDeriv hf _)
            (hasCompactSupport_iteratedPartialDeriv hcs _)).toLp 2
            (volume : Measure (ℝ^n))) : Lp ℂ 2 (volume : Measure (ℝ^n))) : 𝓢'(ℝ^n, ℂ)) := by
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  refine (Lp.smulLeft_toTemperedDistribution_eq_iff
    (hasTemperateGrowth_pureSymbol i)).2 ?_
  filter_upwards [SchwartzMap.coeFn_toLp (𝓕 (cxSchwartz f hf hcs)) 2
      (volume : Measure (ℝ^n)),
    SchwartzMap.coeFn_toLp (𝓕 (cxSchwartz
      (fun x ↦ iteratedPartialDeriv (n := n) (List.replicate k i) f x)
      (PDE.contDiff_top_iteratedPartialDeriv hf _)
      (hasCompactSupport_iteratedPartialDeriv hcs _))) 2 (volume : Measure (ℝ^n))]
    with ξ h1 h2
  rw [h1, h2]
  exact (fourier_cxSchwartz_iteratedPartialDeriv_replicate i hf hcs k ξ).symm

/-- The Fourier transform of the `k`-fold pure derivative coordinate is the symbol
`(2πi ξ_i)^k` times the Fourier transform of the base coordinate, as tempered distributions. -/
private theorem smulLeftCLM_pureSymbol_fourier (U : W^{k,2}((Set.univ : Set (ℝ^n))))
    (i : Fin n) :
    smulLeftCLM ℂ (pureSymbol n k i) ((𝓕 (baseL2 U) : Lp ℂ 2 (volume : Measure (ℝ^n))) : 𝓢'(ℝ^n, ℂ))
      = ((𝓕 (pureDerivL2 U i) : Lp ℂ 2 (volume : Measure (ℝ^n))) : 𝓢'(ℝ^n, ℂ)) := by
  obtain ⟨f, hf, hcs, hbase, hderivTend⟩ := exists_globalApprox U i
  have hmem : ∀ m, MemLp (f m) 2 (volume : Measure (ℝ^n)) := fun m ↦
    (hf m).continuous.memLp_of_hasCompactSupport (μ := (volume : Measure (ℝ^n))) (hcs m)
  have hmemD : ∀ m, MemLp (fun x ↦
      iteratedPartialDeriv (n := n) (List.replicate k i) (f m) x) 2
      (volume : Measure (ℝ^n)) := fun m ↦
    (PDE.contDiff_top_iteratedPartialDeriv (hf m) _).continuous.memLp_of_hasCompactSupport
      (μ := (volume : Measure (ℝ^n))) (hasCompactSupport_iteratedPartialDeriv (hcs m) _)
  have hA : Filter.Tendsto (fun m ↦ cxL2 (hmem m)) Filter.atTop (𝓝 (baseL2 U)) :=
    tendsto_cxL2 hmem (memLp_coordFun U (baseIndex n k)) hbase
  have hB : Filter.Tendsto (fun m ↦ cxL2 (hmemD m)) Filter.atTop (𝓝 (pureDerivL2 U i)) :=
    tendsto_cxL2 hmemD (memLp_coordFun U (topPureDerivIndex n k i)) hderivTend
  have hFC : Continuous (𝓕 : Lp ℂ 2 (volume : Measure (ℝ^n)) → _) :=
    (MeasureTheory.Lp.fourierTransformₗᵢ (ℝ^n) ℂ).continuous
  have hTD : Continuous (fun w : Lp ℂ 2 (volume : Measure (ℝ^n)) ↦ (w : 𝓢'(ℝ^n, ℂ))) :=
    (MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure (ℝ^n)) 2).continuous
  have hLHS : Continuous (fun w : Lp ℂ 2 (volume : Measure (ℝ^n)) ↦
      smulLeftCLM ℂ (pureSymbol n k i) ((𝓕 w : Lp ℂ 2 (volume : Measure (ℝ^n))) : 𝓢'(ℝ^n, ℂ))) :=
    (smulLeftCLM ℂ (pureSymbol n k i)).continuous.comp (hTD.comp hFC)
  have hRHS : Continuous (fun w : Lp ℂ 2 (volume : Measure (ℝ^n)) ↦
      ((𝓕 w : Lp ℂ 2 volume) : 𝓢'(ℝ^n, ℂ))) := hTD.comp hFC
  have h1 := (hLHS.tendsto (baseL2 U)).comp hA
  have h2 := (hRHS.tendsto (pureDerivL2 U i)).comp hB
  refine tendsto_nhds_unique (f := fun m ↦
    ((𝓕 (cxL2 (hmemD m)) : Lp ℂ 2 (volume : Measure (ℝ^n))) : 𝓢'(ℝ^n, ℂ))) ?_ h2
  refine h1.congr fun m ↦ ?_
  have hEq := smulLeftCLM_pureSymbol_fourier_cxSchwartz (k := k) i (hf m) (hcs m)
  rw [toLp_cxSchwartz (hf m) (hcs m) (hmem m),
    toLp_cxSchwartz (PDE.contDiff_top_iteratedPartialDeriv (hf m) _)
      (hasCompactSupport_iteratedPartialDeriv (hcs m) _) (hmemD m)] at hEq
  exact hEq

end Supporting

/-! ## The Bessel-weighted Fourier transform is square integrable -/

/-- For `U ∈ W^{k,2}(ℝ^n)`, almost every `ξ` satisfies
`pureSymbol n k i ξ * 𝓕 (baseL2 U) ξ = 𝓕 (pureDerivL2 U i) ξ` for all directions `i` at once.
This is the pointwise form of the same identity between tempered distributions. -/
theorem pureSymbol_mul_fourier_ae (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    ∀ᵐ ξ ∂(volume : Measure (ℝ^n)), ∀ i : Fin n,
      pureSymbol n k i ξ * (𝓕 (baseL2 U)) ξ
        = ((𝓕 (pureDerivL2 U i) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ := by
  rw [MeasureTheory.ae_all_iff]
  intro i
  have h := (Lp.smulLeft_toTemperedDistribution_eq_iff
    (hasTemperateGrowth_pureSymbol i)).1 (smulLeftCLM_pureSymbol_fourier U i)
  filter_upwards [h] with ξ hξ
  simpa only [smul_eq_mul] using hξ

open FourierTransform in
/-- The first derivative row of a Sobolev graph element is its distributional
derivative. The input may have only weak derivatives. -/
theorem lineDeriv_baseL2 {n : ℕ} (U : W^{1,2}(ℝ^n)) (i : Fin n) :
    ∂_{EuclideanSpace.single i (1 : ℝ)} (baseL2 U : 𝓢'(ℝ^n, ℂ)) =
      (pureDerivL2 U i : 𝓢'(ℝ^n, ℂ)) := by
  apply (fourierCLE ℂ 𝓢'(ℝ^n, ℂ)).injective
  simp only [fourierCLE_apply, fourier_lineDerivOp_eq,
    Lp.fourier_toTemperedDistribution_eq]
  have hcoord : (fun x : ℝ^n ↦
      (inner ℝ x (EuclideanSpace.single i (1 : ℝ)) : ℂ)).HasTemperateGrowth := by
    fun_prop
  change ((2 * Real.pi * Complex.I : ℂ) • smulLeftCLM ℂ
    (fun x : ℝ^n ↦ (inner ℝ x (EuclideanSpace.single i (1 : ℝ)) : ℂ))) _ = _
  rw [← smulLeftCLM_smul hcoord]
  apply (Lp.smulLeft_toTemperedDistribution_eq_iff (by fun_prop)).mpr
  filter_upwards [pureSymbol_mul_fourier_ae U] with ξ hξ
  simpa [pureSymbol, EuclideanSpace.inner_single_right, smul_eq_mul] using hξ i


/-- The modulus of the pure Fourier symbol. -/
private theorem norm_pureSymbol (i : Fin n) (ξ : ℝ^n) :
    ‖pureSymbol n k i ξ‖ = (2 * π) ^ k * |ξ.ofLp i| ^ k := by
  rw [pureSymbol, norm_pow, ← mul_pow]
  congr 1
  rw [norm_mul, norm_mul, norm_mul]
  simp [abs_of_pos Real.pi_pos]

/-- If `pureSymbol n k i ξ * 𝓕 (baseL2 U) ξ = 𝓕 (pureDerivL2 U i) ξ`, then
`|ξᵢ|^k ‖𝓕 (baseL2 U) ξ‖ ≤ ‖𝓕 (pureDerivL2 U i) ξ‖`. The exact identity carries a factor
`(2π)^{-k} ≤ 1`, which is discarded here. -/
private theorem pow_abs_mul_norm_fourier_le (U : W^{k,2}((Set.univ : Set (ℝ^n))))
    (i : Fin n) (ξ : ℝ^n)
    (h : pureSymbol n k i ξ * (𝓕 (baseL2 U)) ξ
      = ((𝓕 (pureDerivL2 U i) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ) :
    |ξ.ofLp i| ^ k * ‖(𝓕 (baseL2 U)) ξ‖
      ≤ ‖((𝓕 (pureDerivL2 U i) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ‖ := by
  have hid : (2 * π) ^ k
      * (|ξ.ofLp i| ^ k * ‖(𝓕 (baseL2 U)) ξ‖)
      = ‖((𝓕 (pureDerivL2 U i) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ‖ := by
    rw [← h, norm_mul, norm_pureSymbol]
    ring
  have hone : (1 : ℝ) ≤ (2 * π) ^ k :=
    one_le_pow₀ (by nlinarith [Real.two_le_pi])
  have hnn : (0 : ℝ) ≤ |ξ.ofLp i| ^ k *
    ‖(𝓕 (baseL2 U)) ξ‖ := by
    positivity
  calc |ξ.ofLp i| ^ k * ‖(𝓕 (baseL2 U)) ξ‖
      ≤ (2 * π) ^ k * (|ξ.ofLp i| ^ k * ‖(𝓕 (baseL2 U)) ξ‖) :=
        le_mul_of_one_le_left hnn hone
    _ = ‖((𝓕 (pureDerivL2 U i) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ‖ := hid

/-- The dimension- and order-dependent constant in the Bessel-weight domination bound. -/
noncomputable def besselWeightBound (n k : ℕ) : ℝ :=
  (2 : ℝ) ^ (k - 1) * (1 + (n : ℝ) ^ (k - 1))

/-- The domination constant `besselWeightBound n k = 2^(k-1) (1 + n^(k-1))` is nonnegative. -/
theorem besselWeightBound_nonneg (n k : ℕ) : (0 : ℝ) ≤ besselWeightBound n k := by
  rw [besselWeightBound]
  positivity

/-- If `1 ≤ k` and `pureSymbol n k i ξ * 𝓕 (baseL2 U) ξ = 𝓕 (pureDerivL2 U i) ξ` for every direction
`i`, then `‖(1 + ‖ξ‖²)^{k/2} 𝓕 (baseL2 U) ξ‖` is at most `besselWeightBound n k` times
`‖𝓕 (baseL2 U) ξ‖ + Σᵢ ‖𝓕 (pureDerivL2 U i) ξ‖`. -/
theorem norm_besselWeight_mul_fourier_le (U : W^{k,2}((Set.univ : Set (ℝ^n))))
    (hk : 1 ≤ k) (ξ : ℝ^n)
    (hξ : ∀ i : Fin n, pureSymbol n k i ξ * (𝓕 (baseL2 U)) ξ
      = ((𝓕 (pureDerivL2 U i) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ) :
    ‖(((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ)
        * (𝓕 (baseL2 U)) ξ‖
      ≤ besselWeightBound n k * (‖(𝓕 (baseL2 U)) ξ‖
          + ∑ i, ‖((𝓕 (pureDerivL2 U i) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ‖) := by
  set A := ‖(𝓕 (baseL2 U)) ξ‖ with hAdef
  set S := ∑ i, ‖((𝓕 (pureDerivL2 U i) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ‖ with hSdef
  have hA : (0 : ℝ) ≤ A := norm_nonneg _
  have hS : (0 : ℝ) ≤ S := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
  -- the weighted norm on the left is the weight times `A`
  have hlhs : ‖(((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ)
      * (𝓕 (baseL2 U)) ξ‖
      = (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) * A := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  -- the symbol bounds `symbol_le` and `sum_pow_le`
  have hsym : (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2)
      ≤ (2 : ℝ) ^ (k - 1) * (1 + (n : ℝ) ^ (k - 1) * ∑ i, |ξ.ofLp i| ^ k) :=
    (symbol_le k ξ).trans (sum_pow_le k hk ξ)
  -- the bound `pow_abs_mul_norm_fourier_le`, summed over the coordinate directions
  have hsum : (∑ i, |ξ.ofLp i| ^ k) * A ≤ S := by
    rw [hSdef, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ ↦ pow_abs_mul_norm_fourier_le U i ξ (hξ i)
  have ha : (0 : ℝ) ≤ (2 : ℝ) ^ (k - 1) := by positivity
  have hb : (0 : ℝ) ≤ (n : ℝ) ^ (k - 1) := by positivity
  rw [hlhs, besselWeightBound]
  calc (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) * A
      ≤ ((2 : ℝ) ^ (k - 1) * (1 + (n : ℝ) ^ (k - 1) * ∑ i, |ξ.ofLp i| ^ k)) * A :=
        mul_le_mul_of_nonneg_right hsym hA
    _ ≤ (2 : ℝ) ^ (k - 1) * (1 + (n : ℝ) ^ (k - 1)) * (A + S) := by
        nlinarith [mul_nonneg ha hS, mul_nonneg (mul_nonneg ha hb) hA,
          mul_le_mul_of_nonneg_left hsum (mul_nonneg ha hb)]

/-- For `k ≥ 1` the Bessel-weighted Fourier transform of the base coordinate of a
graph-space element is square integrable. -/
private theorem memLp_besselWeight (U : W^{k,2}((Set.univ : Set (ℝ^n)))) (hk : 1 ≤ k) :
    MemLp (fun ξ : ℝ^n ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ)
        * (𝓕 (baseL2 U)) ξ) 2 (volume : Measure (ℝ^n)) := by
  have hdom : MemLp (fun ξ : ℝ^n ↦ besselWeightBound n k
      * (‖(𝓕 (baseL2 U)) ξ‖
          + ∑ i, ‖((𝓕 (pureDerivL2 U i) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ‖))
      2 (volume : Measure (ℝ^n)) := by
    refine MemLp.const_mul ?_ _
    exact (Lp.memLp _).norm.add
      (memLp_finsetSum Finset.univ fun i _ ↦ (Lp.memLp _).norm)
  have htg : (fun ξ : ℝ^n ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) :
    ℂ)).HasTemperateGrowth := by
    fun_prop
  refine hdom.mono' (htg.1.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)) ?_
  filter_upwards [pureSymbol_mul_fourier_ae U] with ξ hξ
  exact norm_besselWeight_mul_fourier_le U hk ξ hξ

/-! ## The reverse inclusion -/

/-- The base coordinate of a graph-space element lies in `H^k`.

For `k = 0` this is the statement that `L² = H^0`; for `k ≥ 1` it follows from
`norm_besselWeight_mul_fourier_le`. -/
theorem memSobolev_baseL2 (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    MemSobolev (k : ℝ) 2 (baseL2 U : 𝓢'(ℝ^n, ℂ)) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    rw [Nat.cast_zero]
    exact memSobolev_zero_iff.mpr ⟨baseL2 U, rfl⟩
  · exact (memSobolev_iff_memLp_besselWeight (k : ℝ) (baseL2 U)).mpr
      (memLp_besselWeight U hk)

/-- Reverse inclusion `W^{k,2}(ℝ^n) → H^k(ℝ^n)`.

The image of a graph-space element is the tempered distribution attached to (the
complexification of) its base coordinate, which has Sobolev regularity `k` by
`memSobolev_baseL2`. -/
noncomputable def ofWkpSpace (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    H^{(k : ℝ)}(ℝ^n) :=
  (memSobolev_baseL2 U).toBesselPotentialSpace

/-- The tempered distribution underlying `ofWkpSpace U` is the one attached to the complexified
base coordinate `baseL2 U`. -/
@[simp] theorem toDistr_ofWkpSpace (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    BesselPotentialSpace.toDistr (ofWkpSpace U) = (baseL2 U : 𝓢'(ℝ^n, ℂ)) := by
  simp [ofWkpSpace]

/-- The `L²` representative of `ofWkpSpace U` is the base coordinate of `U`. -/
theorem toL2Fun_ofWkpSpace (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    toL2Fun (Nat.cast_nonneg k) (ofWkpSpace U) = baseL2 U := by
  refine (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot) ?_
  have h : BesselPotentialSpace.toDistr (ofWkpSpace U)
      = (toL2Fun (Nat.cast_nonneg k) (ofWkpSpace U) : 𝓢'(ℝ^n, ℂ)) :=
    toDistr_eq_toL2Fun (Nat.cast_nonneg k) (ofWkpSpace U)
  rw [toDistr_ofWkpSpace] at h
  exact h.symm

/-- Complexifications of real functions are real. -/
private theorem isRealL2_cxL2 {f : ℝ^n → ℝ} (hf : MemLp f 2 (volume : Measure (ℝ^n))) :
    IsRealL2 (cxL2 hf) := by
  filter_upwards [coeFn_cxL2 hf] with x hx
  rw [hx]
  simp

private theorem isRealL2_baseL2 (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    IsRealL2 (baseL2 U) :=
  isRealL2_cxL2 _

/-- The `L²` representative of `ofWkpSpace U` is real.

Together with `toL2Fun_ofWkpSpace` this is exactly the hypothesis needed to feed `ofWkpSpace U`
back into `SobolevSpace.Fractional.toWkpSpace`. -/
theorem isRealL2_toL2Fun_ofWkpSpace (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    IsRealL2 (toL2Fun (Nat.cast_nonneg k) (ofWkpSpace U)) := by
  rw [toL2Fun_ofWkpSpace]
  exact isRealL2_baseL2 U

/-- The coefficient function of `baseL2 U`. -/
private theorem coeFn_baseL2 (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    ((baseL2 U : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ)
      =ᵐ[(volume : Measure (ℝ^n))] fun x ↦ ((coordFun U (baseIndex n k) x : ℝ) : ℂ) :=
  coeFn_cxL2 (memLp_coordFun U (baseIndex n k))

/-- Round trip on functions.  The real part of the `L²` representative of `ofWkpSpace U`
agrees almost everywhere with the base coordinate of `U`. -/
theorem reOfL2_toL2Fun_ofWkpSpace (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    reOfL2 (toL2Fun (Nat.cast_nonneg k) (ofWkpSpace U))
      =ᵐ[(volume : Measure (ℝ^n))] coordFun U (baseIndex n k) := by
  rw [toL2Fun_ofWkpSpace]
  filter_upwards [coeFn_baseL2 U] with x hx
  change (((baseL2 U : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) x).re = _
  rw [hx]
  simp

/-! ## The two maps are mutually inverse

Together with `ofWkpSpace`, the map `SobolevSpace.Fractional.toWkpSpace`
identifies `W^{k,2}(ℝ^n)` with the real-representative part of `H^k(ℝ^n)`.
The final section records the linear structure; norm comparability is proved in
`Fractional.Integer.NormComparison`. -/

/-- Round trip, graph space first.  Reading off the base coordinate and re-differentiating
recovers the original tuple.  This is uniqueness of weak derivatives, via
`SobolevSpace.Fractional.graphTuple_apply_eq`. -/
theorem toWkpSpace_ofWkpSpace (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    toWkpSpace (Nat.cast_nonneg k) (ofWkpSpace U) (isRealL2_toL2Fun_ofWkpSpace U) = U := by
  refine Subtype.ext (PiLp.ext fun a ↦ ?_)
  refine graphTuple_apply_eq (Nat.cast_nonneg k) (ofWkpSpace U)
    (isRealL2_toL2Fun_ofWkpSpace U) ?_
  have hbase : coordFun U (baseIndex n k)
      =ᵐ[domainMeasure n (Set.univ : Set (ℝ^n))]
        reOfL2 (toL2Fun (Nat.cast_nonneg k) (ofWkpSpace U)) := by
    simpa [domainMeasure] using (reOfL2_toL2Fun_ofWkpSpace U).symm
  exact (hasWeakDerivativeOn_congr_ae hbase (Filter.EventuallyEq.refl _ _)).mp
    (U.property a)

/-- The base coordinate of `toWkpSpace h0 u hu` complexifies back to the `L²` representative
of `u`. -/
private theorem baseL2_toWkpSpace (u : H^{(k : ℝ)}(ℝ^n))
    (hu : IsRealL2 (toL2Fun (Nat.cast_nonneg k) u)) :
    baseL2 (toWkpSpace (Nat.cast_nonneg k) u hu) = toL2Fun (Nat.cast_nonneg k) u := by
  refine Lp.ext_iff.mpr ?_
  have h2 : coordFun (toWkpSpace (Nat.cast_nonneg k) u hu) (baseIndex n k)
      =ᵐ[(volume : Measure (ℝ^n))] reOfL2 (toL2Fun (Nat.cast_nonneg k) u) := by
    simpa [coordFun, domainMeasure] using coeFn_toDerivLp (toL2Fun (Nat.cast_nonneg k) u)
  filter_upwards [coeFn_baseL2 (toWkpSpace (Nat.cast_nonneg k) u hu), h2,
    ofReal_reOfL2_ae hu] with x hx1 hx2 hx3
  rw [hx1, hx2, ← hx3]

/-- Round trip, Sobolev space first. -/
theorem ofWkpSpace_toWkpSpace (u : H^{(k : ℝ)}(ℝ^n))
    (hu : IsRealL2 (toL2Fun (Nat.cast_nonneg k) u)) :
    ofWkpSpace (toWkpSpace (Nat.cast_nonneg k) u hu) = u := by
  refine BesselPotentialSpace.ext ?_
  rw [toDistr_ofWkpSpace, baseL2_toWkpSpace, ← toDistr_eq_toL2Fun]

/-! ## The bijection is a linear isomorphism

Every `U` is `toWkpSpace u` for `u := ofWkpSpace U`, so additivity and
homogeneity of `ofWkpSpace` follow from those of `toWkpSpace`. The two
mutually inverse maps then give a linear equivalence. -/

/-- `ofWkpSpace` is additive. Every graph-space element is `toWkpSpace` of its own image, so
this is `toWkpSpace_add` read backwards through the two round-trip identities. -/
theorem ofWkpSpace_add (U V : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    ofWkpSpace (U + V) = ofWkpSpace U + ofWkpSpace V := by
  have hU := toWkpSpace_ofWkpSpace U
  have hV := toWkpSpace_ofWkpSpace V
  conv_lhs => rw [← hU, ← hV, ← toWkpSpace_add]
  exact ofWkpSpace_toWkpSpace _ _

/-- `ofWkpSpace` is `ℝ`-homogeneous: a real scalar on the graph space acts on `H^k` through its
complexification `(c : ℂ)`. Transported from `toWkpSpace_smul` via the round trips, exactly as
for additivity. -/
theorem ofWkpSpace_smul (c : ℝ) (U : W^{k,2}((Set.univ : Set (ℝ^n)))) :
    ofWkpSpace (c • U) = (c : ℂ) • ofWkpSpace U := by
  have hr := isRealL2_toL2Fun_ofWkpSpace U
  have hcr : IsRealL2 (toL2Fun (Nat.cast_nonneg k) ((c : ℂ) • ofWkpSpace U)) := by
    rw [toL2Fun_smul]
    exact hr.smul c
  have hU := toWkpSpace_ofWkpSpace U
  conv_lhs => rw [← hU, ← toWkpSpace_smul (Nat.cast_nonneg k) c (ofWkpSpace U) hr hcr]
  exact ofWkpSpace_toWkpSpace _ _

/-- The real part of `H^k(ℝ^n)` is linearly isomorphic to the integer-order graph
space `W^{k,2}(ℝ^n)`.

This is the forward map `toWkpSpaceLinear` together with `ofWkpSpace` as its
inverse. It is an isomorphism of `ℝ`-modules. With the chosen Fourier and
derivative graph norms, this natural map is not generally isometric;
`Fractional.Integer.NormComparison` proves norm equivalence and exact norm
preservation at order zero. -/
noncomputable def toWkpSpaceEquiv (n k : ℕ) :
    HsSpaceReal n (k : ℝ)
      ≃ₗ[ℝ] W^{k,2}((Set.univ : Set (ℝ^n))) where
  toFun := toWkpSpaceLinear n k
  map_add' := map_add (toWkpSpaceLinear n k)
  map_smul' := map_smul (toWkpSpaceLinear n k)
  invFun U := HsSpaceReal.ofPhysical (Nat.cast_nonneg k) (ofWkpSpace U)
    (isRealL2_toL2Fun_ofWkpSpace U)
  left_inv u :=
    Subtype.ext
      (ofWkpSpace_toWkpSpace u.1
        (HsSpaceReal.isRealL2_toL2Fun (Nat.cast_nonneg k) u))
  right_inv U := toWkpSpace_ofWkpSpace U

end SobolevSpace.Fractional
