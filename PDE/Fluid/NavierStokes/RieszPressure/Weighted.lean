/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Algebra.Order.Chebyshev
public import PDE.Fluid.NavierStokes.RieszPressure.Smooth
public import PDE.Spaces.Sobolev.Approximation.Density.ClassicalDerivatives
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
public import PDE.Analysis.Fourier.WeightedDoubleRiesz

/-!
# The gradient of the Riesz pressure, with and without the weight `|x|²`

The pressure of incompressible flow is `P = ∑ᵢⱼ RᵢRⱼ(uᵢuⱼ)`. This module bounds `∇P` in `L²`,
and in `L²` with the weight `|x|²`, by the same norms of `∇(u ⊗ u)`:

`∫ w |∂_l P|² ≤ n² c ∑ᵢⱼ ∫ w |∂_l(uᵢuⱼ)|²`,

with `c = 1` for `w = 1` and `c = 2 + 128 n` for `w = |x|²` in dimension `n ≥ 3`. The velocity
field `u` on `ℝⁿ` is smooth, lies in `L⁴`, has bounded derivatives of every order and derivatives
of positive order in `L²`; these are the hypotheses of `contDiff_rieszPressure`. The other
weights `|x|^α`, `-n < α < n`, need the theory of `A₂` weights and are not treated.

## Main results

* `PDE.Analysis.Fourier.hasComplexWeakDerivativeOn_doubleRiesz` (all `L²` classes): `RᵢRⱼ`
  commutes with weak derivatives. `hasComplexWeakDerivativeOn_sum` gives the weak derivative of
  a finite sum.
* `NavierStokes.partialDeriv_rieszPressure_ae_eq` (all such `u`, `n ≥ 1`):
  `∂_l P = Re ∑ᵢⱼ RᵢRⱼ ∂_l(uᵢuⱼ)` almost everywhere.
* `NavierStokes.integral_sq_partialDeriv_rieszPressure_le` (all such `u`, `n ≥ 1`):
  `∫ |∂_l P|² ≤ n² ∑ᵢⱼ ∫ |∂_l(uᵢuⱼ)|²`.
* `NavierStokes.integrable_norm_sq_mul_sq_partialDeriv_rieszPressure` (all such `u`, `n ≥ 3`,
  with `|x| ∂_l(uᵢuⱼ) ∈ L²`): `∫ |x|² |∂_l P|² ≤ n² (2 + 128 n) ∑ᵢⱼ ∫ |x|² |∂_l(uᵢuⱼ)|²`.

## How it works

On the Fourier side a double Riesz transform and a weak derivative are both multiplications, so
they commute, and `∂_l P = ∑ᵢⱼ RᵢRⱼ ∂_l(uᵢuⱼ)`: both sides are weak derivatives of the class of
`P`, and weak derivatives are unique. Each `RᵢRⱼ` is a contraction of `L²`
(`norm_doubleRiesz_apply_le`), and in dimension at least three it is bounded on `L²` with the
weight `|x|²` (`integrable_norm_sq_mul_doubleRiesz`, proved with Hardy's inequality on the
Fourier side). The Cauchy–Schwarz inequality over the `n²` terms gives the factor `n²`
(`integrable_weight_mul_sq_partialDeriv_rieszPressure`).

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 2.1, Step 2 of the proof
  of Proposition 4: the bound `‖∇P |ξ|^{α/2}‖_{L²} ≲ ‖∇(Ũ ⊗ Ũ) |ξ|^{α/2}‖_{L²}`, used for
  `α = 0` and `α = 2` and quoted there from the theory of `A₂` weights.
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform Set
open scoped ENNReal

namespace PDE.Analysis.Fourier

variable {n : ℕ}

/-- The double Riesz transforms commute with weak derivatives: if `H = ∂^α F` weakly, then
`RᵢRⱼ H = ∂^α (RᵢRⱼ F)`. On the Fourier side both are multiplications. -/
theorem hasComplexWeakDerivativeOn_doubleRiesz (i j : Fin n) (α : List (Fin n))
    {F H : Lp ℂ 2 (volume : Measure (ℝ^n))}
    (h : SobolevSpace.HasComplexWeakDerivativeOn univ α F H) :
    SobolevSpace.HasComplexWeakDerivativeOn univ α (doubleRiesz i j F) (doubleRiesz i j H) := by
  rw [SobolevSpace.hasComplexWeakDerivativeOn_iff_fourier] at h ⊢
  filter_upwards [h, fourier_doubleRiesz_ae i j F, fourier_doubleRiesz_ae i j H] with ξ h1 h2 h3
  rw [h2, h3, ← h1]
  ring

/-- A finite sum of `L²` classes has the sum of the weak derivatives as its weak derivative. -/
theorem hasComplexWeakDerivativeOn_sum {ι : Type*} [Fintype ι] (α : List (Fin n))
    (F H : ι → Lp ℂ 2 (volume : Measure (ℝ^n)))
    (h : ∀ s, SobolevSpace.HasComplexWeakDerivativeOn univ α (F s) (H s)) :
    SobolevSpace.HasComplexWeakDerivativeOn univ α
      (∑ s, F s : Lp ℂ 2 (volume : Measure (ℝ^n)))
      (∑ s, H s : Lp ℂ 2 (volume : Measure (ℝ^n))) := by
  rw [SobolevSpace.hasComplexWeakDerivativeOn_iff_fourier]
  have hF : (𝓕 (∑ s, F s) : Lp ℂ 2 (volume : Measure (ℝ^n))) = ∑ s, 𝓕 (F s) :=
    map_sum (Lp.fourierTransformₗᵢ (ℝ^n) ℂ) F Finset.univ
  have hH : (𝓕 (∑ s, H s) : Lp ℂ 2 (volume : Measure (ℝ^n))) = ∑ s, 𝓕 (H s) :=
    map_sum (Lp.fourierTransformₗᵢ (ℝ^n) ℂ) H Finset.univ
  rw [hF, hH]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun s ↦ (𝓕 (F s) : Lp ℂ 2 (volume : Measure (ℝ^n)))),
    Lp.coeFn_finsetSum Finset.univ (fun s ↦ (𝓕 (H s) : Lp ℂ 2 (volume : Measure (ℝ^n)))),
    ae_all_iff.2 fun s ↦
      (SobolevSpace.hasComplexWeakDerivativeOn_iff_fourier α (F s) (H s)).1 (h s)]
    with ξ h1 h2 h3
  rw [h1, h2, Finset.sum_apply, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ ↦ h3 s

end PDE.Analysis.Fourier

namespace NavierStokes

open PDE.Analysis.Fourier SobolevSpace

variable {n : ℕ}

/-- The complex `L²` class of `∂_l (uᵢ uⱼ)`, and zero if this derivative is not square
integrable. -/
def velocityProductDerivL2 (u : ℝ^n → ℝ^n) (i j l : Fin n) :
    Lp ℂ 2 (volume : Measure (ℝ^n)) := by
  classical
  exact if h : MemLp (PDE.partialDeriv l (fun y ↦ u y i * u y j)) 2 volume then
    h.ofReal.toLp (fun x ↦ ((PDE.partialDeriv l (fun y ↦ u y i * u y j) x : ℝ) : ℂ)) else 0

/-- For square-integrable `∂_l (uᵢuⱼ)` the class `velocityProductDerivL2 u i j l` is the
complexified derivative. -/
theorem coeFn_velocityProductDerivL2 {u : ℝ^n → ℝ^n} {i j l : Fin n}
    (h : MemLp (PDE.partialDeriv l (fun y ↦ u y i * u y j)) 2 volume) :
    (velocityProductDerivL2 u i j l : ℝ^n → ℂ) =ᵐ[volume]
      fun x ↦ ((PDE.partialDeriv l (fun y ↦ u y i * u y j) x : ℝ) : ℂ) := by
  classical
  unfold velocityProductDerivL2
  simp only [h, dite_true]
  exact MemLp.coeFn_toLp _

section Smooth

variable {u : ℝ^n → ℝ^n} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hu4 : MemLp u 4 volume)
  (hbd : ∀ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k u x‖ ≤ C)
  (hd2 : ∀ k, 1 ≤ k → MemLp (iteratedFDeriv ℝ k u) 2 volume)
include hu hu4 hbd hd2

/-- The derivatives `∂_l (uᵢuⱼ)` are square integrable. -/
theorem memLp_partialDeriv_mul_component (i j l : Fin n) :
    MemLp (PDE.partialDeriv l (fun y ↦ u y i * u y j)) 2 volume := by
  have hprod : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ u x i * u x j) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hu).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hu)
  have hcont : Continuous (PDE.partialDeriv l (fun y ↦ u y i * u y j)) :=
    (hprod.continuous_fderiv (by simp)).clm_apply continuous_const
  refine (memLp_iteratedFDeriv_mul_component hu hu4 hbd hd2 i j 1).of_le
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [norm_iteratedFDeriv_one]
  calc ‖PDE.partialDeriv l (fun y ↦ u y i * u y j) x‖
      ≤ ‖fderiv ℝ (fun y ↦ u y i * u y j) x‖ * ‖EuclideanSpace.single l (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (fun y ↦ u y i * u y j) x‖ := by simp

/-- The product classes have the classes of the classical derivatives as weak derivatives. -/
theorem hasComplexWeakDerivativeOn_velocityProductL2 (i j l : Fin n) :
    HasComplexWeakDerivativeOn univ [l] (velocityProductL2 u i j)
      (velocityProductDerivL2 u i j l) := by
  have hprod : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ u x i * u x j) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hu).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hu)
  have hfun : HasComplexWeakDerivativeOn univ [l] (fun x ↦ ((u x i * u x j : ℝ) : ℂ))
      (fun x ↦ ((PDE.partialDeriv l (fun y ↦ u y i * u y j) x : ℝ) : ℂ)) := by
    refine ⟨?_, ?_⟩
    · simpa only [Complex.ofReal_re, PDE.iteratedPartialDeriv] using
        GraphSpace.hasWeakDerivativeOn_iteratedPartialDeriv (Ω := univ) hprod [l]
    · simpa only [Complex.ofReal_im] using hasWeakDerivativeOn_zero univ [l]
  refine hfun.congr_ae ?_ ?_
  · simpa [domainMeasure] using
      (coeFn_velocityProductL2 (memLp_two_mul_of_memLp_four hu4 i j)).symm
  · simpa [domainMeasure] using
      (coeFn_velocityProductDerivL2 (memLp_partialDeriv_mul_component hu hu4 hbd hd2 i j l)).symm

/-- **The derivative of the Riesz pressure.** Almost everywhere,
`∂_l P = Re ∑ᵢⱼ RᵢRⱼ ∂_l(uᵢuⱼ)`: both sides are weak derivatives of the class of `P`, because
the double Riesz transforms commute with derivatives, and weak derivatives are unique. -/
theorem partialDeriv_rieszPressure_ae_eq [Fact (0 < n)] (l : Fin n) :
    PDE.partialDeriv l (rieszPressure u) =ᵐ[volume] fun x ↦
      ((∑ i, ∑ j, doubleRiesz i j (velocityProductDerivL2 u i j l) :
        Lp ℂ 2 (volume : Measure (ℝ^n))) x).re := by
  obtain ⟨hP, -⟩ := contDiff_rieszPressure hu hu4 hbd hd2
  have hQ : HasComplexWeakDerivativeOn univ [l] (rieszPressureL2 u)
      (∑ i, ∑ j, doubleRiesz i j (velocityProductDerivL2 u i j l) :
        Lp ℂ 2 (volume : Measure (ℝ^n))) :=
    hasComplexWeakDerivativeOn_sum [l] _ _ fun i ↦ hasComplexWeakDerivativeOn_sum [l] _ _ fun j ↦
      hasComplexWeakDerivativeOn_doubleRiesz i j [l]
        (hasComplexWeakDerivativeOn_velocityProductL2 hu hu4 hbd hd2 i j l)
  have h1 : HasWeakDerivativeOn univ [l] (rieszPressure u)
      (PDE.partialDeriv l (rieszPressure u)) := by
    simpa only [PDE.iteratedPartialDeriv] using
      GraphSpace.hasWeakDerivativeOn_iteratedPartialDeriv (Ω := univ) hP [l]
  have h2 := h1.congr_ae (g := fun x ↦ (rieszPressureL2 u x).re)
    (by simpa [domainMeasure] using rieszPressure_ae_eq u) Filter.EventuallyEq.rfl
  simpa [domainMeasure] using h2.unique_ae isOpen_univ hQ.1

/-- The bound for `∂_l P` with a weight `w`, from the bound for each `RᵢRⱼ ∂_l(uᵢuⱼ)`: if every
`RᵢRⱼ` is bounded by `c` on the `n²` derivatives, then
`∫ w |∂_l P|² ≤ n² c ∑ᵢⱼ ∫ w |∂_l(uᵢuⱼ)|²`. -/
theorem integrable_weight_mul_sq_partialDeriv_rieszPressure [Fact (0 < n)] (l : Fin n)
    {w : ℝ^n → ℝ} (hwc : Continuous w) (hw0 : ∀ x, 0 ≤ w x) {c : ℝ}
    (hpiece : ∀ i j,
      Integrable (fun x ↦ w x * ‖doubleRiesz i j (velocityProductDerivL2 u i j l) x‖ ^ 2) ∧
      ∫ x, w x * ‖doubleRiesz i j (velocityProductDerivL2 u i j l) x‖ ^ 2 ≤
        c * ∫ x, w x * PDE.partialDeriv l (fun y ↦ u y i * u y j) x ^ 2) :
    Integrable (fun x ↦ w x * PDE.partialDeriv l (rieszPressure u) x ^ 2) ∧
      ∫ x, w x * PDE.partialDeriv l (rieszPressure u) x ^ 2 ≤
        (n : ℝ) ^ 2 * c *
          ∑ i, ∑ j, ∫ x, w x * PDE.partialDeriv l (fun y ↦ u y i * u y j) x ^ 2 := by
  obtain ⟨hP, -⟩ := contDiff_rieszPressure hu hu4 hbd hd2
  have hPc : Continuous (PDE.partialDeriv l (rieszPressure u)) :=
    (hP.continuous_fderiv (by simp)).clm_apply continuous_const
  set X : Fin n → Fin n → Lp ℂ 2 (volume : Measure (ℝ^n)) :=
    fun i j ↦ doubleRiesz i j (velocityProductDerivL2 u i j l) with hX
  -- pointwise: `|∂_l P|² ≤ n² ∑ᵢⱼ |Xᵢⱼ|²`
  have hle : ∀ᵐ x : ℝ^n, w x * PDE.partialDeriv l (rieszPressure u) x ^ 2 ≤
      (n : ℝ) ^ 2 * ∑ i, ∑ j, w x * ‖X i j x‖ ^ 2 := by
    filter_upwards [partialDeriv_rieszPressure_ae_eq hu hu4 hbd hd2 l,
      Lp.coeFn_finsetSum Finset.univ (fun i ↦ ∑ j, X i j),
      ae_all_iff.2 fun i ↦ Lp.coeFn_finsetSum Finset.univ (fun j ↦ X i j)] with x h1 h2 h3
    have hsum : ‖(∑ i, ∑ j, X i j : Lp ℂ 2 (volume : Measure (ℝ^n))) x‖ ≤
        ∑ i, ∑ j, ‖X i j x‖ := by
      rw [h2, Finset.sum_apply]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
      rw [h3 i, Finset.sum_apply]
      exact norm_sum_le _ _
    have hsq : (∑ i, ∑ j, ‖X i j x‖) ^ 2 ≤ (n : ℝ) ^ 2 * ∑ i, ∑ j, ‖X i j x‖ ^ 2 := by
      have ha := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
        (f := fun i ↦ ∑ j, ‖X i j x‖)
      have hb (i : Fin n) := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
        (f := fun j ↦ ‖X i j x‖)
      simp only [Finset.card_univ, Fintype.card_fin] at ha hb
      calc (∑ i, ∑ j, ‖X i j x‖) ^ 2 ≤ n * ∑ i, (∑ j, ‖X i j x‖) ^ 2 := ha
        _ ≤ n * ∑ i, n * ∑ j, ‖X i j x‖ ^ 2 :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ hb i) (Nat.cast_nonneg n)
        _ = (n : ℝ) ^ 2 * ∑ i, ∑ j, ‖X i j x‖ ^ 2 := by
            rw [← Finset.mul_sum]
            ring
    have habs : PDE.partialDeriv l (rieszPressure u) x ^ 2 ≤
        (∑ i, ∑ j, ‖X i j x‖) ^ 2 := by
      rw [h1, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) ((Complex.abs_re_le_norm _).trans hsum) 2
    calc w x * PDE.partialDeriv l (rieszPressure u) x ^ 2
        ≤ w x * ((n : ℝ) ^ 2 * ∑ i, ∑ j, ‖X i j x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (habs.trans hsq) (hw0 x)
      _ = (n : ℝ) ^ 2 * ∑ i, ∑ j, w x * ‖X i j x‖ ^ 2 := by
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
          ring
  have hmaj : Integrable (fun x : ℝ^n ↦ (n : ℝ) ^ 2 * ∑ i, ∑ j, w x * ‖X i j x‖ ^ 2) :=
    (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ (hpiece i j).1).const_mul _
  have hint : Integrable (fun x ↦ w x * PDE.partialDeriv l (rieszPressure u) x ^ 2) :=
    hmaj.mono' (hwc.mul (hPc.pow 2)).aestronglyMeasurable (hle.mono fun x hx ↦ by
      rwa [Real.norm_of_nonneg (mul_nonneg (hw0 x) (sq_nonneg _))])
  refine ⟨hint, (integral_mono_ae hint hmaj hle).trans ?_⟩
  rw [integral_const_mul, integral_finsetSum _ fun i _ ↦
    integrable_finsetSum _ fun j _ ↦ (hpiece i j).1, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ (hpiece i j).1, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ ↦ (hpiece i j).2

/-- **The gradient of the Riesz pressure in `L²`**: `∫ |∂_l P|² ≤ n² ∑ᵢⱼ ∫ |∂_l(uᵢuⱼ)|²`. The
proof uses only that the double Riesz transforms are contractions of `L²`. -/
theorem integral_sq_partialDeriv_rieszPressure_le [Fact (0 < n)] (l : Fin n) :
    Integrable (fun x ↦ PDE.partialDeriv l (rieszPressure u) x ^ 2) ∧
      ∫ x, PDE.partialDeriv l (rieszPressure u) x ^ 2 ≤
        (n : ℝ) ^ 2 * ∑ i, ∑ j, ∫ x, PDE.partialDeriv l (fun y ↦ u y i * u y j) x ^ 2 := by
  have hpiece (i j : Fin n) :
      Integrable (fun x ↦ (1 : ℝ) * ‖doubleRiesz i j (velocityProductDerivL2 u i j l) x‖ ^ 2) ∧
      ∫ x, (1 : ℝ) * ‖doubleRiesz i j (velocityProductDerivL2 u i j l) x‖ ^ 2 ≤
        1 * ∫ x, (1 : ℝ) * PDE.partialDeriv l (fun y ↦ u y i * u y j) x ^ 2 := by
    simp only [one_mul]
    refine ⟨(Lp.memLp _).norm.integrable_sq, ?_⟩
    have hH := coeFn_velocityProductDerivL2
      (memLp_partialDeriv_mul_component hu hu4 hbd hd2 i j l)
    calc ∫ x, ‖doubleRiesz i j (velocityProductDerivL2 u i j l) x‖ ^ 2
        = ‖doubleRiesz i j (velocityProductDerivL2 u i j l)‖ ^ 2 :=
          (Lp.norm_sq_eq_integral_norm_sq _).symm
      _ ≤ ‖velocityProductDerivL2 u i j l‖ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_doubleRiesz_apply_le i j _) 2
      _ = ∫ x, ‖velocityProductDerivL2 u i j l x‖ ^ 2 := Lp.norm_sq_eq_integral_norm_sq _
      _ = ∫ x, PDE.partialDeriv l (fun y ↦ u y i * u y j) x ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards [hH] with x hx
          rw [hx, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simpa only [one_mul, mul_one] using
    integrable_weight_mul_sq_partialDeriv_rieszPressure hu hu4 hbd hd2 l
      (w := fun _ ↦ 1) continuous_const (fun _ ↦ zero_le_one) hpiece

/-- **The gradient of the Riesz pressure with the weight `|x|²`**, `n ≥ 3`: if every
`|x| ∂_l(uᵢuⱼ)` is square integrable, then so is `|x| ∂_l P`, and
`∫ |x|² |∂_l P|² ≤ n² (2 + 128 n) ∑ᵢⱼ ∫ |x|² |∂_l(uᵢuⱼ)|²`. The weighted bound for each `RᵢRⱼ`
is `integrable_norm_sq_mul_doubleRiesz`, and no theory of `A₂` weights is used. -/
theorem integrable_norm_sq_mul_sq_partialDeriv_rieszPressure (hn : 3 ≤ n) (l : Fin n)
    (hw : ∀ i j, Integrable
      (fun x ↦ ‖x‖ ^ 2 * PDE.partialDeriv l (fun y ↦ u y i * u y j) x ^ 2)) :
    Integrable (fun x ↦ ‖x‖ ^ 2 * PDE.partialDeriv l (rieszPressure u) x ^ 2) ∧
      ∫ x, ‖x‖ ^ 2 * PDE.partialDeriv l (rieszPressure u) x ^ 2 ≤
        (n : ℝ) ^ 2 * (2 + 128 * n) *
          ∑ i, ∑ j, ∫ x, ‖x‖ ^ 2 * PDE.partialDeriv l (fun y ↦ u y i * u y j) x ^ 2 := by
  have : Fact (0 < n) := ⟨by omega⟩
  refine integrable_weight_mul_sq_partialDeriv_rieszPressure hu hu4 hbd hd2 l
    (w := fun x ↦ ‖x‖ ^ 2) (continuous_norm.pow 2) (fun x ↦ sq_nonneg _) fun i j ↦ ?_
  have hH := coeFn_velocityProductDerivL2 (memLp_partialDeriv_mul_component hu hu4 hbd hd2 i j l)
  have hfun : (fun x : ℝ^n ↦ ‖x‖ ^ 2 * ‖velocityProductDerivL2 u i j l x‖ ^ 2) =ᵐ[volume]
      fun x ↦ ‖x‖ ^ 2 * PDE.partialDeriv l (fun y ↦ u y i * u y j) x ^ 2 := by
    filter_upwards [hH] with x hx
    rw [hx, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h := integrable_norm_sq_mul_doubleRiesz hn i j (velocityProductDerivL2 u i j l)
    ((hw i j).congr hfun.symm)
  rwa [integral_congr_ae hfun] at h

end Smooth

end NavierStokes
