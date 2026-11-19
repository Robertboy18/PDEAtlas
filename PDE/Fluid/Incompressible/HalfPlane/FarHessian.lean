/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.SymmetrizedLogKernelTaylor
public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.QuadrantPotential
public import PDE.Fluid.Incompressible.HalfPlane.WeightedStreamBounds
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# The velocity gradient of a far density to fourth order

Let `f` be a far density of radius `R` (`GreenFunction.IsQuadrantFarDensity`: `f = 0` on the
quadrant inside `B(0, R)` and `f/|y|²` integrable there) and `Ψ = quadrantPotential f` its grouped
stream function, smooth on `B(0, R/2)` with `∂ₗ∂ₖΨ(x) = π⁻¹ ∫_{ℝ²₊₊} kₖₗₛ(x, y) f(y) dy`, where
`kₖₗₛ = symmetrizedKernel (hessianKernel k l)` is the odd-odd symmetrization of the planar Hessian
kernel. Its Hessian has the far-part expansion of Chen and Hou, Part I, Lemma 6.11 and Appendix
C.3.3:

`∂ₗ∂ₖΨ(x) = c mₖₗ + d ∂ₖ∂ₗG(x) + O(|x|⁴ ∫ |f|/|y|⁶)`,

with `c = mixedCoefficient f = (4/π) ∫ K₁ f` (`∂₀∂₁Ψ(0)`), `d = quarticCoefficient f = (4/π) ∫ q f`
(`∂₀³∂₁Ψ(0)`), `K₁ = hessianKernel 0 1`, `q = quarticKernel`, `mₖₗ = ∂ₖ∂ₗ(x₀ x₁)`
(`partialDeriv_partialDeriv_mul_coord`) and `G = quarticHarmonic`, `G(x) = (x₀³ x₁ - x₀ x₁³)/6`
(`partialDeriv_partialDeriv_quarticHarmonic`). Integrals without a domain run over the quadrant
`ℝ²₊₊`.

## Main definitions

* `quarticHarmonic`: the quartic harmonic `G(x) = (x₀³ x₁ - x₀ x₁³)/6`.
* `quarticCoefficient`: the fourth Taylor coefficient `d = (4/π) ∫_{ℝ²₊₊} q f` of the grouped stream
  function.

## Main results

* `IsQuadrantFarDensity.integrableOn_div_pow`,
  `IsQuadrantFarDensity.integrableOn_hessianKernel_mul`,
  `IsQuadrantFarDensity.integrableOn_quarticKernel_mul`: `f/|y|ⁿ` for `n ≥ 2`, `K₁ f` and `q f` are
  integrable on the quadrant.
* `IsQuadrantFarDensity.abs_hessian_le`: `|∂ₗ∂ₖΨ(x)| ≤ 2 ∫ |f|/|y|²` for `|x| < R/2`.
* `IsQuadrantFarDensity.abs_hessian_sub_le`: `|∂ₗ∂ₖΨ(x) - ∂ₗ∂ₖΨ(z)| ≤ 8 |x - z| ∫ |f|/|y|³` for
  `4|x|, 4|z| ≤ R`.
* `IsQuadrantFarDensity.abs_hessian_sub_expansion_le`: the expansion with remainder
  `184/(9π) |x|⁴ ∫ |f|/|y|⁶` for `|x| < R/2`.
* `IsQuadrantFarDensity.abs_hessian_expansion_sub_le`: the Lipschitz bound
  `2944/(9π) max(|x|, |z|)³ |x - z| ∫ |f|/|y|⁶` of `∂ₗ∂ₖΨ - d ∂ₖ∂ₗG` for `4|x|, 4|z| ≤ R`.

## How it works

Integrating the Taylor polynomial `4 K₁(y) mₖₗ + 4 q(y) ∂ₖ∂ₗG(x)` of the kernel against `π⁻¹ f`
gives `c mₖₗ + d ∂ₖ∂ₗG(x)`, so the error of the expansion is `π⁻¹` times the integral of the kernel
remainder `kₖₗₛ(x, y) - 4 K₁(y) mₖₗ - 4 q(y) ∂ₖ∂ₗG(x)` against `f`. Since `f` vanishes on the
quadrant inside `B(0, R)`, only points with `2|x| ≤ |y|` contribute when `|x| < R/2`, and only
points with `4|x| ≤ |y|` when `4|x| ≤ R`. There the pointwise bounds
`GreenFunction.abs_symmetrizedKernel_hessianKernel_le`,
`GreenFunction.abs_symmetrizedKernel_hessianKernel_sub_le`,
`GreenFunction.abs_symmetrizedKernel_hessianKernel_remainder_le` and
`GreenFunction.abs_symmetrizedKernel_hessianKernel_remainder_sub_le` bound the kernel, its
increments, its remainder and the increments of the remainder by constants times `|y|⁻²`,
`|x - z| |y|⁻³`, `|x|⁴ |y|⁻⁶` and `max(|x|, |z|)³ |x - z| |y|⁻⁶`, and integrating these bounds
against `|f|` gives the four estimates. The same support argument gives
`|f|/|y|ⁿ ≤ R^{2-n} |f|/|y|²`, which with `|K₁(y)| ≤ 1/(2|y|²)` and `|q(y)| ≤ 6/|y|⁴`
(`abs_quarticKernel_le`) proves the integrability results.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Lemma 6.11, p. 107, (4.26), p. 46,
  and Appendix C.3.3, pp. 146-148.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set GreenFunction PotentialTheory PotentialTheory.Planar

namespace IncompressibleFlow

/-- The quartic harmonic `G(x) = (x₀³ x₁ - x₀ x₁³)/6`. -/
def quarticHarmonic (x : ℝ^2) : ℝ :=
  (x 0 ^ 3 * x 1 - x 0 * x 1 ^ 3) / 6

/-- If `g` has derivative `a(x) dx₀ + b(x) dx₁` at every point `x`, then `∂₀g = a` and `∂₁g = b`. -/
private theorem partialDeriv_of_hasFDerivAt {g a b : ℝ^2 → ℝ}
    (h : ∀ x, HasFDerivAt g (a x • (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ) +
      b x • (EuclideanSpace.proj 1 : ℝ^2 →L[ℝ] ℝ)) x) :
    ∂[(0 : Fin 2)] g = a ∧ ∂[(1 : Fin 2)] g = b := by
  constructor <;> funext x <;> change fderiv ℝ g x _ = _ <;> rw [(h x).fderiv] <;> simp

/-- The coordinate `y ↦ y₀` has derivative `EuclideanSpace.proj 0` at every point. -/
private theorem h0 (x : ℝ^2) :
    HasFDerivAt (fun y : ℝ^2 ↦ y 0) (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ) x :=
  (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).hasFDerivAt

/-- The coordinate `y ↦ y₁` has derivative `EuclideanSpace.proj 1` at every point. -/
private theorem h1 (x : ℝ^2) :
    HasFDerivAt (fun y : ℝ^2 ↦ y 1) (EuclideanSpace.proj 1 : ℝ^2 →L[ℝ] ℝ) x :=
  (EuclideanSpace.proj (1 : Fin 2) : ℝ^2 →L[ℝ] ℝ).hasFDerivAt

/-- The first derivatives of `G` are `∂₀G = (3x₀²x₁ - x₁³)/6` and `∂₁G = (x₀³ - 3x₀x₁²)/6`. -/
private theorem partialDeriv_quarticHarmonic :
    ∂[(0 : Fin 2)] quarticHarmonic = (fun x ↦ (3 * x 0 ^ 2 * x 1 - x 1 ^ 3) / 6) ∧
      ∂[(1 : Fin 2)] quarticHarmonic = (fun x ↦ (x 0 ^ 3 - 3 * x 0 * x 1 ^ 2) / 6) := by
  refine partialDeriv_of_hasFDerivAt fun x ↦ ?_
  have := ((((h0 x).pow 3).mul (h1 x)).sub ((h0 x).mul ((h1 x).pow 3))).mul_const (1 / 6 : ℝ)
  convert this using 1
  · funext y; simp only [quarticHarmonic, Pi.sub_apply, Pi.mul_apply]; ring
  · ext v
    simp
    ring

/-- The first derivatives of `(3x₀²x₁ - x₁³)/6` are `x₀x₁` and `(x₀² - x₁²)/2`. -/
private theorem partialDeriv_cubic_zero :
    ∂[(0 : Fin 2)] (fun x : ℝ^2 ↦ (3 * x 0 ^ 2 * x 1 - x 1 ^ 3) / 6) = (fun x ↦ x 0 * x 1) ∧
      ∂[(1 : Fin 2)] (fun x : ℝ^2 ↦ (3 * x 0 ^ 2 * x 1 - x 1 ^ 3) / 6) =
        (fun x ↦ (x 0 ^ 2 - x 1 ^ 2) / 2) := by
  refine partialDeriv_of_hasFDerivAt fun x ↦ ?_
  have := ((((h0 x).pow 2).mul (h1 x)).const_mul (3 : ℝ) |>.sub ((h1 x).pow 3)).mul_const
    (1 / 6 : ℝ)
  convert this using 1
  · funext y; simp only [Pi.sub_apply, Pi.mul_apply]; ring
  · ext v
    simp
    ring

/-- The first derivatives of `(x₀³ - 3x₀x₁²)/6` are `(x₀² - x₁²)/2` and `-x₀x₁`. -/
private theorem partialDeriv_cubic_one :
    ∂[(0 : Fin 2)] (fun x : ℝ^2 ↦ (x 0 ^ 3 - 3 * x 0 * x 1 ^ 2) / 6) =
        (fun x ↦ (x 0 ^ 2 - x 1 ^ 2) / 2) ∧
      ∂[(1 : Fin 2)] (fun x : ℝ^2 ↦ (x 0 ^ 3 - 3 * x 0 * x 1 ^ 2) / 6) =
        (fun x ↦ -(x 0 * x 1)) := by
  refine partialDeriv_of_hasFDerivAt fun x ↦ ?_
  have := (((h0 x).pow 3).sub (((h0 x).mul ((h1 x).pow 2)).const_mul (3 : ℝ))).mul_const
    (1 / 6 : ℝ)
  convert this using 1
  · funext y; simp only [Pi.sub_apply, Pi.mul_apply]; ring
  · ext v
    simp
    ring

/-- The Hessian of the quartic harmonic: `∂ₗ∂ₖ G = quarticHessian k l`. -/
theorem partialDeriv_partialDeriv_quarticHarmonic (k l : Fin 2) (x : ℝ^2) :
    (∂[l] (∂[k] quarticHarmonic)) x = quarticHessian k l x := by
  obtain ⟨a0, a1⟩ := partialDeriv_quarticHarmonic
  obtain ⟨b0, b1⟩ := partialDeriv_cubic_zero
  obtain ⟨c0, c1⟩ := partialDeriv_cubic_one
  fin_cases k <;> fin_cases l
  · simp only [Fin.zero_eta, Fin.isValue, a0, b0, quarticHessian, ite_true]
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, a0, b1, quarticHessian]; simp
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, a1, c0, quarticHessian]; simp
  · simp only [Fin.mk_one, Fin.isValue, a1, c1, quarticHessian]; simp

/-- The first derivatives of `x₀x₁` are `∂₀(x₀x₁) = x₁` and `∂₁(x₀x₁) = x₀`. -/
private theorem partialDeriv_mixed :
    ∂[(0 : Fin 2)] (fun x : ℝ^2 ↦ x 0 * x 1) = (fun x ↦ x 1) ∧
      ∂[(1 : Fin 2)] (fun x : ℝ^2 ↦ x 0 * x 1) = (fun x ↦ x 0) := by
  refine partialDeriv_of_hasFDerivAt fun x ↦ ?_
  convert (h0 x).mul (h1 x) using 1
  ext v
  simp
  ring

/-- The first derivatives of the coordinates are `∂ᵢxⱼ = δᵢⱼ`. -/
private theorem partialDeriv_coordinate :
    (∂[(0 : Fin 2)] (fun x : ℝ^2 ↦ x 0) = fun _ ↦ 1) ∧
      (∂[(1 : Fin 2)] (fun x : ℝ^2 ↦ x 0) = fun _ ↦ 0) ∧
      (∂[(0 : Fin 2)] (fun x : ℝ^2 ↦ x 1) = fun _ ↦ 0) ∧
      (∂[(1 : Fin 2)] (fun x : ℝ^2 ↦ x 1) = fun _ ↦ 1) := by
  have e0 := partialDeriv_of_hasFDerivAt (a := fun _ ↦ 1) (b := fun _ ↦ 0) fun x ↦ by
    convert h0 x using 1; ext v; simp
  have e1 := partialDeriv_of_hasFDerivAt (a := fun _ ↦ 0) (b := fun _ ↦ 1) fun x ↦ by
    convert h1 x using 1; ext v; simp
  exact ⟨e0.1, e0.2, e1.1, e1.2⟩

/-- The Hessian of the monomial `x₀ x₁`: `∂ₗ∂ₖ(x₀ x₁) = 1` for `k ≠ l` and `0` otherwise. -/
theorem partialDeriv_partialDeriv_mul_coord (k l : Fin 2) (x : ℝ^2) :
    (∂[l] (∂[k] (fun y : ℝ^2 ↦ y 0 * y 1))) x = if k = l then 0 else 1 := by
  obtain ⟨m0, m1⟩ := partialDeriv_mixed
  obtain ⟨p00, p01, p10, p11⟩ := partialDeriv_coordinate
  fin_cases k <;> fin_cases l
  · simp only [Fin.zero_eta, Fin.isValue, m0, p10, ite_true]
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, m0, p11]; simp
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, m1, p00]; simp
  · simp only [Fin.mk_one, Fin.isValue, m1, p01, ite_true]

/-! ### Far densities -/

/-- The quartic coefficient `(4/π) ∫_{ℝ²₊₊} q(y) f(y) dy`, `q = quarticKernel`: the fourth Taylor
coefficient `∂₀³∂₁Ψ(0)` of the grouped stream function, Chen and Hou, Part I, Lemma 6.11 and
(4.26). -/
def quarticCoefficient (f : ℝ^2 → ℝ) : ℝ :=
  4 / Real.pi * ∫ y in quadrant, quarticKernel y * f y

variable {f : ℝ^2 → ℝ} {R : ℝ}

/-- A far density of radius `R` vanishes on the quadrant inside `B(0, R)`, so `R ≤ |y|` at every
point `y` of the quadrant with `f(y) ≠ 0`. -/
private theorem norm_le_of_ne_zero (hf : IsQuadrantFarDensity f R) {y : ℝ^2}
    (hy : y ∈ quadrant) (hfy : f y ≠ 0) : R ≤ ‖y‖ := by
  by_contra h
  exact hfy (hf.eq_zero y hy (lt_of_not_ge h))

/-- `|y₀ y₁| ≤ |y|²/2`. -/
theorem abs_mul_coord_le (y : ℝ^2) : |y 0 * y 1| ≤ ‖y‖ ^ 2 / 2 := by
  rw [EuclideanSpace.norm_sq_fin_two, abs_mul]
  nlinarith [sq_nonneg (|y 0| - |y 1|), sq_abs (y 0), sq_abs (y 1)]

/-- `|y₀² - y₁²| ≤ |y|²`. -/
theorem abs_sq_sub_sq_coord_le (y : ℝ^2) : |y 0 ^ 2 - y 1 ^ 2| ≤ ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_fin_two, abs_le]
  constructor <;> nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]

/-- `f(y)/|y|ⁿ`, `n ≥ 2`, is integrable on the quadrant for a far density. -/
theorem _root_.GreenFunction.IsQuadrantFarDensity.integrableOn_div_pow
    (hf : IsQuadrantFarDensity f R) {n : ℕ} (hn : 2 ≤ n) :
    IntegrableOn (fun y ↦ f y / ‖y‖ ^ n) quadrant := by
  have hR := hf.pos
  have hm : AEStronglyMeasurable (fun y ↦ f y / ‖y‖ ^ n) (volume.restrict quadrant) := by
    have hinv : Measurable fun y : ℝ^2 ↦ (‖y‖ ^ n)⁻¹ := (measurable_norm.pow_const n).inv
    simp only [div_eq_mul_inv]
    exact hf.aestronglyMeasurable.mul hinv.aestronglyMeasurable
  refine Integrable.mono' (hf.integrableOn.norm.const_mul (1 / R ^ (n - 2))) hm ?_
  filter_upwards [ae_restrict_mem measurableSet_quadrant] with y hy
  by_cases hfy : f y = 0
  · simp only [hfy, zero_div, norm_zero]; positivity
  have hRy := norm_le_of_ne_zero hf hy hfy
  have hy0 : 0 < ‖y‖ := lt_of_lt_of_le hR hRy
  rw [norm_div, norm_div, Real.norm_eq_abs, norm_pow, norm_norm, norm_pow, norm_norm,
    show ‖y‖ ^ n = ‖y‖ ^ 2 * ‖y‖ ^ (n - 2) by rw [← pow_add]; congr 1; omega, ← div_div,
    show 1 / R ^ (n - 2) * (|f y| / ‖y‖ ^ 2) = |f y| / ‖y‖ ^ 2 / R ^ (n - 2) by ring]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_left₀ hR.le hRy _)

/-- `|f(y)|/|y|ⁿ`, `n ≥ 2`, is integrable on the quadrant for a far density. -/
theorem _root_.GreenFunction.IsQuadrantFarDensity.integrableOn_abs_div_pow
    (hf : IsQuadrantFarDensity f R) {n : ℕ} (hn : 2 ≤ n) :
    IntegrableOn (fun y ↦ |f y| / ‖y‖ ^ n) quadrant :=
  (hf.integrableOn_div_pow hn).norm.congr (Eventually.of_forall fun y ↦ by
    simp only [norm_div, Real.norm_eq_abs, norm_pow, abs_norm])

/-- The kernel `K₁ = hessianKernel 0 1` is measurable. -/
private theorem measurable_hessianKernel_zero_one :
    Measurable (hessianKernel 0 1 : ℝ^2 → ℝ) := by
  have : (hessianKernel 0 1 : ℝ^2 → ℝ) = fun z ↦ z 0 * z 1 / ‖z‖ ^ 4 :=
    funext hessianKernel_zero_one
  rw [this]
  fun_prop

/-- The quartic kernel `q` is measurable. -/
private theorem measurable_quarticKernel : Measurable quarticKernel := by
  unfold quarticKernel
  fun_prop

/-- `K₁ f` is integrable on the quadrant for a far density. -/
theorem _root_.GreenFunction.IsQuadrantFarDensity.integrableOn_hessianKernel_mul
    (hf : IsQuadrantFarDensity f R) :
    IntegrableOn (fun y ↦ hessianKernel 0 1 y * f y) quadrant := by
  refine Integrable.mono' ((hf.integrableOn_abs_div_pow le_rfl).const_mul (1 / 2))
    (measurable_hessianKernel_zero_one.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_quadrant] with y hy
  have hy0 : 0 < ‖y‖ := norm_pos_of_mem_quadrant hy
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, hessianKernel_zero_one, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < ‖y‖ ^ 4)]
  have h := abs_mul_coord_le y
  calc |y 0 * y 1| / ‖y‖ ^ 4 * |f y| ≤ ‖y‖ ^ 2 / 2 / ‖y‖ ^ 4 * |f y| := by gcongr
    _ = 1 / 2 * (|f y| / ‖y‖ ^ 2) := by field_simp

/-- `|q(y)| ≤ 6/|y|⁴`. -/
theorem abs_quarticKernel_le (y : ℝ^2) : |quarticKernel y| ≤ 6 / ‖y‖ ^ 4 := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [quarticKernel]
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
  unfold quarticKernel
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < ‖y‖ ^ 8),
    show 12 * y 0 * y 1 * (y 0 ^ 2 - y 1 ^ 2) = 12 * (y 0 * y 1) * (y 0 ^ 2 - y 1 ^ 2) by ring,
    abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
  have h1 := abs_mul_coord_le y
  have h2 := abs_sq_sub_sq_coord_le y
  calc 12 * |y 0 * y 1| * |y 0 ^ 2 - y 1 ^ 2| / ‖y‖ ^ 8
      ≤ 12 * (‖y‖ ^ 2 / 2) * ‖y‖ ^ 2 / ‖y‖ ^ 8 := by gcongr
    _ = 6 / ‖y‖ ^ 4 := by field_simp; ring

/-- `q f` is integrable on the quadrant for a far density. -/
theorem _root_.GreenFunction.IsQuadrantFarDensity.integrableOn_quarticKernel_mul
    (hf : IsQuadrantFarDensity f R) :
    IntegrableOn (fun y ↦ quarticKernel y * f y) quadrant := by
  refine Integrable.mono' ((hf.integrableOn_abs_div_pow (by norm_num : 2 ≤ 4)).const_mul 6)
    (measurable_quarticKernel.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_quadrant] with y hy
  have hy0 : 0 < ‖y‖ := norm_pos_of_mem_quadrant hy
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |quarticKernel y| * |f y| ≤ 6 / ‖y‖ ^ 4 * |f y| := by
        gcongr; exact abs_quarticKernel_le y
    _ = 6 * (|f y| / ‖y‖ ^ 4) := by ring

/-- A pointwise bound `|F| ≤ C |f|/|y|ⁿ` on the support of a far density bounds `∫_Q F`. -/
private theorem abs_setIntegral_le_mul (hf : IsQuadrantFarDensity f R) {n : ℕ} (hn : 2 ≤ n)
    {F : ℝ^2 → ℝ} {C : ℝ} (h0 : ∀ y ∈ quadrant, f y = 0 → F y = 0)
    (hF : ∀ y ∈ quadrant, f y ≠ 0 → |F y| ≤ C * (|f y| / ‖y‖ ^ n)) :
    |∫ y in quadrant, F y| ≤ C * ∫ y in quadrant, |f y| / ‖y‖ ^ n := by
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((hf.integrableOn_abs_div_pow hn).const_mul C) ?_
  filter_upwards [ae_restrict_mem measurableSet_quadrant] with y hy
  rw [Real.norm_eq_abs]
  by_cases hfy : f y = 0
  · rw [h0 y hy hfy, hfy]; simp
  · exact hF y hy hfy

/-- The Taylor polynomial `Tₖₗ(x, y) = 4 K₁(y) mₖₗ + 4 q(y) ∂ₖ∂ₗG(x)` of the kernel. -/
private def taylor (k l : Fin 2) (x y : ℝ^2) : ℝ :=
  4 * hessianKernel 0 1 y * (if k = l then 0 else 1) + 4 * quarticKernel y * quarticHessian k l x

/-- For a far density `f`, the product `Tₖₗ(x, ·) f` of the Taylor polynomial of the kernel with
`f` is integrable on the quadrant. -/
private theorem integrableOn_taylor_mul (hf : IsQuadrantFarDensity f R) (k l : Fin 2)
    (x : ℝ^2) : IntegrableOn (fun y ↦ taylor k l x y * f y) quadrant := by
  have h := ((hf.integrableOn_hessianKernel_mul).const_mul (4 * (if k = l then 0 else 1))).add
    ((hf.integrableOn_quarticKernel_mul).const_mul (4 * quarticHessian k l x))
  refine h.congr (Eventually.of_forall fun y ↦ ?_)
  simp only [taylor, Pi.add_apply]
  ring

/-- The Hessian of the far potential minus its expansion as a remainder integral. -/
private theorem hessian_sub_expansion_eq (hf : IsQuadrantFarDensity f R) (k l : Fin 2)
    {x : ℝ^2} (hx : ‖x‖ < R / 2) :
    (∂[l] (∂[k] (quadrantPotential f))) x -
        (mixedCoefficient f * (if k = l then 0 else 1) +
          quarticCoefficient f * quarticHessian k l x) =
      1 / Real.pi * ∫ y in quadrant,
        (symmetrizedKernel (hessianKernel k l) x y - taylor k l x y) * f y := by
  have hks := integrableOn_symmetrizedKernel_hessianKernel_of_far hf k l hx
  have hT : ∫ y in quadrant, taylor k l x y * f y =
      4 * (if k = l then 0 else 1) * (∫ y in quadrant, hessianKernel 0 1 y * f y) +
        4 * quarticHessian k l x * ∫ y in quadrant, quarticKernel y * f y := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hf.integrableOn_hessianKernel_mul).const_mul _)
        ((hf.integrableOn_quarticKernel_mul).const_mul _)]
    refine setIntegral_congr_fun measurableSet_quadrant fun y _ ↦ ?_
    simp only [taylor]
    ring
  simp_rw [sub_mul]
  rw [integral_sub hks (integrableOn_taylor_mul hf k l x), hT,
    partialDeriv_partialDeriv_quadrantPotential_ball hf k l hx, mixedCoefficient,
    quarticCoefficient]
  ring

/-- For `|x| < R/2` and a point `y` of the quadrant where the far density `f` of radius `R` does not
vanish, `2|x| ≤ |y|`. -/
private theorem two_mul_le (hf : IsQuadrantFarDensity f R) {x y : ℝ^2} (hx : ‖x‖ < R / 2)
    (hy : y ∈ quadrant) (hfy : f y ≠ 0) : 2 * ‖x‖ ≤ ‖y‖ := by
  have := norm_le_of_ne_zero hf hy hfy
  linarith

/-- For `4|x| ≤ R` and a point `y` of the quadrant where the far density `f` of radius `R` does not
vanish, `4|x| ≤ |y|`. -/
private theorem four_mul_le (hf : IsQuadrantFarDensity f R) {x y : ℝ^2} (hx : 4 * ‖x‖ ≤ R)
    (hy : y ∈ quadrant) (hfy : f y ≠ 0) : 4 * ‖x‖ ≤ ‖y‖ :=
  hx.trans (norm_le_of_ne_zero hf hy hfy)

/-- **Size of the far velocity gradient**: for a far density of radius `R` and `|x| < R/2`,
`|∂ₗ∂ₖΨ(x)| ≤ 2 ∫_{ℝ²₊₊} |f(y)|/|y|² dy`. -/
theorem _root_.GreenFunction.IsQuadrantFarDensity.abs_hessian_le
    (hf : IsQuadrantFarDensity f R) (k l : Fin 2) {x : ℝ^2} (hx : ‖x‖ < R / 2) :
    |(∂[l] (∂[k] (quadrantPotential f))) x| ≤ 2 * ∫ y in quadrant, |f y| / ‖y‖ ^ 2 := by
  rw [partialDeriv_partialDeriv_quadrantPotential_ball hf k l hx, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
  have h := abs_setIntegral_le_mul hf le_rfl (C := 2 * Real.pi)
    (F := fun y ↦ symmetrizedKernel (hessianKernel k l) x y * f y)
    (fun y _ hfy ↦ by simp [hfy]) fun y hy hfy ↦ by
      rw [abs_mul]
      have hk := abs_symmetrizedKernel_hessianKernel_le k l (ne_zero_of_mem_quadrant hy)
        (two_mul_le hf hx hy hfy)
      calc |symmetrizedKernel (hessianKernel k l) x y| * |f y|
          ≤ 2 * Real.pi / ‖y‖ ^ 2 * |f y| := by gcongr
        _ = 2 * Real.pi * (|f y| / ‖y‖ ^ 2) := by ring
  calc 1 / Real.pi * |∫ y in quadrant, symmetrizedKernel (hessianKernel k l) x y * f y|
      ≤ 1 / Real.pi * (2 * Real.pi * ∫ y in quadrant, |f y| / ‖y‖ ^ 2) := by gcongr
    _ = 2 * ∫ y in quadrant, |f y| / ‖y‖ ^ 2 := by field_simp

/-- **Lipschitz bound of the far velocity gradient**: for a far density of radius `R` and
`4|x|, 4|z| ≤ R`, `|∂ₗ∂ₖΨ(x) - ∂ₗ∂ₖΨ(z)| ≤ 8 |x - z| ∫_{ℝ²₊₊} |f(y)|/|y|³ dy`. -/
theorem _root_.GreenFunction.IsQuadrantFarDensity.abs_hessian_sub_le
    (hf : IsQuadrantFarDensity f R) (k l : Fin 2) {x z : ℝ^2} (hx : 4 * ‖x‖ ≤ R)
    (hz : 4 * ‖z‖ ≤ R) :
    |(∂[l] (∂[k] (quadrantPotential f))) x - (∂[l] (∂[k] (quadrantPotential f))) z| ≤
      8 * ‖x - z‖ * ∫ y in quadrant, |f y| / ‖y‖ ^ 3 := by
  have hR := hf.pos
  have hx2 : ‖x‖ < R / 2 := by linarith [norm_nonneg x]
  have hz2 : ‖z‖ < R / 2 := by linarith [norm_nonneg z]
  rw [partialDeriv_partialDeriv_quadrantPotential_ball hf k l hx2,
    partialDeriv_partialDeriv_quadrantPotential_ball hf k l hz2, ← mul_sub,
    ← integral_sub (integrableOn_symmetrizedKernel_hessianKernel_of_far hf k l hx2)
      (integrableOn_symmetrizedKernel_hessianKernel_of_far hf k l hz2), abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
  have h := abs_setIntegral_le_mul hf (by norm_num : 2 ≤ 3) (C := 8 * Real.pi * ‖x - z‖)
    (F := fun y ↦ symmetrizedKernel (hessianKernel k l) x y * f y -
      symmetrizedKernel (hessianKernel k l) z y * f y)
    (fun y _ hfy ↦ by simp [hfy]) fun y hy hfy ↦ by
      rw [← sub_mul, abs_mul]
      have hk := abs_symmetrizedKernel_hessianKernel_sub_le k l (ne_zero_of_mem_quadrant hy)
        (four_mul_le hf hx hy hfy) (four_mul_le hf hz hy hfy)
      calc |symmetrizedKernel (hessianKernel k l) x y -
            symmetrizedKernel (hessianKernel k l) z y| * |f y|
          ≤ 8 * Real.pi * ‖x - z‖ / ‖y‖ ^ 3 * |f y| := by gcongr
        _ = 8 * Real.pi * ‖x - z‖ * (|f y| / ‖y‖ ^ 3) := by ring
  calc 1 / Real.pi * |∫ y in quadrant, (symmetrizedKernel (hessianKernel k l) x y * f y -
        symmetrizedKernel (hessianKernel k l) z y * f y)|
      ≤ 1 / Real.pi * (8 * Real.pi * ‖x - z‖ * ∫ y in quadrant, |f y| / ‖y‖ ^ 3) := by gcongr
    _ = 8 * ‖x - z‖ * ∫ y in quadrant, |f y| / ‖y‖ ^ 3 := by field_simp

/-- **Fourth-order expansion of the far velocity gradient**: for a far density of radius `R` and
`|x| < R/2`,
`|∂ₗ∂ₖΨ(x) - c mₖₗ - d ∂ₖ∂ₗG(x)| ≤ 184/(9π) |x|⁴ ∫_{ℝ²₊₊} |f(y)|/|y|⁶ dy` with
`c = mixedCoefficient f`, `d = quarticCoefficient f`, `mₖₗ = ∂ₖ∂ₗ(x₀x₁)` and
`G = quarticHarmonic`. -/
theorem _root_.GreenFunction.IsQuadrantFarDensity.abs_hessian_sub_expansion_le
    (hf : IsQuadrantFarDensity f R) (k l : Fin 2) {x : ℝ^2} (hx : ‖x‖ < R / 2) :
    |(∂[l] (∂[k] (quadrantPotential f))) x -
        (mixedCoefficient f * (if k = l then 0 else 1) +
          quarticCoefficient f * quarticHessian k l x)| ≤
      184 / (9 * Real.pi) * ‖x‖ ^ 4 * ∫ y in quadrant, |f y| / ‖y‖ ^ 6 := by
  rw [hessian_sub_expansion_eq hf k l hx, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
  have h := abs_setIntegral_le_mul hf (by norm_num : 2 ≤ 6) (C := 184 / 9 * ‖x‖ ^ 4)
    (F := fun y ↦ (symmetrizedKernel (hessianKernel k l) x y - taylor k l x y) * f y)
    (fun y _ hfy ↦ by simp [hfy]) fun y hy hfy ↦ by
      rw [abs_mul]
      have hk := abs_symmetrizedKernel_hessianKernel_remainder_le k l
        (ne_zero_of_mem_quadrant hy) (two_mul_le hf hx hy hfy)
      calc |symmetrizedKernel (hessianKernel k l) x y - taylor k l x y| * |f y|
          ≤ 184 / 9 * (‖x‖ ^ 4 / ‖y‖ ^ 6) * |f y| := by gcongr; exact hk
        _ = 184 / 9 * ‖x‖ ^ 4 * (|f y| / ‖y‖ ^ 6) := by ring
  calc 1 / Real.pi * |∫ y in quadrant,
        (symmetrizedKernel (hessianKernel k l) x y - taylor k l x y) * f y|
      ≤ 1 / Real.pi * (184 / 9 * ‖x‖ ^ 4 * ∫ y in quadrant, |f y| / ‖y‖ ^ 6) := by gcongr
    _ = 184 / (9 * Real.pi) * ‖x‖ ^ 4 * ∫ y in quadrant, |f y| / ‖y‖ ^ 6 := by ring

/-- **Lipschitz bound of the expansion remainder of the far velocity gradient**: for a far density
of radius `R` and `4|x|, 4|z| ≤ R`,
`|(∂ₗ∂ₖΨ - d ∂ₖ∂ₗG)(x) - (∂ₗ∂ₖΨ - d ∂ₖ∂ₗG)(z)| ≤ 2944/(9π) max(|x|, |z|)³ |x - z|
∫_{ℝ²₊₊} |f(y)|/|y|⁶ dy` with `d = quarticCoefficient f`. -/
theorem _root_.GreenFunction.IsQuadrantFarDensity.abs_hessian_expansion_sub_le
    (hf : IsQuadrantFarDensity f R) (k l : Fin 2) {x z : ℝ^2} (hx : 4 * ‖x‖ ≤ R)
    (hz : 4 * ‖z‖ ≤ R) :
    |((∂[l] (∂[k] (quadrantPotential f))) x - quarticCoefficient f * quarticHessian k l x) -
        ((∂[l] (∂[k] (quadrantPotential f))) z - quarticCoefficient f * quarticHessian k l z)| ≤
      2944 / (9 * Real.pi) * max ‖x‖ ‖z‖ ^ 3 * ‖x - z‖ *
        ∫ y in quadrant, |f y| / ‖y‖ ^ 6 := by
  have hR := hf.pos
  have hx2 : ‖x‖ < R / 2 := by linarith [norm_nonneg x]
  have hz2 : ‖z‖ < R / 2 := by linarith [norm_nonneg z]
  have ex := hessian_sub_expansion_eq hf k l hx2
  have ez := hessian_sub_expansion_eq hf k l hz2
  have hint (w : ℝ^2) (hw : ‖w‖ < R / 2) : IntegrableOn
      (fun y ↦ (symmetrizedKernel (hessianKernel k l) w y - taylor k l w y) * f y) quadrant :=
    ((integrableOn_symmetrizedKernel_hessianKernel_of_far hf k l hw).sub
      (integrableOn_taylor_mul hf k l w)).congr (Eventually.of_forall fun y ↦ by
        simp only [Pi.sub_apply]; ring)
  have hrw : ((∂[l] (∂[k] (quadrantPotential f))) x - quarticCoefficient f * quarticHessian k l x) -
      ((∂[l] (∂[k] (quadrantPotential f))) z - quarticCoefficient f * quarticHessian k l z) =
      1 / Real.pi * ∫ y in quadrant,
        ((symmetrizedKernel (hessianKernel k l) x y - taylor k l x y) * f y -
          (symmetrizedKernel (hessianKernel k l) z y - taylor k l z y) * f y) := by
    rw [integral_sub (hint x hx2) (hint z hz2), mul_sub, ← ex, ← ez]
    ring
  rw [hrw, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
  have h := abs_setIntegral_le_mul hf (by norm_num : 2 ≤ 6)
    (C := 2944 / 9 * max ‖x‖ ‖z‖ ^ 3 * ‖x - z‖)
    (F := fun y ↦ (symmetrizedKernel (hessianKernel k l) x y - taylor k l x y) * f y -
      (symmetrizedKernel (hessianKernel k l) z y - taylor k l z y) * f y)
    (fun y _ hfy ↦ by simp [hfy]) fun y hy hfy ↦ by
      rw [← sub_mul, abs_mul]
      have hk := abs_symmetrizedKernel_hessianKernel_remainder_sub_le k l
        (ne_zero_of_mem_quadrant hy) (four_mul_le hf hx hy hfy) (four_mul_le hf hz hy hfy)
      calc |(symmetrizedKernel (hessianKernel k l) x y - taylor k l x y) -
            (symmetrizedKernel (hessianKernel k l) z y - taylor k l z y)| * |f y|
          ≤ 2944 / 9 * (max ‖x‖ ‖z‖ ^ 3 * ‖x - z‖ / ‖y‖ ^ 6) * |f y| := by gcongr; exact hk
        _ = 2944 / 9 * max ‖x‖ ‖z‖ ^ 3 * ‖x - z‖ * (|f y| / ‖y‖ ^ 6) := by ring
  calc 1 / Real.pi * |∫ y in quadrant,
        ((symmetrizedKernel (hessianKernel k l) x y - taylor k l x y) * f y -
          (symmetrizedKernel (hessianKernel k l) z y - taylor k l z y) * f y)|
      ≤ 1 / Real.pi * (2944 / 9 * max ‖x‖ ‖z‖ ^ 3 * ‖x - z‖ *
          ∫ y in quadrant, |f y| / ‖y‖ ^ 6) := by gcongr
    _ = 2944 / (9 * Real.pi) * max ‖x‖ ‖z‖ ^ 3 * ‖x - z‖ *
          ∫ y in quadrant, |f y| / ‖y‖ ^ 6 := by ring

end IncompressibleFlow
