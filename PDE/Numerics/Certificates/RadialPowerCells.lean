/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.AxialWeight
public import CAS.Continuum.Interval.Rational.Arithmetic
public import CAS.Continuum.Interval.Rational.DyadicHull
public import Mathlib.Analysis.InnerProductSpace.Calculus
import PDE.FDeriv.Euclidean.NormSq

/-!
# Radial power sums: derivatives of their rates

A radial weight `ψ(x) = ∑ c_k |x|^{b_k}` (a list of `AxialTerm`s with axial exponent `0`) is a
function of `R = |x|²`: `ψ(x) = M₁(|x|²)` with the moments `M_f(R) = ∑ f_k c_k R^{b_k/2}`, whose
derivatives are `M_f' = M_{f b}/(2R)` (`hasDerivAt_radialMoment`). Hence the mean degree
`Γ = M_b/M₁` and the degree variance `V = M_{b²}/M₁ - Γ²` satisfy `Γ' = V/(2R)`
(`hasDerivAt_radialDegree`), and on `x ≠ 0`, with `R = |x|²`:

* `∂ₗψ = ψ Γ xₗ/R`, so the rate `Aₗ = ∂ₗψ/ψ = Γ xₗ/R` (`radialRate`);
* `∂ₘ Aₗ = δₗₘ Γ/R + (V - 2Γ) xₗ xₘ/R²`;
* `∂ₘ Γ = V xₘ/R`;
* for the strain rate `S = (x₀ ∂₀ψ - x₁ ∂₁ψ)/ψ = Γ (x₀² - x₁²)/R`,
  `∂ₘ S = (V - 2Γ)(x₀² - x₁²) xₘ/R² + 2 σₘ Γ xₘ/R` with `σ = (1, -1)`;
* for a ratio `Q = ψₐ/ψ_b`, `∂ₗ Q = Q (Γₐ - Γ_b) xₗ/R`;
* for `Aₗ/ψ_u`, `∂ₘ (Aₗ/ψ_u) = (δₗₘ Γ/R + (V - 2Γ - Γ Γ_u) xₗ xₘ/R²)/ψ_u`.

Each is a product `g(|x|²) m(x)` with `m ∈ {1, xₗ, x₀² - x₁²}`, differentiated by
`EuclideanLaplacian.partialDeriv_comp_norm_sq_mul`:
`∂ₖ (g(|x|²) m) = 2 xₖ g'(|x|²) m + g(|x|²) ∂ₖ m`.

## Main definitions

* `radialMoment`: the moment `M_f(R) = ∑ f_k c_k R^{b_k/2}` of a statistic `f` of the terms.
* `radialDegree`, `radialVariance`: the mean degree `Γ = M_b/M₁` and the degree variance `V`.
* `radialRate`, `radialStrainRate`: the rate `Γ xₗ/|x|²` and the strain rate
  `Γ (x₀² - x₁²)/|x|²`.
* `RadialCell`: enclosures on a cell of `Γ`, `V` and the normalized mass of a weight.
* `AxialWeight.radialCell`: these enclosures computed from the polar corners of the cell.
* `AxialWeight.IsRadialWeight`: the normal form of a radial weight used by `radialCell`.

## Main results

* `hasDerivAt_radialMoment`: `M_f'(R) = M_{f b}(R)/(2R)` for `R > 0`.
* `hasDerivAt_radialDegree`: `Γ'(R) = V(R)/(2R)` where `M₁(R) > 0`.
* `radialVariance_eq_centred`: `V = E[(b - c)²] - (Γ - c)²` for every rational centre `c`.
* `partialDeriv_radialRate`: `∂ₖ Aₗ = (V - 2Γ) xₖ xₗ/R² + (Γ/R) δₖₗ`.
* `AxialWeight.radialCell_mem`: the enclosures of `radialCell` are sound for a radial weight in
  normal form.
* `AxialWeight.rate_mem`: `Aₗ = ∂ₗψ/ψ` and `∂ₖ Aₗ` lie in their enclosures at every point of a
  cell with `R₋ > 0`.
* `AxialWeight.strainRate_mem`: the same for the strain rate `S` and `∂ₖ S`.
* `AxialWeight.ratio_mem`: the same for a ratio `ψₐ/ψ_b` of radial weights and its derivatives.
-/

@[expose] public section

namespace CAS.Numerics

open PDE
open PDE.Analysis

/-! ### Moments as functions of `R = |x|²` -/

/-- The terms are radial: every axial exponent is zero. -/
def AxialTerm.IsRadial (ts : List AxialTerm) : Prop := ∀ t ∈ ts, t.axial = 0

/-- `AxialTerm.IsRadial ts` is decidable. -/
instance (ts : List AxialTerm) : Decidable (AxialTerm.IsRadial ts) :=
  inferInstanceAs (Decidable (∀ t ∈ ts, _))

/-- The moment `M_f(R) = ∑ f_k c_k R^{b_k/2}` of the statistic `f` of the terms. -/
noncomputable def radialMoment (ts : List AxialTerm) (f : AxialTerm → ℚ) (R : ℝ) : ℝ :=
  (ts.map fun t ↦ (f t : ℝ) * t.coeff * R ^ ((t.radial : ℝ) / 2)).sum

/-- The moment of `t :: ts` is the term `f_t c_t R^{b_t/2}` plus the moment of `ts`. -/
theorem radialMoment_cons (t : AxialTerm) (ts : List AxialTerm) (f : AxialTerm → ℚ) (R : ℝ) :
    radialMoment (t :: ts) f R =
      (f t : ℝ) * t.coeff * R ^ ((t.radial : ℝ) / 2) + radialMoment ts f R := by
  simp [radialMoment]

/-- Moments of statistics that agree on the terms are equal. -/
theorem radialMoment_congr (ts : List AxialTerm) {f g : AxialTerm → ℚ} (h : ∀ t ∈ ts, f t = g t) :
    radialMoment ts f = radialMoment ts g := by
  funext R
  unfold radialMoment
  congr 1
  exact List.map_congr_left fun t ht ↦ by rw [h t ht]

/-- **The derivative of a moment**: `M_f'(R) = M_{f b}(R)/(2R)` for `R > 0`. -/
theorem hasDerivAt_radialMoment (ts : List AxialTerm) (f : AxialTerm → ℚ) {R : ℝ} (hR : 0 < R) :
    HasDerivAt (radialMoment ts f)
      (radialMoment ts (fun t ↦ f t * t.radial) R / (2 * R)) R := by
  induction ts with
  | nil =>
    have e : radialMoment [] f = fun _ ↦ 0 := funext fun R ↦ by simp [radialMoment]
    rw [e]
    simpa [radialMoment] using hasDerivAt_const R (0 : ℝ)
  | cons t ts ih =>
    have e : radialMoment (t :: ts) f =
        fun R ↦ (f t : ℝ) * t.coeff * R ^ ((t.radial : ℝ) / 2) + radialMoment ts f R :=
      funext fun R ↦ radialMoment_cons t ts f R
    rw [e]
    have hp : HasDerivAt (fun R : ℝ ↦ R ^ ((t.radial : ℝ) / 2))
        ((t.radial : ℝ) / 2 * R ^ ((t.radial : ℝ) / 2 - 1)) R :=
      Real.hasDerivAt_rpow_const (Or.inl hR.ne')
    convert (hp.const_mul ((f t : ℝ) * t.coeff)).add ih using 1
    rw [radialMoment_cons, Real.rpow_sub_one hR.ne']
    push_cast
    field_simp

/-- `M₁' = M_b/(2R)`. -/
theorem hasDerivAt_radialMoment_one (ts : List AxialTerm) {R : ℝ} (hR : 0 < R) :
    HasDerivAt (radialMoment ts 1) (radialMoment ts AxialTerm.radial R / (2 * R)) R := by
  have h := hasDerivAt_radialMoment ts 1 hR
  rwa [radialMoment_congr ts (f := fun t ↦ (1 : AxialTerm → ℚ) t * t.radial)
    (g := AxialTerm.radial) (fun t _ ↦ by simp)] at h

/-- The mean `M_f/M₁` of the statistic `f` at `R`. -/
noncomputable def radialMean (ts : List AxialTerm) (f : AxialTerm → ℚ) (R : ℝ) : ℝ :=
  radialMoment ts f R / radialMoment ts 1 R

/-- The mean degree `Γ = M_b/M₁` at `R`. -/
noncomputable def radialDegree (ts : List AxialTerm) (R : ℝ) : ℝ :=
  radialMean ts AxialTerm.radial R

/-- The degree variance `V = M_{b²}/M₁ - Γ²` at `R`. -/
noncomputable def radialVariance (ts : List AxialTerm) (R : ℝ) : ℝ :=
  radialMean ts (fun t ↦ t.radial * t.radial) R - radialDegree ts R ^ 2

/-- **The derivative of the mean degree**: `Γ'(R) = V(R)/(2R)` where `M₁(R) > 0`. -/
theorem hasDerivAt_radialDegree (ts : List AxialTerm) {R : ℝ} (hR : 0 < R)
    (hM : 0 < radialMoment ts 1 R) :
    HasDerivAt (radialDegree ts) (radialVariance ts R / (2 * R)) R := by
  have h := (hasDerivAt_radialMoment ts AxialTerm.radial hR).div
    (hasDerivAt_radialMoment_one ts hR) hM.ne'
  have e : radialDegree ts = fun R ↦ radialMoment ts AxialTerm.radial R / radialMoment ts 1 R :=
    rfl
  rw [e]
  convert h using 1
  simp only [radialVariance, radialDegree, radialMean]
  field_simp

/-- **The derivative of a ratio of weights**: `(M₁ᵃ/M₁ᵇ)' = (M₁ᵃ/M₁ᵇ)(Γₐ - Γ_b)/(2R)`. -/
theorem hasDerivAt_radialMoment_div (a b : List AxialTerm) {R : ℝ} (hR : 0 < R)
    (ha : 0 < radialMoment a 1 R) (hb : 0 < radialMoment b 1 R) :
    HasDerivAt (fun R ↦ radialMoment a 1 R / radialMoment b 1 R)
      (radialMoment a 1 R / radialMoment b 1 R * (radialDegree a R - radialDegree b R) /
        (2 * R)) R := by
  convert (hasDerivAt_radialMoment_one a hR).div (hasDerivAt_radialMoment_one b hR) hb.ne'
    using 1
  simp only [radialDegree, radialMean]
  field_simp

/-- **The derivative of the rate factor** `Γ/R`: `(Γ/R)' = (V - 2Γ)/(2R²)`. -/
theorem hasDerivAt_radialDegree_div (ts : List AxialTerm) {R : ℝ} (hR : 0 < R)
    (hM : 0 < radialMoment ts 1 R) :
    HasDerivAt (fun R ↦ radialDegree ts R / R)
      ((radialVariance ts R - 2 * radialDegree ts R) / (2 * R ^ 2)) R := by
  convert (hasDerivAt_radialDegree ts hR hM).div (hasDerivAt_id' R) hR.ne' using 1
  field_simp

/-- **The derivative of the remainder rate factor** `Γ/(R ψ_u)`:
`(Γ/(R M₁ᵘ))' = (V - 2Γ - Γ Γ_u)/(2R² M₁ᵘ)`. -/
theorem hasDerivAt_radialDegree_div_mul (ts u : List AxialTerm) {R : ℝ} (hR : 0 < R)
    (hM : 0 < radialMoment ts 1 R) (hu : 0 < radialMoment u 1 R) :
    HasDerivAt (fun R ↦ radialDegree ts R / (R * radialMoment u 1 R))
      ((radialVariance ts R - 2 * radialDegree ts R - radialDegree ts R * radialDegree u R) /
        (2 * R ^ 2 * radialMoment u 1 R)) R := by
  convert (hasDerivAt_radialDegree ts hR hM).div ((hasDerivAt_id' R).mul
    (hasDerivAt_radialMoment_one u hR)) (mul_pos hR hu).ne' using 1
  simp only [radialDegree, radialMean, Pi.mul_apply]
  field_simp
  ring

/-- A centred second moment: `∑ (b - γ)² c R^{b/2} = M_{b²} - 2γ M_b + γ² M₁` for real `γ`. -/
theorem radialMoment_centred (ts : List AxialTerm) (γ R : ℝ) :
    (ts.map fun t ↦ ((t.radial : ℝ) - γ) ^ 2 * t.coeff * R ^ ((t.radial : ℝ) / 2)).sum =
      radialMoment ts (fun t ↦ t.radial * t.radial) R - 2 * γ * radialMoment ts AxialTerm.radial R +
        γ ^ 2 * radialMoment ts 1 R := by
  induction ts with
  | nil => simp [radialMoment]
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, ih, radialMoment_cons, Rat.cast_mul, Pi.one_apply,
      Rat.cast_one]
    ring

/-- The moment `M₁(R)` is positive for `R > 0` when the coefficients are nonnegative and one of
them is positive. -/
theorem radialMoment_one_pos {ts : List AxialTerm} (hts : AxialTerm.NonnegCoeff ts)
    (hpos : ∃ t ∈ ts, 0 < t.coeff) {R : ℝ} (hR : 0 < R) : 0 < radialMoment ts 1 R := by
  obtain ⟨t, ht, hc⟩ := hpos
  unfold radialMoment
  have hnn : ∀ y ∈ ts.map fun t ↦ ((1 : AxialTerm → ℚ) t : ℝ) * t.coeff * R ^ ((t.radial : ℝ) / 2),
      0 ≤ y := fun y hy ↦ by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
    have : (0 : ℝ) ≤ s.coeff := by exact_mod_cast hts s hs
    simp only [Pi.one_apply, Rat.cast_one, one_mul]
    exact mul_nonneg this (Real.rpow_nonneg hR.le _)
  have hc' : (0 : ℝ) < t.coeff := by exact_mod_cast hc
  refine lt_of_lt_of_le ?_ (List.single_le_sum hnn _ (List.mem_map_of_mem ht))
  simp only [Pi.one_apply, Rat.cast_one, one_mul]
  exact mul_pos hc' (Real.rpow_pos_of_pos hR _)

/-- The degree variance is nonnegative. -/
theorem radialVariance_nonneg {ts : List AxialTerm} (hts : AxialTerm.NonnegCoeff ts) {R : ℝ}
    (hR : 0 < R) (hM : 0 < radialMoment ts 1 R) : 0 ≤ radialVariance ts R := by
  have h := radialMoment_centred ts (radialDegree ts R) R
  have hnn : 0 ≤ (ts.map fun t ↦ ((t.radial : ℝ) - radialDegree ts R) ^ 2 * t.coeff *
      R ^ ((t.radial : ℝ) / 2)).sum :=
    List.sum_nonneg fun y hy ↦ by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
      have : (0 : ℝ) ≤ s.coeff := by exact_mod_cast hts s hs
      exact mul_nonneg (mul_nonneg (sq_nonneg _) this) (Real.rpow_nonneg hR.le _)
  rw [h] at hnn
  have e : radialVariance ts R = (radialMoment ts (fun t ↦ t.radial * t.radial) R -
      2 * radialDegree ts R * radialMoment ts AxialTerm.radial R +
        radialDegree ts R ^ 2 * radialMoment ts 1 R) / radialMoment ts 1 R := by
    simp only [radialVariance, radialDegree, radialMean]
    field_simp
    ring
  rw [e]
  exact div_nonneg hnn hM.le

/-- **The centred variance**: `V = E[(b - c)²] - (Γ - c)²` for every rational centre `c`. -/
theorem radialVariance_eq_centred (ts : List AxialTerm) {R : ℝ} (hM : 0 < radialMoment ts 1 R)
    (c : ℚ) :
    radialVariance ts R =
      radialMean ts (fun t ↦ (t.radial - c) ^ 2) R - (radialDegree ts R - c) ^ 2 := by
  have h := radialMoment_centred ts (c : ℝ) R
  have e : radialMoment ts (fun t ↦ (t.radial - c) ^ 2) R =
      (ts.map fun t ↦ ((t.radial : ℝ) - c) ^ 2 * t.coeff * R ^ ((t.radial : ℝ) / 2)).sum := by
    simp [radialMoment]
  simp only [radialVariance, radialDegree, radialMean, e, h]
  field_simp
  ring

/-! ### Functions of `|x|²` in the plane -/

section Plane

variable {x : EuclideanSpace ℝ (Fin 2)}

/-- The chain rule through `|x|²`. -/
theorem hasFDerivAt_comp_norm_sq {g : ℝ → ℝ} {g' : ℝ} (hg : HasDerivAt g g' (‖x‖ ^ 2)) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) ↦ g (‖y‖ ^ 2)) (g' • (2 • innerSL ℝ x)) x :=
  hg.comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt

/-- `y ↦ g(|y|²) m(y)` is differentiable at `x` when `g` has a derivative at `|x|²` and `m` is
differentiable at `x`. -/
theorem differentiableAt_comp_norm_sq_mul {g : ℝ → ℝ} {g' : ℝ} (hg : HasDerivAt g g' (‖x‖ ^ 2))
    {m : EuclideanSpace ℝ (Fin 2) → ℝ} (hm : DifferentiableAt ℝ m x) :
    DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) ↦ g (‖y‖ ^ 2) * m y) x :=
  (hasFDerivAt_comp_norm_sq hg).differentiableAt.mul hm

/-- `∂ₖ (x₀² - x₁²) = 2 σₖ xₖ`, `σ = (1, -1)`. -/
theorem partialDeriv_sq_sub_sq (k : Fin 2) :
    (∂[k] (fun y : EuclideanSpace ℝ (Fin 2) ↦ y 0 ^ 2 - y 1 ^ 2)) x =
      2 * ![1, -1] k * x k := by
  have d : ∀ j : Fin 2, DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) ↦ y j) x :=
    fun j ↦ (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).differentiableAt
  have d2 : ∀ j : Fin 2, DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) ↦ y j ^ 2) x :=
    fun j ↦ (d j).fun_pow 2
  rw [partialDeriv_sub (f := fun y : EuclideanSpace ℝ (Fin 2) ↦ y 0 ^ 2)
    (g := fun y : EuclideanSpace ℝ (Fin 2) ↦ y 1 ^ 2) (d2 0) (d2 1), partialDeriv_sq k (d 0),
    partialDeriv_sq k (d 1), partialDeriv_coord, partialDeriv_coord]
  fin_cases k <;> simp

/-- `y ↦ y₀² - y₁²` is differentiable. -/
theorem differentiableAt_sq_sub_sq :
    DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) ↦ y 0 ^ 2 - y 1 ^ 2) x :=
  ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).differentiableAt.fun_pow
    2).fun_sub ((EuclideanSpace.proj (1 : Fin 2) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).differentiableAt.fun_pow 2)

/-- The coordinate `y ↦ yₗ` is differentiable. -/
theorem differentiableAt_coord (l : Fin 2) :
    DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) ↦ y l) x :=
  (EuclideanSpace.proj l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).differentiableAt

end Plane

/-! ### The rates as functions in the plane -/

section Rates

variable (ts u a b : List AxialTerm) {x : EuclideanSpace ℝ (Fin 2)}

/-- The constant weight `1` as a list of terms. -/
def oneTerms : List AxialTerm := [⟨1, 0, 0⟩]

/-- The constant weight has `M₁ = 1`. -/
@[simp] theorem radialMoment_oneTerms (R : ℝ) : radialMoment oneTerms 1 R = 1 := by
  simp [radialMoment, oneTerms]

/-- The constant weight has mean degree `Γ = 0`. -/
@[simp] theorem radialDegree_oneTerms (R : ℝ) : radialDegree oneTerms R = 0 := by
  simp [radialDegree, radialMean, radialMoment, oneTerms]

/-- The rate `Aₗ(x) = Γ(|x|²) xₗ/|x|²`. -/
noncomputable def radialRate (l : Fin 2) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  radialDegree ts (‖x‖ ^ 2) / ‖x‖ ^ 2 * x l

/-- The strain rate `S(x) = Γ(|x|²) (x₀² - x₁²)/|x|²`. -/
noncomputable def radialStrainRate (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  radialDegree ts (‖x‖ ^ 2) / ‖x‖ ^ 2 * (x 0 ^ 2 - x 1 ^ 2)

/-- The rate divided by a second weight, `Aₗ(x)/ψ_u(x) = Γ(|x|²) xₗ/(|x|² M₁ᵘ(|x|²))`. -/
noncomputable def radialRemainderRate (l : Fin 2) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  radialDegree ts (‖x‖ ^ 2) / (‖x‖ ^ 2 * radialMoment u 1 (‖x‖ ^ 2)) * x l

/-- The ratio `ψₐ/ψ_b` of two radial weights. -/
noncomputable def radialRatio (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  radialMoment a 1 (‖x‖ ^ 2) / radialMoment b 1 (‖x‖ ^ 2)

variable {ts u a b}

/-- `∂ₖ ψ = 2 (M_b/(2R)) xₖ` for the weight `ψ = M₁(|x|²)`. -/
theorem partialDeriv_radialMoment_one (hR : 0 < ‖x‖ ^ 2) (k : Fin 2) :
    DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) ↦ radialMoment ts 1 (‖y‖ ^ 2)) x ∧
      (∂[k] (fun y : EuclideanSpace ℝ (Fin 2) ↦ radialMoment ts 1 (‖y‖ ^ 2))) x =
        2 * (radialMoment ts AxialTerm.radial (‖x‖ ^ 2) / (2 * ‖x‖ ^ 2)) * x k := by
  have hg := hasDerivAt_radialMoment_one ts hR
  exact ⟨(hasFDerivAt_comp_norm_sq hg).differentiableAt,
    by rw [EuclideanLaplacian.partialDeriv_comp_norm_sq k hg.differentiableAt, hg.deriv]; ring⟩

/-- `∂ₖ Γ(|x|²) = V xₖ/R`. -/
theorem partialDeriv_radialDegree (hR : 0 < ‖x‖ ^ 2) (hM : 0 < radialMoment ts 1 (‖x‖ ^ 2))
    (k : Fin 2) :
    DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) ↦ radialDegree ts (‖y‖ ^ 2)) x ∧
      (∂[k] (fun y : EuclideanSpace ℝ (Fin 2) ↦ radialDegree ts (‖y‖ ^ 2))) x =
        2 * (radialVariance ts (‖x‖ ^ 2) / (2 * ‖x‖ ^ 2)) * x k := by
  have hg := hasDerivAt_radialDegree ts hR hM
  exact ⟨(hasFDerivAt_comp_norm_sq hg).differentiableAt,
    by rw [EuclideanLaplacian.partialDeriv_comp_norm_sq k hg.differentiableAt, hg.deriv]; ring⟩

/-- `∂ₖ Aₗ = 2 (V - 2Γ)/(2R²) xₖ xₗ + (Γ/R) δₖₗ`. -/
theorem partialDeriv_radialRate (hR : 0 < ‖x‖ ^ 2) (hM : 0 < radialMoment ts 1 (‖x‖ ^ 2))
    (k l : Fin 2) :
    DifferentiableAt ℝ (radialRate ts l) x ∧
      (∂[k] (radialRate ts l)) x =
        2 * ((radialVariance ts (‖x‖ ^ 2) - 2 * radialDegree ts (‖x‖ ^ 2)) /
            (2 * (‖x‖ ^ 2) ^ 2)) * x k * x l +
          radialDegree ts (‖x‖ ^ 2) / ‖x‖ ^ 2 * (if k = l then 1 else 0) := by
  have hg := hasDerivAt_radialDegree_div ts hR hM
  have e : radialRate ts l = fun y ↦ (fun R ↦ radialDegree ts R / R) (‖y‖ ^ 2) * y l := rfl
  rw [e]
  exact ⟨differentiableAt_comp_norm_sq_mul hg (differentiableAt_coord l),
    by
      rw [EuclideanLaplacian.partialDeriv_comp_norm_sq_mul k hg.differentiableAt
        (differentiableAt_coord l), hg.deriv, partialDeriv_coord]
      ring⟩

/-- `∂ₖ S = 2 (V - 2Γ)/(2R²) xₖ (x₀² - x₁²) + (Γ/R) 2 σₖ xₖ`. -/
theorem partialDeriv_radialStrainRate (hR : 0 < ‖x‖ ^ 2)
    (hM : 0 < radialMoment ts 1 (‖x‖ ^ 2)) (k : Fin 2) :
    DifferentiableAt ℝ (radialStrainRate ts) x ∧
      (∂[k] (radialStrainRate ts)) x =
        2 * ((radialVariance ts (‖x‖ ^ 2) - 2 * radialDegree ts (‖x‖ ^ 2)) /
            (2 * (‖x‖ ^ 2) ^ 2)) * x k * (x 0 ^ 2 - x 1 ^ 2) +
          radialDegree ts (‖x‖ ^ 2) / ‖x‖ ^ 2 * (2 * ![1, -1] k * x k) := by
  have hg := hasDerivAt_radialDegree_div ts hR hM
  have e : radialStrainRate ts =
      fun y ↦ (fun R ↦ radialDegree ts R / R) (‖y‖ ^ 2) * (y 0 ^ 2 - y 1 ^ 2) := rfl
  rw [e]
  exact ⟨differentiableAt_comp_norm_sq_mul hg differentiableAt_sq_sub_sq,
    by
      rw [EuclideanLaplacian.partialDeriv_comp_norm_sq_mul k hg.differentiableAt
        differentiableAt_sq_sub_sq, hg.deriv, partialDeriv_sq_sub_sq]
      ring⟩

/-- `∂ₖ (Aₗ/ψ_u) = 2 (V - 2Γ - Γ Γ_u)/(2R² M₁ᵘ) xₖ xₗ + Γ/(R M₁ᵘ) δₖₗ`. -/
theorem partialDeriv_radialRemainderRate (hR : 0 < ‖x‖ ^ 2)
    (hM : 0 < radialMoment ts 1 (‖x‖ ^ 2)) (hu : 0 < radialMoment u 1 (‖x‖ ^ 2)) (k l : Fin 2) :
    DifferentiableAt ℝ (radialRemainderRate ts u l) x ∧
      (∂[k] (radialRemainderRate ts u l)) x =
        2 * ((radialVariance ts (‖x‖ ^ 2) - 2 * radialDegree ts (‖x‖ ^ 2) -
            radialDegree ts (‖x‖ ^ 2) * radialDegree u (‖x‖ ^ 2)) /
            (2 * (‖x‖ ^ 2) ^ 2 * radialMoment u 1 (‖x‖ ^ 2))) * x k * x l +
          radialDegree ts (‖x‖ ^ 2) / (‖x‖ ^ 2 * radialMoment u 1 (‖x‖ ^ 2)) *
            (if k = l then 1 else 0) := by
  have hg := hasDerivAt_radialDegree_div_mul ts u hR hM hu
  have e : radialRemainderRate ts u l =
      fun y ↦ (fun R ↦ radialDegree ts R / (R * radialMoment u 1 R)) (‖y‖ ^ 2) * y l := rfl
  rw [e]
  exact ⟨differentiableAt_comp_norm_sq_mul hg (differentiableAt_coord l),
    by
      rw [EuclideanLaplacian.partialDeriv_comp_norm_sq_mul k hg.differentiableAt
        (differentiableAt_coord l), hg.deriv, partialDeriv_coord]
      ring⟩

/-- `∂ₖ (ψₐ/ψ_b) = 2 (ψₐ/ψ_b)(Γₐ - Γ_b)/(2R) xₖ`. -/
theorem partialDeriv_radialRatio (hR : 0 < ‖x‖ ^ 2) (ha : 0 < radialMoment a 1 (‖x‖ ^ 2))
    (hb : 0 < radialMoment b 1 (‖x‖ ^ 2)) (k : Fin 2) :
    DifferentiableAt ℝ (radialRatio a b) x ∧
      (∂[k] (radialRatio a b)) x =
        2 * (radialRatio a b x * (radialDegree a (‖x‖ ^ 2) - radialDegree b (‖x‖ ^ 2)) /
          (2 * ‖x‖ ^ 2)) * x k := by
  have hg := hasDerivAt_radialMoment_div a b hR ha hb
  have e : radialRatio a b =
      fun y ↦ (fun R ↦ radialMoment a 1 R / radialMoment b 1 R) (‖y‖ ^ 2) := rfl
  rw [e]
  exact ⟨(hasFDerivAt_comp_norm_sq hg).differentiableAt,
    by rw [EuclideanLaplacian.partialDeriv_comp_norm_sq k hg.differentiableAt, hg.deriv]; ring⟩

end Rates

/-! ### Bridges from the cell API of axial weights -/

section Bridges

variable {ts : List AxialTerm} {x : EuclideanSpace ℝ (Fin 2)}

/-- A term with axial exponent zero is `c (|x|²)^{b/2}`. -/
theorem AxialTerm.value_eq_of_axial_eq_zero {t : AxialTerm} (ht : t.axial = 0)
    (x : EuclideanSpace ℝ (Fin 2)) :
    t.value x = t.coeff * (‖x‖ ^ 2) ^ ((t.radial : ℝ) / 2) := by
  simp [AxialTerm.value, axialPower, ht, norm_rpow_eq_sq]

/-- A radial weight is the moment `M₁` at `|x|²`, at every point. -/
theorem axialTermsValue_eq_radialMoment (hts : AxialTerm.IsRadial ts)
    (x : EuclideanSpace ℝ (Fin 2)) : axialTermsValue ts x = radialMoment ts 1 (‖x‖ ^ 2) := by
  unfold axialTermsValue radialMoment
  congr 1
  refine List.map_congr_left fun t ht ↦ ?_
  rw [AxialTerm.value_eq_of_axial_eq_zero (hts t ht)]
  simp

/-- For radial terms the mean `axialTermsMean ts f x` is the radial mean `radialMean ts f` at
`|x|²`. -/
theorem axialTermsMean_eq_radialMean (hts : AxialTerm.IsRadial ts) (f : AxialTerm → ℚ)
    (x : EuclideanSpace ℝ (Fin 2)) : axialTermsMean ts f x = radialMean ts f (‖x‖ ^ 2) := by
  unfold axialTermsMean radialMean
  rw [axialTermsValue_eq_radialMoment hts]
  congr 1
  unfold radialMoment
  congr 1
  refine List.map_congr_left fun t ht ↦ ?_
  rw [AxialTerm.value_eq_of_axial_eq_zero (hts t ht)]
  ring

/-- For radial terms the moments of the degree and of the radial exponent agree. -/
theorem radialMoment_degree (hts : AxialTerm.IsRadial ts) :
    radialMoment ts AxialTerm.degree = radialMoment ts AxialTerm.radial :=
  radialMoment_congr ts fun t ht ↦ by simp [AxialTerm.degree, hts t ht]

/-- For radial terms the moment is the normalized mass times `R^{G/2}`. -/
theorem radialMoment_eq_rpow_mul (hts : AxialTerm.IsRadial ts) (G : ℚ) {R : ℝ} (hR : 0 < R)
    (W : ℝ) :
    radialMoment ts 1 R = R ^ ((G : ℝ) / 2) * (ts.map fun t ↦ t.polarMass 0 G W R).sum := by
  unfold radialMoment
  rw [← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun t ht ↦ ?_
  simp only [AxialTerm.polarMass, AxialTerm.degree, hts t ht, sub_self, zero_div, Rat.cast_zero,
    Real.rpow_zero, mul_one, zero_add, Pi.one_apply, Rat.cast_one, one_mul]
  rw [mul_left_comm, ← Real.rpow_add hR]
  congr 2
  push_cast
  ring

end Bridges

/-! ### Enclosures on cells -/

section Cells

open CAS.Continuum

/-- The interval between two rationals, in either order. -/
def intervalOf (p q : ℚ) : RationalInterval where
  lo := min p q
  hi := max p q
  hle := min_le_max

/-- A real number between `p` and `q` lies in `intervalOf p q`. -/
theorem intervalOf_mem {p q : ℚ} {v : ℝ} (h₁ : (p : ℝ) ≤ v) (h₂ : v ≤ q) :
    (intervalOf p q).MemReal v := by
  simp only [RationalInterval.MemReal, intervalOf, Rat.cast_min, Rat.cast_max]
  exact ⟨(min_le_left _ _).trans h₁, h₂.trans (le_max_right _ _)⟩

variable {C : PlaneCell} {bits : ℕ} {x : EuclideanSpace ℝ (Fin 2)}

/-- A point of the rectangle spanned by two points of a cell lies in the cell. -/
theorem PlaneCell.mem_of_mem_uIcc {z y : EuclideanSpace ℝ (Fin 2)} (hx : C.Mem x) (hz : C.Mem z)
    (h₀ : y 0 ∈ Set.uIcc (x 0) (z 0)) (h₁ : y 1 ∈ Set.uIcc (x 1) (z 1)) : C.Mem y := by
  obtain ⟨hx0, hx1, hxa, hxb, hxc, hxd⟩ := hx
  obtain ⟨hz0, hz1, hza, hzb, hzc, hzd⟩ := hz
  rw [Set.mem_uIcc] at h₀ h₁
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rcases h₀ with h₀ | h₀ <;> rcases h₁ with h₁ | h₁ <;>
    linarith [h₀.1, h₀.2, h₁.1, h₁.2]

/-- The coordinate intervals `[left, right]` and `[bottom, top]` of a cell. -/
def PlaneCell.coord (C : PlaneCell) : Fin 2 → RationalInterval :=
  ![intervalOf C.left C.right, intervalOf C.bottom C.top]

/-- The coordinate `xₗ` of a point of a cell lies in `C.coord l`. -/
theorem PlaneCell.coord_mem (hx : C.Mem x) (l : Fin 2) : (C.coord l).MemReal (x l) := by
  fin_cases l
  · exact intervalOf_mem hx.2.2.1 hx.2.2.2.1
  · exact intervalOf_mem hx.2.2.2.2.1 hx.2.2.2.2.2

/-- The interval of `x₀² - x₁²` on a cell. -/
def PlaneCell.squareDifference (C : PlaneCell) : RationalInterval :=
  intervalOf (C.left ^ 2 - C.top ^ 2) (C.right ^ 2 - C.bottom ^ 2)

/-- At a point of a valid cell `x₀² - x₁²` lies in `C.squareDifference`. -/
theorem PlaneCell.squareDifference_mem (hC : C.Valid) (hx : C.Mem x) :
    C.squareDifference.MemReal (x 0 ^ 2 - x 1 ^ 2) := by
  obtain ⟨h0, h1, ha, hb, hc, hd⟩ := hx
  have ha0 : (0 : ℝ) ≤ C.left := by exact_mod_cast hC.1
  have hc0 : (0 : ℝ) ≤ C.bottom := by exact_mod_cast hC.2
  refine intervalOf_mem ?_ ?_ <;> push_cast <;> nlinarith

/-- The interval of `R⁻¹ = |x|⁻²` on a cell. -/
def PlaneCell.inverseRadius (C : PlaneCell) (bits : ℕ) : RationalInterval :=
  intervalOf (1 / C.radiusUpper bits) (1 / C.radiusLower bits)

/-- At a point of a valid cell with `R₋ > 0`, `|x|⁻²` lies in `C.inverseRadius bits`. -/
theorem PlaneCell.inverseRadius_mem (hC : C.Valid) (hx : C.Mem x)
    (hR : 0 < C.radiusLower bits) : (C.inverseRadius bits).MemReal (‖x‖ ^ 2)⁻¹ := by
  have h := C.radius_mem hC hx bits
  have hR' : (0 : ℝ) < C.radiusLower bits := by exact_mod_cast hR
  have hn : 0 < ‖x‖ ^ 2 := hR'.trans_le h.2.1
  refine intervalOf_mem ?_ ?_ <;> push_cast <;> rw [one_div]
  · exact inv_anti₀ hn h.2.2
  · exact inv_anti₀ hR' h.2.1

/-- The interval of `R^e` on a cell, for `R₋ > 0`. -/
def PlaneCell.radiusPow (C : PlaneCell) (e : ℚ) (bits : ℕ) : RationalInterval :=
  intervalOf (monoPowLower (C.radiusLower bits) (C.radiusUpper bits) e bits)
    (rpowBounds (if 0 ≤ e then C.radiusUpper bits else C.radiusLower bits) e bits).2

/-- At a point of a valid cell with `R₋ > 0`, `(|x|²)^e` lies in `C.radiusPow e bits`. -/
theorem PlaneCell.radiusPow_mem (hC : C.Valid) (hx : C.Mem x) (hR : 0 < C.radiusLower bits)
    (e : ℚ) : (C.radiusPow e bits).MemReal ((‖x‖ ^ 2) ^ (e : ℝ)) := by
  have h := C.radius_mem hC hx bits
  have hR' : (0 : ℝ) < C.radiusLower bits := by exact_mod_cast hR
  have hn : 0 < ‖x‖ ^ 2 := hR'.trans_le h.2.1
  refine intervalOf_mem (monoPowLower_le h.1 hn h.2.1 h.2.2 e bits) ?_
  split_ifs with he
  · have hU : (0 : ℚ) ≤ C.radiusUpper bits := by
      have : (0 : ℝ) ≤ C.radiusUpper bits := hn.le.trans h.2.2
      exact_mod_cast this
    exact (Real.rpow_le_rpow hn.le h.2.2 (by exact_mod_cast he)).trans
      (rpowBounds_mem hU e bits).2
  · exact (Real.rpow_le_rpow_of_nonpos hR' h.2.1 (by exact_mod_cast (not_le.1 he).le)).trans
      (rpowBounds_mem hR.le e bits).2

/-- `v² ≤ max(a², b²)` for `v ∈ [a, b]`. -/
theorem sq_le_max_sq {a b v : ℝ} (ha : a ≤ v) (hb : v ≤ b) : v ^ 2 ≤ max (a ^ 2) (b ^ 2) := by
  rcases le_total 0 v with hv | hv
  · exact (pow_le_pow_left₀ hv hb 2).trans (le_max_right _ _)
  · refine le_trans ?_ (le_max_left _ _)
    nlinarith

/-- The enclosures on a cell of the mean degree `Γ`, the degree variance `V` and the normalized
mass `N = R^{-G/2} M₁` of a weight at `R = |x|²`, and the normalizing degree `G`. -/
structure RadialCell where
  /-- Bounds of `Γ`. -/
  degree : RationalInterval
  /-- Bounds of `V`. -/
  variance : RationalInterval
  /-- Bounds of `R^{-G/2} M₁`. -/
  mass : RationalInterval
  /-- The normalizing degree `G`. -/
  degreeMin : ℚ

namespace AxialWeight

variable (w : AxialWeight)

variable (C bits) in
/-- The radial enclosures of a weight on a cell: `Γ` from the polar corners (`cellRates`), `V`
from `V = E[(b - c)²] - (Γ - c)²` with `c` the rounded centre of the bounds of `Γ` and the mean
of `(b - c)²` from `cellMean`, and `N` from `splitMasses`. -/
def radialCell : RadialCell :=
  let g := (w.cellRates C bits).degree
  let c := RationalInterval.roundDownRel bits ((g.1 + g.2) / 2)
  let e := w.cellMean C bits fun t ↦ (t.degree - c) ^ 2
  let s := max ((g.1 - c) ^ 2) ((g.2 - c) ^ 2)
  let ms := w.splitMasses C bits
  { degree := RationalInterval.dyadicHull bits (intervalOf g.1 g.2)
    variance := RationalInterval.dyadicHull bits (intervalOf (max 0 (e.1 - s)) e.2)
    mass := intervalOf (totalLower ms) (totalUpper ms)
    degreeMin := w.degreeMin }

/-- **The radial enclosures are sound** for a radial weight with `axialMin = 0` in which a term
with a positive coefficient attains the smallest degree. -/
theorem radialCell_mem (hw : AxialTerm.IsRadial w.terms) (hA : w.axialMin = 0)
    (hmin : ∃ t ∈ w.terms, 0 < t.coeff ∧ t.axial = w.axialMin ∧ t.degree = w.degreeMin)
    (hC : C.Valid) (hx : C.Mem x) :
    (w.radialCell C bits).degree.MemReal (radialDegree w.terms (‖x‖ ^ 2)) ∧
      (w.radialCell C bits).variance.MemReal (radialVariance w.terms (‖x‖ ^ 2)) ∧
      (w.radialCell C bits).mass.MemReal
        ((‖x‖ ^ 2) ^ (-(w.degreeMin : ℝ) / 2) * radialMoment w.terms 1 (‖x‖ ^ 2)) ∧
      0 < (w.radialCell C bits).mass.lo ∧ (w.radialCell C bits).degreeMin = w.degreeMin := by
  have hn : 0 < ‖x‖ ^ 2 := norm_sq_pos_of_pos hx.1
  have hpos : ∃ t ∈ w.terms, 0 < t.coeff := by
    obtain ⟨t, ht, hc, -⟩ := hmin; exact ⟨t, ht, hc⟩
  have hM := radialMoment_one_pos w.nonneg hpos hn
  -- the mean degree
  have hΓ := degree_mem hC (cellRates_valid_of_min hmin) hx (bits := bits)
  rw [axialTermsMean_eq_radialMean hw, radialMean, radialMoment_degree hw, ← radialMean,
    ← radialDegree] at hΓ
  set g := (w.cellRates C bits).degree
  -- the centred second moment
  set c := RationalInterval.roundDownRel bits ((g.1 + g.2) / 2)
  have hv := splitMasses_valid_of_min hmin (w := w) (C := C) (bits := bits)
  have he := w.cellMean_mem hC hx hv fun t ↦ (t.degree - c) ^ 2
  rw [axialTermsMean_eq_radialMean hw,
    show radialMean w.terms (fun t ↦ (t.degree - c) ^ 2) =
      radialMean w.terms (fun t ↦ (t.radial - c) ^ 2) by
        unfold radialMean
        rw [radialMoment_congr w.terms (f := fun t ↦ (t.degree - c) ^ 2)
          (g := fun t ↦ (t.radial - c) ^ 2) fun t ht ↦ by simp [AxialTerm.degree, hw t ht]],
    ← sub_add_cancel (radialMean w.terms (fun t ↦ (t.radial - c) ^ 2) (‖x‖ ^ 2))
      ((radialDegree w.terms (‖x‖ ^ 2) - c) ^ 2), ← radialVariance_eq_centred _ hM] at he
  have hs : (radialDegree w.terms (‖x‖ ^ 2) - c) ^ 2 ≤
      ((max ((g.1 - c) ^ 2) ((g.2 - c) ^ 2) : ℚ) : ℝ) := by
    push_cast
    exact sq_le_max_sq (by linarith [hΓ.1]) (by linarith [hΓ.2])
  have hV0 := radialVariance_nonneg w.nonneg hn hM
  -- the normalized mass
  have hN := w.splitMasses_total_mem hC hx (bits := bits)
  rw [hA] at hN
  have hmass : (‖x‖ ^ 2) ^ (-(w.degreeMin : ℝ) / 2) * radialMoment w.terms 1 (‖x‖ ^ 2) =
      (w.terms.map fun t ↦ t.polarMass 0 w.degreeMin (x 0 ^ 2 / ‖x‖ ^ 2) (‖x‖ ^ 2)).sum := by
    rw [radialMoment_eq_rpow_mul hw w.degreeMin hn (x 0 ^ 2 / ‖x‖ ^ 2), ← mul_assoc,
      ← Real.rpow_add hn, show -(w.degreeMin : ℝ) / 2 + (w.degreeMin : ℝ) / 2 = 0 by ring,
      Real.rpow_zero, one_mul]
  have hlo : 0 < totalLower (w.splitMasses C bits) := hv
  refine ⟨RationalInterval.dyadicHull_sound bits (intervalOf_mem hΓ.1 hΓ.2),
    RationalInterval.dyadicHull_sound bits (intervalOf_mem ?_ ?_),
    intervalOf_mem (hmass ▸ hN.1) (hmass ▸ hN.2), ?_, rfl⟩
  · push_cast at hs ⊢
    exact max_le hV0 (by linarith [he.1, hs])
  · linarith [he.2, sq_nonneg (radialDegree w.terms (‖x‖ ^ 2) - c)]
  · have hlo' : (0 : ℝ) < totalLower (w.splitMasses C bits) := by exact_mod_cast hlo
    have hup : (0 : ℝ) < totalUpper (w.splitMasses C bits) := hlo'.trans_le (hN.1.trans hN.2)
    exact lt_min hlo (by exact_mod_cast hup)

/-- A radial weight in the normal form of `radialCell`: radial terms, `axialMin = 0`, and a term
with a positive coefficient attaining the smallest degree. -/
structure IsRadialWeight : Prop where
  /-- The terms are radial. -/
  radial : AxialTerm.IsRadial w.terms
  /-- The normalizing axial exponent is zero. -/
  axialMin_eq : w.axialMin = 0
  /-- A term with a positive coefficient attains both minima. -/
  min : ∃ t ∈ w.terms, 0 < t.coeff ∧ t.axial = w.axialMin ∧ t.degree = w.degreeMin

/-- A radial weight has `M₁(R) > 0` for `R > 0`. -/
theorem IsRadialWeight.moment_pos {w : AxialWeight} (hw : w.IsRadialWeight) {R : ℝ} (hR : 0 < R) :
    0 < radialMoment w.terms 1 R := by
  obtain ⟨t, ht, hc, -⟩ := hw.min
  exact radialMoment_one_pos w.nonneg ⟨t, ht, hc⟩ hR

/-- The weight `1`. -/
def one : AxialWeight where
  terms := oneTerms
  axialMin := 0
  degreeMin := 0
  nonneg := by decide +kernel
  axialMin_le := by decide +kernel
  degreeMin_le := by decide +kernel
  degree_comonotone := by decide +kernel
  axial_comonotone := by decide +kernel

/-- The weight `1` is a radial weight. -/
theorem one_isRadialWeight : one.IsRadialWeight :=
  ⟨by decide +kernel, rfl, by decide +kernel⟩

end AxialWeight

/-! ### Enclosures of the rates and their derivatives -/

open RationalInterval in
/-- The enclosure `Γ R⁻¹ X`: of the rate `Aₗ = Γ R⁻¹ xₗ` for `X ∋ xₗ`, and of the strain rate
`S = Γ R⁻¹ (x₀² - x₁²)` for `X ∋ x₀² - x₁²`. -/
def rateRange (W : RadialCell) (rinv X : RationalInterval) : RationalInterval :=
  (W.degree.mul rinv).mul X

open RationalInterval in
/-- The enclosure of `∂ₖ Aₗ = (V - 2Γ) R⁻² xₖ xₗ + Γ R⁻¹ δₖₗ`. -/
def rateDerivRange (W : RadialCell) (rinv Xk Xl : RationalInterval) (δ : ℚ) : RationalInterval :=
  (((W.variance.sub ((const 2).mul W.degree)).mul (rinv.mul rinv)).mul (Xk.mul Xl)).add
    ((W.degree.mul rinv).mul (const δ))

/-- The enclosure of `∂ₖ Γ = V R⁻¹ xₖ`. -/
def degreeDerivRange (W : RadialCell) (rinv Xk : RationalInterval) : RationalInterval :=
  (W.variance.mul rinv).mul Xk

open RationalInterval in
/-- The enclosure of `∂ₖ S = (V - 2Γ) R⁻² xₖ (x₀² - x₁²) + Γ R⁻¹ (2 σₖ xₖ)`. -/
def strainDerivRange (W : RadialCell) (rinv Xk M : RationalInterval) (σ : ℚ) :
    RationalInterval :=
  (((W.variance.sub ((const 2).mul W.degree)).mul (rinv.mul rinv)).mul (Xk.mul M)).add
    ((W.degree.mul rinv).mul ((const (2 * σ)).mul Xk))

/-- The enclosure of `Aₗ/ψ_u = Γ R⁻¹ ψ_u⁻¹ xₗ` from an enclosure `Uinv` of `ψ_u⁻¹`. -/
def remainderRateRange (W : RadialCell) (rinv Uinv X : RationalInterval) : RationalInterval :=
  ((W.degree.mul rinv).mul Uinv).mul X

open RationalInterval in
/-- The enclosure of `∂ₖ (Aₗ/ψ_u) = (V - 2Γ - Γ Γ_u) R⁻² ψ_u⁻¹ xₖ xₗ + Γ R⁻¹ ψ_u⁻¹ δₖₗ`. -/
def remainderRateDerivRange (W U : RadialCell) (rinv Uinv Xk Xl : RationalInterval) (δ : ℚ) :
    RationalInterval :=
  (((((W.variance.sub ((const 2).mul W.degree)).sub (W.degree.mul U.degree)).mul
      (rinv.mul rinv)).mul Uinv).mul (Xk.mul Xl)).add (((W.degree.mul rinv).mul Uinv).mul (const δ))

/-- The enclosure of `ψₐ/ψ_b = R^{(Gₐ - G_b)/2} Nₐ/N_b` from an enclosure of the power. -/
def ratioRange (A B : RadialCell) (P : RationalInterval) : RationalInterval :=
  P.mul (A.mass.divPositiveOrZero B.mass)

/-- The enclosure of `∂ₖ (ψₐ/ψ_b) = Q (Γₐ - Γ_b) R⁻¹ xₖ` from an enclosure `Q` of the ratio. -/
def ratioDerivRange (Q : RationalInterval) (A B : RadialCell) (rinv Xk : RationalInterval) :
    RationalInterval :=
  ((Q.mul (A.degree.sub B.degree)).mul rinv).mul Xk

namespace AxialWeight

variable {w u a b : AxialWeight}

/-- The enclosure of `ψₐ/ψ_b` on a cell. -/
def ratioCell (a b : AxialWeight) (C : PlaneCell) (bits : ℕ) : RationalInterval :=
  ratioRange (a.radialCell C bits) (b.radialCell C bits)
    (C.radiusPow ((a.degreeMin - b.degreeMin) / 2) bits)

open RationalInterval in
/-- **The ratio of two radial weights on a cell**: `ψₐ/ψ_b` and `∂ₖ (ψₐ/ψ_b)` lie in their
enclosures, at every point of the cell, when `R₋ > 0`. -/
theorem ratio_mem (ha : a.IsRadialWeight) (hb : b.IsRadialWeight) (hC : C.Valid) (hx : C.Mem x)
    (hR : 0 < C.radiusLower bits) (k : Fin 2) :
    DifferentiableAt ℝ (radialRatio a.terms b.terms) x ∧
      (ratioCell a b C bits).MemReal (radialRatio a.terms b.terms x) ∧
      (ratioDerivRange (ratioCell a b C bits) (a.radialCell C bits) (b.radialCell C bits)
        (C.inverseRadius bits) (C.coord k)).MemReal ((∂[k] (radialRatio a.terms b.terms)) x) := by
  have hn : 0 < ‖x‖ ^ 2 := norm_sq_pos_of_pos hx.1
  have hA := a.radialCell_mem ha.radial ha.axialMin_eq ha.min hC hx (bits := bits)
  have hB := b.radialCell_mem hb.radial hb.axialMin_eq hb.min hC hx (bits := bits)
  have hMa := ha.moment_pos hn
  have hMb := hb.moment_pos hn
  have hd := partialDeriv_radialRatio hn hMa hMb k
  have hQ : (ratioCell a b C bits).MemReal (radialRatio a.terms b.terms x) := by
    unfold ratioCell ratioRange
    have h := mul_sound (C.radiusPow_mem hC hx hR ((a.degreeMin - b.degreeMin) / 2))
      (divPositiveOrZero_sound hB.2.2.2.1 hA.2.2.1 hB.2.2.1)
    convert h using 1
    unfold radialRatio
    have e : (‖x‖ ^ 2) ^ ((((a.degreeMin - b.degreeMin) / 2 : ℚ) : ℝ)) *
        (‖x‖ ^ 2) ^ (-(a.degreeMin : ℝ) / 2) = (‖x‖ ^ 2) ^ (-(b.degreeMin : ℝ) / 2) := by
      rw [← Real.rpow_add hn]; congr 1; push_cast; ring
    have hpa := Real.rpow_pos_of_pos hn (-(a.degreeMin : ℝ) / 2)
    have hpb := Real.rpow_pos_of_pos hn (-(b.degreeMin : ℝ) / 2)
    rw [← mul_div_assoc, ← mul_assoc, e]
    field_simp
  refine ⟨hd.1, hQ, ?_⟩
  rw [hd.2]
  unfold ratioDerivRange
  convert mul_sound (mul_sound (mul_sound hQ (sub_sound hA.1 hB.1))
    (C.inverseRadius_mem hC hx hR)) (C.coord_mem hx k) using 1
  field_simp

open RationalInterval in
/-- **The rate of a radial weight on a cell**: `Aₗ = ∂ₗψ/ψ` and `∂ₖ Aₗ` lie in their enclosures
at every point of the cell, when `R₋ > 0`. -/
theorem rate_mem (hw : w.IsRadialWeight) (hC : C.Valid) (hx : C.Mem x)
    (hR : 0 < C.radiusLower bits) (k l : Fin 2) :
    DifferentiableAt ℝ (radialRate w.terms l) x ∧
      (rateRange (w.radialCell C bits) (C.inverseRadius bits) (C.coord l)).MemReal
        (radialRate w.terms l x) ∧
      (rateDerivRange (w.radialCell C bits) (C.inverseRadius bits) (C.coord k) (C.coord l)
        (if k = l then 1 else 0)).MemReal ((∂[k] (radialRate w.terms l)) x) := by
  have hn : 0 < ‖x‖ ^ 2 := norm_sq_pos_of_pos hx.1
  have hW := w.radialCell_mem hw.radial hw.axialMin_eq hw.min hC hx (bits := bits)
  have hr := C.inverseRadius_mem hC hx hR (bits := bits)
  have hd := partialDeriv_radialRate hn (hw.moment_pos hn) k l
  refine ⟨hd.1, ?_, ?_⟩
  · unfold rateRange
    convert mul_sound (mul_sound hW.1 hr) (C.coord_mem hx l) using 1
    unfold radialRate; field_simp
  · rw [hd.2]
    unfold rateDerivRange
    convert add_sound (mul_sound (mul_sound (sub_sound hW.2.1 (mul_sound (memReal_const 2) hW.1))
      (mul_sound hr hr)) (mul_sound (C.coord_mem hx k) (C.coord_mem hx l)))
      (mul_sound (mul_sound hW.1 hr) (memReal_const (if k = l then 1 else 0))) using 1
    push_cast
    field_simp
    split_ifs <;> ring

/-- **The mean degree of a radial weight on a cell**: `Γ = x·∇ψ/ψ` and `∂ₖ Γ` lie in their
enclosures at every point of the cell, when `R₋ > 0`. -/
theorem degree_deriv_mem (hw : w.IsRadialWeight) (hC : C.Valid) (hx : C.Mem x)
    (hR : 0 < C.radiusLower bits) (k : Fin 2) :
    DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) ↦ radialDegree w.terms (‖y‖ ^ 2)) x ∧
      (w.radialCell C bits).degree.MemReal (radialDegree w.terms (‖x‖ ^ 2)) ∧
      (degreeDerivRange (w.radialCell C bits) (C.inverseRadius bits) (C.coord k)).MemReal
        ((∂[k] (fun y : EuclideanSpace ℝ (Fin 2) ↦ radialDegree w.terms (‖y‖ ^ 2))) x) := by
  have hn : 0 < ‖x‖ ^ 2 := norm_sq_pos_of_pos hx.1
  have hW := w.radialCell_mem hw.radial hw.axialMin_eq hw.min hC hx (bits := bits)
  have hd := partialDeriv_radialDegree hn (hw.moment_pos hn) k
  refine ⟨hd.1, hW.1, ?_⟩
  rw [hd.2]
  unfold degreeDerivRange
  convert RationalInterval.mul_sound (RationalInterval.mul_sound hW.2.1
    (C.inverseRadius_mem hC hx hR)) (C.coord_mem hx k) using 1
  field_simp

open RationalInterval in
/-- **The strain rate of a radial weight on a cell**: `S = (x₀ ∂₀ψ - x₁ ∂₁ψ)/ψ` and `∂ₖ S` lie in
their enclosures at every point of the cell, when `R₋ > 0`. -/
theorem strainRate_mem (hw : w.IsRadialWeight) (hC : C.Valid) (hx : C.Mem x)
    (hR : 0 < C.radiusLower bits) (k : Fin 2) :
    DifferentiableAt ℝ (radialStrainRate w.terms) x ∧
      (rateRange (w.radialCell C bits) (C.inverseRadius bits) C.squareDifference).MemReal
        (radialStrainRate w.terms x) ∧
      (strainDerivRange (w.radialCell C bits) (C.inverseRadius bits) (C.coord k)
        C.squareDifference (![1, -1] k)).MemReal ((∂[k] (radialStrainRate w.terms)) x) := by
  have hn : 0 < ‖x‖ ^ 2 := norm_sq_pos_of_pos hx.1
  have hW := w.radialCell_mem hw.radial hw.axialMin_eq hw.min hC hx (bits := bits)
  have hr := C.inverseRadius_mem hC hx hR (bits := bits)
  have hM := C.squareDifference_mem hC hx
  have hd := partialDeriv_radialStrainRate hn (hw.moment_pos hn) k
  refine ⟨hd.1, ?_, ?_⟩
  · unfold rateRange
    convert mul_sound (mul_sound hW.1 hr) hM using 1
    unfold radialStrainRate; field_simp
  · rw [hd.2]
    unfold strainDerivRange
    convert add_sound (mul_sound (mul_sound (sub_sound hW.2.1 (mul_sound (memReal_const 2) hW.1))
      (mul_sound hr hr)) (mul_sound (C.coord_mem hx k) hM))
      (mul_sound (mul_sound hW.1 hr) (mul_sound (memReal_const (2 * ![1, -1] k))
        (C.coord_mem hx k))) using 1
    fin_cases k <;> simp <;> field_simp

open RationalInterval in
/-- **The rate divided by a second radial weight on a cell**: `Aₗ/ψ_u` and its derivatives lie in
their enclosures at every point of the cell, when `R₋ > 0`. -/
theorem remainderRate_mem (hw : w.IsRadialWeight) (hu : u.IsRadialWeight) (hC : C.Valid)
    (hx : C.Mem x) (hR : 0 < C.radiusLower bits) (k l : Fin 2) :
    DifferentiableAt ℝ (radialRemainderRate w.terms u.terms l) x ∧
      (remainderRateRange (w.radialCell C bits) (C.inverseRadius bits) (ratioCell one u C bits)
        (C.coord l)).MemReal (radialRemainderRate w.terms u.terms l x) ∧
      (remainderRateDerivRange (w.radialCell C bits) (u.radialCell C bits) (C.inverseRadius bits)
        (ratioCell one u C bits) (C.coord k) (C.coord l) (if k = l then 1 else 0)).MemReal
        ((∂[k] (radialRemainderRate w.terms u.terms l)) x) := by
  have hn : 0 < ‖x‖ ^ 2 := norm_sq_pos_of_pos hx.1
  have hW := w.radialCell_mem hw.radial hw.axialMin_eq hw.min hC hx (bits := bits)
  have hU := u.radialCell_mem hu.radial hu.axialMin_eq hu.min hC hx (bits := bits)
  have hr := C.inverseRadius_mem hC hx hR (bits := bits)
  have hMu := hu.moment_pos hn
  have hinv := (ratio_mem one_isRadialWeight hu hC hx hR 0).2.1
  have hinv' : (ratioCell one u C bits).MemReal (radialMoment u.terms 1 (‖x‖ ^ 2))⁻¹ := by
    convert hinv using 1
    simp [radialRatio, one]
  have hd := partialDeriv_radialRemainderRate hn (hw.moment_pos hn) hMu k l
  refine ⟨hd.1, ?_, ?_⟩
  · unfold remainderRateRange
    convert mul_sound (mul_sound (mul_sound hW.1 hr) hinv') (C.coord_mem hx l) using 1
    unfold radialRemainderRate; field_simp
  · rw [hd.2]
    unfold remainderRateDerivRange
    convert add_sound (mul_sound (mul_sound (mul_sound (sub_sound (sub_sound hW.2.1
      (mul_sound (memReal_const 2) hW.1)) (mul_sound hW.1 hU.1)) (mul_sound hr hr)) hinv')
      (mul_sound (C.coord_mem hx k) (C.coord_mem hx l)))
      (mul_sound (mul_sound (mul_sound hW.1 hr) hinv') (memReal_const (if k = l then 1 else 0)))
      using 1
    push_cast
    field_simp
    split_ifs <;> ring

end AxialWeight

end Cells

end CAS.Numerics
