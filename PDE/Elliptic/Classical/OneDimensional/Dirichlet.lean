/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import PDE.FDeriv.Polar.Laplacian
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Constant-coefficient Dirichlet inversion on an interval

Variation of constants constructs a solution of `-f'' - a² f = g` with zero
values at `0` and `L` when `a * sin(aL) ≠ 0`. A continuous forcing gives a
classical `C²` solution. An interval sup bound on the forcing gives explicit
bounds on the solution and its first derivative, with the resonance factor
kept in the denominator. A `C²` approximation with exact zero endpoints
can be corrected to an exact solution, with value and derivative errors
bounded by its differential residual. Conserved oscillator energy proves initial-jet
uniqueness and transfers odd forcing parity to the constructed solution.

The final results apply this construction to the angular equation for
homogeneous planar sources, the boundary value problem (7.7) of Chen and Hou I.
They combine the inverse with the foundational polar Laplacian identities,
including the source exponent range `-2 < α < 0`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 7.2.1, (7.7).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public noncomputable section

open MeasureTheory

namespace PDE.Elliptic.Classical.OneDimensional

private def cosinePrimitive (a : ℝ) (g : ℝ → ℝ) (β : ℝ) : ℝ :=
  ∫ s in 0..β, Real.cos (a * s) * g s

private def sinePrimitive (a : ℝ) (g : ℝ → ℝ) (β : ℝ) : ℝ :=
  ∫ s in 0..β, Real.sin (a * s) * g s

private def dirichletAmplitude (a L : ℝ) (g : ℝ → ℝ) : ℝ :=
  (Real.sin (a * L) * cosinePrimitive a g L -
    Real.cos (a * L) * sinePrimitive a g L) / (a * Real.sin (a * L))

/-- Variation of constants for `-f'' - a² f = g`, with the sine amplitude chosen
to give `f(L) = 0`. Both boundary values hold when `a * sin(aL) ≠ 0`.
At resonance the total formula is defined but need not satisfy the right boundary. -/
def dirichletSolution (a L : ℝ) (g : ℝ → ℝ) (β : ℝ) : ℝ :=
  let C := fun x ↦ ∫ s in 0..x, Real.cos (a * s) * g s
  let S := fun x ↦ ∫ s in 0..x, Real.sin (a * s) * g s
  let A := (Real.sin (a * L) * C L - Real.cos (a * L) * S L) /
    (a * Real.sin (a * L))
  A * Real.sin (a * β) + (Real.cos (a * β) * S β - Real.sin (a * β) * C β) / a

private theorem dirichletSolution_formula (a L : ℝ) (g : ℝ → ℝ) (β : ℝ) :
    dirichletSolution a L g β =
      dirichletAmplitude a L g * Real.sin (a * β) +
      (Real.cos (a * β) * sinePrimitive a g β -
        Real.sin (a * β) * cosinePrimitive a g β) / a := rfl

private def dirichletDerivative (a L : ℝ) (g : ℝ → ℝ) (β : ℝ) : ℝ :=
  a * dirichletAmplitude a L g * Real.cos (a * β) -
    Real.sin (a * β) * sinePrimitive a g β -
      Real.cos (a * β) * cosinePrimitive a g β

private theorem hasDerivAt_cosinePrimitive
    (a β : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    HasDerivAt (cosinePrimitive a g) (Real.cos (a * β) * g β) β := by
  exact ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul hg
    |>.integral_hasStrictDerivAt 0 β).hasDerivAt

private theorem hasDerivAt_sinePrimitive
    (a β : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    HasDerivAt (sinePrimitive a g) (Real.sin (a * β) * g β) β := by
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul hg
    |>.integral_hasStrictDerivAt 0 β).hasDerivAt

private theorem hasDerivAt_dirichletSolution
    {a : ℝ} (ha : a ≠ 0) (L β : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    HasDerivAt (dirichletSolution a L g)
      (dirichletDerivative a L g β) β := by
  have hs := ((hasDerivAt_id β).const_mul a).sin
  have hc := ((hasDerivAt_id β).const_mul a).cos
  have hC := hasDerivAt_cosinePrimitive a β hg
  have hS := hasDerivAt_sinePrimitive a β hg
  convert (hs.const_mul (dirichletAmplitude a L g)).add
    (((hc.mul hS).sub (hs.mul hC)).div_const a) using 1
  · rfl
  · dsimp [dirichletDerivative]
    field_simp
    ring

private theorem hasDerivAt_dirichletDerivative
    (a L β : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    HasDerivAt (dirichletDerivative a L g)
      (-a ^ 2 * dirichletSolution a L g β - g β) β := by
  have hs := ((hasDerivAt_id β).const_mul a).sin
  have hc := ((hasDerivAt_id β).const_mul a).cos
  have hC := hasDerivAt_cosinePrimitive a β hg
  have hS := hasDerivAt_sinePrimitive a β hg
  convert ((hc.const_mul (a * dirichletAmplitude a L g)).sub
    (hs.mul hS)).sub (hc.mul hC) using 1
  · rfl
  · rw [dirichletSolution_formula]
    simp only [id_eq]
    by_cases ha : a = 0
    · subst a
      simp
    · field_simp
      linear_combination g β * Real.sin_sq_add_cos_sq (a * β)

/-- The variation-of-constants formula vanishes at the left endpoint. -/
@[simp] theorem dirichletSolution_zero (a L : ℝ) (g : ℝ → ℝ) :
    dirichletSolution a L g 0 = 0 := by
  rw [dirichletSolution_formula]
  simp [sinePrimitive, cosinePrimitive]

/-- Nonresonance makes the chosen sine amplitude enforce the right boundary value. -/
theorem dirichletSolution_right
    {a L : ℝ} (hL : Real.sin (a * L) ≠ 0) (g : ℝ → ℝ) :
    dirichletSolution a L g L = 0 := by
  have ha : a ≠ 0 := by rintro rfl; simp at hL
  rw [dirichletSolution_formula]
  dsimp [dirichletAmplitude]
  field_simp
  ring

/-- A continuous forcing is recovered exactly by the shifted negative second derivative. -/
theorem dirichletSolution_equation
    {a : ℝ} (ha : a ≠ 0) (L : ℝ) {g : ℝ → ℝ} (hg : Continuous g) (β : ℝ) :
    -deriv (deriv (dirichletSolution a L g)) β -
      a ^ 2 * dirichletSolution a L g β = g β := by
  have hfirst : deriv (dirichletSolution a L g) =
      dirichletDerivative a L g := by
    funext x
    exact (hasDerivAt_dirichletSolution ha L x hg).deriv
  rw [hfirst, (hasDerivAt_dirichletDerivative a L β hg).deriv]
  ring

/-- A continuous forcing gives a classical `C²` angular solution. -/
theorem contDiff_dirichletSolution
    {a : ℝ} (ha : a ≠ 0) (L : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    ContDiff ℝ 2 (dirichletSolution a L g) := by
  have hf : Differentiable ℝ (dirichletSolution a L g) :=
    fun β ↦ (hasDerivAt_dirichletSolution ha L β hg).differentiableAt
  have hfirst : deriv (dirichletSolution a L g) =
      dirichletDerivative a L g := by
    funext β
    exact (hasDerivAt_dirichletSolution ha L β hg).deriv
  have hsecond : deriv (dirichletDerivative a L g) =
      fun β ↦ -a ^ 2 * dirichletSolution a L g β - g β := by
    funext β
    exact (hasDerivAt_dirichletDerivative a L β hg).deriv
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨hf, by norm_num, ?_⟩
  rw [hfirst, contDiff_one_iff_deriv]
  refine ⟨fun β ↦ (hasDerivAt_dirichletDerivative a L β hg).differentiableAt, ?_⟩
  rw [hsecond]
  exact (continuous_const.mul hf.continuous).sub hg

private theorem abs_integral_bounded_mul_le
    {L M β : ℝ} {g k : ℝ → ℝ} (hβ : β ∈ Set.Icc 0 L)
    (hg : ∀ s ∈ Set.Icc 0 L, |g s| ≤ M) (hk : ∀ s, |k s| ≤ 1) :
    |∫ s in 0..β, k s * g s| ≤ M * β := by
  have hb : ∀ s ∈ Set.uIoc 0 β, ‖k s * g s‖ ≤ M := by
    intro s hs
    rw [Set.uIoc_of_le hβ.1] at hs
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |k s| * |g s| ≤ 1 * |g s| :=
        mul_le_mul_of_nonneg_right (hk s) (abs_nonneg _)
      _ ≤ M := by simpa using hg s ⟨hs.1.le, hs.2.trans hβ.2⟩
  simpa [Real.norm_eq_abs, abs_of_nonneg hβ.1] using
    intervalIntegral.norm_integral_le_of_norm_le_const hb

private theorem abs_dirichletAmplitude_le
    {a L M : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    {g : ℝ → ℝ} (hg : ∀ s ∈ Set.Icc 0 L, |g s| ≤ M) :
    |dirichletAmplitude a L g| ≤ (2 * M * L) / (a * |Real.sin (a * L)|) := by
  have hC x (hx : x ∈ Set.Icc 0 L) : |cosinePrimitive a g x| ≤ M * x :=
    abs_integral_bounded_mul_le hx hg (fun s ↦ Real.abs_cos_le_one (a * s))
  have hS x (hx : x ∈ Set.Icc 0 L) : |sinePrimitive a g x| ≤ M * x :=
    abs_integral_bounded_mul_le hx hg (fun s ↦ Real.abs_sin_le_one (a * s))
  have hproduct (t c : ℝ) (ht : |t| ≤ 1) : |t * c| ≤ |c| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_right ht (abs_nonneg c)
  dsimp [dirichletAmplitude]
  rw [abs_div, abs_mul, abs_of_pos ha]
  apply div_le_div_of_nonneg_right _ (mul_nonneg ha.le (abs_nonneg _))
  calc
    _ ≤ |Real.sin (a * L) * cosinePrimitive a g L| +
        |Real.cos (a * L) * sinePrimitive a g L| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
            (Real.sin (a * L) * cosinePrimitive a g L)
            (-(Real.cos (a * L) * sinePrimitive a g L))
    _ ≤ M * L + M * L := add_le_add
      ((hproduct _ _ (Real.abs_sin_le_one _)).trans (hC L ⟨hL, le_rfl⟩))
      ((hproduct _ _ (Real.abs_cos_le_one _)).trans (hS L ⟨hL, le_rfl⟩))
    _ = 2 * M * L := by ring

/-- An interval bound on the forcing gives an explicit sup bound on the solution.
Continuity is needed for the differential equation, but not for this integral estimate.
The right boundary condition separately requires `sin(aL) ≠ 0`. -/
theorem abs_dirichletSolution_le
    {a L M β : ℝ} (ha : 0 < a)
    {g : ℝ → ℝ} (hg : ∀ s ∈ Set.Icc 0 L, |g s| ≤ M)
    (hβ : β ∈ Set.Icc 0 L) :
    |dirichletSolution a L g β| ≤
      2 * M * L / a * (1 + 1 / |Real.sin (a * L)|) := by
  have hL : 0 ≤ L := hβ.1.trans hβ.2
  have hM : 0 ≤ M := (abs_nonneg _).trans (hg β hβ)
  have hC x (hx : x ∈ Set.Icc 0 L) : |cosinePrimitive a g x| ≤ M * x :=
    abs_integral_bounded_mul_le hx hg (fun s ↦ Real.abs_cos_le_one (a * s))
  have hS x (hx : x ∈ Set.Icc 0 L) : |sinePrimitive a g x| ≤ M * x :=
    abs_integral_bounded_mul_le hx hg (fun s ↦ Real.abs_sin_le_one (a * s))
  have hproduct (t c : ℝ) (ht : |t| ≤ 1) : |t * c| ≤ |c| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_right ht (abs_nonneg c)
  have hA := abs_dirichletAmplitude_le ha hL hg
  have hnumerator :
      |Real.cos (a * β) * sinePrimitive a g β -
        Real.sin (a * β) * cosinePrimitive a g β| ≤ 2 * M * L := by
    calc
      _ ≤ |Real.cos (a * β) * sinePrimitive a g β| +
          |Real.sin (a * β) * cosinePrimitive a g β| := by
            simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
              (Real.cos (a * β) * sinePrimitive a g β)
              (-(Real.sin (a * β) * cosinePrimitive a g β))
      _ ≤ M * β + M * β := add_le_add
        ((hproduct _ _ (Real.abs_cos_le_one _)).trans (hS β hβ))
        ((hproduct _ _ (Real.abs_sin_le_one _)).trans (hC β hβ))
      _ ≤ 2 * M * L := by nlinarith [mul_le_mul_of_nonneg_left hβ.2 hM]
  rw [dirichletSolution_formula]
  calc
    _ ≤ |dirichletAmplitude a L g * Real.sin (a * β)| +
        |(Real.cos (a * β) * sinePrimitive a g β -
          Real.sin (a * β) * cosinePrimitive a g β) / a| := abs_add_le _ _
    _ ≤ (2 * M * L) / (a * |Real.sin (a * L)|) + (2 * M * L) / a := by
      apply add_le_add
      · rw [mul_comm]
        exact (hproduct _ _ (Real.abs_sin_le_one _)).trans hA
      · rw [abs_div, abs_of_pos ha]
        exact div_le_div_of_nonneg_right hnumerator ha.le
    _ = _ := by
      field_simp
      ring

/-- A uniform forcing bound controls the first derivative of the angular solution.
The same resonance factor as the value estimate is retained in the coefficient. -/
theorem abs_deriv_dirichletSolution_le
    {a L M β : ℝ} (ha : 0 < a)
    {g : ℝ → ℝ} (hg : Continuous g)
    (hbound : ∀ s ∈ Set.Icc 0 L, |g s| ≤ M) (hβ : β ∈ Set.Icc 0 L) :
    |deriv (dirichletSolution a L g) β| ≤
      2 * M * L * (1 + 1 / |Real.sin (a * L)|) := by
  have hL : 0 ≤ L := hβ.1.trans hβ.2
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbound β hβ)
  have hC : |cosinePrimitive a g β| ≤ M * β :=
    abs_integral_bounded_mul_le hβ hbound (fun s ↦ Real.abs_cos_le_one (a * s))
  have hS : |sinePrimitive a g β| ≤ M * β :=
    abs_integral_bounded_mul_le hβ hbound (fun s ↦ Real.abs_sin_le_one (a * s))
  have hA := abs_dirichletAmplitude_le ha hL hbound
  have hproduct (t c : ℝ) (ht : |t| ≤ 1) : |t * c| ≤ |c| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_right ht (abs_nonneg c)
  have htriangle (x y z : ℝ) : |x - y - z| ≤ |x| + |y| + |z| := by
    calc
      _ ≤ |x - y| + |z| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (x - y) (-z)
      _ ≤ (|x| + |y|) + |z| := by
        apply add_le_add _ le_rfl
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)
  rw [(hasDerivAt_dirichletSolution ha.ne' L β hg).deriv]
  dsimp only [dirichletDerivative]
  calc
    _ ≤ |a * dirichletAmplitude a L g * Real.cos (a * β)| +
        |Real.sin (a * β) * sinePrimitive a g β| +
        |Real.cos (a * β) * cosinePrimitive a g β| := htriangle _ _ _
    _ ≤ a * ((2 * M * L) / (a * |Real.sin (a * L)|)) + M * β + M * β := by
      apply add_le_add
      · apply add_le_add
        · rw [mul_comm (a * _), abs_mul, abs_mul, abs_of_pos ha]
          calc
            _ ≤ 1 * (a * |dirichletAmplitude a L g|) :=
              mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)
            _ ≤ a * ((2 * M * L) / (a * |Real.sin (a * L)|)) := by
              simpa using mul_le_mul_of_nonneg_left hA ha.le
        · exact (hproduct _ _ (Real.abs_sin_le_one _)).trans hS
      · exact (hproduct _ _ (Real.abs_cos_le_one _)).trans hC
    _ ≤ a * ((2 * M * L) / (a * |Real.sin (a * L)|)) + 2 * M * L := by
      nlinarith [mul_le_mul_of_nonneg_left hβ.2 hM]
    _ = _ := by
      field_simp
      ring

/-- A bounded differential residual produces an exact zero-boundary correction,
with explicit value and first-derivative error bounds. The corrected solution
is constructed directly, without assuming uniqueness. -/
theorem exists_dirichletSolution_near_of_residual_bound
    {a L M : ℝ} (ha : 0 < a)
    (hsin : Real.sin (a * L) ≠ 0)
    {q g : ℝ → ℝ} (hq : ContDiff ℝ 2 q) (hg : Continuous g)
    (hq₀ : q 0 = 0) (hqL : q L = 0)
    (hresidual : ∀ β ∈ Set.Icc 0 L,
      |g β + deriv (deriv q) β + a ^ 2 * q β| ≤ M) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ f 0 = 0 ∧ f L = 0 ∧
      (∀ β, -deriv (deriv f) β - a ^ 2 * f β = g β) ∧
      ∀ β ∈ Set.Icc 0 L,
        |f β - q β| ≤ 2 * M * L / a * (1 + 1 / |Real.sin (a * L)|) ∧
        |deriv f β - deriv q β| ≤ 2 * M * L * (1 + 1 / |Real.sin (a * L)|) := by
  let r : ℝ → ℝ := fun β ↦ g β + deriv (deriv q) β + a ^ 2 * q β
  have hq' : ContDiff ℝ 1 (deriv q) := by simpa using hq.deriv' (n := 1)
  have hr : Continuous r :=
    (hg.add hq'.continuous_deriv_one).add (continuous_const.mul hq.continuous)
  let w : ℝ → ℝ := dirichletSolution a L r
  have hw : ContDiff ℝ 2 w := contDiff_dirichletSolution ha.ne' L hr
  have hfirst : deriv (fun β ↦ q β + w β) = fun β ↦ deriv q β + deriv w β := by
    funext β
    exact deriv_fun_add (hq.differentiable (by norm_num) β)
      (hw.differentiable (by norm_num) β)
  have hsecond β :
      deriv (deriv (fun β ↦ q β + w β)) β = deriv (deriv q) β + deriv (deriv w) β := by
    rw [hfirst]
    exact deriv_fun_add (hq.differentiable_deriv_two β) (hw.differentiable_deriv_two β)
  refine ⟨fun β ↦ q β + w β, hq.add hw, ?_, ?_, ?_, ?_⟩
  · simp [w, hq₀]
  · change q L + w L = 0
    rw [hqL, show w L = 0 from dirichletSolution_right hsin r]
    simp
  · intro β
    rw [hsecond]
    have heq := dirichletSolution_equation ha.ne' L hr β
    change -deriv (deriv w) β - a ^ 2 * w β =
      g β + deriv (deriv q) β + a ^ 2 * q β at heq
    linarith
  · intro β hβ
    constructor
    · simpa only [add_sub_cancel_left] using
        abs_dirichletSolution_le ha hresidual hβ
    · rw [hfirst]
      simpa only [add_sub_cancel_left] using
        abs_deriv_dirichletSolution_le ha hr hresidual hβ

/-- A real-frequency homogeneous oscillator with zero initial jet vanishes.
The proof uses conserved energy, including the zero-frequency case. -/
private theorem oscillator_eq_zero_of_initial_jet
    (a t₀ : ℝ) {d : ℝ → ℝ} (hd : ContDiff ℝ 2 d)
    (heq : ∀ t, deriv (deriv d) t + a ^ 2 * d t = 0)
    (hvalue : d t₀ = 0) (hslope : deriv d t₀ = 0) : d = 0 := by
  let E : ℝ → ℝ := fun t ↦ (deriv d t) ^ 2 + a ^ 2 * (d t) ^ 2
  have hd₁ : Differentiable ℝ d := hd.differentiable (by norm_num)
  have hd₂ : Differentiable ℝ (deriv d) := hd.differentiable_deriv_two
  have hE (t : ℝ) : HasDerivAt E 0 t := by
    convert ((hd₂ t).hasDerivAt.pow 2).add
      (((hd₁ t).hasDerivAt.pow 2).const_mul (a ^ 2)) using 1
    have ht := heq t
    dsimp
    rw [show deriv (deriv d) t = -a ^ 2 * d t by linarith]
    ring
  have hconstant (t : ℝ) : E t = E t₀ :=
    is_const_of_deriv_eq_zero (fun x ↦ (hE x).differentiableAt)
      (fun x ↦ (hE x).deriv) t t₀
  have hzero (t : ℝ) : deriv d t = 0 := by
    have ht := hconstant t
    simp only [E, hvalue, hslope] at ht
    have hnonneg : 0 ≤ a ^ 2 * (d t) ^ 2 :=
      mul_nonneg (sq_nonneg a) (sq_nonneg (d t))
    have hsquare : (deriv d t) ^ 2 = 0 :=
      le_antisymm (by linarith) (sq_nonneg _)
    exact sq_eq_zero_iff.mp hsquare
  funext t
  have ht := is_const_of_deriv_eq_zero hd₁ hzero t t₀
  simpa [hvalue] using ht

/-- Forced oscillator solutions with the same initial value and slope agree.
The conserved energy of their difference proves uniqueness. -/
theorem oscillator_eq_of_initial_jet
    (a t₀ : ℝ) {f q g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hq : ContDiff ℝ 2 q)
    (heqf : ∀ t, -deriv (deriv f) t - a ^ 2 * f t = g t)
    (heqq : ∀ t, -deriv (deriv q) t - a ^ 2 * q t = g t)
    (hvalue : f t₀ = q t₀) (hslope : deriv f t₀ = deriv q t₀) : f = q := by
  have hf₁ : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hq₁ : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hfirst : deriv (f - q) = deriv f - deriv q := by
    funext t
    exact deriv_sub (hf₁ t) (hq₁ t)
  have hsecond : deriv (deriv (f - q)) = deriv (deriv f) - deriv (deriv q) := by
    rw [hfirst]
    funext t
    exact deriv_sub (hf.differentiable_deriv_two t) (hq.differentiable_deriv_two t)
  have hd : f - q = 0 := oscillator_eq_zero_of_initial_jet a t₀ (hf.sub hq)
    (by intro t; rw [hsecond]; change
        deriv (deriv f) t - deriv (deriv q) t + a ^ 2 * (f t - q t) = 0
        linarith [heqf t, heqq t])
    (by change f t₀ - q t₀ = 0; exact sub_eq_zero.mpr hvalue)
    (by rw [hfirst]; change deriv f t₀ - deriv q t₀ = 0
        exact sub_eq_zero.mpr hslope)
  exact sub_eq_zero.mp hd

/-- Odd forcing about a zero of the solution gives odd angular streamfunction.
Reflection preserves the equation and its initial jet at the zero. -/
theorem oscillator_odd_about_zero
    (a L : ℝ) {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (heq : ∀ t, -deriv (deriv f) t - a ^ 2 * f t = g t)
    (hzero : f L = 0) (hodd : ∀ t, g (2 * L - t) = -g t) :
    ∀ t, f (2 * L - t) = -f t := by
  let q : ℝ → ℝ := fun t ↦ -f (2 * L - t)
  have hf₁ : Differentiable ℝ f := hf.differentiable (by norm_num)
  have href (t : ℝ) : HasDerivAt (fun s : ℝ ↦ 2 * L - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub (2 * L)
  have hq : ContDiff ℝ 2 q :=
    (hf.comp (contDiff_const.sub contDiff_id)).neg
  have hqfirst : deriv q = fun t ↦ deriv f (2 * L - t) := by
    funext t
    simpa [q, Function.comp_def] using
      (((hf₁ (2 * L - t)).hasDerivAt.comp t (href t)).neg).deriv
  have hqsecond : deriv (deriv q) = fun t ↦ -deriv (deriv f) (2 * L - t) := by
    rw [hqfirst]
    funext t
    simpa [Function.comp_def] using
      ((hf.differentiable_deriv_two (2 * L - t)).hasDerivAt.comp t (href t)).deriv
  have heqq (t : ℝ) : -deriv (deriv q) t - a ^ 2 * q t = g t := by
    rw [hqsecond]
    dsimp [q]
    have h := heq (2 * L - t)
    rw [hodd t] at h
    linarith
  have hequal : f = q := oscillator_eq_of_initial_jet a L hf hq heq heqq
    (by dsimp [q]; rw [show 2 * L - L = L by ring, hzero]; simp)
    (by rw [hqfirst]; congr 1; ring)
  intro t
  have ht := congrFun hequal t
  change f t = -f (2 * L - t) at ht
  linarith

/-- The explicit nonresonant inverse respects tangential oddness of its source. -/
theorem dirichletSolution_odd_about_right
    {a L : ℝ} (hsin : Real.sin (a * L) ≠ 0)
    {g : ℝ → ℝ} (hg : Continuous g)
    (hodd : ∀ t, g (2 * L - t) = -g t) :
    ∀ t, dirichletSolution a L g (2 * L - t) = -dirichletSolution a L g t := by
  have ha : a ≠ 0 := by rintro rfl; simp at hsin
  exact oscillator_odd_about_zero a L (contDiff_dirichletSolution ha L hg)
    (fun t ↦ dirichletSolution_equation ha L hg t)
    (dirichletSolution_right hsin g) hodd

/-- The second angular derivative vanishes at the tangential axis when the
forcing is odd there. This is the C² odd-reflection compatibility condition. -/
theorem dirichletSolution_second_deriv_right_eq_zero
    {a L : ℝ} (hsin : Real.sin (a * L) ≠ 0)
    {g : ℝ → ℝ} (hg : Continuous g)
    (hodd : ∀ t, g (2 * L - t) = -g t) :
    deriv (deriv (dirichletSolution a L g)) L = 0 := by
  have ha : a ≠ 0 := by rintro rfl; simp at hsin
  have hgzero : g L = 0 := by
    have h := hodd L
    rw [show 2 * L - L = L by ring] at h
    linarith
  have h := dirichletSolution_equation ha L hg L
  rw [dirichletSolution_right hsin g, hgzero] at h
  linarith

end PDE.Elliptic.Classical.OneDimensional

namespace PDE.CoordinateSystems

section AngularDirichlet

open PDE.Elliptic.Classical.OneDimensional

private theorem sin_frequency_mul_pi_div_two_pos
    {a : ℝ} (ha : 0 < a) (ha₂ : a < 2) :
    0 < Real.sin (a * (Real.pi / 2)) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos ha (div_pos Real.pi_pos (by norm_num))
  · nlinarith [Real.pi_pos]

/-- For `-2 < α < 0` and continuous `g`, the angular equation `-f'' - (2 + α)² f = g` for
homogeneous planar sources has a `C²` solution with `f 0 = f (π/2) = 0`. This is the angular
problem (7.7) of Chen and Hou I, Section 7.2.1. -/
theorem exists_angularDirichletSolution
    {α : ℝ} (hα : -2 < α) (hα₀ : α < 0)
    {g : ℝ → ℝ} (hg : Continuous g) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ f 0 = 0 ∧ f (Real.pi / 2) = 0 ∧
      ∀ β, -deriv (deriv f) β - (2 + α) ^ 2 * f β = g β := by
  have ha : 0 < 2 + α := by linarith
  have ha₂ : 2 + α < 2 := by linarith
  refine ⟨dirichletSolution (2 + α) (Real.pi / 2) g,
    contDiff_dirichletSolution ha.ne' _ hg, dirichletSolution_zero _ _ _, ?_, ?_⟩
  · exact dirichletSolution_right (sin_frequency_mul_pi_div_two_pos ha ha₂).ne' g
  · exact dirichletSolution_equation ha.ne' _ hg

/-- The exact angular inverse produces the homogeneous far-field source under the
negative polar Laplacian. Cutting off the field also contributes the radial commutator. -/
theorem neg_planarPolarLaplacian_dirichletSolution
    {α : ℝ} (ha : 2 + α ≠ 0) (L r β : ℝ) (hr : 0 < r)
    {g : ℝ → ℝ} (hg : Continuous g) :
    -planarPolarLaplacian
      (fun s θ ↦ s ^ (2 + α) * dirichletSolution (2 + α) L g θ) r β =
        r ^ α * g β := by
  exact neg_planarPolarLaplacian_rpow_add_two_mul_eq _ g α r β hr
    (dirichletSolution_equation ha L hg β)

/-- The angular Dirichlet inverse reconstructs a classical Cartesian solution
of the homogeneous Poisson equation on the polar chart. -/
theorem neg_laplacian_profileFromPolar_dirichletSolution
    {α : ℝ} (ha : 2 + α ≠ 0) (L : ℝ)
    {g : ℝ → ℝ} (hg : Continuous g)
    {p : ℝ^2} (hp : PDE.FDeriv.pointPair p ∈ polarCoord.target) :
    -PDE.laplacian (PDE.FDeriv.profileFromPolar
      (fun r β ↦ r ^ (2 + α) *
        PDE.Elliptic.Classical.OneDimensional.dirichletSolution (2 + α) L g β))
      (planarPolarMap p) = (p 0) ^ α * g (p 1) :=
  EuclideanLaplacian.neg_laplacian_profileFromPolar_rpow_add_two_mul α
    (PDE.Elliptic.Classical.OneDimensional.contDiff_dirichletSolution ha L hg)
    (fun β ↦ PDE.Elliptic.Classical.OneDimensional.dirichletSolution_equation ha L hg β) hp

end AngularDirichlet

end PDE.CoordinateSystems
