/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Euler.Axisymmetric.CylinderStreamModes
public import PDE.Analysis.Fourier.SineSeries.Coefficients
public import PDE.Common.Euclidean
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import PDE.Analysis.Normed.PiLp.CoordinateProjection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Mode cutoffs and sine terms for the stream function series

The stream profile `Ψ(s, z)` of the cylinder, `s = r²`, is built as a sine series in `z` whose
`k`-th coefficient is the mode solution of `4 s Ψ'' + 8 Ψ' - μ_k² Ψ = -F_k`
(`Euler.Cylinder.modeSolution`). The mode solutions are smooth only on `s > -4/μ_k²` and grow
fast beyond `s = 1`, so each mode is multiplied by a cutoff `η_μ` equal to one on `[0, 1]` and
vanishing outside the collar `[-2/μ², 1 + 2/μ²]`, whose derivatives grow like powers of `μ²`
(`modeCutoff`). The cut-off modes are smooth on the whole line (`contDiff_modeTerm`) with the
derivative bounds of the mode solutions on the collar (`exists_abs_iteratedDeriv_modeTerm_le`),
and the planar terms `a(s) sin(μ z)` have iterated derivatives bounded by the derivatives of `a`
and the powers of `μ` (`norm_iteratedFDeriv_sineTerm_le`).

## Main definitions

* `modeStep`, `modeCutoff`: the smooth step and the mode cutoff.
* `modeTerm`: the cut-off mode solution.
* `sineTerm`: the planar term `a(s) sin(μ z)`.
-/

@[expose] public section

namespace Euler.Cylinder

open Set Filter
open scoped Topology Nat

set_option linter.missingDocs true

noncomputable section

/-! ### The step and the mode cutoff -/

/-- The smooth step `x ↦ smoothTransition (2 - x)`: one for `x ≤ 1`, zero for `x ≥ 2`. -/
def modeStep (x : ℝ) : ℝ :=
  Real.smoothTransition (2 - x)

/-- The step is smooth. -/
theorem contDiff_modeStep : ContDiff ℝ (⊤ : ℕ∞) modeStep :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

/-- The step is one for `x ≤ 1`. -/
theorem modeStep_of_le {x : ℝ} (hx : x ≤ 1) : modeStep x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The step vanishes for `x ≥ 2`. -/
theorem modeStep_of_ge {x : ℝ} (hx : 2 ≤ x) : modeStep x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- The derivative of the step vanishes outside `[1, 2]`. -/
theorem deriv_modeStep_eq_zero {x : ℝ} (hx : x ∉ Icc (1 : ℝ) 2) : deriv modeStep x = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · have : modeStep =ᶠ[𝓝 x] fun _ ↦ 1 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact modeStep_of_le (le_of_lt hy)
    rw [this.deriv_eq, deriv_const]
  · have : modeStep =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact modeStep_of_ge (le_of_lt hy)
    rw [this.deriv_eq, deriv_const]

/-- Every iterated derivative of the step is bounded. -/
theorem exists_abs_iteratedDeriv_modeStep_le :
    ∃ C : ℕ → ℝ, ∀ j x, |iteratedDeriv j modeStep x| ≤ C j := by
  have hcs : HasCompactSupport (deriv modeStep) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (1 : ℝ)) (b := 2))
    intro x hx
    by_contra h
    exact hx (deriv_modeStep_eq_zero h)
  have hb : ∀ j, ∃ C, ∀ x, |iteratedDeriv j modeStep x| ≤ C := by
    intro j
    rcases j with _ | j
    · exact ⟨1, fun x ↦ by
        rw [iteratedDeriv_zero]
        unfold modeStep
        rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
        exact Real.smoothTransition.le_one _⟩
    · have hcs' : HasCompactSupport (iteratedDeriv j (deriv modeStep)) := by
        induction j with
        | zero => simpa using hcs
        | succ j ih => rw [iteratedDeriv_succ]; exact ih.deriv
      have hcont : Continuous (iteratedDeriv j (deriv modeStep)) := by
        rw [← iteratedDeriv_succ']
        exact contDiff_modeStep.continuous_iteratedDeriv _ (by exact_mod_cast le_top)
      obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcs'
      exact ⟨C, fun x ↦ by rw [iteratedDeriv_succ']; simpa [Real.norm_eq_abs] using hC x⟩
  choose C hC using hb
  exact ⟨C, hC⟩

/-- The iterated derivatives of `x ↦ modeStep (c x + d)`. -/
theorem iteratedDeriv_modeStep_affine (j : ℕ) (c d : ℝ) :
    iteratedDeriv j (fun x ↦ modeStep (c * x + d)) =
      fun x ↦ c ^ j * iteratedDeriv j modeStep (c * x + d) := by
  have hsh : ContDiff ℝ j (fun u ↦ modeStep (u + d)) :=
    (contDiff_modeStep.comp (contDiff_id.add contDiff_const)).of_le (by exact_mod_cast le_top)
  have := iteratedDeriv_comp_const_mul (f := fun u ↦ modeStep (u + d)) hsh c
  rw [this]
  funext x
  rw [iteratedDeriv_comp_add_const]

/-- The mode cutoff `s ↦ χ(-μ² s) χ(μ² s - μ²)` with the step `χ`: one on `[0, 1]`, zero
outside `[-2/μ², 1 + 2/μ²]`. -/
def modeCutoff (μ s : ℝ) : ℝ :=
  modeStep (-μ ^ 2 * s + 0) * modeStep (μ ^ 2 * s + -μ ^ 2)

/-- The mode cutoff is smooth in `s`. -/
theorem contDiff_modeCutoff (μ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (modeCutoff μ) :=
  (contDiff_modeStep.comp ((contDiff_const.mul contDiff_id).add contDiff_const)).mul
    (contDiff_modeStep.comp ((contDiff_const.mul contDiff_id).add contDiff_const))

/-- The mode cutoff is one on `[0, 1]`. -/
theorem modeCutoff_of_mem {μ s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : modeCutoff μ s = 1 := by
  have h1 : -μ ^ 2 * s + 0 ≤ 1 := by nlinarith [sq_nonneg μ, hs.1]
  have h2 : μ ^ 2 * s + -μ ^ 2 ≤ 1 := by nlinarith [sq_nonneg μ, hs.2]
  rw [modeCutoff, modeStep_of_le h1, modeStep_of_le h2, one_mul]

/-- The mode cutoff vanishes outside the collar `[-2/μ², 1 + 2/μ²]`. -/
theorem modeCutoff_of_notMem {μ s : ℝ} (hμ : 0 < μ)
    (hs : s ∉ Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2)) : modeCutoff μ s = 0 := by
  have hμ2 : 0 < μ ^ 2 := by positivity
  rw [mem_Icc, not_and_or, not_le, not_le] at hs
  rcases hs with hs | hs
  · have : 2 ≤ -μ ^ 2 * s + 0 := by
      rw [lt_div_iff₀ hμ2] at hs
      linarith
    rw [modeCutoff, modeStep_of_ge this, zero_mul]
  · have : 2 ≤ μ ^ 2 * s + -μ ^ 2 := by
      have : 2 / μ ^ 2 < s - 1 := by linarith
      rw [div_lt_iff₀ hμ2] at this
      linarith
    rw [modeCutoff, modeStep_of_ge this, mul_zero]

/-- The iterated derivatives of the mode cutoff grow at most like `μ^{2j}`. -/
theorem exists_abs_iteratedDeriv_modeCutoff_le :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (μ : ℝ) (j : ℕ) (s : ℝ), |iteratedDeriv j (modeCutoff μ) s| ≤ C j * (μ ^ 2) ^ j := by
  obtain ⟨B, hB⟩ := exists_abs_iteratedDeriv_modeStep_le
  have hB0 : ∀ j, 0 ≤ B j := fun j ↦ (abs_nonneg _).trans (hB j 0)
  refine ⟨fun j ↦ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i * B (j - i),
    fun j ↦ Finset.sum_nonneg fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB0 i))
      (hB0 _), fun μ j s ↦ ?_⟩
  have hstep (a b : ℝ) : ContDiffAt ℝ j (fun x ↦ modeStep (a * x + b)) s :=
    (contDiff_modeStep.comp ((contDiff_const.mul contDiff_id).add contDiff_const)).contDiffAt.of_le
      (by exact_mod_cast le_top)
  change |iteratedDeriv j (fun x ↦ modeStep (-μ ^ 2 * x + 0) * modeStep (μ ^ 2 * x + -μ ^ 2)) s|
    ≤ _
  rw [iteratedDeriv_fun_mul (hstep _ _) (hstep _ _)]
  simp only [iteratedDeriv_modeStep_affine]
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
  have hpow : (μ ^ 2) ^ i * (μ ^ 2) ^ (j - i) = (μ ^ 2) ^ j := by
    rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
  have h₁ := hB i (-μ ^ 2 * s + 0)
  have h₂ := hB (j - i) (μ ^ 2 * s + -μ ^ 2)
  have hB0i := hB0 i
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_neg, Nat.abs_cast,
    abs_of_nonneg (sq_nonneg μ), ← hpow]
  calc _ = (j.choose i : ℝ) * ((μ ^ 2) ^ i * (μ ^ 2) ^ (j - i)) *
        (|iteratedDeriv i modeStep (-μ ^ 2 * s + 0)| *
          |iteratedDeriv (j - i) modeStep (μ ^ 2 * s + -μ ^ 2)|) := by ring
    _ ≤ (j.choose i : ℝ) * ((μ ^ 2) ^ i * (μ ^ 2) ^ (j - i)) * (B i * B (j - i)) := by gcongr
    _ = _ := by ring

/-! ### Cut-off mode solutions -/

/-- The cut-off mode solution `η_μ · modeSolution μ F`. -/
def modeTerm (μ : ℝ) (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  modeCutoff μ s * modeSolution μ F s

/-- Near points outside the collar the cut-off mode vanishes. -/
theorem modeTerm_eventuallyEq_zero {μ : ℝ} (hμ : 0 < μ) {F : ℝ → ℝ} {s : ℝ}
    (hs : s ∉ Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2)) : modeTerm μ F =ᶠ[𝓝 s] fun _ ↦ 0 := by
  have hopen : IsOpen (Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2))ᶜ := isClosed_Icc.isOpen_compl
  filter_upwards [hopen.mem_nhds hs] with y hy
  rw [modeTerm, modeCutoff_of_notMem hμ hy, zero_mul]

/-- The cut-off mode solution is smooth on the whole line. -/
theorem contDiff_modeTerm {μ : ℝ} (hμ : 0 < μ) {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (modeTerm μ F) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s ∈ Ioi (-4 / μ ^ 2)
  · exact (contDiff_modeCutoff μ).contDiffAt.mul
      ((contDiffOn_modeSolution hμ hF).contDiffAt (isOpen_Ioi.mem_nhds hs))
  · have hs' : s ∉ Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2) := fun h ↦
      hs (modeInterval_subset hμ h)
    exact contDiffAt_const.congr_of_eventuallyEq (modeTerm_eventuallyEq_zero hμ hs')

/-- On the open interval `(0, 1)` the cut-off mode is the mode solution near every point. -/
theorem modeTerm_eventuallyEq {μ : ℝ} {F : ℝ → ℝ} {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    modeTerm μ F =ᶠ[𝓝 s] modeSolution μ F := by
  filter_upwards [isOpen_Ioo.mem_nhds hs] with y hy
  rw [modeTerm, modeCutoff_of_mem (Ioo_subset_Icc_self hy), one_mul]

/-- The cut-off mode solution vanishes at the wall `s = 1`. -/
theorem modeTerm_one (μ : ℝ) (F : ℝ → ℝ) : modeTerm μ F 1 = 0 := by
  rw [modeTerm, modeSolution_one, mul_zero]

/-- **Derivative bounds for the cut-off modes.** With bounds `M j` for the derivatives of `F` on
the collar, every iterated derivative of the cut-off mode is bounded on the whole line by
`3 Dⱼ (1 + μ²)^j (∑_{l ≤ j} M l) / μ²`, where `Dⱼ` depends only on the cutoff. -/
theorem exists_abs_iteratedDeriv_modeTerm_le :
    ∃ D : ℕ → ℝ, (∀ j, 0 ≤ D j) ∧
      ∀ {μ : ℝ} (_ : 0 < μ) {F : ℝ → ℝ} (_ : ContDiff ℝ (⊤ : ℕ∞) F) (j : ℕ) (M : ℕ → ℝ)
        (_ : ∀ i ≤ j, ∀ s ∈ Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2), |iteratedDeriv i F s| ≤ M i)
        (s : ℝ),
        |iteratedDeriv j (modeTerm μ F) s| ≤
          3 * D j * (1 + μ ^ 2) ^ j * (∑ l ∈ Finset.range (j + 1), M l) / μ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_iteratedDeriv_modeCutoff_le
  refine ⟨fun j ↦ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * C i,
    fun j ↦ Finset.sum_nonneg fun i _ ↦ mul_nonneg (by positivity) (hC0 i), ?_⟩
  intro μ hμ F hF j M hM s
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hM0 : ∀ i ≤ j, 0 ≤ M i := fun i hi ↦ (abs_nonneg _).trans
    (hM i hi 0 ⟨div_nonpos_of_nonpos_of_nonneg (by norm_num) hμ2.le, by positivity⟩)
  have hsum0 : 0 ≤ ∑ l ∈ Finset.range (j + 1), M l :=
    Finset.sum_nonneg fun l hl ↦ hM0 l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))
  by_cases hs : s ∈ Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2)
  · have hΨ := (contDiffOn_modeSolution hμ hF).contDiffAt
      (isOpen_Ioi.mem_nhds (modeInterval_subset hμ hs))
    change |iteratedDeriv j (fun x ↦ modeCutoff μ x * modeSolution μ F x) s| ≤ _
    rw [iteratedDeriv_fun_mul
      ((contDiff_modeCutoff μ).contDiffAt.of_le (by exact_mod_cast le_top))
      (hΨ.of_le (by exact_mod_cast le_top))]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_div_assoc, mul_assoc, mul_assoc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hsub : ∑ l ∈ Finset.range (j - i + 1), M l ≤ ∑ l ∈ Finset.range (j + 1), M l :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
        (fun l hl _ ↦ hM0 l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)))
    have hΨb : |iteratedDeriv (j - i) (modeSolution μ F) s| ≤
        3 * (1 + μ ^ 2) ^ (j - i) * (∑ l ∈ Finset.range (j + 1), M l) / μ ^ 2 :=
      (abs_iteratedDeriv_modeSolution_le hμ hF (j - i) M
        (fun l hl s hs ↦ hM l (hl.trans (Nat.sub_le j i)) s hs) hs).trans (by gcongr)
    have hpow : (μ ^ 2) ^ i * (1 + μ ^ 2) ^ (j - i) ≤ (1 + μ ^ 2) ^ j :=
      calc _ ≤ (1 + μ ^ 2) ^ i * (1 + μ ^ 2) ^ (j - i) := by gcongr; linarith
        _ = _ := by rw [← pow_add, Nat.add_sub_cancel' hij]
    have hCi := hC μ i s
    have hX : 0 ≤ C i * (μ ^ 2) ^ i := mul_nonneg (hC0 i) (by positivity)
    have hCi0 : 0 ≤ (j.choose i : ℝ) * C i := mul_nonneg (by positivity) (hC0 i)
    have h3 : 0 ≤ (∑ l ∈ Finset.range (j + 1), M l) / μ ^ 2 := div_nonneg hsum0 hμ2.le
    rw [abs_mul, abs_mul, Nat.abs_cast, mul_assoc]
    calc _ ≤ (j.choose i : ℝ) * (C i * (μ ^ 2) ^ i *
          (3 * (1 + μ ^ 2) ^ (j - i) * (∑ l ∈ Finset.range (j + 1), M l) / μ ^ 2)) := by
          gcongr
      _ = 3 * ((j.choose i : ℝ) * C i * (((μ ^ 2) ^ i * (1 + μ ^ 2) ^ (j - i)) *
            ((∑ l ∈ Finset.range (j + 1), M l) / μ ^ 2))) := by ring
      _ ≤ _ := by gcongr
  · rw [(modeTerm_eventuallyEq_zero hμ hs).iteratedDeriv_eq, iteratedDeriv_const, ite_self,
      abs_zero]
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun i _ ↦ mul_nonneg (by positivity) (hC0 i))) (by positivity))
      hsum0) hμ2.le

/-! ### Planar sine terms -/

/-- The planar term `a(s) sin(μ z)` at the point `p = (s, z)`. -/
def sineTerm (a : ℝ → ℝ) (μ : ℝ) (p : ℝ^2) : ℝ :=
  a (p 0) * Real.sin (μ * p 1)

/-- A smooth function of one coordinate of the plane. -/
theorem contDiff_comp_coord {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ^2 ↦ f (p i)) :=
  hf.comp (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).contDiff

/-- The planar sine term of a smooth function is smooth. -/
theorem contDiff_sineTerm {a : ℝ → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (μ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (sineTerm a μ) :=
  (contDiff_comp_coord ha 0).mul
    (contDiff_comp_coord (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)) 1)

/-- The iterated derivatives of `z ↦ sin(μ z)` are bounded by `|μ|^j`. -/
theorem abs_iteratedDeriv_sin_mul_le (μ : ℝ) (j : ℕ) (z : ℝ) :
    |iteratedDeriv j (fun z ↦ Real.sin (μ * z)) z| ≤ |μ| ^ j := by
  rw [iteratedDeriv_comp_const_mul (Real.contDiff_sin.of_le (by exact_mod_cast le_top)) μ]
  simp only
  rw [abs_mul, abs_pow]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_iteratedDeriv_sin_le_one j _)

/-- The iterated derivatives of a function of one coordinate of the plane are bounded by those
of the function. -/
theorem norm_iteratedFDeriv_comp_coord_le {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2)
    (n : ℕ) (p : ℝ^2) :
    ‖iteratedFDeriv ℝ n (fun p : ℝ^2 ↦ f (p i)) p‖ ≤ |iteratedDeriv n f (p i)| := by
  have h := (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).iteratedFDeriv_comp_right (f := f) hf p
    (i := n) (by exact_mod_cast le_top)
  change ‖iteratedFDeriv ℝ n (f ∘ (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ)) p‖ ≤ _
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  refine mul_le_of_le_one_right (abs_nonneg _) ?_
  rw [Finset.prod_const]
  exact pow_le_one₀ (norm_nonneg _) (PiLp.norm_proj_le i)

/-- **Bounds for planar sine terms.** The `n`-th derivative of `a(s) sin(μ z)` is bounded by
`∑ (n choose i) |a^{(i)}(s)| |μ|^{n-i}`. -/
theorem norm_iteratedFDeriv_sineTerm_le {a : ℝ → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (μ : ℝ)
    (n : ℕ) (p : ℝ^2) :
    ‖iteratedFDeriv ℝ n (sineTerm a μ) p‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |iteratedDeriv i a (p 0)| *
        |μ| ^ (n - i) := by
  have hsin : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ Real.sin (μ * z)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  have h := norm_iteratedFDeriv_mul_le (contDiff_comp_coord ha 0) (contDiff_comp_coord hsin 1) p
    (n := n) (by exact_mod_cast le_top)
  refine h.trans (Finset.sum_le_sum fun i _ ↦ ?_)
  gcongr
  · exact norm_iteratedFDeriv_comp_coord_le ha 0 i p
  · exact (norm_iteratedFDeriv_comp_coord_le hsin 1 (n - i) p).trans
      (abs_iteratedDeriv_sin_mul_le μ _ _)

/-! ### The stream modes -/

/-- The frequency `2π (k + 1) / L` of the `(k + 1)`-th sine mode of period `L`. -/
def modeFrequency (L : ℝ) (k : ℕ) : ℝ :=
  2 * Real.pi * (k + 1) / L

/-- The `(k + 1)`-th sine coefficient of `Ω(s, ·)` as a function of `s`. -/
def coefficientMode (L : ℝ) (Ω : ℝ × ℝ → ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  PDE.Analysis.Fourier.SineSeries.sineCoeff L (fun z ↦ Ω (s, z)) (k + 1)

/-- The `(k + 1)`-th stream mode `η_μ(s) Ψ_μ(s) sin(μ z)`, `μ = 2π (k + 1) / L`, where `Ψ_μ` is
the mode solution with the `(k + 1)`-th sine coefficient of `Ω` as source. -/
def streamMode (L : ℝ) (Ω : ℝ × ℝ → ℝ) (k : ℕ) : ℝ^2 → ℝ :=
  sineTerm (modeTerm (modeFrequency L k) (coefficientMode L Ω k)) (modeFrequency L k)

/-- The mode frequencies are positive. -/
theorem modeFrequency_pos {L : ℝ} (hL : 0 < L) (k : ℕ) : 0 < modeFrequency L k := by
  unfold modeFrequency
  positivity

/-- The coefficient modes are smooth. -/
theorem contDiff_coefficientMode {L : ℝ} {Ω : ℝ × ℝ → ℝ} (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (coefficientMode L Ω k) :=
  PDE.Analysis.Fourier.SineSeries.contDiff_sineCoeff_param hΩ (k + 1)

/-- The stream modes are smooth. -/
theorem contDiff_streamMode {L : ℝ} (hL : 0 < L) {Ω : ℝ × ℝ → ℝ}
    (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω) (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (streamMode L Ω k) :=
  contDiff_sineTerm (contDiff_modeTerm (modeFrequency_pos hL k)
    (contDiff_coefficientMode hΩ k)) _

/-- **Decay of the stream modes.** For a smooth source `Ω`, `L`-periodic in `z`, every iterated
derivative of the `(k + 1)`-th stream mode is bounded by `D / (1 + k)²` uniformly on the
plane. -/
theorem exists_norm_iteratedFDeriv_streamMode_le {L : ℝ} (hL : 0 < L) {Ω : ℝ × ℝ → ℝ}
    (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω) (hper : ∀ s z, Ω (s, z + L) = Ω (s, z)) (n : ℕ) :
    ∃ D, ∀ k : ℕ, ∀ p : ℝ^2, ‖iteratedFDeriv ℝ n (streamMode L Ω k) p‖ ≤ D / (1 + k) ^ 2 := by
  obtain ⟨Dη, hDη0, hDη⟩ := exists_abs_iteratedDeriv_modeTerm_le
  set c : ℝ := 2 * Real.pi / L
  have hc : 0 < c := by positivity
  set K : Set ℝ := Icc (-2 / c ^ 2) (1 + 2 / c ^ 2)
  have hμ (k : ℕ) : modeFrequency L k = c * (1 + k) := by
    simp only [modeFrequency, c]
    ring
  have hμc (k : ℕ) : c ≤ modeFrequency L k := by
    rw [hμ k]
    exact le_mul_of_one_le_right hc.le (by simp)
  have hcollar (k : ℕ) :
      Icc (-2 / modeFrequency L k ^ 2) (1 + 2 / modeFrequency L k ^ 2) ⊆ K := by
    have hle : 2 / modeFrequency L k ^ 2 ≤ 2 / c ^ 2 := by gcongr; exact hμc k
    exact Icc_subset_Icc (by rw [neg_div, neg_div]; linarith) (by linarith)
  -- Decay of the coefficients and their derivatives on `K`.
  set N : ℕ := 2 * n + 2
  have hcoef (i : ℕ) : ∃ C, 0 ≤ C ∧ ∀ k : ℕ, ∀ s ∈ K,
      |iteratedDeriv i (coefficientMode L Ω k) s| ≤ C / (1 + k) ^ N := by
    obtain ⟨C, hC⟩ := PDE.Analysis.Fourier.SineSeries.exists_abs_iteratedDeriv_sineCoeff_le hL
      hΩ hper i N (isCompact_Icc (a := -2 / c ^ 2) (b := 1 + 2 / c ^ 2))
    have hC0 : 0 ≤ C := by
      simpa using (abs_nonneg _).trans
        (hC 0 0 ⟨div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity), by positivity⟩)
    exact ⟨C, hC0, fun k s hs ↦ (hC (k + 1) s hs).trans (by gcongr; linarith)⟩
  choose C hC0 hC using hcoef
  set SC : ℝ := ∑ l ∈ Finset.range (n + 1), C l
  have hSC0 : 0 ≤ SC := Finset.sum_nonneg fun l _ ↦ hC0 l
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (3 * Dη i * SC / c ^ 2) *
    (1 + c) ^ (2 * n), fun k p ↦ ?_⟩
  set μ := modeFrequency L k
  have hμpos : 0 < μ := modeFrequency_pos hL k
  set B : ℝ := (1 + c) ^ 2 * (1 + k) ^ 2 with hBdef
  have hk1 : 1 ≤ (1 + (k : ℝ)) := by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hμk : μ = c * (1 + k) := hμ k
  have hμB : |μ| ≤ B := by
    have h1 : 1 ≤ (1 + c) * (1 + k) := one_le_mul_of_one_le_of_one_le (by linarith) hk1
    rw [abs_of_pos hμpos, hμk, hBdef, ← mul_pow]
    nlinarith
  have h1μB : 1 + μ ^ 2 ≤ B := by
    rw [hμk]
    have : 1 ≤ (1 + 2 * c) * (1 + k) ^ 2 := one_le_mul_of_one_le_of_one_le (by linarith)
      (one_le_pow₀ hk1)
    nlinarith
  have hμ2c : c ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ hc.le (hμc k) 2
  have hterm : ∀ i ≤ n, |iteratedDeriv i (modeTerm μ (coefficientMode L Ω k)) (p 0)| ≤
      3 * Dη i * B ^ i * SC / (c ^ 2 * (1 + k) ^ N) := by
    intro i hi
    have h3 : 0 ≤ 3 * Dη i := by linarith [hDη0 i]
    have hsum0 : 0 ≤ ∑ l ∈ Finset.range (i + 1), C l / (1 + (k : ℝ)) ^ N :=
      Finset.sum_nonneg fun l _ ↦ div_nonneg (hC0 l) (by positivity)
    have hsum : ∑ l ∈ Finset.range (i + 1), C l / (1 + (k : ℝ)) ^ N ≤ SC / (1 + k) ^ N := by
      rw [← Finset.sum_div]
      gcongr
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
        fun l _ _ ↦ hC0 l
    calc _ ≤ 3 * Dη i * (1 + μ ^ 2) ^ i *
          (∑ l ∈ Finset.range (i + 1), C l / (1 + (k : ℝ)) ^ N) / μ ^ 2 :=
          hDη hμpos (contDiff_coefficientMode hΩ k) i (fun l ↦ C l / (1 + k) ^ N)
            (fun l hl s hs ↦ hC l k s (hcollar k hs)) (p 0)
      _ ≤ 3 * Dη i * B ^ i * (SC / (1 + k) ^ N) / c ^ 2 := by gcongr
      _ = _ := by field_simp
  refine (norm_iteratedFDeriv_sineTerm_le
    (contDiff_modeTerm hμpos (contDiff_coefficientMode (L := L) hΩ k)) μ n p).trans ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hX : 0 ≤ 3 * Dη i * B ^ i * SC / (c ^ 2 * (1 + k) ^ N) :=
    (abs_nonneg _).trans (hterm i hin)
  have hBpow : B ^ i * B ^ (n - i) = (1 + c) ^ (2 * n) * (1 + k) ^ (2 * n) := by
    rw [← pow_add, Nat.add_sub_cancel' hin, hBdef, mul_pow, ← pow_mul, ← pow_mul]
  rw [mul_assoc]
  calc _ ≤ (n.choose i : ℝ) * (3 * Dη i * B ^ i * SC / (c ^ 2 * (1 + k) ^ N) * B ^ (n - i)) := by
        gcongr
        exact hterm i hin
    _ = (n.choose i : ℝ) * (3 * Dη i * SC / c ^ 2) * (B ^ i * B ^ (n - i)) / (1 + k) ^ N := by
        field_simp
    _ = _ := by
        rw [hBpow, show N = 2 * n + 2 from rfl, pow_add]
        field_simp

end

end Euler.Cylinder
