/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Lp.Translation
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Bounded convolution and coefficient multiplication on L²

Translation is an isometry on `L²(ℝ^n; E)`, and each translated vector depends continuously
on the displacement. Integrating this orbit against a signed integrable kernel constructs
`convolutionL2CLM`, with operator norm at most the kernel's `L¹` norm. The integral is taken
in `L²`. For real scalar inputs, `convolutionL2CLM_ae_eq` identifies its representative
with the usual scalar convolution almost everywhere. The defining integral exists almost
everywhere, and convolution preserves `L²` at the level of functions,
not only classes.

`multiplicationL2CLM` applies an `L∞` field of bounded operators to an `L²` vector field.
It is Mathlib's bounded bilinear Hölder map with exponents `∞`, `2`, `2`, for arbitrary
normed source and target spaces over the same scalar field.

Bounded postcomposition commutes with translation and convolution. On real Hilbert-valued
`L²`, the adjoint of convolution reflects the kernel; even kernels give symmetric operators.

The convolution construction works for functions with values in any real Banach space.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Convolution ENNReal Topology

namespace PDE.Analysis

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An integrable scalar kernel times an `L²` translation orbit is Bochner integrable. -/
theorem integrable_smul_translateL2 {k : ℝ^n → ℝ} (hk : Integrable k volume)
    (u : Lp E 2 (volume : Measure (ℝ^n))) :
    Integrable (fun y ↦ k y • translateL2 ℝ y u) volume := by
  let : SecondCountableTopologyEither (ℝ^n) (Lp E 2 (volume : Measure (ℝ^n))) :=
    ⟨Or.inl inferInstance⟩
  exact (ContinuousLinearMap.lsmul ℝ ℝ :
    ℝ →L[ℝ] Lp E 2 (volume : Measure (ℝ^n)) →L[ℝ]
      Lp E 2 (volume : Measure (ℝ^n))).integrable_of_bilin_of_bdd_right ‖u‖ hk
        (continuous_translateL2 ℝ u).aestronglyMeasurable
        (.of_forall fun y ↦ (norm_translateL2 ℝ y u).le)

/-- Integrating translations gives the `L¹`-kernel bound for convolution on `L²`. -/
theorem norm_integral_smul_translateL2_le (k : ℝ^n → ℝ)
    (u : Lp E 2 (volume : Measure (ℝ^n))) :
    ‖∫ y, k y • translateL2 ℝ y u‖ ≤ (∫ y, ‖k y‖) * ‖u‖ := by
  calc
    ‖∫ y, k y • translateL2 ℝ y u‖ ≤ ∫ y, ‖k y • translateL2 ℝ y u‖ :=
      norm_integral_le_integral_norm _
    _ = (∫ y, ‖k y‖) * ‖u‖ := by
      simp only [norm_smul, norm_translateL2]
      exact integral_mul_const ‖u‖ (fun y ↦ ‖k y‖)

variable [CompleteSpace E]

/-- Convolution by a signed integrable kernel as a bounded operator on `L²`.

The integral is taken in `L²` after translation is applied to the input. The translation
orbit of the input is continuous in `L²`, although translation is not continuous in operator
norm. -/
def convolutionL2CLM (k : ℝ^n → ℝ) (hk : Integrable k volume) :
    Lp E 2 (volume : Measure (ℝ^n)) →L[ℝ] Lp E 2 (volume : Measure (ℝ^n)) :=
  LinearMap.mkContinuous
    { toFun := fun u ↦ ∫ y, k y • translateL2 ℝ y u
      map_add' := by
        intro u v
        simp only [map_add, smul_add]
        exact integral_add (integrable_smul_translateL2 hk u)
          (integrable_smul_translateL2 hk v)
      map_smul' := by
        intro c u
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        apply integral_congr_ae
        exact .of_forall fun y ↦ smul_comm (k y) c (translateL2 ℝ y u) }
    (∫ y, ‖k y‖) (norm_integral_smul_translateL2_le k)

omit [CompleteSpace E] in
/-- The bounded convolution operator is the integral of its translated input. -/
theorem convolutionL2CLM_apply (k : ℝ^n → ℝ) (hk : Integrable k volume)
    (u : Lp E 2 (volume : Measure (ℝ^n))) :
    convolutionL2CLM k hk u = ∫ y, k y • translateL2 ℝ y u :=
  rfl

omit [CompleteSpace E] in
/-- Convolution on `L²` has operator norm at most the `L¹` norm of its scalar kernel. -/
theorem norm_convolutionL2CLM_le (k : ℝ^n → ℝ) (hk : Integrable k volume) :
    ‖convolutionL2CLM (E := E) k hk‖ ≤ ∫ y, ‖k y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun y ↦ norm_nonneg (k y))
  exact norm_integral_smul_translateL2_le k

omit [CompleteSpace E] in
/-- The operator integral is Mathlib convolution at zero with the `L²` translation orbit.

This identity concerns the `L²`-valued orbit, not a pointwise representative of the
output. -/
theorem convolutionL2CLM_eq_convolution_orbit (k : ℝ^n → ℝ)
    (hk : Integrable k volume) (u : Lp E 2 (volume : Measure (ℝ^n))) :
    convolutionL2CLM k hk u =
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
        (fun y : ℝ^n ↦ translateL2 ℝ (-y) u)) 0 := by
  simp only [convolutionL2CLM_apply, convolution_lsmul, zero_sub, neg_neg]

end PDE.Analysis

namespace PDE.Analysis

variable {n : ℕ} {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Multiplication by an essentially bounded operator field between normed spaces,
bundled through Hölder's inequality with exponents `∞`, `2`, `2`. -/
def multiplicationL2CLM :
    Lp (E →L[𝕜] F) ∞ (volume : Measure (ℝ^n)) →L[𝕜]
      Lp E 2 (volume : Measure (ℝ^n)) →L[𝕜] Lp F 2 (volume : Measure (ℝ^n)) :=
  (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).holderL volume ∞ 2 2

/-- The multiplication operator applies the coefficient field pointwise almost everywhere. -/
theorem multiplicationL2CLM_ae_eq
    (B : Lp (E →L[𝕜] F) ∞ (volume : Measure (ℝ^n)))
    (u : Lp E 2 (volume : Measure (ℝ^n))) :
    multiplicationL2CLM B u =ᵐ[volume] fun x ↦ B x (u x) :=
  (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).coeFn_holder B u

/-- Multiplication is bounded by the essential supremum of the coefficient norm. -/
theorem norm_multiplicationL2CLM_apply_le
    (B : Lp (E →L[𝕜] F) ∞ (volume : Measure (ℝ^n)))
    (u : Lp E 2 (volume : Measure (ℝ^n))) :
    ‖multiplicationL2CLM B u‖ ≤ ‖B‖ * ‖u‖ := by
  change ‖(ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).holder 2 B u‖ ≤ _
  calc
    _ ≤ ‖ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)‖ * ‖B‖ * ‖u‖ :=
      (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).norm_holder_apply_apply_le B u
    _ = ‖ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)‖ * (‖B‖ * ‖u‖) := mul_assoc _ _ _
    _ ≤ 1 * (‖B‖ * ‖u‖) := mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖B‖ * ‖u‖ := one_mul _

/-- The operator norm of multiplication is at most the L∞ coefficient norm. -/
theorem norm_multiplicationL2CLM_le
    (B : Lp (E →L[𝕜] F) ∞ (volume : Measure (ℝ^n))) :
    ‖multiplicationL2CLM B‖ ≤ ‖B‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
    (norm_multiplicationL2CLM_apply_le B)

end PDE.Analysis

namespace PDE.Analysis

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [CompleteSpace E]

/-- Moving scalar convolution across the real `L²` inner product reflects its kernel. -/
theorem inner_convolutionL2CLM_left (k : ℝ^n → ℝ) (hk : Integrable k volume)
    (u v : Lp E 2 (volume : Measure (ℝ^n))) :
    inner ℝ (convolutionL2CLM k hk u) v =
      inner ℝ u (convolutionL2CLM (fun y ↦ k (-y)) hk.comp_neg v) := by
  calc
    inner ℝ (convolutionL2CLM k hk u) v =
        ∫ y, k y * inner ℝ (translateL2 ℝ y u) v := by
      rw [real_inner_comm, convolutionL2CLM_apply,
        ← integral_inner (integrable_smul_translateL2 hk u)]
      simp only [real_inner_smul_right, real_inner_comm]
    _ = ∫ y, k y * inner ℝ u (translateL2 ℝ (-y) v) := by
      simp only [inner_translateL2_left]
    _ = ∫ y, k (-y) * inner ℝ u (translateL2 ℝ y v) := by
      simpa only [neg_neg] using
        (integral_neg_eq_self
          (fun y ↦ k y * inner ℝ u (translateL2 ℝ (-y) v)) volume).symm
    _ = inner ℝ u (convolutionL2CLM (fun y ↦ k (-y)) hk.comp_neg v) := by
      rw [convolutionL2CLM_apply, ← integral_inner
        (integrable_smul_translateL2 hk.comp_neg v)]
      simp only [real_inner_smul_right]

/-- Convolution by an even integrable real kernel is symmetric on `L²`. -/
theorem inner_convolutionL2CLM_eq_of_even (k : ℝ^n → ℝ)
    (hk : Integrable k volume) (heven : Function.Even k)
    (u v : Lp E 2 (volume : Measure (ℝ^n))) :
    inner ℝ (convolutionL2CLM k hk u) v = inner ℝ u (convolutionL2CLM k hk v) := by
  simpa only [show (fun y ↦ k (-y)) = k from funext heven] using
    inner_convolutionL2CLM_left k hk u v

end PDE.Analysis

namespace PDE.Analysis

variable {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Bounded postcomposition commutes with convolution by an integrable scalar kernel.
The proof moves the bounded map through the L2-valued Bochner integral. -/
theorem compLp_convolutionL2CLM [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℝ] F) (k : ℝ^n → ℝ) (hk : Integrable k volume)
    (u : Lp E 2 (volume : Measure (ℝ^n))) :
    L.compLp (convolutionL2CLM k hk u) = convolutionL2CLM k hk (L.compLp u) := by
  change (L.compLpL 2 volume) (convolutionL2CLM k hk u) = _
  rw [convolutionL2CLM_apply, convolutionL2CLM_apply,
    ← (L.compLpL 2 volume).integral_comp_comm (integrable_smul_translateL2 hk u)]
  apply integral_congr_ae
  filter_upwards with y
  change (L.compLpL 2 volume) (k y • translateL2 ℝ y u) = _
  rw [map_smul]
  exact congrArg (fun w ↦ k y • w) (compLp_translateL2 ℝ L y u)

end PDE.Analysis

namespace PDE.Analysis

section ScalarRepresentative

variable {n : ℕ}

/-- On a set of finite measure, the translated input has a uniform `L¹` bound.
The proof uses the elementary bound `|a| ≤ 1 + a²`. -/
private theorem integral_norm_translate_le (u : Lp ℝ 2 (volume : Measure (ℝ^n)))
    {s : Set (ℝ^n)} (hμs : volume s ≠ ∞) (y : ℝ^n) :
    ∫ x in s, ‖u (x - y)‖ ≤ volume.real s + ∫ x, (u x) ^ 2 := by
  have hu : IntegrableOn (fun x ↦ u (x - y)) s volume :=
    (integrableOn_Lp_of_measure_ne_top (translateL2 ℝ y u)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hμs).congr
        (ae_restrict_of_ae (translateL2_ae_eq ℝ y u))
  have hu2 : Integrable (fun x ↦ (u (x - y)) ^ 2) volume :=
    (Lp.memLp u).integrable_sq.comp_sub_right y
  have h1 : IntegrableOn (fun _ : ℝ^n ↦ (1 : ℝ)) s volume :=
    integrableOn_const hμs
  calc
    ∫ x in s, ‖u (x - y)‖ ≤ ∫ x in s, (1 + (u (x - y)) ^ 2) := by
      apply integral_mono_ae hu.norm (h1.add hu2.integrableOn)
      filter_upwards with x
      rw [Real.norm_eq_abs]
      change |u (x - y)| ≤ 1 + (u (x - y)) ^ 2
      exact abs_le.mpr
        ⟨by nlinarith [sq_nonneg (u (x - y) + 1)],
          by nlinarith [sq_nonneg (u (x - y) - 1)]⟩
    _ = volume.real s + ∫ x in s, (u (x - y)) ^ 2 := by
      rw [integral_add h1 hu2.integrableOn]
      simp only [setIntegral_const, smul_eq_mul, mul_one]
    _ ≤ volume.real s + ∫ x, (u (x - y)) ^ 2 :=
      add_le_add (le_refl _) (setIntegral_le_integral hu2
        (.of_forall fun x ↦ sq_nonneg (u (x - y))))
    _ = volume.real s + ∫ x, (u x) ^ 2 :=
      congrArg (volume.real s + ·) (integral_sub_right_eq_self (fun x ↦ (u x) ^ 2) y)

/-- Fubini applies to the scalar convolution integrand when its output variable is
restricted to a set of finite measure. The input itself need not be integrable on all space. -/
private theorem integrable_convolution_integrand_restrict {k : ℝ^n → ℝ}
    (hk : Integrable k volume) (u : Lp ℝ 2 (volume : Measure (ℝ^n)))
    {s : Set (ℝ^n)} (hμs : volume s ≠ ∞) :
    Integrable (fun z : (ℝ^n) × (ℝ^n) ↦ k z.1 * u (z.2 - z.1))
      (volume.prod (volume.restrict s)) := by
  have hm : AEStronglyMeasurable
      (fun z : (ℝ^n) × (ℝ^n) ↦ k z.1 * u (z.2 - z.1))
      (volume.prod (volume.restrict s)) :=
    hk.aestronglyMeasurable.comp_fst.mul
      ((Lp.stronglyMeasurable u).comp_measurable
        (measurable_snd.sub measurable_fst)).aestronglyMeasurable
  refine (integrable_prod_iff hm).2 ⟨?_, ?_⟩
  · filter_upwards with y
    exact ((integrableOn_Lp_of_measure_ne_top (translateL2 ℝ y u)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hμs).congr
        (ae_restrict_of_ae (translateL2_ae_eq ℝ y u))).const_mul (k y)
  · refine (hk.norm.mul_const (volume.real s + ∫ x, (u x) ^ 2)).mono'
      hm.norm.integral_prod_right' ?_
    filter_upwards with y
    rw [Real.norm_of_nonneg (integral_nonneg fun x ↦ norm_nonneg _)]
    simp_rw [norm_mul]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_norm_translate_le u hμs y) (norm_nonneg _)

/-- An `L¹` kernel and an `L²` input have an absolutely integrable convolution integrand
at almost every output point. Exhausting space by finite-measure sets allows Fubini to
apply without assuming that the input belongs to `L¹`. -/
theorem ae_convolutionExistsAt_of_integrable_memLp_two {k f : ℝ^n → ℝ}
    (hk : Integrable k volume) (hf : MemLp f 2 volume) :
    ∀ᵐ x ∂volume, ConvolutionExistsAt k f x (ContinuousLinearMap.lsmul ℝ ℝ) := by
  let u := hf.toLp f
  have hlocal (j : ℕ) : ∀ᵐ x ∂volume,
      x ∈ spanningSets (volume : Measure (ℝ^n)) j →
        Integrable (fun y ↦ k y * u (x - y)) volume := by
    apply (ae_restrict_iff' (measurableSet_spanningSets volume j)).mp
    exact (integrable_convolution_integrand_restrict hk u
      (measure_spanningSets_lt_top volume j).ne).prod_left_ae
  have hglobal : ∀ᵐ x ∂volume, Integrable (fun y ↦ k y * u (x - y)) volume := by
    filter_upwards [ae_all_iff.2 hlocal] with x hx
    exact hx _ (mem_spanningSetsIndex volume x)
  filter_upwards [hglobal] with x hx
  change Integrable (fun y ↦ k y * f (x - y)) volume
  apply hx.congr
  have heq := hf.coeFn_toLp.comp_tendsto
    (quasiMeasurePreserving_sub_left_of_right_invariant volume x).tendsto_ae
  filter_upwards [heq] with y hy
  exact congrArg (k y * ·) hy

/-- The `L²` convolution operator is represented almost everywhere by the scalar convolution.

Finite-set integrals are bounded functionals on `L²`. Commuting these functionals with the
Bochner integral and applying Fubini identifies the representative, without point evaluation
on `L²` equivalence classes. -/
theorem convolutionL2CLM_ae_eq (k : ℝ^n → ℝ) (hk : Integrable k volume)
    (u : Lp ℝ 2 (volume : Measure (ℝ^n))) :
    convolutionL2CLM k hk u =ᵐ[volume] (k ⋆ (u : ℝ^n → ℝ)) := by
  change (fun x ↦ convolutionL2CLM k hk u x) =ᵐ[volume]
    (fun x ↦ ∫ y, k y * u (x - y))
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s _ hμs
    exact integrableOn_Lp_of_measure_ne_top _ (by norm_num : (1 : ℝ≥0∞) ≤ 2) hμs.ne
  · intro s _ hμs
    exact (integrable_convolution_integrand_restrict hk u hμs.ne).integral_prod_right
  · intro s hs hμs
    calc
      ∫ x in s, convolutionL2CLM k hk u x =
          inner ℝ (indicatorConstLp 2 hs hμs.ne (1 : ℝ)) (convolutionL2CLM k hk u) :=
        (L2.inner_indicatorConstLp_one hs hμs.ne _).symm
      _ = ∫ y, inner ℝ (indicatorConstLp 2 hs hμs.ne (1 : ℝ))
          (k y • translateL2 ℝ y u) := by
        rw [convolutionL2CLM_apply, ← integral_inner (integrable_smul_translateL2 hk u)]
      _ = ∫ y, ∫ x in s, k y * u (x - y) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [real_inner_smul_right, L2.inner_indicatorConstLp_one, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (translateL2_ae_eq ℝ y u)] with x hx
        exact congrArg (k y * ·) hx
      _ = ∫ x in s, ∫ y, k y * u (x - y) :=
        integral_integral_swap (integrable_convolution_integrand_restrict hk u hμs.ne)

/-- Scalar convolution by an integrable kernel preserves `L²` at the level of functions. -/
theorem memLp_convolution_two {k f : ℝ^n → ℝ}
    (hk : Integrable k volume) (hf : MemLp f 2 volume) :
    MemLp (k ⋆ f) 2 volume := by
  have heq : convolutionL2CLM k hk (hf.toLp f) =ᵐ[volume] (k ⋆ f) := by
    calc
      convolutionL2CLM k hk (hf.toLp f) =ᵐ[volume]
          (k ⋆ (hf.toLp f : ℝ^n → ℝ)) := convolutionL2CLM_ae_eq k hk _
      _ = (k ⋆ f) := convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ)
        Filter.EventuallyEq.rfl hf.coeFn_toLp
  exact (Lp.memLp (convolutionL2CLM k hk (hf.toLp f))).ae_eq heq

end ScalarRepresentative

end PDE.Analysis
