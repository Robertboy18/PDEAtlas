/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension
public import PDE.Analysis.Calculus.Radial.Lift.C1
public import PDE.Analysis.Integration.ParametricIntervalSmooth.Local
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Finite regularity of even radial lifts

An even profile of class `C^(2k)` has a radial lift of class `C^k`, including on
the axis. The proof writes the radial derivative as `r` times the average of
the second radial derivative. That average is even and loses two derivatives.
Induction applies to this average and to the derivative in the external parameter.

The fixed interval average preserves its available regularity for any real normed
parameter space. The codomain may be any real Banach space, allowing the induction
to include the operator-valued parameter derivative.

When both the radial and parameter spaces are finite dimensional, a sharp `C²` base case
improves the induction to even `C^(2k+2)` input giving a `C^(k+2)` lift.
In particular, even `C⁶` gives `C⁴`. The axis proof uses the zero trace
of the first radial derivative to cancel the direction-dependent terms,
including mixed derivatives in the external parameter.

The local versions need regularity only at the corresponding meridian point.
At the axis, an even extension of the profile's germ reduces it to the global result.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Filter MeasureTheory
open scoped Topology

universe u v w

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type (max u v)} [NormedAddCommGroup G] [NormedSpace ℝ G]

private def radialDerivative (f : ℝ × F → G) (p : ℝ × F) : G :=
  fderiv ℝ f p (1, 0)

private def parameterDerivative (f : ℝ × F → G) (p : ℝ × F) : F →L[ℝ] G :=
  (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ ℝ F)

private theorem fderiv_reflection
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : H × F → G} (hf : Differentiable ℝ f) (c : ℝ)
    (heven : ∀ r z, f (-r, z) = c • f (r, z)) (r : H) (z : F) (a : H) (b : F) :
    fderiv ℝ f (-r, z) (-a, b) = c • fderiv ℝ f (r, z) (a, b) := by
  let R : H × F →L[ℝ] H × F :=
    (-(ContinuousLinearMap.fst ℝ H F)).prod (ContinuousLinearMap.snd ℝ H F)
  have hcomp := (hf (-r, z)).hasFDerivAt.comp (r, z) (R.hasFDerivAt)
  have hsame : (fun p : H × F ↦ f (R p)) = fun p ↦ c • f p := by
    funext p
    exact heven p.1 p.2
  change HasFDerivAt (fun p ↦ f (R p)) _ _ at hcomp
  rw [hsame] at hcomp
  have heq := hcomp.unique ((hf (r, z)).hasFDerivAt.const_smul c)
  exact congrArg (fun L : H × F →L[ℝ] G ↦ L (a, b)) heq

private theorem radialDerivative_odd
    {f : ℝ × F → G} (hf : Differentiable ℝ f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) (r : ℝ) (z : F) :
    radialDerivative f (-r, z) = -radialDerivative f (r, z) := by
  have h := fderiv_reflection hf 1 (by
    intro r z
    rw [one_smul]
    exact heven r z) r z (-1) 0
  have hp : ((-1 : ℝ), (0 : F)) = -((1, 0) : ℝ × F) := by simp
  rw [hp, map_neg] at h
  simpa [radialDerivative] using h

private theorem radialDerivative_zero
    {f : ℝ × F → G} (hf : Differentiable ℝ f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) (z : F) :
    radialDerivative f (0, z) = 0 := by
  have h := radialDerivative_odd hf heven 0 z
  simp only [neg_zero] at h
  have hsum : (2 : ℝ) • radialDerivative f (0, z) = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr h
  exact (smul_eq_zero.mp hsum).resolve_left (by norm_num)

private theorem parameterDerivative_even
    {f : ℝ × F → G} (hf : Differentiable ℝ f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) (r : ℝ) (z : F) :
    parameterDerivative f (-r, z) = parameterDerivative f (r, z) := by
  ext b
  change fderiv ℝ f (-r, z) (0, b) = fderiv ℝ f (r, z) (0, b)
  have h := fderiv_reflection hf 1 (by
    intro r z
    rw [one_smul]
    exact heven r z) r z 0 b
  simp only [neg_zero, one_smul] at h
  exact h

private theorem contDiff_radialDerivative {n : ℕ} {f : ℝ × F → G}
    (hf : ContDiff ℝ (n + 1 : ℕ) f) :
    ContDiff ℝ n (radialDerivative f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

private theorem contDiff_parameterDerivative {n : ℕ} {f : ℝ × F → G}
    (hf : ContDiff ℝ (n + 1 : ℕ) f) :
    ContDiff ℝ n (parameterDerivative f) :=
  (hf.fderiv_right (by simp)).clm_comp contDiff_const

private theorem radialDerivative_radialDerivative_even
    {f : ℝ × F → G} (hf : ContDiff ℝ 2 f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) (r : ℝ) (z : F) :
    radialDerivative (radialDerivative f) (-r, z) =
      radialDerivative (radialDerivative f) (r, z) := by
  have hr := contDiff_radialDerivative (n := 1) hf
  have h := fderiv_reflection (hr.differentiable one_ne_zero) (-1)
    (by
      intro r z
      rw [neg_one_smul]
      exact radialDerivative_odd (hf.differentiable (by norm_num)) heven r z)
    r z (-1) 0
  have hp : ((-1 : ℝ), (0 : F)) = -((1, 0) : ℝ × F) := by simp
  rw [hp, map_neg] at h
  simpa [radialDerivative] using h

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Evenness supplies the zero radial derivative needed for a C¹ radial lift,
including on the axis. -/
theorem contDiff_one_norm_prod_of_even
    {f : ℝ × F → G} (hf : ContDiff ℝ 1 f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) :
    ContDiff ℝ 1 (fun x : E × F ↦ f (‖x.1‖, x.2)) :=
  contDiff_norm_prod_of_radial_derivative_zero hf
    (radialDerivative_zero (hf.differentiable one_ne_zero) heven)

private def radialDerivativeAverage (f : ℝ × F → G) (p : ℝ × F) : G :=
  ∫ t in (0 : ℝ)..1, radialDerivative (radialDerivative f) (t * p.1, p.2)

private theorem radialDerivativeAverage_even
    {f : ℝ × F → G} (hf : ContDiff ℝ 2 f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) (r : ℝ) (z : F) :
    radialDerivativeAverage f (-r, z) = radialDerivativeAverage f (r, z) := by
  apply intervalIntegral.integral_congr
  intro t _
  simpa only [mul_neg] using radialDerivative_radialDerivative_even hf heven (t * r) z

variable [CompleteSpace G]

private theorem radialDerivative_eq_smul_average
    {f : ℝ × F → G} (hf : ContDiff ℝ 2 f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) (r : ℝ) (z : F) :
    radialDerivative f (r, z) = r • radialDerivativeAverage f (r, z) := by
  have hr := contDiff_radialDerivative (n := 1) hf
  have hrr := contDiff_radialDerivative (n := 0) hr
  have hd (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ radialDerivative f (s * r, z))
        (r • radialDerivative (radialDerivative f) (t * r, z)) t := by
    have hline : HasDerivAt (fun s : ℝ ↦ (s * r, z)) (r, 0) t := by
      simpa only [id, one_mul] using
        ((hasDerivAt_id t).mul_const r).prodMk (hasDerivAt_const t z)
    have h := (hr.differentiable one_ne_zero (t * r, z)).hasFDerivAt.comp_hasDerivAt
      t hline
    have hp : (r, (0 : F)) = r • ((1, 0) : ℝ × F) := by simp
    have heq : fderiv ℝ (radialDerivative f) (t * r, z) (r, 0) =
        r • radialDerivative (radialDerivative f) (t * r, z) := by
      rw [hp, map_smul]
      rfl
    rw [heq] at h
    exact h
  have hcont : Continuous (fun t : ℝ ↦
      r • radialDerivative (radialDerivative f) (t * r, z)) :=
    continuous_const.smul (hrr.continuous.comp
      ((continuous_id.mul continuous_const).prodMk continuous_const))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hd t) (hcont.intervalIntegrable 0 1)
  simpa only [one_mul, zero_mul, radialDerivative_zero
    (hf.differentiable (by norm_num)) heven, sub_zero,
    intervalIntegral.integral_smul, radialDerivativeAverage] using h.symm

private theorem contDiff_radialDerivativeAverage
    {n : ℕ} {f : ℝ × F → G} (hf : ContDiff ℝ (n + 2 : ℕ) f) :
    ContDiff ℝ n (radialDerivativeAverage f) := by
  have hr := contDiff_radialDerivative (n := n + 1) hf
  have hrr := contDiff_radialDerivative hr
  have hpath : ContDiff ℝ n (fun p : (ℝ × F) × ℝ ↦ (p.2 * p.1.1, p.1.2)) :=
    (contDiff_snd.mul contDiff_fst.fst).prodMk contDiff_fst.snd
  exact contDiff_intervalIntegral (n := (n : ℕ∞)) (hrr.comp hpath) 0 1

omit [CompleteSpace G] in
private theorem norm_smul_fderiv_norm {x : E} (hx : x ≠ 0) :
    ‖x‖ • fderiv ℝ (fun y : E ↦ ‖y‖) x = innerSL ℝ x := by
  have hn : DifferentiableAt ℝ (fun y : E ↦ ‖y‖) x :=
    (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E ↦ ‖y‖) x).differentiableAt
      one_ne_zero
  have hsq := hn.hasFDerivAt.mul hn.hasFDerivAt
  have hsquare := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  simp only [pow_two] at hsquare
  have heq := hsq.unique hsquare
  apply smul_right_injective (M := E →L[ℝ] ℝ) (by norm_num : (2 : ℝ) ≠ 0)
  simpa only [two_smul] using heq

omit [CompleteSpace G] in
private theorem fderiv_norm_prod_axis
    {f : ℝ × F → G} (hf : ContDiff ℝ 1 f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) (z : F) (v : E × F) :
    fderiv ℝ (fun x : E × F ↦ f (‖x.1‖, x.2)) (0, z) v =
      parameterDerivative f (0, z) v.2 := by
  let g : E × F → G := fun x ↦ f (‖x.1‖, x.2)
  have hg : Differentiable ℝ g :=
    (contDiff_one_norm_prod_of_even hf heven).differentiable one_ne_zero
  let L := fderiv ℝ g (0, z)
  have hflip := fderiv_reflection hg 1 (by
    intro y w
    change f (‖-y‖, w) = (1 : ℝ) • f (‖y‖, w)
    rw [norm_neg, one_smul]) 0 z v.1 0
  have hp : (-v.1, (0 : F)) = -((v.1, 0) : E × F) := by simp
  simp only [neg_zero, hp, map_neg, one_smul] at hflip
  have hzero : L (v.1, 0) = 0 := by
    have hsum : (2 : ℝ) • L (v.1, 0) = 0 := by
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr hflip.symm
    exact (smul_eq_zero.mp hsum).resolve_left (by norm_num)
  have hslice : HasFDerivAt (fun w : F ↦ f (0, w))
      (L.comp (ContinuousLinearMap.inr ℝ E F)) z := by
    have hpath : HasFDerivAt (fun w : F ↦ ((0 : E), w))
        (ContinuousLinearMap.inr ℝ E F) z :=
      ((hasFDerivAt_const (0 : E) z).prodMk (hasFDerivAt_id z))
    have h := (hg (0, z)).hasFDerivAt.comp z hpath
    change HasFDerivAt (fun w : F ↦ f (‖(0 : E)‖, w)) _ _ at h
    simp only [norm_zero] at h
    exact h
  have hparameter : HasFDerivAt (fun w : F ↦ f (0, w))
      (parameterDerivative f (0, z)) z :=
    (hf.differentiable one_ne_zero (0, z)).hasFDerivAt.comp z
      ((hasFDerivAt_const (0 : ℝ) z).prodMk (hasFDerivAt_id z))
  have heq := congrArg (fun A : F →L[ℝ] G ↦ A v.2) (hslice.unique hparameter)
  change L v = _
  calc
    L v = L (v.1, 0) + L (0, v.2) := by
      rw [← map_add]
      congr 1
      simp
    _ = parameterDerivative f (0, z) v.2 := by
      rw [hzero, zero_add]
      exact heq

private def radialLiftDerivative (f : ℝ × F → G) (x : E × F) : E × F →L[ℝ] G :=
  ((innerSL ℝ x.1).comp (ContinuousLinearMap.fst ℝ E F)).smulRight
      (radialDerivativeAverage f (‖x.1‖, x.2)) +
    (parameterDerivative f (‖x.1‖, x.2)).comp (ContinuousLinearMap.snd ℝ E F)

private theorem hasFDerivAt_norm_prod
    {f : ℝ × F → G} (hf : ContDiff ℝ 2 f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) (x : E × F) :
    HasFDerivAt (fun y : E × F ↦ f (‖y.1‖, y.2)) (radialLiftDerivative f x) x := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  rcases x with ⟨y, z⟩
  by_cases hy : y = 0
  · subst y
    have heq : radialLiftDerivative f (0, z) =
        fderiv ℝ (fun x : E × F ↦ f (‖x.1‖, x.2)) (0, z) := by
      apply ContinuousLinearMap.ext
      intro v
      simpa [radialLiftDerivative] using (fderiv_norm_prod_axis hf1 heven z v).symm
    rw [heq]
    exact ((contDiff_one_norm_prod_of_even hf1 heven).differentiable one_ne_zero _).hasFDerivAt
  · have hn : DifferentiableAt ℝ (fun y : E ↦ ‖y‖) y :=
      (contDiffAt_norm ℝ hy : ContDiffAt ℝ 1 (fun y : E ↦ ‖y‖) y).differentiableAt
        one_ne_zero
    let A : E × F →L[ℝ] ℝ × F :=
      ((fderiv ℝ (fun y : E ↦ ‖y‖) y).comp (ContinuousLinearMap.fst ℝ E F)).prod
        (ContinuousLinearMap.snd ℝ E F)
    have hA : HasFDerivAt (fun p : E × F ↦ (‖p.1‖, p.2)) A (y, z) :=
      (hn.hasFDerivAt.comp (y, z) hasFDerivAt_fst).prodMk hasFDerivAt_snd
    have h := (hf1.differentiable one_ne_zero (‖y‖, z)).hasFDerivAt.comp (y, z) hA
    have heq : (fderiv ℝ f (‖y‖, z)).comp A = radialLiftDerivative f (y, z) := by
      apply ContinuousLinearMap.ext
      intro v
      have hsplit (a : ℝ) (b : F) :
          fderiv ℝ f (‖y‖, z) (a, b) =
            a • radialDerivative f (‖y‖, z) + parameterDerivative f (‖y‖, z) b := by
        have hp : (a, b) = a • ((1, 0) : ℝ × F) + (0, b) := by simp
        rw [hp, map_add, map_smul]
        rfl
      have hnorm :
          fderiv ℝ (fun y : E ↦ ‖y‖) y v.1 * ‖y‖ = innerSL ℝ y v.1 := by
        have hval := congrArg (fun A : E →L[ℝ] ℝ ↦ A v.1) (norm_smul_fderiv_norm hy)
        simpa only [smul_apply, smul_eq_mul, mul_comm] using hval
      change fderiv ℝ f (‖y‖, z) (fderiv ℝ (fun y : E ↦ ‖y‖) y v.1, v.2) =
        innerSL ℝ y v.1 • radialDerivativeAverage f (‖y‖, z) +
          parameterDerivative f (‖y‖, z) v.2
      rw [hsplit, radialDerivative_eq_smul_average hf heven, smul_smul, hnorm]
    change HasFDerivAt _ ((fderiv ℝ f (‖y‖, z)).comp A) (y, z) at h
    rw [heq] at h
    exact h

/-- An even profile of class `C^(2k)` has a `C^k` radial lift. The statement
includes the axis and allows a Banach-valued profile and a real normed
external parameter. The derivative count is not sharp; when the radial space is
finite dimensional along with the parameter space,
`contDiff_add_two_norm_prod_of_even` improves it. -/
theorem contDiff_norm_prod_of_even
    (k : ℕ) {f : ℝ × F → G} (hf : ContDiff ℝ (2 * k : ℕ) f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) :
    ContDiff ℝ k (fun x : E × F ↦ f (‖x.1‖, x.2)) := by
  induction k generalizing G with
  | zero =>
    exact contDiff_zero.mpr
      (hf.continuous.comp (continuous_fst.norm.prodMk continuous_snd))
  | succ k ih =>
    have hf' : ContDiff ℝ (2 * k + 2 : ℕ) f := by
      simpa only [Nat.mul_succ] using hf
    have hf2 : ContDiff ℝ 2 f :=
      hf'.of_le (by exact_mod_cast Nat.le_add_left 2 (2 * k))
    have hq := contDiff_radialDerivativeAverage (n := 2 * k) hf'
    have hqlift := ih hq (radialDerivativeAverage_even hf2 heven)
    have hp : ContDiff ℝ (2 * k : ℕ) (parameterDerivative f) :=
      contDiff_parameterDerivative (hf'.of_le
        (by exact_mod_cast Nat.add_le_add_left (by decide : 1 ≤ 2) (2 * k)))
    have hplift := ih hp
      (parameterDerivative_even (hf2.differentiable (by norm_num)) heven)
    have hinner : ContDiff ℝ k (fun x : E × F ↦
        (innerSL ℝ x.1).comp (ContinuousLinearMap.fst ℝ E F)) :=
      ((innerSL ℝ).contDiff.comp contDiff_fst).clm_comp contDiff_const
    exact contDiff_succ_iff_hasFDerivAt.mpr ⟨radialLiftDerivative f,
      (hinner.smulRight hqlift).add (hplift.clm_comp contDiff_const),
      hasFDerivAt_norm_prod hf2 heven⟩

omit [CompleteSpace G] in
/-- A global even-profile regularity theorem for radial lifts localizes to the
profile's germ. At the axis, symmetrizing a global representative of the germ
lets the global theorem apply without regularity away from that germ. -/
private theorem contDiffAt_norm_prod_of_even_of_global [FiniteDimensional ℝ F]
    {m n : ℕ} (hmn : m ≤ n)
    (hglobal : ∀ a : ℝ × F → G, ContDiff ℝ n a → (∀ r z, a (-r, z) = a (r, z)) →
      ContDiff ℝ m (fun x : E × F ↦ a (‖x.1‖, x.2)))
    {f : ℝ × F → G} {x : E × F}
    (hf : ContDiffAt ℝ n f (‖x.1‖, x.2))
    (heven : ∀ r z, f (-r, z) = f (r, z)) :
    ContDiffAt ℝ m (fun y : E × F ↦ f (‖y.1‖, y.2)) x := by
  rcases x with ⟨y, z⟩
  by_cases hy : y = 0
  · subst y
    simp only [norm_zero] at hf
    obtain ⟨g, hg, _hcompact, heq⟩ := hf.exists_contDiff_compactSupport_eventuallyEq
    let a : ℝ × F → G := fun p ↦ (2 : ℝ)⁻¹ • (g p + g (-p.1, p.2))
    have ha : ContDiff ℝ n a :=
      (hg.add (hg.comp (contDiff_fst.neg.prodMk contDiff_snd))).const_smul _
    have haeven : ∀ r z, a (-r, z) = a (r, z) := by
      intro r z
      simp only [a, neg_neg, add_comm]
    have hreflect : Tendsto (fun p : ℝ × F ↦ (-p.1, p.2))
        (𝓝 (0, z)) (𝓝 (0, z)) := by
      have h :=
        (continuous_fst.neg.prodMk continuous_snd).continuousAt.tendsto
          (x := ((0 : ℝ), z))
      change Tendsto (fun p : ℝ × F ↦ (-p.1, p.2)) _ (𝓝 (- (0 : ℝ), z)) at h
      simpa only [neg_zero] using h
    have hlocal : f =ᶠ[𝓝 (0, z)] a := by
      filter_upwards [heq, heq.comp_tendsto hreflect] with p hp hn
      simp only [Function.comp_def] at hn
      change f p = (2 : ℝ)⁻¹ • (g p + g (-p.1, p.2))
      rw [← hp, ← hn, heven, ← two_smul ℝ (f p),
        inv_smul_smul₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have hpath : Tendsto (fun p : E × F ↦ (‖p.1‖, p.2))
        (𝓝 (0, z)) (𝓝 (0, z)) := by
      simpa only [norm_zero] using
        (continuous_fst.norm.prodMk continuous_snd).continuousAt.tendsto
          (x := ((0 : E), z))
    exact (hglobal a ha haeven).contDiffAt.congr_of_eventuallyEq
      (hlocal.comp_tendsto hpath)
  · exact (hf.of_le (by exact_mod_cast hmn)).comp (y, z)
      (((contDiffAt_norm ℝ hy).comp (y, z) contDiffAt_fst).prodMk contDiffAt_snd)

/-- Local even `C^(2k)` regularity gives local `C^k` regularity of the radial
lift, on the axis as well as away from it. -/
theorem contDiffAt_norm_prod_of_even [FiniteDimensional ℝ F]
    (k : ℕ) {f : ℝ × F → G} {x : E × F}
    (hf : ContDiffAt ℝ (2 * k : ℕ) f (‖x.1‖, x.2))
    (heven : ∀ r z, f (-r, z) = f (r, z)) :
    ContDiffAt ℝ k (fun y : E × F ↦ f (‖y.1‖, y.2)) x :=
  contDiffAt_norm_prod_of_even_of_global (Nat.le_mul_of_pos_left k (by decide))
    (fun _ ha haeven ↦ contDiff_norm_prod_of_even k ha haeven) hf heven

open Asymptotics

omit [CompleteSpace G] in
/-- Multiplication by a linear factor vanishing on the axis needs only continuity
of the coefficient to be differentiable there. -/
private theorem hasFDerivAt_linear_smul_continuous_axis
    (L : E →L[ℝ] ℝ) {q : E × F → G} {z : F}
    (hq : ContinuousAt q (0, z)) :
    HasFDerivAt (fun x : E × F ↦ L x.1 • q x)
      ((L.comp (ContinuousLinearMap.fst ℝ E F)).smulRight (q (0, z))) (0, z) := by
  have hsmall : (fun x : E × F ↦ q x - q (0, z)) =o[𝓝 (0, z)]
      (fun _ ↦ (1 : ℝ)) := by
    apply (isLittleO_one_iff ℝ).mpr
    simpa using hq.tendsto.sub (tendsto_const_nhds (x := q (0, z)))
  have hbig : (fun x : E × F ↦ L x.1) =O[𝓝 (0, z)]
      (fun x ↦ ‖x - (0, z)‖) := by
    have h := (L.comp (ContinuousLinearMap.fst ℝ E F)).isBigO_sub (𝓝 (0, z)) (0, z)
    change (fun x : E × F ↦ L (x.1 - 0)) =O[𝓝 (0, z)] (fun x ↦ x - (0, z)) at h
    simpa only [isBigO_norm_right, sub_zero] using h
  have h := hbig.smul_isLittleO hsmall
  apply HasFDerivAt.of_isLittleO
  change (fun x : E × F ↦ L x.1 • q x - L 0 • q (0, z) -
    L (x.1 - 0) • q (0, z)) =o[𝓝 (0, z)] (fun x ↦ x - (0, z))
  simpa only [smul_sub, map_zero, zero_smul, sub_zero,
    smul_eq_mul, mul_one, isLittleO_norm_right] using h

omit [CompleteSpace G] in
/-- The zero trace on the entire axis removes every parameter component of the
derivative, without requiring a separate mixed-derivative assumption. -/
private theorem fderiv_of_zero_on_axis
    {h : ℝ × F → G} (hh : Differentiable ℝ h) (haxis : ∀ z, h (0, z) = 0)
    (z : F) (v : ℝ × F) :
    fderiv ℝ h (0, z) v = v.1 • radialDerivative h (0, z) := by
  have hs := (hh (0, z)).hasFDerivAt.comp z
    ((hasFDerivAt_const (0 : ℝ) z).prodMk (hasFDerivAt_id z))
  have heq : (fun w : F ↦ h (0, w)) = fun _ ↦ (0 : G) := funext haxis
  change HasFDerivAt (fun w : F ↦ h (0, w)) _ z at hs
  rw [heq] at hs
  have hzero := congrArg (fun A : F →L[ℝ] G ↦ A v.2)
    (hs.unique (hasFDerivAt_const (0 : G) z))
  have hp : v = v.1 • ((1, 0) : ℝ × F) + (0, v.2) := by
    ext <;> simp
  rw [hp, map_add, map_smul]
  change v.1 • radialDerivative h (0, z) + fderiv ℝ h (0, z) (0, v.2) = _
  change fderiv ℝ h (0, z) (0, v.2) = 0 at hzero
  rw [hzero, add_zero]
  simp

private def radialNormDerivative (x : E × F) : E × F →L[ℝ] ℝ :=
  (fderiv ℝ (fun y : E ↦ ‖y‖) x.1).comp (ContinuousLinearMap.fst ℝ E F)

private def radialNormProdDerivative (x : E × F) : E × F →L[ℝ] ℝ × F :=
  (radialNormDerivative x).prod (ContinuousLinearMap.snd ℝ E F)

private theorem norm_radialNormDerivative_le (x : E × F) :
    ‖radialNormDerivative x‖ ≤ 1 := by
  have hnorm : ‖fderiv ℝ (fun y : E ↦ ‖y‖) x.1‖ ≤ 1 :=
    norm_fderiv_le_of_lipschitz ℝ (x₀ := x.1) (C := 1) lipschitzWith_one_norm
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hnorm (ContinuousLinearMap.norm_fst_le ℝ E F)
      (ContinuousLinearMap.opNorm_nonneg _) zero_le_one).trans_eq (one_mul 1))

private theorem norm_radialNormProdDerivative_le (x : E × F) :
    ‖radialNormProdDerivative x‖ ≤ 1 := by
  rw [radialNormProdDerivative, ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  exact max_le (norm_radialNormDerivative_le x) (ContinuousLinearMap.norm_snd_le ℝ E F)

private def radialCoefficientValue (f : ℝ × F → G) (x : E × F) : G :=
  radialDerivativeAverage f (‖x.1‖, x.2)

private def radialCoefficientResidual (f : ℝ × F → G) (x : E × F) : E × F →L[ℝ] G :=
  (fderiv ℝ (radialDerivative f) (‖x.1‖, x.2)).comp (radialNormProdDerivative x) -
    (radialNormDerivative x).smulRight (radialCoefficientValue f x)

private def radialCoefficientDerivative (f : ℝ × F → G) (L : E →L[ℝ] ℝ)
    (x : E × F) : E × F →L[ℝ] G :=
  (L.comp (ContinuousLinearMap.fst ℝ E F)).smulRight (radialCoefficientValue f x) +
    (L x.1 / ‖x.1‖) • radialCoefficientResidual f x

omit [InnerProductSpace ℝ E] in
private theorem continuous_radialCoefficientValue
    {f : ℝ × F → G} (hf : ContDiff ℝ 2 f) :
    Continuous (radialCoefficientValue (E := E) f) :=
  (contDiff_radialDerivativeAverage (n := 0) hf).continuous.comp
    (continuous_fst.norm.prodMk continuous_snd)

omit [InnerProductSpace ℝ E] in
private theorem radialCoefficientValue_axis (f : ℝ × F → G) (z : F) :
    radialCoefficientValue (E := E) f (0, z) =
      radialDerivative (radialDerivative f) (0, z) := by
  simp [radialCoefficientValue, radialDerivativeAverage]

private theorem contDiffAt_radialCoefficientValue_off_axis
    {f : ℝ × F → G} (hf : ContDiff ℝ 2 f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) {x : E × F} (hx : x.1 ≠ 0) :
    ContDiffAt ℝ 1 (radialCoefficientValue f) x := by
  have hn : ContDiffAt ℝ 1 (fun y : E × F ↦ ‖y.1‖) x :=
    (contDiffAt_norm ℝ hx).comp x contDiffAt_fst
  have hne : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hh := (contDiff_radialDerivative (n := 1) hf).contDiffAt.comp x
    (hn.prodMk contDiffAt_snd)
  have heq : radialCoefficientValue f =ᶠ[𝓝 x]
      (fun y : E × F ↦ ‖y.1‖⁻¹ • radialDerivative f (‖y.1‖, y.2)) := by
    filter_upwards [hn.continuousAt.eventually_ne hne] with y hy
    rw [radialDerivative_eq_smul_average hf heven, inv_smul_smul₀ hy]
    rfl
  exact ((hn.inv hne).smul hh).congr_of_eventuallyEq heq

private theorem hasFDerivAt_radialNorm {x : E × F} (hx : x.1 ≠ 0) :
    HasFDerivAt (fun y : E × F ↦ ‖y.1‖) (radialNormDerivative x) x :=
  ((contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E ↦ ‖y‖) x.1).differentiableAt
    one_ne_zero).hasFDerivAt.comp x hasFDerivAt_fst

private theorem hasFDerivAt_radialCoefficient_off_axis
    {f : ℝ × F → G} (hf : ContDiff ℝ 2 f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) (L : E →L[ℝ] ℝ)
    {x : E × F} (hx : x.1 ≠ 0) :
    HasFDerivAt (fun y : E × F ↦ L y.1 • radialCoefficientValue f y)
      (radialCoefficientDerivative f L x) x := by
  have hq := (contDiffAt_radialCoefficientValue_off_axis hf heven hx).differentiableAt
    one_ne_zero
  have hn := hasFDerivAt_radialNorm hx
  have hh := ((contDiff_radialDerivative (n := 1) hf).differentiable one_ne_zero
    (‖x.1‖, x.2)).hasFDerivAt.comp x (hn.prodMk hasFDerivAt_snd)
  have hp := hn.smul hq.hasFDerivAt
  have hfun : (fun y : E × F ↦ ‖y.1‖ • radialCoefficientValue f y) =
      (fun y : E × F ↦ radialDerivative f (‖y.1‖, y.2)) := by
    funext y
    exact (radialDerivative_eq_smul_average hf heven _ _).symm
  change HasFDerivAt (fun y : E × F ↦ ‖y.1‖ • radialCoefficientValue f y) _ x at hp
  rw [hfun] at hp
  have hder := hp.unique hh
  change ‖x.1‖ • fderiv ℝ (radialCoefficientValue f) x +
    (radialNormDerivative x).smulRight (radialCoefficientValue f x) =
    (fderiv ℝ (radialDerivative f) (‖x.1‖, x.2)).comp (radialNormProdDerivative x) at hder
  have hres :
      (fderiv ℝ (radialDerivative f) (‖x.1‖, x.2)).comp (radialNormProdDerivative x) -
        (radialNormDerivative x).smulRight (radialCoefficientValue f x) =
      ‖x.1‖ • fderiv ℝ (radialCoefficientValue f) x := by
    rw [← hder]
    exact add_sub_cancel_right _ _
  have h := (L.hasFDerivAt.comp x hasFDerivAt_fst).smul hq.hasFDerivAt
  have hform : radialCoefficientDerivative f L x =
      L x.1 • fderiv ℝ (radialCoefficientValue f) x +
        (L.comp (ContinuousLinearMap.fst ℝ E F)).smulRight (radialCoefficientValue f x) := by
    unfold radialCoefficientDerivative radialCoefficientResidual
    rw [hres, smul_smul, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx), add_comm]
  rw [hform]
  exact h

private theorem norm_linear_div_norm_le (L : E →L[ℝ] ℝ) (y : E) :
    ‖L y / ‖y‖‖ ≤ ‖L‖ := by
  by_cases hy : y = 0
  · simp only [hy, map_zero, norm_zero, div_zero]
    exact norm_nonneg L
  · rw [norm_div, Real.norm_of_nonneg (norm_nonneg y)]
    exact (div_le_iff₀ (norm_pos_iff.mpr hy)).mpr (L.le_opNorm y)

private theorem continuousAt_radialNormDerivative {x : E × F} (hx : x.1 ≠ 0) :
    ContinuousAt (radialNormDerivative (E := E) (F := F)) x := by
  have hn : ContDiffAt ℝ 1 (fun y : E ↦ ‖y‖) x.1 := contDiffAt_norm ℝ hx
  exact ((hn.continuousAt_fderiv one_ne_zero).comp continuousAt_fst).clm_comp
    continuousAt_const

private theorem continuousAt_radialNormProdDerivative {x : E × F} (hx : x.1 ≠ 0) :
    ContinuousAt (radialNormProdDerivative (E := E) (F := F)) x :=
  (ContinuousLinearMap.prodₗᵢ ℝ
    (𝕜 := ℝ) (E := E × F) (F := ℝ) (G := F)).continuous.continuousAt.comp
      ((continuousAt_radialNormDerivative hx).prodMk continuousAt_const)

private theorem continuousAt_radialCoefficientResidual_off_axis
    {f : ℝ × F → G} (hf : ContDiff ℝ 2 f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) {x : E × F} (hx : x.1 ≠ 0) :
    ContinuousAt (radialCoefficientResidual f) x := by
  have hh := (contDiff_radialDerivative (n := 1) hf).continuous_fderiv one_ne_zero
  have hq := (contDiffAt_radialCoefficientValue_off_axis hf heven hx).continuousAt
  have hfirst := (hh.continuousAt.comp (continuousAt_fst.norm.prodMk continuousAt_snd)).clm_comp
    (continuousAt_radialNormProdDerivative hx)
  have hsecond : ContinuousAt
      (fun y : E × F ↦ (radialNormDerivative y).smulRight (radialCoefficientValue f y)) x :=
    isBoundedBilinearMap_smulRight.continuous.continuousAt.comp
      ((continuousAt_radialNormDerivative hx).prodMk hq)
  exact hfirst.sub hsecond

private theorem continuousAt_radialCoefficientDerivative_off_axis
    {f : ℝ × F → G} (hf : ContDiff ℝ 2 f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) (L : E →L[ℝ] ℝ)
    {x : E × F} (hx : x.1 ≠ 0) :
    ContinuousAt (radialCoefficientDerivative f L) x := by
  have hq := (contDiffAt_radialCoefficientValue_off_axis hf heven hx).continuousAt
  have hfirst := (ContinuousLinearMap.smulRightL ℝ (E × F) G
    (L.comp (ContinuousLinearMap.fst ℝ E F))).continuous.continuousAt.comp hq
  have hscalar := (L.continuous.continuousAt.comp continuousAt_fst).div continuousAt_fst.norm
    (norm_ne_zero_iff.mpr hx)
  exact hfirst.add (hscalar.smul (continuousAt_radialCoefficientResidual_off_axis hf heven hx))

private theorem norm_radialCoefficientResidual_le
    {f : ℝ × F → G} (hf : ContDiff ℝ 2 f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) (z : F) (x : E × F) :
    ‖radialCoefficientResidual f x‖ ≤
      ‖fderiv ℝ (radialDerivative f) (‖x.1‖, x.2) -
        fderiv ℝ (radialDerivative f) (0, z)‖ +
      ‖radialCoefficientValue (E := E) f (0, z) - radialCoefficientValue f x‖ := by
  have hzero := radialDerivative_zero (hf.differentiable (by norm_num)) heven
  have hh := (contDiff_radialDerivative (n := 1) hf).differentiable one_ne_zero
  -- The derivative at the limiting axis point has only a radial component.
  have haxis :
      (fderiv ℝ (radialDerivative f) (0, z)).comp (radialNormProdDerivative x) =
        (radialNormDerivative x).smulRight (radialCoefficientValue (E := E) f (0, z)) := by
    apply ContinuousLinearMap.ext
    intro v
    change fderiv ℝ (radialDerivative f) (0, z)
      (radialNormProdDerivative x v) =
      radialNormDerivative x v • radialCoefficientValue (E := E) f (0, z)
    rw [fderiv_of_zero_on_axis hh hzero, radialCoefficientValue_axis]
    rfl
  have hsplit : radialCoefficientResidual f x =
      (fderiv ℝ (radialDerivative f) (‖x.1‖, x.2) -
        fderiv ℝ (radialDerivative f) (0, z)).comp (radialNormProdDerivative x) +
      (radialNormDerivative x).smulRight
        (radialCoefficientValue (E := E) f (0, z) - radialCoefficientValue f x) := by
    rw [ContinuousLinearMap.sub_comp, haxis]
    apply ContinuousLinearMap.ext
    intro v
    simp only [radialCoefficientResidual, add_apply,
      sub_apply, ContinuousLinearMap.smulRight_apply, smul_sub]
    abel
  rw [hsplit]
  refine (norm_add_le
    ((fderiv ℝ (radialDerivative f) (‖x.1‖, x.2) -
      fderiv ℝ (radialDerivative f) (0, z)).comp (radialNormProdDerivative x))
    ((radialNormDerivative x).smulRight
      (radialCoefficientValue (E := E) f (0, z) - radialCoefficientValue f x))).trans
        (add_le_add ?_ ?_)
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left (norm_radialNormProdDerivative_le x) (norm_nonneg _)).trans_eq
        (mul_one _))
  · rw [ContinuousLinearMap.norm_smulRight_apply]
    exact (mul_le_mul_of_nonneg_right (norm_radialNormDerivative_le x) (norm_nonneg _)).trans_eq
      (one_mul _)

private theorem tendsto_radialCoefficientResidual_axis
    {f : ℝ × F → G} (hf : ContDiff ℝ 2 f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) (z : F) :
    Tendsto (radialCoefficientResidual (E := E) f) (𝓝 (0, z)) (𝓝 0) := by
  have hh := (contDiff_radialDerivative (n := 1) hf).continuous_fderiv one_ne_zero
  have hpath : Tendsto (fun x : E × F ↦ (‖x.1‖, x.2)) (𝓝 (0, z)) (𝓝 (0, z)) := by
    simpa using (continuousAt_fst.norm.prodMk continuousAt_snd :
      ContinuousAt (fun x : E × F ↦ (‖x.1‖, x.2)) (0, z)).tendsto
  have hhzero := ((hh.tendsto (0, z)).comp hpath).sub
    (tendsto_const_nhds (x := fderiv ℝ (radialDerivative f) (0, z)))
  have hqzero := (tendsto_const_nhds (x := radialCoefficientValue (E := E) f (0, z))).sub
    ((continuous_radialCoefficientValue (E := E) hf).tendsto (0, z))
  apply squeeze_zero_norm (E := E × F →L[ℝ] G)
    (fun x ↦ norm_radialCoefficientResidual_le hf heven z x)
  simpa only [Function.comp_apply, sub_self, norm_zero, zero_add] using hhzero.norm.add hqzero.norm

private theorem continuousAt_radialCoefficientDerivative_axis
    {f : ℝ × F → G} (hf : ContDiff ℝ 2 f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) (L : E →L[ℝ] ℝ) (z : F) :
    ContinuousAt (radialCoefficientDerivative f L) (0, z) := by
  have hq : ContinuousAt (radialCoefficientValue (E := E) f) (0, z) :=
    (continuous_radialCoefficientValue hf).continuousAt
  have hfirst := (ContinuousLinearMap.smulRightL ℝ (E × F) G
    (L.comp (ContinuousLinearMap.fst ℝ E F))).continuous.continuousAt.comp hq
  change ContinuousAt (fun x : E × F ↦
    (L.comp (ContinuousLinearMap.fst ℝ E F)).smulRight (radialCoefficientValue f x))
    (0, z) at hfirst
  -- The directional factor can fail to converge, but it is uniformly bounded
  -- and multiplies a residual tending to zero jointly in both variables.
  have hcorrection : Tendsto
      (fun x : E × F ↦ (L x.1 / ‖x.1‖) • radialCoefficientResidual f x)
      (𝓝 (0, z)) (𝓝 0) := by
    have hbound (x : E × F) :
        ‖(L x.1 / ‖x.1‖) • radialCoefficientResidual f x‖ ≤
          ‖L‖ * ‖radialCoefficientResidual f x‖ := by
      exact (ContinuousLinearMap.opNorm_smul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_linear_div_norm_le L x.1)
          (ContinuousLinearMap.opNorm_nonneg (radialCoefficientResidual f x)))
    have hnorm : Tendsto (fun x : E × F ↦ ‖radialCoefficientResidual f x‖)
        (𝓝 (0, z)) (𝓝 0) := by
      have hc : Continuous (fun A : E × F →L[ℝ] G ↦ ‖A‖) :=
        @continuous_norm (E × F →L[ℝ] G) inferInstance
      have ht := (hc.tendsto 0).comp (tendsto_radialCoefficientResidual_axis (E := E) hf heven z)
      change Tendsto (fun x : E × F ↦ ‖radialCoefficientResidual f x‖)
        (𝓝 (0, z)) (𝓝 ‖(0 : E × F →L[ℝ] G)‖) at ht
      rwa [ContinuousLinearMap.opNorm_zero] at ht
    exact squeeze_zero_norm (E := E × F →L[ℝ] G) hbound
      (by simpa only [mul_zero] using (tendsto_const_nhds (x := ‖L‖)).mul hnorm)
  change Tendsto (fun x : E × F ↦ radialCoefficientDerivative f L x) (𝓝 (0, z))
    (𝓝 (radialCoefficientDerivative f L (0, z)))
  dsimp only [radialCoefficientDerivative]
  simpa only [map_zero, norm_zero, div_zero, zero_smul, add_zero] using
    hfirst.tendsto.add hcorrection

private theorem contDiff_radialCoefficient
    {f : ℝ × F → G} (hf : ContDiff ℝ 2 f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) (L : E →L[ℝ] ℝ) :
    ContDiff ℝ 1 (fun x : E × F ↦ L x.1 • radialCoefficientValue f x) := by
  refine contDiff_one_iff_hasFDerivAt.mpr ⟨radialCoefficientDerivative f L, ?_, ?_⟩
  · apply continuous_iff_continuousAt.mpr
    rintro ⟨y, z⟩
    by_cases hy : y = 0
    · subst y
      exact continuousAt_radialCoefficientDerivative_axis hf heven L z
    · exact continuousAt_radialCoefficientDerivative_off_axis hf heven L hy
  · rintro ⟨y, z⟩
    by_cases hy : y = 0
    · subst y
      simpa [radialCoefficientDerivative] using
        (hasFDerivAt_linear_smul_continuous_axis L
          (continuous_radialCoefficientValue hf).continuousAt (z := z))
    · exact hasFDerivAt_radialCoefficient_off_axis hf heven L hy

/-- An even `C²` profile has a `C²` radial lift, including joint derivatives
in the parameter. Finite-dimensionality permits reconstruction of the
continuous derivative from its applications. -/
theorem contDiff_two_norm_prod_of_even [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : ℝ × F → G} (hf : ContDiff ℝ 2 f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) :
    ContDiff ℝ 2 (fun x : E × F ↦ f (‖x.1‖, x.2)) := by
  have hp := contDiff_one_norm_prod_of_even (E := E)
    (contDiff_parameterDerivative (n := 1) hf)
    (parameterDerivative_even (hf.differentiable (by norm_num)) heven)
  have hderivative : ContDiff ℝ 1 (radialLiftDerivative (E := E) f) := by
    apply contDiff_clm_apply_iff.mpr
    intro v
    have hr := contDiff_radialCoefficient hf heven (innerSL ℝ v.1)
    have hpa := hp.clm_apply (contDiff_const (c := v.2))
    change ContDiff ℝ 1 (fun x : E × F ↦
      innerSL ℝ x.1 v.1 • radialCoefficientValue f x +
        parameterDerivative f (‖x.1‖, x.2) v.2)
    simpa only [innerSL_apply_apply, real_inner_comm] using hr.add hpa
  exact contDiff_succ_iff_hasFDerivAt.mpr
    ⟨radialLiftDerivative f, hderivative, hasFDerivAt_norm_prod hf heven⟩

/-- An even `C^(2k+2)` profile has a `C^(k+2)` radial lift. The sharp `C²`
base case saves two input derivatives compared with the elementary averaging
induction; in particular, even `C⁶` input gives a `C⁴` lift. -/
theorem contDiff_add_two_norm_prod_of_even
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (k : ℕ) {f : ℝ × F → G} (hf : ContDiff ℝ (2 * k + 2 : ℕ) f)
    (heven : ∀ r z, f (-r, z) = f (r, z)) :
    ContDiff ℝ (k + 2 : ℕ) (fun x : E × F ↦ f (‖x.1‖, x.2)) := by
  induction k generalizing G with
  | zero =>
    exact contDiff_two_norm_prod_of_even hf heven
  | succ k ih =>
    have hf' : ContDiff ℝ ((2 * k + 2) + 2 : ℕ) f := by
      simpa only [Nat.mul_succ] using hf
    have hf2 : ContDiff ℝ 2 f :=
      hf'.of_le (by exact_mod_cast Nat.le_add_left 2 (2 * k + 2))
    have hq := contDiff_radialDerivativeAverage (n := 2 * k + 2) hf'
    have hqlift := ih hq (radialDerivativeAverage_even hf2 heven)
    have hp : ContDiff ℝ (2 * k + 2 : ℕ) (parameterDerivative f) :=
      contDiff_parameterDerivative (hf'.of_le
        (by exact_mod_cast Nat.add_le_add_left (by decide : 1 ≤ 2) (2 * k + 2)))
    have hplift := ih hp
      (parameterDerivative_even (hf2.differentiable (by norm_num)) heven)
    have hinner : ContDiff ℝ (k + 2 : ℕ) (fun x : E × F ↦
        (innerSL ℝ x.1).comp (ContinuousLinearMap.fst ℝ E F)) :=
      ((innerSL ℝ).contDiff.comp contDiff_fst).clm_comp contDiff_const
    have h : ContDiff ℝ ((k + 2) + 1 : ℕ) (fun x : E × F ↦ f (‖x.1‖, x.2)) :=
      contDiff_succ_iff_hasFDerivAt.mpr ⟨radialLiftDerivative f,
      (hinner.smulRight hqlift).add (hplift.clm_comp contDiff_const),
      hasFDerivAt_norm_prod hf2 heven⟩
    exact h

/-- The improved finite radial theorem is local in the profile's germ. It
therefore applies at knots and at the axis when only local `C^(2k+2)`
regularity is known. -/
theorem contDiffAt_add_two_norm_prod_of_even
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (k : ℕ) {f : ℝ × F → G} {x : E × F}
    (hf : ContDiffAt ℝ (2 * k + 2 : ℕ) f (‖x.1‖, x.2))
    (heven : ∀ r z, f (-r, z) = f (r, z)) :
    ContDiffAt ℝ (k + 2 : ℕ) (fun y : E × F ↦ f (‖y.1‖, y.2)) x :=
  contDiffAt_norm_prod_of_even_of_global (by omega)
    (fun _ ha haeven ↦ contDiff_add_two_norm_prod_of_even k ha haeven) hf heven

end PDE.Analysis
