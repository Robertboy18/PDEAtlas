/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
public import PDE.Analysis.Integration.Rectangle.MixedPrimitive
import Mathlib.Algebra.Order.Ring.Star
import PDE.DistributionTheory.TestFunction.CompactCutoff
import PDE.Spaces.Sobolev.Approximation.Mollification.LpApproximation
import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.LocalizedPullback
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra
import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Sobolev slicing foundations in the plane

Fundamental-theorem identities on almost every coordinate line for a
continuous `F : ℝ^2 → ℝ` whose weak derivative `H = ∂₀F` lies in `L¹(ℝ^2)`;
this is the situation of a continuous representative of a planar `W^{1,1}`
function. For almost every `s`,

`∫_a^b H(r, s) dr = F(b, s) - F(a, s)`.

The identity is proved for smooth compactly supported approximants, where it
is the classical fundamental theorem on each line, and then passed to the
limit. `L¹` convergence on the plane gives, after Fubini, `L¹` convergence of
the line integrals as functions of `s`, hence almost everywhere convergence
along a subsequence, which identifies the limit on almost every line. The
exceptional null set may depend on the endpoints `a, b`; the general ACL
representative theorem, with one null set serving all intervals, is
`Slicing.ACL`.

The identity is then transported to the slope chart
`(r, s) ↦ (r, r s)` on the region `r > δ`. The names treat the first
coordinate as a radial variable `r` and the second as an axial one, as in
axisymmetric `(r, z)` coordinates, and the slope chart parametrizes the rays
`z = s r`. The chart is a smooth partial homeomorphism whose inverse
`(r, z) ↦ (r, z / r)` is made globally smooth by the cutoff `safeInv`, and the
first-order weak chain rule of `Pullback.FirstOrder.LocalizedPullback` gives
the weak radial derivative of the pullback.

## Main results

* `eLpNorm_one_integral_prod_right_le`,
  `exists_subseq_ae_integral_prod_right_tendsto_zero`: integrating out one
  variable is an `L¹` contraction, and `L¹` convergence on a product gives
  a.e. convergence of the partial integrals along a subsequence.
* `slopeOpenPartialHomeomorph`, `hasWeakDerivativeOn_slopeMap_first_of_memLp`:
  the slope chart on `r > δ`, and the weak radial derivative
  `g_r(r, rs) + s g_z(r, rs)` of `f(r, rs)`.
* `ae_intervalIntegral_weakDerivative_firstCoordinate_eq_sub`: the coordinate
  FTC on almost every horizontal line for a continuous `F` with
  `∂₀F ∈ L¹(ℝ^2)`.
* `ae_intervalIntegral_weakDerivative_firstCoordinate_eq_sub_on_rectangle`:
  the same on a compact rectangle inside an open set `U`, with `F` continuous
  and the weak derivative hypothesis (hence local integrability of `H`) only
  on `U`.
* `ae_intervalIntegral_slopeMap_weakDerivative_eq_sub`: the radial FTC along
  rays in the slope chart.

## Implementation notes

Points of the plane are written `EuclideanSpace.single 0 r +
EuclideanSpace.single 1 s`, and `PDE.Analysis.planeEquivSwap` orders the
product coordinates as `(s, r)` so that the second product variable is the
one integrated along the line. The cutoff in `safeInv δ` vanishes for
`r ≤ δ/2` and equals `r⁻¹` for `r ≥ δ`, which is all that is needed for the
chart inverse to be smooth on `ℝ^2` while agreeing with the true inverse on
the chart.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 8, for the fundamental theorem of calculus `ū(b) - ū(a) = ∫_a^b u'` for
  `W^{1,p}` on an interval.
  <https://doi.org/10.1007/978-0-387-70914-7>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace
namespace Slices

open Filter MeasureTheory Set
open scoped ENNReal Topology

variable {α β E : Type*}
  [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

omit [CompleteSpace E] [SFinite μ] in
/-- Integrating out the second variable is a contraction from product `L¹`
to `L¹`. -/
theorem eLpNorm_one_integral_prod_right_le
    {f : α × β → E} (hf : Integrable f (μ.prod ν)) :
    eLpNorm (fun x ↦ ∫ y, f (x, y) ∂ν) 1 μ ≤
      eLpNorm f 1 (μ.prod ν) := by
  rw [eLpNorm_one_eq_lintegral_enorm hf.integral_prod_left.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
  calc
    (∫⁻ x, ‖∫ y, f (x, y) ∂ν‖ₑ ∂μ) ≤
        ∫⁻ x, ∫⁻ y, ‖f (x, y)‖ₑ ∂ν ∂μ := by
      exact lintegral_mono fun x ↦ enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ p, ‖f p‖ₑ ∂(μ.prod ν) := by
      rw [lintegral_prod]
      exact hf.1.enorm

omit [CompleteSpace E] [SFinite μ] in
/-- If product-space functions converge to zero in `L¹`, a subsequence of
their integrals in the second variable converges pointwise almost everywhere
to zero. -/
theorem exists_subseq_ae_integral_prod_right_tendsto_zero
    (f : ℕ → α × β → E)
    (hf : ∀ m, Integrable (f m) (μ.prod ν))
    (hconv : Tendsto (fun m ↦ eLpNorm (f m) 1 (μ.prod ν)) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun i ↦ ∫ y, f (ns i) (x, y) ∂ν)
        atTop (𝓝 0) := by
  let A : ℕ → α → E := fun m x ↦ ∫ y, f m (x, y) ∂ν
  have hAconv : Tendsto (fun m ↦ eLpNorm (A m) 1 μ) atTop (𝓝 0) := by
    apply ENNReal.tendsto_nhds_zero.2
    intro ε hε
    have hev := (ENNReal.tendsto_nhds_zero.1 hconv) ε hε
    filter_upwards [hev] with m hm
    exact (eLpNorm_one_integral_prod_right_le (hf m)).trans hm
  have hmeasure : TendstoInMeasure μ A atTop 0 := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := (1 : ℝ≥0∞)) (by norm_num)
    simpa only [sub_zero] using hAconv
  simpa [A] using hmeasure.exists_seq_tendsto_ae

/-! ## Smooth slope charts away from the radial axis -/

/-- A smooth cutoff times `r⁻¹`, equal to the true reciprocal on `r ≥ δ`
and identically zero near the origin. -/
noncomputable def safeInv (δ r : ℝ) : ℝ :=
  Real.smoothTransition (2 * r / δ - 1) * r⁻¹

/-- For `r ≥ δ` the cutoff equals `1`, so `safeInv δ r = r⁻¹`. -/
theorem safeInv_eq_inv {δ r : ℝ} (hδ : 0 < δ) (hr : δ ≤ r) :
    safeInv δ r = r⁻¹ := by
  have harg : 1 ≤ 2 * r / δ - 1 := by
    apply (le_sub_iff_add_le).2
    rw [show (1 : ℝ) + 1 = 2 by norm_num]
    exact (le_div_iff₀ hδ).2 (by linarith)
  rw [safeInv, Real.smoothTransition.one_of_one_le harg, one_mul]

/-- For `r ≤ δ/2` the cutoff vanishes, so `safeInv δ r = 0`. In particular
`safeInv δ` is identically zero near the origin, where `r⁻¹` is singular. -/
theorem safeInv_eq_zero_of_le_half {δ r : ℝ} (hδ : 0 < δ)
    (hr : r ≤ δ / 2) : safeInv δ r = 0 := by
  have harg : 2 * r / δ - 1 ≤ 0 := by
    rw [sub_nonpos]
    exact (div_le_one hδ).2 (by linarith)
  rw [safeInv, Real.smoothTransition.zero_of_nonpos harg, zero_mul]

/-- `safeInv δ` is smooth on all of `ℝ` when `δ > 0`: away from `0` it is a
product of smooth functions, and near `0` it vanishes identically. -/
theorem contDiff_safeInv (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (safeInv δ) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  by_cases hr : r = 0
  · subst r
    have hevent : safeInv δ =ᶠ[𝓝 (0 : ℝ)] fun _ ↦ 0 := by
      filter_upwards [Iio_mem_nhds (half_pos hδ)] with x hx
      exact safeInv_eq_zero_of_le_half hδ hx.le
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hevent
  · have hcut : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun x ↦ Real.smoothTransition (2 * x / δ - 1)) r := by
      fun_prop
    have hinv : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ x⁻¹) r :=
      contDiffAt_inv ℝ hr
    change ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : ℝ ↦ Real.smoothTransition (2 * x / δ - 1) * x⁻¹) r
    exact hcut.mul hinv

/-- The slope-coordinate map `(r,s) ↦ (r, r*s)`. -/
def slopeMap (x : ℝ^2) : ℝ^2 :=
  EuclideanSpace.single 0 (x 0) + EuclideanSpace.single 1 (x 0 * x 1)

/-- Globally smooth inverse representative for the slope map on `r > δ`. -/
noncomputable def slopeInv (δ : ℝ) (x : ℝ^2) : ℝ^2 :=
  EuclideanSpace.single 0 (x 0) +
    EuclideanSpace.single 1 (safeInv δ (x 0) * x 1)

/-- The open region in slope coordinates where the radial coordinate exceeds `δ`. -/
def radialAway (δ : ℝ) : Set (ℝ^2) := {x | δ < x 0}

/-- The region `r > δ` is open. -/
theorem isOpen_radialAway (δ : ℝ) : IsOpen (radialAway δ) := by
  exact isOpen_lt continuous_const
    (PiLp.continuous_apply (p := (2 : ℝ≥0∞))
      (β := fun _ : Fin 2 ↦ ℝ) 0)

/-- The slope map `(r, s) ↦ (r, r s)` is smooth. -/
theorem contDiff_slopeMap : ContDiff ℝ (⊤ : ℕ∞) slopeMap := by
  have h (k : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^2 ↦ x k) := by fun_prop
  refine (contDiff_piLp 2).2 fun i ↦ ?_
  fin_cases i
  · simpa [slopeMap] using h 0
  · simpa [slopeMap] using (h 0).mul (h 1)

/-- The smoothed inverse `(r, z) ↦ (r, safeInv δ r · z)` is smooth for
`δ > 0`. -/
theorem contDiff_slopeInv (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (slopeInv δ) := by
  have h (k : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^2 ↦ x k) := by fun_prop
  refine (contDiff_piLp 2).2 fun i ↦ ?_
  fin_cases i
  · simpa [slopeInv] using h 0
  · simpa [slopeInv] using ((contDiff_safeInv δ hδ).comp (h 0)).mul (h 1)

/-- On `r > δ`, slope coordinates form a smooth partial
homeomorphism with the globally smoothed inverse above. -/
noncomputable def slopeOpenPartialHomeomorph (δ : ℝ) (hδ : 0 < δ) :
    OpenPartialHomeomorph (ℝ^2) (ℝ^2) where
  toFun := slopeMap
  invFun := slopeInv δ
  source := radialAway δ
  target := radialAway δ
  map_source' x hx := by simpa [radialAway, slopeMap] using hx
  map_target' x hx := by simpa [radialAway, slopeInv] using hx
  left_inv' x hx := by
    have hr : δ ≤ x 0 := hx.le
    have hr0 : x 0 ≠ 0 := ne_of_gt (hδ.trans hx)
    ext i
    fin_cases i
    · simp [slopeMap, slopeInv]
    · simp [slopeMap, slopeInv, safeInv_eq_inv hδ hr, hr0]
  right_inv' x hx := by
    have hr : δ ≤ x 0 := hx.le
    have hr0 : x 0 ≠ 0 := ne_of_gt (hδ.trans hx)
    ext i
    fin_cases i
    · simp [slopeMap, slopeInv]
    · simp [slopeMap, slopeInv, safeInv_eq_inv hδ hr, hr0]
  open_source := isOpen_radialAway δ
  open_target := isOpen_radialAway δ
  continuousOn_toFun := contDiff_slopeMap.continuous.continuousOn
  continuousOn_invFun := (contDiff_slopeInv δ hδ).continuous.continuousOn

/-- The slope chart acts by `slopeMap`. -/
@[simp] theorem slopeOpenPartialHomeomorph_apply
    (δ : ℝ) (hδ : 0 < δ) (x : ℝ^2) :
    slopeOpenPartialHomeomorph δ hδ x = slopeMap x := rfl

/-- The inverse of the slope chart acts by the smoothed inverse `slopeInv δ`. -/
@[simp] theorem slopeOpenPartialHomeomorph_symm_apply
    (δ : ℝ) (hδ : 0 < δ) (x : ℝ^2) :
    (slopeOpenPartialHomeomorph δ hδ).symm x = slopeInv δ x := rfl

/-- The source of the slope chart is the region `r > δ`. -/
@[simp] theorem slopeOpenPartialHomeomorph_source
    (δ : ℝ) (hδ : 0 < δ) :
    (slopeOpenPartialHomeomorph δ hδ).source = radialAway δ :=
  rfl

/-- The target of the slope chart is again the region `r > δ`. -/
@[simp] theorem slopeOpenPartialHomeomorph_target
    (δ : ℝ) (hδ : 0 < δ) :
    (slopeOpenPartialHomeomorph δ hδ).target = radialAway δ :=
  rfl

/-- The radial column of the Jacobian of `(r,s) ↦ (r,r*s)`. -/
theorem fderiv_slopeMap_apply_first (x : ℝ^2) :
    (fderiv ℝ slopeMap x) (EuclideanSpace.single 0 (1 : ℝ)) =
      EuclideanSpace.single 0 (1 : ℝ) +
        EuclideanSpace.single 1 (x 1) := by
  ext j
  rw [show (fderiv ℝ slopeMap x) (EuclideanSpace.single 0 1) j = (∂[0] slopeMap) x j from rfl,
    PDE.partialDeriv_apply 0 j (contDiff_slopeMap.differentiable (by simp) x)]
  have h (k : Fin 2) : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y k) x := by fun_prop
  fin_cases j <;> simp [slopeMap, PDE.partialDeriv_mul (h 0) (h 1)]

/-- Weak radial differentiation in slope coordinates.  For a global
`W^{1,1}` representative on `r > δ`, the pullback `(r,s) ↦ f(r,r*s)` has
weak radial derivative `g_r(r,r*s) + s*g_z(r,r*s)`. -/
theorem hasWeakDerivativeOn_slopeMap_first_of_memLp
    (δ : ℝ) (hδ : 0 < δ) (f gr gz : ℝ^2 → ℝ)
    (hfLp : MemLp f 1 (domainMeasure 2 (radialAway δ)))
    (hgrLp : MemLp gr 1 (domainMeasure 2 (radialAway δ)))
    (hgzLp : MemLp gz 1 (domainMeasure 2 (radialAway δ)))
    (hweakr : HasWeakDerivativeOn (n := 2) (radialAway δ) [0] f gr)
    (hweakz : HasWeakDerivativeOn (n := 2) (radialAway δ) [1] f gz) :
    HasWeakDerivativeOn (n := 2) (radialAway δ) [0]
      (fun x ↦ f (slopeMap x))
      (fun x ↦ gr (slopeMap x) + x 1 * gz (slopeMap x)) := by
  let E := slopeOpenPartialHomeomorph δ hδ
  let du : Fin 2 → ℝ^2 → ℝ := fun j ↦ if j = 0 then gr else gz
  have hduLp : ∀ j, MemLp (du j) 1 (domainMeasure 2 E.target) := by
    intro j
    fin_cases j
    · simpa [du, E] using hgrLp
    · simpa [du, E] using hgzLp
  have hweak : ∀ j, HasWeakDerivativeOn (n := 2) E.target [j] f (du j) := by
    intro j
    fin_cases j
    · simpa [du, E] using hweakr
    · simpa [du, E] using hweakz
  have hchain := WeakChangeOfVariables.hasWeakDerivativeOn_comp_partialHomeomorph_W1p_of_memLp
    (n := 2) (p := (1 : ℝ≥0∞)) (Approximation.standardMollifier 2)
    (by norm_num) (E := E) (contDiff_slopeMap.of_le (by norm_num))
    ((contDiff_slopeInv δ hδ).of_le (by norm_num)) hfLp hduLp hweak (0 : Fin 2)
  have hderiv :
      (fun x ↦ ∑ j : Fin 2, du j (E x) *
        ((fderiv ℝ (fun y ↦ E y) x)
          (EuclideanSpace.single 0 (1 : ℝ))) j) =
        fun x ↦ gr (slopeMap x) + x 1 * gz (slopeMap x) := by
    funext x
    rw [show (fun y ↦ E y) = slopeMap by rfl, fderiv_slopeMap_apply_first]
    simp [du, E]
    ring
  rw [hderiv] at hchain
  simpa [E] using hchain

/-! ## FTC on almost every coordinate line -/

/-- `(r, s) ↦ r e₀ + s e₁` is continuous. -/
private theorem continuous_single_add_single :
    Continuous fun p : ℝ × ℝ ↦ (EuclideanSpace.single 0 p.1 + EuclideanSpace.single 1 p.2 : ℝ^2) :=
  ContDiff.continuous (𝕜 := ℝ) (n := 0) <| (contDiff_piLp 2).2 fun i ↦ by
    fin_cases i <;> simp [continuous_fst, continuous_snd]

/-- Localization by a cutoff: for a compact `K` inside an open `W ⊆ Ω` there is a test function
`ψ` equal to `1` near `K` such that every first weak derivative `∂ᵢf = g` on `W` gives the
compactly supported, integrable weak derivative `∂ᵢ(ψ f) = ψ g + ∂ᵢψ f` on `Ω`. -/
private theorem exists_cutoff_hasWeakDerivativeOn {W Ω K : Set (ℝ^2)} (hW : IsOpen W)
    (hWΩ : W ⊆ Ω) (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ ψ : TestFunction (⊤ : TopologicalSpace.Opens (ℝ^2)) ℝ ⊤, (∀ x ∈ K, ψ.toFun =ᶠ[𝓝 x] 1) ∧
      ∀ {i : Fin 2} {f g : ℝ^2 → ℝ}, HasWeakDerivativeOn (n := 2) W [i] f g →
        HasWeakDerivativeOn (n := 2) Ω [i] (fun x ↦ ψ.toFun x * f x)
            (fun x ↦ ψ.toFun x * g x + iteratedPartialDeriv (n := 2) [i] ψ.toFun x * f x) ∧
          Integrable (fun x ↦ ψ.toFun x * f x) ∧
          Integrable fun x ↦
            ψ.toFun x * g x + iteratedPartialDeriv (n := 2) [i] ψ.toFun x * f x := by
  obtain ⟨V, hV, hKV, hclVW, hclV⟩ := exists_open_between_and_isCompact_closure hK hW hKW
  have hVW : V ⊆ W := subset_closure.trans hclVW
  obtain ⟨ψ, hψV, -, hψ1, -⟩ := TestFunction.exists_eq_one_on_compact hV hK hKV
  obtain ⟨χ, hχV, -, hχ1, -⟩ := TestFunction.exists_eq_one_on_compact hV ψ.hasCompactSupport hψV
  refine ⟨ψ, hψ1, fun {i f g} hw ↦ ?_⟩
  have hs (u v : ℝ^2 → ℝ) : Function.support (fun x ↦ u x * v x) ⊆ tsupport u :=
    (Function.support_mul_subset_left _ _).trans (subset_tsupport _)
  have hsG := (Function.support_add _ _).trans <| union_subset (hs ψ.toFun g)
    ((hs _ f).trans (PDE.tsupport_iteratedPartialDeriv_subset [i] ψ.toFun))
  have hLp {u : ℝ^2 → ℝ} (hu : LocallyIntegrableOn u W) : MemLp u 1 (domainMeasure 2 V) :=
    memLp_one_iff_integrable.2 (hu.integrableOn_compact_subset hclVW hclV |>.mono_set
      subset_closure : IntegrableOn u V volume)
  have hext {Ω' : Set (ℝ^2)} (hVΩ' : V ⊆ Ω') :=
    CompactSupportLocalization.hasWeakDerivativeOn_of_support_subset_of_cutoff_one_nhds
      hV hVΩ' hψV (hs ψ.toFun f) hsG χ hχV hχ1 <|
        hasWeakDerivativeOn_mul_testFunction_first (p := 1) (hLp hw.locallyIntegrable_f)
          (hLp hw.locallyIntegrable_g) (hw.mono hV.measurableSet hVW) ψ
  have hwW := hext hVW
  have hint {u : ℝ^2 → ℝ} (hu : LocallyIntegrableOn u W)
      (hsu : Function.support u ⊆ tsupport ψ.toFun) : Integrable u :=
    (integrableOn_iff_integrable_of_support_subset hsu).1
      (hu.integrableOn_compact_subset (hψV.trans hVW) ψ.hasCompactSupport)
  exact ⟨hext (hVW.trans hWΩ), hint hwW.locallyIntegrable_f (hs ψ.toFun f),
    hint hwW.locallyIntegrable_g hsG⟩

/-- Where `ψ = 1` near `x`, the cut-off pair `(ψ f, ψ g + ∂ᵢψ f)` takes the values `(f x, g x)`. -/
private theorem cutoff_apply_of_eventuallyEq_one {ψ : ℝ^2 → ℝ} {x : ℝ^2} (h : ψ =ᶠ[𝓝 x] 1)
    (i : Fin 2) (f g : ℝ^2 → ℝ) :
    ψ x * f x = f x ∧ ψ x * g x + iteratedPartialDeriv (n := 2) [i] ψ x * f x = g x := by
  have h0 : iteratedPartialDeriv (n := 2) [i] ψ x = 0 := by
    simpa [iteratedPartialDeriv, PDE.partialDeriv] using (h.iteratedPartialDeriv [i]).eq_of_nhds
  simp [h.eq_of_nhds, h0]

/-- A continuous global `W^{1,1}` representative obeys the coordinate FTC
on almost every line parallel to the first coordinate axis. -/
theorem ae_intervalIntegral_weakDerivative_firstCoordinate_eq_sub
    (F H : ℝ^2 → ℝ)
    (hF : Continuous F)
    (hH : MemLp H 1 (volume : Measure (ℝ^2)))
    (hweak : HasWeakDerivativeOn (n := 2) Set.univ [0] F H)
    (a b : ℝ) :
    ∀ᵐ s ∂(volume : Measure ℝ),
      (∫ r in a..b,
        H (EuclideanSpace.single 0 r + EuclideanSpace.single 1 s)) =
      F (EuclideanSpace.single 0 b + EuclideanSpace.single 1 s) -
        F (EuclideanSpace.single 0 a + EuclideanSpace.single 1 s) := by
  let moll := Approximation.standardMollifier 2
  let ε : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  have hεpos : ∀ m, 0 < ε m := fun m ↦ Nat.one_div_pos_of_nat
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hFLoc : LocallyIntegrable F volume := locallyIntegrableOn_univ.mp hweak.locallyIntegrable_f
  let Fm : ℕ → ℝ^2 → ℝ := fun m ↦ Approximation.mollify moll (ε m) F
  let Hm : ℕ → ℝ^2 → ℝ := fun m ↦ Approximation.mollify moll (ε m) H
  let q : ℝ → ℝ → ℝ^2 := fun r s ↦ EuclideanSpace.single 0 r + EuclideanSpace.single 1 s
  -- the classical FTC on every line for the mollified functions
  have hFTC (m : ℕ) (s : ℝ) : (∫ r in a..b, Hm m (q r s)) = Fm m (q b s) - Fm m (q a s) := by
    have hq :
        (fun t ↦ q t s) = fun t ↦ t • EuclideanSpace.single 0 1 + EuclideanSpace.single 1 s := by
      ext t j
      fin_cases j <;> simp [q]
    have hγ (r : ℝ) : HasDerivAt (fun t ↦ q t s) (EuclideanSpace.single 0 1) r := by
      rw [hq]
      simpa using (hasDerivAt_id r).smul_const (EuclideanSpace.single 0 1 : ℝ^2)
    have hderiv : (fun x ↦ (∂[0] (Fm m)) x) = Hm m := by
      change (fun x ↦ iteratedPartialDeriv (n := 2) [0] (Fm m) x) = Hm m
      simpa [Fm, Hm] using
        Approximation.iteratedPartialDeriv_mollify_eq_mollify_of_hasWeakDerivative_univ
          moll (hεpos m) (α := ([0] : List (Fin 2))) (by simp) hFLoc hweak
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t ↦ Fm m (q t s))
      (fun r _ ↦ ?_) ((Approximation.mollify_contDiff_of_pos moll (hεpos m) H
        (hH.locallyIntegrable le_rfl) |>.continuous.comp'
          (continuous_single_add_single.comp' (.prodMk_left s))).intervalIntegrable a b)
    exact ((Approximation.mollify_contDiff_of_pos moll (hεpos m) F hFLoc).differentiable
      (by simp) (q r s)).hasFDerivAt.comp_hasDerivAt r (hγ r) |>.congr_deriv
        (congrFun hderiv (q r s))
  -- `L¹` convergence on the plane gives `L¹` convergence on a.e. line along a subsequence
  have hH1 := memLp_one_iff_integrable.mp hH
  have hHm (m : ℕ) : Integrable (Hm m) := memLp_one_iff_integrable.mp <| lt_of_le_of_lt
    (Approximation.MollifyLp.eLpNorm_mollify_le (n := 2) (p := (1 : ℝ≥0∞)) (μ := moll)
      (ε := ε m) (hεpos m) (by norm_num) hH) hH
  have he := PDE.Analysis.measurePreserving_planeEquivSwap
  have hcomp {g : ℝ^2 → ℝ} (hg : Integrable g) :
      Integrable (fun p ↦ g (PDE.Analysis.planeEquivSwap p)) (volume.prod volume) :=
    (he.integrable_comp_emb PDE.Analysis.planeEquivSwap.measurableEmbedding).2 hg
  obtain ⟨ns, hns, hslice⟩ := exists_subseq_ae_integral_prod_right_tendsto_zero
    (fun m p ↦ ‖Hm m (PDE.Analysis.planeEquivSwap p) - H (PDE.Analysis.planeEquivSwap p)‖)
    (fun m ↦ (hcomp ((hHm m).sub hH1)).norm) <|
      (Approximation.mollify_converges_Lp moll 1 (by norm_num) ε hεpos hε0 hH).congr fun m ↦
        ((eLpNorm_norm _ (hcomp ((hHm m).sub hH1)).aestronglyMeasurable).trans
          (eLpNorm_comp_measurePreserving ((hHm m).sub hH1).aestronglyMeasurable he)).symm
  filter_upwards [hslice, ae_all_iff.2 fun m ↦ (hcomp (hHm m)).prod_right_ae,
    (hcomp hH1).prod_right_ae] with s hs hHmS hHS
  simp only [PDE.Analysis.planeEquivSwap_apply_eq_add] at hs hHmS hHS
  have hlhs : Tendsto (fun i ↦ ∫ r in a..b, Hm (ns i) (q r s)) atTop
      (𝓝 (∫ r in a..b, H (q r s))) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2
      (squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_) hs)
    rw [← intervalIntegral.integral_sub (hHmS _).intervalIntegrable hHS.intervalIntegrable]
    exact intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
      (setIntegral_le_integral ((hHmS _).sub hHS).norm (ae_of_all _ fun _ ↦ norm_nonneg _))
  exact tendsto_nhds_unique (hlhs.congr fun i ↦ hFTC (ns i) s)
    (((Approximation.mollify_tendsto_of_continuous moll hF ε hεpos hε0 (q b s)).sub
      (Approximation.mollify_tendsto_of_continuous moll hF ε hεpos hε0 (q a s))).comp
        hns.tendsto_atTop)

/-- Fixed-interval coordinate FTC on almost every slice of a compact rectangle
inside an open planar domain. No global integrability is assumed: weak local integrability is
converted to `L¹` on a relatively compact intermediate open set, and a
smooth cutoff reduces the result to the global slicing theorem above. -/
theorem ae_intervalIntegral_weakDerivative_firstCoordinate_eq_sub_on_rectangle
    (U : Set (ℝ^2)) (hU : IsOpen U)
    (F H : ℝ^2 → ℝ) (hF : Continuous F)
    (hweak : HasWeakDerivativeOn (n := 2) U [0] F H)
    (a b c d : ℝ)
    (hrect : ∀ r ∈ Set.uIcc a b, ∀ s ∈ Set.Icc c d,
      EuclideanSpace.single 0 r + EuclideanSpace.single 1 s ∈ U) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc c d) : Measure ℝ),
      (∫ r in a..b,
        H (EuclideanSpace.single 0 r + EuclideanSpace.single 1 s)) =
      F (EuclideanSpace.single 0 b + EuclideanSpace.single 1 s) -
        F (EuclideanSpace.single 0 a + EuclideanSpace.single 1 s) := by
  obtain ⟨ψ, hψ1, hψ⟩ := exists_cutoff_hasWeakDerivativeOn hU (subset_univ U)
    ((isCompact_uIcc.prod isCompact_Icc).image continuous_single_add_single)
    (by rintro _ ⟨⟨r, s⟩, hrs, rfl⟩; exact hrect r hrs.1 s hrs.2)
  obtain ⟨hw, -, hint⟩ := hψ hweak
  filter_upwards [ae_restrict_of_ae (ae_intervalIntegral_weakDerivative_firstCoordinate_eq_sub
      (fun x ↦ ψ.toFun x * F x) _ (ψ.contDiff.continuous.mul hF)
      (memLp_one_iff_integrable.2 hint) hw a b),
    ae_restrict_mem measurableSet_Icc] with s hs hscd
  have hpt (r : ℝ) (hr : r ∈ uIcc a b) :=
    cutoff_apply_of_eventuallyEq_one
      (hψ1 (EuclideanSpace.single 0 r + EuclideanSpace.single 1 s) ⟨(r, s), ⟨hr, hscd⟩, rfl⟩) 0 F H
  convert hs using 1
  · exact intervalIntegral.integral_congr fun r hr ↦ (hpt r hr).2.symm
  · rw [(hpt a left_mem_uIcc).1, (hpt b right_mem_uIcc).1]

/-- Fixed-interval radial FTC on almost every line in the slope chart.

This statement concerns the supplied interval `[a,b]`; its exceptional null
set may depend on those endpoints. It is expressed along rays `(r,r*s)` and
requires no global Sobolev norm. -/
theorem ae_intervalIntegral_slopeMap_weakDerivative_eq_sub
    (δ : ℝ) (hδ : 0 < δ) (f gr gz : ℝ^2 → ℝ)
    (hf : Continuous f)
    (hweakr : HasWeakDerivativeOn (n := 2) (radialAway δ) [0] f gr)
    (hweakz : HasWeakDerivativeOn (n := 2) (radialAway δ) [1] f gz)
    (a b c d : ℝ)
    (hrAway : ∀ r ∈ Set.uIcc a b, δ < r) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc c d) : Measure ℝ),
      (∫ r in a..b,
        (gr (slopeMap
            (EuclideanSpace.single 0 r + EuclideanSpace.single 1 s)) +
          s * gz (slopeMap
            (EuclideanSpace.single 0 r + EuclideanSpace.single 1 s)))) =
      f (slopeMap
          (EuclideanSpace.single 0 b + EuclideanSpace.single 1 s)) -
        f (slopeMap
          (EuclideanSpace.single 0 a + EuclideanSpace.single 1 s)) := by
  have hKsub : slopeMap '' ((fun p : ℝ × ℝ ↦ EuclideanSpace.single 0 p.1 +
      EuclideanSpace.single 1 p.2) '' (uIcc a b ×ˢ Icc c d)) ⊆ radialAway δ := by
    rintro _ ⟨x, ⟨⟨r, s⟩, hrs, rfl⟩, rfl⟩
    simpa [radialAway, slopeMap] using hrAway r hrs.1
  obtain ⟨ψ, hψ1, hψ⟩ := exists_cutoff_hasWeakDerivativeOn (isOpen_radialAway δ) subset_rfl
    (((isCompact_uIcc.prod isCompact_Icc).image continuous_single_add_single).image
      contDiff_slopeMap.continuous) hKsub
  obtain ⟨hwr, hF, hGr⟩ := hψ hweakr
  obtain ⟨hwz, -, hGz⟩ := hψ hweakz
  filter_upwards [ae_intervalIntegral_weakDerivative_firstCoordinate_eq_sub_on_rectangle
      (radialAway δ) (isOpen_radialAway δ) (fun x ↦ ψ.toFun (slopeMap x) * f (slopeMap x)) _
      ((ψ.contDiff.continuous.mul hf).comp' contDiff_slopeMap.continuous)
      (hasWeakDerivativeOn_slopeMap_first_of_memLp δ hδ _ _ _
        (memLp_one_iff_integrable.2 hF.integrableOn) (memLp_one_iff_integrable.2 hGr.integrableOn)
        (memLp_one_iff_integrable.2 hGz.integrableOn) hwr hwz)
      a b c d (fun r hr s _ ↦ by simpa [radialAway] using hrAway r hr),
    ae_restrict_mem measurableSet_Icc] with s hs hscd
  have hpt (r : ℝ) (hr : r ∈ uIcc a b) (i : Fin 2) (g : ℝ^2 → ℝ) :=
    cutoff_apply_of_eventuallyEq_one (hψ1 (slopeMap (EuclideanSpace.single 0 r +
      EuclideanSpace.single 1 s)) ⟨_, ⟨(r, s), ⟨hr, hscd⟩, rfl⟩, rfl⟩) i f g
  convert hs using 1
  · exact intervalIntegral.integral_congr fun r hr ↦ by
      simp only [(hpt r hr 0 gr).2, (hpt r hr 1 gz).2]
      simp
  · rw [(hpt a left_mem_uIcc 0 gr).1, (hpt b right_mem_uIcc 0 gr).1]

end Slices
end SobolevSpace
