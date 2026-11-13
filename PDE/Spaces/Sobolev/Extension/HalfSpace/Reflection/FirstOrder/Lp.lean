/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
public import PDE.Spaces.Sobolev.Extension.Lp.ZeroExtension
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Convex.Measure
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Even and odd reflection on `Lp`

The even and odd reflection operators on `Lp` over the upper half-space:

* `evenExtendLp` extends `f` by `f ∘ reflect` on the lower half-space;
* `oddExtendLp` extends `f` by `- f ∘ reflect` on the lower half-space.

These are the core analytic ingredients for the even-reflection extension operator on
`W^{1,p}` of the half-space; the harder step is proving the weak-derivative identities for the
reflected extensions, with weak derivatives in the sense of Evans, PDE, §5.2.1
(`HasWeakDerivativeOn` tests against `C_c^∞(Ω)`). That step is carried out in
`Reflection.FirstOrder.TangentialDerivative` and `HalfSpace.FirstOrder.NormalDerivative`.

## Main results

* `volume_coordinateHyperplane_eq_zero`: every hyperplane `{xᵢ = 0}` is Lebesgue-null, so the
  value of a reflected function on it is immaterial.
* `cutoffAway`, `cutoffAway_eq_zero_of_last_le`, `cutoffAway_eq_one_of_two_mul_le_last`,
  `contDiff_cutoffAway`: the smooth cutoff `η_δ` used to push test functions away from the
  boundary.
* `pullbackLower`, `embedUpper`, `embedLower`: the isometric building blocks (reflection is
  measure preserving between the half-spaces, zero extension is isometric).
* `evenExtendLp`, `oddExtendLp` with their a.e. representatives `evenExtendLp_apply_ae`,
  `oddExtendLp_apply_ae`, and the piecewise forms `*_apply_ae_piecewise_of_ae_eq`.
* `restrict_evenExtendLp`, `restrict_oddExtendLp`, `evenExtendLp_injective`,
  `oddExtendLp_injective`: restriction to `ℝ^n₊` is a left inverse.
* `norm_evenExtendLp`, `norm_oddExtendLp`: in `L²` both reflections scale the norm by exactly
  `√2`, since the upper and reflected lower pieces are orthogonal.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 9, for extension by reflection across a flat boundary.
  <https://doi.org/10.1007/978-0-387-70914-7>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.1, (1)-(3), p. 256, for weak derivatives tested against
  `C_c^∞(U)`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open Set MeasureTheory Function ENNReal
open scoped Topology RealInnerProductSpace

namespace HalfSpace

open SobolevSpace.GraphSpace

/-- Every coordinate hyperplane `{x | x i = 0}` has zero Lebesgue measure: it is the
frontier of the convex half-space `{x | 0 ≤ x i}`. -/
theorem volume_coordinateHyperplane_eq_zero {m : ℕ} (i : Fin m) :
    (volume : Measure (ℝ^m)) (PDE.Common.coordinateHyperplane i) = 0 := by
  have hlinear : IsLinearMap ℝ (fun y : ℝ^m ↦ y i) :=
    (EuclideanSpace.proj i : ℝ^m →L[ℝ] ℝ).isLinear
  have hconv : Convex ℝ {y : ℝ^m | 0 ≤ y i} := convex_halfSpace_ge hlinear 0
  have hnull := Convex.addHaar_frontier (volume : Measure (ℝ^m)) hconv
  rw [frontier_halfSpace 2 0 i] at hnull
  simpa [PDE.Common.coordinateHyperplane, eq_comm] using hnull

variable (n : ℕ) [Fact (0 < n)]
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

local notation "μ₊" => (domainMeasure n ℝ^n₊)
local notation "μ₋" => (domainMeasure n ℝ^n₋)

/-!
## A cutoff vanishing near the boundary

`cutoffAway δ x = 0` for `xₙ ≤ δ` and `cutoffAway δ x = 1` for `xₙ ≥ 2δ` (for `δ > 0`).
This is convenient for building test functions supported strictly inside `ℝ^n₊`.
-/

/-- A smooth normal-direction cutoff that removes a neighborhood of the half-space boundary. -/
noncomputable def cutoffAway (δ : ℝ) : ℝ^n → ℝ :=
  fun x ↦ Real.smoothTransition ((x (PDE.Common.lastIndex (n := n)) - δ) / δ)

/-- `cutoffAway δ` vanishes on the closed strip `xₙ ≤ δ`; in particular it vanishes on a
neighbourhood of the boundary hyperplane and on the whole lower half-space. -/
theorem cutoffAway_eq_zero_of_last_le {δ : ℝ} (hδ : 0 < δ) {x : ℝ^n}
    (hx : x (PDE.Common.lastIndex (n := n)) ≤ δ) :
    cutoffAway (n := n) δ x = 0 := by
  have h : (x (PDE.Common.lastIndex (n := n)) - δ) / δ ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hx) hδ.le
  simp [cutoffAway, Real.smoothTransition.zero_of_nonpos h]

/-- `cutoffAway δ` equals one once `xₙ ≥ 2δ`, so the cutoff only modifies a function on the
strip `δ < xₙ < 2δ`, whose measure (inside any compact set) tends to zero with `δ`. -/
theorem cutoffAway_eq_one_of_two_mul_le_last {δ : ℝ} (hδ : 0 < δ) {x : ℝ^n}
    (hx : 2 * δ ≤ x (PDE.Common.lastIndex (n := n))) :
    cutoffAway (n := n) δ x = 1 := by
  have hx' : δ ≤ x (PDE.Common.lastIndex (n := n)) - δ := by linarith
  have hdiv : (δ / δ) ≤ (x (PDE.Common.lastIndex (n := n)) - δ) / δ := by
    exact div_le_div_of_nonneg_right hx' hδ.le
  have : (1 : ℝ) ≤ (x (PDE.Common.lastIndex (n := n)) - δ) / δ := by
    simpa [hδ.ne'] using hdiv
  simp [cutoffAway, Real.smoothTransition.one_of_one_le this]

variable {n} in
/-- The normal cutoff `cutoffAway δ` is smooth. -/
theorem contDiff_cutoffAway (δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffAway (n := n) δ) := by
  let P : ℝ^n →L[ℝ] ℝ := EuclideanSpace.proj (PDE.Common.lastIndex (n := n))
  change ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ Real.smoothTransition ((P x - δ) / δ))
  exact Real.smoothTransition.contDiff.comp ((P.contDiff.sub contDiff_const).div_const δ)

/-!
## Even and Odd Extension on `Lp`

We implement these as continuous linear maps built from:
* the indicator/zero-extension `Lp(μ.restrict Ω) → Lp(μ)` from `Extension.Lp.ZeroExtension`,
* the measure-preserving pullback along the reflection map on the lower half-space.
-/

/-- The linear isometry transporting an upper-half-space `L^p` class to the lower half-space by
reflection across the boundary hyperplane. -/
noncomputable def pullbackLower :
    DerivLp n p ℝ^n₊ →ₗᵢ[ℝ] DerivLp n p ℝ^n₋ :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (p := p) (E := ℝ)
    (f := SobolevSpace.HalfSpace.reflect n) (μ := μ₋) (μb := μ₊)
    (SobolevSpace.HalfSpace.measurePreserving_reflect_restrict_lower (n := n))

/-- Extend an upper-half-space `L^p` class by zero to the ambient space. -/
noncomputable def embedUpper :
    DerivLp n p ℝ^n₊ →L[ℝ] DerivLp n p Set.univ :=
  SobolevSpace.Extension.Lp.zeroExtendLp (n := n) (p := p) (Ω := ℝ^n₊)
    (measurableSet_upper (n := n))

/-- Extend a lower-half-space `L^p` class by zero to the ambient space. -/
noncomputable def embedLower :
    DerivLp n p ℝ^n₋ →L[ℝ] DerivLp n p Set.univ :=
  SobolevSpace.Extension.Lp.zeroExtendLp (n := n) (p := p) (Ω := ℝ^n₋)
    (measurableSet_lower (n := n))

/-- Extend an upper-half-space `L^p` class evenly by adding its reflected lower-half-space part. -/
noncomputable def evenExtendLp :
    DerivLp n p ℝ^n₊ →L[ℝ] DerivLp n p Set.univ :=
  embedUpper (n := n) (p := p) +
    (embedLower (n := n) (p := p)).comp (pullbackLower (n := n) (p := p)).toContinuousLinearMap

/-- Extend an upper-half-space `L^p` class oddly by subtracting its reflected lower-half-space
part. -/
noncomputable def oddExtendLp :
    DerivLp n p ℝ^n₊ →L[ℝ] DerivLp n p Set.univ :=
  embedUpper (n := n) (p := p) -
    (embedLower (n := n) (p := p)).comp (pullbackLower (n := n) (p := p)).toContinuousLinearMap

/-- The lower pullback is represented by composition with geometric
reflection almost everywhere on the lower half-space. -/
theorem pullbackLower_apply_ae (u : DerivLp n p ℝ^n₊) :
    ((pullbackLower (n := n) (p := p) u : DerivLp n p ℝ^n₋) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n ℝ^n₋]
        fun x ↦ (u : ℝ^n → ℝ) (SobolevSpace.HalfSpace.reflect n x) := by
  change
    (pullbackLower (n := n) (p := p) u : ℝ^n → ℝ)
      =ᵐ[(volume : Measure (ℝ^n)).restrict ℝ^n₋]
        (u : ℝ^n → ℝ) ∘ SobolevSpace.HalfSpace.reflect n
  simpa [pullbackLower] using
    (MeasureTheory.Lp.coeFn_compMeasurePreserving (g := u)
      (SobolevSpace.HalfSpace.measurePreserving_reflect_restrict_lower (n := n)))

private theorem embedLower_pullback_apply_ae (u : DerivLp n p ℝ^n₊) :
    ((embedLower (n := n) (p := p) (pullbackLower (n := n) (p := p) u) :
        DerivLp n p Set.univ) : ℝ^n → ℝ) =ᵐ[volume]
      ℝ^n₋.indicator
        (fun x ↦ (u : ℝ^n → ℝ) (SobolevSpace.HalfSpace.reflect n x)) := by
  have hzero := SobolevSpace.Extension.Lp.zeroExtendLp_apply_ae
    (n := n) (p := p) (measurableSet_lower (n := n))
    (pullbackLower (n := n) (p := p) u)
  have hzeroVolume :
      ((embedLower (n := n) (p := p) (pullbackLower (n := n) (p := p) u) :
          DerivLp n p Set.univ) : ℝ^n → ℝ) =ᵐ[volume]
        SobolevSpace.Extension.Lp.extensionByZero
          (pullbackLower (n := n) (p := p) u) := by
    simpa [embedLower, domainMeasure] using hzero
  have hpb := pullbackLower_apply_ae (n := n) (p := p) u
  have hpbVolume : ∀ᵐ x ∂(volume : Measure (ℝ^n)), x ∈ ℝ^n₋ →
      ((pullbackLower (n := n) (p := p) u : DerivLp n p ℝ^n₋) : ℝ^n → ℝ) x =
        (u : ℝ^n → ℝ) (SobolevSpace.HalfSpace.reflect n x) := by
    simpa [domainMeasure] using
      (MeasureTheory.ae_restrict_iff' (measurableSet_lower (n := n))).1 hpb
  filter_upwards [hzeroVolume, hpbVolume] with x hxzero hxpb
  rw [hxzero]
  by_cases hx : x ∈ ℝ^n₋
  · simp [SobolevSpace.Extension.Lp.extensionByZero,
      Set.indicator_of_mem hx, hxpb hx]
  · simp [SobolevSpace.Extension.Lp.extensionByZero,
      Set.indicator_of_notMem hx]

/-- Almost-everywhere representative of the even `Lp` reflection. -/
theorem evenExtendLp_apply_ae (u : DerivLp n p ℝ^n₊) :
    ((evenExtendLp (n := n) (p := p) u : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[volume]
        fun x ↦ ℝ^n₊.indicator (fun y ↦ (u : ℝ^n → ℝ) y) x +
          ℝ^n₋.indicator
            (fun y ↦ (u : ℝ^n → ℝ) (SobolevSpace.HalfSpace.reflect n y)) x := by
  have hu := SobolevSpace.Extension.Lp.zeroExtendLp_apply_ae
    (n := n) (p := p) (measurableSet_upper (n := n)) u
  have hl := embedLower_pullback_apply_ae (n := n) (p := p) u
  have hadd := MeasureTheory.Lp.coeFn_add
    (embedUpper (n := n) (p := p) u)
    (embedLower (n := n) (p := p) (pullbackLower (n := n) (p := p) u))
  have huVolume :
      ((embedUpper (n := n) (p := p) u : DerivLp n p Set.univ) : ℝ^n → ℝ)
        =ᵐ[volume] SobolevSpace.Extension.Lp.extensionByZero u := by
    simpa [embedUpper, domainMeasure] using hu
  have haddVolume :
      (((embedUpper (n := n) (p := p) u +
          embedLower (n := n) (p := p) (pullbackLower (n := n) (p := p) u) :
            DerivLp n p Set.univ) : ℝ^n → ℝ)) =ᵐ[volume]
        fun x ↦ (embedUpper (n := n) (p := p) u : ℝ^n → ℝ) x +
          (embedLower (n := n) (p := p) (pullbackLower (n := n) (p := p) u) :
            ℝ^n → ℝ) x := by
    have hadd' :
        (((embedUpper (n := n) (p := p) u +
            embedLower (n := n) (p := p) (pullbackLower (n := n) (p := p) u) :
              DerivLp n p Set.univ) : ℝ^n → ℝ)) =ᵐ[volume]
          ((embedUpper (n := n) (p := p) u : ℝ^n → ℝ) +
            (embedLower (n := n) (p := p) (pullbackLower (n := n) (p := p) u) :
              ℝ^n → ℝ)) := by
      simpa [domainMeasure] using hadd
    filter_upwards [hadd'] with x hx
    exact hx
  filter_upwards [huVolume, hl, haddVolume] with x hux hlx hsum
  rw [hux, hlx] at hsum
  simpa [evenExtendLp,
    SobolevSpace.Extension.Lp.extensionByZero] using hsum

/-- Almost-everywhere representative of the odd `Lp` reflection. -/
theorem oddExtendLp_apply_ae (u : DerivLp n p ℝ^n₊) :
    ((oddExtendLp (n := n) (p := p) u : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[volume]
        fun x ↦ ℝ^n₊.indicator (fun y ↦ (u : ℝ^n → ℝ) y) x -
          ℝ^n₋.indicator
            (fun y ↦ (u : ℝ^n → ℝ) (SobolevSpace.HalfSpace.reflect n y)) x := by
  have hu := SobolevSpace.Extension.Lp.zeroExtendLp_apply_ae
    (n := n) (p := p) (measurableSet_upper (n := n)) u
  have hl := embedLower_pullback_apply_ae (n := n) (p := p) u
  have hsub := MeasureTheory.Lp.coeFn_sub
    (embedUpper (n := n) (p := p) u)
    (embedLower (n := n) (p := p) (pullbackLower (n := n) (p := p) u))
  have huVolume :
      ((embedUpper (n := n) (p := p) u : DerivLp n p Set.univ) : ℝ^n → ℝ)
        =ᵐ[volume] SobolevSpace.Extension.Lp.extensionByZero u := by
    simpa [embedUpper, domainMeasure] using hu
  have hsubVolume :
      (((embedUpper (n := n) (p := p) u -
          embedLower (n := n) (p := p) (pullbackLower (n := n) (p := p) u) :
            DerivLp n p Set.univ) : ℝ^n → ℝ)) =ᵐ[volume]
        fun x ↦ (embedUpper (n := n) (p := p) u : ℝ^n → ℝ) x -
          (embedLower (n := n) (p := p) (pullbackLower (n := n) (p := p) u) :
            ℝ^n → ℝ) x := by
    have hsub' :
        (((embedUpper (n := n) (p := p) u -
            embedLower (n := n) (p := p) (pullbackLower (n := n) (p := p) u) :
              DerivLp n p Set.univ) : ℝ^n → ℝ)) =ᵐ[volume]
          ((embedUpper (n := n) (p := p) u : ℝ^n → ℝ) -
            (embedLower (n := n) (p := p) (pullbackLower (n := n) (p := p) u) :
              ℝ^n → ℝ)) := by
      simpa [domainMeasure] using hsub
    filter_upwards [hsub'] with x hx
    exact hx
  filter_upwards [huVolume, hl, hsubVolume] with x hux hlx hdiff
  rw [hux, hlx] at hdiff
  simpa [oddExtendLp,
    SobolevSpace.Extension.Lp.extensionByZero] using hdiff

/-- Transfer a concrete upper-half-space representative through even `Lp`
reflection. -/
theorem evenExtendLp_apply_ae_of_ae_eq (u : DerivLp n p ℝ^n₊)
    (f : ℝ^n → ℝ)
    (hu : (u : ℝ^n → ℝ) =ᵐ[domainMeasure n ℝ^n₊] f) :
    ((evenExtendLp (n := n) (p := p) u : DerivLp n p Set.univ) :
        ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ ℝ^n₊.indicator f x +
        ℝ^n₋.indicator (fun y ↦ f (SobolevSpace.HalfSpace.reflect n y)) x := by
  have huVolume : ∀ᵐ x ∂(volume : Measure (ℝ^n)), x ∈ ℝ^n₊ →
      (u : ℝ^n → ℝ) x = f x := by
    simpa [domainMeasure] using
      (MeasureTheory.ae_restrict_iff' (measurableSet_upper (n := n))).1 hu
  have hreflect :=
    (SobolevSpace.HalfSpace.measurePreserving_reflect_restrict_lower
      (n := n)).quasiMeasurePreserving.ae_eq_comp hu
  have hreflectVolume : ∀ᵐ x ∂(volume : Measure (ℝ^n)), x ∈ ℝ^n₋ →
      (u : ℝ^n → ℝ) (SobolevSpace.HalfSpace.reflect n x) =
        f (SobolevSpace.HalfSpace.reflect n x) := by
    simpa [domainMeasure] using
      (MeasureTheory.ae_restrict_iff' (measurableSet_lower (n := n))).1 hreflect
  filter_upwards [evenExtendLp_apply_ae (n := n) (p := p) u,
    huVolume, hreflectVolume] with x hext hux hrefx
  rw [hext]
  by_cases hxU : x ∈ ℝ^n₊ <;> by_cases hxL : x ∈ ℝ^n₋ <;>
    simp [hxU, hxL, hux, hrefx]

/-- Transfer a concrete upper-half-space representative through odd `Lp`
reflection. -/
theorem oddExtendLp_apply_ae_of_ae_eq (u : DerivLp n p ℝ^n₊)
    (f : ℝ^n → ℝ)
    (hu : (u : ℝ^n → ℝ) =ᵐ[domainMeasure n ℝ^n₊] f) :
    ((oddExtendLp (n := n) (p := p) u : DerivLp n p Set.univ) :
        ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ ℝ^n₊.indicator f x -
        ℝ^n₋.indicator (fun y ↦ f (SobolevSpace.HalfSpace.reflect n y)) x := by
  have huVolume : ∀ᵐ x ∂(volume : Measure (ℝ^n)), x ∈ ℝ^n₊ →
      (u : ℝ^n → ℝ) x = f x := by
    simpa [domainMeasure] using
      (MeasureTheory.ae_restrict_iff' (measurableSet_upper (n := n))).1 hu
  have hreflect :=
    (SobolevSpace.HalfSpace.measurePreserving_reflect_restrict_lower
      (n := n)).quasiMeasurePreserving.ae_eq_comp hu
  have hreflectVolume : ∀ᵐ x ∂(volume : Measure (ℝ^n)), x ∈ ℝ^n₋ →
      (u : ℝ^n → ℝ) (SobolevSpace.HalfSpace.reflect n x) =
        f (SobolevSpace.HalfSpace.reflect n x) := by
    simpa [domainMeasure] using
      (MeasureTheory.ae_restrict_iff' (measurableSet_lower (n := n))).1 hreflect
  filter_upwards [oddExtendLp_apply_ae (n := n) (p := p) u,
    huVolume, hreflectVolume] with x hext hux hrefx
  rw [hext]
  by_cases hxU : x ∈ ℝ^n₊ <;> by_cases hxL : x ∈ ℝ^n₋ <;>
    simp [hxU, hxL, hux, hrefx]

/-- Literal piecewise representative of an even `Lp` reflection.  Its value
on the reflecting hyperplane is irrelevant and is removed by the hyperplane
null-set theorem. -/
theorem evenExtendLp_apply_ae_piecewise_of_ae_eq (u : DerivLp n p ℝ^n₊)
    (f : ℝ^n → ℝ)
    (hu : (u : ℝ^n → ℝ) =ᵐ[domainMeasure n ℝ^n₊] f) :
    ((evenExtendLp (n := n) (p := p) u : DerivLp n p Set.univ) :
        ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ if x (PDE.Common.lastIndex (n := n)) < 0 then
        f (SobolevSpace.HalfSpace.reflect n x) else f x := by
  have haxis : ∀ᵐ x ∂(volume : Measure (ℝ^n)), x ∉ boundary n := by
    rw [MeasureTheory.ae_iff]
    simpa using volume_boundary n
  filter_upwards [evenExtendLp_apply_ae_of_ae_eq
    (n := n) (p := p) u f hu, haxis] with x hx hxb
  rw [hx]
  have hne : x (PDE.Common.lastIndex (n := n)) ≠ 0 := by
    simpa [boundary] using hxb
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · simp [upper, lower, hneg, not_lt.mpr hneg.le]
  · simp [upper, lower, hpos, not_lt.mpr hpos.le]

/-- Literal piecewise representative of an odd `Lp` reflection. -/
theorem oddExtendLp_apply_ae_piecewise_of_ae_eq (u : DerivLp n p ℝ^n₊)
    (f : ℝ^n → ℝ)
    (hu : (u : ℝ^n → ℝ) =ᵐ[domainMeasure n ℝ^n₊] f) :
    ((oddExtendLp (n := n) (p := p) u : DerivLp n p Set.univ) :
        ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ if x (PDE.Common.lastIndex (n := n)) < 0 then
        -f (SobolevSpace.HalfSpace.reflect n x) else f x := by
  have haxis : ∀ᵐ x ∂(volume : Measure (ℝ^n)), x ∉ boundary n := by
    rw [MeasureTheory.ae_iff]
    simpa using volume_boundary n
  filter_upwards [oddExtendLp_apply_ae_of_ae_eq
    (n := n) (p := p) u f hu, haxis] with x hx hxb
  rw [hx]
  have hne : x (PDE.Common.lastIndex (n := n)) ≠ 0 := by
    simpa [boundary] using hxb
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · simp [upper, lower, hneg, not_lt.mpr hneg.le]
  · simp [upper, lower, hpos, not_lt.mpr hpos.le]

/-- Restricting an even reflection back to the upper half-space recovers the
original `Lᵖ` class. -/
@[simp] theorem restrict_evenExtendLp (u : DerivLp n p ℝ^n₊) :
    GraphSpace.restrictDerivLp
        (n := n) (p := p)
        (subset_univ ℝ^n₊)
        (evenExtendLp (n := n) (p := p) u) =
      u := by
  apply MeasureTheory.Lp.ext
  have hrestrict := GraphSpace.restrictDerivLp_apply_ae
    (n := n) (p := p)
    (subset_univ ℝ^n₊) (evenExtendLp (n := n) (p := p) u)
  have hext := evenExtendLp_apply_ae_piecewise_of_ae_eq
    (n := n) (p := p) u (u : ℝ^n → ℝ) (MeasureTheory.ae_eq_refl _)
  have hextUpper :
      ∀ᵐ x ∂ domainMeasure n ℝ^n₊,
        ((evenExtendLp (n := n) (p := p) u :
            DerivLp n p Set.univ) : ℝ^n → ℝ) x =
          if x (PDE.Common.lastIndex (n := n)) < 0 then
            (u : ℝ^n → ℝ) (SobolevSpace.HalfSpace.reflect n x) else u x := by
    simpa [domainMeasure] using
      MeasureTheory.ae_restrict_of_ae (s := ℝ^n₊) hext
  have hmem :
      ∀ᵐ x ∂ domainMeasure n ℝ^n₊, x ∈ ℝ^n₊ := by
    simpa [domainMeasure] using
      (MeasureTheory.ae_restrict_mem (measurableSet_upper (n := n)) :
        ∀ᵐ x ∂ (MeasureTheory.volume : Measure (ℝ^n)).restrict ℝ^n₊, x ∈ ℝ^n₊)
  filter_upwards [hrestrict, hextUpper, hmem] with x hr he hx
  rw [hr, he]
  have hpos : 0 < x (PDE.Common.lastIndex (n := n)) := by
    simpa [upper] using hx
  simp [not_lt.mpr hpos.le]

/-- Restricting an odd reflection back to the upper half-space recovers the
original `Lᵖ` class. -/
@[simp] theorem restrict_oddExtendLp (u : DerivLp n p ℝ^n₊) :
    GraphSpace.restrictDerivLp
        (n := n) (p := p)
        (subset_univ ℝ^n₊)
        (oddExtendLp (n := n) (p := p) u) =
      u := by
  apply MeasureTheory.Lp.ext
  have hrestrict := GraphSpace.restrictDerivLp_apply_ae
    (n := n) (p := p)
    (subset_univ ℝ^n₊) (oddExtendLp (n := n) (p := p) u)
  have hext := oddExtendLp_apply_ae_piecewise_of_ae_eq
    (n := n) (p := p) u (u : ℝ^n → ℝ) (MeasureTheory.ae_eq_refl _)
  have hextUpper :
      ∀ᵐ x ∂ domainMeasure n ℝ^n₊,
        ((oddExtendLp (n := n) (p := p) u :
            DerivLp n p Set.univ) : ℝ^n → ℝ) x =
          if x (PDE.Common.lastIndex (n := n)) < 0 then
            -(u : ℝ^n → ℝ) (SobolevSpace.HalfSpace.reflect n x) else u x := by
    simpa [domainMeasure] using
      MeasureTheory.ae_restrict_of_ae (s := ℝ^n₊) hext
  have hmem :
      ∀ᵐ x ∂ domainMeasure n ℝ^n₊, x ∈ ℝ^n₊ := by
    simpa [domainMeasure] using
      (MeasureTheory.ae_restrict_mem (measurableSet_upper (n := n)) :
        ∀ᵐ x ∂ (MeasureTheory.volume : Measure (ℝ^n)).restrict ℝ^n₊, x ∈ ℝ^n₊)
  filter_upwards [hrestrict, hextUpper, hmem] with x hr he hx
  rw [hr, he]
  have hpos : 0 < x (PDE.Common.lastIndex (n := n)) := by
    simpa [upper] using hx
  simp [not_lt.mpr hpos.le]

/-- Scalar even reflection is injective. -/
theorem evenExtendLp_injective :
    Function.Injective (evenExtendLp (n := n) (p := p)) := by
  intro u v huv
  have hrestrict := congrArg
    (GraphSpace.restrictDerivLp
      (n := n) (p := p)
      (subset_univ ℝ^n₊))
    huv
  simpa using hrestrict

/-- Scalar odd reflection is injective. -/
theorem oddExtendLp_injective :
    Function.Injective (oddExtendLp (n := n) (p := p)) := by
  intro u v huv
  have hrestrict := congrArg
    (GraphSpace.restrictDerivLp
      (n := n) (p := p)
      (subset_univ ℝ^n₊))
    huv
  simpa using hrestrict

section L2Norm

/-- Upper and lower zero extensions have disjoint supports and are therefore
orthogonal in global `L²`. -/
private theorem inner_embedUpper_embedLower_eq_zero
    (u : DerivLp n 2 ℝ^n₊) (v : DerivLp n 2 ℝ^n₋) :
    inner ℝ
      (embedUpper (n := n) (p := (2 : ℝ≥0∞)) u : DerivLp n 2 Set.univ)
      (embedLower (n := n) (p := (2 : ℝ≥0∞)) v : DerivLp n 2 Set.univ) = 0 := by
  rw [MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_eq_zero_of_ae
  have hu := SobolevSpace.Extension.Lp.zeroExtendLp_apply_ae
    (n := n) (p := (2 : ℝ≥0∞)) (measurableSet_upper (n := n)) u
  have hv := SobolevSpace.Extension.Lp.zeroExtendLp_apply_ae
    (n := n) (p := (2 : ℝ≥0∞)) (measurableSet_lower (n := n)) v
  filter_upwards [hu, hv] with x hux hvx
  change
    ((embedUpper (n := n) (p := (2 : ℝ≥0∞)) u : DerivLp n 2 Set.univ) : ℝ^n → ℝ) x =
      SobolevSpace.Extension.Lp.extensionByZero u x at hux
  change
    ((embedLower (n := n) (p := (2 : ℝ≥0∞)) v : DerivLp n 2 Set.univ) : ℝ^n → ℝ) x =
      SobolevSpace.Extension.Lp.extensionByZero v x at hvx
  change
    inner ℝ
      ((embedUpper (n := n) (p := (2 : ℝ≥0∞)) u : DerivLp n 2 Set.univ) x)
      ((embedLower (n := n) (p := (2 : ℝ≥0∞)) v : DerivLp n 2 Set.univ) x) = 0
  rw [hux, hvx]
  by_cases hxU : x ∈ ℝ^n₊
  · have hxL : x ∉ ℝ^n₋ := by
      have hxPos : 0 < x (PDE.Common.lastIndex (n := n)) := hxU
      simpa [SobolevSpace.HalfSpace.lower] using (not_lt_of_ge hxPos.le)
    simp [SobolevSpace.Extension.Lp.extensionByZero, hxU, hxL]
  · simp [SobolevSpace.Extension.Lp.extensionByZero, hxU]

/-- Every scalar even reflection doubles the squared `L²` norm. -/
theorem norm_evenExtendLp_sq (u : DerivLp n 2 ℝ^n₊) :
    ‖evenExtendLp (n := n) (p := (2 : ℝ≥0∞)) u‖ ^ 2 =
      2 * ‖u‖ ^ 2 := by
  let v := pullbackLower (n := n) (p := (2 : ℝ≥0∞)) u
  have horth := inner_embedUpper_embedLower_eq_zero (n := n) u v
  calc
    ‖evenExtendLp (n := n) (p := (2 : ℝ≥0∞)) u‖ ^ 2 =
        ‖embedUpper (n := n) (p := (2 : ℝ≥0∞)) u +
          embedLower (n := n) (p := (2 : ℝ≥0∞)) v‖ ^ 2 := by
            rfl
    _ = ‖embedUpper (n := n) (p := (2 : ℝ≥0∞)) u‖ ^ 2 +
        ‖embedLower (n := n) (p := (2 : ℝ≥0∞)) v‖ ^ 2 :=
      by simpa [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
    _ = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
      rw [show ‖embedUpper (n := n) (p := (2 : ℝ≥0∞)) u‖ = ‖u‖ by
          exact SobolevSpace.Extension.Lp.norm_zeroExtendLp
            (n := n) (p := (2 : ℝ≥0∞)) (measurableSet_upper (n := n)) u,
        show ‖embedLower (n := n) (p := (2 : ℝ≥0∞)) v‖ = ‖v‖ by
          exact SobolevSpace.Extension.Lp.norm_zeroExtendLp
            (n := n) (p := (2 : ℝ≥0∞)) (measurableSet_lower (n := n)) v]
    _ = 2 * ‖u‖ ^ 2 := by
      have hvnorm : ‖v‖ = ‖u‖ := by
        exact (pullbackLower (n := n) (p := (2 : ℝ≥0∞))).norm_map u
      rw [hvnorm]
      ring

/-- Every scalar even reflection multiplies the `L²` norm by `√2`. -/
theorem norm_evenExtendLp (u : DerivLp n 2 ℝ^n₊) :
    ‖evenExtendLp (n := n) (p := (2 : ℝ≥0∞)) u‖ =
      Real.sqrt 2 * ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg _))).mp
  rw [norm_evenExtendLp_sq, mul_pow, Real.sq_sqrt (by norm_num)]

/-- Every scalar odd reflection has the same exact squared-norm factor. -/
theorem norm_oddExtendLp_sq (u : DerivLp n 2 ℝ^n₊) :
    ‖oddExtendLp (n := n) (p := (2 : ℝ≥0∞)) u‖ ^ 2 =
      2 * ‖u‖ ^ 2 := by
  let v := pullbackLower (n := n) (p := (2 : ℝ≥0∞)) u
  have horth := inner_embedUpper_embedLower_eq_zero (n := n) u v
  calc
    ‖oddExtendLp (n := n) (p := (2 : ℝ≥0∞)) u‖ ^ 2 =
        ‖embedUpper (n := n) (p := (2 : ℝ≥0∞)) u -
          embedLower (n := n) (p := (2 : ℝ≥0∞)) v‖ ^ 2 := by
            rfl
    _ = ‖embedUpper (n := n) (p := (2 : ℝ≥0∞)) u‖ ^ 2 +
        ‖embedLower (n := n) (p := (2 : ℝ≥0∞)) v‖ ^ 2 :=
      by simpa [pow_two] using norm_sub_sq_eq_norm_sq_add_norm_sq_real horth
    _ = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
      rw [show ‖embedUpper (n := n) (p := (2 : ℝ≥0∞)) u‖ = ‖u‖ by
          exact SobolevSpace.Extension.Lp.norm_zeroExtendLp
            (n := n) (p := (2 : ℝ≥0∞)) (measurableSet_upper (n := n)) u,
        show ‖embedLower (n := n) (p := (2 : ℝ≥0∞)) v‖ = ‖v‖ by
          exact SobolevSpace.Extension.Lp.norm_zeroExtendLp
            (n := n) (p := (2 : ℝ≥0∞)) (measurableSet_lower (n := n)) v]
    _ = 2 * ‖u‖ ^ 2 := by
      have hvnorm : ‖v‖ = ‖u‖ := by
        exact (pullbackLower (n := n) (p := (2 : ℝ≥0∞))).norm_map u
      rw [hvnorm]
      ring

/-- Every scalar odd reflection multiplies the `L²` norm by `√2`. -/
theorem norm_oddExtendLp (u : DerivLp n 2 ℝ^n₊) :
    ‖oddExtendLp (n := n) (p := (2 : ℝ≥0∞)) u‖ =
      Real.sqrt 2 * ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg _))).mp
  rw [norm_oddExtendLp_sq, mul_pow, Real.sq_sqrt (by norm_num)]

end L2Norm

end HalfSpace

end SobolevSpace
