/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IndicatorExtension
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Restriction

/-!
# Zero extension on `Lp`

For a measurable set `Ω`, we bundle indicator extension
`u ↦ Ω.indicator u` as a continuous linear map from `L^p(Ω)` to
`L^p(ℝ^n)`, backed by its canonical linear-isometry structure. We prove the
almost-everywhere formula, exact norm preservation, agreement on `Ω`, the
restriction left-inverse law, and the cutoff identities used by Sobolev
extension constructions.

The order-zero Sobolev graph-space operator is in
`PDE.Spaces.Sobolev.Extension.GraphSpace.Operator.ZeroOrder`.

Extension by zero is the `L^p` half of every Sobolev extension operator built here: the
half-space reflection operator is `embedUpper + embedLower ∘ pullback`, where both embeddings
are instances of `zeroExtendLp`. At Sobolev order `k ≥ 1` zero extension alone does not
preserve weak derivatives (Evans, PDE, §5.4), which is why the reflection and cutoff machinery
is needed on top of it.

## Main results

* `extensionByZero`, `zeroExtendLpₗᵢ`, `zeroExtendLp`: the indicator extension as a function,
  a linear isometry, and a continuous linear map `L^p(Ω) → L^p(ℝ^n)`.
* `zeroExtendLp_apply_ae`, `zeroExtendLp_agree_ae`: a.e. formulas on `ℝ^n` and on `Ω`.
* `integral_zeroExtendLp_mul`: pairing a zero extension with `f` integrates `u f` over `Ω`.
* `norm_zeroExtendLp`, `zeroExtendLp_injective`: exact norm preservation and injectivity.
* `inner_zeroExtendLp_eq_inner_restrict`: in real `L²`, restriction to `Ω` is the adjoint of
  zero extension.
* `zeroExtendLp_restrict_lpSMul`, `zeroExtendLp_testFunction_smul_restrict`: compatibility with
  multiplication by (restricted) bounded functions and by cutoffs supported in `Ω`.
* `restrict_zeroExtendLp`, `restrictDerivLp_comp_zeroExtendLp`: restriction is a left inverse.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, p. 268, the remark before Theorem 1 that extension by
  zero does not in general preserve weak first derivatives.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open MeasureTheory Set Function ENNReal

namespace Extension
namespace Lp

open SobolevSpace.GraphSpace

open MeasureTheory
open Set

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- Zero extension on the level of functions: `u ↦ 1_Ω u`. -/
noncomputable def extensionByZero (u : DerivLp n p Ω) : ℝ^n → ℝ :=
  Ω.indicator fun x ↦ (u : ℝ^n → ℝ) x

/-- The identity map is measure preserving from Lebesgue measure restricted to the whole
space to Lebesgue measure. -/
theorem measurePreserving_id_univ :
    MeasurePreserving (id : ℝ^n → ℝ^n)
      (MeasureTheory.volume.restrict Set.univ) MeasureTheory.volume := by
  simpa only [Measure.restrict_univ] using
    (MeasurePreserving.id (MeasureTheory.volume : Measure (ℝ^n)))

/-- Zero extension on `Lp` as a linear isometry. -/
noncomputable def zeroExtendLpₗᵢ (hΩmeas : MeasurableSet Ω) :
    DerivLp n p Ω →ₗᵢ[ℝ] DerivLp n p Set.univ :=
  (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ id
      (measurePreserving_id_univ (n := n))).comp
    (MeasureTheory.Lp.extendByZeroₗᵢ
      (E := ℝ) (𝕜 := ℝ) (μ := (MeasureTheory.volume : Measure (ℝ^n)))
      (p := p) hΩmeas)

/-- Zero extension on `Lp`: `u ↦ 1_Ω u` as a continuous linear map. -/
noncomputable def zeroExtendLp (hΩmeas : MeasurableSet Ω) :
    DerivLp n p Ω →L[ℝ] DerivLp n p Set.univ :=
  (zeroExtendLpₗᵢ (n := n) (p := p) (Ω := Ω) hΩmeas).toContinuousLinearMap

/-- The continuous linear zero extension is represented by the indicator extension almost
everywhere. -/
theorem zeroExtendLp_apply_ae (hΩmeas : MeasurableSet Ω) (u : DerivLp n p Ω) :
    (zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas u : ℝ^n → ℝ) =ᵐ[
        domainMeasure n (Set.univ : Set (ℝ^n))]
      extensionByZero (n := n) (p := p) (Ω := Ω) u := by
  have hzero := MeasureTheory.Lp.extendByZeroₗᵢ_apply_ae
    (E := ℝ) (𝕜 := ℝ) (μ := (MeasureTheory.volume : Measure (ℝ^n)))
    (p := p) hΩmeas u
  have htransport := MeasureTheory.Lp.coeFn_compMeasurePreserving
    ((MeasureTheory.Lp.extendByZeroₗᵢ
      (E := ℝ) (𝕜 := ℝ) (μ := (MeasureTheory.volume : Measure (ℝ^n)))
      (p := p) hΩmeas) u)
    (measurePreserving_id_univ (n := n))
  change
    (MeasureTheory.Lp.compMeasurePreserving id
      (measurePreserving_id_univ (n := n))
      ((MeasureTheory.Lp.extendByZeroₗᵢ
        (E := ℝ) (𝕜 := ℝ) (μ := (MeasureTheory.volume : Measure (ℝ^n)))
        (p := p) hΩmeas) u) : ℝ^n → ℝ) =ᵐ[
      MeasureTheory.volume.restrict Set.univ]
        extensionByZero (n := n) (p := p) (Ω := Ω) u
  filter_upwards [htransport,
    show (MeasureTheory.Lp.extendByZeroₗᵢ
        (E := ℝ) (𝕜 := ℝ) (μ := (MeasureTheory.volume : Measure (ℝ^n)))
        (p := p) hΩmeas u : ℝ^n → ℝ) =ᵐ[
          MeasureTheory.volume.restrict Set.univ]
        extensionByZero (n := n) (p := p) (Ω := Ω) u by
      simpa only [Measure.restrict_univ, extensionByZero] using hzero] with
      x hxtransport hxzero
  simpa using hxtransport.trans hxzero

/-- Pairing a zero extension with any function reduces to integration on its domain. -/
theorem integral_zeroExtendLp_mul (hΩmeas : MeasurableSet Ω) (u : DerivLp n p Ω)
    (f : ℝ^n → ℝ) :
    (∫ x, zeroExtendLp hΩmeas u x * f x) = ∫ x in Ω, u x * f x := by
  have h := zeroExtendLp_apply_ae hΩmeas u
  simp only [domainMeasure, Measure.restrict_univ] at h
  calc
    _ = ∫ x, Ω.indicator (fun x ↦ u x * f x) x := by
      apply integral_congr_ae
      filter_upwards [h] with x hx
      rw [hx, extensionByZero]
      by_cases hxΩ : x ∈ Ω <;> simp [hxΩ]
    _ = _ := integral_indicator hΩmeas

/-- Zero extension is an isometry from `L^p(volume.restrict Ω)` into
`L^p(volume)`. -/
theorem norm_zeroExtendLp (hΩmeas : MeasurableSet Ω) (u : DerivLp n p Ω) :
    ‖zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas u‖ = ‖u‖ :=
  (zeroExtendLpₗᵢ (n := n) (p := p) (Ω := Ω) hΩmeas).norm_map u

/-- Zero extension on `Lp` is injective. -/
theorem zeroExtendLp_injective (hΩmeas : MeasurableSet Ω) :
    Function.Injective (zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas) :=
  (zeroExtendLpₗᵢ (n := n) (p := p) (Ω := Ω) hΩmeas).injective

/-- On real `L²`, restriction to `Ω` is the Hilbert-space adjoint of
extension by zero from `Ω`.  This identity is the local/global bridge used
when applying whole-space translation and difference-quotient formulas to
weak equations posed on a domain. -/
theorem inner_zeroExtendLp_eq_inner_restrict
    (hΩmeas : MeasurableSet Ω)
    (u : DerivLp n 2 Ω) (v : DerivLp n 2 Set.univ) :
    inner ℝ
        (zeroExtendLp (n := n) (p := 2) (Ω := Ω) hΩmeas u) v =
      inner ℝ u
        (SobolevSpace.GraphSpace.restrictDerivLp
          (n := n) (p := 2) (Ω := Ω) (Ωbig := Set.univ)
          (Set.subset_univ Ω) v) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  let F : ℝ^n → ℝ := fun x ↦ inner ℝ
    ((zeroExtendLp (n := n) (p := 2) (Ω := Ω) hΩmeas u :
      DerivLp n 2 Set.univ) x) (v x)
  let G : ℝ^n → ℝ := fun x ↦ inner ℝ (u x)
    ((SobolevSpace.GraphSpace.restrictDerivLp
      (n := n) (p := 2) (Ω := Ω) (Ωbig := Set.univ)
      (Set.subset_univ Ω) v) x)
  have hzero := zeroExtendLp_apply_ae
    (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) hΩmeas u
  have hrestrict := SobolevSpace.GraphSpace.restrictDerivLp_apply_ae
    (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) (Ωbig := Set.univ)
    (Set.subset_univ Ω) v
  have hrestrictImp :
      ∀ᵐ x ∂MeasureTheory.volume, x ∈ Ω →
        ((SobolevSpace.GraphSpace.restrictDerivLp
          (n := n) (p := 2) (Ω := Ω) (Ωbig := Set.univ)
          (Set.subset_univ Ω) v : DerivLp n 2 Ω) x) = v x := by
    apply (MeasureTheory.ae_restrict_iff' hΩmeas).1
    change
      ((SobolevSpace.GraphSpace.restrictDerivLp
        (n := n) (p := 2) (Ω := Ω) (Ωbig := Set.univ)
        (Set.subset_univ Ω) v : DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[
          MeasureTheory.volume.restrict Ω] (v : ℝ^n → ℝ) at hrestrict
    filter_upwards [hrestrict] with x hx
    exact hx
  have hpointwise : F =ᵐ[MeasureTheory.volume] Ω.indicator G := by
    filter_upwards [show
      (zeroExtendLp (n := n) (p := 2) (Ω := Ω) hΩmeas u :
          ℝ^n → ℝ) =ᵐ[MeasureTheory.volume]
        extensionByZero (n := n) (p := 2) (Ω := Ω) u by
      simpa [domainMeasure] using hzero,
      hrestrictImp] with x hxzero hxrestrict
    by_cases hx : x ∈ Ω
    · rw [show F x = inner ℝ
          ((zeroExtendLp (n := n) (p := 2) (Ω := Ω) hΩmeas u :
            DerivLp n 2 Set.univ) x) (v x) by rfl,
        hxzero, Set.indicator_of_mem hx]
      change inner ℝ (extensionByZero (n := n) (p := 2) (Ω := Ω) u x) (v x) =
        inner ℝ (u x)
          ((SobolevSpace.GraphSpace.restrictDerivLp
            (n := n) (p := 2) (Ω := Ω) (Ωbig := Set.univ)
            (Set.subset_univ Ω) v) x)
      rw [hxrestrict hx]
      simp [extensionByZero, hx]
    · rw [show F x = inner ℝ
          ((zeroExtendLp (n := n) (p := 2) (Ω := Ω) hΩmeas u :
            DerivLp n 2 Set.univ) x) (v x) by rfl,
        hxzero, Set.indicator_of_notMem hx]
      simp [extensionByZero, hx]
  change (∫ x, F x ∂domainMeasure n Set.univ) =
    ∫ x, G x ∂domainMeasure n Ω
  calc
    (∫ x, F x ∂domainMeasure n Set.univ) =
        ∫ x, F x ∂MeasureTheory.volume := by
      congr 1
      simp [domainMeasure]
    _ = ∫ x, Ω.indicator G x ∂MeasureTheory.volume :=
      MeasureTheory.integral_congr_ae hpointwise
    _ = ∫ x, G x ∂(MeasureTheory.volume.restrict Ω) :=
      MeasureTheory.integral_indicator hΩmeas
    _ = ∫ x, G x ∂domainMeasure n Ω := by
      rfl

/-- Zero extension commutes with multiplication by the restriction of a
global bounded coefficient.  Equivalently,
`E₀((a|Ω)u) = a E₀u`.  This is the exact localization identity needed
before applying whole-space difference-quotient product rules. -/
theorem zeroExtendLp_restrict_lpSMul
    (hΩmeas : MeasurableSet Ω)
    (a : DerivLp n ∞ Set.univ) (u : DerivLp n 2 Ω) :
    zeroExtendLp (n := n) (p := 2) (Ω := Ω) hΩmeas
        ((SobolevSpace.GraphSpace.restrictDerivLp
          (n := n) (p := ∞) (Ω := Ω) (Ωbig := Set.univ)
          (Set.subset_univ Ω) a) • u) =
      a • zeroExtendLp (n := n) (p := 2) (Ω := Ω) hΩmeas u := by
  apply MeasureTheory.Lp.ext
  have hleft := zeroExtendLp_apply_ae
    (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) hΩmeas
    ((SobolevSpace.GraphSpace.restrictDerivLp
      (n := n) (p := ∞) (Ω := Ω) (Ωbig := Set.univ)
      (Set.subset_univ Ω) a) • u)
  have hzero := zeroExtendLp_apply_ae
    (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) hΩmeas u
  have hright := SobolevSpace.GraphSpace.mulLpLeft_apply_ae
    (n := n) (p := (2 : ℝ≥0∞)) a
    (zeroExtendLp (n := n) (p := 2) (Ω := Ω) hΩmeas u)
  have hrestrict := SobolevSpace.GraphSpace.restrictDerivLp_apply_ae
    (n := n) (p := (∞ : ℝ≥0∞)) (Ω := Ω) (Ωbig := Set.univ)
    (Set.subset_univ Ω) a
  have hlocalMul := SobolevSpace.GraphSpace.mulLpLeft_apply_ae
    (n := n) (p := (2 : ℝ≥0∞))
    (SobolevSpace.GraphSpace.restrictDerivLp
      (n := n) (p := ∞) (Ω := Ω) (Ωbig := Set.univ)
      (Set.subset_univ Ω) a) u
  have hrestrictImp :
      ∀ᵐ x ∂MeasureTheory.volume, x ∈ Ω →
        ((SobolevSpace.GraphSpace.restrictDerivLp
          (n := n) (p := ∞) (Ω := Ω) (Ωbig := Set.univ)
          (Set.subset_univ Ω) a : DerivLp n ∞ Ω) x) = a x := by
    apply (MeasureTheory.ae_restrict_iff' hΩmeas).1
    change
      ((SobolevSpace.GraphSpace.restrictDerivLp
        (n := n) (p := ∞) (Ω := Ω) (Ωbig := Set.univ)
        (Set.subset_univ Ω) a : DerivLp n ∞ Ω) : ℝ^n → ℝ) =ᵐ[
          MeasureTheory.volume.restrict Ω] (a : ℝ^n → ℝ) at hrestrict
    filter_upwards [hrestrict] with x hx
    exact hx
  have hlocalMulImp :
      ∀ᵐ x ∂MeasureTheory.volume, x ∈ Ω →
        (((SobolevSpace.GraphSpace.restrictDerivLp
          (n := n) (p := ∞) (Ω := Ω) (Ωbig := Set.univ)
          (Set.subset_univ Ω) a) • u : DerivLp n 2 Ω) x) =
          (SobolevSpace.GraphSpace.restrictDerivLp
            (n := n) (p := ∞) (Ω := Ω) (Ωbig := Set.univ)
            (Set.subset_univ Ω) a) x * u x := by
    apply (MeasureTheory.ae_restrict_iff' hΩmeas).1
    filter_upwards [hlocalMul] with x hx
    exact hx
  filter_upwards [hleft, hzero,
    show ((a • zeroExtendLp (n := n) (p := 2) (Ω := Ω) hΩmeas u :
        DerivLp n 2 Set.univ) : ℝ^n → ℝ) =ᵐ[domainMeasure n Set.univ]
          fun x ↦ a x * zeroExtendLp (n := n) (p := 2) (Ω := Ω) hΩmeas u x by
      simpa only [SobolevSpace.GraphSpace.mulLpLeft_apply] using hright,
    show ∀ᵐ x ∂domainMeasure n Set.univ, x ∈ Ω →
        ((SobolevSpace.GraphSpace.restrictDerivLp
          (n := n) (p := ∞) (Ω := Ω) (Ωbig := Set.univ)
          (Set.subset_univ Ω) a : DerivLp n ∞ Ω) x) = a x by
      simpa [domainMeasure] using hrestrictImp,
    show ∀ᵐ x ∂domainMeasure n Set.univ, x ∈ Ω →
        (((SobolevSpace.GraphSpace.restrictDerivLp
          (n := n) (p := ∞) (Ω := Ω) (Ωbig := Set.univ)
          (Set.subset_univ Ω) a) • u : DerivLp n 2 Ω) x) =
          (SobolevSpace.GraphSpace.restrictDerivLp
            (n := n) (p := ∞) (Ω := Ω) (Ωbig := Set.univ)
            (Set.subset_univ Ω) a) x * u x by
      simpa [domainMeasure] using hlocalMulImp] with
    x hxleft hxzero hxright hxrestrict hxlocalMul
  rw [hxleft, hxright, hxzero]
  by_cases hx : x ∈ Ω
  · rw [show extensionByZero (n := n) (p := 2) (Ω := Ω)
        ((SobolevSpace.GraphSpace.restrictDerivLp
          (n := n) (p := ∞) (Ω := Ω) (Ωbig := Set.univ)
          (Set.subset_univ Ω) a) • u) x =
        (((SobolevSpace.GraphSpace.restrictDerivLp
          (n := n) (p := ∞) (Ω := Ω) (Ωbig := Set.univ)
          (Set.subset_univ Ω) a) • u : DerivLp n 2 Ω) x) by
        simp [extensionByZero, hx],
      hxlocalMul hx, hxrestrict hx]
    simp [extensionByZero, hx]
  · simp [extensionByZero, hx]

/-- If a smooth cutoff is supported in `Ω`, multiplying after restriction
and then extending by zero agrees with whole-space multiplication. -/
theorem zeroExtendLp_testFunction_smul_restrict
    (hΩmeas : MeasurableSet Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψΩ : tsupport ψ.toFun ⊆ Ω)
    (v : DerivLp n 2 Set.univ) :
    zeroExtendLp (n := n) (p := 2) (Ω := Ω) hΩmeas
        (testFunctionLpTop (n := n) (Ω := Ω) ψ •
          SobolevSpace.GraphSpace.restrictDerivLp
            (n := n) (p := 2) (Set.subset_univ Ω) v) =
      testFunctionLpTop (n := n) (Ω := Set.univ) ψ • v := by
  rw [← SobolevSpace.GraphSpace.restrict_testFunctionLpTop
    (n := n) (Ω := Ω) ψ]
  rw [zeroExtendLp_restrict_lpSMul]
  apply MeasureTheory.Lp.ext
  let r := SobolevSpace.GraphSpace.restrictDerivLp
    (n := n) (p := 2) (Set.subset_univ Ω) v
  have hleft := SobolevSpace.GraphSpace.mulLpLeft_apply_ae
    (n := n) (p := (2 : ℝ≥0∞))
    (testFunctionLpTop (n := n) (Ω := Set.univ) ψ)
    (zeroExtendLp (n := n) (p := 2) (Ω := Ω) hΩmeas r)
  have hright := SobolevSpace.GraphSpace.mulLpLeft_apply_ae
    (n := n) (p := (2 : ℝ≥0∞))
    (testFunctionLpTop (n := n) (Ω := Set.univ) ψ) v
  have hcutoff := testFunctionLpTop_apply_ae
    (n := n) (Ω := Set.univ) ψ
  have hzero := zeroExtendLp_apply_ae
    (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) hΩmeas r
  have hrestrict := SobolevSpace.GraphSpace.restrictDerivLp_apply_ae
    (n := n) (p := (2 : ℝ≥0∞)) (Set.subset_univ Ω) v
  have hrestrictImp :
      ∀ᵐ x ∂domainMeasure n Set.univ, x ∈ Ω → (r : ℝ^n → ℝ) x = v x := by
    have hr : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Ω →
        (r : ℝ^n → ℝ) x = v x := by
      apply (MeasureTheory.ae_restrict_iff' hΩmeas).1
      change (r : ℝ^n → ℝ) =ᵐ[MeasureTheory.volume.restrict Ω] (v : ℝ^n → ℝ)
        at hrestrict
      filter_upwards [hrestrict] with x hx
      exact hx
    simpa [domainMeasure] using hr
  filter_upwards [hleft, hright, hcutoff, hzero, hrestrictImp] with
    x hxleft hxright hxcutoff hxzero hxrestrict
  simp only [SobolevSpace.GraphSpace.mulLpLeft_apply] at hxleft hxright
  rw [hxleft, hxright, hxcutoff, hxzero]
  by_cases hx : x ∈ Ω
  · rw [show extensionByZero (n := n) (p := 2) (Ω := Ω) r x = r x by
        simp [extensionByZero, hx], hxrestrict hx]
  · have hψzero : ψ.toFun x = 0 := by
      by_contra hne
      exact hx (hψΩ (subset_tsupport ψ.toFun hne))
    simp [hψzero]

/-- Zero extension agrees almost everywhere with the original `Lp` function on `Ω`. -/
theorem zeroExtendLp_agree_ae (hΩmeas : MeasurableSet Ω) (u : DerivLp n p Ω) :
    (zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas u :
      ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (u : ℝ^n → ℝ) := by
  let μuniv : Measure (ℝ^n) := (MeasureTheory.volume : Measure (ℝ^n))
  have htoLp :
      (zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas u : ℝ^n → ℝ) =ᵐ[μuniv]
        extensionByZero (n := n) (p := p) (Ω := Ω) u := by
    rw [show μuniv = domainMeasure n Set.univ by simp [μuniv, domainMeasure]]
    exact zeroExtendLp_apply_ae (n := n) (p := p) (Ω := Ω) hΩmeas u
  have hImp :
      ∀ᵐ x ∂ μuniv, x ∈ Ω →
        (zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas u : ℝ^n → ℝ) x = (u : ℝ^n → ℝ) x := by
    filter_upwards [htoLp] with x hx hxΩ
    simpa [extensionByZero, hxΩ] using hx
  have :
      ∀ᵐ x ∂ μuniv.restrict Ω,
        (zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas u : ℝ^n → ℝ) x = (u : ℝ^n → ℝ) x :=
    (ae_restrict_iff' (μ := μuniv) (s := Ω) hΩmeas).2 hImp
  filter_upwards [this] with x hx
  exact hx

/-- Restricting a zero extension to its original domain recovers the input. -/
@[simp] theorem restrict_zeroExtendLp
    (hΩmeas : MeasurableSet Ω) (u : DerivLp n p Ω) :
    SobolevSpace.GraphSpace.restrictDerivLp
        (n := n) (p := p) (Ω := Ω) (Ωbig := Set.univ)
        (Set.subset_univ Ω)
        (zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas u) =
      u := by
  apply MeasureTheory.Lp.ext
  have hrestrict := SobolevSpace.GraphSpace.restrictDerivLp_apply_ae
    (n := n) (p := p) (Ω := Ω) (Ωbig := Set.univ)
    (Set.subset_univ Ω)
    (zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas u)
  have hagree := zeroExtendLp_agree_ae
    (n := n) (p := p) (Ω := Ω) hΩmeas u
  exact hrestrict.trans hagree

/-- Restriction is a left inverse to zero extension as an operator identity. -/
@[simp] theorem restrictDerivLp_comp_zeroExtendLp
    (hΩmeas : MeasurableSet Ω) :
    (SobolevSpace.GraphSpace.restrictDerivLp
      (n := n) (p := p) (Ω := Ω) (Ωbig := Set.univ)
      (Set.subset_univ Ω)).comp
        (zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas) =
      ContinuousLinearMap.id ℝ (DerivLp n p Ω) := by
  apply ContinuousLinearMap.ext
  intro u
  exact restrict_zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas u

end Lp

end Extension

end SobolevSpace

end
