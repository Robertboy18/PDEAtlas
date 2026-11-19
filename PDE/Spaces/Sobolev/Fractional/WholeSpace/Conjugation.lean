/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.L2Representative
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Real
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Embedding
public import PDE.Analysis.MeasureTheory.Lp.Star

/-!
# Conjugation, and the two notions of realness agree

`Fractional.WholeSpace.Real` defines the real subspace of `H^s` through the Bessel
representative, `IsRealL2 (toLp u)`.  Everything built on the weak-derivative
side instead uses the function representative, `IsRealL2 (toL2Fun hs u)`.
We prove the two agree for `s ≥ 0`, which connects `hsRealSubmodule` to the
weak-derivative side.

## Main results

* `SobolevSpace.Fractional.fourier_star`: conjugation and the Fourier transform.
* `SobolevSpace.Fractional.isRealL2_iff_star`: realness is star-invariance.
* `SobolevSpace.Fractional.isRealL2_iff_isHermitian_fourier`: realness is
  Hermitian symmetry of the transform.
* `SobolevSpace.Fractional.isHermitian_lpSMul_iff`: a real, even, nonvanishing
  bounded multiplier preserves and detects Hermitian symmetry.
* `SobolevSpace.Fractional.isRealL2_toL2Fun_iff`: the two notions of realness
  coincide, and `mem_HsRealSubmodule_iff_toL2Fun` restates it as membership.

## Implementation notes

The mathematical content is that the Bessel potential preserves realness,
because its symbol `(1 + ‖ξ‖²)^(s/2)` is real and even.  Via Plancherel that
says: multiplying a Hermitian-symmetric Fourier transform by a real even
function keeps it Hermitian.

Mathlib supplies neither half of the required conjugation calculus:

* there is no `Star` structure on `SchwartzMap` or `TemperedDistribution`;
* there is no pointwise identity relating the Euclidean Fourier transform to conjugation, such
  as `𝓕(conj f)(ξ) = conj(𝓕 f(-ξ))`; the nearest result,
  `integral_sesq_fourierIntegral_eq_neg_flip`, is an integrated identity for sesquilinear
  pairings.

So `conjSchwartz` (conjugation on Schwartz functions), `reflL2` (reflection
`x ↦ -x` on `L²`), and `fourier_star`, the missing identity
`𝓕 (star f) = reflL2 (star (𝓕 f))`, are all built here.  `L²`
itself does carry a `Star` instance, which is what makes this tractable.

## References

* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Princeton
  University Press, 1971, Chapter I, The Fourier Transform, pp. 1-36, for the elementary properties
  of the Fourier transform, from which `𝓕(conj f)(ξ) = conj(𝓕 f(-ξ))` and the Hermitian symmetry of
  the transform of a real function follow.
  <https://doi.org/10.1515/9781400883899>
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Springer, 2014, Chapter 2, Maximal Functions,
  Fourier Transform, and Distributions, pp. 85-172, for the basic properties of the Fourier
  transform on `𝓢(ℝ^n)`.
  <https://doi.org/10.1007/978-1-4939-1194-3>
-/

@[expose] public section

open MeasureTheory TemperedDistribution FourierTransform SchwartzMap Complex
open scoped BesselPotentialSpace ENNReal SchwartzMap RealInnerProductSpace ComplexConjugate

noncomputable section
namespace SobolevSpace.Fractional
variable {n : ℕ} {s t : ℝ}
open BesselPotentialSpace

/-! ## Conjugation and reflection -/

/-- Pointwise complex conjugation as a real continuous linear map on Schwartz space. -/
def conjSchwartz (n : ℕ) : 𝓢(ℝ^n, ℂ) →L[ℝ] 𝓢(ℝ^n, ℂ) :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap

/-- `conjSchwartz` acts pointwise by complex conjugation. -/
theorem conjSchwartz_apply (φ : 𝓢(ℝ^n,
  ℂ)) (x : ℝ^n) : conjSchwartz n φ x = conj (φ x) := rfl

/-- Reflection `f(x) ↦ f(-x)` as an additive isometry of complex `L²(ℝ^n)`. -/
def reflL2 (n : ℕ) : Lp ℂ 2 (volume : Measure (ℝ^n)) →+ Lp ℂ 2 (volume : Measure (ℝ^n)) :=
  Lp.compMeasurePreserving (fun x ↦ -x) (Measure.measurePreserving_neg (volume : Measure (ℝ^n)))

/-- Reflection is continuous on `L²`; it is an isometry because `x ↦ -x` preserves Lebesgue
measure. -/
theorem continuous_reflL2 : Continuous (reflL2 n) :=
  (Lp.isometry_compMeasurePreserving (E := ℂ) (p := 2)
    (Measure.measurePreserving_neg (volume : Measure (ℝ^n)))).continuous

/-- A representative of `reflL2 n f` is `x ↦ f (-x)`. -/
theorem coeFn_reflL2 (f : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    (reflL2 n f : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (f : ℝ^n → ℂ) (-x) :=
  Lp.coeFn_compMeasurePreserving f _

/-- Transport an a.e. statement through `x ↦ -x`. -/
theorem ae_neg {p : ℝ^n → Prop} (h : ∀ᵐ x ∂(volume : Measure (ℝ^n)), p x) :
    ∀ᵐ x ∂(volume : Measure (ℝ^n)), p (-x) :=
  (Measure.measurePreserving_neg (volume : Measure (ℝ^n))).quasiMeasurePreserving.ae h

/-- The Fourier integral of a conjugate: `𝓕(conj f)(w) = conj(𝓕 f(-w))`. There is no
integrability hypothesis: for non-integrable `f` both Bochner integrals are zero. -/
theorem fourier_conj (f : ℝ^n → ℂ) (w : ℝ^n) :
    𝓕 (fun v ↦ conj (f v)) w = conj (𝓕 f (-w)) := by
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
  simp only [Circle.smul_def, smul_eq_mul, map_mul, inner_neg_right, neg_neg,
    ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]

/-- Conjugating the `L²` class of a Schwartz function gives the `L²` class of its conjugate. -/
theorem star_toLp (φ : 𝓢(ℝ^n, ℂ)) :
    star (φ.toLp 2 (volume : Measure (ℝ^n))) = (conjSchwartz n φ).toLp 2 volume := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (φ.toLp 2 (volume : Measure (ℝ^n))),
    φ.coeFn_toLp 2 (volume : Measure (ℝ^n)),
    (conjSchwartz n φ).coeFn_toLp 2 (volume : Measure (ℝ^n))] with x h1 h2 h3
  rw [h1, h3, Pi.star_apply, h2, conjSchwartz_apply]
  rfl

/-- On `L²`, the Fourier transform of `star f` is the reflection of `star (𝓕 f)`. -/
theorem fourier_star (f : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    𝓕 (star f) = reflL2 n (star (𝓕 f)) := by
  have key : (fun g : Lp ℂ 2 (volume : Measure (ℝ^n)) ↦ 𝓕 (star g)) =
      (fun g ↦ reflL2 n (star (𝓕 g))) := by
    refine (SchwartzMap.denseRange_toLpCLM (E := ℝ^n) (F := ℂ) (p := 2)
      ENNReal.ofNat_ne_top (μ := (volume : Measure (ℝ^n)))).equalizer ?_ ?_ ?_
    · exact ContinuousFourier.continuous_fourier.comp continuous_star
    · exact continuous_reflL2.comp
        (continuous_star.comp ContinuousFourier.continuous_fourier)
    · funext φ
      simp only [Function.comp_apply, SchwartzMap.toLpCLM_apply]
      rw [star_toLp, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq, star_toLp]
      refine Lp.ext ?_
      filter_upwards [(𝓕 (conjSchwartz n φ)).coeFn_toLp 2 (volume : Measure (ℝ^n)),
        coeFn_reflL2 ((conjSchwartz n (𝓕 φ)).toLp 2 (volume : Measure (ℝ^n))),
        ae_neg ((conjSchwartz n (𝓕 φ)).coeFn_toLp 2 (volume : Measure (ℝ^n)))] with x h1 h2 h3
      rw [h1, h2, h3, conjSchwartz_apply, SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
      exact fourier_conj (φ : ℝ^n → ℂ) x
  exact congrFun key f

/-! ## Realness as a star condition -/

/-- An `L²` function is a.e. real exactly when it is fixed by conjugation. -/
theorem isRealL2_iff_star (f : Lp ℂ 2 (volume : Measure (ℝ^n))) : IsRealL2 f ↔ star f = f := by
  rw [IsRealL2, Lp.ext_iff]
  constructor
  · intro h
    filter_upwards [Lp.coeFn_star f, h] with x h1 h2
    rw [h1, Pi.star_apply, RCLike.star_def, Complex.conj_eq_iff_im]
    exact h2
  · intro h
    filter_upwards [Lp.coeFn_star f, h] with x h1 h2
    rw [h1, Pi.star_apply, RCLike.star_def] at h2
    exact Complex.conj_eq_iff_im.mp h2

/-- Hermitian symmetry of an `L²` function on the Fourier side. -/
def IsHermitianL2 (g : Lp ℂ 2 (volume : Measure (ℝ^n))) : Prop := reflL2 n (star g) = g

/-- An `L²` function is a.e. real exactly when its Fourier transform is Hermitian symmetric,
`ĝ(-ξ) = conj (ĝ ξ)`. This is `fourier_star` combined with injectivity of the `L²` Fourier
transform. -/
theorem isRealL2_iff_isHermitian_fourier (f : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    IsRealL2 f ↔ IsHermitianL2 (𝓕 f) := by
  rw [isRealL2_iff_star, IsHermitianL2]
  constructor
  · intro h
    rw [← fourier_star, h]
  · intro h
    have := (fourier_star f).trans h
    exact (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).injective this


/-! ## The multiplier step -/

/-- Multiplication by a real, even `L^∞` function commutes with the Hermitian-conjugation
operation `g ↦ reflL2 (star g)`. The multiplier `m` is given through an a.e. representative
`M` so that evenness and realness can be stated pointwise. -/
theorem refl_star_lpSMul (m : Lp ℂ ∞ (volume : Measure (ℝ^n))) (M : ℝ^n → ℂ)
    (hm : ⇑m =ᵐ[(volume : Measure (ℝ^n))] M) (hMeven : ∀ x, M (-x) = M x)
    (hMreal : ∀ x, conj (M x) = M x) (F : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    reflL2 n (star (m • F : Lp ℂ 2 (volume : Measure (ℝ^n)))) = m • reflL2 n (star F) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reflL2 (star (m • F : Lp ℂ 2 (volume : Measure (ℝ^n)))),
      ae_neg (Lp.coeFn_star (m • F : Lp ℂ 2 (volume : Measure (ℝ^n)))),
      ae_neg (Lp.coeFn_lpSMul (r := 2) m F), ae_neg hm,
      Lp.coeFn_lpSMul (r := 2) m (reflL2 n (star F)), hm,
      coeFn_reflL2 (star F), ae_neg (Lp.coeFn_star F)] with x h1 h2 h3 h4 h5 h6 h7 h8
  rw [h1, h2, Pi.star_apply, h3, Pi.smul_apply', h4, smul_eq_mul, RCLike.star_def, map_mul,
    hMreal, hMeven, h5, Pi.smul_apply', h6, smul_eq_mul, h7, h8, Pi.star_apply, RCLike.star_def]

/-- A nowhere-vanishing `L^∞` multiplier can be cancelled: `m • F = m • G` forces `F = G`. No
lower bound on `|M|` is needed, since the cancellation happens pointwise a.e. -/
theorem lpSMul_cancel (m : Lp ℂ ∞ (volume : Measure (ℝ^n))) (M : ℝ^n → ℂ)
    (hm : ⇑m =ᵐ[(volume : Measure (ℝ^n))] M) (hM : ∀ x, M x ≠ 0)
    {F G : Lp ℂ 2 (volume : Measure (ℝ^n))}
    (h : (m • F : Lp ℂ 2 (volume : Measure (ℝ^n))) = m • G) : F = G := by
  refine Lp.ext ?_
  have h' := Lp.ext_iff.mp h
  filter_upwards [h', Lp.coeFn_lpSMul (r := 2) m F, Lp.coeFn_lpSMul (r := 2) m G, hm]
    with x hx h1 h2 h3
  rw [h1, h2, Pi.smul_apply', Pi.smul_apply', h3, smul_eq_mul, smul_eq_mul] at hx
  exact mul_left_cancel₀ (hM x) hx

/-- Multiplication by a real, even, nowhere-vanishing `L^∞` symbol preserves and detects
Hermitian symmetry. This is the abstract form of "the Bessel potential preserves realness". -/
theorem isHermitian_lpSMul_iff (m : Lp ℂ ∞ (volume : Measure (ℝ^n))) (M : ℝ^n → ℂ)
    (hm : ⇑m =ᵐ[(volume : Measure (ℝ^n))] M) (hMeven : ∀ x, M (-x) = M x)
    (hMreal : ∀ x, conj (M x) = M x) (hM : ∀ x, M x ≠ 0) (F : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    IsHermitianL2 (m • F : Lp ℂ 2 (volume : Measure (ℝ^n))) ↔ IsHermitianL2 F := by
  unfold IsHermitianL2
  rw [refl_star_lpSMul m M hm hMeven hMreal F]
  constructor
  · intro h; exact lpSMul_cancel m M hm hM h
  · intro h; rw [h]

/-! ## The two notions of realness agree -/

/-- The Bessel symbol is even. -/
theorem besselSymbol_neg (r : ℝ) (x : ℝ^n) : besselSymbol n r (-x) = besselSymbol n r x := by
  unfold besselSymbol; rw [norm_neg]

/-- The Bessel symbol is real-valued, hence fixed by conjugation. -/
theorem conj_besselSymbol (r : ℝ) (x : ℝ^n) :
    conj (besselSymbol n r x) = besselSymbol n r x := Complex.conj_ofReal _

/-- The Bessel symbol never vanishes: `(1 + ‖ξ‖²)^{r/2} > 0`. -/
theorem besselSymbol_ne_zero (r : ℝ) (x : ℝ^n) : besselSymbol n r x ≠ 0 := by
  unfold besselSymbol
  simpa using ne_of_gt (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 1 + ‖x‖ ^ 2) (r / 2))

/-- A representative of the `L^∞` class `symbolLinf n r hr` is the Bessel symbol itself. -/
theorem coeFn_symbolLinf {r : ℝ} (hr : r ≤ 0) :
    ⇑(symbolLinf n r hr) =ᵐ[(volume : Measure (ℝ^n))] besselSymbol n r :=
  MemLp.coeFn_toLp _

/-- Realness of the Bessel representative is preserved and detected by the inclusion
`H^s ⊆ H^t`. On the Fourier side the inclusion multiplies by the Bessel symbol of order
`t - s`, which is real, even and nonvanishing, so Hermitian symmetry is unaffected. -/
theorem isRealL2_toLp_inclLinear_iff (h : t ≤ s) (u : H^{s}(ℝ^n)) :
    IsRealL2 (toLp (inclLinear n h u)) ↔ IsRealL2 (toLp u) := by
  rw [isRealL2_iff_isHermitian_fourier, isRealL2_iff_isHermitian_fourier]
  have h1 : 𝓕 (toLp (inclLinear n h u))
      = (symbolLinf n (t - s) (sub_nonpos.mpr h) • 𝓕 (toLp u) : Lp ℂ 2 (volume : Measure (ℝ^n))) :=
    fourier_toLp_inclLinear h u
  rw [h1]
  exact isHermitian_lpSMul_iff _ (besselSymbol n (t - s)) (coeFn_symbolLinf _)
    (besselSymbol_neg _) (conj_besselSymbol _) (besselSymbol_ne_zero _) _

/-- Realness of the function representative equals realness of the Bessel representative. -/
theorem isRealL2_toL2Fun_iff (hs : (0 : ℝ) ≤ s) (u : H^{s}(ℝ^n)) :
    IsRealL2 (toL2Fun hs u) ↔ IsRealL2 (toLp u) :=
  isRealL2_toLp_inclLinear_iff hs u

/-- For `s ≥ 0`, membership in `hsRealSubmodule` (realness of the Bessel representative) is
equivalent to realness of the function representative `toL2Fun hs u`. This is the bridge that
lets the weak-derivative and graph-space results apply to `HsSpaceReal`. -/
theorem mem_HsRealSubmodule_iff_toL2Fun (hs : (0 : ℝ) ≤ s) {u : H^{s}(ℝ^n)} :
    u ∈ hsRealSubmodule n s ↔ IsRealL2 (toL2Fun hs u) :=
  mem_HsRealSubmodule_iff.trans (isRealL2_toL2Fun_iff hs u).symm

/-- The physical `L²` representative of an element of the canonical real
fractional Sobolev space is real almost everywhere.

This is the preferred elimination lemma for `u : HsSpaceReal n s` when
`s ≥ 0`.  It keeps the definition of the real space independent of a proof of
nonnegativity while exposing the function representative needed by the
weak-derivative and graph-space APIs. -/
theorem HsSpaceReal.isRealL2_toL2Fun (hs : (0 : ℝ) ≤ s) (u : HsSpaceReal n s) :
    IsRealL2 (toL2Fun hs u.1) :=
  (mem_HsRealSubmodule_iff_toL2Fun hs).mp u.2

/-- Package an element whose physical `L²` representative is real into the
canonical real fractional Sobolev space. -/
def HsSpaceReal.ofPhysical (hs : (0 : ℝ) ≤ s) (u : H^{s}(ℝ^n))
    (hu : IsRealL2 (toL2Fun hs u)) : HsSpaceReal n s :=
  ⟨u, (mem_HsRealSubmodule_iff_toL2Fun hs).mpr hu⟩

/-- The underlying `H^s` element of `ofPhysical hs u hu` is `u`. -/
@[simp] theorem HsSpaceReal.coe_ofPhysical (hs : (0 : ℝ) ≤ s) (u : H^{s}(ℝ^n))
    (hu : IsRealL2 (toL2Fun hs u)) :
    (HsSpaceReal.ofPhysical hs u hu : H^{s}(ℝ^n)) = u :=
  rfl

/-- The real-valued physical `L²` representative of a real fractional
Sobolev function. -/
noncomputable def HsSpaceReal.toL2FunCLM (n : ℕ) (hs : (0 : ℝ) ≤ s) :
    HsSpaceReal n s →L[ℝ] Lp ℝ 2 (volume : Measure (ℝ^n)) := by
  let physicalComplex : HsSpaceReal n s →L[ℝ] Lp ℂ 2 (volume : Measure (ℝ^n)) :=
    ((SobolevSpace.Fractional.toL2FunCLM n hs).restrictScalars ℝ).comp
      (hsRealSubmodule n s).subtypeL
  exact
    (Complex.reCLM.compLpL 2 (volume : Measure (ℝ^n))).comp
      physicalComplex

/-- The real `L²` realization agrees almost everywhere with the real part of
the complex physical representative. -/
theorem HsSpaceReal.toL2FunCLM_apply_ae (hs : (0 : ℝ) ≤ s)
    (u : HsSpaceReal n s) :
    (HsSpaceReal.toL2FunCLM n hs u : ℝ^n → ℝ)
      =ᵐ[(volume : Measure (ℝ^n))]
        fun x ↦ ((toL2Fun hs u.1 : ℝ^n → ℂ) x).re := by
  simpa [HsSpaceReal.toL2FunCLM] using
    (Complex.reCLM.coeFn_compLpL (toL2Fun hs u.1))

namespace HsSpaceReal

/-- Complexifying the real physical representative recovers the complex physical class. -/
theorem ofReal_toL2FunCLM (hs : 0 ≤ s) (u : HsSpaceReal n s) :
    Complex.ofRealCLM.compLpL 2 volume (toL2FunCLM n hs u) = toL2Fun hs u.1 := by
  apply Lp.ext
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (toL2FunCLM n hs u),
    toL2FunCLM_apply_ae hs u, isRealL2_toL2Fun hs u] with x hc hr hi
  rw [hc, hr]
  exact Complex.ext rfl (by simpa using hi.symm)

/-- The real physical `L²` realization is faithful. -/
theorem toL2FunCLM_injective (hs : 0 ≤ s) :
    Function.Injective (toL2FunCLM n hs) := by
  intro u v huv
  apply Subtype.ext
  apply toL2Fun_injective hs
  rw [← ofReal_toL2FunCLM hs u, ← ofReal_toL2FunCLM hs v, huv]

/-- Taking real physical representatives preserves the physical complex `L²` norm. -/
theorem norm_toL2FunCLM_eq (hs : 0 ≤ s) (u : HsSpaceReal n s) :
    ‖toL2FunCLM n hs u‖ = ‖toL2Fun hs u.1‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [toL2FunCLM_apply_ae hs u, isRealL2_toL2Fun hs u] with x hr hi
  rw [hr, ← Complex.norm_real]
  congr 1
  exact Complex.ext rfl (by simpa using hi.symm)

end HsSpaceReal

end SobolevSpace.Fractional
