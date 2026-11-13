/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Restriction
public import PDE.Spaces.Sobolev.GraphSpace.Model.Notation
import PDE.Analysis.Normed.PiLp.Coordinatewise

/-!
# Restriction of Sobolev functions to a subdomain

If `Ω ⊆ Ωbig`, a function in `W^{k,p}(Ωbig)` restricts to a function in `W^{k,p}(Ω)`, and each
weak derivative restricts to the corresponding weak derivative on `Ω`. Since the graph-space model
`WkpSpaceOn` stores a Sobolev element as a bundle of `Lᵖ` coordinates indexed by `DerivIndex n k`,
restriction is performed coordinate by coordinate: `domainMeasure n Ω ≤ domainMeasure n Ωbig`, so
Mathlib's `MeasureTheory.Lp.restrictionCLMOfLE` gives a contraction `Lᵖ(Ωbig) → Lᵖ(Ω)` on every
coordinate. The result is a bounded linear map of operator norm at most one, functorial in the
domain and the identity when `Ω = Ωbig`.

Only the last step, checking that the restricted bundle still satisfies the weak-derivative
identities on `Ω`, needs `Ω` to be measurable (`HasWeakDerivativeOn.mono`). The ambient maps
`restrictDerivLp` and `restrictAmbient` are defined for arbitrary subsets. For open subsets the
restriction property is Evans, PDE, §5.2.3, Theorem 1(iii), whose proof Evans omits as easy.

## Main results

* `restrictDerivLp`: restriction of one `Lᵖ` coordinate, with `norm_restrictDerivLp_le`
  (contraction) and `restrictDerivLp_apply_ae` (agrees with the original a.e. on `Ω`).
* `restrictAmbient`: coordinatewise restriction of the ambient `PiLp` bundle; contractive
  (`norm_restrictAmbient_apply_le`) and functorial (`restrictAmbient_self`, `restrictAmbient_comp`).
* `restrictCLM`: the bounded restriction `W^{k,p}(Ωbig) → W^{k,p}(Ω)` for measurable `Ω ⊆ Ωbig`,
  with `norm_restrictCLM_le_one`, `restrictCLM_apply_ae`, `restrictCLM_self`, `restrictCLM_comp`.
* `restrictDerivLp_lpSMul`, `restrict_testFunctionLpTop`, `restrict_partialTestFunctionLpTop`:
  restriction commutes with the `L^∞ · L²` product and with viewing a test function (or one of its
  first partials) as an `L^∞` coefficient. These are the compatibilities needed when a variable
  coefficient equation is localized to a smaller domain.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.2, pp. 258-259, for the space `W^{k,p}(U)`, and §5.2.3,
  Theorem 1(iii), p. 261: if `V ⊆ U` is open, then `u ∈ W^{k,p}(V)`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace

open MeasureTheory Set Function ENNReal

namespace GraphSpace

section Restriction

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω Ωbig : Set (ℝ^n)}

/-- The domain measure is monotone in the domain. -/
theorem domainMeasure_le (hsub : Ω ⊆ Ωbig) :
    domainMeasure n Ω ≤ domainMeasure n Ωbig :=
  Measure.restrict_mono hsub le_rfl

/-- Restrict one `Lᵖ` derivative coordinate from `Ωbig` to a subdomain `Ω`.
This is a contraction. -/
noncomputable def restrictDerivLp (hsub : Ω ⊆ Ωbig) :
    DerivLp n p Ωbig →L[ℝ] DerivLp n p Ω :=
  MeasureTheory.Lp.restrictionCLMOfLE
    (domainMeasure_le (n := n) hsub)

/-- Restricting an `Lᵖ` coordinate to a subdomain is contractive. -/
theorem norm_restrictDerivLp_le (hsub : Ω ⊆ Ωbig)
    (u : DerivLp n p Ωbig) :
    ‖restrictDerivLp (n := n) (p := p) hsub u‖ ≤ ‖u‖ :=
  MeasureTheory.Lp.norm_restrictionCLMOfLE_apply_le
    (domainMeasure_le (n := n) hsub) u

/-- The restricted coordinate represents the original coordinate almost
everywhere on the smaller domain. -/
theorem restrictDerivLp_apply_ae (hsub : Ω ⊆ Ωbig)
    (u : DerivLp n p Ωbig) :
    (restrictDerivLp (n := n) (p := p) hsub u : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] (u : ℝ^n → ℝ) :=
  MeasureTheory.Lp.restrictionCLMOfLE_apply_ae
    (domainMeasure_le (n := n) hsub) u

/-- Restricting an `Lᵖ` derivative coordinate to the same domain is the
identity. -/
theorem restrictDerivLp_self :
    restrictDerivLp (n := n) (p := p)
        (Set.Subset.rfl : Ω ⊆ Ω) =
      ContinuousLinearMap.id ℝ (DerivLp n p Ω) := by
  simpa only [restrictDerivLp] using
    (MeasureTheory.Lp.restrictionCLMOfLE_refl
      (E := ℝ) (p := p) (μ := domainMeasure n Ω))

/-- Restriction of derivative coordinates is functorial under nested domains. -/
theorem restrictDerivLp_comp
    {Ω₁ Ω₂ Ω₃ : Set (ℝ^n)}
    (h₁₂ : Ω₁ ⊆ Ω₂) (h₂₃ : Ω₂ ⊆ Ω₃) :
    (restrictDerivLp (n := n) (p := p) h₁₂).comp
        (restrictDerivLp (n := n) (p := p) h₂₃) =
      restrictDerivLp (n := n) (p := p) (h₁₂.trans h₂₃) := by
  simpa only [restrictDerivLp] using
    (MeasureTheory.Lp.restrictionCLMOfLE_trans
      (E := ℝ) (p := p)
      (domainMeasure_le (n := n) h₁₂)
      (domainMeasure_le (n := n) h₂₃))

section Multiplication

/-- Restriction commutes with multiplication of an `L∞` coefficient by an
`L²` field. -/
theorem restrictDerivLp_lpSMul
    (hΩ : MeasurableSet Ω) (hsub : Ω ⊆ Ωbig)
    (a : DerivLp n ∞ Ωbig) (u : DerivLp n 2 Ωbig) :
    restrictDerivLp (n := n) (p := 2) hsub (a • u) =
      restrictDerivLp (n := n) (p := ∞) hsub a •
        restrictDerivLp (n := n) (p := 2) hsub u := by
  apply MeasureTheory.Lp.ext
  have hleft := restrictDerivLp_apply_ae
    (n := n) (p := (2 : ℝ≥0∞)) hsub (a • u)
  have ha := restrictDerivLp_apply_ae
    (n := n) (p := (∞ : ℝ≥0∞)) hsub a
  have hu := restrictDerivLp_apply_ae
    (n := n) (p := (2 : ℝ≥0∞)) hsub u
  have hmulBig := mulLpLeft_apply_ae
    (n := n) (p := (2 : ℝ≥0∞)) a u
  have hmulSmall := mulLpLeft_apply_ae
    (n := n) (p := (2 : ℝ≥0∞))
    (restrictDerivLp (n := n) (p := ∞) hsub a)
    (restrictDerivLp (n := n) (p := 2) hsub u)
  have hmeasure :
      (domainMeasure n Ωbig).restrict Ω = domainMeasure n Ω := by
    rw [domainMeasure, Measure.restrict_restrict hΩ]
    congr 1
    exact Set.inter_eq_left.2 hsub
  have hmulBigΩ := MeasureTheory.ae_restrict_of_ae
    (s := Ω) hmulBig
  rw [hmeasure] at hmulBigΩ
  filter_upwards [hleft, ha, hu, hmulBigΩ, hmulSmall] with
    x hxleft hxa hxu hxmulBig hxmulSmall
  calc
    (restrictDerivLp (n := n) (p := 2) hsub (a • u) :
        ℝ^n → ℝ) x =
        ((a • u : DerivLp n 2 Ωbig) : ℝ^n → ℝ) x := hxleft
    _ = a x * u x := hxmulBig
    _ = (restrictDerivLp (n := n) (p := ∞) hsub a : ℝ^n → ℝ) x *
        (restrictDerivLp (n := n) (p := 2) hsub u : ℝ^n → ℝ) x := by
      rw [hxa, hxu]
    _ = ((restrictDerivLp (n := n) (p := ∞) hsub a •
        restrictDerivLp (n := n) (p := 2) hsub u :
          DerivLp n 2 Ω) : ℝ^n → ℝ) x := hxmulSmall.symm

end Multiplication

/-- Viewing a test function as an `L∞` coefficient commutes with
restriction from the whole space to a measurable domain. -/
theorem restrict_testFunctionLpTop
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    restrictDerivLp (n := n) (p := ∞) (subset_univ Ω)
        (testFunctionLpTop (n := n) (Ω := Set.univ) ψ) =
      testFunctionLpTop (n := n) (Ω := Ω) ψ := by
  apply MeasureTheory.Lp.ext
  have hrestrict := restrictDerivLp_apply_ae
    (n := n) (p := (∞ : ℝ≥0∞)) (subset_univ Ω)
    (testFunctionLpTop (n := n) (Ω := Set.univ) ψ)
  have hglobal := testFunctionLpTop_apply_ae
    (n := n) (Ω := Set.univ) ψ
  have hglobalΩ :
      ((testFunctionLpTop (n := n) (Ω := Set.univ) ψ :
          DerivLp n ∞ Set.univ) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] ψ.toFun := by
    have hmeasure :
        (domainMeasure n Set.univ).restrict Ω = domainMeasure n Ω := by
      simp [domainMeasure]
    rw [← hmeasure]
    exact MeasureTheory.ae_restrict_of_ae (s := Ω) hglobal
  have hlocal := testFunctionLpTop_apply_ae (n := n) (Ω := Ω) ψ
  filter_upwards [hrestrict, hglobalΩ, hlocal] with x hr hg hl
  rw [hr, hg, hl]

/-- The same restriction identity for a first derivative of a test
function. -/
theorem restrict_partialTestFunctionLpTop
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i : Fin n) :
    restrictDerivLp (n := n) (p := ∞) (subset_univ Ω)
        (partialTestFunctionLpTop (n := n) (Ω := Set.univ) ψ i) =
      partialTestFunctionLpTop (n := n) (Ω := Ω) ψ i := by
  simpa only [partialTestFunctionLpTop] using
    restrict_testFunctionLpTop (n := n) (Ω := Ω)
      (_root_.TestFunction.lineDerivCLM ℝ
        (EuclideanSpace.single i (1 : ℝ)) ψ)

/-- Coordinatewise restriction on the Banach derivative bundle. -/
noncomputable def restrictAmbient (hsub : Ω ⊆ Ωbig) :
    WkpAmbientOn n k p Ωbig →L[ℝ] WkpAmbientOn n k p Ω := by
  classical
  let e := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := p)
    (β := fun _ : DerivIndex n k ↦ DerivLp n p Ω)
  exact e.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a ↦
      (restrictDerivLp (n := n) (p := p) hsub).comp
        (PiLp.proj (𝕜 := ℝ) (p := p)
          (β := fun _ : DerivIndex n k ↦ DerivLp n p Ωbig) a))

/-- Coordinate `a` of the restricted bundle is the `Lᵖ` restriction of coordinate `a`. -/
@[simp] theorem restrictAmbient_apply
    (hsub : Ω ⊆ Ωbig) (U : WkpAmbientOn n k p Ωbig)
    (a : DerivIndex n k) :
    restrictAmbient (n := n) (k := k) (p := p) hsub U a =
      restrictDerivLp (n := n) (p := p) hsub (U a) := by
  classical
  simp [restrictAmbient]

/-- Coordinatewise domain restriction contracts the ambient Sobolev bundle. -/
theorem norm_restrictAmbient_apply_le
    (hsub : Ω ⊆ Ωbig)
    (U : WkpAmbientOn n k p Ωbig) :
    ‖restrictAmbient (n := n) (k := k) (p := p) hsub U‖ ≤ ‖U‖ :=
  PiLp.norm_mono _ _ fun a ↦ norm_restrictDerivLp_le hsub (U a)

/-- Coordinatewise restriction to the same domain is the identity on the
ambient Sobolev bundle. -/
theorem restrictAmbient_self :
    restrictAmbient (n := n) (k := k) (p := p)
        (Set.Subset.rfl : Ω ⊆ Ω) =
      ContinuousLinearMap.id ℝ (WkpAmbientOn n k p Ω) := by
  apply ContinuousLinearMap.ext
  intro U
  apply PiLp.ext
  intro a
  simp only [restrictAmbient_apply, ContinuousLinearMap.id_apply]
  rw [restrictDerivLp_self]
  rfl

/-- Coordinatewise restriction of ambient Sobolev bundles is functorial. -/
theorem restrictAmbient_comp
    {Ω₁ Ω₂ Ω₃ : Set (ℝ^n)}
    (h₁₂ : Ω₁ ⊆ Ω₂) (h₂₃ : Ω₂ ⊆ Ω₃) :
    (restrictAmbient (n := n) (k := k) (p := p) h₁₂).comp
        (restrictAmbient (n := n) (k := k) (p := p) h₂₃) =
      restrictAmbient (n := n) (k := k) (p := p) (h₁₂.trans h₂₃) := by
  apply ContinuousLinearMap.ext
  intro U
  apply PiLp.ext
  intro a
  simp only [ContinuousLinearMap.comp_apply, restrictAmbient_apply]
  have hcomp :=
    congrArg
      (fun T : DerivLp n p Ω₃ →L[ℝ] DerivLp n p Ω₁ ↦ T (U a))
      (restrictDerivLp_comp
        (n := n) (p := p) h₁₂ h₂₃)
  simpa only [ContinuousLinearMap.comp_apply] using hcomp

/-- Restriction to a measurable subdomain preserves the weak-derivative graph
relations of the ambient bundle. -/
theorem restrictAmbient_mapsIsWkpOn
    (hΩ : MeasurableSet Ω) (hsub : Ω ⊆ Ωbig)
    (U : WkpAmbientOn n k p Ωbig)
    (hU : IsWkpOn (n := n) (k := k) (p := p) (Ω := Ωbig) U) :
    IsWkpOn (n := n) (k := k) (p := p) (Ω := Ω)
      (restrictAmbient (n := n) (k := k) (p := p) hsub U) := by
  intro a
  have hweak := HasWeakDerivativeOn.mono (n := n) hΩ hsub (hU a)
  have hbase := restrictDerivLp_apply_ae (n := n) (p := p) hsub
    (U (baseIndex n k))
  have ha := restrictDerivLp_apply_ae (n := n) (p := p) hsub (U a)
  exact (hasWeakDerivativeOn_congr_ae
    (n := n) (Ω := Ω) (α := a.toList)
    (by simpa [restrictAmbient_apply] using hbase)
    (by simpa [restrictAmbient_apply] using ha)).2 hweak

/-- Restriction is a bounded linear map between the weak-derivative graph spaces whenever
`Ω` is a measurable subset of `Ωbig`.  If both sets are open, this is the usual bounded Sobolev
restriction `W^{k,p}(Ωbig) → W^{k,p}(Ω)`. -/
noncomputable def restrictCLM (hΩ : MeasurableSet Ω) (hsub : Ω ⊆ Ωbig) :
    W^{k,p}(Ωbig) →L[ℝ] W^{k,p}(Ω) :=
  ContinuousLinearMap.codRestrict
    ((restrictAmbient (n := n) (k := k) (p := p) hsub).comp
      (Submodule.subtypeL (wkpSubmoduleOn n k p Ωbig)))
    (wkpSubmoduleOn n k p Ω)
    (fun U ↦ restrictAmbient_mapsIsWkpOn
      (n := n) (k := k) (p := p) hΩ hsub U U.property)

/-- On underlying bundles, `restrictCLM` is `restrictAmbient`; the graph-space version only adds
the proof that the weak-derivative identities descend to `Ω`. -/
@[simp] theorem restrictCLM_apply_coe
    (hΩ : MeasurableSet Ω) (hsub : Ω ⊆ Ωbig)
    (U : W^{k,p}(Ωbig)) :
    ((restrictCLM (n := n) (k := k) (p := p) hΩ hsub U :
        W^{k,p}(Ω)) : WkpAmbientOn n k p Ω) =
      restrictAmbient (n := n) (k := k) (p := p) hsub U :=
  rfl

/-- Domain restriction contracts the Sobolev graph norm. -/
theorem norm_restrictCLM_apply_le
    (hΩ : MeasurableSet Ω) (hsub : Ω ⊆ Ωbig)
    (U : W^{k,p}(Ωbig)) :
    ‖restrictCLM (n := n) (k := k) (p := p) hΩ hsub U‖ ≤ ‖U‖ := by
  change
    ‖restrictAmbient (n := n) (k := k) (p := p) hsub
      (U : WkpAmbientOn n k p Ωbig)‖ ≤
      ‖(U : WkpAmbientOn n k p Ωbig)‖
  exact norm_restrictAmbient_apply_le
    (n := n) (k := k) (p := p) (Ω := Ω) (Ωbig := Ωbig)
    hsub (U : WkpAmbientOn n k p Ωbig)

/-- The operator norm of Sobolev graph-space restriction is at most one. -/
theorem norm_restrictCLM_le_one
    (hΩ : MeasurableSet Ω) (hsub : Ω ⊆ Ωbig) :
    ‖restrictCLM (n := n) (k := k) (p := p) hΩ hsub‖ ≤ 1 :=
  (restrictCLM (n := n) (k := k) (p := p) hΩ hsub).opNorm_le_bound
    zero_le_one fun U ↦ by
      simpa only [one_mul] using
        norm_restrictCLM_apply_le
          (n := n) (k := k) (p := p) (Ω := Ω) (Ωbig := Ωbig)
          hΩ hsub U

/-- Restriction preserves every represented derivative coordinate almost
everywhere on the smaller domain. -/
theorem restrictCLM_apply_ae
    (hΩ : MeasurableSet Ω) (hsub : Ω ⊆ Ωbig)
    (U : W^{k,p}(Ωbig)) (a : DerivIndex n k) :
    ((((restrictCLM (n := n) (k := k) (p := p) hΩ hsub U :
        W^{k,p}(Ω)) : WkpAmbientOn n k p Ω) a : DerivLp n p Ω) :
        ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        (((U : WkpAmbientOn n k p Ωbig) a : DerivLp n p Ωbig) : ℝ^n → ℝ) := by
  simpa [restrictCLM_apply_coe, restrictAmbient_apply] using
    restrictDerivLp_apply_ae (n := n) (p := p) hsub
      ((U : WkpAmbientOn n k p Ωbig) a)

/-- Restricting a Sobolev graph-space element to the same domain is the
identity. -/
theorem restrictCLM_self (hΩ : MeasurableSet Ω) :
    restrictCLM (n := n) (k := k) (p := p) hΩ
        (Set.Subset.rfl : Ω ⊆ Ω) =
      ContinuousLinearMap.id ℝ (W^{k,p}(Ω)) := by
  apply ContinuousLinearMap.ext
  intro U
  apply Subtype.ext
  have hself :=
    congrArg
      (fun T : WkpAmbientOn n k p Ω →L[ℝ] WkpAmbientOn n k p Ω ↦
        T (U : WkpAmbientOn n k p Ω))
      (restrictAmbient_self (n := n) (k := k) (p := p))
  simpa only [restrictCLM_apply_coe, ContinuousLinearMap.id_apply] using hself

/-- Sobolev graph-space restriction is functorial under nested measurable
domains. -/
theorem restrictCLM_comp
    {Ω₁ Ω₂ Ω₃ : Set (ℝ^n)}
    (hΩ₁ : MeasurableSet Ω₁) (hΩ₂ : MeasurableSet Ω₂)
    (h₁₂ : Ω₁ ⊆ Ω₂) (h₂₃ : Ω₂ ⊆ Ω₃) :
    (restrictCLM (n := n) (k := k) (p := p) hΩ₁ h₁₂).comp
        (restrictCLM (n := n) (k := k) (p := p) hΩ₂ h₂₃) =
      restrictCLM (n := n) (k := k) (p := p)
        hΩ₁ (h₁₂.trans h₂₃) := by
  apply ContinuousLinearMap.ext
  intro U
  apply Subtype.ext
  have hcomp :=
    congrArg
      (fun T : WkpAmbientOn n k p Ω₃ →L[ℝ] WkpAmbientOn n k p Ω₁ ↦
        T (U : WkpAmbientOn n k p Ω₃))
      (restrictAmbient_comp
        (n := n) (k := k) (p := p) h₁₂ h₂₃)
  simpa only [ContinuousLinearMap.comp_apply, restrictCLM_apply_coe] using hcomp

end Restriction

end GraphSpace

end SobolevSpace
