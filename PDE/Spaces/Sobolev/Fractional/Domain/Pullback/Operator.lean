/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Pullback.Graph

/-!
# Bounded pullback on intrinsic fractional spaces

The pullback of `Graph` is a bounded linear operator on the `GagliardoSpace` at all finite
exponents at least one, with operator norm at most
`(D + D² (L^(n / p.toReal + s))^p.toReal)^(1 / p.toReal)`. Pulling back along a chart and then
its inverse recovers the original element, so the operator is a continuous linear equivalence.
The quadratic case `p = 2` is in `Quadratic`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal FractionalSobolev

namespace SobolevSpace.Fractional.GagliardoSpace

variable {n : ℕ} {s : ℝ} {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)} {L D : ℝ≥0}

section General

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (hs : 0 ≤ (n : ℝ) / p.toReal + s) (hE : Measurable (fun x ↦ E x))
  (hL : LipschitzOnWith L E E.source)
  (hD : Measure.map E (volume.restrict E.source) ≤
    (D : ℝ≥0∞) • volume.restrict E.target)

/-- Bounded intrinsic pullback, constructed from the Gagliardo integral estimate. -/
def pullbackL (hp : p ≠ ∞) :
    W^{s,p}(E.target; F) →L[ℝ]
      W^{s,p}(E.source; F) :=
  LinearMap.mkContinuous
    { toFun := pullback hs hE hL hD
      map_add' := fun u v ↦ by
        apply toLp_injective
        apply Lp.ext
        have hq : QuasiMeasurePreserving E
            (volume.restrict E.source) (volume.restrict E.target) :=
          ⟨hE, Measure.absolutelyContinuous_of_le_smul hD⟩
        have hadd := hq.ae (Lp.coeFn_add (toLp n s E.target u) (toLp n s E.target v))
        have hout := Lp.coeFn_add
          (toLp n s E.source (pullback hs hE hL hD u))
          (toLp n s E.source (pullback hs hE hL hD v))
        simp only [map_add]
        filter_upwards [toLp_pullback_apply_ae hs hE hL hD (u + v),
          toLp_pullback_apply_ae hs hE hL hD u,
          toLp_pullback_apply_ae hs hE hL hD v, hadd, hout] with x hsum hu hv ha ho
        simpa only [Function.comp_apply, map_add] using
          hsum.trans (ha.trans ((congrArg₂ (· + ·) hu hv).symm.trans ho.symm))
      map_smul' := fun c u ↦ by
        apply toLp_injective
        apply Lp.ext
        have hq : QuasiMeasurePreserving E
            (volume.restrict E.source) (volume.restrict E.target) :=
          ⟨hE, Measure.absolutelyContinuous_of_le_smul hD⟩
        have hsmul := hq.ae (Lp.coeFn_smul c (toLp n s E.target u))
        have hout := Lp.coeFn_smul c (toLp n s E.source (pullback hs hE hL hD u))
        simp only [map_smul, RingHom.id_apply]
        filter_upwards [toLp_pullback_apply_ae hs hE hL hD (c • u),
          toLp_pullback_apply_ae hs hE hL hD u, hsmul, hout] with x hcu hu hc ho
        simpa only [Function.comp_apply, map_smul] using
          hcu.trans (hc.trans ((congrArg (c • ·) hu).symm.trans ho.symm)) }
    _ (norm_pullback_le_of_ne_top hs hE hL hD hp)

/-- The bounded operator has the intended physical representative. -/
theorem toLp_pullbackL_apply_ae (hp : p ≠ ∞) (u : W^{s,p}(E.target; F)) :
    (toLp n s E.source (pullbackL hs hE hL hD hp u) : ℝ^n → F) =ᵐ[volume.restrict E.source]
      (toLp n s E.target u : ℝ^n → F) ∘ E :=
  toLp_pullback_apply_ae hs hE hL hD u

/-- Pullback respects any chosen physical representative of its input. -/
theorem toLp_pullbackL_apply_ae_of_ae_eq (hp : p ≠ ∞)
    (u : W^{s,p}(E.target; F))
    {f : ℝ^n → F} (hf : (toLp n s E.target u : ℝ^n → F) =ᵐ[volume.restrict E.target] f) :
    (toLp n s E.source (pullbackL hs hE hL hD hp u) : ℝ^n → F) =ᵐ[volume.restrict E.source]
      f ∘ E := by
  have hq : QuasiMeasurePreserving E
      (volume.restrict E.source) (volume.restrict E.target) :=
    ⟨hE, Measure.absolutelyContinuous_of_le_smul hD⟩
  exact (toLp_pullbackL_apply_ae hs hE hL hD hp u).trans (hq.ae hf)

/-- On a function satisfying the intrinsic condition, pullback is ordinary composition. -/
theorem pullbackL_ofFunction (hp : p ≠ ∞) {f : ℝ^n → F}
    (hf : MemGagliardo n s E.target f (p := p)) :
    pullbackL hs hE hL hD hp (ofFunction f hf) =
      ofFunction (f ∘ E) (Pullback.memGagliardo_comp hs hE hL hD hf) := by
  apply toLp_injective
  apply Lp.ext
  exact (toLp_pullbackL_apply_ae_of_ae_eq hs hE hL hD hp _
    (toLp_ofFunction_apply_ae f hf)).trans (toLp_ofFunction_apply_ae _ _).symm

/-- Different valid numerical bounds define the same mathematical pullback operator. -/
theorem pullbackL_eq (hp : p ≠ ∞) {L' D' : ℝ≥0}
    (hL' : LipschitzOnWith L' E E.source)
    (hD' : Measure.map E (volume.restrict E.source) ≤
      (D' : ℝ≥0∞) • volume.restrict E.target) :
    pullbackL hs hE hL hD hp = pullbackL (F := F) hs hE hL' hD' hp := by
  apply ContinuousLinearMap.ext
  intro u
  apply toLp_injective
  apply Lp.ext
  exact (toLp_pullbackL_apply_ae hs hE hL hD hp u).trans
    (toLp_pullbackL_apply_ae hs hE hL' hD' hp u).symm

/-- The bounded pullback has the quantitative operator-norm bound. -/
theorem norm_pullbackL_le (hp : p ≠ ∞) :
    ‖pullbackL (F := F) hs hE hL hD hp‖ ≤
      ((D : ℝ) + ((L : ℝ) ^ ((n : ℝ) / p.toReal + s)) ^ p.toReal * (D : ℝ) ^ 2) ^
        (1 / p.toReal) :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (norm_pullback_le_of_ne_top hs hE hL hD hp)

variable {M J : ℝ≥0}
  (hSymm : Measurable (fun y ↦ E.symm y))
  (hM : LipschitzOnWith M E.symm E.target)
  (hJ : Measure.map E.symm (volume.restrict E.target) ≤
    (J : ℝ≥0∞) • volume.restrict E.source)

/-- Pulling back along a chart and then its inverse recovers the original
intrinsic element, as witnessed by the physical Lp representative. -/
theorem pullbackL_symm_pullbackL (hp : p ≠ ∞) (u : W^{s,p}(E.target; F)) :
    pullbackL hs hSymm hM hJ hp (pullbackL hs hE hL hD hp u) = u := by
  apply toLp_injective
  apply Lp.ext
  have hq : QuasiMeasurePreserving E.symm
      (volume.restrict E.target) (volume.restrict E.source) :=
    ⟨hSymm, Measure.absolutelyContinuous_of_le_smul hJ⟩
  filter_upwards [
    toLp_pullbackL_apply_ae hs hSymm hM hJ hp (pullbackL hs hE hL hD hp u),
    hq.ae (toLp_pullbackL_apply_ae hs hE hL hD hp u),
    ae_restrict_mem E.open_target.measurableSet] with y hy hxy hyT
  exact hy.trans (hxy.trans (congrArg (toLp n s E.target u) (E.right_inv hyT)))

/-- A chart with controlled distortion in both directions gives a bounded
equivalence of the intrinsic fractional spaces. -/
def pullbackEquiv (hp : p ≠ ∞ := by norm_num) :
    W^{s,p}(E.target; F) ≃L[ℝ]
      W^{s,p}(E.source; F) :=
  ContinuousLinearEquiv.equivOfInverse (pullbackL hs hE hL hD hp)
    (pullbackL hs hSymm hM hJ hp)
    (pullbackL_symm_pullbackL hs hE hL hD hSymm hM hJ hp)
    (pullbackL_symm_pullbackL hs hSymm hM hJ hE hL hD hp)

end General

end SobolevSpace.Fractional.GagliardoSpace
