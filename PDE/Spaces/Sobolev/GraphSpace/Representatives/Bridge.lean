/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Model.Notation
public import PDE.Spaces.Sobolev.Foundations.Representatives.Definitions
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# Graph-space and representative Sobolev models

We relate the quotient-level graph-space model
`WkpSpaceOn` to the representative-level model `SobolevSpaceOn`. Passing to a
representative uses the stored derivative coordinates. Passing in the other
direction chooses representatives for the weak derivatives, so it is
noncanonical.

`SobolevSpaceOn` follows Evans's definition of `W^{k,p}(U)` in §5.2.2: a function in `L^p` whose
weak derivatives `D^α u`, `|α| ≤ k`, exist and lie in `L^p`. The graph model stores these
derivatives as coordinates. `toRepresentative` keeps the order-zero coordinate, and on an open
domain `ofRepresentative_toRepresentative` shows that nothing is lost: by the uniqueness of weak
derivatives, Evans §5.2.1, Lemma (`HasWeakDerivativeOn.unique_ae`), every chosen derivative
coordinate agrees almost everywhere with the stored one.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.1, Lemma (Uniqueness of weak derivatives), p. 257; and
  §5.2.2, definition of `W^{k,p}(U)`, p. 258.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory ENNReal
open scoped Sobolev

variable {n k : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)}

/-- Read a Sobolev graph-space element through its canonical coordinate representatives. -/
noncomputable def toRepresentative (U : W^{k,p}(Ω)) : SobolevSpaceOn n k p Ω where
  toFun := (U : WkpAmbientOn n k p Ω) (baseIndex n k)
  memLp := by
    simpa using (MeasureTheory.Lp.memLp ((U : WkpAmbientOn n k p Ω) (baseIndex n k)))
  weak_derivs_inLp := by
    intro α hαk
    let a : DerivIndex n k := derivIndexOfList (n := n) (k := k) α hαk
    refine ⟨(U : WkpAmbientOn n k p Ω) a, ?_, ?_⟩
    · simpa using (MeasureTheory.Lp.memLp ((U : WkpAmbientOn n k p Ω) a))
    · simpa [a] using
        U.property.hasWeakDerivativeOn_list α hαk

/-- The function underlying `toRepresentative U` is the canonical order-zero representative
`baseRepresentative U`. -/
@[simp]
theorem toRepresentative_toFun (U : W^{k,p}(Ω)) :
    (toRepresentative U).toFun = baseRepresentative U :=
  rfl

variable [Fact (1 ≤ p)]

/-- Package a representative-level Sobolev function as a graph-space value.

The construction chooses one weak-derivative representative for every
derivative index, so no computational canonicity is claimed. -/
noncomputable def ofRepresentative (u : SobolevSpaceOn n k p Ω) : W^{k,p}(Ω) :=
  let μΩ : Measure (ℝ^n) := domainMeasure n Ω
  let choice :
      ∀ a : DerivIndex n k,
        { g : ℝ^n → ℝ //
          MeasureTheory.MemLp g p μΩ ∧
            HasWeakDerivativeOn (n := n) Ω a.toList u.toFun g } :=
    fun a ↦
      if ha : a = baseIndex n k then
        ⟨u.toFun, u.memLp, by
          subst ha
          have hloc := memLp_locallyIntegrableOn_domain u.memLp
            (Fact.out : (1 : ℝ≥0∞) ≤ p)
          simpa only [baseIndex_toList] using hasWeakDerivativeOn_nil hloc⟩
      else
        let hlen : a.toList.length ≤ k := a.toList_length_le
        let w := u.weak_derivs_inLp a.toList hlen
        ⟨Classical.choose w, (Classical.choose_spec w).1, by
          simpa using (Classical.choose_spec w).2⟩
  let U : WkpAmbientOn n k p Ω :=
    WithLp.toLp p (fun a ↦ (choice a).property.1.toLp (choice a).1)
  ⟨U, by
    intro a
    refine ⟨memLp_locallyIntegrableOn_domain (MeasureTheory.Lp.memLp _) Fact.out,
      memLp_locallyIntegrableOn_domain (MeasureTheory.Lp.memLp _) Fact.out, ?_⟩
    intro φ hφ
    have hbase_ae :
        (U (baseIndex n k) : ℝ^n → ℝ) =ᵐ[μΩ] u.toFun := by
      simpa [U, choice, μΩ] using
        (u.memLp.coeFn_toLp :
          (u.memLp.toLp u.toFun : ℝ^n → ℝ) =ᵐ[μΩ] u.toFun)
    have hUae : (U a : ℝ^n → ℝ) =ᵐ[μΩ] (choice a).1 := by
      simpa [U] using
        ((choice a).property.1.coeFn_toLp :
          ((choice a).property.1.toLp (choice a).1 : ℝ^n → ℝ) =ᵐ[μΩ] (choice a).1)
    have hweak : HasWeakDerivativeOn (n := n) Ω a.toList u.toFun (choice a).1 :=
      (choice a).property.2
    have hbase :
        (∫ x, (U (baseIndex n k)) x *
            iteratedPartialDeriv (n := n) a.toList φ.toFun x ∂μΩ) =
          ∫ x, u.toFun x *
            iteratedPartialDeriv (n := n) a.toList φ.toFun x ∂μΩ := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hbase_ae] with x hx
      simp [hx]
    have hderiv :
        (∫ x, (U a) x * φ.toFun x ∂μΩ) =
          ∫ x, (choice a).1 x * φ.toFun x ∂μΩ := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hUae] with x hx
      simp [hx]
    calc
      (∫ x, (U (baseIndex n k)) x *
          iteratedPartialDeriv (n := n) a.toList φ.toFun x ∂μΩ) =
          ∫ x, u.toFun x *
            iteratedPartialDeriv (n := n) a.toList φ.toFun x ∂μΩ := hbase
      _ = (-1) ^ a.toList.length *
          (∫ x, (choice a).1 x * φ.toFun x ∂μΩ) := by
        simpa only [μΩ] using hweak φ hφ
      _ = (-1) ^ a.toList.length *
          (∫ x, (U a) x * φ.toFun x ∂μΩ) := by rw [hderiv]⟩

/-- The order-zero coordinate of `ofRepresentative u` is `u.toFun` almost everywhere on `Ω`.
No choice is involved in this coordinate: it is `u.toFun` packaged into `Lᵖ` through `u.memLp`. -/
theorem ofRepresentative_base_ae (u : SobolevSpaceOn n k p Ω) :
    (((ofRepresentative u : WkpAmbientOn n k p Ω) (baseIndex n k) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] u.toFun) := by
  simpa [ofRepresentative] using
    (u.memLp.coeFn_toLp :
      (u.memLp.toLp u.toFun : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] u.toFun)

/-- Converting a representative package to graph space and reading its base
coordinate back recovers the original representative almost everywhere. -/
theorem toRepresentative_ofRepresentative_toFun_ae
    (u : SobolevSpaceOn n k p Ω) :
    (toRepresentative (ofRepresentative u)).toFun
      =ᵐ[domainMeasure n Ω] u.toFun :=
  ofRepresentative_base_ae u

/-- On an open domain, converting a graph-space element to a representative
package and back is the identity.

The reverse construction chooses representatives for the derivative
coordinates. Openness makes those choices irrelevant: uniqueness of weak
derivatives identifies every chosen coordinate with the original `Lp`
coordinate almost everywhere. -/
theorem ofRepresentative_toRepresentative
    (hΩ : IsOpen Ω) (U : W^{k,p}(Ω)) :
    ofRepresentative (toRepresentative U) = U := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  apply MeasureTheory.Lp.ext
  have hbase :
      (((ofRepresentative (toRepresentative U) :
          WkpAmbientOn n k p Ω) (baseIndex n k) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω]
          ((U : WkpAmbientOn n k p Ω) (baseIndex n k) : ℝ^n → ℝ)) := by
    simpa [toRepresentative] using
      ofRepresentative_base_ae (u := toRepresentative U)
  have hchosen :
      HasWeakDerivativeOn (n := n) Ω a.toList
        ((U : WkpAmbientOn n k p Ω) (baseIndex n k))
        ((ofRepresentative (toRepresentative U) :
          WkpAmbientOn n k p Ω) a) := by
    exact
      (hasWeakDerivativeOn_congr_ae
        (n := n) (Ω := Ω) (α := a.toList)
        hbase (MeasureTheory.ae_eq_refl _)).mp
        ((ofRepresentative (toRepresentative U)).property a)
  exact hchosen.unique_ae hΩ (U.property a)

end SobolevSpace.GraphSpace

end
