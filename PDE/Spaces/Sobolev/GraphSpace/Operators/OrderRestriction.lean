/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Restriction
import PDE.Analysis.Normed.PiLp.Coordinatewise

/-!
# Restricting the order of a Sobolev derivative bundle

For `k ≤ m`, every `W^{m,p}(Ω)` function determines an element of `W^{k,p}(Ω)` by
forgetting the derivative coordinates of order greater than `k`. Because `WkpSpaceOn`
stores the finite bundle of weak derivatives, this inclusion is a map,

`lowerOrderCLM : W^{m,p}(Ω) →L[ℝ] W^{k,p}(Ω)`,

rather than an inclusion of sets. It is a contraction, every retained coordinate is the
corresponding coordinate of the original bundle, and it commutes with domain restriction.
We also define the coordinate projections `wkpCoordinateCLM` and `wkpBaseCoordinateCLM` and the
index map `DerivIndex.castOrder`.

Higher-regularity arguments use the map to compare weak-derivative relations between
functions of different Sobolev orders, for example successive time derivatives of a
solution, in one common lower-order space.

By Evans's definition of `W^{k,p}(U)` in §5.2.2, every `u ∈ W^{m,p}(U)` lies in `W^{k,p}(U)` for
`k ≤ m`, and the norm `‖u‖_{W^{k,p}(U)}` sums only over the multi-indices `|α| ≤ k`. `lowerOrderCLM`
is this inclusion for the graph model, with the norm bound `norm_lowerOrderCLM_le_one`. By
`restrictCLM_lowerOrderCLM` it commutes with the restriction `restrictCLM` to a measurable subset,
which for an open subset is §5.2.3, Theorem 1(iii).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.2, definitions of `W^{k,p}(U)` and its norm,
  pp. 258-259; and §5.2.3, Theorem 1(iii), p. 261.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace GraphSpace

open MeasureTheory
open scoped ENNReal Sobolev

variable {n k m r : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {Ω : Set (ℝ^n)}

/-! ## Coordinate projections -/

/--
Bounded projection onto one weak-derivative coordinate of a Sobolev bundle.
-/
noncomputable def wkpCoordinateCLM (a : DerivIndex n m) :
    W^{m,p}(Ω) →L[ℝ] DerivLp n p Ω :=
  (PiLp.proj (𝕜 := ℝ) (p := p)
    (β := fun _ : DerivIndex n m ↦ DerivLp n p Ω) a).comp
      (Submodule.subtypeL (wkpSubmoduleOn n m p Ω))

attribute [inherit_doc wkpCoordinateCLM] wkpCoordinateCLM.eq_1

/-- The coordinate projection reads off the `a`-th entry of the underlying derivative bundle. -/
@[simp]
theorem wkpCoordinateCLM_apply
    (a : DerivIndex n m) (U : W^{m,p}(Ω)) :
    wkpCoordinateCLM (n := n) (p := p) (Ω := Ω) a U =
      (U : WkpAmbientOn n m p Ω) a :=
  rfl

/-- Every Sobolev coordinate projection is contractive. -/
theorem wkpCoordinateCLM_norm_le
    (a : DerivIndex n m) (U : W^{m,p}(Ω)) :
    ‖wkpCoordinateCLM (n := n) (p := p) (Ω := Ω) a U‖ ≤ ‖U‖ := by
  simpa [wkpCoordinateCLM] using
    (PiLp.norm_apply_le (U : WkpAmbientOn n m p Ω) a)

/-- Bounded projection onto the order-zero coordinate of `W^{m,p}(Ω)`. -/
noncomputable def wkpBaseCoordinateCLM :
    W^{m,p}(Ω) →L[ℝ] DerivLp n p Ω :=
  wkpCoordinateCLM (n := n) (p := p) (Ω := Ω)
    (baseIndex n m)

attribute [inherit_doc wkpBaseCoordinateCLM] wkpBaseCoordinateCLM.eq_1

/-- The order-zero projection returns the `baseIndex` entry, the function itself. -/
@[simp]
theorem wkpBaseCoordinateCLM_apply
    (U : W^{m,p}(Ω)) :
    wkpBaseCoordinateCLM (n := n) (m := m) (p := p) (Ω := Ω) U =
      (U : WkpAmbientOn n m p Ω) (baseIndex n m) :=
  rfl

/-- The order-zero coordinate projection is contractive. -/
theorem wkpBaseCoordinateCLM_norm_le
    (U : W^{m,p}(Ω)) :
    ‖wkpBaseCoordinateCLM
        (n := n) (m := m) (p := p) (Ω := Ω) U‖ ≤ ‖U‖ :=
  wkpCoordinateCLM_norm_le (n := n) (p := p) (Ω := Ω)
    (baseIndex n m) U

/-- Spatial restriction commutes with the Sobolev base-coordinate projection. -/
theorem wkpBaseCoordinateCLM_restrictCLM {Ωbig : Set ℝ^n}
    (hΩ : MeasurableSet Ω) (hsub : Ω ⊆ Ωbig) (U : W^{m,p}(Ωbig)) :
    wkpBaseCoordinateCLM (restrictCLM hΩ hsub U) =
      restrictDerivLp hsub (wkpBaseCoordinateCLM U) :=
  rfl

namespace DerivIndex

/--
Regard a derivative index of order at most `k` as an index of order at most
`m`, assuming `k ≤ m`.

The underlying symmetric multi-index is unchanged; only its ambient order
bound is enlarged.
-/
def castOrder (hkm : k ≤ m) (a : DerivIndex n k) : DerivIndex n m :=
  ⟨⟨a.1.1, Nat.lt_succ_of_le ((Nat.lt_succ_iff.mp a.1.2).trans hkm)⟩, a.2⟩

attribute [inherit_doc castOrder] castOrder.eq_1

/-- Enlarging the order bound does not change the chosen list representative of the index. -/
@[simp]
theorem castOrder_toList (hkm : k ≤ m) (a : DerivIndex n k) :
    (a.castOrder hkm).toList = a.toList :=
  rfl

/-- The empty multi-index at order `k` is sent to the empty multi-index at order `m`. -/
@[simp]
theorem castOrder_baseIndex (hkm : k ≤ m) :
    (baseIndex n k).castOrder hkm = baseIndex n m := by
  rfl

/-- The first-derivative coordinate `∂_i` is preserved when the order bound is enlarged. -/
@[simp]
theorem castOrder_firstDerivIndex
    (hk : 0 < k) (hkm : k ≤ m) (i : Fin n) :
    (firstDerivIndex n k hk i).castOrder hkm =
      firstDerivIndex n m (hk.trans_le hkm) i := by
  rfl

/-- The second-derivative coordinate `∂_i ∂_j` is preserved when the order bound is enlarged. -/
@[simp]
theorem castOrder_secondDerivIndex
    (hk : 2 ≤ k) (hkm : k ≤ m) (i j : Fin n) :
    (secondDerivIndex n k hk i j).castOrder hkm =
      secondDerivIndex n m (hk.trans hkm) i j := by
  rfl

/-- The order-one coordinate `∂_i` viewed at order `m ≥ 1` is the general first-derivative
coordinate `firstDerivIndex n m _ i`. -/
@[simp]
theorem castOrder_singleDerivIndex (hm : 1 ≤ m) (i : Fin n) :
    (singleDerivIndex n i).castOrder hm =
      firstDerivIndex n m (by omega) i := by
  rfl

/-- The order-two coordinate `∂_i ∂_j` viewed at order `m ≥ 2` is the general second-derivative
coordinate `secondDerivIndex n m _ i j`. -/
@[simp]
theorem castOrder_pairDerivIndex (hm : 2 ≤ m) (i j : Fin n) :
    (pairDerivIndex n i j).castOrder hm =
      secondDerivIndex n m hm i j := by
  rfl

/--
Enlarging the ambient order in two stages gives the same derivative index as
enlarging it directly.
-/
theorem castOrder_trans
    (hrk : r ≤ k) (hkm : k ≤ m) (a : DerivIndex n r) :
    (a.castOrder hrk).castOrder hkm =
      a.castOrder (hrk.trans hkm) := by
  rfl

/-- Enlarging the ambient derivative-order bound is injective. -/
theorem castOrder_injective (hkm : k ≤ m) :
    Function.Injective (castOrder (n := n) hkm) := by
  intro a b hab
  have hord : a.1 = b.1 := by
    apply Fin.ext
    exact congrArg (fun c : DerivIndex n m ↦ c.1.1) hab
  apply Sigma.ext hord
  exact (Sigma.ext_iff.mp hab).2

end DerivIndex

/-! ## Ambient derivative-bundle map -/

/--
Bounded coordinate restriction between the finite `PiLp` Sobolev ambient
bundles.
-/
noncomputable def lowerOrderAmbient (hkm : k ≤ m) :
    WkpAmbientOn n m p Ω →L[ℝ] WkpAmbientOn n k p Ω :=
  let eHigh :=
    PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := p)
      (β := fun _ : DerivIndex n m ↦ DerivLp n p Ω)
  let eLow :=
    PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := p)
      (β := fun _ : DerivIndex n k ↦ DerivLp n p Ω)
  eLow.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun a ↦
        ContinuousLinearMap.proj (a.castOrder hkm)).comp
      eHigh.toContinuousLinearMap)


/-- Coordinate `a` of the restricted bundle is coordinate `a.castOrder hkm` of the original one:
the map only forgets entries, it never recombines them. -/
@[simp]
theorem lowerOrderAmbient_apply
    (hkm : k ≤ m) (U : WkpAmbientOn n m p Ω)
    (a : DerivIndex n k) :
    lowerOrderAmbient (n := n) (p := p) (Ω := Ω) hkm U a =
      U (a.castOrder hkm) :=
  rfl

/-- Forgetting higher derivative coordinates contracts the ambient Sobolev bundle. -/
theorem norm_lowerOrderAmbient_apply_le
    (hkm : k ≤ m) (U : WkpAmbientOn n m p Ω) :
    ‖lowerOrderAmbient (n := n) (p := p) (Ω := Ω) hkm U‖ ≤
      ‖U‖ :=
  PiLp.norm_mono_of_injective
    (DerivIndex.castOrder hkm) (DerivIndex.castOrder_injective hkm) _ _ fun _ ↦ le_rfl

/-- Forgetting the higher-order coordinates preserves the weak-derivative graph
relations of the ambient bundle. -/
theorem lowerOrderAmbient_mapsIsWkpOn
    (hkm : k ≤ m) (U : WkpAmbientOn n m p Ω)
    (hU : IsWkpOn (n := n) (k := m) (p := p) (Ω := Ω) U) :
    IsWkpOn (n := n) (k := k) (p := p) (Ω := Ω)
      (lowerOrderAmbient (n := n) (p := p) (Ω := Ω) hkm U) := by
  intro a
  simpa only [lowerOrderAmbient_apply, DerivIndex.castOrder_toList,
    DerivIndex.castOrder_baseIndex] using hU (a.castOrder hkm)

/-! ## Bounded map on Sobolev spaces -/

/--
The canonical bounded linear map
`W^{m,p}(Ω) → W^{k,p}(Ω)` for `k ≤ m`.
-/
noncomputable def lowerOrderCLM (hkm : k ≤ m) :
    W^{m,p}(Ω) →L[ℝ] W^{k,p}(Ω) :=
  ContinuousLinearMap.codRestrict
    ((lowerOrderAmbient (n := n) (p := p) (Ω := Ω) hkm).comp
      (Submodule.subtypeL (wkpSubmoduleOn n m p Ω)))
    (wkpSubmoduleOn n k p Ω)
    (fun U ↦
      lowerOrderAmbient_mapsIsWkpOn
        (n := n) (p := p) (Ω := Ω) hkm U U.property)

attribute [inherit_doc lowerOrderCLM] lowerOrderCLM.eq_1

/-- On underlying derivative bundles, `lowerOrderCLM` is `lowerOrderAmbient`; the Sobolev-space
version only adds the proof that the weak-derivative relations survive. -/
@[simp]
theorem lowerOrderCLM_apply_coe
    (hkm : k ≤ m) (U : W^{m,p}(Ω)) :
    ((lowerOrderCLM (n := n) (p := p) (Ω := Ω) hkm U :
        W^{k,p}(Ω)) : WkpAmbientOn n k p Ω) =
      lowerOrderAmbient (n := n) (p := p) (Ω := Ω) hkm
        (U : WkpAmbientOn n m p Ω) :=
  rfl

/--
Every retained weak-derivative coordinate is exactly the corresponding
coordinate of the higher-order Sobolev bundle.
-/
theorem lowerOrderCLM_apply
    (hkm : k ≤ m) (U : W^{m,p}(Ω))
    (a : DerivIndex n k) :
    ((lowerOrderCLM (n := n) (p := p) (Ω := Ω) hkm U :
        W^{k,p}(Ω)) : WkpAmbientOn n k p Ω) a =
      (U : WkpAmbientOn n m p Ω) (a.castOrder hkm) := by
  rfl

/-- Forgetting higher derivative coordinates preserves the canonical
order-zero representative exactly. -/
theorem baseRepresentative_lowerOrderCLM
    (hkm : k ≤ m) (U : W^{m,p}(Ω)) :
    baseRepresentative
        (lowerOrderCLM (n := n) (p := p) (Ω := Ω) hkm U) =
      baseRepresentative U := by
  funext x
  simp only [baseRepresentative, lowerOrderCLM_apply,
    DerivIndex.castOrder_baseIndex]

/-- Forgetting higher derivative coordinates preserves the base coordinate. -/
theorem wkpBaseCoordinateCLM_lowerOrderCLM
    (hkm : k ≤ m) (U : W^{m,p}(Ω)) :
    wkpBaseCoordinateCLM
        (lowerOrderCLM (n := n) (p := p) (Ω := Ω) hkm U) =
      wkpBaseCoordinateCLM U := by
  simp only [wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply,
    DerivIndex.castOrder_baseIndex]

/-- Forgetting higher derivative coordinates contracts the Sobolev graph norm. -/
theorem norm_lowerOrderCLM_apply_le
    (hkm : k ≤ m) (U : W^{m,p}(Ω)) :
    ‖lowerOrderCLM (n := n) (p := p) (Ω := Ω) hkm U‖ ≤
      ‖U‖ := by
  change
    ‖lowerOrderAmbient (n := n) (p := p) (Ω := Ω) hkm
      (U : WkpAmbientOn n m p Ω)‖ ≤
      ‖(U : WkpAmbientOn n m p Ω)‖
  exact norm_lowerOrderAmbient_apply_le hkm
    (U : WkpAmbientOn n m p Ω)

/-- The operator norm of Sobolev order restriction is at most one. -/
theorem norm_lowerOrderCLM_le_one (hkm : k ≤ m) :
    ‖lowerOrderCLM (n := n) (p := p) (Ω := Ω) hkm‖ ≤ 1 :=
  (lowerOrderCLM (n := n) (p := p) (Ω := Ω) hkm).opNorm_le_bound
    zero_le_one fun U ↦ by
      simpa only [one_mul] using
        norm_lowerOrderCLM_apply_le hkm U

/-- Lowering Sobolev order in two stages agrees with lowering it directly on each element. -/
theorem lowerOrderCLM_trans_apply
    (hrk : r ≤ k) (hkm : k ≤ m)
    (U : W^{m,p}(Ω)) :
    lowerOrderCLM (n := n) (p := p) (Ω := Ω) hrk
        (lowerOrderCLM (n := n) (p := p) (Ω := Ω) hkm U) =
      lowerOrderCLM (n := n) (p := p) (Ω := Ω)
        (hrk.trans hkm) U := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  simp only [lowerOrderCLM_apply, DerivIndex.castOrder_trans]

/-- Lowering Sobolev order in two stages is the direct order-restriction operator. -/
theorem lowerOrderCLM_trans
    (hrk : r ≤ k) (hkm : k ≤ m) :
    (lowerOrderCLM (n := n) (p := p) (Ω := Ω) hrk).comp
        (lowerOrderCLM (n := n) (p := p) (Ω := Ω) hkm) =
      lowerOrderCLM (n := n) (p := p) (Ω := Ω)
        (hrk.trans hkm) := by
  apply ContinuousLinearMap.ext
  exact lowerOrderCLM_trans_apply hrk hkm

/--
Restricting the domain commutes with forgetting the highest Sobolev
derivatives.

This identity is useful in local regularity arguments: coefficient and
forcing bundles may first be restricted to a smaller open set or first be
viewed at lower order, without changing any retained derivative coordinate.
-/
theorem restrictCLM_lowerOrderCLM_apply
    {OmegaSmall : Set (ℝ^n)}
    (hOmegaSmall : MeasurableSet OmegaSmall)
    (hsub : OmegaSmall ⊆ Ω)
    (hkm : k ≤ m)
    (U : W^{m,p}(Ω)) :
    restrictCLM (n := n) (k := k) (p := p) hOmegaSmall hsub
        (lowerOrderCLM (n := n) (p := p) (Ω := Ω) hkm U) =
      lowerOrderCLM (n := n) (p := p) (Ω := OmegaSmall) hkm
        (restrictCLM (n := n) (k := m) (p := p) hOmegaSmall hsub U) := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  simp only [restrictCLM_apply_coe, restrictAmbient_apply,
    lowerOrderCLM_apply]

/-- Domain restriction and order restriction commute as continuous linear maps. -/
theorem restrictCLM_lowerOrderCLM
    {OmegaSmall : Set (ℝ^n)}
    (hOmegaSmall : MeasurableSet OmegaSmall)
    (hsub : OmegaSmall ⊆ Ω)
    (hkm : k ≤ m) :
    (restrictCLM (n := n) (k := k) (p := p) hOmegaSmall hsub).comp
        (lowerOrderCLM (n := n) (p := p) (Ω := Ω) hkm) =
      (lowerOrderCLM (n := n) (p := p) (Ω := OmegaSmall) hkm).comp
        (restrictCLM (n := n) (k := m) (p := p) hOmegaSmall hsub) := by
  apply ContinuousLinearMap.ext
  exact restrictCLM_lowerOrderCLM_apply hOmegaSmall hsub hkm

/-- Restricting from order `k` to the same order fixes every element. -/
theorem lowerOrderCLM_refl_apply
    (U : W^{k,p}(Ω)) :
    lowerOrderCLM (n := n) (p := p) (Ω := Ω)
        (le_rfl : k ≤ k) U = U := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  simp only [lowerOrderCLM_apply]
  rfl

/-- Restriction from order `k` to the same order is the identity operator. -/
@[simp]
theorem lowerOrderCLM_refl :
    lowerOrderCLM (n := n) (p := p) (Ω := Ω)
        (le_rfl : k ≤ k) =
      ContinuousLinearMap.id ℝ (W^{k,p}(Ω)) := by
  apply ContinuousLinearMap.ext
  exact lowerOrderCLM_refl_apply

end GraphSpace
end SobolevSpace
