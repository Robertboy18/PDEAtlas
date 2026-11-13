/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Integrability
import PDE.Spaces.Sobolev.Calculus.Slicing.FirstOrder

/-!
# Higher-order reciprocals of positive Sobolev coefficients

On a bounded Euclidean domain, a globally `C^k` representative of a
uniformly positive scalar coefficient has a reciprocal in
`W^{k,∞}`. Boundedness of the domain is used only to put the
continuous classical derivatives of the reciprocal in `L^∞`.

The statements are elementary: if `a` is `C^k` and `a ≥ δ > 0` a.e. on the
domain, then `x ↦ (a x)⁻¹` agrees a.e. with the `C^k` function
`safeInv δ ∘ a`, whose derivatives up to order `k` are continuous and hence
bounded on a bounded domain (or globally, when `a` is constant outside a
compact set). We produce the `W^{k,∞}` element, with
its full derivative bundle, from that observation; it is used to invert
leading coefficients of divergence-form operators.

## Main results

* `WkpSpaceOn.exists_reciprocal_of_contDiff_bounded`: on a bounded domain, a `C^k` coefficient
  bounded below by `δ > 0` a.e. has a `W^{k,∞}` reciprocal whose base coordinate is `a⁻¹`.
* `WkpSpaceOn.exists_reciprocal_of_contDiff_compactPerturbation`: the same on an arbitrary
  domain when `a` is constant outside a compact set.
* `memLp_top_iteratedPartialDeriv_of_contDiff_sub_const`: the `L^∞` bound on classical
  derivatives that drives the second result.

## Implementation notes

The reciprocal is realized through `SobolevSpace.Slices.safeInv δ`, a smooth function equal
to `r⁻¹` for `r ≥ δ` and to zero near `r = 0`. This gives a globally `C^k` representative
without any assumption on `a` off the domain or on the null set where `a < δ`.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n k : ℕ} {Ω : Set (ℝ^n)}

/-- Every nonempty iterated derivative is unchanged by subtracting a
constant. -/
theorem iteratedPartialDeriv_sub_const_of_differentiable
    (f : ℝ^n → ℝ) (hf : Differentiable ℝ f) (c : ℝ)
    (alpha : List (Fin n)) (halpha : alpha ≠ []) :
    (fun x ↦ iteratedPartialDeriv (n := n) alpha
      (fun y ↦ f y - c) x) =
      fun x ↦ iteratedPartialDeriv (n := n) alpha f x := by
  induction alpha with
  | nil => exact (halpha rfl).elim
  | cons i rest ih =>
      by_cases hrest : rest = []
      · subst rest
        funext x
        simp only [iteratedPartialDeriv]
        simpa using
          (PDE.partialDeriv_sub (n := n) (i := i) (f := f)
            (g := fun _ : ℝ^n ↦ c) (x := x)
            (hf x) (differentiableAt_const c))
      · simp only [iteratedPartialDeriv]
        rw [ih hrest]

/--
If a finitely smooth function differs from a constant by a compactly
supported function, every classical derivative through that finite order
belongs to `L∞` on an arbitrary domain.
-/
theorem memLp_top_iteratedPartialDeriv_of_contDiff_sub_const
    {m : ℕ} (f : ℝ^n → ℝ) (c : ℝ) (hf : ContDiff ℝ m f)
    (hcompact : HasCompactSupport (fun x ↦ f x - c))
    (U : Set (ℝ^n)) (a : DerivIndex n m) :
    MemLp (fun x ↦ iteratedPartialDeriv (n := n) a.toList f x)
      ∞ (domainMeasure n U) := by
  let g : ℝ^n → ℝ := fun x ↦ f x - c
  have hg : ContDiff ℝ m g := by
    simpa [g] using hf.sub contDiff_const
  have hlength : a.toList.length ≤ m := a.toList_length_le
  by_cases ha : a.toList = []
  · have hgMem : MemLp g ∞ (domainMeasure n U) :=
      hg.continuous.memLp_top_of_hasCompactSupport
        (by simpa [g] using hcompact) (domainMeasure n U)
    have hcMem : MemLp (fun _ : ℝ^n ↦ c) ∞ (domainMeasure n U) :=
      memLp_top_const c
    convert hgMem.add hcMem using 1
    funext x
    simp [ha, iteratedPartialDeriv, g]
  · have hderivCont : Continuous
        (fun x ↦ iteratedPartialDeriv (n := n) a.toList g x) :=
      (PDE.contDiff_iteratedPartialDeriv_of_le hg a.toList hlength).continuous
    have hderivCompact : HasCompactSupport
        (fun x ↦ iteratedPartialDeriv (n := n) a.toList g x) :=
      hasCompactSupport_iteratedPartialDeriv
        (n := n) (f := g) (by simpa [g] using hcompact) a.toList
    have hmem : MemLp
        (fun x ↦ iteratedPartialDeriv (n := n) a.toList g x)
        ∞ (domainMeasure n U) :=
      hderivCont.memLp_top_of_hasCompactSupport
        hderivCompact (domainMeasure n U)
    have heq :
        (fun x ↦ iteratedPartialDeriv (n := n) a.toList g x) =
          fun x ↦ iteratedPartialDeriv (n := n) a.toList f x := by
      have hmpos : 0 < m :=
        (List.length_pos_iff.mpr ha).trans_le hlength
      have hmne : (m : WithTop ℕ∞) ≠ 0 := by
        exact_mod_cast hmpos.ne'
      simpa [g] using
        iteratedPartialDeriv_sub_const_of_differentiable
          f (hf.differentiable hmne) c a.toList ha
    rwa [heq] at hmem

/--
A uniformly positive coefficient with a global `C^k` representative has a
`W^{k,infinity}` reciprocal on every bounded domain.

The returned base coordinate is the reciprocal of the selected classical
representative.
-/
theorem WkpSpaceOn.exists_reciprocal_of_contDiff_bounded
    (hOmegaBounded : Bornology.IsBounded Ω)
    (a : ℝ^n → ℝ)
    (ha : ContDiff ℝ k a)
    {delta : ℝ} (hdelta : 0 < delta)
    (hpositive :
      ∀ᵐ x ∂domainMeasure n Ω, delta ≤ a x) :
    ∃ R : W^{k,∞}(Ω),
      ((((R : WkpAmbientOn n k ∞ Ω) (baseIndex n k) :
        DerivLp n ∞ Ω) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Ω] fun x ↦ (a x)⁻¹ := by
  let reciprocal : ℝ^n → ℝ := fun x ↦
    SobolevSpace.Slices.safeInv delta (a x)
  have hreciprocal : ContDiff ℝ k reciprocal := by
    change ContDiff ℝ k (SobolevSpace.Slices.safeInv delta ∘ a)
    exact
      ((SobolevSpace.Slices.contDiff_safeInv delta hdelta).of_le (by
        exact WithTop.coe_le_coe.mpr
          (show (k : ℕ∞) ≤ ⊤ from le_top))).comp ha
  have hmem (alpha : DerivIndex n k) :
      MemLp
        (fun x ↦
          iteratedPartialDeriv (n := n) alpha.toList reciprocal x)
        ∞ (domainMeasure n Ω) := by
    have halpha : alpha.toList.length ≤ k := alpha.toList_length_le
    have hsmooth :=
      PDE.contDiff_iteratedPartialDeriv_of_le
        (n := n) hreciprocal alpha.toList halpha
    exact
      SobolevSpace.WeakChangeOfVariables.memLp_top_on_bounded_of_continuous
        hOmegaBounded hsmooth.continuous
  let R : W^{k,∞}(Ω) :=
    mkWkpSpaceOnOfContDiffMemLpFinite
      (n := n) (k := k) (p := (∞ : ENNReal)) (Ω := Ω)
      reciprocal hreciprocal hmem
  have hR :
      ((((R : WkpAmbientOn n k ∞ Ω) (baseIndex n k) :
        DerivLp n ∞ Ω) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Ω] reciprocal := by
    simpa [R, reciprocal, baseIndex_toList, iteratedPartialDeriv] using
      mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae
        (n := n) (k := k) (p := (∞ : ENNReal)) (Ω := Ω)
        reciprocal hreciprocal hmem (baseIndex n k)
  refine ⟨R, ?_⟩
  filter_upwards [hR, hpositive] with x hRx hpos
  rw [hRx, show reciprocal x =
      SobolevSpace.Slices.safeInv delta (a x) by rfl,
    SobolevSpace.Slices.safeInv_eq_inv hdelta hpos]

/--
A uniformly positive `C^k` coefficient which is constant outside a compact
set has a `W^{k,infinity}` reciprocal on an arbitrary domain.
-/
theorem WkpSpaceOn.exists_reciprocal_of_contDiff_compactPerturbation
    (a : ℝ^n → ℝ)
    (ha : ContDiff ℝ k a)
    (c : ℝ)
    (hcompact : HasCompactSupport (fun x ↦ a x - c))
    {delta : ℝ} (hdelta : 0 < delta)
    (hpositive :
      ∀ᵐ x ∂domainMeasure n Ω, delta ≤ a x) :
    ∃ R : W^{k,∞}(Ω),
      ((((R : WkpAmbientOn n k ∞ Ω) (baseIndex n k) :
        DerivLp n ∞ Ω) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Ω] fun x ↦ (a x)⁻¹ := by
  let reciprocal : ℝ^n → ℝ := fun x ↦
    SobolevSpace.Slices.safeInv delta (a x)
  have hreciprocal : ContDiff ℝ k reciprocal := by
    change ContDiff ℝ k (SobolevSpace.Slices.safeInv delta ∘ a)
    exact
      ((SobolevSpace.Slices.contDiff_safeInv delta hdelta).of_le (by
        exact WithTop.coe_le_coe.mpr
          (show (k : ℕ∞) ≤ ⊤ from le_top))).comp ha
  have hsupport :
      Function.support (fun x ↦
        reciprocal x - SobolevSpace.Slices.safeInv delta c) ⊆
        Function.support (fun x ↦ a x - c) := by
    intro x hx
    change reciprocal x - SobolevSpace.Slices.safeInv delta c ≠ 0 at hx
    change a x - c ≠ 0
    intro hac
    apply hx
    have haeq : a x = c := sub_eq_zero.mp hac
    rw [show reciprocal x =
      SobolevSpace.Slices.safeInv delta (a x) by rfl, haeq]
    simp
  have hreciprocalCompact :
      HasCompactSupport
        (fun x ↦ reciprocal x -
          SobolevSpace.Slices.safeInv delta c) :=
    HasCompactSupport.of_support_subset_isCompact
      hcompact.isCompact (hsupport.trans subset_closure)
  have hmem (alpha : DerivIndex n k) :
      MemLp
        (fun x ↦
          iteratedPartialDeriv (n := n) alpha.toList reciprocal x)
        ∞ (domainMeasure n Ω) :=
    memLp_top_iteratedPartialDeriv_of_contDiff_sub_const
      reciprocal (SobolevSpace.Slices.safeInv delta c) hreciprocal
        hreciprocalCompact Ω alpha
  let R : W^{k,∞}(Ω) :=
    mkWkpSpaceOnOfContDiffMemLpFinite
      (n := n) (k := k) (p := (∞ : ENNReal)) (Ω := Ω)
      reciprocal hreciprocal hmem
  have hR :
      ((((R : WkpAmbientOn n k ∞ Ω) (baseIndex n k) :
        DerivLp n ∞ Ω) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Ω] reciprocal := by
    simpa [R, reciprocal, baseIndex_toList, iteratedPartialDeriv] using
      mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae
        (n := n) (k := k) (p := (∞ : ENNReal)) (Ω := Ω)
        reciprocal hreciprocal hmem (baseIndex n k)
  refine ⟨R, ?_⟩
  filter_upwards [hR, hpositive] with x hRx hpos
  rw [hRx, show reciprocal x =
      SobolevSpace.Slices.safeInv delta (a x) by rfl,
    SobolevSpace.Slices.safeInv_eq_inv hdelta hpos]

end SobolevSpace.GraphSpace
