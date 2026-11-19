/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PartialRegularity
public import PDE.Spaces.Holder.HigherOrder.Derivatives

/-!
# Mixed derivatives of curves in Hölder spaces

Let `R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ` be curves in `C^{k,γ}` on `Ω`, each continuous on
`[a, b]`, such that `R (j + 1) t` is the derivative of `R j` within `[a, b]` at every `t ∈ [a, b]`
for `j < k`. The mixed field `mixedField R j α (x, t)` is the derivative field of multiindex `α` of
`R j t` at `x`, extended by zero outside `closure Ω`. It is continuous on `closure Ω ×ˢ Icc a b`
(`continuousOn_mixedField`), its time derivative within `[a, b]`, endpoints included, is the field
of `R (j + 1)` (`hasDerivWithinAt_mixedField`), and for open `Ω` it is `C^m` on `Ω ×ˢ Ioo a b` when
`j + α.order + m ≤ k` (`contDiffOn_mixedField`). The joint derivative comes from
`PDE.Analysis.hasFDerivAt_of_partial_derivatives`, which uses continuous partial differentials in
the two factors on the open cylinder, so we need no extension across the spatial boundary or the
time endpoints.
-/

@[expose] public section

noncomputable section

open Set
open scoped Topology

namespace HolderSpace.CKGammaOn

variable {n k : ℕ} {Ω : Set (ℝ^n)} {γ : Exponent} {a b : ℝ}

/-- The mixed field `(x, t) ↦ (R j t).interiorDerivative α x`: the derivative field of multiindex
`α` of `R j t`, extended by zero outside `closure Ω`. -/
def mixedField (R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ)
    (j : Fin (k + 1)) (α : MultiIndex n k) (p : ℝ^n × ℝ) : ℝ :=
  (R j p.2).interiorDerivative α p.1

/-- If every `R j` is continuous on `[a, b]`, then `mixedField R j α` is continuous on
`closure Ω ×ˢ Icc a b`. -/
theorem continuousOn_mixedField
    {R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ}
    (hR : ∀ j, ContinuousOn (R j) (Icc a b))
    (j : Fin (k + 1)) (α : MultiIndex n k) :
    ContinuousOn (mixedField R j α) (closure Ω ×ˢ Icc a b) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have ht : Continuous (fun p : closure Ω ×ˢ Icc a b ↦ R j p.1.2) :=
    (hR j).comp_continuous (continuous_snd.comp continuous_subtype_val)
      (fun p ↦ p.2.2)
  have hx : Continuous (fun p : closure Ω ×ˢ Icc a b ↦
      (⟨p.1.1, p.2.1⟩ : closure Ω)) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have he := ((derivativeCLM α).continuous.comp ht).eval hx
  convert he using 1
  funext p
  exact interiorDerivative_apply _ _ p.2.1

/-- If `R j.succ t` is the derivative of `R j.castSucc` within `[a, b]` at every `t ∈ [a, b]`, then
for `x ∈ closure Ω` and `t ∈ [a, b]`, endpoints included, `s ↦ mixedField R j.castSucc α (x, s)` has
derivative `mixedField R j.succ α (x, t)` within `[a, b]` at `t`. -/
theorem hasDerivWithinAt_mixedField
    {R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ}
    (hR : ∀ j : Fin k, ∀ t ∈ Icc a b,
      HasDerivWithinAt (R j.castSucc) (R j.succ t) (Icc a b) t)
    (j : Fin k) (α : MultiIndex n k) {x : ℝ^n} (hx : x ∈ closure Ω)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s ↦ mixedField R j.castSucc α (x, s))
      (mixedField R j.succ α (x, t)) (Icc a b) t := by
  let E : CKGammaOn n k Ω γ →L[ℝ] ℝ :=
    (BoundedContinuousFunction.evalCLM ℝ ⟨x, hx⟩).comp (derivativeCLM α)
  have hd := E.hasFDerivAt.comp_hasDerivWithinAt t (hR j t ht)
  simpa only [E, Function.comp_def, ContinuousLinearMap.comp_apply,
    BoundedContinuousFunction.evalCLM_apply, derivativeCLM_apply,
    mixedField, interiorDerivative_apply _ _ hx] using hd

/-- For `α.order < k` and `x ∈ Ω`, the map `y ↦ mixedField R j α (y, t)` has at `x` the derivative
`∑ i, mixedField R j (α.succ hα i) (x, t) • proj i`. -/
theorem hasFDerivAt_mixedField_space
    (R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ)
    (j : Fin (k + 1)) (α : MultiIndex n k) (hα : α.order < k)
    {x : ℝ^n} (hx : x ∈ Ω) (t : ℝ) :
    HasFDerivAt (fun y ↦ mixedField R j α (y, t))
      (∑ i : Fin n, mixedField R j (α.succ hα i) (x, t) •
        (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)) x := by
  simpa only [mixedField, interiorDerivative_apply _ _ (subset_closure hx)] using
    (R j t).hasFDerivAt_derivative α hα hx

/-- Under the hypothesis of `hasDerivWithinAt_mixedField`, for `x ∈ closure Ω` and `t ∈ (a, b)` the
map `s ↦ mixedField R j.castSucc α (x, s)` has Fréchet derivative
`mixedField R j.succ α (x, t) • id` at `t`. -/
theorem hasFDerivAt_mixedField_time
    {R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ}
    (hR : ∀ j : Fin k, ∀ t ∈ Icc a b,
      HasDerivWithinAt (R j.castSucc) (R j.succ t) (Icc a b) t)
    (j : Fin k) (α : MultiIndex n k) {x : ℝ^n} (hx : x ∈ closure Ω)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasFDerivAt (fun s ↦ mixedField R j.castSucc α (x, s))
      (mixedField R j.succ α (x, t) • ContinuousLinearMap.id ℝ ℝ) t := by
  have hd := (hasDerivWithinAt_mixedField hR j α hx (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  apply hd.hasFDerivAt.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [mul_comm]

/-- Let `Ω` be open, let every `R j` be continuous on `[a, b]` with `R j.succ` the derivative of
`R j.castSucc` within `[a, b]`, and let `α.order < k`. At `p ∈ Ω ×ˢ Ioo a b` the derivative of
`mixedField R j.castSucc α` is `D_x ∘ fst + D_t ∘ snd` with
`D_x = ∑ i, mixedField R j.castSucc (α.succ hα i) p • proj i` and
`D_t = mixedField R j.succ α p • id`. -/
theorem hasFDerivAt_mixedField
    {R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ} (hΩ : IsOpen Ω)
    (hcontinuous : ∀ j, ContinuousOn (R j) (Icc a b))
    (hderiv : ∀ j : Fin k, ∀ t ∈ Icc a b,
      HasDerivWithinAt (R j.castSucc) (R j.succ t) (Icc a b) t)
    (j : Fin k) (α : MultiIndex n k) (hα : α.order < k)
    {p : ℝ^n × ℝ} (hp : p ∈ Ω ×ˢ Ioo a b) :
    HasFDerivAt (mixedField R j.castSucc α)
      ((∑ i : Fin n, mixedField R j.castSucc (α.succ hα i) p •
        (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)).comp
          (ContinuousLinearMap.fst ℝ (ℝ^n) ℝ) +
        (mixedField R j.succ α p • ContinuousLinearMap.id ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ (ℝ^n) ℝ)) p := by
  have hc (l : Fin (k + 1)) (β : MultiIndex n k) :
      ContinuousOn (mixedField R l β) (Ω ×ˢ Ioo a b) :=
    (continuousOn_mixedField hcontinuous l β).mono
      (prod_mono subset_closure Ioo_subset_Icc_self)
  apply PDE.Analysis.hasFDerivAt_of_partial_derivatives (hΩ.prod isOpen_Ioo)
    (continuousOn_finsetSum _ fun i _ ↦
      (hc j.castSucc (α.succ hα i)).smul continuousOn_const)
    ((hc j.succ α).smul continuousOn_const)
    (fun q hq ↦ hasFDerivAt_mixedField_space R j.castSucc α hα hq.1 q.2)
    (fun q hq ↦ hasFDerivAt_mixedField_time hderiv j α (subset_closure hq.1) hq.2)
    hp

/-- For open `Ω` and curves `R j` continuous on `[a, b]` with `R j.succ` the derivative of
`R j.castSucc` within `[a, b]`, `mixedField R j α` is `C^m` on `Ω ×ˢ Ioo a b` whenever
`j + α.order + m ≤ k`. -/
theorem contDiffOn_mixedField
    {R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ} (hΩ : IsOpen Ω)
    (hcontinuous : ∀ j, ContinuousOn (R j) (Icc a b))
    (hderiv : ∀ j : Fin k, ∀ t ∈ Icc a b,
      HasDerivWithinAt (R j.castSucc) (R j.succ t) (Icc a b) t)
    (m : ℕ) (j : Fin (k + 1)) (α : MultiIndex n k)
    (hm : j.val + α.order + m ≤ k) :
    ContDiffOn ℝ m (mixedField R j α) (Ω ×ˢ Ioo a b) := by
  induction m generalizing j α with
  | zero =>
    exact contDiffOn_zero.mpr
      ((continuousOn_mixedField hcontinuous j α).mono
        (prod_mono subset_closure Ioo_subset_Icc_self))
  | succ m ih =>
    have hj : j.val < k := by omega
    have hα : α.order < k := by omega
    let j' : Fin k := ⟨j.val, hj⟩
    apply PDE.Analysis.contDiffOn_succ_of_partial_derivatives
      (hΩ.prod isOpen_Ioo)
      (D₁ := fun p ↦ ∑ i : Fin n,
        mixedField R j (α.succ hα i) p • EuclideanSpace.proj i)
      (D₂ := fun p ↦ mixedField R j'.succ α p • ContinuousLinearMap.id ℝ ℝ)
    · apply ContDiffOn.sum
      intro i _
      exact (ih j (α.succ hα i) (by simp only [MultiIndex.order_succ]; omega)).smul
        contDiffOn_const
    · exact (ih j'.succ α (by dsimp [j']; omega)).smul contDiffOn_const
    · intro p hp
      exact hasFDerivAt_mixedField_space R j α hα hp.1 p.2
    · intro p hp
      exact hasFDerivAt_mixedField_time hderiv j' α (subset_closure hp.1) hp.2

end HolderSpace.CKGammaOn
