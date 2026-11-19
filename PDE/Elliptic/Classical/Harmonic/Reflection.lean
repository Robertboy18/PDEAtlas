/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.Definitions
public import PDE.Common.Euclidean.CoordinateReflection
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Odd reflection of harmonic functions across a coordinate hyperplane

The Schwarz reflection principle in the form used for Dirichlet problems on a half-space: if `g`
is `C²` on the closed half-space `{x | 0 ≤ x k}`, harmonic in the open half-space and zero on the
hyperplane `{x | x k = 0}`, then its odd reflection

`oddReflection k g x = g x` for `0 ≤ x k`, `-g (Rₖ x)` for `x k < 0`

is harmonic on all of `ℝⁿ`. Evans poses this on the unit half-ball as Problem 10 (a) of §2.5; we
work on a half-space bounded by any coordinate hyperplane.

The proof glues derivatives on the two closed half-spaces. On the hyperplane, `g = 0` kills the
tangential first and second derivatives, and the equation `Δg = 0`, which extends to the
hyperplane by continuity of the second derivative, kills `∂ₖ∂ₖ g`. These are exactly the
conditions under which the one-sided first and second derivatives of the reflection agree.

## Main definitions

* `oddReflection`: `g` on `{x | 0 ≤ x k}` and `-g ∘ Rₖ` on the other side.

## Main results

* `contDiff_oddReflection`: under the hypotheses above the odd reflection is `C²` on `ℝⁿ`.
* `isHarmonicPDE_oddReflection`: the odd reflection is harmonic on `ℝⁿ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.5, Problem 10 (a) (Reflection principle), p. 86.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open PDE (laplacian)

namespace PDE.Common

/-- The odd reflection of `g` across the coordinate hyperplane `{x | x k = 0}`: `g` on the closed
half-space `{x | 0 ≤ x k}` and `-g ∘ Rₖ` on the other side. -/
def oddReflection {n : ℕ} (k : Fin n) (g : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  if 0 ≤ x k then g x else -g (coordinateReflection k x)

end PDE.Common

namespace LaplacianEquation

open PDE.Common

variable {n : ℕ}

/-- A within-derivative on each of two closed sets covering the space is a derivative. -/
private theorem hasFDerivAt_of_isClosed_cover {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {A B : Set E} (hA : IsClosed A)
    (hB : IsClosed B) (hAB : A ∪ B = univ) {f : E → F} {f' : E → E →L[ℝ] F}
    (hfA : ∀ x ∈ A, HasFDerivWithinAt f (f' x) A x)
    (hfB : ∀ x ∈ B, HasFDerivWithinAt f (f' x) B x) (x : E) : HasFDerivAt f (f' x) x := by
  have h1 : HasFDerivWithinAt f (f' x) A x := by
    by_cases hx : x ∈ A
    · exact hfA x hx
    · exact HasFDerivWithinAt.of_notMem_closure (by rwa [hA.closure_eq])
  have h2 : HasFDerivWithinAt f (f' x) B x := by
    by_cases hx : x ∈ B
    · exact hfB x hx
    · exact HasFDerivWithinAt.of_notMem_closure (by rwa [hB.closure_eq])
  rw [← hasFDerivWithinAt_univ, ← hAB]
  exact h1.union h2

/-- For `j ≠ k` the `k`-th coordinate of the unit vector `eⱼ` is zero. -/
private theorem single_apply_of_ne {k j : Fin n} (h : j ≠ k) :
    (EuclideanSpace.single j (1 : ℝ) : ℝ^n) k = 0 := by
  simp [Ne.symm h]

/-- The derivatives of the odd reflection: a first derivative `D`, its derivative `D'`, which is
continuous, and the trace of `D'` vanishes. -/
private theorem exists_fderiv_oddReflection (k : Fin n) {g : ℝ^n → ℝ}
    (hg : ContDiffOn ℝ 2 g {x | 0 ≤ x k}) (hΔ : ∀ x, 0 < x k → laplacian g x = 0)
    (hb : ∀ x, x k = 0 → g x = 0) :
    ∃ D : ℝ^n → ℝ^n →L[ℝ] ℝ, ∃ D' : ℝ^n → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ,
      (∀ x, HasFDerivAt (oddReflection k g) (D x) x) ∧ (∀ x, HasFDerivAt D (D' x) x) ∧
      Continuous D' ∧
      ∀ x, ∑ j, D' x (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) = 0 := by
  set A : Set (ℝ^n) := {x | 0 ≤ x k} with hAdef
  set B : Set (ℝ^n) := {x | x k ≤ 0} with hBdef
  set e : ℝ^n := EuclideanSpace.single k 1
  have hAmem (z : ℝ^n) : z ∈ A ↔ 0 ≤ z k := Iff.rfl
  have hcoord : Continuous fun x : ℝ^n ↦ x k := (EuclideanSpace.proj k).continuous
  have hopen : IsOpen {x : ℝ^n | 0 < x k} := isOpen_lt continuous_const hcoord
  have hAc : IsClosed A := isClosed_le continuous_const hcoord
  have hBc : IsClosed B := isClosed_le hcoord continuous_const
  have hAB : A ∪ B = univ := eq_univ_of_forall fun x ↦ le_total 0 (x k)
  set R : ℝ^n →L[ℝ] ℝ^n :=
    (coordinateReflectionLinearIsometryEquiv k).toContinuousLinearEquiv.toContinuousLinearMap
  have hR : ∀ x, R x = coordinateReflection k x := fun x ↦ rfl
  have hRk : ∀ x, R x k = -x k := fun x ↦ coordinateReflection_apply_same k x
  have hRR : ∀ x, R (R x) = x := fun x ↦ coordinateReflection_involutive k x
  have hRfix : ∀ x : ℝ^n, x k = 0 → R x = x := fun x hx ↦
    (coordinateReflection_eq_self_iff k x).mpr hx
  have hRe : R e = -e := by
    rw [hR, coordinateReflection_single_same]
    ext j
    by_cases h : j = k <;> simp [e, h]
  have hmaps : MapsTo R B A := fun x hx ↦ by
    simp only [mem_ofPred_eq, hRk, A, B] at hx ⊢
    linarith
  have hU : UniqueDiffOn ℝ A := by
    refine uniqueDiffOn_convex
      (convex_halfSpace_ge (EuclideanSpace.proj k : ℝ^n →L[ℝ] ℝ).toLinearMap.isLinear 0)
      ⟨e, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact mem_of_superset (hopen.mem_nhds (by simp [e])) fun y hy ↦ (hAmem y).2 hy.le
  -- the derivatives of `g` within the closed half-space
  set D₁ := fderivWithin ℝ g A
  have hD₁ : ContDiffOn ℝ 1 D₁ A := hg.fderivWithin hU (by norm_num)
  set D₂ := fderivWithin ℝ D₁ A
  have hD₂ : ContinuousOn D₂ A := hD₁.continuousOn_fderivWithin hU le_rfl
  have hgA : ∀ x ∈ A, HasFDerivWithinAt g (D₁ x) A x := fun x hx ↦
    ((hg.differentiableOn (by norm_num)) x hx).hasFDerivWithinAt
  have hD₁A : ∀ x ∈ A, HasFDerivWithinAt D₁ (D₂ x) A x := fun x hx ↦
    ((hD₁.differentiableOn (by norm_num)) x hx).hasFDerivWithinAt
  -- lines along the hyperplane
  have hline : ∀ x : ℝ^n, x k = 0 → ∀ v : ℝ^n, v k = 0 →
      HasDerivWithinAt (fun t : ℝ ↦ x + t • v) v univ 0 ∧
        MapsTo (fun t : ℝ ↦ x + t • v) univ A ∧ ∀ t : ℝ, (x + t • v) k = 0 := by
    intro x hx v hv
    refine ⟨?_, fun t _ ↦ ?_, fun t ↦ ?_⟩
    · have h : HasDerivAt (fun t : ℝ ↦ t • v) v 0 := by
        simpa using HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) v
      exact HasDerivAt.hasDerivWithinAt (HasDerivAt.const_add x h)
    · simp [A, hx, hv]
    · simp [hx, hv]
  have hT1 : ∀ x : ℝ^n, x k = 0 → ∀ v : ℝ^n, v k = 0 → D₁ x v = 0 := by
    intro x hx v hv
    obtain ⟨hc, hmap, hzero⟩ := hline x hx v hv
    have h := (hgA x (by simp [A, hx])).comp_hasDerivWithinAt_of_eq 0 hc hmap (by simp)
    have hfun : (g ∘ fun t : ℝ ↦ x + t • v) = fun _ ↦ 0 := funext fun t ↦ hb _ (hzero t)
    rw [hfun, hasDerivWithinAt_univ] at h
    exact h.unique (hasDerivAt_const 0 0)
  have hT2 : ∀ x : ℝ^n, x k = 0 → ∀ v w : ℝ^n, v k = 0 → w k = 0 → D₂ x v w = 0 := by
    intro x hx v w hv hw
    obtain ⟨hc, hmap, hzero⟩ := hline x hx v hv
    have h := HasDerivWithinAt.clm_apply ((hD₁A x (by simp [A, hx])).comp_hasDerivWithinAt_of_eq
      0 hc hmap (by simp)) (hasDerivWithinAt_const (0 : ℝ) univ w)
    have hfun : (fun t : ℝ ↦ (D₁ ∘ fun t : ℝ ↦ x + t • v) t w) = fun _ ↦ 0 :=
      funext fun t ↦ hT1 _ (hzero t) w hw
    rw [hfun, hasDerivWithinAt_univ, map_zero, add_zero] at h
    exact h.unique (hasDerivAt_const 0 0)
  -- the equation on the closed half-space
  have htrace : ∀ x ∈ A,
      ∑ j, D₂ x (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) = 0 := by
    have hint : EqOn (fun x ↦ ∑ j, D₂ x (EuclideanSpace.single j 1) (EuclideanSpace.single j 1))
        0 {x : ℝ^n | 0 < x k} := by
      intro x hx
      have hxA : A ∈ 𝓝 x := mem_of_superset (hopen.mem_nhds hx) fun y hy ↦ (hAmem y).2 hy.le
      have hgx : ContDiffAt ℝ 2 g x := hg.contDiffAt hxA
      have heq : fderiv ℝ g =ᶠ[𝓝 x] D₁ := by
        filter_upwards [hopen.mem_nhds hx] with y hy
        exact (fderivWithin_of_mem_nhds
          (mem_of_superset (hopen.mem_nhds hy) fun y hy ↦ (hAmem y).2 hy.le)).symm
      have hdiff : DifferentiableAt ℝ (fderiv ℝ g) x :=
        (hgx.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
      have h2 : fderiv ℝ (fderiv ℝ g) x = D₂ x := by
        rw [heq.fderiv_eq]
        exact (fderivWithin_of_mem_nhds hxA).symm
      have h := hΔ x hx
      unfold laplacian at h
      simp only [PDE.secondPartialDeriv_eq_fderiv _ _ hdiff, h2] at h
      exact h
    have hcont : ContinuousOn
        (fun x ↦ ∑ j, D₂ x (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)) A :=
      continuousOn_finsetSum _ fun j _ ↦
        (hD₂.clm_apply continuousOn_const).clm_apply continuousOn_const
    refine hint.of_subset_closure hcont continuousOn_const (fun y hy ↦ (hAmem y).2 hy.le) ?_
    rw [show {x : ℝ^n | 0 < x k} = coordinateUpperHalfSpace k from rfl,
      closure_coordinateUpperHalfSpace]
  have hL : ∀ x : ℝ^n, x k = 0 → D₂ x e e = 0 := by
    intro x hx
    have h := htrace x (by simp [A, hx])
    rwa [Finset.sum_eq_single k (fun j _ hj ↦ hT2 x hx _ _ (single_apply_of_ne hj)
      (single_apply_of_ne hj)) (by simp)] at h
  -- the boundary symmetries of the one-sided derivatives
  have hS1 : ∀ x : ℝ^n, x k = 0 → D₁ x = -(D₁ x).comp R := by
    intro x hx
    ext v
    have h := hT1 x hx (v + R v) (by simp [hRk])
    rw [map_add] at h
    simp only [neg_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply]
    linarith
  have hsplit : ∀ v : ℝ^n, v = (v - v k • e) + v k • e ∧ R v = (v - v k • e) - v k • e ∧
      (v - v k • e) k = 0 := by
    intro v
    have ht : R (v - v k • e) = v - v k • e := hRfix _ (by simp [e])
    refine ⟨by abel, ?_, by simp [e]⟩
    calc R v = R (v - v k • e) + v k • R e := by rw [← map_smul, ← map_add]; abel_nf
      _ = _ := by rw [ht, hRe, smul_neg, ← sub_eq_add_neg]
  have hS2 : ∀ x : ℝ^n, x k = 0 → ∀ v w : ℝ^n, D₂ x (R v) (R w) = -D₂ x v w := by
    intro x hx v w
    have key : ∀ t s : ℝ^n, t k = 0 → s k = 0 → ∀ α β : ℝ,
        D₂ x (t - α • e) (s - β • e) = -D₂ x (t + α • e) (s + β • e) := by
      intro t s ht hs α β
      have h1 := hT2 x hx t s ht hs
      have h2 := hL x hx
      simp only [map_add, map_sub, map_smul, add_apply, sub_apply, smul_apply, smul_eq_mul, h1,
        h2]
      ring
    obtain ⟨hv, hRv, hvt⟩ := hsplit v
    obtain ⟨hw, hRw, hwt⟩ := hsplit w
    have h := key _ _ hvt hwt (v k) (w k)
    rwa [← hv, ← hw, ← hRv, ← hRw] at h
  -- the first derivative of the reflection
  set Ψ : (ℝ^n →L[ℝ] ℝ) →L[ℝ] (ℝ^n →L[ℝ] ℝ) :=
    -(ContinuousLinearMap.compL ℝ (ℝ^n) (ℝ^n) ℝ).flip R
  have hΨ : ∀ L : ℝ^n →L[ℝ] ℝ, Ψ L = -L.comp R := fun L ↦ rfl
  set D : ℝ^n → ℝ^n →L[ℝ] ℝ := fun x ↦ if 0 ≤ x k then D₁ x else Ψ (D₁ (R x))
  have hDA : ∀ x ∈ A, D x = D₁ x := fun x hx ↦ ite_eq_left hx
  have hDB : ∀ x ∈ B, D x = Ψ (D₁ (R x)) := by
    intro x hx
    by_cases h : 0 ≤ x k
    · have hx0 : x k = 0 := le_antisymm hx h
      simp only [D, ite_eq_left h, hRfix x hx0, hΨ]
      exact hS1 x hx0
    · exact ite_eq_right h
  have hHA : EqOn (oddReflection k g) g A := fun x hx ↦ ite_eq_left hx
  have hHB : EqOn (oddReflection k g) (fun x ↦ -g (R x)) B := by
    intro x hx
    by_cases h : 0 ≤ x k
    · have hx0 : x k = 0 := le_antisymm hx h
      simp only [oddReflection, ite_eq_left h, hR]
      rw [← hR, hRfix x hx0, hb x hx0, neg_zero]
    · exact ite_eq_right h
  have hfirst : ∀ x, HasFDerivAt (oddReflection k g) (D x) x := by
    refine hasFDerivAt_of_isClosed_cover hAc hBc hAB (fun x hx ↦ ?_) (fun x hx ↦ ?_)
    · rw [hDA x hx]
      exact (hgA x hx).congr hHA (hHA hx)
    · rw [hDB x hx, hΨ]
      have h := ((hgA (R x) (hmaps hx)).comp x R.hasFDerivWithinAt hmaps).neg
      exact h.congr hHB (hHB hx)
  -- the second derivative
  set F' : ℝ^n → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ := fun x ↦ Ψ.comp ((D₂ (R x)).comp R)
  have hF'apply : ∀ x v w, F' x v w = -D₂ (R x) (R v) (R w) := fun x v w ↦ rfl
  set D' : ℝ^n → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ := fun x ↦ if 0 ≤ x k then D₂ x else F' x
  have hD'A : ∀ x ∈ A, D' x = D₂ x := fun x hx ↦ ite_eq_left hx
  have hD'B : ∀ x ∈ B, D' x = F' x := by
    intro x hx
    by_cases h : 0 ≤ x k
    · have hx0 : x k = 0 := le_antisymm hx h
      simp only [D', ite_eq_left h]
      ext v w
      rw [hF'apply, hRfix x hx0, hS2 x hx0, neg_neg]
    · exact ite_eq_right h
  have hsecond : ∀ x, HasFDerivAt D (D' x) x := by
    refine hasFDerivAt_of_isClosed_cover hAc hBc hAB (fun x hx ↦ ?_) (fun x hx ↦ ?_)
    · rw [hD'A x hx]
      exact (hD₁A x hx).congr hDA (hDA x hx)
    · rw [hD'B x hx]
      have h := Ψ.hasFDerivAt.comp_hasFDerivWithinAt x
        ((hD₁A (R x) (hmaps hx)).comp x R.hasFDerivWithinAt hmaps)
      exact h.congr hDB (hDB x hx)
  have hcont : Continuous D' := by
    rw [← continuousOn_univ, ← hAB]
    refine ContinuousOn.union_of_isClosed ?_ ?_ hAc hBc
    · exact hD₂.congr hD'A
    · refine ContinuousOn.congr ?_ hD'B
      exact continuousOn_const.clm_comp
        ((hD₂.comp R.continuous.continuousOn hmaps).clm_comp continuousOn_const)
  refine ⟨D, D', hfirst, hsecond, hcont, fun x ↦ ?_⟩
  by_cases hx : 0 ≤ x k
  · rw [hD'A x hx]
    exact htrace x hx
  · have hxB : x ∈ B := le_of_lt (not_le.mp hx)
    rw [hD'B x hxB]
    have h := htrace (R x) (hmaps hxB)
    rw [← neg_eq_zero, ← h, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hF'apply, neg_neg]
    by_cases hj : j = k
    · subst hj
      rw [show EuclideanSpace.single j (1 : ℝ) = e from rfl, hRe]
      simp only [map_neg, neg_apply, neg_neg]
    · rw [hR (EuclideanSpace.single j 1), coordinateReflection_single_of_ne k j hj]

/-- **Odd reflection.** If `g` is `C²` on `{x | 0 ≤ x k}`, harmonic on `{x | 0 < x k}` and zero
on `{x | x k = 0}`, its odd reflection is `C²` on `ℝⁿ`. -/
theorem contDiff_oddReflection (k : Fin n) {g : ℝ^n → ℝ}
    (hg : ContDiffOn ℝ 2 g {x | 0 ≤ x k}) (hΔ : ∀ x, 0 < x k → laplacian g x = 0)
    (hb : ∀ x, x k = 0 → g x = 0) : ContDiff ℝ 2 (oddReflection k g) := by
  obtain ⟨D, D', h1, h2, hc, -⟩ := exists_fderiv_oddReflection k hg hΔ hb
  have hD : ContDiff ℝ ((0 : ℕ) + 1) D :=
    contDiff_succ_iff_hasFDerivAt.mpr
      ⟨D', by simpa using (contDiff_zero (𝕜 := ℝ) (f := D')).mpr hc, h2⟩
  have h : ContDiff ℝ ((1 : ℕ) + 1) (oddReflection k g) :=
    contDiff_succ_iff_hasFDerivAt.mpr ⟨D, by simpa using hD, h1⟩
  exact h

/-- **Schwarz reflection.** If `g` is `C²` on `{x | 0 ≤ x k}`, harmonic on `{x | 0 < x k}` and
zero on `{x | x k = 0}`, its odd reflection is harmonic on `ℝⁿ`. -/
theorem isHarmonicPDE_oddReflection (k : Fin n) {g : ℝ^n → ℝ}
    (hg : ContDiffOn ℝ 2 g {x | 0 ≤ x k}) (hΔ : ∀ x, 0 < x k → laplacian g x = 0)
    (hb : ∀ x, x k = 0 → g x = 0) : IsHarmonicPDE n (oddReflection k g) univ := by
  obtain ⟨D, D', h1, h2, -, htr⟩ := exists_fderiv_oddReflection k hg hΔ hb
  refine ⟨(contDiff_oddReflection k hg hΔ hb).contDiffOn, fun x _ ↦ ?_⟩
  have hfd : fderiv ℝ (oddReflection k g) = D := funext fun y ↦ (h1 y).fderiv
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (oddReflection k g)) x := by
    rw [hfd]; exact (h2 x).differentiableAt
  unfold laplacian
  simp only [PDE.secondPartialDeriv_eq_fderiv _ _ hdiff, hfd, (h2 x).fderiv]
  exact htr x

end LaplacianEquation
