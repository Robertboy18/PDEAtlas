/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import PDE.FDeriv.PartialDeriv
public import PDE.Spaces.Holder.HigherOrder.Graph
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Classical derivatives of higher-order Hölder functions

For `f : CKGammaOn n k Ω γ` and a multiindex `a`, `f.derivative a` is the derivative field of `f` on
`closure Ω` and `f.interiorDerivative a` is that field extended by zero to `ℝ^n`. The compatibility
relations of the graph give, for `a.order < k` and `x ∈ Ω`, the derivative
`∑ i, f.derivative (a.succ ha i) x • proj i` of `f.interiorDerivative a` at `x`
(`hasFDerivAt_derivative`), hence `C^m` regularity on open `Ω` when `a.order + m ≤ k`
(`contDiffOn_derivative`). The fields are determined by the zero-order field on `Ω` (`ext_of_eqOn`),
so `CKGammaOn n k Ω γ` is a type of functions on `closure Ω`. `jetEvalCLM x` collects the values of
all fields at a point `x` of the closure into one continuous linear map. On an open convex domain
the same formula holds within `closure Ω` at boundary points
(`hasFDerivWithinAt_derivative_closure`), by Mathlib's
`hasFDerivWithinAt_closure_of_tendsto_fderiv`. `ofDerivativeFields` builds an element from fields
that are continuous and bounded on the closure, with top-order Hölder bounds there and the
derivative relations on `Ω`.
-/

@[expose] public section

open PDE (partialDeriv)

noncomputable section

open Set
open scoped Topology BoundedContinuousFunction

namespace HolderSpace.CKGammaOn

variable {n k : ℕ} {Ω : Set (ℝ^n)} {γ : Exponent}

/-- The continuous extension to the closure of a coordinate derivative. -/
def derivative (f : CKGammaOn n k Ω γ) (a : MultiIndex n k) : closure Ω →ᵇ ℝ :=
  f.1.1 a

/-- Taking a derivative field is continuous and linear in the Hölder graph norm. -/
def derivativeCLM (a : MultiIndex n k) :
    CKGammaOn n k Ω γ →L[ℝ] (closure Ω →ᵇ ℝ) :=
  ((ContinuousLinearMap.proj a).comp (ContinuousLinearMap.fst ℝ _ _)).comp
    (JetData.compatibleSubmodule n k Ω γ).subtypeL

/-- The derivative projection evaluates to the corresponding continuous field. -/
@[simp]
theorem derivativeCLM_apply (a : MultiIndex n k) (f : CKGammaOn n k Ω γ) :
    derivativeCLM a f = f.derivative a :=
  rfl

/-- All derivative traces through order `k` at a point of the closure. At a boundary
point these are the continuous extensions of the interior derivatives. -/
def jetEvalCLM (x : closure Ω) : CKGammaOn n k Ω γ →L[ℝ] (MultiIndex n k → ℝ) :=
  ContinuousLinearMap.pi fun a ↦
    (BoundedContinuousFunction.evalCLM ℝ x).comp (derivativeCLM a)

/-- Each jet coordinate is the corresponding continuous derivative trace. -/
@[simp] theorem jetEvalCLM_apply (x : closure Ω) (f : CKGammaOn n k Ω γ)
    (a : MultiIndex n k) : jetEvalCLM x f a = f.derivative a x :=
  rfl

/-- The underlying function on the closure is the field of order zero. -/
def toBoundedContinuousFunction (f : CKGammaOn n k Ω γ) : closure Ω →ᵇ ℝ :=
  f.derivative 0

/-- The derivative field `f.derivative a`, extended by zero outside `closure Ω`. -/
def interiorDerivative (f : CKGammaOn n k Ω γ) (a : MultiIndex n k) : ℝ^n → ℝ :=
  Function.extend Subtype.val (f.derivative a) 0

/-- The interior expression agrees with the continuous derivative field. -/
theorem interiorDerivative_apply (f : CKGammaOn n k Ω γ) (a : MultiIndex n k)
    {x : ℝ^n} (hx : x ∈ closure Ω) :
    f.interiorDerivative a x = f.derivative a ⟨x, hx⟩ :=
  BoundedContinuousFunction.extend_zero_apply _ hx

section OfDerivativeFields

open scoped NNReal

/-- For open `Ω`, the element of `CKGammaOn n k Ω γ` with derivative fields `v a`, given that each
`v a` is continuous on `closure Ω` with `‖v a x‖ ≤ C a` there, each top-order field `v a` is
`H a`-Hölder on `closure Ω`, and for `a.order < k` and `x ∈ Ω` the map `v a` has derivative
`∑ i, v (a.succ ha i) x • proj i` at `x`. The bounds `C a` and `H a` may differ between fields. -/
def ofDerivativeFields (hΩ : IsOpen Ω) (v : MultiIndex n k → ℝ^n → ℝ)
    (hcont : ∀ a, ContinuousOn (v a) (closure Ω))
    (C : MultiIndex n k → ℝ≥0)
    (hbound : ∀ a x, x ∈ closure Ω → ‖v a x‖ ≤ C a)
    (H : MultiIndex.Top n k → ℝ≥0)
    (hholder : ∀ a, HolderOnWith (H a) (γ : ℝ≥0) (v a.1) (closure Ω))
    (hderiv : ∀ a (ha : a.order < k) x, x ∈ Ω →
      HasFDerivAt (v a)
        (∑ i : Fin n, v (a.succ ha i) x • (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)) x) :
    CKGammaOn n k Ω γ := by
  let V (a : MultiIndex n k) : closure Ω →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ v a x)
      (continuousOn_iff_continuous_domRestrict.mp (hcont a)) (C a)
      (fun x ↦ hbound a x x.2)
  let W (a : MultiIndex.Top n k) : C0GammaOn (closure Ω) γ :=
    ⟨V a.1, (HolderWith.restrict_iff.mpr (hholder a)).memHolder⟩
  refine ⟨(V, W), (fun _ ↦ rfl), ?_⟩
  intro a ha x hx
  have heq : Function.extend Subtype.val (V a) 0 =ᶠ[𝓝 x] v a := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact BoundedContinuousFunction.extend_zero_apply _ (subset_closure hy)
  have hgrad : JetData.gradientCLM a ha (V, W) ⟨x, subset_closure hx⟩ =
      ∑ i : Fin n, v (a.succ ha i) x • (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ) := by
    rw [JetData.gradientCLM_apply]
    rfl
  rw [hgrad]
  exact (hderiv a ha x hx).congr_of_eventuallyEq heq

variable (hΩ : IsOpen Ω) (v : MultiIndex n k → ℝ^n → ℝ)
  (hcont : ∀ a, ContinuousOn (v a) (closure Ω))
  (C : MultiIndex n k → ℝ≥0)
  (hbound : ∀ a x, x ∈ closure Ω → ‖v a x‖ ≤ C a)
  (H : MultiIndex.Top n k → ℝ≥0)
  (hholder : ∀ a, HolderOnWith (H a) (γ : ℝ≥0) (v a.1) (closure Ω))
  (hderiv : ∀ a (ha : a.order < k) x, x ∈ Ω →
    HasFDerivAt (v a)
      (∑ i : Fin n, v (a.succ ha i) x • (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)) x)

/-- The constructed graph retains the supplied field values, including boundary traces. -/
@[simp]
theorem derivative_ofDerivativeFields (a : MultiIndex n k) (x : closure Ω) :
    (ofDerivativeFields hΩ v hcont C hbound H hholder hderiv).derivative a x = v a x :=
  rfl

end OfDerivativeFields

/-- On a bounded domain, every continuous derivative extension is uniformly continuous. -/
theorem uniformContinuous_derivative_of_isBounded (f : CKGammaOn n k Ω γ)
    (a : MultiIndex n k) (hΩ : Bornology.IsBounded Ω) :
    UniformContinuous (f.derivative a) := by
  have : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp hΩ.isCompact_closure
  exact CompactSpace.uniformContinuous_of_continuous (f.derivative a).continuous

/-- `f.interiorDerivative a` is uniformly continuous on every bounded set `s ⊆ closure Ω`; `Ω`
itself may be unbounded. -/
theorem uniformContinuousOn_interiorDerivative_of_isBounded (f : CKGammaOn n k Ω γ)
    (a : MultiIndex n k) {s : Set (ℝ^n)} (hs : Bornology.IsBounded s)
    (hsΩ : s ⊆ closure Ω) : UniformContinuousOn (f.interiorDerivative a) s := by
  have hc := (f.derivative a).continuousOn_extend_zero.mono
    (closure_minimal hsΩ isClosed_closure)
  exact (hs.isCompact_closure.uniformContinuousOn_of_continuous hc).mono subset_closure

/-- For `a.order < k` and `x ∈ Ω`, `f.interiorDerivative a` has derivative
`∑ i, f.derivative (a.succ ha i) x • proj i` at `x`. -/
theorem hasFDerivAt_derivative (f : CKGammaOn n k Ω γ) (a : MultiIndex n k)
    (ha : a.order < k) {x : ℝ^n} (hx : x ∈ Ω) :
    HasFDerivAt (f.interiorDerivative a)
      (∑ i : Fin n, f.derivative (a.succ ha i) ⟨x, subset_closure hx⟩ •
        (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)) x := by
  simpa only [JetData.gradientCLM_apply, derivative, interiorDerivative] using f.2.2 a ha x hx

/-- If `Ω` is open and convex, `a.order < k` and `x ∈ closure Ω`, then `f.interiorDerivative a` has
derivative `∑ i, f.derivative (a.succ ha i) x • proj i` within `closure Ω` at `x`. -/
theorem hasFDerivWithinAt_derivative_closure (f : CKGammaOn n k Ω γ)
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) (a : MultiIndex n k)
    (ha : a.order < k) {x : ℝ^n} (hx : x ∈ closure Ω) :
    HasFDerivWithinAt (f.interiorDerivative a)
      (∑ i : Fin n, f.derivative (a.succ ha i) ⟨x, hx⟩ •
        (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)) (closure Ω) x := by
  let G : ℝ^n → ℝ^n →L[ℝ] ℝ :=
    Function.extend Subtype.val (JetData.gradientCLM a ha f.1) 0
  have hG : ContinuousOn G (closure Ω) :=
    (JetData.gradientCLM a ha f.1).continuousOn_extend_zero
  have heq (y : ℝ^n) (hy : y ∈ Ω) :
      fderiv ℝ (f.interiorDerivative a) y = G y := by
    rw [(f.hasFDerivAt_derivative a ha hy).fderiv]
    simp only [G, BoundedContinuousFunction.extend_zero_apply _ (subset_closure hy),
      JetData.gradientCLM_apply, derivative]
  have hlimit : Filter.Tendsto (fun y ↦ fderiv ℝ (f.interiorDerivative a) y)
      (𝓝[Ω] x) (𝓝 (G x)) := by
    apply ((hG x hx).mono subset_closure).congr'
    exact Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun y hy ↦ (heq y hy).symm
  have hboundary := hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy ↦ (f.hasFDerivAt_derivative a ha hy).differentiableAt.differentiableWithinAt)
    hconv hΩ (fun y hy ↦ ((f.derivative a).continuousOn_extend_zero y hy).mono subset_closure)
    hlimit
  simpa only [G, BoundedContinuousFunction.extend_zero_apply _ hx,
    JetData.gradientCLM_apply, derivative] using hboundary

/-- The gradient of a coordinate derivative field, assembled as a continuous linear
functional. Its values on the closure use the prescribed derivative traces. -/
def gradient (f : CKGammaOn n k Ω γ) (a : MultiIndex n k) (ha : a.order < k)
    (x : ℝ^n) : ℝ^n →L[ℝ] ℝ :=
  ∑ i : Fin n, f.interiorDerivative (a.succ ha i) x • EuclideanSpace.proj i

/-- The Hessian of a coordinate derivative field, as a curried bilinear form.
The first argument differentiates the gradient; the second evaluates that gradient. -/
def hessian (f : CKGammaOn n k Ω γ) (a : MultiIndex n k) (ha : a.order + 1 < k)
    (x : ℝ^n) : ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ :=
  ∑ i : Fin n,
    (f.gradient (a.succ (by omega) i) (by simp only [MultiIndex.order_succ]; omega) x).smulRight
      (EuclideanSpace.proj i)

/-- If `Ω` is open and convex, `a.order + 1 < k` and `x ∈ closure Ω`, then `f.gradient a` has
derivative `f.hessian a ha x` within `closure Ω` at `x`. -/
theorem hasFDerivWithinAt_gradient_closure (f : CKGammaOn n k Ω γ)
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) (a : MultiIndex n k)
    (ha : a.order + 1 < k) {x : ℝ^n} (hx : x ∈ closure Ω) :
    HasFDerivWithinAt (f.gradient a (by omega)) (f.hessian a ha x) (closure Ω) x := by
  dsimp only [gradient, hessian]
  refine HasFDerivWithinAt.fun_sum (𝕜 := ℝ) (u := Finset.univ) fun i _ ↦ ?_
  simpa only [interiorDerivative_apply _ _ hx] using
    (f.hasFDerivWithinAt_derivative_closure hΩ hconv (a.succ (by omega) i)
      (by simp only [MultiIndex.order_succ]; omega) hx).smul_const
        (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)

/-- For `a.order < k` and `x ∈ Ω`,
`∂[i] (f.interiorDerivative a) x = f.interiorDerivative (a.succ ha i) x`. -/
theorem partialDeriv_derivative (f : CKGammaOn n k Ω γ) (a : MultiIndex n k)
    (ha : a.order < k) (i : Fin n) {x : ℝ^n} (hx : x ∈ Ω) :
    (∂[i] (f.interiorDerivative a)) x =
      f.interiorDerivative (a.succ ha i) x := by
  rw [partialDeriv, (f.hasFDerivAt_derivative a ha hx).fderiv]
  rw [interiorDerivative_apply _ _ (subset_closure hx)]
  simp

/-- For open `Ω`, `f.interiorDerivative a` is `C^m` on `Ω` whenever `a.order + m ≤ k`. -/
theorem contDiffOn_derivative (f : CKGammaOn n k Ω γ) (hΩ : IsOpen Ω)
    (m : ℕ) (a : MultiIndex n k) (hm : a.order + m ≤ k) :
    ContDiffOn ℝ m (f.interiorDerivative a) Ω := by
  induction m generalizing a with
  | zero =>
    exact contDiffOn_zero.mpr
      ((f.derivative a).continuousOn_extend_zero.mono subset_closure)
  | succ m ih =>
    have ha : a.order < k := by omega
    rw [Nat.cast_add, Nat.cast_one]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hΩ.uniqueDiffOn).mpr
    refine ⟨by simp, (fun x ↦ ∑ i : Fin n,
      f.interiorDerivative (a.succ ha i) x • EuclideanSpace.proj i), ?_, ?_⟩
    · apply ContDiffOn.sum
      intro i _
      exact (ih (a.succ ha i) (by simp only [MultiIndex.order_succ]; omega)).smul
        contDiffOn_const
    · intro x hx
      convert (f.hasFDerivAt_derivative a ha hx).hasFDerivWithinAt using 1
      simp only [interiorDerivative_apply _ _ (subset_closure hx)]

/-- If `f.interiorDerivative a` and `g.interiorDerivative a` agree on `Ω`, then
`f.derivative a = g.derivative a`. -/
theorem derivative_eq_of_eqOn {f g : CKGammaOn n k Ω γ} (a : MultiIndex n k)
    (h : EqOn (f.interiorDerivative a) (g.interiorDerivative a) Ω) :
    f.derivative a = g.derivative a := by
  have hc := h.of_subset_closure (f.derivative a).continuousOn_extend_zero
    (g.derivative a).continuousOn_extend_zero subset_closure Subset.rfl
  apply BoundedContinuousFunction.ext
  intro x
  simpa only [interiorDerivative_apply _ _ x.2] using hc x.2

/-- If the zero-order fields of `f` and `g` agree on `Ω`, then `f = g`. -/
theorem ext_of_eqOn {f g : CKGammaOn n k Ω γ}
    (h : EqOn (f.interiorDerivative 0) (g.interiorDerivative 0) Ω) : f = g := by
  have hfields : ∀ m (a : MultiIndex n k), a.order = m → f.derivative a = g.derivative a := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro a ham
      by_cases ha : a.order = 0
      · rw [MultiIndex.eq_zero_of_order_eq_zero ha]
        exact derivative_eq_of_eqOn 0 h
      · obtain ⟨b, hb, i, rfl⟩ := MultiIndex.exists_pred ha
        have heq := ih b.order (by rw [MultiIndex.order_succ] at ham; omega) b rfl
        apply derivative_eq_of_eqOn
        intro x hx
        rw [← partialDeriv_derivative _ _ _ _ hx, ← partialDeriv_derivative _ _ _ _ hx]
        change (∂[i] (Function.extend Subtype.val (f.derivative b) 0)) x =
          (∂[i] (Function.extend Subtype.val (g.derivative b) 0)) x
        rw [heq]
  apply Subtype.ext
  apply Prod.ext
  · exact funext fun a ↦ hfields a.order a rfl
  · funext a
    apply C0GammaOn.toBoundedContinuousFunction_injective
    rw [f.2.1 a, g.2.1 a]
    exact hfields a.1.order a.1 rfl

/-- Hölder derivative graphs are functions: their zero-order values determine the graph. -/
instance : FunLike (CKGammaOn n k Ω γ) (closure Ω) ℝ where
  coe f := f.toBoundedContinuousFunction
  coe_injective f g h := ext_of_eqOn fun x hx ↦ by
    rw [interiorDerivative_apply _ _ (subset_closure hx),
      interiorDerivative_apply _ _ (subset_closure hx)]
    exact congrFun h ⟨x, subset_closure hx⟩

/-- Equality of values on the closure is equality in the Hölder space. -/
@[ext]
theorem ext {f g : CKGammaOn n k Ω γ} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- For open `Ω`, the zero-order field `f.interiorDerivative 0` is `C^k` on `Ω`. -/
theorem contDiffOn (f : CKGammaOn n k Ω γ) (hΩ : IsOpen Ω) :
    ContDiffOn ℝ k (f.interiorDerivative 0) Ω :=
  f.contDiffOn_derivative hΩ k 0 (by simp)

/-- Coordinate derivatives commute with addition in the Hölder space. -/
@[simp]
theorem derivative_add (f g : CKGammaOn n k Ω γ) (a : MultiIndex n k) :
    (f + g).derivative a = f.derivative a + g.derivative a :=
  rfl

/-- Coordinate derivatives commute with constant scalar multiplication. -/
@[simp]
theorem derivative_smul (c : ℝ) (f : CKGammaOn n k Ω γ) (a : MultiIndex n k) :
    (c • f).derivative a = c • f.derivative a :=
  rfl

end HolderSpace.CKGammaOn
