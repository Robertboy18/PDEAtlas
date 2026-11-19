/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.ProperPrecomposition
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.Lp
import CAS.ExactTactic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Test-function calculus for half-space reflection

The reflection lemma for `W^{1,p}(ℝ^n₊)` (Brezis, *Functional Analysis, Sobolev Spaces and PDE*,
Chapter 9) tests the reflected function against `φ ∘ reflect`, `φ ± φ ∘ reflect`
and `η_δ · φ`, where `φ ∈ C_c^∞(ℝ^n)` and `η_δ = cutoffAway δ` is a cutoff vanishing for
`xₙ ≤ δ`. We set up those test functions and the elementary facts about them that the
weak-derivative arguments consume: how reflection interacts with partial derivatives (a sign in
the normal direction, none tangentially), that cutoff-multiplied tests are supported inside the
open half-space, and that the cutoff can be removed in the limit `δ → 0` by dominated convergence.

## Main results

* `reflectTestFunction`, `evenPartTestFunction`, `oddPartTestFunction`: `φ ∘ reflect`,
  `φ + φ ∘ reflect`, `φ - φ ∘ reflect` as test functions, with `*_toFun` unfolding lemmas.
* `partialDeriv_reflect_comp`: `∂ᵢ(φ ∘ reflect) = ±(∂ᵢφ) ∘ reflect`, with the minus sign exactly
  when `i` is the normal index.
* `lineDerivCLM_evenPartTestFunction_of_ne_last`, `lineDerivCLM_oddPartTestFunction_of_ne_last`:
  tangential derivatives preserve parity; `lineDerivCLM_oddPartTestFunction_last`: the normal
  derivative swaps it, `∂ₙ(oddPartTestFunction φ) = evenPartTestFunction (∂ₙφ)`.
* `oddPartTestFunction_zero_on_boundary`: the odd part vanishes on `{xₙ = 0}`.
* `cutoffMul`, `tsupport_cutoffMul_subset_upper`, `partialDeriv_cutoffMul_of_ne_last`: cutoff
  tests lie in `C_c^∞(ℝ^n₊)` and tangential derivatives pass through the cutoff.
* `δSeq`, `tendsto_integral_mul_cutoff`: the scale sequence `δₘ = 1/(m+1)` and the dominated
  convergence statement `∫ h η_{δₘ} → ∫ h` for integrable `h` on `ℝ^n₊`.
* `integrable_mul_of_memLp`, `integrable_mul_of_memLp_measure`: an `L^p` function times a
  compactly supported continuous function is integrable (`p ≥ 1`).

## Implementation notes

`evenPartTestFunction` and `oddPartTestFunction` carry no factor `1/2`; the normalisation is
irrelevant for the identities they feed into and its absence keeps the formulas free of division.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 9, for extension by reflection across a flat boundary.
  <https://doi.org/10.1007/978-0-387-70914-7>
-/

@[expose] public section

open PDE (partialDeriv)

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open Set MeasureTheory Function
open scoped ENNReal Topology

section

namespace Extension

namespace GraphSpace

open SobolevSpace.GraphSpace


namespace HalfSpace

open _root_.SobolevSpace.HalfSpace

variable (n : ℕ)
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]


section Proofs

open scoped RealInnerProductSpace
open Filter


local notation "μ" => (domainMeasure n (Set.univ : Set (ℝ^n)))
local notation "μ₊" => (domainMeasure n ℝ^n₊)
local notation "μ₋" => (domainMeasure n ℝ^n₋)

/-- A compactly supported continuous multiplier makes an `Lᵖ` field integrable. -/
theorem integrable_mul_of_memLp_measure
    {μ' : Measure (ℝ^n)} [IsLocallyFiniteMeasure μ'] {f : ℝ^n → ℝ}
    (hf : MeasureTheory.MemLp f p μ')
    {ψ : ℝ^n → ℝ} (hψ_cont : Continuous ψ) (hψ_cs : HasCompactSupport ψ) :
    Integrable (fun x ↦ f x * ψ x) μ' := by
  have hf_loc : MeasureTheory.LocallyIntegrable f μ' :=
    hf.locallyIntegrable (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have : Integrable (fun x ↦ (ψ x) • f x) μ' :=
    hf_loc.integrable_smul_left_of_hasCompactSupport hψ_cont hψ_cs
  simpa [smul_eq_mul, mul_comm] using this

section PositiveDimension

variable [Fact (0 < n)]

/-- Multiplying an `Lᵖ` function on the upper half-space by a compactly supported continuous
function gives an integrable product. -/
theorem integrable_mul_of_memLp
    {f : ℝ^n → ℝ} (hf : MeasureTheory.MemLp f p μ₊)
    {ψ : ℝ^n → ℝ} (hψ_cont : Continuous ψ) (hψ_cs : HasCompactSupport ψ) :
    Integrable (fun x ↦ f x * ψ x) μ₊ := by
  exact integrable_mul_of_memLp_measure (n := n) (p := p) (μ' := μ₊)
    hf hψ_cont hψ_cs

/-!
### Reflection on test functions

We precompose a test function with the reflection map `reflect`.
-/

/-- Half-space reflection is smooth. -/
theorem contDiff_reflect : ContDiff ℝ (⊤ : ℕ∞) (_root_.SobolevSpace.HalfSpace.reflect n) := by
  simpa using (_root_.SobolevSpace.HalfSpace.reflectLinearIsometryEquiv (n := n)).contDiff

/-- Half-space reflection is a proper map. -/
theorem isProper_reflect :
    IsProperMap (_root_.SobolevSpace.HalfSpace.reflect n) := by
  simpa using
    (_root_.SobolevSpace.HalfSpace.reflectLinearIsometryEquiv
      (n := n)).toHomeomorph.isProperMap

/-- Pull a compactly supported smooth test function back along half-space reflection. -/
noncomputable def reflectTestFunction (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
  TestFunction.precompProper
    (_root_.SobolevSpace.HalfSpace.reflect n)
    (contDiff_reflect (n := n)) (isProper_reflect (n := n)) φ

/-- The underlying function of `reflectTestFunction φ` is `φ ∘ reflect`. -/
theorem reflectTestFunction_toFun (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (reflectTestFunction (n := n) φ).toFun =
      fun x ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n x) :=
  rfl

@[simp] private lemma reflectTestFunction_apply (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n) :
    reflectTestFunction (n := n) φ x = φ (_root_.SobolevSpace.HalfSpace.reflect n x) :=
  rfl

/-!
### Derivatives under reflection
-/

private theorem reflect_single (i : Fin n) :
    _root_.SobolevSpace.HalfSpace.reflect n (EuclideanSpace.single i (1 : ℝ)) =
      (if i = PDE.Common.lastIndex (n := n) then
          -EuclideanSpace.single i (1 : ℝ)
        else
          EuclideanSpace.single i (1 : ℝ)) := by
  classical
  ext j
  by_cases hi : i = PDE.Common.lastIndex (n := n)
  · subst hi
    by_cases hj : j = PDE.Common.lastIndex (n := n)
    · subst hj
      simp [_root_.SobolevSpace.HalfSpace.reflect]
    · simp [_root_.SobolevSpace.HalfSpace.reflect, hj]
  · by_cases hj : j = PDE.Common.lastIndex (n := n)
    · subst hj
      have hli : PDE.Common.lastIndex (n := n) ≠ i := by
        intro h
        exact hi h.symm
      simp [_root_.SobolevSpace.HalfSpace.reflect, hi, hli]
    · simp [_root_.SobolevSpace.HalfSpace.reflect, hi, hj]

/-- Chain rule for reflection: `∂ᵢ(φ ∘ reflect)(x) = ±(∂ᵢφ)(reflect x)`, with the minus sign
exactly in the normal direction `i = n`, since `reflect` fixes the tangential coordinates and
negates `xₙ`. -/
theorem partialDeriv_reflect_comp (i : Fin n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n) :
    (∂[i] (fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y))) x =
      (if i = PDE.Common.lastIndex (n := n) then
          -(∂[i] φ.toFun) (_root_.SobolevSpace.HalfSpace.reflect n x)
        else
          (∂[i] φ.toFun) (_root_.SobolevSpace.HalfSpace.reflect n x)) := by
  classical
  -- Represent reflection by its continuous linear isometry for the chain rule.
  let R : ℝ^n →L[ℝ] ℝ^n :=
    (_root_.SobolevSpace.HalfSpace.reflectLinearIsometryEquiv (n := n)).toContinuousLinearMap
  have hreflect (y : ℝ^n) :
      (_root_.SobolevSpace.HalfSpace.reflectLinearIsometryEquiv (n := n)) y =
        _root_.SobolevSpace.HalfSpace.reflect n y := by
    rfl
  -- `R` agrees pointwise with the reflection equivalence.
  have hfun :
      (fun y ↦ φ.toFun ((_root_.SobolevSpace.HalfSpace.reflectLinearIsometryEquiv (n := n)) y)) =
        fun y ↦ φ.toFun (R y) := by
    funext y; rfl
  have hxR : R x = (_root_.SobolevSpace.HalfSpace.reflectLinearIsometryEquiv (n := n)) x := by
    rfl
  have hφ : DifferentiableAt ℝ φ.toFun (R x) := by
    -- `C^∞` implies differentiable.
    have hCD : ContDiffAt ℝ (⊤ : ℕ∞) φ.toFun (R x) := φ.contDiff.contDiffAt
    exact hCD.differentiableAt (by simp)
  have hRdiff : DifferentiableAt ℝ (fun y ↦ R y) x := by
    simp
  have hcomp :
      fderiv ℝ (φ.toFun ∘ R) x =
        (fderiv ℝ φ.toFun (R x)).comp (fderiv ℝ (fun y ↦ R y) x) := by
    exact fderiv_comp (x := x) hφ hRdiff
  have hRfderiv : fderiv ℝ (fun y ↦ R y) x = R := by
    simp
  have hRfun' : ∀ y : ℝ^n, R y = _root_.SobolevSpace.HalfSpace.reflect n y := by
    intro y
    calc
      R y = (_root_.SobolevSpace.HalfSpace.reflectLinearIsometryEquiv (n := n)) y := rfl
      _ = _root_.SobolevSpace.HalfSpace.reflect n y := hreflect y
  -- Reflection fixes tangential basis vectors and negates the normal basis vector.
  by_cases hi : i = PDE.Common.lastIndex (n := n)
  · subst hi
    have hRe :
        R (EuclideanSpace.single (PDE.Common.lastIndex (n := n)) (1 : ℝ)) =
          -EuclideanSpace.single (PDE.Common.lastIndex (n := n)) (1 : ℝ) := by
      simpa [R] using (reflect_single (n := n) (i := PDE.Common.lastIndex (n := n)))
    have hxR' : R x = _root_.SobolevSpace.HalfSpace.reflect n x := by
      simpa [hreflect] using hxR
    have hfun' :
        (fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y)) =
          fun y ↦ φ.toFun (R y) := by
      funext y
      simp [hRfun' (y := y)]
    -- Compute using the chain rule and the fact `R e_last = -e_last`.
    have hmain :
        (∂[PDE.Common.lastIndex (n := n)]
            (fun y ↦ φ.toFun (R y))) x =
          -(∂[PDE.Common.lastIndex (n := n)]
            φ.toFun) (R x) := by
      -- Coordinate derivatives evaluate the Fréchet derivative on basis vectors.
      change (fderiv ℝ (fun y ↦ φ.toFun (R y)) x)
          (EuclideanSpace.single (PDE.Common.lastIndex (n := n)) 1) =
        -(fderiv ℝ φ.toFun (R x))
          (EuclideanSpace.single (PDE.Common.lastIndex (n := n)) 1)
      rw [show (fun y ↦ φ.toFun (R y)) = φ.toFun ∘ R by rfl]
      rw [hcomp, hRfderiv]
      simp [hRe]
    -- The continuous linear map and the geometric reflection agree pointwise.
    rw [← hfun', hxR'] at hmain
    simpa using hmain
  · have hRe :
        R (EuclideanSpace.single i (1 : ℝ)) = EuclideanSpace.single i (1 : ℝ) := by
      have hli : i ≠ PDE.Common.lastIndex (n := n) := hi
      simpa [R, hli] using (reflect_single (n := n) (i := i))
    have hxR' : R x = _root_.SobolevSpace.HalfSpace.reflect n x := by
      simpa [hreflect] using hxR
    have hfun' :
        (fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y)) =
          fun y ↦ φ.toFun (R y) := by
      funext y
      simp [hRfun' (y := y)]
    have hmain :
        (∂[i] (fun y ↦ φ.toFun (R y))) x =
          (∂[i] φ.toFun) (R x) := by
      change (fderiv ℝ (fun y ↦ φ.toFun (R y)) x) (EuclideanSpace.single i 1) =
        (fderiv ℝ φ.toFun (R x)) (EuclideanSpace.single i 1)
      rw [show (fun y ↦ φ.toFun (R y)) = φ.toFun ∘ R by rfl]
      rw [hcomp, hRfderiv]
      simp [hRe]
    rw [← hfun', hxR'] at hmain
    simpa [hi] using hmain

/-!
### Cutoff test functions supported strictly inside `ℝ^n₊`
-/

/-- A test function multiplied by the smooth cutoff away from the boundary. -/
noncomputable def cutoffMul
    (δ : ℝ) (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) : 𝓓((⊤ : Opens (ℝ^n)), ℝ) where
  toFun := fun x ↦ _root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ x * ψ.toFun x
  contDiff' := by
    -- Expand `cutoffAway` and use that `Real.smoothTransition` is smooth.
    -- `ℝ^n` is `PiLp 2 (fun _ : Fin n => ℝ)`, so use the `PiLp` projection.
    let projLast : ℝ^n →L[ℝ] ℝ :=
      PiLp.proj (𝕜 := ℝ) (p := (2 : ℝ≥0∞)) (β := fun _ : Fin n ↦ ℝ)
        (PDE.Common.lastIndex (n := n))
    have hproj : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^n ↦ projLast x) := by
      simpa using (projLast.contDiff (n := (⊤ : ℕ∞)))
    have haux :
        ContDiff ℝ (⊤ : ℕ∞)
          (fun x : ℝ^n ↦
            ((projLast x - δ) / δ)) := by
      fun_prop
    have hcut :
        ContDiff ℝ (⊤ : ℕ∞) (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ) := by
      change ContDiff ℝ (⊤ : ℕ∞)
        (fun x : ℝ^n ↦ Real.smoothTransition ((projLast x - δ) / δ))
      have hc := Real.smoothTransition.contDiff.comp haux
      change ContDiff ℝ (⊤ : ℕ∞)
        (fun x : ℝ^n ↦ Real.smoothTransition ((projLast x - δ) / δ)) at hc
      exact hc
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ^n ↦
        _root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ x * ψ.toFun x)
    exact hcut.mul ψ.contDiff
  hasCompactSupport' := ψ.hasCompactSupport.mul_left
  tsupport_subset' := Set.subset_univ _

/-- A cutoff test function with positive cutoff scale is supported in the upper half-space. -/
theorem tsupport_cutoffMul_subset_upper
    {δ : ℝ} (hδ : 0 < δ) (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    tsupport (cutoffMul (n := n) δ ψ).toFun ⊆ ℝ^n₊ := by
  -- The support lies in `{x | xₙ ≥ δ}`, hence in `ℝ^n₊`.
  have hsupp :
      Function.support (cutoffMul (n := n) δ ψ).toFun ⊆
        {x : ℝ^n | δ ≤ x (PDE.Common.lastIndex (n := n))} := by
    intro x hx
    have hxne : (cutoffMul (n := n) δ ψ).toFun x ≠ 0 := by
      simpa [Function.mem_support] using hx
    by_contra hle
    have hxl : x (PDE.Common.lastIndex (n := n)) ≤ δ := le_of_not_ge hle
    have hcut :
        _root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ x = 0 :=
      _root_.SobolevSpace.HalfSpace.cutoffAway_eq_zero_of_last_le (n := n) (δ := δ) hδ hxl
    exact hxne (by simp [cutoffMul, hcut])
  have hclosed :
      IsClosed {x : ℝ^n | δ ≤ x (PDE.Common.lastIndex (n := n))} := by
    have hcont : Continuous fun x : ℝ^n ↦ x (PDE.Common.lastIndex (n := n)) := by
      simpa using
        (EuclideanSpace.proj (PDE.Common.lastIndex (n := n)) : ℝ^n →L[ℝ] ℝ).continuous
    change IsClosed
      ((fun x : ℝ^n ↦ x (PDE.Common.lastIndex (n := n))) ⁻¹' Set.Ici δ)
    exact isClosed_Ici.preimage hcont
  have hts :
      tsupport (cutoffMul (n := n) δ ψ).toFun ⊆
        {x : ℝ^n | δ ≤ x (PDE.Common.lastIndex (n := n))} :=
    closure_minimal hsupp hclosed
  intro x hx
  have hxδ : δ ≤ x (PDE.Common.lastIndex (n := n)) := hts hx
  have : 0 < x (PDE.Common.lastIndex (n := n)) := lt_of_lt_of_le hδ hxδ
  exact this

/-!
### Passing from `C_c^∞(ℝ^n₊)` tests to reflected tests via cutoff limits

For a general test function `φ ∈ C_c^∞(ℝ^n)`, the reflected combinations
`φ ± φ ∘ reflect` need not have support contained in `ℝ^n₊`. To apply the hypothesis
`HasWeakDerivativeOn ℝ^n₊ …` (which tests against `C_c^∞(ℝ^n₊)`), we multiply by a cutoff
`cutoffAway δ` that vanishes near the boundary and let `δ → 0`.
-/

end PositiveDimension

section PositiveDimension

variable [Fact (0 < n)]

/-- A cutoff depending only on the normal coordinate has zero tangential derivative. -/
theorem partialDeriv_cutoffAway_of_ne_last {δ : ℝ} (hδ : δ ≠ 0) (i : Fin n)
    (hi : i ≠ PDE.Common.lastIndex (n := n)) (x : ℝ^n) :
    (∂[i] (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ)) x = 0 := by
  classical
  -- Write as `smoothTransition ∘ h`, where `h` depends only on the last coordinate.
  let projLast : ℝ^n →L[ℝ] ℝ :=
    PiLp.proj (𝕜 := ℝ) (p := (2 : ℝ≥0∞)) (β := fun _ : Fin n ↦ ℝ)
      (PDE.Common.lastIndex (n := n))
  let Lδ : ℝ^n →L[ℝ] ℝ := (1 / δ : ℝ) • projLast
  let h : ℝ^n → ℝ := fun y ↦ Lδ y - 1
  have hcut :
      (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ) =
        fun y ↦ Real.smoothTransition (h y) := by
    funext y
    -- Unfold and normalize the affine expression in the argument of `smoothTransition`.
    have harg :
        (y (PDE.Common.lastIndex (n := n)) - δ) / δ =
          δ⁻¹ * y (PDE.Common.lastIndex (n := n)) - (1 : ℝ) := by
      cas using hδ
    simp [_root_.SobolevSpace.HalfSpace.cutoffAway, h, Lδ, projLast, harg, div_eq_mul_inv,
       mul_comm]
  have hdiff_g : DifferentiableAt ℝ Real.smoothTransition (h x) := by
    have hCD : ContDiffAt ℝ (⊤ : ℕ∞) Real.smoothTransition (h x) :=
      Real.smoothTransition.contDiff.contDiffAt
    exact hCD.differentiableAt (by simp)
  have hdiff_h : DifferentiableAt ℝ h x := by
    -- `h` is affine, hence differentiable.
    simp [h, Lδ]
  have hcomp :
      fderiv ℝ (Real.smoothTransition ∘ h) x =
        (fderiv ℝ Real.smoothTransition (h x)).comp (fderiv ℝ h x) := by
    exact fderiv_comp (x := x) hdiff_g hdiff_h
  have hfderiv_h : fderiv ℝ h x = Lδ := by
    -- Subtracting a constant doesn't change the derivative, and `Lδ` is linear.
    have hLin : fderiv ℝ (fun y : ℝ^n ↦ Lδ y) x = Lδ := by
      simp
    calc
      fderiv ℝ h x = fderiv ℝ (fun y : ℝ^n ↦ Lδ y - (1 : ℝ)) x := by
        rfl
      _ = fderiv ℝ (fun y : ℝ^n ↦ Lδ y) x := by
        simpa using (fderiv_sub_const (𝕜 := ℝ) (f := fun y : ℝ^n ↦ Lδ y) (x := x) (c := (1 : ℝ)))
      _ = Lδ := hLin
  have hLδ_single :
      (Lδ (EuclideanSpace.single i (1 : ℝ))) = 0 := by
    have : (projLast (EuclideanSpace.single i (1 : ℝ))) = 0 := by
      -- projection to last coordinate kills `e_i` if `i ≠ last`
      have hne : PDE.Common.lastIndex (n := n) ≠ i := by
        intro h
        exact hi h.symm
      simp [projLast, PiLp.proj_apply, hne]
    simp [Lδ, this]
  -- Chain rule + `h` has zero derivative in direction `i ≠ last`.
  have :
      (∂[i] (fun y ↦ Real.smoothTransition (h y))) x = 0 := by
    rw [show (fun y ↦ Real.smoothTransition (h y)) = Real.smoothTransition ∘ h by rfl]
    simp [partialDeriv, hcomp, hfderiv_h, hLδ_single]
  simpa [hcut] using this

/-- The smooth boundary cutoff is differentiable at every point. -/
theorem differentiableAt_cutoffAway (δ : ℝ) (x : ℝ^n) :
    DifferentiableAt ℝ (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ) x := by
  have hCD : ContDiffAt ℝ (1 : ℕ∞) (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ) x :=
    (contDiff_cutoffAway (n := n) (δ := δ)).contDiffAt.of_le (by simp)
  exact hCD.differentiableAt (by simp)

/-- The smooth boundary cutoff is continuous. -/
theorem continuous_cutoffAway (δ : ℝ) :
    Continuous (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ) :=
  (contDiff_cutoffAway (n := n) (δ := δ)).continuous

/-- Every coordinate derivative of the smooth boundary cutoff is continuous. -/
theorem continuous_partialDeriv_cutoffAway (δ : ℝ) (i : Fin n) :
    Continuous fun x : ℝ^n ↦
      (∂[i] (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ)) x := by
  have hfderiv :
      ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ)) := by
    simpa using
      ((contDiff_cutoffAway (n := n) (δ := δ)).fderiv_right
        (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) (by simp))
  have :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun x : ℝ^n ↦
          (fderiv ℝ (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ) x)
            (EuclideanSpace.single i (1 : ℝ))) := by
    simpa using
      hfderiv.clm_apply
        (contDiff_const :
          ContDiff ℝ (⊤ : ℕ∞) fun _ : ℝ^n ↦ EuclideanSpace.single i (1 : ℝ))
  simpa [partialDeriv] using this.continuous

/-- Tangential differentiation commutes with multiplication by the boundary cutoff. -/
theorem partialDeriv_cutoffMul_of_ne_last {δ : ℝ} (hδ : δ ≠ 0) (i : Fin n)
    (hi : i ≠ PDE.Common.lastIndex (n := n))
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n) :
    (∂[i] (cutoffMul (n := n) δ ψ).toFun) x =
      _root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ x *
        (∂[i] ψ.toFun) x := by
  have hcut : DifferentiableAt ℝ (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ) x :=
    differentiableAt_cutoffAway (n := n) (δ := δ) x
  have hψ : DifferentiableAt ℝ ψ.toFun x :=
    (ψ.contDiff.contDiffAt.differentiableAt (by simp))
  -- Product rule; the tangential derivative of the cutoff is zero.
  have hmul :=
    PDE.partialDeriv_mul (n := n) (i := i)
      (f := _root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ) (g := ψ.toFun)
      (x := x) hcut hψ
  have hzero :
      (∂[i] (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ)) x = 0 :=
    partialDeriv_cutoffAway_of_ne_last (n := n) (δ := δ) hδ i hi x
  change (∂[i]
      (fun y ↦
        _root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ y * ψ.toFun y)) x =
    _root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ x *
      (∂[i] ψ.toFun) x
  rw [hmul, hzero]
  ring

private theorem cutoffAway_abs_le_one (δ : ℝ) (x : ℝ^n) :
    |(_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ x)| ≤ 1 := by
  -- `Real.smoothTransition` takes values in `[0,1]`.
  have h0 :
      0 ≤ (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ x) := by
    simp [_root_.SobolevSpace.HalfSpace.cutoffAway, Real.smoothTransition.nonneg]
  have h1 :
      (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ x) ≤ 1 := by
    simp [_root_.SobolevSpace.HalfSpace.cutoffAway, Real.smoothTransition.le_one]
  simpa [abs_of_nonneg h0] using h1

/-! #### A convenient cutoff sequence `δₘ → 0` -/

/-- A positive sequence of cutoff scales converging to zero. -/
noncomputable def δSeq (m : ℕ) : ℝ := ((m : ℝ) + 1)⁻¹

/-- Every cutoff scale in `δSeq` is positive. -/
theorem δSeq_pos (m : ℕ) : 0 < δSeq m := by
  have : 0 < (m : ℝ) + 1 := by positivity
  simpa [δSeq] using inv_pos.2 this

/-- The cutoff scales converge to zero. -/
theorem tendsto_δSeq : Tendsto δSeq atTop (𝓝 (0 : ℝ)) := by
  change Tendsto (fun m : ℕ ↦ ((m : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ))
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private theorem cutoffAway_tendsto_one_ae :
    (∀ᵐ x ∂ μ₊, Tendsto (fun m ↦ _root_.SobolevSpace.HalfSpace.cutoffAway (n := n) (δSeq m) x)
      atTop (𝓝 (1 : ℝ))) := by
  -- On `ℝ^n₊`, eventually `2δₘ ≤ xₙ`, hence `cutoffAway δₘ x = 1`.
  have hxΩ : ∀ᵐ x ∂ μ₊, x ∈ ℝ^n₊ := by
    -- `μ₊ = volume.restrict ℝ^n₊`.
    simpa [domainMeasure] using
      (ae_restrict_mem (measurableSet_upper (n := n)) :
        (∀ᵐ x ∂ (MeasureTheory.volume : Measure (ℝ^n)).restrict ℝ^n₊, x ∈ ℝ^n₊))
  refine hxΩ.mono ?_
  intro x hx
  have hxpos : 0 < x (PDE.Common.lastIndex (n := n)) := hx
  have hlt :
      ∀ᶠ m in atTop, δSeq m < x (PDE.Common.lastIndex (n := n)) / 2 := by
    have hnhds :
        Iio (x (PDE.Common.lastIndex (n := n)) / 2) ∈ 𝓝 (0 : ℝ) := by
      have : 0 < x (PDE.Common.lastIndex (n := n)) / 2 := by positivity
      simpa using (Iio_mem_nhds this)
    exact tendsto_δSeq.eventually hnhds
  have hEq :
      (fun m ↦ _root_.SobolevSpace.HalfSpace.cutoffAway (n := n) (δSeq m) x) =ᶠ[atTop]
        fun _ ↦ (1 : ℝ) := by
    filter_upwards [hlt] with m hm
    have hδm : 0 < δSeq m := δSeq_pos m
    have h2 : 2 * δSeq m ≤ x (PDE.Common.lastIndex (n := n)) := by
      linarith
    simpa using
      (_root_.SobolevSpace.HalfSpace.cutoffAway_eq_one_of_two_mul_le_last (n := n)
        (δ := δSeq m) hδm h2)
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 (1 : ℝ))).congr' hEq.symm

/-! #### Dominated convergence for multiplying by the cutoff -/

/-- Integrals against the boundary cutoff converge to the uncut integral. -/
theorem tendsto_integral_mul_cutoff {h : ℝ^n → ℝ} (hh : Integrable h μ₊) :
    Tendsto
        (fun m ↦
          ∫ x, h x *
              _root_.SobolevSpace.HalfSpace.cutoffAway (n := n) (δSeq m) x ∂ μ₊)
        atTop (𝓝 (∫ x, h x ∂ μ₊)) := by
  -- Apply dominated convergence with `bound = ‖h‖`.
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (F := fun m x ↦ h x * _root_.SobolevSpace.HalfSpace.cutoffAway (n := n) (δSeq m) x)
    (f := h) (bound := fun x ↦ ‖h x‖) ?_ ?_ ?_ ?_
  · intro m
    -- `h` is a.e. strongly measurable (since integrable), and the cutoff is continuous.
    have hcut :
        AEStronglyMeasurable
          (fun x ↦
            _root_.SobolevSpace.HalfSpace.cutoffAway (n := n) (δSeq m) x) μ₊ :=
      (continuous_cutoffAway (n := n) (δ := δSeq m)).aestronglyMeasurable
    exact hh.aestronglyMeasurable.mul hcut
  · -- `‖h‖` is integrable.
    simpa using hh.norm
  · intro m
    refine Filter.Eventually.of_forall (fun x ↦ ?_)
    -- `‖h x * cutoff‖ ≤ ‖h x‖` since `|cutoff| ≤ 1`.
    have hle : ‖_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) (δSeq m) x‖ ≤ 1 := by
      simpa [Real.norm_eq_abs] using cutoffAway_abs_le_one (n := n) (δ := δSeq m) x
    calc
      ‖h x * _root_.SobolevSpace.HalfSpace.cutoffAway (n := n) (δSeq m) x‖
          = ‖h x‖ * ‖_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) (δSeq m) x‖ := by
              simp [norm_mul]
      _ ≤ ‖h x‖ * 1 := by gcongr
      _ = ‖h x‖ := by simp
  · -- Pointwise a.e. convergence: cutoff → 1.
    have hcut := cutoffAway_tendsto_one_ae (n := n)
    refine hcut.mono ?_
    intro x hx
    have : Tendsto (fun m ↦ h x * _root_.SobolevSpace.HalfSpace.cutoffAway (n := n) (δSeq m) x)
          atTop (𝓝 (h x * (1 : ℝ))) :=
      (tendsto_const_nhds.mul hx)
    simpa using this

/-! #### Even/odd parts of a test function -/

/-- The unnormalized reflection-even part `φ + φ ∘ reflect` of a test function. -/
noncomputable def evenPartTestFunction (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
  φ + reflectTestFunction (n := n) φ

/-- The unnormalized reflection-odd part `φ - φ ∘ reflect` of a test function. -/
noncomputable def oddPartTestFunction (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
  φ - reflectTestFunction (n := n) φ

/-- The underlying function of `evenPartTestFunction φ` is `x ↦ φ x + φ (reflect x)`. -/
theorem evenPartTestFunction_toFun (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (evenPartTestFunction (n := n) φ).toFun =
      fun x ↦ φ.toFun x + φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n x) := by
  funext x
  change (evenPartTestFunction (n := n) φ) x = φ x + φ (_root_.SobolevSpace.HalfSpace.reflect n x)
  simp [evenPartTestFunction]

@[simp] private lemma evenPartTestFunction_apply (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n) :
    evenPartTestFunction (n := n) φ x =
      φ x + φ (_root_.SobolevSpace.HalfSpace.reflect n x) := by
  simp [evenPartTestFunction]

/-- The underlying function of `oddPartTestFunction φ` is `x ↦ φ x - φ (reflect x)`. -/
theorem oddPartTestFunction_toFun (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (oddPartTestFunction (n := n) φ).toFun =
      fun x ↦ φ.toFun x - φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n x) := by
  funext x
  change (oddPartTestFunction (n := n) φ) x = φ x - φ (_root_.SobolevSpace.HalfSpace.reflect n x)
  simp [oddPartTestFunction, sub_eq_add_neg]

@[simp] private lemma oddPartTestFunction_apply (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n) :
    oddPartTestFunction (n := n) φ x =
      φ x - φ (_root_.SobolevSpace.HalfSpace.reflect n x) := by
  simp [oddPartTestFunction]

/-- The odd part of a test function vanishes on the reflecting hyperplane. -/
theorem oddPartTestFunction_zero_on_boundary (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) {x : ℝ^n}
    (hx : x (PDE.Common.lastIndex (n := n)) = 0) :
    (oddPartTestFunction (n := n) φ).toFun x = 0 := by
  have hreflect : _root_.SobolevSpace.HalfSpace.reflect n x = x := by
    ext i
    by_cases hi : i = PDE.Common.lastIndex (n := n)
    · subst hi
      simp [_root_.SobolevSpace.HalfSpace.reflect, hx]
    · simp [_root_.SobolevSpace.HalfSpace.reflect, hi]
  simp [hreflect]

/-! #### Partial derivatives of the symmetrized test functions -/

/-- A tangential derivative commutes with taking the even part of a test function. -/
theorem lineDerivCLM_evenPartTestFunction_of_ne_last (i : Fin n)
    (hi : i ≠ PDE.Common.lastIndex (n := n))
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n) :
    (_root_.TestFunction.lineDerivCLM ℝ
        (EuclideanSpace.single i (1 : ℝ)) (evenPartTestFunction (n := n) φ) :
      𝓓((⊤ : Opens (ℝ^n)), ℝ)) x =
      (evenPartTestFunction (n := n)
        (_root_.TestFunction.lineDerivCLM ℝ
          (EuclideanSpace.single i (1 : ℝ)) φ :
            𝓓((⊤ : Opens (ℝ^n)), ℝ))) x := by
  -- Expand `evenPartTestFunction` and differentiate termwise.
  have hφ : DifferentiableAt ℝ φ.toFun x :=
    (φ.contDiff.contDiffAt.differentiableAt (by simp))
  have href :
      DifferentiableAt ℝ
        (fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y)) x := by
    -- smoothness of `reflect` + smoothness of `φ`
    have hCD :
        ContDiffAt ℝ (⊤ : ℕ∞)
          (fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y)) x := by
      change ContDiffAt ℝ (⊤ : ℕ∞)
        (φ.toFun ∘ _root_.SobolevSpace.HalfSpace.reflect n) x
      exact (φ.contDiff.comp (contDiff_reflect (n := n))).contDiffAt
    exact hCD.differentiableAt (by simp)
  -- Use `partialDeriv_add` and the reflection chain rule.
  have hadd := PDE.partialDeriv_add (i := i) (f := φ.toFun)
    (g := fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y))
    (x := x) hφ href
  -- Simplify the reflected derivative using the sign computation.
  have href' := partialDeriv_reflect_comp (n := n) (i := i) φ x
  have hsign : (if i = PDE.Common.lastIndex (n := n) then
        -(∂[i] φ.toFun) (_root_.SobolevSpace.HalfSpace.reflect n x)
      else
        (∂[i] φ.toFun) (_root_.SobolevSpace.HalfSpace.reflect n x))
      = (∂[i] φ.toFun) (_root_.SobolevSpace.HalfSpace.reflect n x) := by
    simp [hi]
  have hlineEven :
      (_root_.TestFunction.lineDerivCLM ℝ
          (EuclideanSpace.single i (1 : ℝ)) (evenPartTestFunction (n := n) φ) :
        𝓓((⊤ : Opens (ℝ^n)), ℝ)) x =
        (∂[i] (evenPartTestFunction (n := n) φ).toFun) x := by
    rw [_root_.TestFunction.lineDerivCLM_apply_of_le (by simp)]
    rw [((evenPartTestFunction (n := n) φ).contDiff.differentiable
      (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    rfl
  have hlineφ (y : ℝ^n) :
      (_root_.TestFunction.lineDerivCLM ℝ
          (EuclideanSpace.single i (1 : ℝ)) φ :
        𝓓((⊤ : Opens (ℝ^n)), ℝ)) y =
        (∂[i] φ.toFun) y := by
    rw [_root_.TestFunction.lineDerivCLM_apply_of_le (by simp)]
    rw [(φ.contDiff.differentiable
      (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    rfl
  rw [hlineEven, evenPartTestFunction_apply, hlineφ, hlineφ, evenPartTestFunction_toFun]
  change (∂[i]
      (fun y ↦ φ.toFun y + φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y))) x =
    (∂[i] φ.toFun) x +
      (∂[i] φ.toFun)
        (_root_.SobolevSpace.HalfSpace.reflect n x)
  calc
    (∂[i]
          (fun y ↦ φ.toFun y + φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y))) x =
        (∂[i] φ.toFun) x +
          (∂[i]
            (fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y))) x := by
      rw [show
        (fun y ↦ φ.toFun y +
          φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y)) =
            φ.toFun + fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y) by
          funext y
          rfl]
      exact hadd
    _ = _ := by
      rw [href', hsign]

/-- Tangential differentiation preserves odd reflection parity. -/
theorem lineDerivCLM_oddPartTestFunction_of_ne_last (i : Fin n)
    (hi : i ≠ PDE.Common.lastIndex (n := n))
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n) :
    (_root_.TestFunction.lineDerivCLM ℝ
        (EuclideanSpace.single i (1 : ℝ)) (oddPartTestFunction (n := n) φ) :
      𝓓((⊤ : Opens (ℝ^n)), ℝ)) x =
      (oddPartTestFunction (n := n)
        (_root_.TestFunction.lineDerivCLM ℝ
          (EuclideanSpace.single i (1 : ℝ)) φ :
            𝓓((⊤ : Opens (ℝ^n)), ℝ))) x := by
  have hφ : DifferentiableAt ℝ φ.toFun x :=
    φ.contDiff.contDiffAt.differentiableAt (by simp)
  have href : DifferentiableAt ℝ
      (fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y)) x := by
    have hCD : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y)) x := by
      change ContDiffAt ℝ (⊤ : ℕ∞)
        (φ.toFun ∘ _root_.SobolevSpace.HalfSpace.reflect n) x
      exact (φ.contDiff.comp (contDiff_reflect (n := n))).contDiffAt
    exact hCD.differentiableAt (by simp)
  have hsub := PDE.partialDeriv_sub (i := i) (f := φ.toFun)
    (g := fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y))
    (x := x) hφ href
  have href' := partialDeriv_reflect_comp (n := n) (i := i) φ x
  have hlineOdd :
      (_root_.TestFunction.lineDerivCLM ℝ
          (EuclideanSpace.single i (1 : ℝ)) (oddPartTestFunction (n := n) φ) :
        𝓓((⊤ : Opens (ℝ^n)), ℝ)) x =
        (∂[i] (oddPartTestFunction (n := n) φ).toFun) x := by
    rw [_root_.TestFunction.lineDerivCLM_apply_of_le (by simp)]
    rw [((oddPartTestFunction (n := n) φ).contDiff.differentiable
      (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    rfl
  have hlineφ (y : ℝ^n) :
      (_root_.TestFunction.lineDerivCLM ℝ
          (EuclideanSpace.single i (1 : ℝ)) φ :
        𝓓((⊤ : Opens (ℝ^n)), ℝ)) y =
        (∂[i] φ.toFun) y := by
    rw [_root_.TestFunction.lineDerivCLM_apply_of_le (by simp)]
    rw [(φ.contDiff.differentiable
      (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    rfl
  rw [hlineOdd, oddPartTestFunction_apply, hlineφ, hlineφ, oddPartTestFunction_toFun]
  change (∂[i]
      (fun y ↦ φ.toFun y -
        φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y))) x =
    (∂[i] φ.toFun) x -
      (∂[i] φ.toFun)
        (_root_.SobolevSpace.HalfSpace.reflect n x)
  calc
    (∂[i]
        (fun y ↦ φ.toFun y -
          φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y))) x =
      (∂[i] φ.toFun) x -
        (∂[i]
          (fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y))) x := by
      rw [show
        (fun y ↦ φ.toFun y -
          φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y)) =
            φ.toFun - fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y) by
          funext y
          rfl]
      exact hsub
    _ = _ := by
      rw [href']
      rw [ite_eq_right hi]

/-- The normal derivative flips parity: `∂ₙ(oddPartTestFunction φ) = evenPartTestFunction (∂ₙφ)`.
Differentiating `φ - φ ∘ reflect` in `xₙ` gives `∂ₙφ + (∂ₙφ) ∘ reflect` because of the sign in
`partialDeriv_reflect_comp`. This is the identity that makes the normal weak derivative of an even
reflection odd. -/
theorem lineDerivCLM_oddPartTestFunction_last (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n) :
    (_root_.TestFunction.lineDerivCLM ℝ
        (EuclideanSpace.single (PDE.Common.lastIndex (n := n)) (1 : ℝ))
        (oddPartTestFunction (n := n) φ) :
      𝓓((⊤ : Opens (ℝ^n)), ℝ)) x =
      (evenPartTestFunction (n := n)
        (_root_.TestFunction.lineDerivCLM ℝ
          (EuclideanSpace.single (PDE.Common.lastIndex (n := n)) (1 : ℝ)) φ :
            𝓓((⊤ : Opens (ℝ^n)), ℝ))) x := by
  classical
  let i : Fin n := PDE.Common.lastIndex (n := n)
  change
    (_root_.TestFunction.lineDerivCLM ℝ
        (EuclideanSpace.single i (1 : ℝ)) (oddPartTestFunction (n := n) φ) :
      𝓓((⊤ : Opens (ℝ^n)), ℝ)) x =
      (evenPartTestFunction (n := n)
        (_root_.TestFunction.lineDerivCLM ℝ
          (EuclideanSpace.single i (1 : ℝ)) φ :
            𝓓((⊤ : Opens (ℝ^n)), ℝ))) x
  have hφ : DifferentiableAt ℝ φ.toFun x :=
    (φ.contDiff.contDiffAt.differentiableAt (by simp))
  have href :
      DifferentiableAt ℝ
        (fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y)) x := by
    have hCD :
        ContDiffAt ℝ (⊤ : ℕ∞)
          (fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y)) x := by
      change ContDiffAt ℝ (⊤ : ℕ∞)
        (φ.toFun ∘ _root_.SobolevSpace.HalfSpace.reflect n) x
      exact (φ.contDiff.comp (contDiff_reflect (n := n))).contDiffAt
    exact hCD.differentiableAt (by simp)
  -- Differentiate `φ - φ∘reflect`.
  have hsub := PDE.partialDeriv_sub (i := i) (f := φ.toFun)
    (g := fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y))
    (x := x) hφ href
  have href' := partialDeriv_reflect_comp (n := n) (i := i) φ x
  -- At the last coordinate, reflection flips the sign.
  have hsign :
      (if i = PDE.Common.lastIndex (n := n) then
          -(∂[i] φ.toFun) (_root_.SobolevSpace.HalfSpace.reflect n x)
        else
          (∂[i] φ.toFun) (_root_.SobolevSpace.HalfSpace.reflect n x))
        =
      -(∂[i] φ.toFun) (_root_.SobolevSpace.HalfSpace.reflect n x) := by
    simp [i]
  have hlineOdd :
      (_root_.TestFunction.lineDerivCLM ℝ
          (EuclideanSpace.single i (1 : ℝ)) (oddPartTestFunction (n := n) φ) :
        𝓓((⊤ : Opens (ℝ^n)), ℝ)) x =
        (∂[i] (oddPartTestFunction (n := n) φ).toFun) x := by
    rw [_root_.TestFunction.lineDerivCLM_apply_of_le (by simp)]
    rw [((oddPartTestFunction (n := n) φ).contDiff.differentiable
      (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    rfl
  have hlineφ (y : ℝ^n) :
      (_root_.TestFunction.lineDerivCLM ℝ
          (EuclideanSpace.single i (1 : ℝ)) φ :
        𝓓((⊤ : Opens (ℝ^n)), ℝ)) y =
        (∂[i] φ.toFun) y := by
    rw [_root_.TestFunction.lineDerivCLM_apply_of_le (by simp)]
    rw [(φ.contDiff.differentiable
      (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    rfl
  rw [hlineOdd, evenPartTestFunction_apply, hlineφ, hlineφ, oddPartTestFunction_toFun]
  change (∂[i]
      (fun y ↦ φ.toFun y - φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y))) x =
    (∂[i] φ.toFun) x +
      (∂[i] φ.toFun)
        (_root_.SobolevSpace.HalfSpace.reflect n x)
  calc
    (∂[i]
          (fun y ↦ φ.toFun y - φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y))) x =
        (∂[i] φ.toFun) x -
          (∂[i]
            (fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y))) x := by
      rw [show
        (fun y ↦ φ.toFun y -
          φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y)) =
            φ.toFun - fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y) by
          funext y
          rfl]
      exact hsub
    _ = _ := by
      rw [href', hsign]
      rw [_root_.TestFunction.toFun_eq_coe]
      ring_nf

end PositiveDimension

end Proofs

end HalfSpace

end GraphSpace

end Extension

end

end SobolevSpace
