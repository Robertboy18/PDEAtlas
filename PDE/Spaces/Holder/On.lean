/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.HolderNorm
public import PDE.Spaces.Holder.Exponent

/-!
# Hölder spaces on a metric domain

`HolderSpace.C0GammaOn Ω γ` is the Banach space of bounded real-valued
`γ`-Hölder functions on a metric type `Ω`, with the norm

`‖f‖ = ‖f‖∞ + [f]γ`,

where `[f]γ` is Mathlib's least Hölder constant `nnHolderNorm γ f`. In
geometric applications `Ω` is a set with its subtype metric. No openness,
measurability, or finite dimension is assumed, and because the carrier is a
`BoundedContinuousFunction`, membership includes global boundedness even when
`Ω` is unbounded.

Mathlib has `HolderWith`, `MemHolder` and `nnHolderNorm`, but no bundled space with this norm, so we
build the space, its `NormedSpace` structure and its completeness. We also prove
`LipschitzOnWith.holderOnWith_of_norm_le`: a value bound and a Lipschitz bound give an explicit
Hölder constant on any set, bounded or not, for maps into any seminormed additive group.

## Main declarations

* `C0GammaOn Ω γ`: a bounded continuous function together with a proof that its `γ`-Hölder
  seminorm is finite.
* `holderSeminorm`: the least Hölder constant `[f]γ`, and `norm_def`: `‖f‖ = ‖f‖∞ + [f]γ`.
* The `AddCommGroup`, `Module ℝ`, `NormedAddCommGroup`, `NormedSpace ℝ`, and `CompleteSpace`
  instances.
* `toBoundedContinuousFunctionCLM`, `evalCLM`, `restrictCLM`: forgetting the Hölder bound,
  evaluating at a point, and restricting to a metric subspace, each as a continuous linear map
  of norm at most one.

## How it works

We prove completeness with `Metric.complete_of_cauchySeq_tendsto`. A Cauchy sequence `u n` is Cauchy
in `Ω →ᵇ ℝ`, since `toBoundedContinuousFunctionCLM` is uniformly continuous, so it has a uniform
limit `F` there. For large `n` and `m`, `u n - u m` is Hölder with constant
`nndist (u n) (u m) < ε / 2` (`holderWith_sub_nndist`), and letting `m → ∞` pointwise shows that
`u n - F` is Hölder with constant `ε / 2`. Taking `ε = 2` puts `F` in the space, and together with
the uniform convergence this gives `‖u n - F‖ < ε` for large `n`. The interpolation lemma combines
the `0`-Hölder bound `2 * C`, which follows from the value bound, with the Lipschitz bound through
Mathlib's `HolderOnWith.interpolate`. Evans states the Banach property of `C^{k,γ}(Ū)` in §5.1,
Theorem 1; we prove the case `k = 0` for a metric type `Ω`, with no boundedness of `Ω`.

## Implementation notes

The norm is defined by hand and the normed-group structure is built from `NormedSpace.Core`,
so that the `AddCommGroup` structure transported from `Ω →ᵇ ℝ` and the norm are definitionally
compatible with projection lemmas such as `toBoundedContinuousFunction_add`. All coercions
to functions go through the underlying bounded continuous function.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.1, pp. 254-255, for the norm
  `‖u‖_{C^{0,γ}} = ‖u‖_C + [u]_γ`, and §5.1, Theorem 1, p. 255, which states that `C^{k,γ}(Ū)` is a
  Banach space.
  <https://doi.org/10.1090/gsm/019>
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 4.
  <https://doi.org/10.1007/978-3-642-61798-0>
-/

@[expose] public section

noncomputable section

open Filter NNReal Topology
open scoped BoundedContinuousFunction

/-- If `f` is `L`-Lipschitz on `s` and `‖f x‖ ≤ C` for every `x ∈ s`, then for every exponent
`r ≤ 1` the map `f` is `r`-Hölder on `s` with constant `(2 * C) ^ (1 - r) * L ^ r`. The set `s`
need not be bounded. -/
theorem LipschitzOnWith.holderOnWith_of_norm_le
    {X E : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup E]
    {s : Set X} {f : X → E} {C L r : ℝ≥0}
    (hL : LipschitzOnWith L f s) (hC : ∀ x ∈ s, ‖f x‖ ≤ C) (hr : r ≤ 1) :
    HolderOnWith ((2 * C) ^ ((1 - r : ℝ≥0) : ℝ) * L ^ (r : ℝ)) r f s := by
  have hzero : HolderOnWith (2 * C) 0 f s := by
    intro x hx y hy
    simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one, edist_nndist]
    apply ENNReal.coe_le_coe.mpr
    have hdist : dist (f x) (f y) ≤ (2 : ℝ) * C := by
      calc
        dist (f x) (f y) ≤ ‖f x‖ + ‖f y‖ := dist_le_norm_add_norm _ _
        _ ≤ (C : ℝ) + C := add_le_add (hC x hx) (hC y hy)
        _ = _ := (two_mul _).symm
    exact_mod_cast hdist
  simpa only [zero_mul, one_mul, zero_add] using
    hzero.interpolate hL.holderOnWith (tsub_add_cancel_of_le hr)

namespace HolderSpace

/-- The Banach space of bounded `γ`-Hölder real-valued functions on a metric
type `Ω`, equipped with `‖f‖∞ + [f]γ`.

For a geometric domain, take `Ω` to be the corresponding subtype. -/
structure C0GammaOn (Ω : Type*) [MetricSpace Ω] (γ : Exponent) where
  /-- The underlying bounded continuous function on the metric domain `Ω`. -/
  toBoundedContinuousFunction : Ω →ᵇ ℝ
  /-- Finiteness of the `γ`-Hölder seminorm. -/
  memHolder :
    _root_.MemHolder (γ : ℝ≥0) toBoundedContinuousFunction

namespace C0GammaOn

variable {Ω : Type*} [MetricSpace Ω] {γ : Exponent}

instance : CoeFun (C0GammaOn Ω γ) fun _ ↦ Ω → ℝ :=
  ⟨fun f ↦ f.toBoundedContinuousFunction⟩

/-- Two bundled Hölder functions with the same values at every point are equal. -/
@[ext]
theorem ext {f g : C0GammaOn Ω γ} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f hf =>
      cases g with
      | mk g hg =>
          congr
          exact BoundedContinuousFunction.ext h

/-- The underlying bounded continuous function determines a Hölder function. -/
theorem toBoundedContinuousFunction_injective :
    Function.Injective
      (toBoundedContinuousFunction : C0GammaOn Ω γ → Ω →ᵇ ℝ) := by
  intro f g h
  exact ext fun x ↦ DFunLike.congr_fun h x

/-- A bundled Hölder function is continuous on its domain. -/
theorem continuous (f : C0GammaOn Ω γ) : Continuous f :=
  f.toBoundedContinuousFunction.continuous

/-- The least Hölder constant of a bundled function. -/
noncomputable def holderSeminorm (f : C0GammaOn Ω γ) : ℝ≥0 :=
  _root_.nnHolderNorm (γ : ℝ≥0) f.toBoundedContinuousFunction

/-- The least Hölder constant is itself an admissible constant. -/
theorem holderWith (f : C0GammaOn Ω γ) :
    _root_.HolderWith f.holderSeminorm (γ : ℝ≥0) f :=
  f.memHolder.holderWith

instance : Zero (C0GammaOn Ω γ) where
  zero :=
    ⟨0, by
      simpa only [BoundedContinuousFunction.coe_zero] using
        (_root_.memHolder_zero :
          _root_.MemHolder (γ : ℝ≥0) (0 : Ω → ℝ))⟩

instance : Add (C0GammaOn Ω γ) where
  add f g :=
    ⟨f.toBoundedContinuousFunction + g.toBoundedContinuousFunction, by
      simpa only [BoundedContinuousFunction.coe_add] using
        f.memHolder.add g.memHolder⟩

instance : Neg (C0GammaOn Ω γ) where
  neg f :=
    ⟨-f.toBoundedContinuousFunction, by
      simpa only [BoundedContinuousFunction.coe_neg, neg_one_smul] using
        f.memHolder.smul (c := (-1 : ℝ))⟩

instance : Sub (C0GammaOn Ω γ) where
  sub f g := f + -g

instance : SMul ℝ (C0GammaOn Ω γ) where
  smul c f :=
    ⟨c • f.toBoundedContinuousFunction, by
      rw [BoundedContinuousFunction.coe_smul]
      change
        _root_.MemHolder (γ : ℝ≥0)
          (c • (f.toBoundedContinuousFunction : Ω → ℝ))
      exact f.memHolder.smul⟩

instance : SMul ℕ (C0GammaOn Ω γ) where
  smul n f :=
    ⟨n • f.toBoundedContinuousFunction, by
      simpa only [BoundedContinuousFunction.coe_nsmul] using
        f.memHolder.nsmul n⟩

instance : SMul ℤ (C0GammaOn Ω γ) where
  smul z f :=
    ⟨z • f.toBoundedContinuousFunction, by
      rw [BoundedContinuousFunction.coe_zsmul]
      change
        _root_.MemHolder (γ : ℝ≥0)
          (z • (f.toBoundedContinuousFunction : Ω → ℝ))
      simpa only [← Int.cast_smul_eq_zsmul ℝ] using
        f.memHolder.smul (c := (z : ℝ))⟩

/-- The underlying bounded continuous function of `0` is `0`. -/
@[simp]
theorem toBoundedContinuousFunction_zero :
    (0 : C0GammaOn Ω γ).toBoundedContinuousFunction = 0 :=
  rfl

/-- The underlying function of a sum is the sum of the underlying functions. -/
@[simp]
theorem toBoundedContinuousFunction_add (f g : C0GammaOn Ω γ) :
    (f + g).toBoundedContinuousFunction =
      f.toBoundedContinuousFunction + g.toBoundedContinuousFunction :=
  rfl

/-- The underlying function of a negation is the negated underlying function. -/
@[simp]
theorem toBoundedContinuousFunction_neg (f : C0GammaOn Ω γ) :
    (-f).toBoundedContinuousFunction = -f.toBoundedContinuousFunction :=
  rfl

/-- The underlying function of a difference is the difference of the underlying functions. -/
@[simp]
theorem toBoundedContinuousFunction_sub (f g : C0GammaOn Ω γ) :
    (f - g).toBoundedContinuousFunction =
      f.toBoundedContinuousFunction - g.toBoundedContinuousFunction := by
  rfl

/-- The underlying function of a real scalar multiple is the scalar multiple of the underlying
function. -/
@[simp]
theorem toBoundedContinuousFunction_smul (c : ℝ) (f : C0GammaOn Ω γ) :
    (c • f).toBoundedContinuousFunction =
      c • f.toBoundedContinuousFunction :=
  rfl

instance : AddCommGroup (C0GammaOn Ω γ) := fast_instance%
  toBoundedContinuousFunction_injective.addCommGroup
    toBoundedContinuousFunction
    toBoundedContinuousFunction_zero
    toBoundedContinuousFunction_add
    toBoundedContinuousFunction_neg
    toBoundedContinuousFunction_sub
    (fun _ _ ↦ rfl)
    fun _ _ ↦ rfl

instance : Module ℝ (C0GammaOn Ω γ) := fast_instance%
  Module.ofMinimalAxioms
    (fun c f g ↦ ext fun x ↦ by simp)
    (fun c d f ↦ ext fun x ↦ by simp [add_mul])
    (fun c d f ↦ ext fun x ↦ by simp [mul_smul])
    fun f ↦ ext fun x ↦ by simp

/-- The Evans `C^{0,γ}` norm: uniform norm plus Hölder seminorm. -/
instance : Norm (C0GammaOn Ω γ) where
  norm f := ‖f.toBoundedContinuousFunction‖ + f.holderSeminorm

/-- The `C^{0,γ}` norm is the sum of the uniform norm and the Hölder seminorm. -/
theorem norm_def (f : C0GammaOn Ω γ) :
    ‖f‖ = ‖f.toBoundedContinuousFunction‖ + f.holderSeminorm :=
  rfl

/-- The uniform norm is bounded by the full Hölder norm. -/
theorem norm_toBoundedContinuousFunction_le (f : C0GammaOn Ω γ) :
    ‖f.toBoundedContinuousFunction‖ ≤ ‖f‖ := by
  rw [norm_def]
  exact le_add_of_nonneg_right f.holderSeminorm.coe_nonneg

/-- The Hölder seminorm is bounded by the full Hölder norm. -/
theorem holderSeminorm_le_norm (f : C0GammaOn Ω γ) :
    (f.holderSeminorm : ℝ) ≤ ‖f‖ := by
  rw [norm_def]
  exact le_add_of_nonneg_left (norm_nonneg _)

/-- The supremum norm plus the Hölder seminorm satisfies the real normed-space axioms. -/
theorem normedSpaceCore :
    NormedSpace.Core ℝ (C0GammaOn Ω γ) where
  norm_nonneg f :=
    add_nonneg (norm_nonneg _) f.holderSeminorm.coe_nonneg
  norm_smul c f := by
    rw [norm_def, norm_def, toBoundedContinuousFunction_smul, norm_smul]
    have hseminorm :=
      f.memHolder.nnHolderNorm_smul c
    change
      nnHolderNorm (γ : ℝ≥0)
          (fun x ↦ c • f.toBoundedContinuousFunction x) =
        ‖c‖₊ *
          nnHolderNorm (γ : ℝ≥0) f.toBoundedContinuousFunction
      at hseminorm
    change
      ‖c‖ * ‖f.toBoundedContinuousFunction‖ +
          ((nnHolderNorm (γ : ℝ≥0)
            (c • f.toBoundedContinuousFunction) : ℝ≥0) : ℝ) =
        ‖c‖ *
          (‖f.toBoundedContinuousFunction‖ +
            ((nnHolderNorm (γ : ℝ≥0)
              f.toBoundedContinuousFunction : ℝ≥0) : ℝ))
    rw [BoundedContinuousFunction.coe_smul]
    rw [hseminorm, NNReal.coe_mul, coe_nnnorm]
    ring
  norm_triangle f g := by
    rw [norm_def, norm_def, norm_def, toBoundedContinuousFunction_add]
    have hseminorm :=
      f.memHolder.nnHolderNorm_add_le g.memHolder
    change
      ‖f.toBoundedContinuousFunction + g.toBoundedContinuousFunction‖ +
          ((nnHolderNorm (γ : ℝ≥0)
            (f.toBoundedContinuousFunction +
              g.toBoundedContinuousFunction) : ℝ≥0) : ℝ) ≤
        (‖f.toBoundedContinuousFunction‖ +
          ((nnHolderNorm (γ : ℝ≥0)
            f.toBoundedContinuousFunction : ℝ≥0) : ℝ)) +
        (‖g.toBoundedContinuousFunction‖ +
          ((nnHolderNorm (γ : ℝ≥0)
            g.toBoundedContinuousFunction : ℝ≥0) : ℝ))
    calc
      _ ≤
          (‖f.toBoundedContinuousFunction‖ +
            ‖g.toBoundedContinuousFunction‖) +
          (((nnHolderNorm (γ : ℝ≥0)
              f.toBoundedContinuousFunction : ℝ≥0) : ℝ) +
            ((nnHolderNorm (γ : ℝ≥0)
              g.toBoundedContinuousFunction : ℝ≥0) : ℝ)) := by
            exact add_le_add (norm_add_le _ _) (by exact_mod_cast hseminorm)
      _ = _ := by ring
  norm_eq_zero_iff f := by
    constructor
    · intro h
      have hsup : ‖f.toBoundedContinuousFunction‖ = 0 := by
        have hnonneg : 0 ≤ (f.holderSeminorm : ℝ) :=
          f.holderSeminorm.coe_nonneg
        rw [norm_def] at h
        linarith [norm_nonneg f.toBoundedContinuousFunction]
      apply ext
      intro x
      have hfzero : f.toBoundedContinuousFunction = 0 :=
        norm_eq_zero.mp hsup
      simp [hfzero]
    · rintro rfl
      simp [norm_def, holderSeminorm]

noncomputable instance : NormedAddCommGroup (C0GammaOn Ω γ) :=
  NormedAddCommGroup.ofCore normedSpaceCore

noncomputable instance : NormedSpace ℝ (C0GammaOn Ω γ) :=
  NormedSpace.ofCore normedSpaceCore

/-- The Hölder seminorm, as an `ℝ≥0` quantity, is bounded by the full norm. -/
theorem holderSeminorm_le_nnnorm (f : C0GammaOn Ω γ) :
    f.holderSeminorm ≤ ‖f‖₊ := by
  exact_mod_cast f.holderSeminorm_le_norm

/-- Point evaluation is controlled by the full Hölder norm. -/
theorem norm_apply_le (f : C0GammaOn Ω γ) (x : Ω) :
    ‖f x‖ ≤ ‖f‖ :=
  (f.toBoundedContinuousFunction.norm_coe_le_norm x).trans
    f.norm_toBoundedContinuousFunction_le

/-- Forgetting Hölder control gives a contraction to bounded continuous
functions. -/
noncomputable def toBoundedContinuousFunctionCLM :
    C0GammaOn Ω γ →L[ℝ] (Ω →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := toBoundedContinuousFunction
      map_add' := toBoundedContinuousFunction_add
      map_smul' := toBoundedContinuousFunction_smul }
    1 fun f ↦ by
      simpa using f.norm_toBoundedContinuousFunction_le

/-- The forgetful continuous linear map acts by taking the underlying bounded continuous
function. -/
@[simp]
theorem toBoundedContinuousFunctionCLM_apply (f : C0GammaOn Ω γ) :
    toBoundedContinuousFunctionCLM f = f.toBoundedContinuousFunction :=
  rfl

/-- Evaluation at a point is a norm-at-most-one continuous linear map. -/
noncomputable def evalCLM (x : Ω) : C0GammaOn Ω γ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 fun f ↦ by
      simpa using f.norm_apply_le x

/-- The evaluation functional at `x` agrees with pointwise evaluation. -/
@[simp]
theorem evalCLM_apply (x : Ω) (f : C0GammaOn Ω γ) :
    evalCLM x f = f x :=
  rfl

section Restriction

variable {Z : Type*} [MetricSpace Z]

/-- Restrict a global Hölder function to a metric subspace. -/
noncomputable def restrict (s : Set Z) (f : C0GammaOn Z γ) :
    C0GammaOn s γ where
  toBoundedContinuousFunction :=
    f.toBoundedContinuousFunction.compContinuous
      ⟨Subtype.val, continuous_subtype_val⟩
  memHolder := (f.holderWith.holderOnWith s).holderWith.memHolder

/-- The restriction to `s` evaluates the original function at the underlying point of `Z`. -/
@[simp]
theorem restrict_apply (s : Set Z) (f : C0GammaOn Z γ) (x : s) :
    restrict s f x = f x :=
  rfl

/-- Restricting the zero function gives the zero function. -/
@[simp]
theorem restrict_zero (s : Set Z) :
    restrict s (0 : C0GammaOn Z γ) = 0 :=
  rfl

/-- Restriction to `s` is additive. -/
@[simp]
theorem restrict_add (s : Set Z) (f g : C0GammaOn Z γ) :
    restrict s (f + g) = restrict s f + restrict s g :=
  rfl

/-- Restriction to `s` commutes with real scalar multiplication. -/
@[simp]
theorem restrict_smul (s : Set Z) (c : ℝ) (f : C0GammaOn Z γ) :
    restrict s (c • f) = c • restrict s f :=
  rfl

/-- Restriction does not increase the `C^{0,γ}` norm. -/
theorem norm_restrict_le (s : Set Z) (f : C0GammaOn Z γ) :
    ‖restrict s f‖ ≤ ‖f‖ := by
  rw [norm_def, norm_def]
  apply add_le_add
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
    intro x
    exact f.toBoundedContinuousFunction.norm_coe_le_norm x
  · exact_mod_cast
      (f.holderWith.holderOnWith s).holderWith.nnholderNorm_le

/-- Restriction to a metric subspace, as a norm-at-most-one continuous
linear map. -/
noncomputable def restrictCLM (s : Set Z) :
    C0GammaOn Z γ →L[ℝ] C0GammaOn s γ :=
  LinearMap.mkContinuous
    { toFun := restrict s
      map_add' := restrict_add s
      map_smul' := restrict_smul s }
    1 fun f ↦ by
      simpa using norm_restrict_le s f

/-- The bundled restriction map acts by `restrict s`. -/
@[simp]
theorem restrictCLM_apply (s : Set Z) (f : C0GammaOn Z γ) :
    restrictCLM s f = restrict s f :=
  rfl

end Restriction

/-- The difference seminorm is controlled by the distance in `C^{0,γ}`. -/
theorem holderSeminorm_sub_le_nndist (f g : C0GammaOn Ω γ) :
    holderSeminorm (f - g) ≤ nndist f g := by
  calc
    holderSeminorm (f - g) ≤ ‖f - g‖₊ :=
      holderSeminorm_le_nnnorm (f - g)
    _ = nndist f g := (nndist_eq_nnnorm_sub f g).symm

/-- A difference is Hölder with constant bounded by its full-space distance. -/
theorem holderWith_sub_nndist (f g : C0GammaOn Ω γ) :
    _root_.HolderWith (nndist f g) (γ : ℝ≥0)
      (f.toBoundedContinuousFunction - g.toBoundedContinuousFunction) := by
  exact (f - g).memHolder.holderWith.mono
    (holderSeminorm_sub_le_nndist f g)

private theorem holderWith_sub_limit
    (u : ℕ → C0GammaOn Ω γ) (F : Ω →ᵇ ℝ)
    (hF :
      Tendsto (fun n ↦ (u n).toBoundedContinuousFunction)
        atTop (𝓝 F))
    (n : ℕ) (C : ℝ≥0)
    (hC : ∀ᶠ m in atTop, nndist (u n) (u m) ≤ C) :
    _root_.HolderWith C (γ : ℝ≥0) fun x ↦ u n x - F x := by
  intro x y
  have hFx :
      Tendsto (fun m ↦ (u m).toBoundedContinuousFunction x)
        atTop (𝓝 (F x)) :=
    ((BoundedContinuousFunction.evalCLM ℝ x).continuous.tendsto F).comp hF
  have hFy :
      Tendsto (fun m ↦ (u m).toBoundedContinuousFunction y)
        atTop (𝓝 (F y)) :=
    ((BoundedContinuousFunction.evalCLM ℝ y).continuous.tendsto F).comp hF
  have hx :
      Tendsto (fun m ↦ u n x - u m x)
        atTop (𝓝 (u n x - F x)) :=
    tendsto_const_nhds.sub hFx
  have hy :
      Tendsto (fun m ↦ u n y - u m y)
        atTop (𝓝 (u n y - F y)) :=
    tendsto_const_nhds.sub hFy
  refine le_of_tendsto (hx.edist hy) ?_
  filter_upwards [hC] with m hm
  exact (holderWith_sub_nndist (u n) (u m)).mono hm x y

/-- `C0GammaOn Ω γ` is complete for `‖f‖∞ + [f]γ`. -/
noncomputable instance : CompleteSpace (C0GammaOn Ω γ) :=
  Metric.complete_of_cauchySeq_tendsto fun u hu ↦ by
    have hbcf :
        CauchySeq (fun n ↦ (u n).toBoundedContinuousFunction) := by
      simpa only [Function.comp_def,
        toBoundedContinuousFunctionCLM_apply] using
        toBoundedContinuousFunctionCLM.uniformContinuous.comp_cauchySeq hu
    obtain ⟨F, hF⟩ :=
      cauchySeq_tendsto_of_complete hbcf
    obtain ⟨N, hN⟩ :=
      (Metric.cauchySeq_iff.1 hu) 1 zero_lt_one
    have htail :
        ∀ᶠ m in atTop, nndist (u N) (u m) ≤ 1 := by
      filter_upwards [eventually_ge_atTop N] with m hm
      exact le_of_lt (by
        exact_mod_cast hN N le_rfl m hm)
    have hdiff :
        _root_.HolderWith 1 (γ : ℝ≥0) fun x ↦ u N x - F x :=
      holderWith_sub_limit u F hF N 1 htail
    have hFholder :
        _root_.MemHolder (γ : ℝ≥0) F := by
      have hneg :
          _root_.MemHolder (γ : ℝ≥0)
            (-(fun x ↦ u N x - F x)) := by
        simpa only [neg_one_smul] using
          hdiff.memHolder.smul (c := (-1 : ℝ))
      have hadd :=
        (u N).memHolder.add hneg
      convert hadd using 1
      funext x
      simp
    let limit : C0GammaOn Ω γ := ⟨F, hFholder⟩
    refine ⟨limit, Metric.tendsto_atTop.2 fun ε hε ↦ ?_⟩
    have hhalf : 0 < ε / 2 := half_pos hε
    obtain ⟨Nc, hNc⟩ :=
      (Metric.cauchySeq_iff.1 hu) (ε / 2) hhalf
    obtain ⟨Nu, hNu⟩ :=
      (Metric.tendsto_atTop.1 hF) (ε / 2) hhalf
    refine ⟨max Nc Nu, fun n hn ↦ ?_⟩
    have hnc : Nc ≤ n := le_trans (le_max_left _ _) hn
    have hnu : Nu ≤ n := le_trans (le_max_right _ _) hn
    let C : ℝ≥0 := ⟨ε / 2, hhalf.le⟩
    have htail' :
        ∀ᶠ m in atTop, nndist (u n) (u m) ≤ C := by
      filter_upwards [eventually_ge_atTop Nc] with m hm
      exact le_of_lt (by
        exact_mod_cast hNc n hnc m hm)
    have hdiff' :
        _root_.HolderWith C (γ : ℝ≥0) fun x ↦ u n x - F x :=
      holderWith_sub_limit u F hF n C htail'
    have hseminorm :
        ((nnHolderNorm (γ : ℝ≥0)
          ((u n).toBoundedContinuousFunction - F) : ℝ≥0) : ℝ) ≤
            ε / 2 := by
      exact_mod_cast hdiff'.nnholderNorm_le
    have huniform :
        ‖(u n).toBoundedContinuousFunction - F‖ < ε / 2 := by
      simpa only [dist_eq_norm] using hNu n hnu
    rw [dist_eq_norm, norm_def]
    change
      ‖(u n).toBoundedContinuousFunction - F‖ +
          ((nnHolderNorm (γ : ℝ≥0)
            ((u n).toBoundedContinuousFunction - F) : ℝ≥0) : ℝ) < ε
    calc
      _ < ε / 2 + ε / 2 :=
        add_lt_add_of_lt_of_le huniform hseminorm
      _ = ε := by ring

end C0GammaOn

end HolderSpace
