/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import PDE.Analysis.Evolution.Semigroup.ExponentialShift
public import PDE.Analysis.Evolution.Semigroup.LaplaceTransform
public import PDE.Analysis.Evolution.Semigroup.Yosida

/-!
# Complex-linear semigroups and their generators

Spectral theory of a generator needs complex scalars: resolvents at complex parameters,
eigenvalues, Riesz projections. A complex Banach space is a real Banach space, so a semigroup
on it is a `StronglyContinuousSemigroup` of the real library, and no second semigroup structure
is needed. It is complex linear when every `T(t)` commutes with multiplication by `i`. This
module makes the real generator of such a semigroup a complex-linear partial operator, with the
same domain and the same values, and proves the facts about it that the complex spectral
theory uses. Semigroups over other fields containing `ℝ` are not treated.

## Main results

* `ContinuousLinearMap.ofCommuteI`: a real-linear bounded operator between complex normed
  spaces that commutes with `i` is complex linear, with the same norm.
* `StronglyContinuousSemigroup.IsComplexLinear`: every `T(t)` commutes with `i`; then
  `IsComplexLinear.clm t` is `T(t)` as a complex-linear bounded operator.
* `IsComplexLinear.generator`: the generator as a complex-linear partial operator. Its graph is
  the generator relation (`mem_graph_generator_iff`), and on a Banach space it is closed
  (`isClosed_generator`) and densely defined (`dense_domain_generator`).
* `IsComplexLinear.map_mem_graph_of_commute`: a bounded operator that commutes with the
  semigroup maps the graph of the generator into itself.
* `IsComplexLinear.rescale` and `hasGeneratorAt_rescale_iff`: for every complex `z`,
  `e^{zt} T(t)` is a complex-linear semigroup whose generator is `A + z` on the domain of `A`.
* `StronglyContinuousSemigroup.hasGeneratorAt_integratedOperator`: for every semigroup on a
  real Banach space, `∫₀ᵗ T(s) x ds` is in the domain of the generator, which maps it to
  `T(t) x - x`. `IsComplexLinear.integral` is this time integral as a complex-linear operator.

## How it works

If `T(t)` commutes with `i`, it commutes with every complex scalar
(`IsComplexLinear.map_smul_complex`), so the orbit of `c x` is `c` times the orbit of `x`. Hence
the domain of the real generator is a complex subspace and the generator is complex linear on
it, and its closedness and density are those of the real generator (`isClosed_generatorPMap`,
`dense_generatorPMap_domain_of_complete`). The rescaled semigroup moves a complex spectral
parameter to `0`. At a real rate it is the real library's `expRescale`
(`IsComplexLinear.rescale_ofReal`), and its generator is computed in the same way, by the
product rule at time zero. The time integral is the case `λ = 0` of
`hasGeneratorAt_truncatedLaplaceTransform`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Graduate Texts in Mathematics 194, Springer, 2000, Chapter II, Section 1 (the generator of a
  strongly continuous semigroup and the time integral of an orbit).
  <https://doi.org/10.1007/b97696>
-/

@[expose] public noncomputable section

open Set

namespace ContinuousLinearMap

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- A real-linear bounded operator between complex normed spaces that commutes with
multiplication by `i`, as a complex-linear bounded operator. For operators out of `ℂ`, Mathlib's
`ContinuousLinearMap.complexOfReal` builds the same operator from its value at `i`. -/
def ofCommuteI (f : X →L[ℝ] Y) (hf : ∀ x, f (Complex.I • x) = Complex.I • f x) : X →L[ℂ] Y where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    have hc (u : X) : c • u = c.re • u + c.im • (Complex.I • u) := by
      conv_lhs => rw [← Complex.re_add_im c]
      rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    have hc' (u : Y) : c • u = c.re • u + c.im • (Complex.I • u) := by
      conv_lhs => rw [← Complex.re_add_im c]
      rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    rw [RingHom.id_apply, hc x, hc' (f x), _root_.map_add, _root_.map_smul, _root_.map_smul, hf]
  cont := f.continuous

/-- `ofCommuteI` does not change the values. -/
@[simp]
theorem ofCommuteI_apply (f : X →L[ℝ] Y) (hf : ∀ x, f (Complex.I • x) = Complex.I • f x)
    (x : X) : f.ofCommuteI hf x = f x :=
  rfl

/-- Forgetting the complex linearity of `ofCommuteI` gives the real-linear operator back. -/
@[simp]
theorem restrictScalars_ofCommuteI (f : X →L[ℝ] Y)
    (hf : ∀ x, f (Complex.I • x) = Complex.I • f x) :
    (f.ofCommuteI hf).restrictScalars ℝ = f :=
  rfl

/-- `ofCommuteI` does not change the operator norm. -/
@[simp]
theorem norm_ofCommuteI (f : X →L[ℝ] Y) (hf : ∀ x, f (Complex.I • x) = Complex.I • f x) :
    ‖f.ofCommuteI hf‖ = ‖f‖ := by
  rw [← norm_restrictScalars (𝕜' := ℝ), restrictScalars_ofCommuteI]

end ContinuousLinearMap

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

/-- The time integral of an orbit is in the generator domain, and the generator maps
`∫₀ᵗ T(s) x ds` to `T(t) x - x`. -/
theorem hasGeneratorAt_integratedOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (T : StronglyContinuousSemigroup E) (t : NNReal) (x : E) :
    T.HasGeneratorAt (T.integratedOperator t x) (T t x - x) := by
  have h := T.hasGeneratorAt_truncatedLaplaceTransform 0 t x
  have e : T.truncatedLaplaceTransform 0 t x = T.integratedOperator t x := by
    simp [truncatedLaplaceTransform_apply, integratedOperator_apply]
  simpa [e] using h

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- A strongly continuous semigroup on a complex normed space is complex linear when every
`T(t)` commutes with multiplication by `i`. -/
def IsComplexLinear (T : StronglyContinuousSemigroup X) : Prop :=
  ∀ (t : NNReal) (x : X), T t (Complex.I • x) = Complex.I • T t x

namespace IsComplexLinear

variable {T : StronglyContinuousSemigroup X} (hT : T.IsComplexLinear) {x y : X}

include hT

/-- The operator `T(t)` of a complex-linear semigroup as a complex-linear bounded operator. -/
def clm (t : NNReal) : X →L[ℂ] X := (T t).ofCommuteI (hT t)

/-- `hT.clm t` acts as `T t`. -/
@[simp]
theorem clm_apply (t : NNReal) (x : X) : hT.clm t x = T t x :=
  rfl

/-- The operators of a complex-linear semigroup commute with complex scalars. -/
theorem map_smul_complex (t : NNReal) (c : ℂ) (x : X) : T t (c • x) = c • T t x :=
  _root_.map_smul (hT.clm t) c x

/-- At time zero, `hT.clm` is the identity. -/
@[simp]
theorem clm_zero : hT.clm 0 = 1 :=
  ContinuousLinearMap.ext fun x ↦ T.map_zero_apply x

/-- The semigroup law for `hT.clm`. -/
theorem clm_add (s t : NNReal) : hT.clm (s + t) = hT.clm s * hT.clm t :=
  ContinuousLinearMap.ext fun x ↦ T.map_add_apply s t x

/-- The operators of a semigroup commute. -/
theorem commute_clm (s t : NNReal) : Commute (hT.clm s) (hT.clm t) := by
  rw [Commute, SemiconjBy, ← clm_add, ← clm_add, add_comm]

/-- The complex-linear operator `hT.clm t` has the norm of `T t`. -/
@[simp]
theorem norm_clm (t : NNReal) : ‖hT.clm t‖ = ‖T t‖ :=
  ContinuousLinearMap.norm_ofCommuteI _ _

/-- The generator relation of a complex-linear semigroup is closed under complex scalars. -/
theorem hasGeneratorAt_smul (c : ℂ) (hx : T.HasGeneratorAt x y) :
    T.HasGeneratorAt (c • x) (c • y) :=
  (HasDerivWithinAt.const_smul c hx).congr
    (fun s _ ↦ by simp [realOrbit, hT.map_smul_complex])
    (by simp [realOrbit])

/-- **The generator of a complex-linear semigroup** as a complex-linear partial operator: the
generator of the real library, with the same domain and the same values. -/
def generator : X →ₗ.[ℂ] X where
  domain :=
    { carrier := T.generatorPMap.domain
      add_mem' := T.generatorPMap.domain.add_mem
      zero_mem' := T.generatorPMap.domain.zero_mem
      smul_mem' := fun c _ ⟨Ax, hx⟩ ↦ ⟨c • Ax, hT.hasGeneratorAt_smul c hx⟩ }
  toFun :=
    { toFun := fun x ↦ T.generatorPMap ⟨x.1, x.2⟩
      map_add' := fun x y ↦ T.generatorPMap.map_add ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
      map_smul' := fun c x ↦ (T.hasGeneratorAt_generatorPMap ⟨c • x.1, (c • x).2⟩).unique
        (hT.hasGeneratorAt_smul c (T.hasGeneratorAt_generatorPMap ⟨x.1, x.2⟩)) }

/-- **The graph of the generator is the generator relation**: `(x, y)` is in the graph exactly
when the orbit of `x` has the right derivative `y` at time zero. -/
theorem mem_graph_generator_iff : (x, y) ∈ hT.generator.graph ↔ T.HasGeneratorAt x y := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨u, rfl, rfl⟩
    exact T.hasGeneratorAt_generatorPMap ⟨u.1, u.2⟩
  · intro h
    exact ⟨⟨x, ⟨y, h⟩⟩, rfl, (T.hasGeneratorAt_generatorPMap ⟨x, ⟨y, h⟩⟩).unique h⟩

/-- The graph of the complex generator is the graph of the generator of the real library. -/
theorem coe_graph_generator :
    (hT.generator.graph : Set (X × X)) = (T.generatorPMap.graph : Set (X × X)) := by
  ext ⟨x, y⟩
  rw [SetLike.mem_coe, SetLike.mem_coe, hT.mem_graph_generator_iff,
    T.hasGeneratorAt_iff_mem_generatorPMap_graph]

/-- The semigroup maps the graph of its generator into itself: `A T(t) x = T(t) A x`. -/
theorem map_mem_graph (t : NNReal) (h : (x, y) ∈ hT.generator.graph) :
    (T t x, T t y) ∈ hT.generator.graph :=
  hT.mem_graph_generator_iff.mpr ((hT.mem_graph_generator_iff.mp h).map t)

/-- **What commutes with the semigroup commutes with the generator.** A bounded operator `S`
with `S T(t) = T(t) S` for all `t` maps the graph of the generator into itself. -/
theorem map_mem_graph_of_commute {S : X →L[ℂ] X} (hS : ∀ t, Commute S (hT.clm t))
    (h : (x, y) ∈ hT.generator.graph) : (S x, S y) ∈ hT.generator.graph :=
  hT.mem_graph_generator_iff.mpr ((hT.mem_graph_generator_iff.mp h).map_of_commute
    (C := S.restrictScalars ℝ) fun t x ↦ DFunLike.congr_fun (hS t).eq x)

/-- The generator of a complex-linear semigroup on a Banach space is closed. -/
theorem isClosed_generator [CompleteSpace X] : hT.generator.IsClosed := by
  change IsClosed (hT.generator.graph : Set (X × X))
  rw [hT.coe_graph_generator]
  exact T.isClosed_generatorPMap

/-- The generator of a complex-linear semigroup on a Banach space is densely defined. -/
theorem dense_domain_generator [CompleteSpace X] : Dense (hT.generator.domain : Set X) :=
  T.dense_generatorPMap_domain_of_complete

/-! ### Rescaling by a complex exponential -/

/-- The rescaled semigroup `t ↦ exp (z t) T(t)` of a complex-linear semigroup. -/
def rescale (z : ℂ) : StronglyContinuousSemigroup X where
  toMonoidHom :=
    { toFun := fun t ↦ Complex.exp (z * ((t.toAdd : ℝ) : ℂ)) • T t.toAdd
      map_one' := by simp
      map_mul' := by
        intro s t
        change Complex.exp (z * (((s.toAdd + t.toAdd : NNReal) : ℝ) : ℂ)) •
            T (s.toAdd + t.toAdd) =
          (Complex.exp (z * ((s.toAdd : ℝ) : ℂ)) • T s.toAdd) *
            (Complex.exp (z * ((t.toAdd : ℝ) : ℂ)) • T t.toAdd)
        ext x
        simp only [NNReal.coe_add, Complex.ofReal_add, mul_add, Complex.exp_add, smul_apply,
          mul_apply_eq_comp, T.map_add_apply, hT.map_smul_complex, smul_smul] }
  continuous_toPointwise := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro x
    exact (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp NNReal.continuous_coe))).smul (T.continuous_orbit x)

/-- The rescaled semigroup at time `t` is `exp (z t) T(t)`. -/
@[simp]
theorem rescale_apply (z : ℂ) (t : NNReal) :
    hT.rescale z t = Complex.exp (z * ((t : ℝ) : ℂ)) • T t :=
  rfl

/-- The rescaled semigroup is complex linear. -/
theorem isComplexLinear_rescale (z : ℂ) : (hT.rescale z).IsComplexLinear := fun t x ↦ by
  simp only [rescale_apply, smul_apply, hT t x, smul_comm Complex.I]

/-- Rescaling by `z` and then by `w` is rescaling by `w + z`. -/
theorem rescale_rescale (z w : ℂ) :
    (hT.isComplexLinear_rescale z).rescale w = hT.rescale (w + z) := by
  ext t x
  simp only [rescale_apply, smul_apply, smul_smul, add_mul, Complex.exp_add]

/-- Rescaling by `0` does not change the semigroup. -/
@[simp]
theorem rescale_zero : hT.rescale 0 = T := by
  ext t x
  simp

/-- Rescaling by a real number is the rescaling of the real library. -/
theorem rescale_ofReal (ω : ℝ) : hT.rescale ω = T.expRescale ω := by
  ext t x
  simp only [rescale_apply, smul_apply, expRescale_apply, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp, Complex.coe_smul]

/-- Multiplying by `exp (z t)` adds `z x` to the generator value at `x`. -/
theorem hasGeneratorAt_rescale (h : T.HasGeneratorAt x y) (z : ℂ) :
    (hT.rescale z).HasGeneratorAt x (y + z • x) := by
  have he : HasDerivAt (fun t : ℝ ↦ Complex.exp (z * (t : ℂ))) z 0 := by
    have h1 : HasDerivAt (fun t : ℝ ↦ z * (t : ℂ)) z 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul z
    simpa using h1.cexp
  have hd := he.hasDerivWithinAt.fun_smul h
  have hd' : HasDerivWithinAt (fun t : ℝ ↦ Complex.exp (z * (t : ℂ)) • T.realOrbit x t)
      (y + z • x) (Ici 0) 0 := by
    simpa [realOrbit, T.map_zero_apply] using hd
  refine hd'.congr_of_mem (fun t ht ↦ ?_) self_mem_Ici
  simp only [realOrbit, rescale_apply, smul_apply, Real.coe_toNNReal t ht]

/-- **The generator of the rescaled semigroup is `A + z`**, on the domain of `A`. -/
theorem hasGeneratorAt_rescale_iff (z : ℂ) :
    (hT.rescale z).HasGeneratorAt x y ↔ T.HasGeneratorAt x (y - z • x) := by
  constructor
  · intro h
    simpa [rescale_rescale, sub_eq_add_neg] using
      (hT.isComplexLinear_rescale z).hasGeneratorAt_rescale h (-z)
  · intro h
    simpa using hT.hasGeneratorAt_rescale h z

/-! ### Time integrals -/

variable [CompleteSpace X]

/-- The time integral `∫₀ᵗ T(s) x ds` of a complex-linear semigroup as a complex-linear bounded
operator. -/
def integral (t : NNReal) : X →L[ℂ] X :=
  (T.integratedOperator t).ofCommuteI fun x ↦ by
    rw [integratedOperator_apply, integratedOperator_apply, ← intervalIntegral.integral_smul]
    exact intervalIntegral.integral_congr fun s _ ↦ hT _ x

/-- `hT.integral t x` is `∫₀ᵗ T(s) x ds`. -/
theorem integral_apply (t : NNReal) (x : X) :
    hT.integral t x = ∫ s in (0 : ℝ)..(t : ℝ), T.realOrbit x s :=
  rfl

/-- The generator maps `∫₀ᵗ T(s) x ds` to `T(t) x - x`. -/
theorem integral_mem_graph (t : NNReal) (x : X) :
    (hT.integral t x, T t x - x) ∈ hT.generator.graph :=
  hT.mem_graph_generator_iff.mpr (T.hasGeneratorAt_integratedOperator t x)

/-- On the domain, `∫₀ᵗ T(s) A x ds = T(t) x - x`. -/
theorem integral_apply_of_mem_graph (t : NNReal) (h : (x, y) ∈ hT.generator.graph) :
    hT.integral t y = T t x - x :=
  (T.hasGeneratorAt_iff_integratedOperator x y).mp (hT.mem_graph_generator_iff.mp h) t

end IsComplexLinear

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
