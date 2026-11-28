/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.InnerProductSpace.Complexification.Operator
public import PDE.Analysis.Spectral.UnstableSplitting
public import PDE.Analysis.Evolution.Semigroup.Complex.Generator
public import PDE.Analysis.InnerProductSpace.Complexification.PartialOperator

/-!
# The complexification of a real semigroup, and conjugation by an isometry

Spectral theory needs complex scalars, while many semigroups of the library act on real
Hilbert spaces. On the complexification `H + iH` a real semigroup acts on the real and the
imaginary part separately. The result is a complex-linear semigroup with the same norms, its
generator is the complexification of the real generator, and real eigenvectors stay
eigenvectors. Some spaces of the library carry a Hilbert norm without an inner product and are
isometric to a Hilbert space; vector `L²` seen as the Sobolev space of order zero is one. A
semigroup moves along a linear isometry by conjugation, with the same norms and the conjugated
generator. This is the semigroup form of the conjugation that
`PDE.Analysis.Spectral.exists_unstable_splitting_of_linearIsometryEquiv` does for one operator.
The conjugation symmetry of the spectrum of the complexified generator is not proved here; for
Riesz projections it is `PDE.Analysis.Complexification.conjOp_rieszProjection_resolvent`.

## Main results

* `StronglyContinuousSemigroup.conj`: the conjugate `φ T(t) φ⁻¹` by a linear isometry
  equivalence `φ`. It has the same norms (`norm_conj_apply`), `φ` maps eigenvectors of `T` to
  eigenvectors of the conjugate (`conj_apply_eq_exp_smul`), and `HasGeneratorAt.conj` and
  `HasGeneratorAt.of_conj` transport the generator relation in both directions.
* `StronglyContinuousSemigroup.complexify`: the complexified semigroup of a semigroup on a real
  inner product space. It is complex linear (`isComplexLinear_complexify`), its operators are the
  complexifications of the real ones (`clm_complexify`), and they have the same norms
  (`norm_complexify_apply`).
* `StronglyContinuousSemigroup.generator_complexify`: the generator of the complexified
  semigroup is the complexification of the real generator, as partial operators;
  `mem_graph_generator_complexify_iff` says the same on real and imaginary parts.
* `StronglyContinuousSemigroup.mem_graph_generator_complexify`: if `T(t) u = e^{μt} u` for all
  `t ≥ 0`, then `u` is an eigenvector of the complex generator with eigenvalue `μ`.

## How it works

Each operator of the complexified semigroup is the complexification of a bounded real
operator, so it is complex linear and has the same norm. The real part, the imaginary part and
the embedding `H → H + iH` are bounded real-linear maps, so they carry orbits to orbits and
right derivatives at zero to right derivatives at zero; this gives continuity of the orbits and
identifies the generator. For a real eigenvector the orbit is `t ↦ e^{μt} u`, whose derivative
at zero is `μ u`. The converse for complex-linear semigroups is
`IsComplexLinear.apply_eq_exp_smul_of_mem_graph_smul`. Conjugation composes orbits with the
bounded operators `φ` and `φ⁻¹`, which transports the generator relation.
-/

@[expose] public noncomputable section

open Set PDE.Analysis PDE.Analysis.Complexification

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

section Conj

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The conjugate `φ T(t) φ⁻¹` of a strongly continuous semigroup by a linear isometry
equivalence `φ`. -/
def conj (T : StronglyContinuousSemigroup E) (φ : E ≃ₗᵢ[ℝ] F) :
    StronglyContinuousSemigroup F where
  toMonoidHom :=
    (MonoidHom.ofClass φ.toContinuousLinearEquiv.conjContinuousAlgEquiv).comp
      T.toMonoidHom
  continuous_toPointwise := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro x
    exact φ.continuous.comp (T.continuous_orbit (φ.symm x))

/-- The conjugated semigroup acts as `φ T(t) φ⁻¹`. -/
@[simp]
theorem conj_apply (T : StronglyContinuousSemigroup E) (φ : E ≃ₗᵢ[ℝ] F) (t : NNReal) (x : F) :
    T.conj φ t x = φ (T t (φ.symm x)) :=
  rfl

/-- The operators of the conjugated semigroup are the conjugates. -/
theorem conj_eq (T : StronglyContinuousSemigroup E) (φ : E ≃ₗᵢ[ℝ] F) (t : NNReal) :
    T.conj φ t = φ.toContinuousLinearEquiv.conjContinuousAlgEquiv (T t) :=
  rfl

/-- Conjugation by an isometry preserves the norms of the semigroup. -/
theorem norm_conj_apply (T : StronglyContinuousSemigroup E) (φ : E ≃ₗᵢ[ℝ] F) (t : NNReal) :
    ‖T.conj φ t‖ = ‖T t‖ := by
  rw [conj_eq, PDE.Analysis.Spectral.norm_conjContinuousAlgEquiv]

/-- An eigenvector of the semigroup is mapped to an eigenvector of the conjugated semigroup. -/
theorem conj_apply_eq_exp_smul {T : StronglyContinuousSemigroup E} (φ : E ≃ₗᵢ[ℝ] F) {u : E}
    {μ : ℝ} (h : ∀ t : NNReal, T t u = Real.exp (μ * t) • u) (t : NNReal) :
    T.conj φ t (φ u) = Real.exp (μ * t) • φ u := by
  rw [conj_apply, LinearIsometryEquiv.symm_apply_apply, h, map_smul]

/-- The orbits of the conjugated semigroup are the images of the orbits. -/
theorem realOrbit_conj (T : StronglyContinuousSemigroup E) (φ : E ≃ₗᵢ[ℝ] F) (x : E) (s : ℝ) :
    (T.conj φ).realOrbit (φ x) s = φ (T.realOrbit x s) := by
  rw [realOrbit, realOrbit, conj_apply, LinearIsometryEquiv.symm_apply_apply]

/-- **The generator of the conjugated semigroup**: if `x` is in the domain of the generator of
`T` with value `y`, then `φ x` is in the domain of the generator of `φ T φ⁻¹` with value
`φ y`. -/
theorem HasGeneratorAt.conj {T : StronglyContinuousSemigroup E} (φ : E ≃ₗᵢ[ℝ] F) {x y : E}
    (h : T.HasGeneratorAt x y) : (T.conj φ).HasGeneratorAt (φ x) (φ y) := by
  have horbit : (T.conj φ).realOrbit (φ x) = ⇑φ.toContinuousLinearEquiv ∘ T.realOrbit x :=
    funext fun s ↦ realOrbit_conj T φ x s
  rw [HasGeneratorAt, horbit]
  exact φ.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt 0 h

/-- **The generator of the conjugated semigroup, back**: if `z` is in the domain of the
generator of `φ T φ⁻¹` with value `w`, then `φ⁻¹ z` is in the domain of the generator of `T`
with value `φ⁻¹ w`. -/
theorem HasGeneratorAt.of_conj {T : StronglyContinuousSemigroup E} {φ : E ≃ₗᵢ[ℝ] F} {z w : F}
    (h : (T.conj φ).HasGeneratorAt z w) : T.HasGeneratorAt (φ.symm z) (φ.symm w) := by
  have horbit : T.realOrbit (φ.symm z) =
      ⇑φ.symm.toContinuousLinearEquiv ∘ (T.conj φ).realOrbit z := funext fun s ↦ by
    rw [Function.comp_apply, realOrbit, realOrbit, conj_apply]
    exact (LinearIsometryEquiv.symm_apply_apply φ _).symm
  rw [HasGeneratorAt, horbit]
  exact φ.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt
    0 h

end Conj

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The complexification of a strongly continuous semigroup on a real inner product space: on
`H + iH`, the operator `T(t)` acts on the real and the imaginary part. -/
def complexify (T : StronglyContinuousSemigroup H) :
    StronglyContinuousSemigroup (Complexification H) where
  toMonoidHom :=
    { toFun := fun t ↦ (Complexification.complexify (T t.toAdd)).restrictScalars ℝ
      map_one' := by
        ext z <;> simp
      map_mul' := fun s t ↦ by
        ext z <;> simp }
  continuous_toPointwise := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro z
    exact ((ofRealCLM.continuous.comp (T.continuous_orbit z.re)).add
      ((ofRealCLM.continuous.comp (T.continuous_orbit z.im)).const_smul Complex.I)).congr
        fun t ↦ ofReal_re_add_I_smul_ofReal_im (Complexification.complexify (T t) z)

/-- The complexified semigroup acts by the complexified operators. -/
@[simp]
theorem complexify_apply (T : StronglyContinuousSemigroup H) (t : NNReal)
    (z : Complexification H) : T.complexify t z = Complexification.complexify (T t) z :=
  rfl

/-- The complexified semigroup is complex linear. -/
theorem isComplexLinear_complexify (T : StronglyContinuousSemigroup H) :
    T.complexify.IsComplexLinear := fun t z ↦ by
  rw [complexify_apply, complexify_apply, map_smul]

/-- The complex-linear operators of the complexified semigroup are the complexifications of the
real ones. -/
theorem clm_complexify (T : StronglyContinuousSemigroup H) (t : NNReal) :
    (isComplexLinear_complexify T).clm t = Complexification.complexify (T t) :=
  rfl

/-- The complexified semigroup has the norms of the real one. -/
theorem norm_complexify_apply (T : StronglyContinuousSemigroup H) (t : NNReal) :
    ‖T.complexify t‖ = ‖T t‖ := by
  rw [← (isComplexLinear_complexify T).norm_clm, clm_complexify, norm_complexify]

/-- The orbits of the complexified semigroup: the real semigroup acts on the real and on the
imaginary part. -/
theorem realOrbit_complexify (T : StronglyContinuousSemigroup H) (z : Complexification H)
    (s : ℝ) : T.complexify.realOrbit z s =
      ofRealCLM (T.realOrbit z.re s) + Complex.I • ofRealCLM (T.realOrbit z.im s) := by
  rw [realOrbit, complexify_apply, ofRealCLM_apply, ofRealCLM_apply,
    ← ofReal_re_add_I_smul_ofReal_im (Complexification.complexify (T s.toNNReal) z),
    re_complexify, im_complexify]
  rfl

/-- **The generator of the complexified semigroup acts on real and imaginary parts**: `(z, w)`
is in the graph of the generator of the complexification of `T` exactly when `z.re` and `z.im`
are in the domain of the generator of `T`, with values `w.re` and `w.im`. -/
theorem mem_graph_generator_complexify_iff {T : StronglyContinuousSemigroup H}
    {z w : Complexification H} :
    (z, w) ∈ (isComplexLinear_complexify T).generator.graph ↔
      T.HasGeneratorAt z.re w.re ∧ T.HasGeneratorAt z.im w.im := by
  rw [IsComplexLinear.mem_graph_generator_iff]
  have horbit : T.complexify.realOrbit z = fun s ↦
      ofRealCLM (T.realOrbit z.re s) + Complex.I • ofRealCLM (T.realOrbit z.im s) :=
    funext fun s ↦ realOrbit_complexify T z s
  constructor
  · intro h
    have hre : T.realOrbit z.re = ⇑(reCLM : Complexification H →L[ℝ] H) ∘
        T.complexify.realOrbit z := funext fun s ↦ by
      rw [Function.comp_apply, horbit]
      simp
    have him : T.realOrbit z.im = ⇑(imCLM : Complexification H →L[ℝ] H) ∘
        T.complexify.realOrbit z := funext fun s ↦ by
      rw [Function.comp_apply, horbit]
      simp
    refine ⟨?_, ?_⟩
    · rw [HasGeneratorAt, hre]
      exact (reCLM : Complexification H →L[ℝ] H).hasFDerivAt.comp_hasDerivWithinAt 0 h
    · rw [HasGeneratorAt, him]
      exact (imCLM : Complexification H →L[ℝ] H).hasFDerivAt.comp_hasDerivWithinAt 0 h
  · rintro ⟨hre, him⟩
    have h1 := (ofRealCLM : H →L[ℝ] Complexification H).hasFDerivAt.comp_hasDerivWithinAt 0 hre
    have h2 := ((ofRealCLM : H →L[ℝ] Complexification H).hasFDerivAt.comp_hasDerivWithinAt 0
      him).const_smul Complex.I
    have h3 := h1.add h2
    rw [HasGeneratorAt, horbit, ← ofReal_re_add_I_smul_ofReal_im w]
    exact h3

/-- The real part of an orbit of the complexified semigroup is the orbit of the real part. -/
theorem re_realOrbit_complexify (T : StronglyContinuousSemigroup H) (z : Complexification H)
    (s : ℝ) : (T.complexify.realOrbit z s).re = T.realOrbit z.re s :=
  rfl

/-- The imaginary part of an orbit of the complexified semigroup is the orbit of the imaginary
part. -/
theorem im_realOrbit_complexify (T : StronglyContinuousSemigroup H) (z : Complexification H)
    (s : ℝ) : (T.complexify.realOrbit z s).im = T.realOrbit z.im s :=
  rfl

/-- **The generator of the complexified semigroup is the complexified generator**, as partial
operators: the same domain, real and imaginary parts in the domain of the real generator, and
the same values. -/
theorem generator_complexify (T : StronglyContinuousSemigroup H) :
    (isComplexLinear_complexify T).generator = T.generatorPMap.complexify := by
  refine LinearPMap.eq_of_eq_graph ?_
  ext ⟨z, w⟩
  rw [mem_graph_generator_complexify_iff, LinearPMap.mem_graph_complexify_iff,
    T.hasGeneratorAt_iff_mem_generatorPMap_graph, T.hasGeneratorAt_iff_mem_generatorPMap_graph]

/-- **A real eigenvector of the semigroup is an eigenvector of the complex generator.** If
`T(t) u = e^{μt} u` for all `t ≥ 0`, then `u`, as an element of the complexification, lies in
the domain of the generator of the complexified semigroup, with value `μ u`. The orbit is
`t ↦ e^{μt} u`, and its derivative at zero is `μ u`. -/
theorem mem_graph_generator_complexify {T : StronglyContinuousSemigroup H} {u : H} {μ : ℝ}
    (h : ∀ t : NNReal, T t u = Real.exp (μ * t) • u) :
    (ofReal u, (μ : ℂ) • ofReal u) ∈ (isComplexLinear_complexify T).generator.graph := by
  rw [IsComplexLinear.mem_graph_generator_iff, HasGeneratorAt]
  have hd : HasDerivAt (fun s : ℝ ↦ Real.exp (μ * s) • (ofReal u : Complexification H))
      ((Real.exp (μ * 0) * (μ * 1)) • (ofReal u : Complexification H)) 0 :=
    ((Real.hasDerivAt_exp _).comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul μ)).smul_const _
  have hval : (Real.exp (μ * 0) * (μ * 1)) • (ofReal u : Complexification H) =
      (μ : ℂ) • ofReal u := by
    rw [mul_zero, Real.exp_zero, one_mul, mul_one, Complex.coe_smul]
  rw [hval] at hd
  have horbit (s : ℝ) (hs : s ∈ Ici (0 : ℝ)) :
      T.complexify.realOrbit (ofReal u) s = Real.exp (μ * s) • ofReal u := by
    rw [realOrbit, complexify_apply, complexify_ofReal, h, ofReal_smul, Real.coe_toNNReal s hs]
  exact hd.hasDerivWithinAt.congr horbit (horbit 0 self_mem_Ici)

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
