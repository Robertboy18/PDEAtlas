/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Basic
public import Mathlib.Topology.Algebra.Module.LinearPMap
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import CAS.ExactTactic

/-!
# Infinitesimal generators of strongly continuous semigroups

For a strongly continuous semigroup `T`, its infinitesimal generator is the
strong right derivative of the orbit at time zero,

`A x = d/dt|₀⁺ T(t)x`.

The derivative need not exist for every vector. Its natural domain and values
are given directly by Mathlib's `LinearPMap`. The semigroup preserves this domain and
commutes with the generator. Orbits starting in the generator domain are
continuously differentiable at positive real times.

These are the definitions (8)-(9) of Evans §7.4.1, his Theorem 1, and the closedness half of
his Theorem 2. No contractivity is assumed; completeness is used to construct the bounded
integrated-orbit operator and to prove the integral characterization of the generator,
positive-time orbit regularity, and closedness.

## How it works

Evans states these results for contraction semigroups, and his proof of Theorem 1 uses
`‖S(t - h)‖ ≤ 1` to control the left difference quotient. We avoid the left quotient. The
semigroup law gives the right derivative `T(t)(Ax)` at every time
(`HasGeneratorAt.hasDerivWithinAt_realOrbit`), and Mathlib's one-sided fundamental theorem of
calculus, `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`, turns it into the integral
identity `T(t)x - x = ∫₀ᵗ T(s)(Ax) ds` (`hasGeneratorAt_iff_integratedOperator`). The two-sided
derivative at positive times then comes from `Continuous.integral_hasStrictDerivAt`. The same
identity gives closedness (`isClosed_generatorPMap`) exactly as in step 3 of Evans's proof of
Theorem 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.1, definitions (8)-(9), Theorem 1 and Theorem 2 with
  their proofs, pp. 435-437. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Set Topology

namespace PDE.Analysis.Evolution

namespace StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The semigroup orbit extended to real time by truncating negative time to zero. -/
def realOrbit (T : StronglyContinuousSemigroup E) (x : E) (t : ℝ) : E :=
  T t.toNNReal x

/-- On nonnegative times, the real-time orbit agrees with the original semigroup orbit. -/
@[simp]
theorem realOrbit_coe (T : StronglyContinuousSemigroup E) (x : E) (t : NNReal) :
    T.realOrbit x t = T t x := by
  simp [realOrbit]

/-- Every real-time orbit starts at its initial vector. -/
@[simp]
theorem realOrbit_zero (T : StronglyContinuousSemigroup E) (x : E) :
    T.realOrbit x 0 = x := by
  simp [realOrbit]

/-- The real-time extension of a strongly continuous orbit is continuous. -/
theorem continuous_realOrbit (T : StronglyContinuousSemigroup E) (x : E) :
    Continuous (T.realOrbit x) :=
  (T.continuous_orbit x).comp continuous_real_toNNReal

/-- The time integral of the semigroup orbit over `[0, t]`, as a bounded linear operator. -/
def integratedOperator [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (t : NNReal) : E →L[ℝ] E :=
  let integralLinearMap : E →ₗ[ℝ] E :=
    { toFun := fun x ↦ ∫ s in (0 : ℝ)..(t : ℝ), T.realOrbit x s
      map_add' := by
        intro x y
        rw [← intervalIntegral.integral_add
          ((T.continuous_realOrbit x).intervalIntegrable _ _)
          ((T.continuous_realOrbit y).intervalIntegrable _ _)]
        apply intervalIntegral.integral_congr
        intro s _
        simp [realOrbit]
      map_smul' := by
        intro c x
        rw [← intervalIntegral.integral_smul]
        apply intervalIntegral.integral_congr
        intro s _
        simp [realOrbit] }
  integralLinearMap.mkContinuousOfExistsBound <| by
    obtain ⟨C, _, hC⟩ := T.exists_norm_le_on_Icc t
    refine ⟨C * (t : ℝ), fun x ↦ ?_⟩
    change ‖∫ s in (0 : ℝ)..(t : ℝ), T.realOrbit x s‖ ≤
      (C * (t : ℝ)) * ‖x‖
    calc
      ‖∫ s in (0 : ℝ)..(t : ℝ), T.realOrbit x s‖ ≤
          (C * ‖x‖) * |(t : ℝ) - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s hs
        rw [Set.uIoc_of_le t.coe_nonneg] at hs
        have hs0 : 0 ≤ s := hs.1.le
        have hst : s.toNNReal ≤ t := by
          apply NNReal.coe_le_coe.mp
          simpa only [Real.coe_toNNReal _ hs0] using hs.2
        exact (T s.toNNReal).le_opNorm x |>.trans <|
          mul_le_mul_of_nonneg_right (hC s.toNNReal ⟨bot_le, hst⟩) (norm_nonneg x)
      _ = (C * (t : ℝ)) * ‖x‖ := by
        rw [abs_of_nonneg]
        · ring
        · exact sub_nonneg.mpr t.coe_nonneg

/-- Evaluating the integrated operator gives the Bochner interval integral of the orbit. -/
@[simp]
theorem integratedOperator_apply [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (t : NNReal) (x : E) :
    T.integratedOperator t x =
      ∫ s in (0 : ℝ)..(t : ℝ), T.realOrbit x s :=
  rfl

/-- `Ax` is the infinitesimal generator applied to `x` when the real-time
orbit has right derivative `Ax` at zero. -/
def HasGeneratorAt (T : StronglyContinuousSemigroup E) (x Ax : E) : Prop :=
  HasDerivWithinAt (T.realOrbit x) Ax (Ici 0) 0

namespace HasGeneratorAt

variable {T : StronglyContinuousSemigroup E} {x y Ax Ay : E}

/-- A generator value at a fixed vector is unique. -/
theorem unique (hx : T.HasGeneratorAt x Ax) (hy : T.HasGeneratorAt x Ay) :
    Ax = Ay := by
  exact UniqueDiffWithinAt.eq_deriv (Ici 0) (uniqueDiffWithinAt_Ici 0) hx hy

/-- The generator relation contains the zero vector with value zero. -/
theorem zero (T : StronglyContinuousSemigroup E) :
    T.HasGeneratorAt 0 0 := by
  have h :=
    hasDerivWithinAt_const (x := (0 : ℝ)) (s := Ici 0) (c := (0 : E))
  exact h.congr
    (fun s _ ↦ by simp [realOrbit])
    (by simp [realOrbit])

/-- Generator derivatives are closed under addition. -/
theorem add (hx : T.HasGeneratorAt x Ax) (hy : T.HasGeneratorAt y Ay) :
    T.HasGeneratorAt (x + y) (Ax + Ay) := by
  exact (HasDerivWithinAt.add hx hy).congr
    (fun s _ ↦ by simp [realOrbit, Pi.add_apply])
    (by simp [realOrbit, Pi.add_apply])

/-- Generator derivatives are closed under real scalar multiplication. -/
theorem smul (c : ℝ) (hx : T.HasGeneratorAt x Ax) :
    T.HasGeneratorAt (c • x) (c • Ax) := by
  exact (HasDerivWithinAt.const_smul c hx).congr
    (fun s _ ↦ by simp [realOrbit, Pi.smul_apply])
    (by simp [realOrbit, Pi.smul_apply])

/-- Applying a time-evolution operator transports a generator derivative. -/
theorem map (hx : T.HasGeneratorAt x Ax) (t : NNReal) :
    T.HasGeneratorAt (T t x) (T t Ax) := by
  have hcomp :
      HasDerivWithinAt
        ((T t) ∘ T.realOrbit x) (T t Ax) (Ici 0) 0 :=
    (T t).hasFDerivAt.comp_hasDerivWithinAt 0 hx
  exact hcomp.congr
    (fun s _ ↦ by
      simpa [Function.comp_apply, realOrbit] using
        T.map_apply_comm s.toNNReal t x)
    (by simp [Function.comp_apply, realOrbit])

/-- A generator derivative is the right derivative of the orbit at every
nonnegative time. -/
theorem hasDerivWithinAt_realOrbit
    (hx : T.HasGeneratorAt x Ax) (t : NNReal) :
    HasDerivWithinAt (T.realOrbit x) (T t Ax)
      (Ici (t : ℝ)) (t : ℝ) := by
  have hshift :
      HasDerivWithinAt (fun s : ℝ ↦ s - (t : ℝ)) 1
        (Ici (t : ℝ)) (t : ℝ) := by
    cas
  have hmaps :
      MapsTo (fun s : ℝ ↦ s - (t : ℝ)) (Ici (t : ℝ)) (Ici 0) := by
    intro s hs
    change (t : ℝ) ≤ s at hs
    exact sub_nonneg.mpr hs
  have hcomp :
      HasDerivWithinAt
        (fun s : ℝ ↦ T.realOrbit (T t x) (s - (t : ℝ)))
        (T t Ax) (Ici (t : ℝ)) (t : ℝ) := by
    have hout :
        HasFDerivWithinAt (T.realOrbit (T t x))
          (ContinuousLinearMap.toSpanSingleton ℝ (T t Ax))
          (Ici 0) ((t : ℝ) - (t : ℝ)) := by
      simpa only [sub_self] using (hx.map t).hasFDerivWithinAt
    have h :=
      (hout.comp (f := fun s : ℝ ↦ s - (t : ℝ)) (t : ℝ)
        hshift.hasFDerivWithinAt hmaps).hasDerivWithinAt
    simpa [Function.comp_def] using h
  have horbit (s : ℝ) (hs : s ∈ Ici (t : ℝ)) :
      T.realOrbit x s =
        T.realOrbit (T t x) (s - (t : ℝ)) := by
    change (t : ℝ) ≤ s at hs
    have hs0 : 0 ≤ s := t.coe_nonneg.trans hs
    simp only [realOrbit]
    rw [← T.map_add_apply]
    have htime : s.toNNReal = (s - (t : ℝ)).toNNReal + t := by
      apply NNReal.eq
      rw [NNReal.coe_add, Real.coe_toNNReal _ (sub_nonneg.mpr hs),
        Real.coe_toNNReal _ hs0]
      ring
    rw [htime]
  exact hcomp.congr horbit (horbit (t : ℝ) (by simp))

end HasGeneratorAt

/-- A vector has generator value `Ax` exactly when integrating the orbit of `Ax`
recovers every semigroup increment of the vector. -/
theorem hasGeneratorAt_iff_integratedOperator [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (x Ax : E) :
    T.HasGeneratorAt x Ax ↔
      ∀ t : NNReal, T.integratedOperator t Ax = T t x - x := by
  constructor
  · intro hx t
    rw [integratedOperator_apply]
    have hderiv (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) (t : ℝ)) :
        HasDerivWithinAt (T.realOrbit x) (T.realOrbit Ax s) (Ioi s) s := by
      have hs0 : 0 ≤ s := hs.1.le
      have hcoe : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs0
      simpa only [realOrbit, hcoe] using
        (hx.hasDerivWithinAt_realOrbit s.toNNReal).mono Ioi_subset_Ici_self
    simpa using intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      t.coe_nonneg (T.continuous_realOrbit x).continuousOn hderiv
      ((T.continuous_realOrbit Ax).intervalIntegrable 0 (t : ℝ))
  · intro h
    have hprimitive :
        HasDerivAt
          (fun s : ℝ ↦
            (∫ r in (0 : ℝ)..s, T.realOrbit Ax r) + x)
          Ax 0 := by
      simpa using
        ((T.continuous_realOrbit Ax).integral_hasStrictDerivAt 0 0).hasDerivAt.add_const x
    exact hprimitive.hasDerivWithinAt.congr_of_mem
      (fun s hs ↦ by
        have hs0 : 0 ≤ s := hs
        have hcoe : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs0
        rw [← hcoe, realOrbit_coe]
        calc
          T s.toNNReal x = (T s.toNNReal x - x) + x := (sub_add_cancel _ _).symm
          _ = T.integratedOperator s.toNNReal Ax + x := by rw [h]
          _ = (∫ r in (0 : ℝ)..(s.toNNReal : ℝ), T.realOrbit Ax r) + x := by
            rw [integratedOperator_apply])
      self_mem_Ici

namespace HasGeneratorAt

variable {T : StronglyContinuousSemigroup E} {x Ax : E}

/-- A generator-domain orbit has an ordinary two-sided derivative at every
positive time. This is Evans §7.4.1, Theorem 1(iii)-(iv). -/
theorem hasDerivAt_realOrbit [CompleteSpace E]
    (hx : T.HasGeneratorAt x Ax) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (T.realOrbit x) (T.realOrbit Ax t) t := by
  have hprimitive :
      HasDerivAt
        (fun s : ℝ ↦ (∫ r in (0 : ℝ)..s, T.realOrbit Ax r) + x)
        (T.realOrbit Ax t) t :=
    ((T.continuous_realOrbit Ax).integral_hasStrictDerivAt 0 t).hasDerivAt.add_const x
  apply hprimitive.congr_of_eventuallyEq
  filter_upwards [Ici_mem_nhds ht] with s hs
  have hcoe : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs
  rw [← hcoe, realOrbit_coe]
  calc
    T s.toNNReal x = (T s.toNNReal x - x) + x := (sub_add_cancel _ _).symm
    _ = T.integratedOperator s.toNNReal Ax + x := by
      rw [(T.hasGeneratorAt_iff_integratedOperator x Ax).1 hx]
    _ = (∫ r in (0 : ℝ)..(s.toNNReal : ℝ), T.realOrbit Ax r) + x := by
      rw [integratedOperator_apply]

end HasGeneratorAt

/-- The infinitesimal generator on its natural domain, represented by
Mathlib's canonical partial linear-map structure. -/
def generatorPMap (T : StronglyContinuousSemigroup E) : E →ₗ.[ℝ] E :=
  let domain : Submodule ℝ E :=
    { carrier := {x | ∃ Ax, T.HasGeneratorAt x Ax}
      zero_mem' := ⟨0, HasGeneratorAt.zero T⟩
      add_mem' := by
        rintro x y ⟨Ax, hx⟩ ⟨Ay, hy⟩
        exact ⟨Ax + Ay, hx.add hy⟩
      smul_mem' := by
        rintro c x ⟨Ax, hx⟩
        exact ⟨c • Ax, hx.smul c⟩ }
  { domain := domain
    toFun :=
      { toFun := fun x ↦ Classical.choose x.property
        map_add' := by
          intro x y
          apply HasGeneratorAt.unique
          · exact Classical.choose_spec (x + y).property
          · exact
              (Classical.choose_spec x.property).add
                (Classical.choose_spec y.property)
        map_smul' := by
          intro c x
          apply HasGeneratorAt.unique
          · exact Classical.choose_spec (c • x).property
          · exact (Classical.choose_spec x.property).smul c } }

/-- The partial generator map realizes the generator relation on its domain. -/
theorem hasGeneratorAt_generatorPMap
    (T : StronglyContinuousSemigroup E) (x : T.generatorPMap.domain) :
    T.HasGeneratorAt x (T.generatorPMap x) :=
  Classical.choose_spec x.property

/-- The derivative definition of the generator agrees with its partial linear-map graph. -/
theorem hasGeneratorAt_iff_mem_generatorPMap_graph
    (T : StronglyContinuousSemigroup E) (x Ax : E) :
    T.HasGeneratorAt x Ax ↔ (x, Ax) ∈ T.generatorPMap.graph := by
  constructor
  · intro hx
    let y : T.generatorPMap.domain := ⟨x, ⟨Ax, hx⟩⟩
    refine (LinearPMap.mem_graph_iff T.generatorPMap).2 ⟨y, rfl, ?_⟩
    exact (T.hasGeneratorAt_generatorPMap y).unique hx
  · intro hx
    obtain ⟨y, hy, hAy⟩ := (LinearPMap.mem_graph_iff T.generatorPMap).1 hx
    simpa only [hy, hAy] using T.hasGeneratorAt_generatorPMap y

/-- Integrating the generator along the semigroup recovers the orbit increment. -/
theorem integratedOperator_generatorPMap [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (t : NNReal)
    (x : T.generatorPMap.domain) :
    T.integratedOperator t (T.generatorPMap x) = T t x - x :=
  (T.hasGeneratorAt_iff_integratedOperator x (T.generatorPMap x)).1
    (T.hasGeneratorAt_generatorPMap x) t

/-- The infinitesimal generator of a strongly continuous semigroup is closed. -/
theorem isClosed_generatorPMap [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) :
    T.generatorPMap.IsClosed := by
  rw [LinearPMap.IsClosed]
  refine IsSeqClosed.isClosed fun u p hu hup ↦ ?_
  have hidentity (t : NNReal) :
      T.integratedOperator t p.2 = T t p.1 - p.1 := by
    have hleft :
        Tendsto (fun n ↦ T.integratedOperator t (u n).2) atTop
          (𝓝 (T.integratedOperator t p.2)) :=
      (((T.integratedOperator t).continuous.comp continuous_snd).tendsto p).comp hup
    have hright :
        Tendsto (fun n ↦ T t (u n).1 - (u n).1) atTop
          (𝓝 (T t p.1 - p.1)) :=
      ((((T t).continuous.comp continuous_fst).sub continuous_fst).tendsto p).comp hup
    have hpointwise (n : ℕ) :
        T.integratedOperator t (u n).2 =
          T t (u n).1 - (u n).1 := by
      obtain ⟨xn, hxn, hAxn⟩ :=
        (LinearPMap.mem_graph_iff T.generatorPMap).1 (hu n)
      rw [← hAxn, T.integratedOperator_generatorPMap, hxn]
    exact tendsto_nhds_unique
      (hleft.congr' (Filter.Eventually.of_forall hpointwise)) hright
  have hgenerator : T.HasGeneratorAt p.1 p.2 :=
    (T.hasGeneratorAt_iff_integratedOperator p.1 p.2).2 hidentity
  let x : T.generatorPMap.domain := ⟨p.1, ⟨p.2, hgenerator⟩⟩
  refine (LinearPMap.mem_graph_iff T.generatorPMap).2 ⟨x, rfl, ?_⟩
  exact HasGeneratorAt.unique (T.hasGeneratorAt_generatorPMap x) hgenerator

/-- The semigroup preserves the natural domain of its infinitesimal generator. -/
theorem map_mem_generatorPMap_domain
    (T : StronglyContinuousSemigroup E) (t : NNReal)
    (x : T.generatorPMap.domain) :
    T t x ∈ T.generatorPMap.domain :=
  ⟨T t (T.generatorPMap x), (T.hasGeneratorAt_generatorPMap x).map t⟩

/-- The restriction of a semigroup operator to the invariant generator domain. -/
def generatorDomainMap
    (T : StronglyContinuousSemigroup E) (t : NNReal) :
    T.generatorPMap.domain →L[ℝ] T.generatorPMap.domain :=
  (T t).restrict fun x hx ↦
    T.map_mem_generatorPMap_domain t ⟨x, hx⟩

/-- The restricted domain map has the same underlying value as the ambient semigroup map. -/
@[simp]
theorem generatorDomainMap_apply
    (T : StronglyContinuousSemigroup E) (t : NNReal)
    (x : T.generatorPMap.domain) :
    T.generatorDomainMap t x = T t x :=
  rfl

/-- The restricted semigroup map at time zero is the identity on the generator domain. -/
@[simp]
theorem generatorDomainMap_zero (T : StronglyContinuousSemigroup E) :
    T.generatorDomainMap 0 =
      ContinuousLinearMap.id ℝ T.generatorPMap.domain := by
  ext x
  exact T.map_zero_apply x

/-- Restricted generator-domain maps satisfy the semigroup addition law. -/
theorem generatorDomainMap_add
    (T : StronglyContinuousSemigroup E) (s t : NNReal) :
    T.generatorDomainMap (s + t) =
      (T.generatorDomainMap s).comp (T.generatorDomainMap t) := by
  ext x
  exact T.map_add_apply s t x

/-- The semigroup restricted to its invariant generator domain, equipped with
the norm inherited from the ambient space. -/
def generatorDomainSemigroup
    (T : StronglyContinuousSemigroup E) :
    StronglyContinuousSemigroup T.generatorPMap.domain where
  toMonoidHom :=
    { toFun := fun t ↦ T.generatorDomainMap t.toAdd
      map_one' := T.generatorDomainMap_zero
      map_mul' := by
        intro s t
        simpa only [toAdd_mul, ContinuousLinearMap.mul_def] using
          T.generatorDomainMap_add s.toAdd t.toAdd }
  continuous_toPointwise :=
    PointwiseConvergenceCLM.continuous_of_continuous_eval fun x ↦
      continuous_induced_rng.mpr (T.continuous_orbit x)

/-- The generator-domain semigroup evaluates through the restricted domain map. -/
@[simp]
theorem generatorDomainSemigroup_apply
    (T : StronglyContinuousSemigroup E) (t : NNReal)
    (x : T.generatorPMap.domain) :
    T.generatorDomainSemigroup t x = T.generatorDomainMap t x :=
  rfl

/-- The semigroup commutes with its infinitesimal generator on the natural domain. -/
theorem generatorPMap_generatorDomainMap
    (T : StronglyContinuousSemigroup E) (t : NNReal)
    (x : T.generatorPMap.domain) :
    T.generatorPMap (T.generatorDomainMap t x) =
      T t (T.generatorPMap x) := by
  apply HasGeneratorAt.unique
  · exact T.hasGeneratorAt_generatorPMap (T.generatorDomainMap t x)
  · exact (T.hasGeneratorAt_generatorPMap x).map t

/-- An orbit starting in the generator domain solves the abstract homogeneous
Cauchy problem, with the derivative expressed by Mathlib's predicate. -/
theorem hasDerivWithinAt_realOrbit_generatorPMap
    (T : StronglyContinuousSemigroup E) (t : NNReal)
    (x : T.generatorPMap.domain) :
    HasDerivWithinAt (T.realOrbit x)
      (T.generatorPMap (T.generatorDomainMap t x))
      (Ici (t : ℝ)) (t : ℝ) := by
  rw [T.generatorPMap_generatorDomainMap]
  exact (T.hasGeneratorAt_generatorPMap x).hasDerivWithinAt_realOrbit t

/-- At every positive real time, an orbit from the generator domain has the
two-sided derivative `T(t) (A x)`. -/
theorem hasDerivAt_realOrbit_generatorPMap [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) {t : ℝ} (ht : 0 < t)
    (x : T.generatorPMap.domain) :
    HasDerivAt (T.realOrbit x) (T.realOrbit (T.generatorPMap x) t) t :=
  (T.hasGeneratorAt_generatorPMap x).hasDerivAt_realOrbit ht

/-- An orbit from the generator domain is `C^1` on positive real time, as in the remark after
Evans §7.4.1, Theorem 1. -/
theorem contDiffOn_realOrbit_generatorPMap [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (x : T.generatorPMap.domain) :
    ContDiffOn ℝ 1 (T.realOrbit x) (Ioi 0) := by
  rw [contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn]
  refine ⟨fun t ht ↦ ?_, ?_⟩
  · exact
      (T.hasDerivAt_realOrbit_generatorPMap ht x).differentiableAt.differentiableWithinAt
  · exact (T.continuous_realOrbit (T.generatorPMap x)).continuousOn.congr fun t ht ↦
      (T.hasDerivAt_realOrbit_generatorPMap ht x).hasDerivWithinAt.derivWithin
        (isOpen_Ioi.uniqueDiffOn t ht)

/-- Along an orbit starting in the generator domain, the generator value
depends continuously on time. -/
theorem continuous_generatorPMap_orbit
    (T : StronglyContinuousSemigroup E) (x : T.generatorPMap.domain) :
    Continuous fun t ↦ T.generatorPMap (T.generatorDomainMap t x) := by
  have hcont : Continuous fun t ↦ T t (T.generatorPMap x) :=
    T.continuous_orbit (T.generatorPMap x)
  exact hcont.congr fun t ↦ (T.generatorPMap_generatorDomainMap t x).symm

/-- Every vector has generator value zero for the identity semigroup. -/
theorem identity_hasGeneratorAt (x : E) :
    (identity (E := E)).HasGeneratorAt x 0 := by
  have h :=
    hasDerivWithinAt_const (x := (0 : ℝ)) (s := Ici 0) (c := x)
  exact h.congr
    (fun s _ ↦ by simp [realOrbit])
    (by simp [realOrbit])

/-- The identity semigroup has the full ambient space as generator domain. -/
@[simp]
theorem identity_generatorPMap_domain :
    (identity (E := E)).generatorPMap.domain = ⊤ := by
  ext x
  simp only [Submodule.mem_top, iff_true]
  exact ⟨0, identity_hasGeneratorAt x⟩

/-- The infinitesimal generator of the identity semigroup vanishes. -/
@[simp]
theorem identity_generatorPMap
    (x : (identity (E := E)).generatorPMap.domain) :
    (identity (E := E)).generatorPMap x = 0 := by
  apply HasGeneratorAt.unique
  · exact (identity (E := E)).hasGeneratorAt_generatorPMap x
  · exact identity_hasGeneratorAt (E := E) x

end StronglyContinuousSemigroup

end PDE.Analysis.Evolution
