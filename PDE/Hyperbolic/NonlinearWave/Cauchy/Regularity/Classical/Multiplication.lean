/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Composition

/-!
# Bounded multiplication at the classical Sobolev level

Polarization of the higher weak chain rule constructs products. Their canonical
representatives identify the algebraic operations and their closed graphs.
Applying the linear closed graph theorem twice then gives a bounded bilinear
multiplication on Hᵏ for `n < 2(k - 1)`. No continuity of a nonlinear map is
inferred merely from a closed graph.
-/

@[expose] public noncomputable section

open Filter SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n]

/-- The Sobolev product obtained by polarizing the square composition. -/
def higherProduct (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (u v : W^{k,2}(ℝ^n)) : W^{k,2}(ℝ^n) :=
  (1 / 4 : ℝ) • (higherComposition hk (contDiff_id.pow 2) (by simp) (u + v) -
    higherComposition hk (contDiff_id.pow 2) (by simp) (u - v))

/-- The product has the expected value at every spatial point. -/
theorem classicalRepresentative_higherProduct
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (u v : W^{k,2}(ℝ^n)) (x : ℝ^n) :
    classicalRepresentativeCLM hk (higherProduct hk u v) x =
      classicalRepresentativeCLM hk u x * classicalRepresentativeCLM hk v x := by
  simp only [higherProduct, map_smul, map_sub, BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.sub_apply, smul_eq_mul, classicalRepresentative_higherComposition,
    map_add, BoundedContinuousFunction.add_apply, id_eq]
  ring

/-- The product distributes over addition in its second variable. -/
theorem higherProduct_add_right (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (u v w : W^{k,2}(ℝ^n)) :
    higherProduct hk u (v + w) = higherProduct hk u v + higherProduct hk u w := by
  apply classicalRepresentativeCLM_injective hk
  ext x
  simp only [map_add, BoundedContinuousFunction.add_apply, classicalRepresentative_higherProduct]
  ring

/-- The product respects scalar multiplication in its second variable. -/
theorem higherProduct_smul_right (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (u v : W^{k,2}(ℝ^n)) (c : ℝ) :
    higherProduct hk u (c • v) = c • higherProduct hk u v := by
  apply classicalRepresentativeCLM_injective hk
  ext x
  simp only [map_smul, BoundedContinuousFunction.smul_apply, smul_eq_mul,
    classicalRepresentative_higherProduct]
  ring

/-- The algebraic multiplier associated to a Sobolev function. -/
def higherMultiplierLM (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (u : W^{k,2}(ℝ^n)) : W^{k,2}(ℝ^n) →ₗ[ℝ] W^{k,2}(ℝ^n) where
  toFun := higherProduct hk u
  map_add' := higherProduct_add_right hk u
  map_smul' := fun c v ↦ higherProduct_smul_right hk u v c

/-- Convergence of the input and product identifies the limiting product. -/
theorem higherMultiplierLM_seqClosedGraph (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (u : W^{k,2}(ℝ^n))
    (v : ℕ → W^{k,2}(ℝ^n)) (V W : W^{k,2}(ℝ^n)) (hv : Tendsto v atTop (𝓝 V))
    (hW : Tendsto (higherMultiplierLM hk u ∘ v) atTop (𝓝 W)) :
    W = higherMultiplierLM hk u V := by
  apply classicalRepresentativeCLM_injective hk
  ext x
  let E := (BoundedContinuousFunction.evalCLM ℝ x).comp (classicalRepresentativeCLM hk)
  have hleft := (E.continuous.tendsto W).comp hW
  have hright := ((E.continuous.tendsto V).comp hv).const_mul (classicalRepresentativeCLM hk u x)
  change classicalRepresentativeCLM hk W x = classicalRepresentativeCLM hk (higherProduct hk u V) x
  rw [classicalRepresentative_higherProduct]
  exact tendsto_nhds_unique hleft
    (hright.congr fun j ↦ (classicalRepresentative_higherProduct hk u (v j) x).symm)

/-- Multiplication by a fixed Sobolev element is a bounded linear map. -/
def higherMultiplierCLM (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (u : W^{k,2}(ℝ^n)) : W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n) :=
  ContinuousLinearMap.ofSeqClosedGraph (g := higherMultiplierLM hk u)
    (higherMultiplierLM_seqClosedGraph hk u)

/-- The bounded multiplier is pointwise multiplication on representatives. -/
theorem classicalRepresentative_higherMultiplierCLM
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (u v : W^{k,2}(ℝ^n)) (x : ℝ^n) :
    classicalRepresentativeCLM hk (higherMultiplierCLM hk u v) x =
      classicalRepresentativeCLM hk u x * classicalRepresentativeCLM hk v x :=
  classicalRepresentative_higherProduct hk u v x

/-- The multiplier depends linearly on its coefficient. -/
def higherProductLM (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) :
    W^{k,2}(ℝ^n) →ₗ[ℝ] W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n) where
  toFun := higherMultiplierCLM hk
  map_add' := by
    intro u v
    refine ContinuousLinearMap.ext fun w ↦ ?_
    apply classicalRepresentativeCLM_injective hk
    ext x
    simp only [add_apply, map_add,
      BoundedContinuousFunction.add_apply, classicalRepresentative_higherMultiplierCLM]
    ring
  map_smul' := by
    intro c u
    refine ContinuousLinearMap.ext fun v ↦ ?_
    apply classicalRepresentativeCLM_injective hk
    ext x
    simp only [smul_apply, map_smul, RingHom.id_apply,
      BoundedContinuousFunction.smul_apply, smul_eq_mul,
      classicalRepresentative_higherMultiplierCLM]
    ring

/-- Convergence in operator norm identifies the limiting multiplier. -/
theorem higherProductLM_seqClosedGraph (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (u : ℕ → W^{k,2}(ℝ^n))
    (U : W^{k,2}(ℝ^n)) (A : W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n)) (hu : Tendsto u atTop (𝓝 U))
    (hA : Tendsto (higherProductLM hk ∘ u) atTop (𝓝 A)) :
    A = higherProductLM hk U := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  apply classicalRepresentativeCLM_injective hk
  ext x
  let E := (BoundedContinuousFunction.evalCLM ℝ x).comp (classicalRepresentativeCLM hk)
  have hleft := (E.continuous.tendsto (A v)).comp
    ((ContinuousLinearMap.apply ℝ _ v).continuous.tendsto A |>.comp hA)
  have hright := ((E.continuous.tendsto U).comp hu).mul_const (classicalRepresentativeCLM hk v x)
  change classicalRepresentativeCLM hk (A v) x =
    classicalRepresentativeCLM hk (higherMultiplierCLM hk U v) x
  rw [classicalRepresentative_higherMultiplierCLM]
  exact tendsto_nhds_unique hleft (hright.congr fun j ↦
      (classicalRepresentative_higherMultiplierCLM hk (u j) v x).symm)

/-- Multiplication is bounded bilinear on the entire higher Sobolev space. -/
def higherProductCLM (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) :
    W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n) :=
  ContinuousLinearMap.ofSeqClosedGraph (𝕜 := ℝ) (E := W^{k,2}(ℝ^n))
    (F := W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n)) (g := higherProductLM hk)
    (by
      exact fun u U A hu hA ↦ higherProductLM_seqClosedGraph hk u U A hu hA)

/-- The bounded bilinear map represents the ordinary pointwise product. -/
theorem classicalRepresentative_higherProductCLM
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (u v : W^{k,2}(ℝ^n)) (x : ℝ^n) :
    classicalRepresentativeCLM hk (higherProductCLM hk u v) x =
      classicalRepresentativeCLM hk u x * classicalRepresentativeCLM hk v x :=
  classicalRepresentative_higherProduct hk u v x

end PDE.Hyperbolic.NonlinearWave.Cauchy
