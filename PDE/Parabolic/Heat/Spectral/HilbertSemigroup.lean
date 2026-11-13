/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Generator
public import PDE.Parabolic.Heat.Spectral.HilbertEvolution
import CAS.ExactTactic

/-!
# The generator of Hilbert spectral heat evolution

The coordinate construction defines bounded linear operators and hence a strongly
continuous semigroup. Closedness of its generator passes the finite eigenvector
calculation to every vector whose eigenvalue-weighted coordinates are square summable,
so the series is differentiable without absolute summability of its coefficients.
-/

@[expose] public section

noncomputable section

namespace HeatEquation

open PDE.Analysis.Evolution Filter Set
open scoped Topology NNReal ENNReal lp

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (b : HilbertBasis ι ℝ H) (lambda : ι → ℝ) (hlambda : ∀ i, 0 ≤ lambda i)

/-- The spectral heat operator is bounded and linear in the initial datum. -/
def spectralHeatCLM (t : ℝ≥0) : H →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ spectralHeatEvolution b lambda hlambda f t
      map_add' := by
        intro f g
        apply b.repr.injective
        ext i
        simp [mul_add]
      map_smul' := by
        intro c f
        apply b.repr.injective
        ext i
        simp [mul_left_comm] }
    1 (fun f ↦ by simpa using norm_spectralHeatEvolution_le b lambda hlambda f t)

/-- Applying the bundled operator gives the original coordinate construction. -/
@[simp] theorem spectralHeatCLM_apply (t : ℝ≥0) (f : H) :
    spectralHeatCLM b lambda hlambda t f = spectralHeatEvolution b lambda hlambda f t :=
  rfl

/-- Hilbert spectral damping as a strongly continuous semigroup. -/
def spectralHeatSemigroup : StronglyContinuousSemigroup H where
  toMonoidHom :=
    { toFun := fun t ↦ spectralHeatCLM b lambda hlambda t.toAdd
      map_one' := by ext f; simp
      map_mul' := by
        intro s t
        ext f
        exact spectralHeatEvolution_add b lambda hlambda f s.toAdd t.toAdd }
  continuous_toPointwise := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro f
    exact continuous_spectralHeatEvolution b lambda hlambda f

/-- The semigroup at time `t` applied to `f` is the Hilbert heat series
`spectralHeatEvolution f t`. -/
@[simp] theorem spectralHeatSemigroup_apply (t : ℝ≥0) (f : H) :
    spectralHeatSemigroup b lambda hlambda t f =
      spectralHeatEvolution b lambda hlambda f t :=
  rfl

/-- Every basis vector evolves by its scalar heat multiplier. -/
theorem spectralHeatEvolution_basis (i : ι) (t : ℝ≥0) :
    spectralHeatEvolution b lambda hlambda (b i) t =
      Real.exp (-lambda i * t) • b i := by
  classical
  apply b.repr.injective
  ext j
  simp only [spectralHeatEvolution_repr, map_smul, b.repr_self, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, lp.single_apply]
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

/-- The infinitesimal generator acts on a basis vector by minus its eigenvalue. -/
theorem spectralHeatSemigroup_hasGeneratorAt_basis (i : ι) :
    (spectralHeatSemigroup b lambda hlambda).HasGeneratorAt (b i) (-lambda i • b i) := by
  have he : HasDerivAt (fun t : ℝ ↦ Real.exp (-lambda i * t)) (-lambda i) 0 := by
    cas
  have hd : HasDerivAt (fun t : ℝ ↦ Real.exp (-lambda i * t) • b i)
      (-lambda i • b i) 0 := he.smul_const (b i)
  apply hd.hasDerivWithinAt.congr_of_mem _ self_mem_Ici
  intro t ht
  simp only [StronglyContinuousSemigroup.realOrbit, spectralHeatSemigroup_apply,
    spectralHeatEvolution_basis, Real.coe_toNNReal t ht]

variable [CompleteSpace H]

/-- Square-summable weighted coordinates determine the generator, by closure of its graph.
The second vector supplies the weighted coordinates, not a differentiation hypothesis. -/
theorem spectralHeatSemigroup_hasGeneratorAt_of_repr (f g : H)
    (hfg : ∀ i, b.repr g i = -lambda i * b.repr f i) :
    (spectralHeatSemigroup b lambda hlambda).HasGeneratorAt f g := by
  let T := spectralHeatSemigroup b lambda hlambda
  apply (T.hasGeneratorAt_iff_mem_generatorPMap_graph f g).2
  apply T.isClosed_generatorPMap.mem_of_tendsto
    ((b.hasSum_repr f).prodMk (b.hasSum_repr g))
  apply Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro i _
  have hi := (spectralHeatSemigroup_hasGeneratorAt_basis b lambda hlambda i).smul
    (b.repr f i)
  have hg := (T.hasGeneratorAt_iff_mem_generatorPMap_graph _ _).1 hi
  simpa only [hfg i, smul_smul, mul_comm] using hg

end HeatEquation
