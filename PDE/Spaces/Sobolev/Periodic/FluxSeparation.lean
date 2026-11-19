/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Periodic.DirectionalTests

/-!
# Smooth directional tests separate vector fluxes

The density of compactly supported smooth functions in the canonical
zero-boundary Sobolev space, followed by the dense L² base inclusion, shows that
smooth scalar tests in each coordinate determine an L² vector field. The pairing
bridge uses the scalar and vector Lp representations.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace SobolevSpace.GraphSpace
open scoped ENNReal Topology InnerProductSpace Sobolev Distributions

namespace SobolevSpace.Periodic

variable {n : ℕ} {Ω : Set (ℝ^n)} [IsFiniteMeasure (volume.restrict Ω)]

/-- Pairing a vector flux with a scalar test times a coordinate direction is
the canonical scalar coordinate pairing. -/
theorem inner_coordinate_base_test (q : Lp (ℝ^n) 2 (volume.restrict Ω))
    (i : Fin n) (φ : TestFunctionOn n Ω) :
    ⟪(EuclideanSpace.proj (𝕜 := ℝ) i).compLp q,
      baseCoordCLM (testFunctionToH10 φ)⟫_ℝ =
    ⟪q, testFunctionLpTop (Ω := Ω) φ.1 •
      Lp.const 2 (volume.restrict Ω) (EuclideanSpace.single i (1 : ℝ))⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(EuclideanSpace.proj (𝕜 := ℝ) i).coeFn_compLp q,
    baseCoordCLM_testFunction_apply_ae φ, testFunctionLpTop_apply_ae (Ω := Ω) φ.1,
    Lp.coeFn_const 2 (volume.restrict Ω) (EuclideanSpace.single i (1 : ℝ)),
    Lp.coeFn_lpSMul (r := 2) (testFunctionLpTop (Ω := Ω) φ.1)
      (Lp.const 2 (volume.restrict Ω) (EuclideanSpace.single i (1 : ℝ)))]
    with x hp hb hφ hc hm
  rw [hp, hb, hm, Pi.smul_apply', hφ, hc]
  simp only [Function.const_apply, real_inner_smul_right, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul, RCLike.inner_apply]
  rfl

/-- Compactly supported smooth scalar tests in each coordinate separate L² fluxes
on an open domain. Density is inherited from the canonical zero-boundary Sobolev API. -/
theorem eq_of_inner_weighted_const_eq (hΩo : IsOpen Ω)
    (P Q : Lp (ℝ^n) 2 (volume.restrict Ω))
    (h : ∀ (i : Fin n) (φ : TestFunctionOn n Ω),
      ⟪P, testFunctionLpTop (Ω := Ω) φ.1 •
        Lp.const 2 (volume.restrict Ω) (EuclideanSpace.single i (1 : ℝ))⟫_ℝ =
      ⟪Q, testFunctionLpTop (Ω := Ω) φ.1 •
        Lp.const 2 (volume.restrict Ω) (EuclideanSpace.single i (1 : ℝ))⟫_ℝ) : P = Q := by
  have hd := (baseCoordCLM_denseRange hΩo).comp denseRange_testFunctionToH10Linear
    (baseCoordCLM (n := n) (Ω := Ω)).continuous
  have he (i : Fin n) : (EuclideanSpace.proj (𝕜 := ℝ) i).compLp P =
      (EuclideanSpace.proj (𝕜 := ℝ) i).compLp Q := by
    apply ext_inner_right ℝ
    intro g
    refine hd.induction_on g (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro φ
    change ⟪(EuclideanSpace.proj (𝕜 := ℝ) i).compLp P,
      baseCoordCLM (testFunctionToH10 φ)⟫_ℝ =
      ⟪(EuclideanSpace.proj (𝕜 := ℝ) i).compLp Q,
        baseCoordCLM (testFunctionToH10 φ)⟫_ℝ
    rw [inner_coordinate_base_test, inner_coordinate_base_test]
    exact h i φ
  calc
    P = Lp.euclideanTuple (fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).compLp P) :=
      (Lp.euclideanTuple_coordinates P).symm
    _ = Lp.euclideanTuple (fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).compLp Q) := by
      congr 1
      funext i
      exact he i
    _ = Q := Lp.euclideanTuple_coordinates Q

end SobolevSpace.Periodic
