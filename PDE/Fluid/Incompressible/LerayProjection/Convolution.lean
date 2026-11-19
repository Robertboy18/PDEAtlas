/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.LerayProjection.Translation
public import PDE.Analysis.Lp.Translation

/-!
# Scalar convolution commutes with the actual whole-space Leray projection

Scalar convolution is the Bochner integral of translated L² vector fields.
The established translation identity lets the bounded Leray projector pass
through this integral. No Fourier description of the solenoidal subspace
is needed.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Topology Sobolev

namespace IncompressibleFlow

variable {n : ℕ}

/-- Spatial translations have continuous orbits on the actual fluid L² pivot. -/
theorem continuous_l2Translate (u : WholeSpaceL2 n) :
    Continuous (fun y : ℝ^n ↦ l2Translate y u) := by
  let g : ℝ^n → C(ℝ^n, ℝ^n) := fun y ↦ ⟨fun x ↦ x + y,
    continuous_id.add continuous_const⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_snd.add continuous_fst
  exact (continuous_const : Continuous (fun _ : ℝ^n ↦ u)).compMeasurePreservingLp
    hg wholeSpace_translation_measurePreserving (by norm_num)

/-- Every integrable scalar kernel gives an integrable translated vector orbit. -/
theorem integrable_smul_l2Translate {k : ℝ^n → ℝ} (hk : Integrable k volume)
    (u : WholeSpaceL2 n) :
    Integrable (fun y ↦ k y • l2Translate (-y) u) volume := by
  let : SecondCountableTopologyEither (ℝ^n) (WholeSpaceL2 n) :=
    ⟨Or.inl inferInstance⟩
  exact (ContinuousLinearMap.lsmul ℝ ℝ :
    ℝ →L[ℝ] WholeSpaceL2 n →L[ℝ] WholeSpaceL2 n).integrable_of_bilin_of_bdd_right
      ‖u‖ hk ((continuous_l2Translate u).comp continuous_neg).aestronglyMeasurable
      (.of_forall fun y ↦ (l2Translate (-y)).norm_map u |>.le)

/-- Convolution by a scalar integrable kernel on the actual vector L² pivot. -/
def l2Convolution (k : ℝ^n → ℝ) (hk : Integrable k volume) :
    WholeSpaceL2 n →L[ℝ] WholeSpaceL2 n :=
  LinearMap.mkContinuous
    { toFun := fun u ↦ ∫ y, k y • l2Translate (-y) u
      map_add' := by
        intro u v
        simp only [map_add, smul_add]
        exact integral_add (integrable_smul_l2Translate hk u)
          (integrable_smul_l2Translate hk v)
      map_smul' := by
        intro c u
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        apply integral_congr_ae
        exact .of_forall fun y ↦ smul_comm (k y) c (l2Translate (-y) u) }
    (∫ y, ‖k y‖) (fun u ↦ by
      calc
        ‖∫ y, k y • l2Translate (-y) u‖ ≤ ∫ y, ‖k y • l2Translate (-y) u‖ :=
          norm_integral_le_integral_norm _
        _ = (∫ y, ‖k y‖) * ‖u‖ := by
          simp only [norm_smul, (l2Translate _).norm_map]
          exact integral_mul_const ‖u‖ (fun y ↦ ‖k y‖))

/-- The bounded convolution operator is the integral of the actual translation orbit. -/
theorem l2Convolution_apply (k : ℝ^n → ℝ) (hk : Integrable k volume)
    (u : WholeSpaceL2 n) :
    l2Convolution k hk u = ∫ y, k y • l2Translate (-y) u := rfl

/-- The actual L² Leray projector commutes with every scalar integrable convolution. -/
theorem lerayProjection_l2Convolution (k : ℝ^n → ℝ) (hk : Integrable k volume)
    (u : WholeSpaceL2 n) :
    lerayProjection n (l2Convolution k hk u) =
      l2Convolution k hk (lerayProjection n u) := by
  rw [l2Convolution_apply, l2Convolution_apply,
    ← (lerayProjection n).integral_comp_comm (integrable_smul_l2Translate hk u)]
  apply integral_congr_ae
  filter_upwards with y
  rw [map_smul, lerayProjection_l2Translate]

/-- Scalar convolution preserves actual distributional solenoidality. -/
theorem l2Convolution_mem_solenoidal (k : ℝ^n → ℝ) (hk : Integrable k volume)
    {u : WholeSpaceL2 n} (hu : u ∈ l2Solenoidal n) :
    l2Convolution k hk u ∈ l2Solenoidal n := by
  have he : lerayProjection n (l2Convolution k hk u) = l2Convolution k hk u := by
    rw [lerayProjection_l2Convolution, lerayProjection_eq_self hu]
  rw [← he]
  exact lerayProjection_mem n _

end IncompressibleFlow
