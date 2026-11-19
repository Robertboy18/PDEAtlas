/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.ProfileIncrementEquation
public import PDE.Fluid.NavierStokes.Nonuniqueness.PhysicalFieldReduction
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.HilbertEmbedding

/-!
# Time regularity of the constructed solutions

The physical profile `t^{-1/2} Ũ(x/√t)` is `Ũ + Ψ(t^{-1/2})` with the increment `Ψ` of the
dilations of the profile, which is smooth in every `Hᴺ`; through the inclusions
`H^{k+3}(ℝ³) ⊂ W^{k,∞}(ℝ³)` and `H^{k+3}(ℝ³) ⊂ W^{k,4}(ℝ³)` the physical profile is a smooth path
on `(0, 1)` in every `W^{k,∞}` and every `W^{k,4}` (`contDiffOn_physicalProfileWkTop`,
`contDiffOn_physicalProfileWkFour`). With the smoothness of the physical cutoff field, this gives
the time regularity of the correction at every order and the smoothness of the physical velocity
on `(0, 1) × ℝ³` (`physical_time_regularity`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open HeatEquation.WholeSpace IncompressibleFlow
open scoped NNReal ENNReal Sobolev

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

namespace UnstableProfile

variable (D : UnstableProfile)

/-- Every derivative of `a Ũ(a ·) - Ũ` lies in `Lᵠ` when every derivative of `Ũ` does. -/
theorem memLp_iteratedFDeriv_dilateField_sub_of {q : ℝ≥0∞} {a : ℝ} (ha : 0 < a)
    (hU : ∀ m : ℕ, MemLp (iteratedFDeriv ℝ m D.U) q volume) (m : ℕ) :
    MemLp (iteratedFDeriv ℝ m (dilateField a D.U - D.U)) q volume := by
  have hd := contDiff_dilateField a D.contDiff_U
  have heq : iteratedFDeriv ℝ m (dilateField a D.U - D.U) =
      iteratedFDeriv ℝ m (dilateField a D.U) - iteratedFDeriv ℝ m D.U := by
    funext x
    exact iteratedFDeriv_sub_apply (hd.contDiffAt.of_le (by exact_mod_cast le_top))
      (D.contDiff_U.contDiffAt.of_le (by exact_mod_cast le_top))
  rw [heq]
  exact (memLp_iteratedFDeriv_dilateField ha.ne' D.contDiff_U (hU m)).sub (hU m)

/-- A smooth vector field is the sum of its parts in `W^{k,q}`. -/
theorem vectorWkpOfContDiff_add_sub {k : ℕ} {q : ℝ≥0∞} {X Y : ℝ^3 → ℝ^3}
    (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (hmX : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m X) q volume)
    (hmY : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m Y) q volume)
    (hmD : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m (Y - X)) q volume) :
    vectorWkpOfContDiff Y hY hmY =
      vectorWkpOfContDiff X hX hmX + vectorWkpOfContDiff (Y - X) (hY.sub hX) hmD := by
  funext j
  refine WkpSpaceOn.ext_of_base_ae isOpen_univ _ _ ?_
  change baseRepresentative _ =ᵐ[domainMeasure 3 univ] baseRepresentative _
  have h₁ := baseRepresentative_add_ae (vectorWkpOfContDiff X hX hmX j)
    (vectorWkpOfContDiff (Y - X) (hY.sub hX) hmD j)
  simp only [domainMeasure, Measure.restrict_univ] at h₁ ⊢
  rw [Pi.add_apply]
  filter_upwards [h₁, baseRepresentative_vectorWkpOfContDiff Y hY hmY j,
    baseRepresentative_vectorWkpOfContDiff X hX hmX j,
    baseRepresentative_vectorWkpOfContDiff (Y - X) (hY.sub hX) hmD j] with x e₁ e₂ e₃ e₄
  rw [e₁, e₂, e₃, e₄, Pi.sub_apply, PiLp.sub_apply]
  ring

/-- The physical factor composed with the logarithm is smooth on `(0, 1)`. -/
theorem contDiffOn_physicalFactor_log :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun t ↦ physicalFactor (Real.log t)) (Ioo 0 1) := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) physicalFactor :=
    Real.contDiff_exp.comp ((contDiff_id.div_const 2).neg)
  exact hf.comp_contDiffOn (Real.contDiffOn_log.mono fun t ht ↦ ne_of_gt ht.1)

/-- The increment of the dilations is smooth on `a > 0` in every vector `Hᴺ`, `N ≥ 2`. -/
theorem contDiffOn_top_profileIncrement {N : ℕ} (hm : (3 : ℝ) < 2 * N) :
    ContDiffOn ℝ (⊤ : ℕ∞) (D.profileIncrement N) (Ioi 0) :=
  contDiffOn_infty.mpr fun j ↦ D.contDiffOn_profileIncrement j N hm

/-- The physical profile in `W^{k,∞}` is the profile plus the image of the increment at
`t^{-1/2}`. -/
theorem physicalProfileWkTop_eq (k : ℕ) (t : ℝ) :
    physicalProfileWkTop D k t = D.velocityWkTop k +
      vectorHilbertEmbeddingCLM k memLp_top_baseRepresentative_three
        (D.profileIncrement (k + 3) (physicalFactor (Real.log t))) := by
  have ha := physicalFactor_pos (Real.log t)
  rw [D.profileIncrement_eq (k + 3) ha, vectorHilbertEmbeddingCLM_vectorWkpOfContDiff k
    memLp_top_baseRepresentative_three _ _
    fun m _ ↦ D.memLp_iteratedFDeriv_dilateField_sub_of ha D.memLp_top_iteratedFDeriv m]
  exact vectorWkpOfContDiff_add_sub D.contDiff_U (contDiff_dilateField _ D.contDiff_U) _ _ _

/-- The physical profile in `W^{k,4}` is the profile plus the image of the increment at
`t^{-1/2}`. -/
theorem physicalProfileWkFour_eq (k : ℕ) (t : ℝ) :
    physicalProfileWkFour D k t = D.velocityWkFour k +
      vectorHilbertEmbeddingCLM k memLp_four_baseRepresentative_three
        (D.profileIncrement (k + 3) (physicalFactor (Real.log t))) := by
  have ha := physicalFactor_pos (Real.log t)
  rw [D.profileIncrement_eq (k + 3) ha, vectorHilbertEmbeddingCLM_vectorWkpOfContDiff k
    memLp_four_baseRepresentative_three _ _
    fun m _ ↦ D.memLp_iteratedFDeriv_dilateField_sub_of ha D.derivatives_memLp_four m]
  exact vectorWkpOfContDiff_add_sub D.contDiff_U (contDiff_dilateField _ D.contDiff_U) _ _ _

/-- Orders `k + 3` are above the algebra threshold. -/
theorem three_lt_two_mul_add_three (k : ℕ) : (3 : ℝ) < 2 * ((k + 3 : ℕ) : ℝ) := by
  push_cast
  linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]

/-- **The physical profile is a smooth path in every `W^{k,∞}`** on `(0, 1)`. -/
theorem contDiffOn_physicalProfileWkTop (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (physicalProfileWkTop D k) (Ioo 0 1) := by
  let _ : NormedSpace ℝ (Fin 3 → W^{k,∞}(ℝ^3)) := Pi.normedSpace
  have h := (D.contDiffOn_top_profileIncrement (three_lt_two_mul_add_three k)).comp
    contDiffOn_physicalFactor_log fun t _ ↦ physicalFactor_pos (Real.log t)
  refine (contDiffOn_const.add
    ((vectorHilbertEmbeddingCLM k memLp_top_baseRepresentative_three).contDiff.comp_contDiffOn
      h)).congr fun t _ ↦ D.physicalProfileWkTop_eq k t

/-- **The physical profile is a smooth path in every `W^{k,4}`** on `(0, 1)`. -/
theorem contDiffOn_physicalProfileWkFour (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (physicalProfileWkFour D k) (Ioo 0 1) := by
  let _ : NormedSpace ℝ (Fin 3 → W^{k,4}(ℝ^3)) := Pi.normedSpace
  have h := (D.contDiffOn_top_profileIncrement (three_lt_two_mul_add_three k)).comp
    contDiffOn_physicalFactor_log fun t _ ↦ physicalFactor_pos (Real.log t)
  refine (contDiffOn_const.add
    ((vectorHilbertEmbeddingCLM k memLp_four_baseRepresentative_three).contDiff.comp_contDiffOn
      h)).congr fun t _ ↦ D.physicalProfileWkFour_eq k t

end UnstableProfile

/-- **Time regularity from a smooth cutoff field.** Above the threshold radius and for
`s ∈ [0, 1]`, if the physical cutoff field `-e^{tΔ} w` is a smooth path on `(0, 1)` in every
`W^{k,∞}` and every `W^{k,4}`, then the physical correction
`u_cor(t) = t^{-1/2} U_cor(log t, ·/√t)` is `C^j` on `(0, 1)` with values in every vector
`Hᵐ⁺¹`, for every `j`, and the physical velocity is smooth at every point of `(0, 1) × ℝ³`. -/
theorem physical_time_regularity_of_cutoff (D : UnstableProfile) (R s : ℝ)
    (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hcut : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalCutoffSobolev D R k le_top) (Ioo 0 1))
    (hcut₄ : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalCutoffSobolev D R k le_rfl) (Ioo 0 1)) :
    (∀ (j m : ℕ) (hm : (3 : ℝ) < 2 * m),
        ContDiffOn ℝ j (physicalCorrection D R s m hm) (Ioo 0 1)) ∧
      ∀ z ∈ IncompressibleFlow.finiteTimeDomain 3 1,
        ContDiffAt ℝ (⊤ : ℕ∞) (physicalVelocity D R s) z :=
  physical_time_regularity_of_fields hR hs hcut hcut₄ D.contDiffOn_physicalProfileWkTop
    D.contDiffOn_physicalProfileWkFour

end NavierStokes.Nonuniqueness
