/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Generation.Limit

/-!
# Construction of the contraction semigroup

The locally uniform strong limit of the Yosida semigroups is linear, contractive,
strongly continuous, and satisfies the semigroup law. Evans leaves this verification to the
reader at the end of step 5 of the proof of §7.4.2, Theorem 4.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.2, proof of Theorem 4, step 5, p. 440.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Set Topology

namespace PDE.Analysis.Evolution.HasContractionResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A : E →ₗ.[ℝ] E} (hA : HasContractionResolvent A)
  (hdense : Dense (A.domain : Set E))

include hdense

/-- The limit orbit is additive in the initial vector. -/
theorem limitOrbit_add (x y : E) (t : NNReal) :
    hA.limitOrbit (x + y) t = hA.limitOrbit x t + hA.limitOrbit y t := by
  apply tendsto_nhds_unique (hA.tendsto_yosidaSemigroup hdense (x + y) t)
  simpa only [map_add] using (hA.tendsto_yosidaSemigroup hdense x t).add
    (hA.tendsto_yosidaSemigroup hdense y t)

/-- The limit orbit respects scalar multiplication in the initial vector. -/
theorem limitOrbit_smul (c : ℝ) (x : E) (t : NNReal) :
    hA.limitOrbit (c • x) t = c • hA.limitOrbit x t := by
  apply tendsto_nhds_unique (hA.tendsto_yosidaSemigroup hdense (c • x) t)
  simpa only [map_smul] using (hA.tendsto_yosidaSemigroup hdense x t).const_smul c

/-- The strong limit retains the contraction estimate. -/
theorem norm_limitOrbit_le (x : E) (t : NNReal) :
    ‖hA.limitOrbit x t‖ ≤ ‖x‖ :=
  le_of_tendsto' (hA.tendsto_yosidaSemigroup hdense x t).norm
    (fun lambda ↦ (hA.yosidaSemigroup_isContraction lambda.property).norm_apply_le t x)

/-- The strong orbit limit, bundled as a bounded linear operator at each time. -/
def limitOperator (t : NNReal) : E →L[ℝ] E :=
  ({ toFun := fun x ↦ hA.limitOrbit x t
     map_add' := fun x y ↦ hA.limitOrbit_add hdense x y t
     map_smul' := fun c x ↦ hA.limitOrbit_smul hdense c x t } : E →ₗ[ℝ] E).mkContinuous
    1 (fun x ↦ by
      change ‖hA.limitOrbit x t‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using hA.norm_limitOrbit_le hdense x t)

/-- Evaluation of the limit operator is the strong orbit limit. -/
@[simp]
theorem limitOperator_apply (t : NNReal) (x : E) :
    hA.limitOperator hdense t x = hA.limitOrbit x t :=
  rfl

/-- Yosida evolution also converges when the initial vectors converge. -/
theorem tendsto_yosidaSemigroup_apply {v : Ioi (0 : ℝ) → E} {x : E}
    (hv : Tendsto v atTop (𝓝 x)) (t : NNReal) :
    Tendsto (fun lambda ↦ hA.yosidaSemigroup lambda.property t (v lambda))
      atTop (𝓝 (hA.limitOrbit x t)) := by
  have hzero : Tendsto (fun lambda : Ioi (0 : ℝ) ↦
      hA.yosidaSemigroup lambda.property t (v lambda) -
        hA.yosidaSemigroup lambda.property t x) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun lambda ↦ ?_)
      (by simpa only [sub_self, norm_zero] using (hv.sub_const x).norm)
    rw [← map_sub]
    exact (hA.yosidaSemigroup_isContraction lambda.property).norm_apply_le t _
  simpa only [sub_add_cancel, zero_add] using
    hzero.add (hA.tendsto_yosidaSemigroup hdense x t)

/-- At time zero the limit operator is the identity. -/
theorem limitOperator_zero :
    hA.limitOperator hdense 0 = ContinuousLinearMap.id ℝ E := by
  ext x
  apply tendsto_nhds_unique (hA.tendsto_yosidaSemigroup hdense x 0)
  simpa only [StronglyContinuousSemigroup.map_zero_apply, ContinuousLinearMap.id_apply] using
    (tendsto_const_nhds : Tendsto (fun _ : Ioi (0 : ℝ) ↦ x) atTop (𝓝 x))

/-- Composition passes to the strong limit because every approximating operator is contractive. -/
theorem limitOperator_add (s t : NNReal) :
    hA.limitOperator hdense (s + t) =
      (hA.limitOperator hdense s).comp (hA.limitOperator hdense t) := by
  ext x
  apply tendsto_nhds_unique (hA.tendsto_yosidaSemigroup hdense x (s + t))
  simpa only [StronglyContinuousSemigroup.map_add_apply, ContinuousLinearMap.comp_apply,
    limitOperator_apply] using
    hA.tendsto_yosidaSemigroup_apply hdense (hA.tendsto_yosidaSemigroup hdense x t) s

/-- Local uniform convergence gives continuity of every limit orbit, including at zero. -/
theorem continuous_limitOrbit (x : E) : Continuous (hA.limitOrbit x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc := (hA.tendstoUniformlyOn_yosidaSemigroup hdense x (t + 1)).continuousOn
    (Filter.Eventually.of_forall (fun lambda ↦
      (hA.yosidaSemigroup lambda.property).continuous_orbit x |>.continuousOn)).frequently
  apply hc.continuousAt
  have hset : Icc (0 : NNReal) (t + 1) = Iic (t + 1) := by ext; simp
  rw [hset]
  exact Iic_mem_nhds (lt_add_one t)

/-- The contraction semigroup constructed solely from the resolvent hypotheses and density. -/
def semigroup : StronglyContinuousSemigroup E where
  toMonoidHom :=
    { toFun := fun t ↦ hA.limitOperator hdense t.toAdd
      map_one' := hA.limitOperator_zero hdense
      map_mul' := fun s t ↦ hA.limitOperator_add hdense s.toAdd t.toAdd }
  continuous_toPointwise := PointwiseConvergenceCLM.continuous_of_continuous_eval
    (fun x ↦ hA.continuous_limitOrbit hdense x)

/-- The constructed semigroup acts by the Yosida orbit limit. -/
@[simp]
theorem semigroup_apply (t : NNReal) (x : E) :
    hA.semigroup hdense t x = hA.limitOrbit x t :=
  rfl

/-- The constructed semigroup is contractive. -/
theorem semigroup_isContraction : (hA.semigroup hdense).IsContraction :=
  fun t ↦ ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x ↦ by
      change ‖hA.limitOrbit x t‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using hA.norm_limitOrbit_le hdense x t)

end PDE.Analysis.Evolution.HasContractionResolvent
