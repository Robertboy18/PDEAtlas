/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Normed.ContinuousMap.Bounded.Bilinear
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Finite regularity of composition on a compact parameter space

The composition operator on continuous functions preserves each finite
differentiability class. In particular, a C² scalar reaction induces a C²
map on the space of continuous functions on a compact backward cone.
No third derivative or Lipschitz Hessian is needed.
-/

@[expose] public noncomputable section

open Set Filter BoundedContinuousFunction
open scoped Topology

namespace WaveEquation.SmallData.Classical.LocalPower

universe v

variable {α E F : Type v} [TopologicalSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Evaluation cannot increase the norm of a linear map into bounded functions. -/
theorem norm_eval_comp_le (A : E →L[ℝ] (α →ᵇ F)) (a : α) :
    ‖(evalCLM ℝ a).comp A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro v
  exact (A v).norm_coe_le_norm a |>.trans (A.le_opNorm v)

/-- Continuous candidate derivatives assemble pointwise derivatives into a
Fréchet derivative in the uniform norm. -/
theorem hasFDerivAt_of_eval {f : E → (α →ᵇ F)} {D : E → E →L[ℝ] (α →ᵇ F)} (hD : Continuous D)
    (hf : ∀ x a, HasFDerivAt (fun y ↦ f y a) ((evalCLM ℝ a).comp (D x)) x) (x : E) :
    HasFDerivAt f (D x) x := by
  apply hasFDerivAt_iff_isLittleO.mpr
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := Metric.continuousAt_iff.mp (hD.continuousAt (x := x)) ε hε
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro a
  have hd : ∀ z ∈ Metric.ball x δ, HasFDerivWithinAt (fun w ↦ f w a - D x w a)
        ((evalCLM ℝ a).comp (D z - D x)) (Metric.ball x δ) z := by
    intro z _
    have heq : (evalCLM ℝ a).comp (D z - D x) =
        (evalCLM ℝ a).comp (D z) - (evalCLM ℝ a).comp (D x) := by
      ext v
      rfl
    rw [heq]
    exact ((hf z a).sub (((evalCLM ℝ a).comp (D x)).hasFDerivAt)).hasFDerivWithinAt
  have hb : ∀ z ∈ Metric.ball x δ,
      ‖(evalCLM ℝ a).comp (D z - D x)‖ ≤ ε := by
    intro z hz
    exact (norm_eval_comp_le _ a).trans
      (by simpa only [dist_eq_norm] using (hbound hz).le)
  have hm := (convex_ball x δ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hd hb (Metric.mem_ball_self hδ) hy
  simpa only [BoundedContinuousFunction.sub_apply, map_sub, evalCLM_apply,
    sub_sub_sub_comm] using hm

variable [CompactSpace α]

/-- Postcomposition on continuous functions over a compact space. Mathlib's
bounded continuous functions carry the uniform norm used below. -/
def composeCompact (f : C(E, F)) (u : α →ᵇ E) : α →ᵇ F :=
  mkOfCompact (f.comp u.toContinuousMap)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Evaluation of compact postcomposition. -/
@[simp] theorem composeCompact_apply (f : C(E, F)) (u : α →ᵇ E) (a : α) :
    composeCompact f u a = f (u a) := rfl

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Continuity of postcomposition follows from the compact-open topology,
which agrees with the uniform norm on a compact domain. -/
theorem continuous_composeCompact (f : C(E, F)) :
    Continuous (composeCompact (α := α) f) :=
  (ContinuousMap.isometryEquivBoundedOfCompact α F).continuous.comp
    ((ContinuousMap.continuous_postcomp f).comp
      (ContinuousMap.isometryEquivBoundedOfCompact α E).symm.continuous)

/-- A finite Cᵏ map induces a finite Cᵏ postcomposition operator in the
uniform norm. This applies to Banach-valued derivatives as well as scalar maps. -/
theorem contDiff_composeCompact {k : ℕ} {f : E → F} (hf : ContDiff ℝ k f) :
    ContDiff ℝ k (composeCompact (α := α) ⟨f, hf.continuous⟩) := by
  induction k generalizing F with
  | zero =>
    exact contDiff_zero.mpr (continuous_composeCompact _)
  | succ k ih =>
    obtain ⟨df, hdf, hderiv⟩ := contDiff_succ_iff_hasFDerivAt.mp hf
    let B := (ContinuousLinearMap.id ℝ (E →L[ℝ] F)).compLeftContinuousBounded₂ α
    let D (u : α →ᵇ E) := B (composeCompact ⟨df, hdf.continuous⟩ u)
    have hD : ContDiff ℝ k D := B.contDiff.comp (ih hdf)
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨D, hD, ?_⟩
    intro u
    apply hasFDerivAt_of_eval hD.continuous
    intro v a
    have heq : (evalCLM ℝ a).comp (D v) = (df (v a)).comp (evalCLM ℝ a) := by
      ext w
      rfl
    rw [heq]
    have hev : HasFDerivAt (fun w : α →ᵇ E ↦ w a) (evalCLM ℝ a) v := by
      have heval : (⇑(evalCLM ℝ a : (α →ᵇ E) →L[ℝ] E)) = fun w ↦ w a := by
        funext w
        exact evalCLM_apply ℝ a w
      rw [← heval]
      exact (evalCLM ℝ a : (α →ᵇ E) →L[ℝ] E).hasFDerivAt
    exact (hderiv (v a)).comp v hev

end WaveEquation.SmallData.Classical.LocalPower
