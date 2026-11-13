/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Uniform limits of derivative graphs on an open subset

Bounded continuous functions on a set are extended by zero only to write their
interior Fréchet derivatives. No continuity across the boundary is asserted.
Mathlib's uniform-limit theorem proves that the derivative relation is closed.
-/

@[expose] public section

open Filter Set
open scoped Topology BoundedContinuousFunction

namespace BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] {s U : Set E}

/-- The zero extension agrees with a function at every point of its domain. -/
theorem extend_zero_apply (f : s →ᵇ F) {x : E} (hx : x ∈ s) :
    Function.extend Subtype.val f 0 x = f ⟨x, hx⟩ :=
  Subtype.val_injective.extend_apply f 0 ⟨x, hx⟩

/-- Zero extension is continuous when restricted to its original domain. -/
theorem continuousOn_extend_zero (f : s →ᵇ F) :
    ContinuousOn (Function.extend Subtype.val f 0) s := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have heq : s.domRestrict (Function.extend Subtype.val f 0) = f :=
    funext fun x ↦ extend_zero_apply f x.2
  rw [heq]
  exact f.continuous

/-- Extending the zero bounded continuous function gives the zero function. -/
theorem extend_zero_zero :
    Function.extend Subtype.val (0 : s →ᵇ F) 0 = (0 : E → F) := by
  funext x
  simp [Function.extend]

/-- Zero extension preserves addition. -/
theorem extend_zero_add (f g : s →ᵇ F) :
    Function.extend Subtype.val (f + g) 0 =
      Function.extend Subtype.val f 0 + Function.extend Subtype.val g 0 := by
  classical
  funext x
  simp only [Function.extend, Pi.add_apply]
  split <;> simp

/-- Zero extension commutes with multiplication by a constant. -/
theorem extend_zero_smul [NormedSpace ℝ F] (c : ℝ) (f : s →ᵇ F) :
    Function.extend Subtype.val (c • f) 0 = c • Function.extend Subtype.val f 0 := by
  classical
  funext x
  simp only [Function.extend, Pi.smul_apply]
  split <;> simp

/-- Uniform convergence of bounded continuous functions persists after zero extension. -/
theorem tendstoUniformly_extend_zero {f : ℕ → s →ᵇ F} {g : s →ᵇ F}
    (h : Tendsto f atTop (𝓝 g)) :
    TendstoUniformly (fun j ↦ Function.extend Subtype.val (f j) 0)
      (Function.extend Subtype.val g 0) atTop := by
  have hu := tendsto_iff_tendstoUniformly.mp h
  refine Metric.tendstoUniformly_iff.mpr fun ε hε ↦ ?_
  filter_upwards [Metric.tendstoUniformly_iff.mp hu ε hε] with j hj x
  by_cases hx : x ∈ s
  · rw [extend_zero_apply _ hx, extend_zero_apply _ hx]
    exact hj ⟨x, hx⟩
  · have hn : ¬ ∃ y : s, (y : E) = x := by simpa using hx
    simpa only [Function.extend_apply' _ _ _ hn, Pi.zero_apply, dist_self] using hε

/-- A uniform limit of derivative pairs on an open set is again a derivative pair. -/
theorem hasFDerivAt_of_tendsto [NormedSpace ℝ E] [NormedSpace ℝ F]
    (hU : IsOpen U) (hUs : U ⊆ s)
    {f : ℕ → s →ᵇ F} {f' : ℕ → s →ᵇ (E →L[ℝ] F)}
    {g : s →ᵇ F} {g' : s →ᵇ (E →L[ℝ] F)}
    (hf : Tendsto f atTop (𝓝 g)) (hf' : Tendsto f' atTop (𝓝 g'))
    (hd : ∀ j x (hx : x ∈ U),
      HasFDerivAt (Function.extend Subtype.val (f j) 0) (f' j ⟨x, hUs hx⟩) x)
    {x : E} (hx : x ∈ U) :
    HasFDerivAt (Function.extend Subtype.val g 0) (g' ⟨x, hUs hx⟩) x := by
  have h := hasFDerivAt_of_tendstoUniformlyOn hU
    (tendstoUniformly_extend_zero hf').tendstoUniformlyOn
    (fun j y hy ↦ by
      rw [extend_zero_apply _ (hUs hy)]
      exact hd j y hy)
    (fun y _ ↦ (tendstoUniformly_extend_zero hf).tendsto_at y) hx
  rwa [extend_zero_apply _ (hUs hx)] at h

/-- The actual derivative relation on an open subset is closed in the two
supremum-norm fields. -/
theorem isClosed_setOf_hasFDerivAt [NormedSpace ℝ E] [NormedSpace ℝ F]
    (hU : IsOpen U) (hUs : U ⊆ s) :
    IsClosed {fg : (s →ᵇ F) × (s →ᵇ (E →L[ℝ] F)) |
      ∀ x (hx : x ∈ U), HasFDerivAt (Function.extend Subtype.val fg.1 0)
        (fg.2 ⟨x, hUs hx⟩) x} := by
  refine IsSeqClosed.isClosed ?_
  intro f g hf hg x hx
  exact hasFDerivAt_of_tendsto hU hUs
    (continuous_fst.tendsto g |>.comp hg)
    (continuous_snd.tendsto g |>.comp hg) (fun j y hy ↦ hf j y hy) hx

/-- Derivative identities of continuous families persist at boundary parameters.
Only the spatial derivative graph is closed; no smooth parameter extension is used. -/
theorem hasFDerivAt_closure_parameter [NormedSpace ℝ E] [NormedSpace ℝ F]
    {T : Type*} [TopologicalSpace T] {S : Set T}
    (hU : IsOpen U) (hUs : U ⊆ s)
    {f : T → s →ᵇ F} {g : T → s →ᵇ (E →L[ℝ] F)}
    (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ t ∈ S, ∀ x (hx : x ∈ U),
      HasFDerivAt (Function.extend Subtype.val (f t) 0) (g t ⟨x, hUs hx⟩) x)
    {t : T} (ht : t ∈ closure S) {x : E} (hx : x ∈ U) :
    HasFDerivAt (Function.extend Subtype.val (f t) 0) (g t ⟨x, hUs hx⟩) x :=
  closure_minimal hd
    ((isClosed_setOf_hasFDerivAt hU hUs).preimage (hf.prodMk hg)) ht x hx

/-- Uniform continuity of bounded continuous functions is preserved by a norm limit. -/
theorem uniformContinuous_of_tendsto {f : ℕ → s →ᵇ F} {g : s →ᵇ F}
    (h : Tendsto f atTop (𝓝 g)) (hf : ∀ j, UniformContinuous (f j)) :
    UniformContinuous g :=
  (tendsto_iff_tendstoUniformly.mp h).uniformContinuous
    (Filter.Eventually.frequently (Filter.Eventually.of_forall hf))

end BoundedContinuousFunction
