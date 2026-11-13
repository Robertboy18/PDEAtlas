/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Common compact supports in an exhaustion

A finite family of compactly supported smooth functions is supported in one member of any
compact exhaustion. Bundling the functions in that fixed-support space preserves their
values and all constraints expressed in terms of those values.
-/

@[expose] public noncomputable section

open Set TopologicalSpace
open scoped Distributions

namespace TestFunction

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Finite ι]

/-- A finite family of test functions can be realized, without changing any function, in
one member of a compact exhaustion. The differentiability order may be finite. -/
theorem exists_supportedIn_compactExhaustion
    {m : ℕ∞} (K : CompactExhaustion E) (f : ι → 𝓓^{m}((⊤ : Opens E), F)) :
    ∃ n, ∃ g : ι → 𝓓^{m}_{(⟨K n, K.isCompact n⟩ : Compacts E)}(E, F),
      ∀ i, (g i : E → F) = (f i : E → F) := by
  obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact
    (isCompact_iUnion fun i ↦ (f i).hasCompactSupport)
  refine ⟨n, fun i ↦ .of_support_subset (f i).contDiff ?_, fun _ ↦ rfl⟩
  exact (subset_tsupport _).trans ((subset_iUnion (fun i ↦ tsupport (f i)) i).trans hn)

end TestFunction
