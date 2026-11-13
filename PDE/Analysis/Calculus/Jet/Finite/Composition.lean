/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Composition of equal finite jets

The Taylor composition formula shows that agreement through a fixed derivative
order is preserved by a smooth outer map. For curves, the hypotheses can be
stated directly with `iteratedDeriv`, including the value at order zero.
-/

@[expose] public section

open scoped ContDiff

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace PDE

/-- Equal derivatives through order `n` remain equal after smooth composition. -/
theorem iteratedFDeriv_comp_eq_of_iteratedFDeriv_eq
    {n : ℕ} {f g : E → F} {Φ : F → G} {x : E}
    (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x)
    (hΦ : ContDiffAt 𝕜 n Φ (f x))
    (heq : ∀ i ≤ n, iteratedFDeriv 𝕜 i f x = iteratedFDeriv 𝕜 i g x) :
    iteratedFDeriv 𝕜 n (Φ ∘ f) x = iteratedFDeriv 𝕜 n (Φ ∘ g) x := by
  have hzero : f x = g x := by
    simpa using congrArg (fun A ↦ A (fun i : Fin 0 ↦ Fin.elim0 i)) (heq 0 (by omega))
  rw [iteratedFDeriv_comp hΦ hf le_rfl,
    iteratedFDeriv_comp (hzero ▸ hΦ) hg le_rfl, ← hzero]
  classical
  apply Finset.sum_congr rfl
  intro c _
  change c.compAlongOrderedFinpartition _
    (fun m ↦ iteratedFDeriv 𝕜 (c.partSize m) f x) =
      c.compAlongOrderedFinpartition _ (fun m ↦ iteratedFDeriv 𝕜 (c.partSize m) g x)
  congr 1
  funext m
  exact heq _ (c.partSize_le m)

/-- Equal finite jets of curves remain equal after smooth composition. -/
theorem iteratedDeriv_comp_eq_of_iteratedDeriv_eq
    {n : ℕ} {f g : 𝕜 → F} {Φ : F → G} {x : 𝕜}
    (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x)
    (hΦ : ContDiffAt 𝕜 n Φ (f x))
    (heq : ∀ i ≤ n, iteratedDeriv i f x = iteratedDeriv i g x) :
    iteratedDeriv n (Φ ∘ f) x = iteratedDeriv n (Φ ∘ g) x := by
  have hfull (i : ℕ) (hi : i ≤ n) :
      iteratedFDeriv 𝕜 i f x = iteratedFDeriv 𝕜 i g x := by
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, heq i hi]
  exact congrArg (fun A ↦ A (fun _ ↦ 1))
    (iteratedFDeriv_comp_eq_of_iteratedFDeriv_eq hf hg hΦ hfull)

end PDE
