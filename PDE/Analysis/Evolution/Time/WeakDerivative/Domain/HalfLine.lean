/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Basic

/-!
# Weak differentiation on a half-line

Weak derivative identities on all bounded initial intervals give the identity on the
entire half-line: each compactly supported test fits inside one finite interval.
Local integrability is transferred through the same open neighborhoods.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Evolution.HasWeakTimeDerivativeOn

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Weak differentiation on every finite initial interval gives weak differentiation
on the entire open half-line. -/
theorem of_forall_Ioo {a : ℝ} {f g : ℝ → X}
    (h : ∀ b, a < b → HasWeakTimeDerivativeOn (Ioo a b) f g) :
    HasWeakTimeDerivativeOn (Ioi a) f g := by
  have hlocal {q : ℝ → X}
      (hq : ∀ b, a < b → LocallyIntegrableOn q (Ioo a b) volume) :
      LocallyIntegrableOn q (Ioi a) volume := by
    intro t ht
    change a < t at ht
    have hb : a < t + 1 := by linarith
    have hqt := hq (t + 1) hb t ⟨ht, by linarith⟩
    rw [nhdsWithin_eq_nhds.2 (Ioo_mem_nhds ht (by linarith))] at hqt
    exact hqt.filter_mono nhdsWithin_le_nhds
  refine ⟨hlocal (fun b hb ↦ (h b hb).locallyIntegrable_f),
    hlocal (fun b hb ↦ (h b hb).locallyIntegrable_g), ?_⟩
  intro ell φ hφ hcompact hsupp
  obtain ⟨M, hM⟩ := hcompact.bddAbove
  have hb : a < max M a + 1 := by linarith [le_max_right M a]
  apply (h _ hb).integral_eq ell φ hφ hcompact
  intro t ht
  exact ⟨hsupp ht, by linarith [hM ht, le_max_left M a]⟩

end PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
