/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalToWeak
import PDE.Analysis.Calculus.LocalExtension

/-!
# Interior classical derivatives as higher weak derivatives

Finite classical regularity on an open domain identifies all derivative words through that
order as weak derivatives. No ambient extension or boundary regularity is required.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open Set

namespace SobolevSpace

variable {n k : ℕ} {Ω : Set (ℝ^n)} {f : ℝ^n → ℝ}

/-- On an open set, finite classical regularity makes derivative words depend only on
their commutative multi-index. No regularity outside the set is required. -/
theorem iteratedPartialDeriv_congr_perm_of_contDiffOn
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ k f Ω)
    {α β : List (Fin n)} (hα : α.length ≤ k) (hperm : α.Perm β) :
    EqOn (iteratedPartialDeriv α f) (iteratedPartialDeriv β f) Ω := by
  intro x hx
  obtain ⟨g, hg, _, heq⟩ :=
    (hf.contDiffAt (hΩ.mem_nhds hx)).exists_contDiff_compactSupport_eventuallyEq
  calc
    iteratedPartialDeriv α f x = iteratedPartialDeriv α g x :=
      (heq.iteratedPartialDeriv α).eq_of_nhds
    _ = iteratedPartialDeriv β g x :=
      congrFun (iteratedPartialDeriv_congr_perm_of_contDiff
        (hg.of_le (by exact_mod_cast hα)) hperm) x
    _ = iteratedPartialDeriv β f x := (heq.iteratedPartialDeriv β).eq_of_nhds.symm

/-- A derivative word lowers finite local regularity by its length. -/
theorem contDiffAt_iteratedPartialDeriv_of_le {x : ℝ^n}
    (hf : ContDiffAt ℝ k f x) (α : List (Fin n)) (hα : α.length ≤ k) :
    ContDiffAt ℝ ((k - α.length : ℕ) : ℕ∞) (iteratedPartialDeriv α f) x := by
  obtain ⟨g, hg, _, heq⟩ := hf.exists_contDiff_compactSupport_eventuallyEq
  exact (PDE.contDiff_iteratedPartialDeriv_of_le hg α hα).contDiffAt.congr_of_eventuallyEq
    (heq.iteratedPartialDeriv α)

/-- Interior `C^k` regularity suffices for the classical-to-weak derivative identity
through order `k`. The proof composes the first-order integration-by-parts identities. -/
theorem hasWeakDerivativeOn_iteratedPartialDeriv_of_contDiffOn
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ k f Ω)
    (α : List (Fin n)) (hα : α.length ≤ k) :
    HasWeakDerivativeOn Ω α f (iteratedPartialDeriv α f) := by
  induction α with
  | nil =>
    exact hasWeakDerivativeOn_nil (hf.continuousOn.locallyIntegrableOn hΩ.measurableSet)
  | cons i α ih =>
    have hlt : α.length < k := by simpa using hα
    have hstep := hasWeakDerivativeOn_of_contDiffAt_one hΩ
      (fun x hx ↦ (contDiffAt_iteratedPartialDeriv_of_le
        (hf.contDiffAt (hΩ.mem_nhds hx)) α hlt.le).of_le
          (by exact_mod_cast (show 1 ≤ k - α.length by omega))) i
    exact ((ih hlt.le).append_single i hstep).perm List.perm_append_comm

end SobolevSpace
