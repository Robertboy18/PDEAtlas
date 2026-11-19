/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DivergenceForm.HigherOrder
import PDE.Analysis.MeasureTheory.LocalRepresentative
import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.Interior

/-!
# Smooth interior representatives for the full elliptic equation

Smooth coefficients and smooth forcing give an H¹ weak solution of the full equation one smooth
representative on the whole domain (`exists_smoothRepresentative_of_interior_full_solution`).
Neither a trace condition nor any regularity of the boundary is needed. This is Evans's §6.3.1,
Theorem 3 (Infinite differentiability in the interior); the L∞ coefficients and L² forcing are the
standing weak-form hypotheses.

Evans applies Theorem 2 for every `m` and the Sobolev embedding of §5.6.3, Theorem 6. We work near
each point: `exists_interior_higherOrder_of_contDiffOn` of order `k + 1 + n/2` and the local
embedding `exists_contDiffAt_representative_of_order` give a representative that is `C^k` near the
point. Continuous representatives agree on open overlaps, so
`MeasureTheory.exists_contDiffOn_ae_eq_of_forall_nat` produces one smooth representative.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, Theorem 3 (Infinite differentiability in the
  interior) and its proof, p. 334.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Sobolev

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Smooth interior data give a single smooth representative of an arbitrary H¹
weak solution of the full elliptic equation. The L∞ coefficients and L² forcing
are the standing weak-form hypotheses; higher norms are derived only locally. -/
theorem exists_smoothRepresentative_of_interior_full_solution
    (hΩ : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (B : Fin n → DerivLp n ∞ Ω) (C : DerivLp n ∞ Ω)
    (f : DerivLp n 2 Ω)
    (a : Fin n → Fin n → ℝ^n → ℝ) (b : Fin n → ℝ^n → ℝ) (c g : ℝ^n → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (a i j) Ω)
    (hb : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (b i) Ω)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c Ω) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω)
    (hArep : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a i j)
    (hBrep : ∀ i, (B i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] b i)
    (hCrep : (C : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] c)
    (hfrep : (f : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] g)
    {alpha : ℝ} (hA : AEUniformlyElliptic A alpha)
    (u : H¹(Ω)) (hu : IsInteriorWeakFullDivergenceSolution A B C f u) :
    ∃ v : ℝ^n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v Ω ∧
      v =ᵐ[domainMeasure n Ω] (wkpBaseCoordinateCLM u : ℝ^n → ℝ) := by
  by_cases hn : 0 < n
  · apply MeasureTheory.exists_contDiffOn_ae_eq_of_forall_nat
      (𝕜 := ℝ) (μ := volume) hΩ (Subset.refl Ω) subset_closure
    intro k
    obtain ⟨v, hv, hrep⟩ : ∃ v : ℝ^n → ℝ, (∀ x ∈ Ω, ContDiffAt ℝ k v x) ∧
        v =ᵐ[domainMeasure n Ω] (wkpBaseCoordinateCLM u : ℝ^n → ℝ) := by
      refine MeasureTheory.exists_contDiffAt_ae_eq_of_locally (μ := volume) fun x hx ↦ ?_
      obtain ⟨N, hN, hxN, hNΩ, hNc⟩ :=
        exists_open_between_and_isCompact_closure (isCompact_singleton (x := x))
          hΩ (singleton_subset_iff.mpr hx)
      obtain ⟨V, hV, hxV, hVN, hVc⟩ :=
        exists_open_between_and_isCompact_closure (isCompact_singleton (x := x))
          hN hxN
      let m := k + 1 + n / 2
      let hsub : N ⊆ Ω := subset_closure.trans hNΩ
      let uN : H¹(N) := restrictCLM hN.measurableSet hsub u
      obtain ⟨F, hF⟩ := isLocallyWkpOn_of_contDiffOn (k := m) hΩ
        (hg.of_le (by simp)) 2 N hN hNc hNΩ
      have hFbase : wkpBaseCoordinateCLM F = restrictDerivLp hsub f :=
        Lp.ext (hF.trans ((hfrep.filter_mono (ae_mono (domainMeasure_le hsub))).symm.trans
          (restrictDerivLp_apply_ae hsub f).symm))
      obtain ⟨W, hW⟩ := exists_interior_higherOrder_of_contDiffOn m hN _ _ _ a b c
        (fun i j ↦ ((ha i j).of_le (by simp)).mono hsub)
        (fun i ↦ ((hb i).of_le (by simp)).mono hsub) ((hc.of_le (by simp)).mono hsub)
        (fun i j ↦ (restrictDerivLp_apply_ae hsub (A i j)).trans
          (ae_mono (domainMeasure_le hsub) (hArep i j)))
        (fun i ↦ (restrictDerivLp_apply_ae hsub (B i)).trans
          (ae_mono (domainMeasure_le hsub) (hBrep i)))
        ((restrictDerivLp_apply_ae hsub C).trans
          (ae_mono (domainMeasure_le hsub) hCrep))
        (hA.restrict hsub) F uN (by rw [hFbase]; exact hu.restrict hN hsub)
        hV hVc hVN
      obtain ⟨v, hv, hvW⟩ := exists_contDiffAt_representative_of_order hn hV W
        (show k + 1 + n / 2 ≤ m + 2 by omega)
      refine ⟨V, hV, hxV (mem_singleton x), (subset_closure.trans hVN).trans hsub,
        v, fun y hy ↦ (hv y hy).contDiffWithinAt, ?_⟩
      have hWbase : baseRepresentative W =
          (restrictDerivLp (subset_closure.trans hVN) (wkpBaseCoordinateCLM uN) :
            ℝ^n → ℝ) := congrArg (fun z : DerivLp n 2 V ↦ (z : ℝ^n → ℝ)) hW
      rw [hWbase] at hvW
      filter_upwards [hvW, restrictDerivLp_apply_ae (subset_closure.trans hVN)
        (wkpBaseCoordinateCLM uN),
        ae_mono (domainMeasure_le (subset_closure.trans hVN))
          (restrictCLM_apply_ae hN.measurableSet hsub u (baseIndex n 1))]
        with y hy hz hw
      exact hy.trans (hz.trans hw)
    exact ⟨v, fun x hx ↦ (hv x hx).contDiffWithinAt, hrep⟩
  · obtain rfl : n = 0 := Nat.eq_zero_of_not_pos hn
    exact ⟨fun _ ↦ (wkpBaseCoordinateCLM u : ℝ^0 → ℝ) 0, contDiffOn_const,
      .of_forall fun x ↦ congrArg (wkpBaseCoordinateCLM u : ℝ^0 → ℝ) (Subsingleton.elim 0 x)⟩

end SobolevSpace.GraphSpace
