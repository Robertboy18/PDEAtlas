/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Divergence.Regularity
public import PDE.Spaces.Sobolev.GraphSpace.Norms.WeakDerivativeBounds

/-!
# Quantitative recovery of a Sobolev flux component

The divergence controls the missing matching derivative by the load and
the transverse derivatives. Summing the resulting coordinate estimates
controls the full H¹ norm of the component.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A uniform transverse derivative bound yields a full H¹ bound for
the distinguished flux component. The estimate is uniform over fluxes and
loads with the displayed L² and transverse derivative bounds. -/
theorem norm_component_H1_le_of_weakDivergence
    (hΩ : IsOpen Ω) (normal : Fin n)
    (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω)
    (hdiv : ∀ (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)), tsupport φ.toFun ⊆ Ω →
      (∑ i : Fin n, ∫ x, (q i : ℝ^n → ℝ) x *
        (∂[i] φ.toFun) x ∂domainMeasure n Ω) =
        ∫ x, (f : ℝ^n → ℝ) x * φ.toFun x ∂domainMeasure n Ω)
    {B : ℝ} (hB : 0 ≤ B)
    (htransverse : ∀ k : Fin n, k ≠ normal → ∀ i : Fin n,
      ∃ g : DerivLp n 2 Ω, ‖g‖ ≤ B ∧
        HasWeakDerivativeOn Ω [k] (q i : ℝ^n → ℝ) (g : ℝ^n → ℝ))
    (Q : W^{1,2}(Ω)) (hQ : wkpBaseCoordinateCLM Q = q normal) :
    ‖Q‖ ≤ ‖q normal‖ + n * (‖f‖ + (n + 1) * B) := by
  have hdiag (i : Fin n) : ∃ g : DerivLp n 2 Ω, ‖g‖ ≤ B ∧
      (i ≠ normal → HasWeakDerivativeOn Ω [i] (q i : ℝ^n → ℝ) (g : ℝ^n → ℝ)) := by
    by_cases hi : i ≠ normal
    · obtain ⟨g, hg, hd⟩ := htransverse i hi i
      exact ⟨g, hg, fun _ ↦ hd⟩
    · exact ⟨0, by simpa using hB, fun h ↦ (hi h).elim⟩
  choose dq hdq hd using hdiag
  obtain ⟨g, hg, hweak⟩ := exists_component_weakDerivative_of_weakDivergence_with_norm
    normal q dq f hdiv hd
  have hsum : (∑ i ∈ Finset.univ.erase normal, ‖dq i‖) ≤ n * B := by
    calc
      _ ≤ ∑ i : Fin n, ‖dq i‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (by
          intro i _ _
          exact norm_nonneg _)
      _ ≤ ∑ _ : Fin n, B := Finset.sum_le_sum fun i _ ↦ hdq i
      _ = _ := by simp
  have hbound : ‖Q‖ ≤ ‖wkpBaseCoordinateCLM Q‖ +
      ∑ _ : Fin n, (‖f‖ + (n + 1) * B) := by
    apply norm_le_base_add_sum_of_weakDerivative_bounds hΩ Q
    intro k
    have hb : baseRepresentative Q = (q normal : ℝ^n → ℝ) :=
      congrArg (fun v : DerivLp n 2 Ω ↦ (v : ℝ^n → ℝ)) hQ
    rw [hb]
    by_cases hk : k = normal
    · subst k
      refine ⟨g, ?_, hweak⟩
      have hg' := hg.trans (add_le_add le_rfl hsum)
      nlinarith
    · obtain ⟨v, hv, hvweak⟩ := htransverse k hk normal
      refine ⟨v, hv.trans ?_, hvweak⟩
      nlinarith [norm_nonneg f, mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hB]
  simpa only [hQ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    using hbound

end SobolevSpace.GraphSpace
