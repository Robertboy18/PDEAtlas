/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Divergence.Component
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder

/-!
# First-order regularity of one flux component

Tangential derivatives of all flux components, together with the weak divergence,
recover every derivative of the remaining component. The conclusion is an
`H¹` element whose base coordinate equals that component in `L²`.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A weak divergence and all transverse component derivatives give a
first-order Sobolev element with the distinguished component as its L² value. -/
theorem exists_component_H1_of_weakDivergence
    (normal : Fin n) (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω)
    (hdiv : ∀ (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)), tsupport φ.toFun ⊆ Ω →
      (∑ i : Fin n, ∫ x, (q i : ℝ^n → ℝ) x *
        (∂[i] φ.toFun) x ∂domainMeasure n Ω) =
        ∫ x, (f : ℝ^n → ℝ) x * φ.toFun x ∂domainMeasure n Ω)
    (htransverse : ∀ k : Fin n, k ≠ normal → ∀ i : Fin n,
      ∃ g : DerivLp n 2 Ω,
        HasWeakDerivativeOn Ω [k] (q i : ℝ^n → ℝ) (g : ℝ^n → ℝ)) :
    ∃ Q : W^{1,2}(Ω), Q.val (baseIndex n 1) = q normal := by
  have hdiag (i : Fin n) : ∃ g : DerivLp n 2 Ω, i ≠ normal →
      HasWeakDerivativeOn Ω [i] (q i : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
    by_cases hi : i ≠ normal
    · obtain ⟨g, hg⟩ := htransverse i hi i
      exact ⟨g, fun _ ↦ hg⟩
    · exact ⟨0, fun h ↦ (hi h).elim⟩
  choose dq hdq using hdiag
  obtain ⟨g, _, hg⟩ := exists_component_weakDerivative_of_weakDivergence_with_norm
    normal q dq f hdiv hdq
  have hex (k : Fin n) : ∃ v : DerivLp n 2 Ω,
      HasWeakDerivativeOn Ω [k] (q normal : ℝ^n → ℝ) (v : ℝ^n → ℝ) := by
    by_cases hk : k = normal
    · exact ⟨g, hk ▸ hg⟩
    · exact htransverse k hk normal
  choose d hd using hex
  obtain ⟨Q, hQ, _⟩ := exists_of_weakDerivative_coordinates (q normal) d hd
  exact ⟨Q, hQ⟩

end SobolevSpace.GraphSpace
