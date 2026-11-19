/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.WeakHarmonic
public import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.LaplacianH10

/-!
# The mixed Green pairing depends only on boundary values

An H² function may be integrated by parts against any H¹₀ function. Consequently
its Green pairing with an H¹ function is unchanged by replacing that function
with another lifting of the same trace. This lets a smooth boundary lifting
replace a rough harmonic corrector in a classical first Green identity.
No classical boundary derivative of the H¹ factor is needed.

For `U, V ∈ C²(Ω̄)` the pairing `∫_Ω (ΔV) U dx + ∫_Ω ∇V · ∇U dx` is the boundary term
`∫_{∂Ω} U ∂V/∂ν dS` of Green's first identity, Evans App. C.2, Theorem 3(ii), and so depends only on
`U` on `∂Ω`. `laplacian_pairing_add_gradient_eq_of_trace_eq` is the corresponding statement for
`V ∈ H²(Ω)` and `U ∈ H¹(Ω)`, with the boundary values of `U` replaced by its trace.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. C.2, Theorem 3(ii), p. 712.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Sobolev InnerProductSpace

namespace SobolevSpace.Trace.C1

open GraphSpace

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- An H² function has its weak Laplacian in L² and hence a weak normal trace. -/
def weakNormalTraceOfH2 (V : W^{2,2}(Ω)) : HilbertTraceSpace (Ω := Ω) →L[ℝ] ℝ :=
  weakNormalTrace (lowerOrderCLM (show 1 ≤ 2 by omega) V) (wkpLaplacianCLM V)
    (sum_inner_gradient_eq_neg_inner_laplacian V)

/-- The H² normal trace evaluates by its Laplacian and gradient volume pairings. -/
@[simp]
theorem weakNormalTraceOfH2_traceClass (V : W^{2,2}(Ω)) (U : H¹(Ω)) :
    weakNormalTraceOfH2 V (traceClass U) =
      inner ℝ (wkpLaplacianCLM V) (wkpBaseCoordinateCLM U) +
        inner ℝ (∇ (lowerOrderCLM (show 1 ≤ 2 by omega) V)) (∇ U) :=
  rfl

/-- The L² Laplacian and gradient bound the H² weak normal trace. -/
theorem norm_weakNormalTraceOfH2_le (V : W^{2,2}(Ω)) :
    ‖weakNormalTraceOfH2 V‖ ≤ ‖wkpLaplacianCLM V‖ +
      ‖∇ (lowerOrderCLM (show 1 ≤ 2 by omega) V)‖ :=
  norm_weakNormalTrace_le _ _ _

/-- The mixed Green pairing depends only on the trace of the `H¹` factor: if `U, A ∈ H¹(Ω)` have
the same trace, then `⟪ΔV, U⟫ + ⟪∇V, ∇U⟫ = ⟪ΔV, A⟫ + ⟪∇V, ∇A⟫` in `L²` for every
`V ∈ W^{2,2}(Ω)`, with `ΔV` the weak Laplacian. -/
theorem laplacian_pairing_add_gradient_eq_of_trace_eq
    (V : W^{2,2}(Ω)) (U A : H¹(Ω)) (htrace : trace U = trace A) :
    inner ℝ (wkpLaplacianCLM V) (wkpBaseCoordinateCLM U) +
        inner ℝ (∇ (lowerOrderCLM (show 1 ≤ 2 by omega) V)) (∇ U) =
      inner ℝ (wkpLaplacianCLM V) (wkpBaseCoordinateCLM A) +
        inner ℝ (∇ (lowerOrderCLM (show 1 ≤ 2 by omega) V)) (∇ A) :=
  weak_laplacian_pairing_eq_of_trace_eq _ _
    (sum_inner_gradient_eq_neg_inner_laplacian V) htrace

/-- If `U ∈ H¹(Ω)` is weakly harmonic (`∑ᵢ ⟪∂ᵢ U, ∂ᵢ t⟫ = 0` for every `t ∈ H¹₀(Ω)`) and
`A ∈ H¹(Ω)` has the same trace as `U`, then for every `V ∈ W^{2,2}(Ω)`,
`⟪ΔV, U⟫ + N = ⟪ΔV, A⟫ + ⟪∇V, ∇A⟫`, where `N` is the weak normal trace
`weakHarmonicNormalTrace U hU` evaluated on the trace class of `V`. The lifting `A` may be chosen
smooth. -/
theorem laplacian_pairing_add_weakHarmonicNormalTrace_eq
    (V : W^{2,2}(Ω)) (U A : H¹(Ω))
    (hU : ∀ t : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) U)
        (derivCoordCLM i t)) = 0)
    (htrace : trace U = trace A) :
    inner ℝ (wkpLaplacianCLM V) (wkpBaseCoordinateCLM U) +
        weakHarmonicNormalTrace U hU
          (traceClass (lowerOrderCLM (show 1 ≤ 2 by omega) V)) =
      inner ℝ (wkpLaplacianCLM V) (wkpBaseCoordinateCLM A) +
        inner ℝ (∇ (lowerOrderCLM (show 1 ≤ 2 by omega) V)) (∇ A) := by
  rw [weakHarmonicNormalTrace_traceClass, real_inner_comm _ (∇ U)]
  exact laplacian_pairing_add_gradient_eq_of_trace_eq V U A htrace

end SobolevSpace.Trace.C1
