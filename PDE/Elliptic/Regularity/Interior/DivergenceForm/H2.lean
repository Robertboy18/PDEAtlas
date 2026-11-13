/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Coefficients.Restriction
public import PDE.Elliptic.Regularity.Interior.DivergenceForm.Energy
import PDE.Elliptic.Regularity.Interior.DivergenceForm.Estimate
import PDE.Elliptic.Regularity.Interior.H2Compactness
public import PDE.Spaces.Sobolev.GraphSpace.Operators.ZeroOrder

/-!
# Full interior H² regularity

An arbitrary H¹ weak solution of the full divergence-form equation `Lu = f` has an H² representative
on each relatively compact open subdomain when the principal coefficients are C¹ and the drift and
potential are bounded. The estimate has the L² norm of the state as remainder. No boundary condition
or boundary regularity is needed, and the domain need not be bounded.

This is Evans's §6.3.1, Theorem 1 (Interior H²-regularity), for the operator (4), with bounded
coefficients and a uniformly elliptic principal part. The C¹ condition is local, so the derivatives
of the principal coefficients may be unbounded near the boundary.

## Main results

* `exists_interior_h2_of_contDiffOn`: the H² representative, Evans's (7).
* `exists_interior_h2_estimate_of_contDiffOn`: the estimate (8), with a constant independent of the
  solution and the forcing.

## How it works

Evans moves the lower-order terms into the forcing `f̃ = f - b · Du - cu` (10), bounds the
difference quotients of `Du` with the test function `-D_k^{-h}(ζ² D_k^h u)` (11), and obtains (23)
with an H¹ remainder; in step 7, testing (9) with `ζ² u` reduces the remainder to the L² norm. We
also move the lower-order terms into the L² forcing, and `exists_local_h2_of_locallyLipschitzOn`,
the difference-quotient theorem for the principal part, constructs the second derivatives. The bound
with an H¹ remainder then comes from the closed graph theorem rather than from the constants of the
proof, and `exists_interior_estimate_with_L2_remainder` removes that remainder with the cutoff
energy estimate on a slightly larger interior set.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, the operator (4), Theorem 1 (Interior H²-regularity)
  and its proof, (9)-(11) and (23)-(24), pp. 327-331.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Sobolev

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω V : Set (ℝ^n)}

/-- Local C¹ principal coefficients suffice for H² membership for the full equation.
The principal coefficients may have unbounded derivatives near the boundary. -/
theorem exists_interior_h2_of_contDiffOn
    (hΩ : IsOpen Ω) (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (a : Fin n → Fin n → ℝ^n → ℝ) (ha : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω)
    (hrep : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a i j)
    {alpha : ℝ} (hA : AEUniformlyElliptic A alpha)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    (f : DerivLp n 2 Ω) (u : H¹(Ω))
    (hu : IsInteriorWeakFullDivergenceSolution A b c f u)
    (hV : IsOpen V) (hcompact : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) :
    ∃ W : W^{2,2}(V),
      wkpBaseCoordinateCLM W =
        restrictDerivLp (subset_closure.trans hVΩ) (wkpBaseCoordinateCLM u) := by
  have hlip (i j : Fin n) : LocallyLipschitzOn Ω (a i j) := by
    intro x hx
    obtain ⟨C, N, hN, hlip⟩ :=
      ((ha i j).contDiffAt (hΩ.mem_nhds hx)).exists_lipschitzOnWith
    exact ⟨C, N, mem_nhdsWithin_of_mem_nhds hN, hlip⟩
  have hp := (isInteriorWeakFullDivergenceSolution_iff A b c f u).mp hu
  obtain ⟨N, hN, hVN, _, W, hW⟩ :=
    exists_local_h2_of_locallyLipschitzOn hΩ A a hlip hrep hA
      (f - interiorLowerOrderOperator b c u) u hp (closure V) hcompact hVΩ
  let hsub : V ⊆ N := subset_closure.trans hVN
  refine ⟨restrictCLM hV.measurableSet hsub W, ?_⟩
  apply Lp.ext
  filter_upwards [restrictCLM_apply_ae hV.measurableSet hsub W (baseIndex n 2),
    ae_mono (domainMeasure_le hsub) hW,
    restrictDerivLp_apply_ae (subset_closure.trans hVΩ) (wkpBaseCoordinateCLM u)]
    with x hx hy hz
  exact hx.trans (hy.trans hz.symm)

/-- Interior H² regularity with Evans's L² remainder. The constant is independent
of the weak solution and forcing. Boundedness of the domain is not required. -/
theorem exists_interior_h2_estimate_of_contDiffOn
    (hΩ : IsOpen Ω) (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (a : Fin n → Fin n → ℝ^n → ℝ) (ha : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω)
    (hrep : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a i j)
    {alpha : ℝ} (hA : AEUniformlyElliptic A alpha)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    (hV : IsOpen V) (hcompact : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : DerivLp n 2 Ω) (u : H¹(Ω)),
      IsInteriorWeakFullDivergenceSolution A b c f u →
      ∃ W : W^{2,2}(V),
        wkpBaseCoordinateCLM W =
          restrictDerivLp (subset_closure.trans hVΩ) (wkpBaseCoordinateCLM u) ∧
        ‖W‖ ≤ C * (‖f‖ + ‖wkpBaseCoordinateCLM u‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_interior_estimate_with_L2_remainder
    (m := 0) hΩ hV hcompact hVΩ A b c hA (fun N hN _ hNΩ hVN F u hu ↦ by
      let hsub : N ⊆ Ω := subset_closure.trans hNΩ
      exact exists_interior_h2_of_contDiffOn hN _ a
        (fun i j ↦ (ha i j).mono hsub)
        (fun i j ↦ (restrictDerivLp_apply_ae hsub (A i j)).trans
          (ae_mono (domainMeasure_le hsub) (hrep i j)))
        (hA.restrict hsub) _ _ (wkpBaseCoordinateCLM F) u hu hV hcompact hVN)
  refine ⟨C, hC, ?_⟩
  intro f u hu
  simpa only [norm_lpToZeroOrder] using hbound (lpToZeroOrder f) u hu

end SobolevSpace.GraphSpace
