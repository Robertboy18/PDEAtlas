/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Variational.TestIdentity
public import PDE.Spaces.Sobolev.Foundations.VectorValued.WeakDerivatives
import PDE.DistributionTheory.Distribution.Regular.Evaluation

/-!
# The ordinary distributional Stokes residual

The residual is `Δu + f`, with the Laplacian defined by differentiating the
native first weak derivatives. Antisymmetric tests show that its coordinate
derivatives commute. This statement precedes pressure reconstruction: the
residual is an ordinary distribution, with no L² representative assumed. In the weak Stokes
problem (40) of Evans (§8.4.4(a)), this residual is the pressure gradient `Dp`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.4.4(a), equation (40), p. 497.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions ENNReal

open scoped Sobolev

namespace IncompressibleFlow.Stokes

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Opens (ℝ^n)}

/-- The Laplacian-plus-force residual of a native vector H¹₀ field, as an
ordinary distribution on the original open domain. -/
def residual (f : Lp (ℝ^n) 2 (domainMeasure n Ω))
    (u : H¹₀(Ω; ℝ^n)) (j : Fin n) : 𝓓'(Ω, ℝ) :=
  (∑ k : Fin n, Distribution.lineDerivCLM (EuclideanSpace.single k (1 : ℝ))
    (Distribution.ofFun Ω (derivCoordCLM k (u j)) volume ⊤)) +
    Distribution.ofFun Ω (fun x ↦ f x j) volume ⊤

/-- Evaluation of the residual uses the first weak derivatives of
the state and the Fréchet derivatives of the test. -/
theorem residual_apply (f : Lp (ℝ^n) 2 (domainMeasure n Ω))
    (u : H¹₀(Ω; ℝ^n)) (j : Fin n) (φ : 𝓓(Ω, ℝ)) :
    residual f u j φ =
      -(∑ k : Fin n, ∫ x in (Ω : Set (ℝ^n)),
        derivCoordCLM k (u j) x * (∂[k] (φ : ℝ^n → ℝ)) x) +
      ∫ x in (Ω : Set (ℝ^n)), f x j * φ x := by
  have hf : MemLp (fun x ↦ f x j) 2 (domainMeasure n Ω) := by
    simpa only [EuclideanSpace.coe_proj, Function.comp_def] using
      (EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp' (Lp.memLp f)
  have hterm (k : Fin n) :
      Distribution.lineDerivCLM (EuclideanSpace.single k (1 : ℝ))
        (Distribution.ofFun Ω (derivCoordCLM k (u j)) volume ⊤) φ =
      -(∫ x in (Ω : Set (ℝ^n)),
        derivCoordCLM k (u j) x * (∂[k] (φ : ℝ^n → ℝ)) x) := by
    rw [Distribution.lineDerivCLM_apply, Distribution.ofFun_apply_eq_setIntegral_mul
      (memLp_locallyIntegrableOn_domain (Lp.memLp _) (by norm_num))]
    congr 1
  simp only [residual, add_apply, _root_.sum_apply,
    hterm, Finset.sum_neg_distrib, Distribution.ofFun_apply_eq_setIntegral_mul
      (memLp_locallyIntegrableOn_domain hf (by norm_num))]

/-- The residual of a raw divergence-free energy minimizer is weakly closed.
The hypotheses involve no pressure, second weak derivative, or local regularity. -/
theorem lineDeriv_residual_eq_of_minimizes_energy
    (f : Lp (ℝ^n) 2 (domainMeasure n Ω)) (u : H¹₀(Ω; ℝ^n))
    (hu : ∇· u = 0)
    (hmin : ∀ w : H¹₀(Ω; ℝ^n), ∇· w = 0 →
      energy f u ≤ energy f w) (i j : Fin n) :
    Distribution.lineDerivCLM (EuclideanSpace.single i (1 : ℝ)) (residual f u j) =
      (Distribution.lineDerivCLM (EuclideanSpace.single j (1 : ℝ))
        (residual f u i) : 𝓓'(Ω, ℝ)) := by
  ext φ
  let ψ : TestFunctionOn n (Ω : Set (ℝ^n)) :=
    ⟨⟨φ, φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩, φ.tsupport_subset⟩
  have h := antisymmetric_test_identity_of_minimizes_energy f u hu hmin i j ψ
  have hd (k : Fin n) :
      (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single k (1 : ℝ)) φ :
        𝓓(Ω, ℝ)) = (∂[k] (φ : ℝ^n → ℝ)) := by
    funext x
    exact testFunction_lineDerivCLM_apply φ _ x
  simp only [Distribution.lineDerivCLM_apply, residual_apply]
  simp only [hd]
  change
    -(-(∑ k : Fin n, ∫ x in (Ω : Set (ℝ^n)),
      derivCoordCLM k (u j) x * (∂[k] (∂[i] (φ : ℝ^n → ℝ))) x) +
      ∫ x in (Ω : Set (ℝ^n)), f x j * (∂[i] (φ : ℝ^n → ℝ)) x) =
    -(-(∑ k : Fin n, ∫ x in (Ω : Set (ℝ^n)),
      derivCoordCLM k (u i) x * (∂[k] (∂[j] (φ : ℝ^n → ℝ))) x) +
      ∫ x in (Ω : Set (ℝ^n)), f x i * (∂[j] (φ : ℝ^n → ℝ)) x)
  linarith only [h]

end IncompressibleFlow.Stokes
