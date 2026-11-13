/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.ConstantCoefficient
public import PDE.DistributionTheory.Distribution.Operator.FundamentalSolution
public import PDE.DistributionTheory.Distribution.Regular
public import PDE.Elliptic.PotentialTheory.FundamentalSolution

/-!
# One-dimensional Laplace fundamental solution

We prove that `Φ(x) = -|x|/2` is a fundamental solution of `-d²/dx²` on the real line: for every
compactly supported `C²` function `φ`,

`∫ x, (-(|x|)/2) * φ''(x) = - φ(0)`

(`fundamentalSolution_distributional`), and the regular distribution of `Φ` satisfies
`-Φ'' = δ₀` (`fundamentalSolutionDistribution_isFundamentalSolution`). The proof splits the
integral at the origin; on each half-line, the fundamental theorem of calculus applied to
`x φ'(x)` and to `φ` evaluates `∫ x φ''(x) dx`. Evans defines the fundamental solution only for
`n ≥ 2`, in §2.2.1, (6); `Φ` is its one-dimensional analogue, and the identity is the case `n = 1`
of `-ΔΦ = δ₀`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.1(a), the fundamental solution (6) for `n ≥ 2`, p. 22,
  and the interpretation `-ΔΦ = δ₀`, p. 25.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PotentialTheory.OneDimensional

open MeasureTheory TopologicalSpace
open scoped Distributions

/-- The 1D fundamental solution for `-d²/dx²`: `Φ(x) = -|x|/2`. -/
def fundamentalSolution (x : ℝ) : ℝ :=
  -|x| / 2

/-- The scalar one-dimensional kernel agrees with the canonical Euclidean
fundamental solution under the standard embedding `ℝ ≃ ℝ^1`. -/
theorem canonical_fundamentalSolution_apply (x : ℝ) :
    PotentialTheory.fundamentalSolution 1
        (EuclideanSpace.single (0 : Fin 1) x) =
      fundamentalSolution x := by
  by_cases hx : x = 0
  · subst x
    simp [PotentialTheory.fundamentalSolution, fundamentalSolution]
  · have hsingle :
        EuclideanSpace.single (0 : Fin 1) x ≠ (0 : ℝ^1) := by
      intro hzero
      have := congrArg (fun y : ℝ^1 ↦ y 0) hzero
      exact hx (by simpa using this)
    simp [PotentialTheory.fundamentalSolution, fundamentalSolution, hsingle]

/-- The scalar one-dimensional fundamental solution is continuous on `ℝ`. -/
theorem continuous_fundamentalSolution : Continuous fundamentalSolution := by
  unfold fundamentalSolution
  fun_prop

/-- The scalar one-dimensional fundamental solution is locally integrable. -/
theorem fundamentalSolution_locallyIntegrable :
    LocallyIntegrable fundamentalSolution volume :=
  continuous_fundamentalSolution.locallyIntegrable

/-! ## Integration by parts on half-lines -/

private theorem integrableOn_deriv_of_hasCompactSupport {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) (s : Set ℝ) : IntegrableOn (deriv f) s := by
  -- `deriv f` is continuous and has compact support, hence integrable.
  have hcont : Continuous (deriv f) := hf.continuous_deriv_one
  exact (hcont.integrable_of_hasCompactSupport hcf.deriv).integrableOn

private theorem integrableOn_mul_id_deriv_deriv_of_hasCompactSupport {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hcf : HasCompactSupport f) (s : Set ℝ) :
    IntegrableOn (fun x ↦ x * deriv (deriv f) x) s := by
  have hcont : Continuous fun x ↦ x * deriv (deriv f) x := by
    have h2 : Continuous (deriv (deriv f)) := by
      have : ContDiff ℝ 0 (deriv (deriv f)) := by
        -- `C²` gives continuity of the second derivative.
        simpa using (hf.deriv' (n := 1) |>.deriv' (n := 0))
      exact this.continuous
    fun_prop
  have hcs : HasCompactSupport (fun x ↦ x * deriv (deriv f) x) := by
    -- Compact support is inherited from `deriv (deriv f)`.
    change HasCompactSupport ((fun x : ℝ ↦ x) * deriv (deriv f))
    exact hcf.deriv.deriv.mul_left
  exact (hcont.integrable_of_hasCompactSupport hcs).integrableOn

/-- Integration by parts for the first moment on a set whose boundary functional
is evaluation at zero, with sign `σ`. -/
private theorem integral_id_mul_secondDeriv (s : Set ℝ) (σ : ℝ)
    (hFTC : ∀ g : ℝ → ℝ, ContDiff ℝ 1 g → HasCompactSupport g →
      (∫ x in s, deriv g x) = σ * g 0)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hcf : HasCompactSupport f) :
    (∫ x in s, x * deriv (deriv f) x) = -(σ * f 0) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hu : ContDiff ℝ 1 (deriv f) := by simpa using hf.deriv' (n := 1)
  have hcg : HasCompactSupport (fun x : ℝ ↦ x * deriv f x) :=
    hcf.deriv.mul_left
  have hcontg : ContDiff ℝ 1 (fun x : ℝ ↦ x * deriv f x) := contDiff_id.mul hu
  have hderiv : (deriv fun x : ℝ ↦ x * deriv f x) =
      fun x ↦ deriv f x + x * deriv (deriv f) x := by
    funext x
    simpa using (deriv_fun_mul differentiableAt_id hu.differentiable_one.differentiableAt)
  have hzero := hFTC (fun x : ℝ ↦ x * deriv f x) hcontg hcg
  rw [hderiv, integral_add
    (integrableOn_deriv_of_hasCompactSupport hf1 hcf s)
    (integrableOn_mul_id_deriv_deriv_of_hasCompactSupport hf hcf s),
    hFTC f hf1 hcf] at hzero
  simpa using eq_neg_of_add_eq_zero_right (by simpa using hzero)

private theorem integral_Ioi_id_mul_secondDeriv (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hcf : HasCompactSupport f) :
    (∫ x in Set.Ioi (0 : ℝ), x * deriv (deriv f) x) = f 0 := by
  have hFTC (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hcg : HasCompactSupport g) :
      (∫ x in Set.Ioi (0 : ℝ), deriv g x) = (-1 : ℝ) * g 0 := by
    simpa using hcg.integral_Ioi_deriv_eq hg (b := 0)
  simpa using integral_id_mul_secondDeriv (Set.Ioi 0) (-1) hFTC f hf hcf

private theorem integral_Iic_id_mul_secondDeriv (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hcf : HasCompactSupport f) :
    (∫ x in Set.Iic (0 : ℝ), x * deriv (deriv f) x) = -f 0 := by
  have hFTC (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hcg : HasCompactSupport g) :
      (∫ x in Set.Iic (0 : ℝ), deriv g x) = (1 : ℝ) * g 0 := by
    simpa using hcg.integral_Iic_deriv_eq hg (b := 0)
  simpa using integral_id_mul_secondDeriv (Set.Iic 0) 1 hFTC f hf hcf

/-! ## Main distributional identity -/

/-- The scalar kernel `Φ(x) = -|x| / 2` satisfies `-Φ'' = δ₀` distributionally.

The test function is Mathlib's bundled compactly supported `C²` function on
the whole real line. The displayed integral is the action of the regular
distribution `Φ` on the second derivative of the test function. -/
theorem fundamentalSolution_distributional
    (φ : TestFunction (⊤ : TopologicalSpace.Opens ℝ) ℝ 2) :
    (∫ x : ℝ, fundamentalSolution x * deriv (deriv φ) x) = - φ 0 := by
  let f : ℝ → ℝ := fun x ↦ fundamentalSolution x * deriv (deriv φ) x
  have hφ'' : ContDiff ℝ 0 (deriv (deriv φ)) := by
    simpa using (φ.contDiff.deriv' (n := 1)).deriv' (n := 0)
  have hf : Integrable f := (continuous_fundamentalSolution.mul hφ''.continuous)
    |>.integrable_of_hasCompactSupport φ.hasCompactSupport.deriv.deriv.mul_left
  have hIic : (∫ x in Set.Iic (0 : ℝ), f x) =
      (1 / 2 : ℝ) * ∫ x in Set.Iic (0 : ℝ), x * deriv (deriv φ) x := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Iic fun x hx ↦ ?_
    simp only [f, fundamentalSolution, abs_of_nonpos (show x ≤ 0 from hx)]
    ring
  have hIoi : (∫ x in Set.Ioi (0 : ℝ), f x) =
      -(1 / 2 : ℝ) * ∫ x in Set.Ioi (0 : ℝ), x * deriv (deriv φ) x := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    simp only [f, fundamentalSolution, abs_of_pos (show 0 < x from hx)]
    ring
  change ∫ x, f x = _
  rw [← intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn, hIic, hIoi,
    integral_Iic_id_mul_secondDeriv (f := φ) φ.contDiff φ.hasCompactSupport,
    integral_Ioi_id_mul_secondDeriv (f := φ) φ.contDiff φ.hasCompactSupport]
  ring

/-- The canonical `ℝ^1` kernel satisfies the one-dimensional distributional
identity after pullback along the standard scalar embedding. -/
theorem canonical_fundamentalSolution_distributional
    (φ : TestFunction (⊤ : TopologicalSpace.Opens ℝ) ℝ 2) :
    (∫ x : ℝ,
      PotentialTheory.fundamentalSolution 1
          (EuclideanSpace.single (0 : Fin 1) x) *
        deriv (deriv φ) x) = -φ 0 := by
  simpa [canonical_fundamentalSolution_apply] using
    fundamentalSolution_distributional φ

/-! ## The ordinary distribution equation -/

/-- The regular distribution induced by the scalar kernel `Φ(x) = -|x| / 2`. -/
noncomputable def fundamentalSolutionDistribution :
    𝓓'((⊤ : Opens ℝ), ℝ) :=
  Distribution.ofFun ⊤ fundamentalSolution volume ⊤

/-- The one-dimensional fundamental-solution distribution acts by its integral pairing. -/
@[simp]
theorem fundamentalSolutionDistribution_apply
    (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    fundamentalSolutionDistribution φ =
      ∫ x, φ x * fundamentalSolution x := by
  rw [fundamentalSolutionDistribution,
    Distribution.ofFun_apply
      (fundamentalSolution_locallyIntegrable.locallyIntegrableOn (Set.univ : Set ℝ))]
  simp only [smul_eq_mul]

/-- The constant-coefficient distributional operator `-D²` on the real line. -/
noncomputable def negativeSecondDerivativeCLM :
    𝓓'((⊤ : Opens ℝ), ℝ) →L[ℝ] 𝓓'((⊤ : Opens ℝ), ℝ) :=
  PDE.Analysis.constantCoeffLineDerivCLM
    (fun _ : Fin 1 ↦ (-1 : ℝ))
    (fun _ : Fin 1 ↦ 2)
    (fun _ _ ↦ (1 : ℝ))

/-- The operator `-D²` acts by pairing with the negative second derivative of a test
function. -/
theorem negativeSecondDerivativeCLM_apply
    (T : 𝓓'((⊤ : Opens ℝ), ℝ))
    (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    negativeSecondDerivativeCLM T φ =
      -T (TestFunction.lineDerivCLM ℝ (1 : ℝ)
        (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ :
          𝓓((⊤ : Opens ℝ), ℝ)) :
            𝓓((⊤ : Opens ℝ), ℝ)) := by
  rw [negativeSecondDerivativeCLM,
    PDE.Analysis.constantCoeffLineDerivCLM_apply]
  simp only [Fin.sum_univ_one, neg_smul, one_smul]
  change
    (-(Distribution.lineDerivCLM (1 : ℝ)
      (Distribution.lineDerivCLM (1 : ℝ) T))) φ = _
  simp only [neg_apply, Distribution.lineDerivCLM_apply, neg_neg]

private theorem lineDerivCLM_apply_eq_deriv
    (φ : 𝓓((⊤ : Opens ℝ), ℝ)) (x : ℝ) :
    (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ :
      𝓓((⊤ : Opens ℝ), ℝ)) x =
      deriv (fun y : ℝ ↦ φ y) x := by
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
  rw [(φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
  simp [fderiv_eq_smul_deriv]

private theorem secondLineDerivCLM_apply_eq_secondDeriv
    (φ : 𝓓((⊤ : Opens ℝ), ℝ)) (x : ℝ) :
    (TestFunction.lineDerivCLM ℝ (1 : ℝ)
      (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ :
        𝓓((⊤ : Opens ℝ), ℝ)) :
        𝓓((⊤ : Opens ℝ), ℝ)) x =
      deriv (deriv (fun y : ℝ ↦ φ y)) x := by
  rw [lineDerivCLM_apply_eq_deriv]
  have hfirst :
      (fun y : ℝ ↦
        (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ :
          𝓓((⊤ : Opens ℝ), ℝ)) y) =
        deriv (fun y : ℝ ↦ φ y) := by
    funext y
    exact lineDerivCLM_apply_eq_deriv φ y
  rw [hfirst]

/-- The scalar kernel distribution is a fundamental solution for `-D²` at the origin. -/
theorem fundamentalSolutionDistribution_isFundamentalSolution :
    Distribution.IsFundamentalSolutionAt negativeSecondDerivativeCLM
      fundamentalSolutionDistribution (0 : ℝ) := by
  rw [Distribution.isFundamentalSolutionAt_iff]
  refine ⟨by simp, ?_⟩
  intro φ
  rw [negativeSecondDerivativeCLM_apply,
    fundamentalSolutionDistribution_apply]
  let φ₂ : TestFunction (⊤ : Opens ℝ) ℝ 2 :=
    TestFunction.monoCLM ℝ φ
  have hφ₂ : (φ₂ : ℝ → ℝ) = φ := by
    simp [φ₂]
  have hfinite := fundamentalSolution_distributional φ₂
  rw [hφ₂] at hfinite
  calc
    -(∫ x, (TestFunction.lineDerivCLM ℝ (1 : ℝ)
        (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ) :
          𝓓((⊤ : Opens ℝ), ℝ)) x *
        fundamentalSolution x) =
        -(∫ x, fundamentalSolution x *
          deriv (deriv (fun y : ℝ ↦ φ y)) x) := by
      apply congrArg Neg.neg
      apply integral_congr_ae
      filter_upwards with x
      rw [secondLineDerivCLM_apply_eq_secondDeriv]
      ring
    _ = φ 0 := by
      linarith

end PotentialTheory.OneDimensional
