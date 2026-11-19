/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.Exhaustion
public import PDE.Fluid.NavierStokes.Stationary.ConvectionLimit

/-!
# Whole-space stationary correction from compact tests

Uniform mass and gradient radii bound the actual H¹ correction graph norm.
Compact cutoff observations pass its quadratic convection through exhaustion.
A bounded reconstruction may include the finite-rank correction used by
Hou, Wang and Yang (Section 4.3). The inverse-radius background is retained in the
linear and forcing terms, without asserting that it belongs to whole-space H¹.

This theorem passes already constructed approximate corrections to the limit, together with
any family of continuous linear constraints they all satisfy, such as membership in a symmetry
sector. It does not construct the bounded-domain corrections or certify their budgets.

The mass and gradient maps split the norm, `‖u‖² = ‖massCLM u‖² + ‖gradientCLM u‖²`
(`norm_sq_eq_mass_add_gradient`), so separate mass and gradient radii give the boundedness
required by the general exhaustion theorem
`PDE.Analysis.Variational.exists_solution_of_eventually_eq`. The tests may be indexed by any
type, countable or not. The radii concern the correction `u`, while the convection is that of
its reconstruction `R u`, a bounded map that preserves vanishing divergence. For Hou, Wang and
Yang these are `U₁` and `U₁ + G U₁`, and the theorem is their passage from the bounded-domain
equations (4.37) to the whole-space equation (4.21).

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 4.3, (4.21)-(4.23), p. 28,
  and (4.37) and the weak limit as `R → ∞`, p. 31.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal RealInnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert
open scoped Topology Distributions

namespace NavierStokes.Stationary

variable {n : ℕ}

local notation "H" => PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))
local notation "M" => PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 univ)
local notation "G" => PiLp 2 (fun _ : Fin n ↦ PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 univ))

/-- The actual mass-coordinate map on whole-space Sobolev velocity corrections. -/
def massCLM : H →L[ℝ] M :=
  ContinuousLinearMap.piLpMap 2 fun _ ↦ wkpBaseCoordinateCLM

/-- All first partial derivatives of one scalar whole-space Sobolev field. -/
def scalarGradientCLM : H¹(ℝ^n) →L[ℝ] PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 univ) :=
  (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j ↦ wkpCoordinateCLM (singleDerivIndex n j))

/-- The full correction-gradient matrix, with the finite Hilbert product norm. -/
def gradientCLM : H →L[ℝ] G :=
  ContinuousLinearMap.piLpMap 2 fun _ ↦ scalarGradientCLM

/-- Sum of the actual weak diagonal partial derivatives. -/
def divergenceCLM : H →L[ℝ] DerivLp n 2 univ :=
  ∑ j, (wkpCoordinateCLM (singleDerivIndex n j)).comp (PiLp.proj 2 _ j)

/-- The divergence map is exactly the sum of weak velocity partials. -/
theorem divergenceCLM_apply (U : H) :
    divergenceCLM U = ∑ j, wkpCoordinateCLM (singleDerivIndex n j) (U j) := by
  simp only [divergenceCLM, sum_apply, ContinuousLinearMap.comp_apply]
  rfl

/-- Mass and full gradient are the two orthogonal parts of the H¹ graph norm. -/
theorem norm_sq_eq_mass_add_gradient (U : H) :
    ‖U‖ ^ 2 = ‖massCLM U‖ ^ 2 + ‖gradientCLM U‖ ^ 2 := by
  classical
  have hm : ‖massCLM U‖ ^ 2 = ∑ i, ‖wkpBaseCoordinateCLM (U i)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    rfl
  have hg : ‖gradientCLM U‖ ^ 2 =
      ∑ i, ∑ j, ‖wkpCoordinateCLM (singleDerivIndex n j) (U i)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro i _
    rw [PiLp.norm_sq_eq_of_L2]
    rfl
  rw [PiLp.norm_sq_eq_of_L2, hm, hg, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact ambient_norm_sq_eq_base_sq_add_sum_deriv_sq (U i).val

/-- The squared gradient norm of a scalar field is the sum of its squared partial norms. -/
theorem norm_scalarGradientCLM_sq (u : H¹(ℝ^n)) :
    ‖scalarGradientCLM u‖ ^ 2 =
      ∑ j : Fin n, ‖wkpCoordinateCLM (singleDerivIndex n j) u‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

/-- Each partial derivative norm of a scalar field is at most its gradient norm. -/
theorem norm_partial_le_norm_scalarGradientCLM (u : H¹(ℝ^n)) (j : Fin n) :
    ‖wkpCoordinateCLM (singleDerivIndex n j) u‖ ≤ ‖scalarGradientCLM u‖ :=
  PiLp.norm_apply_le (scalarGradientCLM u) j

/-- The full gradient norm is at most the `H¹` graph norm. -/
theorem norm_gradientCLM_le (U : H) : ‖gradientCLM U‖ ≤ ‖U‖ := by
  have h := norm_sq_eq_mass_add_gradient U
  have hm := sq_nonneg ‖massCLM U‖
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by linarith)

/-- Separate mass and gradient radii imply boundedness in the complete correction space. -/
theorem isBounded_range_of_mass_gradient_bounds {ι : Type*} (U : ι → H)
    (r₀ r₁ : ℝ) (hmass : ∀ i, ‖massCLM (U i)‖ ≤ r₀)
    (hgradient : ∀ i, ‖gradientCLM (U i)‖ ≤ r₁) : Bornology.IsBounded (range U) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨r₀ + r₁, ?_⟩
  rintro _ ⟨i, rfl⟩
  have hnorm := norm_sq_eq_mass_add_gradient (U i)
  have hm := norm_nonneg (massCLM (U i))
  have hg := norm_nonneg (gradientCLM (U i))
  have hu := norm_nonneg (U i)
  have hcross := mul_nonneg hm hg
  have hsum : ‖U i‖ ≤ ‖massCLM (U i)‖ + ‖gradientCLM (U i)‖ := by
    nlinarith
  exact hsum.trans (add_le_add (hmass i) (hgradient i))

/-- Eventually satisfied compact-tested equations yield a solenoidal whole-space correction
that also satisfies every continuous linear constraint met by all approximate corrections, for
instance invariance under a symmetry group, given by the family `fun g ↦ A g - id`.
The nonlinear term is the actual Lebesgue convection of its bounded reconstruction.
Every approximate correction obeys the same separate mass and gradient radii. -/
theorem exists_correction_of_eventually_tested_eq_of_constraints
    {ι T K C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C] (l : Filter ι) [l.NeBot]
    (U : ι → H) (r₀ r₁ : ℝ) (hmass : ∀ i, ‖massCLM (U i)‖ ≤ r₀)
    (hgradient : ∀ i, ‖gradientCLM (U i)‖ ≤ r₁)
    (hdiv : ∀ i, divergenceCLM (U i) = 0)
    (constraints : K → H →L[ℝ] C) (hconstraints : ∀ i k, constraints k (U i) = 0)
    (R : H →L[ℝ] H)
    (hR : ∀ u, divergenceCLM u = 0 → divergenceCLM (R u) = 0)
    (Φ : T → Fin n → W^{1,∞}(ℝ^n))
    (ψ : T → 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ))
    (hψ : ∀ t i j, ∀ᵐ x ∂domainMeasure n univ,
      testGradient (Φ t) (i, j) x = 0 ∨ ψ t x = 1)
    (linear : T → StrongDual ℝ H) (forcing : T → ℝ)
    (hequation : ∀ t, ∀ᶠ i in l,
      linear t (U i) + testedConvection (Φ t) (fun j ↦ R (U i) j) = forcing t) :
    ∃ u : H, ‖massCLM u‖ ≤ r₀ ∧ ‖gradientCLM u‖ ≤ r₁ ∧
      divergenceCLM u = 0 ∧ (∀ k, constraints k u = 0) ∧
      ∀ t, linear t u + testedConvection (Φ t) (fun j ↦ R u j) = forcing t := by
  classical
  have hidentity (t : T) (u : H) (hu : divergenceCLM u = 0) :
      testedConvection (Φ t) (fun j ↦ R u j) =
        testedFlux (testGradient (Φ t)) (cutoffValues (ψ t) (R u)) := by
    rw [testedConvection_eq_testedFlux (Φ t) _
      (by simpa only [divergenceCLM_apply] using hR u hu)]
    exact testedFlux_eq_of_multiplier_eq _ _ _
      (testGradient_mul_cutoffValues (Φ t) (ψ t) (hψ t) (R u))
  have hcompact (t : T) : IsCompactOperator ((cutoffValues (ψ t)).comp R) :=
    (cutoffValues_isCompactOperator (ψ t)).comp_clm R
  have hcontinuous (t : T) : Continuous (testedFlux (testGradient (Φ t))) := by
    exact ((ContinuousLinearMap.l2MatrixTransport (testGradient (Φ t))).continuous.inner
      continuous_id).neg
  let cons : Option K → H →L[ℝ] (DerivLp n 2 univ × C) := fun j ↦
    j.elim ((ContinuousLinearMap.inl ℝ _ _).comp divergenceCLM) fun k ↦
      (ContinuousLinearMap.inr ℝ _ _).comp (constraints k)
  have hcons (i : ι) (j : Option K) : cons j (U i) = 0 := by
    cases j with
    | none => simp [cons, hdiv i]
    | some k => simp [cons, hconstraints i k]
  obtain ⟨u, hmassU, hgradientU, hconsU, heqU⟩ :=
    PDE.Analysis.Variational.exists_solution_of_eventually_eq l U
      (isBounded_range_of_mass_gradient_bounds U r₀ r₁ hmass hgradient)
      massCLM gradientCLM r₀ r₁ (Eventually.of_forall hmass) (Eventually.of_forall hgradient)
      cons (Eventually.of_forall hcons)
      linear (fun t ↦ (cutoffValues (ψ t)).comp R) hcompact
      (fun t ↦ testedFlux (testGradient (Φ t))) hcontinuous forcing
      (fun t ↦ (hequation t).mono fun i hi ↦ by
        simpa only [ContinuousLinearMap.comp_apply, ← hidentity t (U i) (hdiv i)] using hi)
  have hdivU : divergenceCLM u = 0 := by
    simpa [cons] using congrArg Prod.fst (hconsU none)
  refine ⟨u, hmassU, hgradientU, hdivU, fun k ↦ ?_, fun t ↦ ?_⟩
  · simpa [cons] using congrArg Prod.snd (hconsU (some k))
  · simpa only [ContinuousLinearMap.comp_apply, ← hidentity t u hdivU] using heqU t

/-- Eventually satisfied compact-tested equations yield a solenoidal whole-space correction.
The nonlinear term is the actual Lebesgue convection of its bounded reconstruction.
Every approximate correction obeys the same separate mass and gradient radii. -/
theorem exists_correction_of_eventually_tested_eq
    {ι T : Type*} (l : Filter ι) [l.NeBot] (U : ι → H)
    (r₀ r₁ : ℝ) (hmass : ∀ i, ‖massCLM (U i)‖ ≤ r₀)
    (hgradient : ∀ i, ‖gradientCLM (U i)‖ ≤ r₁)
    (hdiv : ∀ i, divergenceCLM (U i) = 0)
    (R : H →L[ℝ] H)
    (hR : ∀ u, divergenceCLM u = 0 → divergenceCLM (R u) = 0)
    (Φ : T → Fin n → W^{1,∞}(ℝ^n))
    (ψ : T → 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ))
    (hψ : ∀ t i j, ∀ᵐ x ∂domainMeasure n univ,
      testGradient (Φ t) (i, j) x = 0 ∨ ψ t x = 1)
    (linear : T → StrongDual ℝ H) (forcing : T → ℝ)
    (hequation : ∀ t, ∀ᶠ i in l,
      linear t (U i) + testedConvection (Φ t) (fun j ↦ R (U i) j) = forcing t) :
    ∃ u : H, ‖massCLM u‖ ≤ r₀ ∧ ‖gradientCLM u‖ ≤ r₁ ∧
      divergenceCLM u = 0 ∧
      ∀ t, linear t u + testedConvection (Φ t) (fun j ↦ R u j) = forcing t := by
  obtain ⟨u, hm, hg, hd, -, he⟩ := exists_correction_of_eventually_tested_eq_of_constraints l U
    r₀ r₁ hmass hgradient hdiv (fun e : Empty ↦ e.elim : Empty → H →L[ℝ] H)
    (fun _ e ↦ e.elim) R hR Φ ψ hψ linear forcing hequation
  exact ⟨u, hm, hg, hd, he⟩

end NavierStokes.Stationary
