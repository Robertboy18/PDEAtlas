/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.FiniteRankTransport
public import PDE.Analysis.Operator.CompactConvergence
public import PDE.Spaces.Sobolev.Calculus.Product.IntegrationByParts
public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Cutoff
public import PDE.Spaces.Sobolev.Variational.Spaces.WholeSpaceHilbert
public import PDE.Analysis.Normed.Operator.FiniteProduct

/-!
# Compact testing of stationary convection

Testing against a bounded Sobolev field moves the derivative off the velocity.
For divergence-free whole-space H¹ fields the resulting flux is a quadratic
L² pairing with the test-gradient matrix. Its continuity needs only strong
convergence of local observations, rather than global compactness of H¹.

The flux satisfies `|testedFlux D u - testedFlux D v| ≤ ‖D‖ (‖u‖ + ‖v‖) ‖u - v‖`
(`abs_testedFlux_sub_le`). The velocity values lie in the finite Hilbert product of scalar `L²`
spaces and `D` in the finite Hilbert product of its scalar `L∞` entries; the bound is in these
product norms, not in a pointwise matrix operator norm. A smooth compact cutoff equal to one
wherever the test gradient is nonzero preserves the flux (`testGradient_mul_cutoffValues`), and
its observation of `H¹` values is compact (`cutoffValues_isCompactOperator`), so for
divergence-free velocities bounded weak `H¹` convergence passes the tested convection to the
limit (`tendsto_testedConvection_of_weak`).

The H¹ velocity here is the correction, including its finite-rank reconstruction.
The published background has inverse-radius decay and is not asserted to be in
whole-space L². Its contributions belong to the linear and forcing terms, or to
an affine local observation in a separate application.

Hou, Wang and Yang make the same passage in the convection term when they take weak limits of
(4.37) as `R → ∞` (Section 4.3).

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 4.3, (4.37) and the weak
  limit that follows it, p. 31.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal RealInnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert
open scoped Topology Distributions

namespace NavierStokes.Stationary

variable {n : ℕ}

private theorem multiplier_sum
    (a : DerivLp n ∞ univ) (u : Fin n → DerivLp n 2 univ) :
    a • (∑ j, u j) = ∑ j, a • u j := by
  classical
  have h (s : Finset (Fin n)) : a • (∑ j ∈ s, u j) = ∑ j ∈ s, a • u j := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, Lp.smul_zero]
    | @insert j s hj hs =>
      simp only [Finset.sum_insert hj, Lp.add_smul, hs]
  simpa using h Finset.univ

private theorem multiplier_inner_swap
    (a : DerivLp n ∞ univ) (u v : DerivLp n 2 univ) :
    ⟪a • u, v⟫ = ⟪a • v, u⟫ := by
  rw [Lp.inner_lpSMul_left, real_inner_comm]

/-- Velocity values in the finite Hilbert product of spatial L² spaces. -/
def massValues (U : Fin n → H¹(ℝ^n)) :
    PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 univ) :=
  WithLp.toLp 2 (fun i ↦ wkpBaseCoordinateCLM (U i))

/-- The actual weak derivative matrix of the testing field. -/
def testGradient (Φ : Fin n → W^{1,∞}(ℝ^n)) :
    PiLp 2 (fun _ : Fin n × Fin n ↦ DerivLp n ∞ univ) :=
  WithLp.toLp 2 (fun ij ↦ wkpCoordinateCLM (singleDerivIndex n ij.2) (Φ ij.1))

/-- Convection tested against a bounded field, retaining the weak velocity derivative. -/
def testedConvection (Φ : Fin n → W^{1,∞}(ℝ^n)) (U : Fin n → H¹(ℝ^n)) : ℝ :=
  ∑ i, ∑ j, ⟪wkpBaseCoordinateCLM (Φ i) • wkpBaseCoordinateCLM (U j),
    wkpCoordinateCLM (singleDerivIndex n j) (U i)⟫

/-- Flux after the velocity derivative has been moved onto the testing field. -/
def testedFlux (D : PiLp 2 (fun _ : Fin n × Fin n ↦ DerivLp n ∞ univ))
    (u : PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 univ)) : ℝ :=
  -⟪ContinuousLinearMap.l2MatrixTransport D u, u⟫

/-- The flux is the ordinary Lebesgue pairing of the test gradient and velocity tensor. -/
theorem testedFlux_eq_integrals
    (D : PiLp 2 (fun _ : Fin n × Fin n ↦ DerivLp n ∞ univ))
    (u : PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 univ)) :
    testedFlux D u = -(∑ i, ∑ j, ∫ x, D (i, j) x * u j x * u i x) := by
  classical
  simp only [testedFlux, PiLp.inner_apply,
    ContinuousLinearMap.l2MatrixTransport_apply, sum_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [L2.inner_def]
  simp only [domainMeasure, Measure.restrict_univ]
  apply integral_congr_ae
  have hmul := Lp.coeFn_lpSMul (r := 2) (D (i, j)) (u j)
  simp only [domainMeasure, Measure.restrict_univ] at hmul
  filter_upwards [hmul] with x hx
  simp only [hx, smul_eq_mul, RCLike.inner_apply, conj_trivial, Pi.mul_apply]
  ring

/-- Integration by parts identifies the actual convection with the quadratic mass flux. -/
theorem testedConvection_eq_testedFlux
    (Φ : Fin n → W^{1,∞}(ℝ^n)) (U : Fin n → H¹(ℝ^n))
    (hdiv : ∑ j, wkpCoordinateCLM (singleDerivIndex n j) (U j) = 0) :
    testedConvection Φ U = testedFlux (testGradient Φ) (massValues U) := by
  classical
  have hrow (i : Fin n) :
      (∑ j, ⟪wkpBaseCoordinateCLM (Φ i) • wkpBaseCoordinateCLM (U j),
        wkpCoordinateCLM (singleDerivIndex n j) (U i)⟫) =
      -(∑ j, ⟪wkpCoordinateCLM (singleDerivIndex n j) (Φ i) •
        wkpBaseCoordinateCLM (U j), wkpBaseCoordinateCLM (U i)⟫) := by
    have hterm (j : Fin n) :
        ⟪wkpBaseCoordinateCLM (Φ i) • wkpBaseCoordinateCLM (U j),
          wkpCoordinateCLM (singleDerivIndex n j) (U i)⟫ +
        ⟪wkpBaseCoordinateCLM (Φ i) •
          wkpCoordinateCLM (singleDerivIndex n j) (U j), wkpBaseCoordinateCLM (U i)⟫ =
        -⟪wkpCoordinateCLM (singleDerivIndex n j) (Φ i) •
          wkpBaseCoordinateCLM (U j), wkpBaseCoordinateCLM (U i)⟫ := by
      have h := inner_mul_deriv_add_inner_mul_deriv_univ (Φ i) j (U i) (U j)
      change ⟪wkpBaseCoordinateCLM (Φ i) •
          wkpCoordinateCLM (singleDerivIndex n j) (U i), wkpBaseCoordinateCLM (U j)⟫ +
        ⟪wkpBaseCoordinateCLM (Φ i) •
          wkpCoordinateCLM (singleDerivIndex n j) (U j), wkpBaseCoordinateCLM (U i)⟫ =
        -⟪wkpCoordinateCLM (singleDerivIndex n j) (Φ i) •
          wkpBaseCoordinateCLM (U i), wkpBaseCoordinateCLM (U j)⟫ at h
      rw [multiplier_inner_swap (wkpBaseCoordinateCLM (Φ i)),
        multiplier_inner_swap (wkpCoordinateCLM (singleDerivIndex n j) (Φ i))] at h
      exact h
    have hzero :
        (∑ j, ⟪wkpBaseCoordinateCLM (Φ i) •
          wkpCoordinateCLM (singleDerivIndex n j) (U j),
          wkpBaseCoordinateCLM (U i)⟫) = 0 := by
      rw [← sum_inner, ← multiplier_sum, hdiv, Lp.smul_zero, inner_zero_left]
    have hparts := Finset.sum_congr (s₁ := Finset.univ) rfl fun j _ ↦ hterm j
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib] at hparts
    linarith
  simp only [testedConvection, testedFlux, PiLp.inner_apply,
    ContinuousLinearMap.l2MatrixTransport_apply, massValues, testGradient, sum_inner]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ hrow i

/-- The Hilbert norm of the bounded test-gradient matrix controls the flux. -/
theorem abs_testedFlux_le
    (D : PiLp 2 (fun _ : Fin n × Fin n ↦ DerivLp n ∞ univ))
    (u : PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 univ)) :
    |testedFlux D u| ≤ ‖D‖ * ‖u‖ ^ 2 := by
  rw [testedFlux, abs_neg]
  calc
    _ ≤ ‖ContinuousLinearMap.l2MatrixTransport D u‖ * ‖u‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖D‖ * ‖u‖) * ‖u‖ := mul_le_mul_of_nonneg_right
      (ContinuousLinearMap.norm_l2MatrixTransportLinear_le D u) (norm_nonneg _)
    _ = _ := by ring

/-- The quadratic flux is Lipschitz on every bounded mass ball, with its test-gradient norm. -/
theorem abs_testedFlux_sub_le
    (D : PiLp 2 (fun _ : Fin n × Fin n ↦ DerivLp n ∞ univ))
    (u v : PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 univ)) :
    |testedFlux D u - testedFlux D v| ≤ ‖D‖ * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  let A := ContinuousLinearMap.l2MatrixTransport D
  have hidentity : testedFlux D u - testedFlux D v =
      -(⟪A (u - v), u⟫ + ⟪A v, u - v⟫) := by
    simp only [testedFlux, map_sub, inner_sub_left, inner_sub_right, A]
    ring
  rw [hidentity, abs_neg]
  calc
    _ ≤ |⟪A (u - v), u⟫| + |⟪A v, u - v⟫| := abs_add_le _ _
    _ ≤ ‖A (u - v)‖ * ‖u‖ + ‖A v‖ * ‖u - v‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (‖D‖ * ‖u - v‖) * ‖u‖ + (‖D‖ * ‖v‖) * ‖u - v‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_right
          (ContinuousLinearMap.norm_l2MatrixTransportLinear_le D (u - v)) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right
          (ContinuousLinearMap.norm_l2MatrixTransportLinear_le D v) (norm_nonneg _))
    _ = _ := by ring

/-- Strong convergence in mass suffices for a fixed bounded test gradient. -/
theorem tendsto_testedFlux
    (D : PiLp 2 (fun _ : Fin n × Fin n ↦ DerivLp n ∞ univ))
    {ι : Type*} {l : Filter ι}
    {u : ι → PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 univ)}
    {v : PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 univ)}
    (hu : Tendsto u l (𝓝 v)) :
    Tendsto (fun k ↦ testedFlux D (u k)) l (𝓝 (testedFlux D v)) := by
  exact ((ContinuousLinearMap.l2MatrixTransport D).continuous.tendsto v |>.comp hu).inner
    hu |>.neg

/-- Equal locally weighted velocities give equal tested flux, without global equality. -/
theorem testedFlux_eq_of_multiplier_eq
    (D : PiLp 2 (fun _ : Fin n × Fin n ↦ DerivLp n ∞ univ))
    (u v : PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 univ))
    (h : ∀ i j k, D (i, j) • u k = D (i, j) • v k) :
    testedFlux D u = testedFlux D v := by
  classical
  simp only [testedFlux, PiLp.inner_apply,
    ContinuousLinearMap.l2MatrixTransport_apply, sum_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [h i j j, Lp.inner_lpSMul_left, h i j i, ← Lp.inner_lpSMul_left]

/-- A compact local observation passes the actual quadratic flux through a bounded weak limit.
The multiplier identities express agreement wherever the test gradient is nonzero. -/
theorem tendsto_testedFlux_of_compact_observation
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (D : PiLp 2 (fun _ : Fin n × Fin n ↦ DerivLp n ∞ univ))
    (J : H →L[ℝ] PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 univ))
    (hJ : IsCompactOperator J)
    (values : H → PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 univ))
    (hlocal : ∀ x i j k, D (i, j) • values x k = D (i, j) • J x k)
    {ι : Type*} {l : Filter ι} {u : ι → H} {v : H}
    (hbounded : Bornology.IsBounded (range u))
    (hu : Tendsto (fun k ↦ toWeakSpace ℝ H (u k)) l (𝓝 (toWeakSpace ℝ H v))) :
    Tendsto (fun k ↦ testedFlux D (values (u k))) l (𝓝 (testedFlux D (values v))) := by
  have hstrong := PDE.Analysis.tendsto_compactOperator_of_tendsto_weak_of_bounded
    J hJ hbounded hu
  have hflux := tendsto_testedFlux D hstrong
  simpa only [testedFlux_eq_of_multiplier_eq D _ _ (hlocal _)] using hflux

/-- Compactly observed values of a whole-space Sobolev velocity. -/
def cutoffValues (ψ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ)) :
    PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)) →L[ℝ]
      PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 univ) :=
  ContinuousLinearMap.piLpMap 2 fun _ : Fin n ↦
    wkpBaseCoordinateCLM.comp (cutoffCLM ψ)

/-- Cutoff observations are compact; no global compact embedding is needed. -/
theorem cutoffValues_isCompactOperator
    (ψ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ)) :
    IsCompactOperator (cutoffValues ψ) :=
  ContinuousLinearMap.isCompactOperator_piLpMap 2 _ fun _ ↦
    RellichKondrachov.cutoffBaseCoordinate_isCompactOperator (by norm_num) ψ

/-- A cutoff equal to one wherever the test gradient is nonzero preserves its flux. -/
theorem testGradient_mul_cutoffValues
    (Φ : Fin n → W^{1,∞}(ℝ^n))
    (ψ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ))
    (hψ : ∀ i j, ∀ᵐ x ∂domainMeasure n univ,
      testGradient Φ (i, j) x = 0 ∨ ψ x = 1)
    (U : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) (i j k : Fin n) :
    testGradient Φ (i, j) • massValues (fun k ↦ U k) k =
      testGradient Φ (i, j) • cutoffValues ψ U k := by
  apply Lp.ext
  have hc := cutoffCLM_base_apply_ae (n := n) (p := 2) (Ω := univ) ψ (U k)
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (testGradient Φ (i, j))
      (massValues (fun k ↦ U k) k),
    Lp.coeFn_lpSMul (r := 2) (testGradient Φ (i, j)) (cutoffValues ψ U k), hc,
    hψ i j] with x hx hy hc' hψ'
  rw [hx, hy]
  change testGradient Φ (i, j) x * wkpBaseCoordinateCLM (U k) x =
    testGradient Φ (i, j) x * wkpBaseCoordinateCLM (cutoffCLM ψ (U k)) x
  change wkpBaseCoordinateCLM (cutoffCLM ψ (U k)) x =
    ψ x * wkpBaseCoordinateCLM (U k) x at hc'
  rw [hc']
  rcases hψ' with hzero | hone
  · simp [hzero]
  · simp [hone]

/-- Bounded weak whole-space H¹ convergence passes stationary convection against a fixed test.
The compact cutoff covers the support of its gradient, and the velocities are solenoidal. -/
theorem tendsto_testedConvection_of_weak
    (Φ : Fin n → W^{1,∞}(ℝ^n))
    (ψ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ))
    (hψ : ∀ i j, ∀ᵐ x ∂domainMeasure n univ,
      testGradient Φ (i, j) x = 0 ∨ ψ x = 1)
    {ι : Type*} {l : Filter ι}
    {U : ι → PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))}
    {V : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))}
    (hbounded : Bornology.IsBounded (range U))
    (hweak : Tendsto (fun k ↦ toWeakSpace ℝ _ (U k)) l (𝓝 (toWeakSpace ℝ _ V)))
    (hdiv : ∀ k, ∑ j, wkpCoordinateCLM (singleDerivIndex n j) (U k j) = 0)
    (hdivV : ∑ j, wkpCoordinateCLM (singleDerivIndex n j) (V j) = 0) :
    Tendsto (fun k ↦ testedConvection Φ (fun i ↦ U k i)) l
      (𝓝 (testedConvection Φ (fun i ↦ V i))) := by
  have hflux := tendsto_testedFlux_of_compact_observation (testGradient Φ)
    (cutoffValues ψ) (cutoffValues_isCompactOperator ψ)
    (fun x ↦ massValues (fun i ↦ x i))
    (testGradient_mul_cutoffValues Φ ψ hψ) hbounded hweak
  simpa only [← testedConvection_eq_testedFlux Φ _ (hdiv _),
    ← testedConvection_eq_testedFlux Φ _ hdivV] using hflux

end NavierStokes.Stationary
