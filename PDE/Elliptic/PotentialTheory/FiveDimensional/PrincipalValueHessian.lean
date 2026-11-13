/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.PolarTruncation
public import PDE.Analysis.Integration.PrincipalValue

/-!
# Principal values of the five-dimensional Newtonian Hessian

Spherical truncations of the classical Hessian converge against every smooth
compact test function. Their discrepancy from the distributional Hessian is
`-(δᵢⱼ / 5) δ₀`. Translation gives the corresponding convolution identity.
The principal-value contract includes integrability of each positive truncation.

The final vector coefficient bounds are elementary inequalities for the four
mixed axial components.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Filter LineDeriv TopologicalSpace
open scoped Distributions ENNReal Topology
open PDE.Analysis SobolevSpace

namespace PotentialTheory

/-- Pointwise existence of the spherical five-dimensional Hessian principal
value, using the general PDE principal-value
contract with integrable truncations in the full lifted distance.
-/
def HasFiveDimensionalHessianPrincipalValueAt
    (i j : Fin 5) (F : ℝ^5 → ℝ)
    (X : ℝ^5) (v : ℝ) : Prop :=
  PDE.Analysis.HasPrincipalValueAt Set.univ
    (fun X Y ↦ iteratedPartialDeriv (n := 5) [i, j]
      (fundamentalSolution 5) (X - Y)) F X v

/-- Every Cartesian Hessian component has a spherical principal value against
a test function, with the limit given by the integrable radial-angular
cancellation formula.
-/
theorem fundamentalSolution_five_classicalHessian_principalValue_tendsto
    (i j : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    Tendsto (fun ε : ℝ ↦
      ∫ X in {X : ℝ^5 | ε < ‖X‖},
        iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X *
          φ.toFun X)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ r in Set.Ioi (0 : ℝ), r⁻¹ *
        ∫ ω : Metric.sphere (0 : ℝ^5) 1,
          ((15 / (8 * Real.pi ^ 2)) *
              (ω : ℝ^5) i *
              (ω : ℝ^5) j -
            (3 / (8 * Real.pi ^ 2)) * (if i = j then 1 else 0)) *
            φ.toFun (r • (ω : ℝ^5))
          ∂(volume : Measure ℝ^5).toSphere)) := by
  apply (fiveDimensionalHessianAngularRadial_tendsto i j φ).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (fundamentalSolution_five_classicalHessian_polar ε hε i j φ).symm

/-- The spherical principal-value pairing of one classical Hessian component
with a test function.
-/
noncomputable def fiveDimensionalHessianPrincipalValue
    (i j : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) : ℝ :=
  ∫ r in Set.Ioi (0 : ℝ), r⁻¹ *
    ∫ ω : Metric.sphere (0 : ℝ^5) 1,
      ((15 / (8 * Real.pi ^ 2)) *
          (ω : ℝ^5) i *
          (ω : ℝ^5) j -
        (3 / (8 * Real.pi ^ 2)) * (if i = j then 1 else 0)) *
        φ.toFun (r • (ω : ℝ^5))
      ∂(volume : Measure ℝ^5).toSphere

/-- Spherical truncations converge to the named principal-value pairing.
-/
theorem fiveDimensionalHessianPrincipalValue_tendsto
    (i j : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    Tendsto (fun ε : ℝ ↦
      ∫ X in {X : ℝ^5 | ε < ‖X‖},
        iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X *
          φ.toFun X)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (fiveDimensionalHessianPrincipalValue i j φ)) := by
  simpa [fiveDimensionalHessianPrincipalValue] using
    fundamentalSolution_five_classicalHessian_principalValue_tendsto i j φ

/-- A test function which vanishes at the Newtonian pole sees no Dirac part:
its spherical principal value converges to the distributional Hessian pairing.
-/
theorem fundamentalSolution_five_principalValue_tendsto_distributional_of_zero
    (i j : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ))
    (hφ0 : φ.toFun 0 = 0) :
    Tendsto (fun ε : ℝ ↦
      ∫ X in {X : ℝ^5 | ε < ‖X‖},
        iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X *
          φ.toFun X)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ X : ℝ^5,
        (fundamentalSolution 5) X *
          iteratedPartialDeriv (n := 5) [i, j] φ.toFun X)) := by
  let f : ℝ^5 → ℝ := fun X ↦
    iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X * φ.toFun X
  obtain ⟨hfInt, hdist⟩ :=
    fundamentalSolution_five_distributionalHessian_eq_classical_of_zero j i φ hφ0
  have hcomm (X : ℝ^5) : iteratedPartialDeriv (n := 5) [i, j] φ.toFun X =
      iteratedPartialDeriv (n := 5) [j, i] φ.toFun X :=
    PDE.partialDeriv_partialDeriv_comm i j (φ.contDiff.of_le (WithTop.coe_le_coe.mpr le_top)) X
  have hS (ε : ℝ) : MeasurableSet {X : ℝ^5 | ε < ‖X‖} :=
    measurableSet_lt measurable_const measurable_norm
  simp only [hcomm, hdist]
  refine (tendsto_integral_filter_of_dominated_convergence (fun X ↦ ‖f X‖)
    (.of_forall fun ε ↦ hfInt.aestronglyMeasurable.indicator (hS ε))
    (.of_forall fun ε ↦ .of_forall fun X ↦ norm_indicator_le_norm_self _ _) hfInt.norm ?_).congr
      fun ε ↦ integral_indicator (hS ε)
  filter_upwards [(Set.countable_singleton (0 : ℝ^5)).ae_notMem volume] with X hX
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (norm_pos_iff.2 hX)] with ε hε
  exact (Set.indicator_of_mem (show X ∈ {X : ℝ^5 | ε < ‖X‖} from hε.2) f).symm

/-- For a fixed Hessian component, the difference between the distributional
pairing and any spherical principal-value limit depends only on the value of
the test function at the pole.
-/
theorem fundamentalSolution_five_discrepancy_eq_of_origin_eq
    (i j : Fin 5) (φ ψ : 𝓓((⊤ : Opens ℝ^5), ℝ)) (Lφ Lψ : ℝ)
    (hφ : Tendsto (fun δ : ℝ ↦
      ∫ X in {X : ℝ^5 | δ < ‖X‖},
        iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X *
          φ.toFun X) (nhdsWithin 0 (Set.Ioi 0)) (nhds Lφ))
    (hψ : Tendsto (fun δ : ℝ ↦
      ∫ X in {X : ℝ^5 | δ < ‖X‖},
        iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X *
          ψ.toFun X) (nhdsWithin 0 (Set.Ioi 0)) (nhds Lψ))
    (horigin : φ.toFun 0 = ψ.toFun 0) :
    (∫ X : ℝ^5, (fundamentalSolution 5) X *
        iteratedPartialDeriv (n := 5) [i, j] φ.toFun X) - Lφ =
      (∫ X : ℝ^5, (fundamentalSolution 5) X *
        iteratedPartialDeriv (n := 5) [i, j] ψ.toFun X) - Lψ := by
  let θ : 𝓓((⊤ : Opens ℝ^5), ℝ) := φ - ψ
  have hlimitEq : (∫ X : ℝ^5, (fundamentalSolution 5) X *
      iteratedPartialDeriv (n := 5) [i, j] θ.toFun X) = Lφ - Lψ := by
    refine tendsto_nhds_unique
      (fundamentalSolution_five_principalValue_tendsto_distributional_of_zero i j θ
        (by simpa [θ, sub_eq_zero] using horigin)) ((hφ.sub hψ).congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    rw [← integral_sub (fundamentalSolution_five_classicalHessian_integrableOn δ hδ i j φ)
      (fundamentalSolution_five_classicalHessian_integrableOn δ hδ i j ψ)]
    exact integral_congr_ae (.of_forall fun X ↦ by simp [θ, mul_sub])
  have hpair : (∫ X : ℝ^5, (fundamentalSolution 5) X *
      iteratedPartialDeriv (n := 5) [i, j] θ.toFun X) =
      (∫ X : ℝ^5, (fundamentalSolution 5) X * iteratedPartialDeriv (n := 5) [i, j] φ.toFun X) -
        ∫ X : ℝ^5, (fundamentalSolution 5) X * iteratedPartialDeriv (n := 5) [i, j] ψ.toFun X := by
    rw [← integral_sub (fundamentalSolution_five_mul_testHessian_integrable i j φ)
      (fundamentalSolution_five_mul_testHessian_integrable i j ψ)]
    refine integral_congr_ae (.of_forall fun X ↦ ?_)
    dsimp only
    rw [← mul_sub]
    congr 1
    simpa [θ] using congrFun (PDE.iteratedPartialDeriv_sub_of_contDiff [i, j]
      (φ.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (ψ.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))) X
  linarith

/-- Orthogonal coordinate symmetry forces all five diagonal local
discrepancies to be equal.
-/
theorem fundamentalSolution_five_diagonal_discrepancy_eq
    (i j : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    (∫ X : ℝ^5, (fundamentalSolution 5) X *
        iteratedPartialDeriv (n := 5) [i, i] φ.toFun X) -
        fiveDimensionalHessianPrincipalValue i i φ =
      (∫ X : ℝ^5, (fundamentalSolution 5) X *
        iteratedPartialDeriv (n := 5) [j, j] φ.toFun X) -
        fiveDimensionalHessianPrincipalValue j j φ := by
  let ψ := fiveDimensionalSwapTestFunction i j φ
  have hi := fiveDimensionalHessianPrincipalValue_tendsto i i φ
  have hj := fiveDimensionalHessianPrincipalValue_tendsto j j φ
  have hψ : Tendsto (fun δ : ℝ ↦
      ∫ X in {X : ℝ^5 | δ < ‖X‖},
        iteratedPartialDeriv (n := 5) [i, i] (fundamentalSolution 5) X *
          ψ.toFun X)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (fiveDimensionalHessianPrincipalValue j j φ)) := by
    apply hj.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (fundamentalSolution_five_classical_diagonal_truncation_swap
      δ hδ i j φ).symm
  have horigin : φ.toFun 0 = ψ.toFun 0 := by
    change φ.toFun 0 = fiveDimensionalSwapTestFunction i j φ 0
    rw [fiveDimensionalSwapTestFunction_apply]
    simp
  have hdisc := fundamentalSolution_five_discrepancy_eq_of_origin_eq
    i i φ ψ (fiveDimensionalHessianPrincipalValue i i φ)
      (fiveDimensionalHessianPrincipalValue j j φ) hi hψ horigin
  rw [fundamentalSolution_five_distributional_diagonal_swap i j φ] at hdisc
  exact hdisc

/-- Reflection symmetry eliminates every mixed local discrepancy.
-/
theorem fundamentalSolution_five_mixed_discrepancy_zero
    (i j : Fin 5) (hij : i ≠ j) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    (∫ X : ℝ^5, (fundamentalSolution 5) X *
        iteratedPartialDeriv (n := 5) [i, j] φ.toFun X) -
      fiveDimensionalHessianPrincipalValue i j φ = 0 := by
  let ψ := fiveDimensionalSignFlipTestFunction i φ
  have hφ := fiveDimensionalHessianPrincipalValue_tendsto i j φ
  have hψ : Tendsto (fun δ : ℝ ↦ ∫ X in {X : ℝ^5 | δ < ‖X‖},
      iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X * ψ.toFun X)
      (𝓝[>] 0) (𝓝 (-fiveDimensionalHessianPrincipalValue i j φ)) := by
    refine hφ.neg.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (fundamentalSolution_five_classical_mixed_truncation_signFlip δ hδ i j hij φ).symm
  have hdisc := fundamentalSolution_five_discrepancy_eq_of_origin_eq i j φ ψ _ _ hφ hψ (by
    change φ.toFun 0 = φ.toFun (PDE.Common.coordinateReflection i 0)
    rw [(PDE.Common.coordinateReflection_eq_zero_iff i 0).mpr rfl])
  have hcomm (θ : 𝓓((⊤ : Opens ℝ^5), ℝ)) (X : ℝ^5) :
      iteratedPartialDeriv (n := 5) [j, i] θ.toFun X =
        iteratedPartialDeriv (n := 5) [i, j] θ.toFun X :=
    PDE.partialDeriv_partialDeriv_comm j i (θ.contDiff.of_le (WithTop.coe_le_coe.mpr le_top)) X
  have hflip := fundamentalSolution_five_distributional_mixed_signFlip i j hij φ
  simp only [hcomm] at hflip
  rw [hflip] at hdisc
  linarith

/-- The classical Hessian of the five-dimensional Newtonian kernel is traceless
away from its pole. Thus the local Dirac mass in the distributional Hessian
cannot be recovered by pointwise differentiation alone.
-/
theorem fundamentalSolution_five_classicalHessian_trace_zero
    (X : ℝ^5) (hX : X ≠ 0) :
    ∑ i : Fin 5,
      iteratedPartialDeriv (n := 5) [i, i] (fundamentalSolution 5) X = 0 := by
  have : Fact (0 < 5) := ⟨by norm_num⟩
  have h := PotentialTheory.laplacian_fundamentalSolution_eq_zero 5 X hX
  exact h

/-- The five diagonal spherical principal-value limits sum to zero. The local
Dirac mass is therefore entirely the difference between the distributional
trace and the classical punctured trace.
-/
theorem fundamentalSolution_five_principalValue_diagonal_sum_zero
    (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    (∑ i : Fin 5,
      ∫ r in Set.Ioi (0 : ℝ), r⁻¹ *
        ∫ ω : Metric.sphere (0 : ℝ^5) 1,
          ((15 / (8 * Real.pi ^ 2)) *
              (ω : ℝ^5) i *
                (ω : ℝ^5) i -
            (3 / (8 * Real.pi ^ 2))) *
            φ.toFun (r • (ω : ℝ^5))
          ∂(volume : Measure ℝ^5).toSphere) = 0 := by
  have hzero : Tendsto (fun ε : ℝ ↦ ∑ i : Fin 5, ∫ X in {X : ℝ^5 | ε < ‖X‖},
      iteratedPartialDeriv (n := 5) [i, i] (fundamentalSolution 5) X * φ.toFun X)
      (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [← integral_finsetSum _ fun i _ ↦
      fundamentalSolution_five_classicalHessian_integrableOn ε hε i i φ]
    refine (setIntegral_eq_zero_of_forall_eq_zero fun X (hX : ε < ‖X‖) ↦ ?_).symm
    rw [← Finset.sum_mul, fundamentalSolution_five_classicalHessian_trace_zero X
      (norm_pos_iff.1 (hε.trans hX)), zero_mul]
  simpa using tendsto_nhds_unique (tendsto_finsetSum Finset.univ fun i _ ↦
    fundamentalSolution_five_classicalHessian_principalValue_tendsto i i φ) hzero

/-- The complete local discrepancy between the distributional and punctured
diagonal traces has mass `-φ(0)`.
-/
theorem fundamentalSolution_five_distributionalMinusPV_trace
    (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    (∑ i : Fin 5,
      ((∫ X : ℝ^5,
          (fundamentalSolution 5) X *
            iteratedPartialDeriv (n := 5) [i, i] φ.toFun X) -
        ∫ r in Set.Ioi (0 : ℝ), r⁻¹ *
          ∫ ω : Metric.sphere (0 : ℝ^5) 1,
            ((15 / (8 * Real.pi ^ 2)) *
                (ω : ℝ^5) i *
                  (ω : ℝ^5) i -
              (3 / (8 * Real.pi ^ 2))) *
              φ.toFun (r • (ω : ℝ^5))
            ∂(volume : Measure ℝ^5).toSphere)) =
      -φ.toFun 0 := by
  rw [Finset.sum_sub_distrib,
    fundamentalSolution_five_distributional_laplacian φ,
    fundamentalSolution_five_principalValue_diagonal_sum_zero φ, sub_zero]

/-- Each diagonal discrepancy is one fifth of the distributional trace. -/
theorem fundamentalSolution_five_diagonal_discrepancy
    (i : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    (∫ X : ℝ^5, (fundamentalSolution 5) X *
        iteratedPartialDeriv (n := 5) [i, i] φ.toFun X) -
      fiveDimensionalHessianPrincipalValue i i φ =
        -(1 / 5 : ℝ) * φ.toFun 0 := by
  let D : Fin 5 → ℝ := fun k ↦
    (∫ X : ℝ^5, (fundamentalSolution 5) X * iteratedPartialDeriv (n := 5) [k, k] φ.toFun X) -
      fiveDimensionalHessianPrincipalValue k k φ
  have hsum : (∑ k : Fin 5, D k) = -φ.toFun 0 := by
    simpa [D, fiveDimensionalHessianPrincipalValue] using
      fundamentalSolution_five_distributionalMinusPV_trace φ
  simp only [show ∀ k, D k = D i from fun k ↦
      fundamentalSolution_five_diagonal_discrepancy_eq k i φ, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hsum
  dsimp only [D] at hsum
  linarith


/-- The five-dimensional Hessian identity, stated through spherical principal
value truncations against test functions.
-/
theorem fiveDimensionalFundamentalSolution_distributionalHessian
    (i j : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    ∃ L : ℝ,
      Tendsto (fun ε : ℝ ↦
        ∫ X in {X : ℝ^5 | ε < ‖X‖},
          iteratedPartialDeriv (n := 5) [i, j]
            (fundamentalSolution 5) X * φ.toFun X)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ∧
      ∫ X : ℝ^5,
          (fundamentalSolution 5) X *
            iteratedPartialDeriv (n := 5) [i, j] φ.toFun X =
        L - (if i = j then (1 / 5 : ℝ) * φ.toFun 0 else 0) := by
  refine ⟨fiveDimensionalHessianPrincipalValue i j φ,
    fiveDimensionalHessianPrincipalValue_tendsto i j φ, ?_⟩
  by_cases hij : i = j
  · subst j
    have hdiag := fundamentalSolution_five_diagonal_discrepancy i φ
    simp
    linear_combination hdiag
  · have hmixed := fundamentalSolution_five_mixed_discrepancy_zero i j hij φ
    simp only [ite_eq_right hij]
    linarith

/-- Test-function pullback by the affine involution `Y ↦ X - Y` used to
translate the origin-centered distributional Hessian into convolution form.
-/
noncomputable def fiveDimensionalConvolutionTestFunction
    (X : ℝ^5)
    (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    𝓓((⊤ : Opens ℝ^5), ℝ) :=
  TestFunction.precompProper (fun Y ↦ X - Y)
    (contDiff_const.sub contDiff_id)
    (by
      change IsProperMap (Homeomorph.subLeft X)
      exact (Homeomorph.subLeft X).isProperMap) φ

/-- Evaluation of the pulled-back test function: `(φ ∘ (X - ·)) Y = φ (X - Y)`. -/
@[simp]
theorem fiveDimensionalConvolutionTestFunction_apply
    (X Y : ℝ^5)
    (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    fiveDimensionalConvolutionTestFunction X φ Y = φ (X - Y) := rfl

/-- Translation of the complete Hessian identity to an arbitrary convolution
output point.  The left pairing is retained in distributional
test-function form; identifying it with a classical derivative of the
convolution is the subsequent differentiation-under-the-integral step.
-/
theorem fiveDimensionalFundamentalSolution_distributionalHessian_convolution
    (i j : Fin 5) (X : ℝ^5)
    (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    ∃ L : ℝ,
      Tendsto (fun ε : ℝ ↦
        ∫ Y in {Y : ℝ^5 | ε < ‖X - Y‖},
          iteratedPartialDeriv (n := 5) [i, j]
            (fundamentalSolution 5) (X - Y) * φ.toFun Y)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ∧
      (∫ Y : ℝ^5, (fundamentalSolution 5) Y *
          iteratedPartialDeriv (n := 5) [i, j]
            (fiveDimensionalConvolutionTestFunction X φ).toFun Y) =
        L - (if i = j then (1 / 5 : ℝ) * φ.toFun X else 0) := by
  obtain ⟨L, hL, hpair⟩ :=
    fiveDimensionalFundamentalSolution_distributionalHessian i j
      (fiveDimensionalConvolutionTestFunction X φ)
  refine ⟨L, hL.congr' (.of_forall fun ε ↦ ?_), by simpa using hpair⟩
  have h := (Measure.measurePreserving_sub_left volume X).setIntegral_preimage_emb
    (MeasurableEquiv.subLeft X).measurableEmbedding
    (fun Z ↦ iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) Z * φ.toFun (X - Z))
    {Y | ε < ‖Y‖}
  simp only [sub_sub_cancel] at h
  exact h.symm

/-- The spherical Hessian principal value exists for
every smooth compactly supported source.  This is the named-convention form
of the translated distributional Hessian theorem above.
-/
theorem hasFiveDimensionalHessianPrincipalValueAt_testFunction
    (i j : Fin 5) (X : ℝ^5)
    (F : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    ∃ v : ℝ,
      HasFiveDimensionalHessianPrincipalValueAt i j F.toFun X v := by
  obtain ⟨v, hv, _⟩ :=
    fiveDimensionalFundamentalSolution_distributionalHessian_convolution i j X F
  refine ⟨v, ?_, hv.congr' (.of_forall fun ε ↦ by simp [PDE.Analysis.principalValueTruncation])⟩
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simpa [Function.comp_def] using
    ((Measure.measurePreserving_sub_left volume X).integrableOn_comp_preimage
      (MeasurableEquiv.subLeft X).measurableEmbedding).2
      (fundamentalSolution_five_classicalHessian_integrableOn ε hε i j
        (fiveDimensionalConvolutionTestFunction X F))


/-- The vector-valued coefficient `-z y / (|y|² + z²) ∈ ℝ⁴` attached to the
four mixed `z`-`yₖ` Hessian components at once. Formally it is the Fourier
symbol of `∂_z ∂_{yₖ} (-Δ)⁻¹` read in the variables `(y, z)`; the results about
this definition are the elementary norm bounds below.

Keeping the four components together matters: for a function radial in the
first four coordinates, the pointwise Euclidean norm of the output vector is
the radial mixed derivative. Estimating one fixed Cartesian component and then
reducing angularly would lose a factor of two.
-/
noncomputable def mixedAxialFirstFourMultiplier
    (y : ℝ^4) (z : ℝ) :
    ℝ^4 :=
  (-z / (‖y‖ ^ 2 + z ^ 2)) • y

/-- A radial four-vector has exactly the norm of its scalar radial
coefficient.  This is the finite-dimensional norm identity used when the
four mixed Cartesian Hessian components are reduced to the radial mixed derivative `∂_z ∂_r`.
-/
theorem norm_scalar_smul_unitRadial
    (y : ℝ^4) (g : ℝ) (hy : y ≠ 0) :
    ‖(g / ‖y‖) • y‖ = |g| := by
  rw [norm_smul, norm_div, norm_norm, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hy),
    Real.norm_eq_abs]

/-- The full four-component mixed Hessian multiplier has Euclidean norm at
most `1 / 2`.  This is the sharp elementary estimate
`|z| * ‖y‖ ≤ (z² + ‖y‖²) / 2`.
-/
theorem mixedAxialFirstFourMultiplier_norm_le_half
    (y : ℝ^4) (z : ℝ) :
    ‖mixedAxialFirstFourMultiplier y z‖ ≤ (1 / 2 : ℝ) := by
  have hq : 0 ≤ ‖y‖ ^ 2 + z ^ 2 := by positivity
  simp only [mixedAxialFirstFourMultiplier, norm_smul, norm_div, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg hq]
  rcases hq.eq_or_lt with h | h
  · simp [← h]
  · rw [div_mul_eq_mul_div, div_le_iff₀ h]
    nlinarith [sq_nonneg (‖y‖ - |z|), sq_abs z]

/-- The geometric part of the mixed Hessian kernel bound.  If `R` is the
five-dimensional radius of `(y,z)`, then the vector numerator contributes at
most half of `R²`, leaving the decay `R⁻⁵` after division by `R⁷`.

Multiplying this inequality by `15 / (8 * π²)` gives the coefficient
`15 / (16 * π²)`.
-/
theorem mixedAxialFirstFourKernel_geometricFactor_le
    (y : ℝ^4) (z R : ℝ)
    (hR : 0 < R) (hR_sq : R ^ 2 = ‖y‖ ^ 2 + z ^ 2) :
    |z| * ‖y‖ / R ^ 7 ≤ (1 / 2 : ℝ) * R⁻¹ ^ 5 := by
  have hprod : |z| * ‖y‖ ≤ R ^ 2 / 2 := by
    rw [hR_sq]
    rw [← sq_abs z]
    nlinarith [sq_nonneg (‖y‖ - |z|)]
  have hR7 : 0 ≤ R ^ 7 := by positivity
  calc
    |z| * ‖y‖ / R ^ 7 ≤ (R ^ 2 / 2) / R ^ 7 :=
      div_le_div_of_nonneg_right hprod hR7
    _ = (1 / 2 : ℝ) * R⁻¹ ^ 5 := by
      field_simp

/-- The exact mixed-vector kernel constant used by the shell estimate. -/
theorem mixedAxialFirstFourKernel_coefficient_le
    (y : ℝ^4) (z R : ℝ)
    (hR : 0 < R) (hR_sq : R ^ 2 = ‖y‖ ^ 2 + z ^ 2) :
    (15 / (8 * Real.pi ^ 2)) * (|z| * ‖y‖ / R ^ 7) ≤
      (15 / (16 * Real.pi ^ 2)) * R⁻¹ ^ 5 := by
  have hc : 0 ≤ (15 / (8 * Real.pi ^ 2) : ℝ) := by positivity
  calc
    (15 / (8 * Real.pi ^ 2)) * (|z| * ‖y‖ / R ^ 7) ≤
        (15 / (8 * Real.pi ^ 2)) * ((1 / 2 : ℝ) * R⁻¹ ^ 5) :=
      mul_le_mul_of_nonneg_left
        (mixedAxialFirstFourKernel_geometricFactor_le y z R hR hR_sq) hc
    _ = (15 / (16 * Real.pi ^ 2)) * R⁻¹ ^ 5 := by ring

end PotentialTheory
