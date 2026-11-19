/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.LipschitzSuperposition
public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates

/-!
# L² components of a Lipschitz Sobolev flux

A Lipschitz map applied to the weak gradient is square-integrable on a
bounded domain. The constant value of the map at zero is retained. The
result gives simultaneous almost-everywhere component identities, so it
can be used directly in weak divergence equations.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A Lipschitz flux of a Sobolev gradient has `L²`
components, without a normalization at zero or a boundary regularity
hypothesis. -/
theorem exists_L2_flux_of_lipschitz (hbounded : Bornology.IsBounded Ω)
    {A : ℝ^n → ℝ^n} {C : ℝ≥0} (hA : LipschitzWith C A)
    (u : H¹(Ω)) :
    ∃ q : Fin n → DerivLp n 2 Ω, ∀ᵐ x ∂domainMeasure n Ω,
      A (WithLp.toLp 2 (fun i ↦ u.val (singleDerivIndex n i) x)) =
        WithLp.toLp 2 (fun i ↦ q i x) := by
  have := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  have hmem : MemLp (fun x ↦ A (∇ u x)) 2 (domainMeasure n Ω) :=
    hA.comp_memLp_of_memLp_const (memLp_const _) (Lp.memLp (∇ u))
  let F := hmem.toLp (fun x ↦ A (∇ u x))
  let q (i : Fin n) : DerivLp n 2 Ω :=
    (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).compLpL 2 (domainMeasure n Ω) F
  refine ⟨q, ?_⟩
  have hq := ae_all_iff.mpr fun i ↦
    (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).coeFn_compLpL F
  filter_upwards [wkpGradientCLM_apply_ae u, hmem.coeFn_toLp, hq] with x hu hF hq'
  have hu' : ∇ u x =
      WithLp.toLp 2 (fun i ↦ u.val (singleDerivIndex n i) x) :=
    PiLp.ext hu
  rw [← hu', ← hF]
  exact PiLp.ext fun i ↦ (hq' i).symm

/-- Flux components and their literal integral pairing with every
zero-boundary test. The solution itself has arbitrary trace. -/
theorem exists_L2_flux_pairing_of_lipschitz (hbounded : Bornology.IsBounded Ω)
    {A : ℝ^n → ℝ^n} {C : ℝ≥0} (hA : LipschitzWith C A)
    (u : H¹(Ω)) :
    ∃ q : Fin n → DerivLp n 2 Ω,
      (∀ᵐ x ∂domainMeasure n Ω, A (∇ u x) = Lp.euclideanTuple q x) ∧
      ∀ v : H¹₀(Ω),
        Integrable (fun x ↦ ⟪A (∇ u x), ∇ (v : H¹(Ω)) x⟫)
          (domainMeasure n Ω) ∧
        (∫ x, ⟪A (∇ u x), ∇ (v : H¹(Ω)) x⟫ ∂domainMeasure n Ω) =
          ∑ i, ⟪q i, derivCoordCLM i v⟫ := by
  obtain ⟨q, hq⟩ := exists_L2_flux_of_lipschitz hbounded hA u
  have hrep : ∀ᵐ x ∂domainMeasure n Ω,
      A (∇ u x) = Lp.euclideanTuple q x := by
    filter_upwards [hq, wkpGradientCLM_apply_ae u, Lp.euclideanTuple_apply_ae q]
      with x hx hu hq'
    have hu' : ∇ u x =
        WithLp.toLp 2 (fun i ↦ u.val (singleDerivIndex n i) x) := PiLp.ext hu
    have hq'' : Lp.euclideanTuple q x = WithLp.toLp 2 (fun i ↦ q i x) := PiLp.ext hq'
    rw [hu', hq'']
    exact hx
  refine ⟨q, hrep, fun v ↦ ⟨?_, ?_⟩⟩
  · apply (L2.integrable_inner (𝕜 := ℝ) (Lp.euclideanTuple q) (∇ (v : H¹(Ω)))).congr
    exact hrep.mono fun x hx ↦ congrArg (fun z ↦ ⟪z, (∇ (v : H¹(Ω))) x⟫) hx.symm
  · calc
      _ = ⟪Lp.euclideanTuple q, ∇ (v : H¹(Ω))⟫ := by
        rw [L2.inner_def]
        exact integral_congr_ae (hrep.mono fun x hx ↦
          congrArg (fun z ↦ ⟪z, (∇ (v : H¹(Ω))) x⟫) hx)
      _ = _ := Lp.inner_euclideanTuple q (fun i ↦ derivCoordCLM i v)

end SobolevSpace.GraphSpace
