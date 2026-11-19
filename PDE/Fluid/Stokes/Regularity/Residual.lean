/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Regularity.Vorticity
import PDE.DistributionTheory.Distribution.Function.FiniteSum

/-!
# A locally L² representative of the Stokes residual

Taking the divergence of the locally H¹ vorticity tensor produces a locally
L² vector field. Incompressibility identifies it with the velocity Laplacian
as an ordinary distribution. Adding the original L² force thus gives the
locally L² residual needed for weak pressure reconstruction.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Sobolev ENNReal Distributions

namespace IncompressibleFlow.Stokes

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Opens (ℝ^n)}

/-- The residual of a raw incompressible energy minimizer has a derived
locally L² representative. No second derivative of the state is assumed. -/
theorem exists_locally_memLp_residual_of_minimizes_energy
    (f : Lp (ℝ^n) 2 (domainMeasure n Ω)) (u : H¹₀(Ω; ℝ^n))
    (hu : ∇· u = 0)
    (hmin : ∀ w : H¹₀(Ω; ℝ^n), ∇· w = 0 →
      energy f u ≤ energy f w) :
    ∃ R : ℝ^n → ℝ^n,
      (∀ j, LocallyIntegrableOn (fun x ↦ R x j) (Ω : Set (ℝ^n)) volume) ∧
      (∀ j, ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω →
        MemLp (fun x ↦ R x j) 2 (domainMeasure n K)) ∧
      ∀ j, Distribution.ofFun Ω (fun x ↦ R x j) volume ⊤ = residual f u j := by
  obtain ⟨g, _, hmem, hweak⟩ :=
    exists_vorticity_weak_derivatives_of_minimizes_energy f u hu hmin
  let s (j : Fin n) : ℝ^n → ℝ := ∑ i : Fin n, g i j i
  have hsLp (j : Fin n) (K : Set (ℝ^n)) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
      MemLp (s j) 2 (domainMeasure n K) :=
    memLp_finsetSum' Finset.univ (fun i _ ↦ hmem i j i K hK hKΩ)
  have hs (j : Fin n) : LocallyIntegrableOn (s j) (Ω : Set (ℝ^n)) volume := by
    apply (locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed).mpr
    intro K hKΩ hK
    have : IsFiniteMeasure (domainMeasure n K) :=
      isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact MemLp.integrable (by norm_num) (hsLp j K hK hKΩ)
  have hf (j : Fin n) : MemLp (fun x ↦ f x j) 2 (domainMeasure n Ω) := by
    simpa only [EuclideanSpace.coe_proj, Function.comp_def] using
      (EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp' (Lp.memLp f)
  let R (x : ℝ^n) : ℝ^n := WithLp.toLp 2 fun j ↦ f x j + s j x
  refine ⟨R, ?_, ?_, ?_⟩
  · intro j
    exact (memLp_locallyIntegrableOn_domain (hf j) (by norm_num)).add (hs j)
  · intro j K hK hKΩ
    exact ((hf j).mono_measure (Measure.restrict_mono hKΩ le_rfl)).add
      (hsLp j K hK hKΩ)
  · intro j
    change Distribution.ofFun Ω ((fun x ↦ f x j) + s j) volume ⊤ = _
    rw [Distribution.ofFun_add
      (memLp_locallyIntegrableOn_domain (hf j) (by norm_num)) (hs j)]
    have hsum :
        Distribution.ofFun Ω (s j) volume ⊤ =
          ∑ i : Fin n, Distribution.ofFun Ω (g i j i) volume ⊤ :=
      Distribution.ofFun_finsetSum Finset.univ (fun i ↦ g i j i)
        (fun i _ ↦ (hweak i j i).locallyIntegrable_g)
    rw [hsum]
    have hD (i : Fin n) :
        Distribution.ofFun Ω (g i j i) volume ⊤ =
          Distribution.lineDerivCLM (EuclideanSpace.single i (1 : ℝ))
            (Distribution.ofLp Ω 2 (vorticity u i j)) :=
      (hweak i j i).lineDerivCLM_ofFun.symm
    simp_rw [hD]
    rw [sum_lineDeriv_vorticity_eq_residual_sub_force f u hu j]
    abel

end IncompressibleFlow.Stokes
