/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.BochnerConsistency
public import PDE.Spaces.Sobolev.Variational.Spaces.WholeSpaceHilbert
import PDE.Spaces.Sobolev.Approximation.Mollification.ProductH1

/-!
# H1 approximations of L2 initial data and Bochner forcing

Apply the spatial mollifier to each component. Each positive scale gives H1
initial data and Bochner L2 forcing valued in the H1 product. Their base rows converge
in the L2 product and Bochner L2, respectively. The measure on the forcing parameter
space is arbitrary, and no time continuity is assumed.

The H1 norms may grow as the scale tends to zero. Only the L2 base maps are contractive;
this is why the L2 difference estimate is needed for completing the solution sequence.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology Sobolev

namespace SobolevSpace.Approximation

open GraphSpace PDE.Analysis.Evolution

open scoped SobolevSpace.WholeSpaceHilbert

/-- Construct H1 approximations simultaneously for the initial state and forcing.
The displayed base map uses the zeroth Sobolev coordinates. The forcing parameter
measure need not be finite, and the finite component type may be empty. -/
theorem exists_h1_product_initial_forcing_approximation
    {n : ℕ} {ι α : Type*} [Fintype ι] [MeasurableSpace α] (ν : Measure α)
    (μ : Mollifier n) (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (x : PiLp 2 (fun _ : ι ↦ DerivLp n 2 univ))
    (f : Lp (PiLp 2 (fun _ : ι ↦ DerivLp n 2 univ)) 2 ν) :
    let J : PiLp 2 (fun _ : ι ↦ W^{1,2}(ℝ^n)) →L[ℝ]
        PiLp 2 (fun _ : ι ↦ DerivLp n 2 univ) :=
      (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : ι ↦ DerivLp n 2 univ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi fun p ↦
          (wkpCoordinateCLM (baseIndex n 1)).comp
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι ↦ W^{1,2}(ℝ^n)) p));
    ∃ X : ℕ → PiLp 2 (fun _ : ι ↦ W^{1,2}(ℝ^n)),
      ∃ F : ℕ → Lp (PiLp 2 (fun _ : ι ↦ W^{1,2}(ℝ^n))) 2 ν,
        Tendsto (fun k ↦ J (X k)) atTop (𝓝 x) ∧
        Tendsto (fun k ↦ J.compLpL 2 ν (F k)) atTop (𝓝 f) ∧
        ∀ k, ‖J (X k)‖ ≤ ‖x‖ := by
  classical
  dsimp only
  let J : PiLp 2 (fun _ : ι ↦ W^{1,2}(ℝ^n)) →L[ℝ]
      PiLp 2 (fun _ : ι ↦ DerivLp n 2 univ) :=
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : ι ↦ DerivLp n 2 univ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun p ↦
        (wkpCoordinateCLM (baseIndex n 1)).comp
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι ↦ W^{1,2}(ℝ^n)) p))
  let R (k : ℕ) : PiLp 2 (fun _ : ι ↦ DerivLp n 2 univ) →L[ℝ]
      PiLp 2 (fun _ : ι ↦ W^{1,2}(ℝ^n)) :=
    mollifierProductH1CLM μ (hε k)
  let Q (k : ℕ) := J.comp (R k)
  have hQ_apply (k : ℕ) (u : PiLp 2 (fun _ : ι ↦ DerivLp n 2 univ)) (p : ι) :
      Q k u p = mollifierRowCLM μ (hε k) (u p) :=
    mollifierH1CLM_base μ (hε k) (u p)
  have hQbound (k : ℕ) (u : PiLp 2 (fun _ : ι ↦ DerivLp n 2 univ)) :
      ‖Q k u‖ ≤ ‖u‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    simp only [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro p _
    rw [hQ_apply]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
      (norm_mollifierRowCLM_apply_le μ (hε k) (u p))
  have hQstrong (u : PiLp 2 (fun _ : ι ↦ DerivLp n 2 univ)) :
      Tendsto (fun k ↦ Q k u) atTop (𝓝 u) := by
    have hcoord : Tendsto (fun k p ↦ Q k u p) atTop (𝓝 (fun p ↦ u p)) := by
      apply tendsto_pi_nhds.mpr
      intro p
      simpa only [hQ_apply] using tendsto_mollifierRowCLM μ ε hε hε0 (u p)
    exact (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : ι ↦ DerivLp n 2 univ)).symm.continuous.continuousAt.tendsto.comp hcoord
  have hforce : Tendsto (fun k ↦ (Q k).compLpL 2 ν f) atTop (𝓝 f) := by
    apply tendsto_compLpL_of_tendsto_strongly Q 1 zero_le_one
    · intro k u
      simpa only [one_mul] using hQbound k u
    · exact hQstrong
  have hcomp (k : ℕ) :
      J.compLpL 2 ν ((R k).compLpL 2 ν f) = (Q k).compLpL 2 ν f := by
    apply Lp.ext
    filter_upwards [J.coeFn_compLpL ((R k).compLpL 2 ν f),
      (R k).coeFn_compLpL f, (Q k).coeFn_compLpL f] with t hJ hR hQ
    rw [hJ, hR, hQ]
    rfl
  refine ⟨fun k ↦ R k x, fun k ↦ (R k).compLpL 2 ν f, hQstrong x, ?_, ?_⟩
  · change Tendsto (fun k ↦ J.compLpL 2 ν ((R k).compLpL 2 ν f)) atTop (𝓝 f)
    simpa only [hcomp] using hforce
  · exact fun k ↦ hQbound k x

end SobolevSpace.Approximation
