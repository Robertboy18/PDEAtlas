/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Sobolev.Energy.RegularizedBounds
import PDE.Analysis.MeasureTheory.Lp.Continuous

/-!
# Bounded regularized heat families

For any sequence of positive smoothing scales, Carathéodory heat
trajectories give three bounded Bochner families: the H¹ states, their
smoothed H² states, and their projected L² velocities. These are different
families. Their almost-everywhere representatives retain the regularized
equation and the initial datum.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Heat

open MeasureTheory Set
open PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open scoped ENNReal Sobolev

variable {n : ℕ} {ε a b : ℝ}

/-- The Bochner classes of H¹ regularized trajectories form a bounded family. -/
theorem isBounded_range_regularized_heat_states
    (hε : 0 < ε) (hab : a ≤ b) {δ : ℕ → ℝ} (hδ : ∀ k, 0 < δ k)
    {F : ℝ → DerivLp n 2 univ}
    (hf : MemLp F 2 (volume.restrict (Ioc a b))) {q : W^{1,2}(ℝ^n)}
    (U : ∀ k, AffineCaratheodorySolutionOn
      (fun _ ↦ ε • regularizedLaplacianCLM (n := n) 1 (hδ k))
      (fun t ↦ mollifierSmoothingCLM 1 (standardMollifier n) (hδ k) (F t)) a b q)
    (u : ℕ → Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (hu : ∀ k, (u k : ℝ → W^{1,2}(ℝ^n)) =ᵐ[volume.restrict (Ioc a b)]
      (U k).trajectory) :
    Bornology.IsBounded (range u) := by
  let K := ‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ t in a..b, ‖F t‖ ^ 2
  have hF : 0 ≤ ∫ t in a..b, ‖F t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab fun _ _ ↦ sq_nonneg _
  have hK : 0 ≤ K := by positivity
  apply isBounded_range_of_norm_sq_le u
    (C := (b - a) * Real.exp (b - a) * K) (by positivity)
  intro k
  rw [Lp.norm_sq_eq_integral_norm_sq]
  calc
    _ = ∫ t in a..b, ‖(U k).trajectory t‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le hab]
      exact integral_congr_ae ((hu k).fun_comp fun z ↦ ‖z‖ ^ 2)
    _ ≤ _ := regularized_heat_integral_norm_sq_le hε (hδ k) hab hf (U k)

/-- The smoothed H² Bochner class satisfies the dissipative bound.
The right side is independent of the auxiliary smoothing scale. -/
theorem regularized_heat_smoothing_norm_sq_le
    (hε : 0 < ε) (hab : a ≤ b) {δ : ℝ} (hδ : 0 < δ)
    {F : ℝ → DerivLp n 2 univ}
    (hf : MemLp F 2 (volume.restrict (Ioc a b))) {q : W^{1,2}(ℝ^n)}
    (U : AffineCaratheodorySolutionOn
      (fun _ ↦ ε • regularizedLaplacianCLM (n := n) 1 hδ)
      (fun t ↦ mollifierSmoothingCLM 1 (standardMollifier n) hδ (F t)) a b q)
    (v : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (hv : (v : ℝ → W^{2,2}(ℝ^n)) =ᵐ[volume.restrict (Ioc a b)] fun t ↦
      mollifierSmoothingCLM 2 (standardMollifier n) hδ
        (wkpBaseCoordinateCLM (U.trajectory t))) :
    ε * ‖v‖ ^ 2 ≤ (1 + (1 + ε) * (b - a) * Real.exp (b - a)) *
      (‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ t in a..b, ‖F t‖ ^ 2) := by
  rw [Lp.norm_sq_eq_integral_norm_sq]
  have heq : (∫ t, ‖v t‖ ^ 2 ∂volume.restrict (Ioc a b)) =
      ∫ t in a..b, ‖mollifierSmoothingCLM 2 (standardMollifier n) hδ
        (wkpBaseCoordinateCLM (U.trajectory t))‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hab]
    exact integral_congr_ae (hv.fun_comp fun z ↦ ‖z‖ ^ 2)
  rw [heq]
  exact regularized_heat_integral_smoothing_sq_le hε hδ hab hf U

/-- The smoothed H² states are uniformly bounded in Bochner L². -/
theorem isBounded_range_regularized_heat_smoothings
    (hε : 0 < ε) (hab : a ≤ b) {δ : ℕ → ℝ} (hδ : ∀ k, 0 < δ k)
    {F : ℝ → DerivLp n 2 univ}
    (hf : MemLp F 2 (volume.restrict (Ioc a b))) {q : W^{1,2}(ℝ^n)}
    (U : ∀ k, AffineCaratheodorySolutionOn
      (fun _ ↦ ε • regularizedLaplacianCLM (n := n) 1 (hδ k))
      (fun t ↦ mollifierSmoothingCLM 1 (standardMollifier n) (hδ k) (F t)) a b q)
    (v : ℕ → Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (hv : ∀ k, (v k : ℝ → W^{2,2}(ℝ^n)) =ᵐ[volume.restrict (Ioc a b)] fun t ↦
      mollifierSmoothingCLM 2 (standardMollifier n) (hδ k)
        (wkpBaseCoordinateCLM ((U k).trajectory t))) :
    Bornology.IsBounded (range v) := by
  let K := ‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ t in a..b, ‖F t‖ ^ 2
  have hF : 0 ≤ ∫ t in a..b, ‖F t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab fun _ _ ↦ sq_nonneg _
  have hK : 0 ≤ K := by positivity
  apply isBounded_range_of_norm_sq_le v
    (C := ((1 + (1 + ε) * (b - a) * Real.exp (b - a)) * K) / ε) (by positivity)
  intro k
  rw [le_div_iff₀ hε, mul_comm]
  exact regularized_heat_smoothing_norm_sq_le hε hab (hδ k) hf (U k) (v k) (hv k)

/-- The projected velocities are uniformly bounded in Bochner L²(L²). -/
theorem isBounded_range_regularized_heat_velocities
    (hε : 0 < ε) (hab : a ≤ b) {δ : ℕ → ℝ} (hδ : ∀ k, 0 < δ k)
    {F : ℝ → DerivLp n 2 univ}
    (hf : MemLp F 2 (volume.restrict (Ioc a b))) {q : W^{1,2}(ℝ^n)}
    (U : ∀ k, AffineCaratheodorySolutionOn
      (fun _ ↦ ε • regularizedLaplacianCLM (n := n) 1 (hδ k))
      (fun t ↦ mollifierSmoothingCLM 1 (standardMollifier n) (hδ k) (F t)) a b q)
    (g : ℕ → Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
    (hg : ∀ k, (g k : ℝ → DerivLp n 2 univ) =ᵐ[volume.restrict (Ioc a b)] fun t ↦
      wkpBaseCoordinateCLM (ε • regularizedLaplacianCLM (n := n) 1 (hδ k) ((U k).trajectory t) +
        mollifierSmoothingCLM 1 (standardMollifier n) (hδ k) (F t))) :
    Bornology.IsBounded (range g) := by
  let K := ‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ t in a..b, ‖F t‖ ^ 2
  have hF : 0 ≤ ∫ t in a..b, ‖F t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab fun _ _ ↦ sq_nonneg _
  have hK : 0 ≤ K := by positivity
  apply isBounded_range_of_norm_sq_le g
    (C := 2 * ε * ‖(wkpLaplacianCLM :
      W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)‖ ^ 2 *
        ((1 + (1 + ε) * (b - a) * Real.exp (b - a)) * K) +
      2 * ∫ t in a..b, ‖F t‖ ^ 2) (by positivity)
  intro k
  rw [Lp.norm_sq_eq_integral_norm_sq]
  calc
    _ = ∫ t in a..b,
        ‖wkpBaseCoordinateCLM (ε • regularizedLaplacianCLM (n := n) 1 (hδ k) ((U k).trajectory t) +
          mollifierSmoothingCLM 1 (standardMollifier n) (hδ k) (F t))‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le hab]
      exact integral_congr_ae ((hg k).fun_comp fun z ↦ ‖z‖ ^ 2)
    _ ≤ _ := regularized_heat_integral_velocity_sq_le hε (hδ k) hab hf (U k)

/-- A regularized trajectory and its projected derivative determine
Bochner classes with their pointwise representatives. -/
theorem exists_regularized_heat_classes
    {δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b)
    {F : ℝ → DerivLp n 2 univ}
    (hf : MemLp F 2 (volume.restrict (Ioc a b))) {q : W^{1,2}(ℝ^n)}
    (U : AffineCaratheodorySolutionOn
      (fun _ ↦ ε • regularizedLaplacianCLM (n := n) 1 hδ)
      (fun t ↦ mollifierSmoothingCLM 1 (standardMollifier n) hδ (F t)) a b q) :
    ∃ (u : Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
      (v : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
      (g : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b))),
      (u : ℝ → W^{1,2}(ℝ^n)) =ᵐ[volume.restrict (Ioc a b)] U.trajectory ∧
      (v : ℝ → W^{2,2}(ℝ^n)) =ᵐ[volume.restrict (Ioc a b)] (fun t ↦
        mollifierSmoothingCLM 2 (standardMollifier n) hδ
          (wkpBaseCoordinateCLM (U.trajectory t))) ∧
      (g : ℝ → DerivLp n 2 univ) =ᵐ[volume.restrict (Ioc a b)] (fun t ↦
        wkpBaseCoordinateCLM (ε • regularizedLaplacianCLM (n := n) 1 hδ (U.trajectory t) +
          mollifierSmoothingCLM 1 (standardMollifier n) hδ (F t))) := by
  have hcont : ContinuousOn U.trajectory (Icc a b) := by
    simpa only [uIcc_of_le hab] using U.absolutely_continuous.continuousOn
  have hu : MemLp U.trajectory 2 (volume.restrict (Ioc a b)) :=
    hcont.memLp_of_subset_isCompact isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  let P : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := wkpBaseCoordinateCLM
  let S : DerivLp n 2 univ →L[ℝ] W^{2,2}(ℝ^n) :=
    mollifierSmoothingCLM 2 (standardMollifier n) hδ
  let V := S ∘ P ∘ U.trajectory
  have hv : MemLp V 2 (volume.restrict (Ioc a b)) := S.comp_memLp' (P.comp_memLp' hu)
  let G (t : ℝ) : DerivLp n 2 univ := P
    (ε • regularizedLaplacianCLM (n := n) 1 hδ (U.trajectory t) +
      mollifierSmoothingCLM 1 (standardMollifier n) hδ (F t))
  have hg : MemLp G 2 (volume.restrict (Ioc a b)) :=
    P.comp_memLp'
      (((ε • regularizedLaplacianCLM (n := n) 1 hδ).comp_memLp' hu).add
        ((mollifierSmoothingCLM 1 (standardMollifier n) hδ).comp_memLp' hf))
  exact ⟨hu.toLp U.trajectory, hv.toLp V, hg.toLp G,
    hu.coeFn_toLp, hv.coeFn_toLp, hg.coeFn_toLp⟩

/-- Bounded state, smoothed-state, and velocity families built from an H¹
initial datum and Bochner L² forcing. -/
theorem exists_bounded_regularized_heat_family
    (hε : 0 < ε) (hab : a ≤ b) (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k)
    (F : ℝ → DerivLp n 2 univ)
    (hf : MemLp F 2 (volume.restrict (Ioc a b))) (q : W^{1,2}(ℝ^n)) :
    ∃ (U : ∀ k, AffineCaratheodorySolutionOn
        (fun _ ↦ ε • regularizedLaplacianCLM (n := n) 1 (hδ k))
        (fun t ↦ mollifierSmoothingCLM 1 (standardMollifier n) (hδ k) (F t)) a b q)
      (u : ℕ → Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
      (v : ℕ → Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
      (g : ℕ → Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b))),
      Bornology.IsBounded (range u) ∧ Bornology.IsBounded (range v) ∧
      Bornology.IsBounded (range g) ∧
      (∀ k, (u k : ℝ → W^{1,2}(ℝ^n)) =ᵐ[volume.restrict (Ioc a b)]
        (U k).trajectory) ∧
      (∀ k, (v k : ℝ → W^{2,2}(ℝ^n)) =ᵐ[volume.restrict (Ioc a b)] fun t ↦
        mollifierSmoothingCLM 2 (standardMollifier n) (hδ k)
          (wkpBaseCoordinateCLM ((U k).trajectory t))) ∧
      (∀ k, (g k : ℝ → DerivLp n 2 univ) =ᵐ[volume.restrict (Ioc a b)] fun t ↦
        wkpBaseCoordinateCLM (ε • regularizedLaplacianCLM (n := n) 1 (hδ k) ((U k).trajectory t) +
          mollifierSmoothingCLM 1 (standardMollifier n) (hδ k) (F t))) := by
  choose U _ using fun k ↦ exists_regularized_heat_solution hε (hδ k) hab F hf q
  choose u v g hu hv hg using fun k ↦ exists_regularized_heat_classes (hδ k) hab hf (U k)
  exact ⟨U, u, v, g,
    isBounded_range_regularized_heat_states hε hab hδ hf U u hu,
    isBounded_range_regularized_heat_smoothings hε hab hδ hf U v hv,
    isBounded_range_regularized_heat_velocities hε hab hδ hf U g hg, hu, hv, hg⟩

end PDE.Parabolic.Heat
