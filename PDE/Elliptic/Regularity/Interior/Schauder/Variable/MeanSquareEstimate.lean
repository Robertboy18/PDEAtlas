/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Variable.LocalEnergy
public import PDE.Elliptic.Regularity.Interior.Schauder.Variable.LocalOscillation
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.Perturbation
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.PerturbativeDecay
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.BallEnergy

/-!
# Positive Campanato decay for general Hölder coefficients

An H¹ solution with Hölder coefficients and divergence forcing has
gradient mean-square oscillation of positive order. The proof first derives
mean-energy growth with a small power loss, then inserts that estimate into
the frozen quadratic oscillation comparison. No boundedness or continuity
of the input gradient is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace
open PDE.Elliptic.Regularity.Campanato
open scoped Sobolev ENNReal NNReal InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- Hölder coefficients and divergence forcing give positive gradient
Campanato decay from H¹ alone. The radius is uniform over centres and
solutions; the outer mean gradient energy is the only solution-dependent
quantity on the right. -/
theorem exists_local_meanSquare_gradient_estimate_of_holder_coefficients
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0)) {α Λ : ℝ}
    (hα : 0 < α) (hΛ : 0 ≤ Λ) {K M γ : ℝ≥0}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) {R₀ : ℝ} (hR₀ : 0 < R₀) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ R₀ ∧ 0 < C ∧
      ∀ {Ω : Set ℝ^n}, IsOpen Ω →
      ∀ (a : Fin n → Fin n → DerivLp n ∞ Ω)
        (A : Fin n → Fin n → ℝ^n → ℝ),
        (∀ i j, HolderOnWith K γ (A i j) Ω) →
        (∀ i j, (a i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] A i j) →
      ∀ (u : H¹(Ω)) (F : Fin n → DerivLp n 2 Ω) (f : Fin n → ℝ^n → ℝ),
        (∀ i, HolderOnWith M γ (f i) Ω) →
        (∀ i, (F i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f i) →
        (∀ v : H¹₀(Ω),
          interiorVariableCoeffForm (multiplicationCoefficientOperator a) u v =
            ∑ i, ⟪F i, derivCoordCLM i v⟫_ℝ) →
      ∀ z : ℝ^n, ball z ρ ⊆ Ω →
        (∀ i j, ‖A i j z‖ ≤ Λ) →
        (∀ ξ : Fin n → ℝ,
          α * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, A i j z * ξ j * ξ i) →
      ∀ (r : ℝ), 0 < r → r ≤ ρ → ∀ i : Fin n,
        (⨍ x in ball z r, ‖wkpCoordinateCLM (singleDerivIndex n i) u x -
          ⨍ y in ball z r, wkpCoordinateCLM (singleDerivIndex n i) u y‖ ^ 2) ≤
        C * (r / ρ) ^ (γ : ℝ) *
          ((∑ j, ⨍ x in ball z ρ,
            ‖wkpCoordinateCLM (singleDerivIndex n j) u x‖ ^ 2) + 1) := by
  classical
  obtain ⟨L, hL, henergy⟩ :=
    exists_local_gradient_mean_energy_of_holder_coefficients hq2 hq hα hΛ
  obtain ⟨D, hD, hosc⟩ :=
    exists_local_gradient_oscillation_of_holder_coefficients hq2 hq hα hΛ
  let H := (2 * n * (M : ℝ) ^ 2 + 2 * (n : ℝ) ^ 2 * (K : ℝ) ^ 2) / α ^ 2
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hγ : (0 : ℝ) < γ := by exact_mod_cast hγ0
  have hγlt : (γ : ℝ) < 1 := by exact_mod_cast hγ1
  obtain ⟨ρ, C, hρ, hρR, hC, hdecay⟩ :=
    exists_perturbative_oscillation_decay n
      (by positivity : 0 < 4 * L) (by positivity : 0 ≤ n * (2 + 4 * L) * H)
      (by positivity : 0 < 4 * D) (by positivity : 0 ≤ (2 + 4 * D) * H)
      hγ (by linarith : (γ : ℝ) < 2) hR₀
  refine ⟨ρ, 2 * C, hρ, hρR, by positivity, ?_⟩
  intro Ω hΩ a A hA hrep u F f hf hF hu z hsub hAz hell r hr hrρ i
  let E (s : ℝ) := ∑ j, ⨍ x in ball z s, ‖wkpCoordinateCLM (singleDerivIndex n j) u x‖ ^ 2
  let Φ (s : ℝ) := ⨍ x in ball z s, ‖wkpCoordinateCLM (singleDerivIndex n i) u x -
    ⨍ y in ball z s, wkpCoordinateCLM (singleDerivIndex n i) u y‖ ^ 2
  have hE (s : ℝ) : 0 ≤ E s :=
    Finset.sum_nonneg (fun _ _ ↦ average_nonneg (fun _ ↦ sq_nonneg _))
  have hΦ (s : ℝ) : 0 ≤ Φ s := average_nonneg (fun _ ↦ sq_nonneg _)
  have hmem (s : ℝ) (hs : s ≤ ρ) (j : Fin n) :
      MemLp (wkpCoordinateCLM (singleDerivIndex n j) u) 2
        (volume.restrict (ball z s)) :=
    (Lp.memLp _).mono_measure (domainMeasure_le ((ball_subset_ball hs).trans hsub))
  have hEmono (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s) (hsρ : s ≤ ρ) :
      E r ≤ (s / r) ^ n * E s := by
    simpa only [E, Finset.mul_sum] using Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦
      setAverage_norm_sq_le_of_radius_le hr hrs (hmem s hsρ j)
  have hΦmono (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s) (hsρ : s ≤ ρ) :
      Φ r ≤ (s / r) ^ n * Φ s :=
    setAverage_oscillation_sq_le_of_radius_le hr hrs (hmem s hsρ i)
  have herror (s : ℝ) (hs : 0 < s) :
      (2 * n * (M * s ^ (γ : ℝ)) ^ 2 +
        2 * (n : ℝ) ^ 2 * (K * s ^ (γ : ℝ)) ^ 2 * E s) / α ^ 2 ≤
          H * s ^ (2 * (γ : ℝ)) * (1 + E s) :=
    holder_comparison_error_le n hα hs (hE s)
  have hEstep (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s / 4) (hsρ : s ≤ ρ) :
      E r ≤ (4 * L) * E s +
        (n * (2 + 4 * L) * H) * (s / r) ^ n * s ^ (2 * (γ : ℝ)) * (1 + E s) := by
    have hs : 0 < s := by linarith
    have hQ : (1 : ℝ) ≤ (s / r) ^ n :=
      one_le_pow₀ ((one_le_div hr).mpr (by linarith))
    have hp : n * (2 * (s / r) ^ n + 4 * L) ≤
        n * (2 + 4 * L) * (s / r) ^ n := by
      have ht := mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ 4 * L)
      have ht' := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      nlinarith only [ht']
    have he := henergy hΩ a A K M γ hA hrep u F f hf hF hu z s hs
      ((ball_subset_ball hsρ).trans hsub) hAz hell r hr hrs
    have := hE s
    calc _ ≤ 4 * L * E s + (n * (2 + 4 * L) * (s / r) ^ n) *
          (H * s ^ (2 * (γ : ℝ)) * (1 + E s)) := he.trans (by gcongr; exact herror s hs)
      _ = _ := by ring
  have hΦstep (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s / 8) (hsρ : s ≤ ρ) :
      Φ r ≤ (4 * D) * (r / s) ^ 2 * Φ s +
        ((2 + 4 * D) * H) * (s / r) ^ n * s ^ (2 * (γ : ℝ)) * (1 + E s) := by
    have hs : 0 < s := by linarith
    have hQ : (1 : ℝ) ≤ (s / r) ^ n :=
      one_le_pow₀ ((one_le_div hr).mpr (by linarith))
    have ht : (r / s) ^ 2 ≤ 1 :=
      pow_le_one₀ (div_nonneg hr.le hs.le) ((div_le_one hs).mpr (by linarith))
    have hp : 2 * (s / r) ^ n + 4 * D * (r / s) ^ 2 ≤
        (2 + 4 * D) * (s / r) ^ n := by
      have hb := mul_le_mul_of_nonneg_left (ht.trans hQ) (by positivity : 0 ≤ 4 * D)
      nlinarith only [hb]
    have he := hosc hΩ a A K M γ hA hrep u F f hf hF hu z s hs
      ((ball_subset_ball hsρ).trans hsub) hAz hell i r hr hrs
    have := hE s
    calc _ ≤ 4 * D * (r / s) ^ 2 * Φ s + ((2 + 4 * D) * (s / r) ^ n) *
          (H * s ^ (2 * (γ : ℝ)) * (1 + E s)) := he.trans (by gcongr; exact herror s hs)
      _ = _ := by ring
  have hd := hdecay E Φ (fun s _ _ ↦ hE s) (fun s _ _ ↦ hΦ s)
    hEmono hΦmono hEstep hΦstep r hr hrρ
  have hΦE : Φ ρ ≤ E ρ := by
    have hm := setAverage_norm_sub_average_sq_le (hmem ρ le_rfl i) 0
    simp only [sub_zero] at hm
    exact hm.trans (Finset.single_le_sum
      (fun j _ ↦ average_nonneg (fun x ↦
        sq_nonneg ‖wkpCoordinateCLM (singleDerivIndex n j) u x‖)) (Finset.mem_univ i))
  calc _ ≤ C * (r / ρ) ^ (γ : ℝ) * (2 * (E ρ + 1)) := hd.trans (by gcongr; linarith)
    _ = _ := by ring

end SobolevSpace.GraphSpace
