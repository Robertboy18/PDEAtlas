/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Variable.MeanSquareEstimate
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.MeanSquare

/-!
# Hölder gradients from H¹ for general elliptic coefficients

The perturbative mean-square estimate supplies the Campanato hypothesis
uniformly over nearby centres. The original gradient has only L² regularity.
Its zero extension as an L² function permits use of the representative
theorem, giving a locally Hölder gradient with half the coefficient exponent.
This first gain also supplies local boundedness for the sharper estimate.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace
open PDE.Elliptic.Regularity.Campanato
open scoped Sobolev ENNReal NNReal InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- A uniformly elliptic H¹ solution with Hölder coefficients and divergence
forcing has locally Hölder weak gradient representatives. The input gradient
need not be bounded or continuous. The first gain has exponent `γ / 2`. -/
theorem exists_holder_gradient_of_holder_coefficients
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0)) {α Λ : ℝ}
    (hα : 0 < α) (hΛ : 0 ≤ Λ) {Ω : Set ℝ^n} (hΩ : IsOpen Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (A : Fin n → Fin n → ℝ^n → ℝ) {K M γ : ℝ≥0}
    (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hA : ∀ i j, HolderOnWith K γ (A i j) Ω)
    (hrep : ∀ i j, (a i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] A i j)
    (hAbound : ∀ x ∈ Ω, ∀ i j, ‖A i j x‖ ≤ Λ)
    (hell : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ,
      α * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i)
    (u : H¹(Ω)) (F : Fin n → DerivLp n 2 Ω) (f : Fin n → ℝ^n → ℝ)
    (hf : ∀ i, HolderOnWith M γ (f i) Ω)
    (hF : ∀ i, (F i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f i)
    (hu : ∀ v : H¹₀(Ω),
      interiorVariableCoeffForm (multiplicationCoefficientOperator a) u v =
        ∑ i, ⟪F i, derivCoordCLM i v⟫_ℝ)
    {z : ℝ^n} {R : ℝ} (hR : 0 < R) (hsub : ball z R ⊆ Ω) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R / 32 ∧
      ∀ i : Fin n, ∃ (g : ℝ^n → ℝ) (N : ℝ≥0), Continuous g ∧
        HolderOnWith N (γ / 2) g (ball z r) ∧
        g =ᵐ[volume.restrict (ball z r)] wkpCoordinateCLM (singleDerivIndex n i) u := by
  classical
  let : NeZero n := ⟨(Fact.out : 0 < n).ne'⟩
  obtain ⟨ρ, C, hρ, hρR, hC, hestimate⟩ :=
    exists_local_meanSquare_gradient_estimate_of_holder_coefficients
      hq2 hq hα hΛ (K := K) (M := M) hγ0 hγ1
      (by positivity : 0 < R / 4)
  let v (j : Fin n) : ℝ^n → ℝ :=
    Ω.indicator (wkpCoordinateCLM (singleDerivIndex n j) u)
  have hv (j : Fin n) : MemLp (v j) 2 volume :=
    (memLp_indicator_iff_restrict hΩ.measurableSet.nullMeasurableSet).mpr (Lp.memLp _)
  have hvrep (j : Fin n) {x : ℝ^n} {s : ℝ} (hxs : ball x s ⊆ Ω) :
      v j =ᵐ[volume.restrict (ball x s)] wkpCoordinateCLM (singleDerivIndex n j) u :=
    (ae_restrict_mem isOpen_ball.measurableSet).mono
      (fun y hy ↦ indicator_of_mem (hxs hy) _)
  let I := ∑ j, ∫ x, ‖v j x‖ ^ 2
  have hI : 0 ≤ I := Finset.sum_nonneg (fun _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
  let B := (volume.real (ball z ρ))⁻¹ * I + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let P := C / ρ ^ (γ : ℝ) * B
  have hP : 0 ≤ P := by dsimp [P]; positivity
  let N : ℝ≥0 := ⟨Real.sqrt P, Real.sqrt_nonneg _⟩
  have hN : (N : ℝ) ^ 2 = P := Real.sq_sqrt hP
  have hβ : (0 : ℝ≥0) < γ / 2 := div_pos hγ0 (by norm_num)
  have hβeq : 2 * ((γ / 2 : ℝ≥0) : ℝ) = γ := by push_cast; ring
  refine ⟨ρ / 8, by positivity, by linarith, ?_⟩
  intro i
  have hav {x : ℝ^n} {s : ℝ} (hxs : ball x s ⊆ Ω) :
      (⨍ y in ball x s, ‖v i y - ⨍ w in ball x s, v i w‖ ^ 2) =
      ⨍ y in ball x s, ‖wkpCoordinateCLM (singleDerivIndex n i) u y -
        ⨍ w in ball x s, wkpCoordinateCLM (singleDerivIndex n i) u w‖ ^ 2 := by
    rw [average_congr (hvrep i hxs)]
    exact average_congr ((hvrep i hxs).fun_comp (fun t ↦ ‖t -
      ⨍ w in ball x s, wkpCoordinateCLM (singleDerivIndex n i) u w‖ ^ 2))
  have hcamp (x : ℝ^n) (hx : x ∈ ball z ρ) (s : ℝ) (hs : 0 < s) (hsρ : s ≤ ρ) :
      (⨍ y in closedBall x s, ‖v i y - ⨍ w in closedBall x s, v i w‖ ^ 2) ≤
        (N * s ^ ((γ / 2 : ℝ≥0) : ℝ)) ^ 2 := by
    have hxsub : ball x ρ ⊆ Ω := (ball_subset_ball' (by linarith [mem_ball.mp hx])).trans hsub
    have hxΩ : x ∈ Ω := hxsub (mem_ball_self hρ)
    have hxsmall : ball x s ⊆ Ω := (ball_subset_ball hsρ).trans hxsub
    have hd := hestimate hΩ a A hA hrep u F f hf hF hu x hxsub
      (hAbound x hxΩ) (hell x hxΩ) s hs hsρ i
    rw [← hav hxsmall] at hd
    have hvol : volume.real (ball x ρ) = volume.real (ball z ρ) := by
      rw [Measure.addHaar_real_ball_center volume x, Measure.addHaar_real_ball_center volume z]
    have hmean (j : Fin n) :
        (⨍ y in ball x ρ, ‖wkpCoordinateCLM (singleDerivIndex n j) u y‖ ^ 2) ≤
          (volume.real (ball z ρ))⁻¹ * ∫ y, ‖v j y‖ ^ 2 := by
      have ha : (⨍ y in ball x ρ, ‖wkpCoordinateCLM (singleDerivIndex n j) u y‖ ^ 2) =
          ⨍ y in ball x ρ, ‖v j y‖ ^ 2 :=
        average_congr ((hvrep j hxsub).fun_comp (fun t ↦ ‖t‖ ^ 2)).symm
      rw [ha, setAverage_eq, smul_eq_mul, hvol]
      exact mul_le_mul_of_nonneg_left (setIntegral_le_integral (hv j).norm.integrable_sq
        (.of_forall fun _ ↦ sq_nonneg _)) (by positivity)
    have houter : (∑ j, ⨍ y in ball x ρ,
        ‖wkpCoordinateCLM (singleDerivIndex n j) u y‖ ^ 2) + 1 ≤ B := by
      have ht := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hmean j)
      simpa only [B, I, Finset.mul_sum] using add_le_add ht (le_rfl : (1 : ℝ) ≤ 1)
    have hballs : closedBall x s =ᵐ[volume] ball x s :=
      (ae_eq_of_subset_of_measure_ge ball_subset_closedBall
        (Measure.addHaar_closedBall_eq_addHaar_ball volume x s).le
        isOpen_ball.measurableSet.nullMeasurableSet measure_closedBall_lt_top.ne).symm
    simp_rw [setAverage_congr hballs]
    calc
      _ ≤ C * (s / ρ) ^ (γ : ℝ) * B :=
        hd.trans (mul_le_mul_of_nonneg_left houter (by positivity))
      _ = _ := by
        have hp := Real.rpow_mul_natCast hs.le ((γ / 2 : ℝ≥0) : ℝ) 2
        norm_num only [Nat.cast_ofNat] at hp
        rw [mul_pow (N : ℝ), hN, ← hp,
          mul_comm ((γ / 2 : ℝ≥0) : ℝ) 2, hβeq, Real.div_rpow hs.le hρ.le]
        dsimp only [P]
        ring
  obtain ⟨L, _, hholder⟩ := exists_holderOnWith_representative_of_meanSquare (n := n) hβ
  obtain ⟨g, hg, hgHolder, hgAE⟩ := hholder (v i) N
    (fun _ _ ↦ (hv i).mono_measure Measure.restrict_le_self) z ρ hρ hcamp
  refine ⟨g, L * N, hg, hgHolder, hgAE.trans ?_⟩
  exact hvrep i ((ball_subset_ball (by linarith : ρ / 8 ≤ R)).trans hsub)

end SobolevSpace.GraphSpace
