/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Localization.CutoffEquation.ZeroBoundaryCutoff
public import PDE.Elliptic.Variational.InteriorLowerOrder
import PDE.Analysis.MeasureTheory.Lp.MultiplierPairing
import PDE.DistributionTheory.TestFunction.CompactCutoff
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized
import PDE.Spaces.Sobolev.GraphSpace.Norms

/-!
# Interior energy for the full elliptic operator

Testing with η²u controls the localized gradient by the L² norms of the forcing and the state
(`exists_cutoff_gradient_estimate`), and on a relatively compact open subset the full H¹ norm is
controlled in the same way (`exists_interior_h1_estimate`). The coefficients of the principal,
drift, and potential terms need only be bounded measurable functions. Only the principal part is
required to be elliptic.

This is the estimate of step 7 of Evans's proof of §6.3.1, Theorem 1, where `v = ζ² u` in (9) gives
`∫ ζ² |Du|² ≤ C ∫ f² + u²`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, step 7 of the proof of Theorem 1, p. 331.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Sobolev

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Distributions InnerProductSpace

namespace SobolevSpace.GraphSpace

open DifferenceQuotient

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The cutoff gradient of an interior weak solution is bounded by its L² data.
The constant depends on the coefficients, ellipticity, and cutoff, independently of
the solution and forcing. No sign condition on the drift or potential is needed. -/
theorem exists_cutoff_gradient_estimate
    (hΩ : IsOpen Ω) (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha : ℝ} (ha : AEUniformlyElliptic a alpha)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : DerivLp n 2 Ω) (u : H¹(Ω)),
      IsInteriorWeakFullDivergenceSolution a b c f u →
      ∀ i : Fin n,
        ‖testFunctionLpTop (Ω := Ω) η •
          wkpCoordinateCLM (singleDerivIndex n i) u‖ ≤
            C * (‖f‖ + ‖wkpBaseCoordinateCLM u‖) := by
  classical
  let q : DerivLp n ∞ Ω := testFunctionLpTop η
  let d (i : Fin n) : DerivLp n ∞ Ω := partialTestFunctionLpTop η i
  let M : ℝ := 2 * (∑ i, ∑ j, ‖a i j‖ * ‖d i‖) + (∑ i, ‖b i‖) * ‖q‖
  let D : ℝ := (‖c‖ + 1) * ‖q‖ ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have halpha : 0 < alpha := ha.1
  let C : ℝ := 1 + (M + D) / alpha
  have hC : 1 ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (by positivity)
  have hCa : alpha * C = alpha + M + D := by
    dsimp [C]
    field_simp [halpha.ne']
    ring
  refine ⟨C, zero_lt_one.trans_le hC, fun f u hu ↦ ?_⟩
  let u₀ : DerivLp n 2 Ω := wkpBaseCoordinateCLM u
  let du (i : Fin n) : DerivLp n 2 Ω := wkpCoordinateCLM (singleDerivIndex n i) u
  let G : PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 Ω) :=
    WithLp.toLp 2 (fun i ↦ q • du i)
  have hGi (i : Fin n) : ‖q • du i‖ ≤ ‖G‖ := PiLp.norm_apply_le G i
  have hGs : ∑ i, ‖q • du i‖ ^ 2 = ‖G‖ ^ 2 := (PiLp.norm_sq_eq_of_L2 _ G).symm
  let v : H¹₀(Ω) := cutoffH1ToH10 hΩ (squaredCutoff η)
    ((tsupport_squaredCutoff_subset η).trans hη) u
  have hv₀ : baseCoordCLM v = q • (q • u₀) := by
    rw [baseCoordCLM_cutoffH1ToH10]
    change testFunctionLpTop (Ω := Ω) (TestFunction.mul η η) • u₀ = _
    rw [testFunctionLpTop_mul, lpSMul_top_top_two_assoc]
  have hvd (i : Fin n) : derivCoordCLM i v =
      q • (q • du i) + (q • (d i • u₀) + q • (d i • u₀)) := by
    rw [derivCoordCLM_cutoffH1ToH10, partialSquaredCutoff_smul]
    change testFunctionLpTop (Ω := Ω) (TestFunction.mul η η) • du i + _ = _
    simp only [testFunctionLpTop_mul, ← lpSMul_top_top_two_assoc]
    rfl
  have hpr (i j : Fin n) : ⟪a i j • du j, derivCoordCLM i v⟫_ℝ =
      ⟪a i j • (q • du j), q • du i⟫_ℝ +
        2 * ⟪a i j • (q • du j), d i • u₀⟫_ℝ := by
    rw [hvd, inner_add_right, inner_add_right]
    simp only [← Lp.inner_lpSMul_left q, lpSMul_top_top_two_comm q (a i j)]
    ring
  have hcross (i j : Fin n) :
      |⟪a i j • (q • du j), d i • u₀⟫_ℝ| ≤
        ‖a i j‖ * ‖d i‖ * ‖G‖ * ‖u₀‖ := by
    calc
      _ ≤ ‖a i j‖ * ‖q • du j‖ * ‖d i • u₀‖ := Lp.abs_inner_lpSMul_le _ _ _
      _ ≤ ‖a i j‖ * ‖G‖ * (‖d i‖ * ‖u₀‖) := by gcongr; exacts [hGi j, Lp.norm_smul_le _ _]
      _ = _ := by ring
  have hprincipal :
      alpha * ‖G‖ ^ 2 -
          2 * (∑ i, ∑ j, ‖a i j‖ * ‖d i‖) * ‖G‖ * ‖u₀‖ ≤
        ∑ i, ∑ j, ⟪a i j • du j, derivCoordCLM i v⟫_ℝ := by
    have he := aeUniformlyElliptic_energy_le a ha (fun i ↦ q • du i)
    simp only [real_inner_self_eq_norm_sq, multiplicationCoefficientOperator_apply,
      hGs] at he
    have hc := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦
      Finset.sum_le_sum (s := Finset.univ) fun j _ ↦
        (neg_le_abs _).trans (hcross i j)
    simp only [Finset.sum_neg_distrib, ← Finset.sum_mul] at hc
    simp only [hpr, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    linarith
  have hbterm (i : Fin n) : |⟪b i • du i, baseCoordCLM v⟫_ℝ| ≤
      ‖b i‖ * ‖G‖ * (‖q‖ * ‖u₀‖) := by
    rw [hv₀, ← Lp.inner_lpSMul_left, lpSMul_top_top_two_comm]
    exact (Lp.abs_inner_lpSMul_le _ _ _).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (hGi i) (norm_nonneg _))
        (Lp.norm_smul_le _ _) (norm_nonneg _) (by positivity))
  have hb : -(∑ i, ⟪b i • du i, baseCoordCLM v⟫_ℝ) ≤
      (∑ i, ‖b i‖) * ‖q‖ * ‖G‖ * ‖u₀‖ := by
    rw [← Finset.sum_neg_distrib]
    exact (Finset.sum_le_sum fun i _ ↦ (neg_le_abs _).trans (hbterm i)).trans_eq
      (by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring)
  have hqbase : ‖baseCoordCLM v‖ ≤ ‖q‖ ^ 2 * ‖u₀‖ := by
    rw [hv₀, sq, mul_assoc]
    exact (Lp.norm_smul_le _ _).trans (by gcongr; exact Lp.norm_smul_le _ _)
  have hc : -⟪c • u₀, baseCoordCLM v⟫_ℝ ≤ ‖c‖ * ‖q‖ ^ 2 * ‖u₀‖ ^ 2 :=
    (neg_le_abs _).trans ((Lp.abs_inner_lpSMul_le _ _ _).trans
      ((mul_le_mul_of_nonneg_left hqbase (by positivity)).trans_eq (by ring)))
  have hf : ⟪f, baseCoordCLM v⟫_ℝ ≤ ‖f‖ * ‖q‖ ^ 2 * ‖u₀‖ :=
    (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left hqbase (norm_nonneg _)).trans_eq (by ring)))
  have hweak := hu.equation v
  change (∑ i, ∑ j, ⟪a i j • du j, derivCoordCLM i v⟫_ℝ) +
    (∑ i, ⟪b i • du i, baseCoordCLM v⟫_ℝ) +
    ⟪c • u₀, baseCoordCLM v⟫_ℝ = ⟪f, baseCoordCLM v⟫_ℝ at hweak
  have he : alpha * ‖G‖ ^ 2 ≤ M * ‖G‖ * ‖u₀‖ +
      ‖c‖ * ‖q‖ ^ 2 * ‖u₀‖ ^ 2 + ‖f‖ * ‖q‖ ^ 2 * ‖u₀‖ := by
    dsimp only [M]
    nlinarith only [hprincipal, hb, hc, hf, hweak]
  let R : ℝ := ‖f‖ + ‖u₀‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have huR : ‖u₀‖ ≤ R := le_add_of_nonneg_left (norm_nonneg f)
  have hfR : ‖f‖ ≤ R := le_add_of_nonneg_right (norm_nonneg u₀)
  have he' : alpha * ‖G‖ ^ 2 ≤ M * ‖G‖ * R + D * R ^ 2 := calc
    _ ≤ M * ‖G‖ * R + ‖c‖ * ‖q‖ ^ 2 * R ^ 2 + R * ‖q‖ ^ 2 * R := he.trans (by gcongr)
    _ = _ := by dsimp only [D]; ring
  have hG : ‖G‖ ≤ C * R := by
    by_contra! h
    have hRG : R < ‖G‖ := (le_mul_of_one_le_left hR hC).trans_lt h
    have hGpos : 0 < ‖G‖ := hR.trans_lt hRG
    have hmul := mul_lt_mul_of_pos_left h (mul_pos ha.1 hGpos)
    have hDR : D * R ^ 2 ≤ D * ‖G‖ * R := by
      nlinarith [mul_nonneg hD hR]
    nlinarith [hCa, mul_pos ha.1 (mul_pos hGpos hGpos)]
  exact fun i ↦ (hGi i).trans hG

/-- On a relatively compact open set the full H¹ norm is controlled by the
global L² norms of the forcing and state. This removes the gradient remainder
from subsequent interior regularity estimates. -/
theorem exists_interior_h1_estimate
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha : ℝ} (ha : AEUniformlyElliptic a alpha)
    {V : Set (ℝ^n)} (hV : IsOpen V) (hcompact : IsCompact (closure V))
    (hVΩ : closure V ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : DerivLp n 2 Ω) (u : H¹(Ω)),
      IsInteriorWeakFullDivergenceSolution a b c f u →
      ‖restrictCLM hV.measurableSet (subset_closure.trans hVΩ) u‖ ≤
        C * (‖f‖ + ‖wkpBaseCoordinateCLM u‖) := by
  classical
  by_cases hΩ : IsOpen Ω
  swap
  · exact ⟨1, one_pos, fun f u hu ↦ absurd hu.1 hΩ⟩
  obtain ⟨η, hη, hηone, _⟩ :=
    _root_.TestFunction.exists_eq_one_on_compact hΩ hcompact hVΩ
  obtain ⟨C, hC, hbound⟩ := exists_cutoff_gradient_estimate hΩ a b c ha η hη
  refine ⟨1 + n * C, by positivity, fun f u hu ↦ ?_⟩
  let R : ℝ := ‖f‖ + ‖wkpBaseCoordinateCLM u‖
  let hsub : V ⊆ Ω := subset_closure.trans hVΩ
  have heq (i : Fin n) :
      restrictDerivLp hsub
          (testFunctionLpTop (Ω := Ω) η • wkpCoordinateCLM (singleDerivIndex n i) u) =
        restrictDerivLp hsub (wkpCoordinateCLM (singleDerivIndex n i) u) := by
    apply Lp.ext
    filter_upwards [restrictDerivLp_apply_ae hsub
      (testFunctionLpTop (Ω := Ω) η • wkpCoordinateCLM (singleDerivIndex n i) u),
      restrictDerivLp_apply_ae hsub (wkpCoordinateCLM (singleDerivIndex n i) u),
      ae_mono (domainMeasure_le hsub) (Lp.coeFn_lpSMul
        (r := (2 : ℝ≥0∞)) (testFunctionLpTop (Ω := Ω) η)
        (wkpCoordinateCLM (singleDerivIndex n i) u)),
      ae_mono (domainMeasure_le hsub) (testFunctionLpTop_apply_ae (Ω := Ω) η),
      ae_restrict_mem hV.measurableSet] with x hx hy hz hq hxV
    rw [hx, hy, hz, Pi.smul_apply', hq, hηone x (subset_closure hxV), one_smul]
  have hderiv (i : Fin n) :
      ‖restrictDerivLp hsub (wkpCoordinateCLM (singleDerivIndex n i) u)‖ ≤ C * R :=
    heq i ▸ (norm_restrictDerivLp_le hsub _).trans (hbound f u hu i)
  have hbase : ‖restrictDerivLp hsub (wkpBaseCoordinateCLM u)‖ ≤ R :=
    (norm_restrictDerivLp_le hsub _).trans (le_add_of_nonneg_left (norm_nonneg f))
  calc
    _ ≤ ‖restrictDerivLp hsub (wkpBaseCoordinateCLM u)‖ +
        ∑ i, ‖restrictDerivLp hsub (wkpCoordinateCLM (singleDerivIndex n i) u)‖ := by
      change ‖(restrictCLM hV.measurableSet hsub u : WkpAmbientOn n 1 2 V)‖ ≤ _
      rw [restrictCLM_apply_coe]
      have hn := ambient_norm_le_base_add_sum_deriv
        (restrictCLM hV.measurableSet hsub u : WkpAmbientOn n 1 2 V)
      simpa only [restrictCLM_apply_coe, restrictAmbient_apply,
        wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply] using hn
    _ ≤ R + ∑ _i : Fin n, C * R :=
      add_le_add hbase (Finset.sum_le_sum fun i _ ↦ hderiv i)
    _ = (1 + n * C) * R := by simp; ring

end SobolevSpace.GraphSpace
