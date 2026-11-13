/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.FiniteEstimate
public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.FiniteApproximation
import PDE.Spaces.Sobolev.GraphSpace.Topology.SupportedBall

/-!
# Quantitative composition of finite Sobolev families

For `n < 2k`, a smooth zero-preserving reaction of finitely many scalar
Sobolev functions has a Sobolev graph. Its norm has a continuous bound that
is nondecreasing in every input norm, as in Evans §12.2.2, Theorem 2(ii).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.2.2, Theorem 2(ii), estimate (7), p. 666: for `k > n/2`,
  smooth `f` with `f(0) = 0` and `u_1, ..., u_m ∈ Hᵏ(ℝ^n)`,
  `‖f(u)‖_{Hᵏ} ≤ Φ(‖u_1‖_{Hᵏ}, ..., ‖u_m‖_{Hᵏ})` with `Φ` continuous and nondecreasing in each
  argument.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Set
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.Composition

open GraphSpace GagliardoNirenberg

variable {n k m : ℕ} [NeZero n]

omit [NeZero n] in
private theorem exists_finite_composition_of_approximation
    {f : (Fin m → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (U : Fin m → W^{k,2}(ℝ^n)) (v : ℕ → ℝ^n → Fin m → ℝ)
    (hv : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j)) (hc : ∀ j, HasCompactSupport (v j))
    (hlim : ∀ i, Tendsto (fun j ↦ mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ)
      (fun x ↦ v j x i) ((contDiff_apply ℝ (fun _ ↦ ℝ) i).comp (hv j))
      ((hc j).comp_left (g := fun y : Fin m → ℝ ↦ y i) rfl)) atTop (𝓝 (U i)))
    {S B : ℝ} (hS : 0 ≤ S) (hvpoint : ∀ j x, ‖v j x‖ ≤ S)
    (hUpoint : ∀ᵐ x ∂volume, ‖fun i ↦ baseRepresentative (U i) x‖ ≤ S)
    (hWnorm : ∀ j, ‖mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ)
      (f ∘ v j) (hf.comp (hv j)) ((hc j).comp_left hf0)‖ ≤ B) :
    ∃ W : W^{k,2}(ℝ^n),
      baseRepresentative W =ᵐ[volume] (fun x ↦ f (fun i ↦ baseRepresentative (U i) x)) ∧
      ‖W‖ ≤ B := by
  let V (j : ℕ) (i : Fin m) : W^{k,2}(ℝ^n) :=
    mkWkpSpaceOnOfContDiff (fun x ↦ v j x i) ((contDiff_apply ℝ (fun _ ↦ ℝ) i).comp (hv j))
      ((hc j).comp_left (g := fun y : Fin m → ℝ ↦ y i) rfl)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  obtain ⟨K, hK⟩ := hf1.contDiffOn.exists_lipschitzOnWith
    one_ne_zero (convex_closedBall (0 : Fin m → ℝ) S) (isCompact_closedBall _ _)
  obtain ⟨g, hg, hgf⟩ := hK.extend_real
  have hg0 : g 0 = 0 := (hgf (by simpa using hS)).symm.trans hf0
  let T := finiteTupleL2 (m := m) (domainMeasure n univ)
  let Ubase := T (fun i ↦ wkpBaseCoordinateCLM (U i))
  let Vbase (j : ℕ) := T (fun i ↦ wkpBaseCoordinateCLM (V j i))
  have hVbase : Tendsto Vbase atTop (𝓝 Ubase) :=
    T.continuous.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr fun i ↦
      wkpBaseCoordinateCLM.continuous.continuousAt.tendsto.comp (hlim i))
  have hVae (j : ℕ) : Vbase j =ᵐ[domainMeasure n univ] v j := by
    have he := ae_all_iff.mpr fun (i : Fin m) ↦ mkWkpSpaceOnOfContDiff_apply_ae
      (k := k) (p := (2 : ℝ≥0∞)) (Ω := univ) (fun x ↦ v j x i)
      ((contDiff_apply ℝ (fun _ ↦ ℝ) i).comp (hv j))
      ((hc j).comp_left (g := fun y : Fin m → ℝ ↦ y i) rfl) (baseIndex n k)
    filter_upwards [finiteTupleL2_ae _ (fun i ↦ wkpBaseCoordinateCLM (V j i)), he] with x hx hy
    exact hx.trans (funext fun i ↦ by
      simpa only [wkpBaseCoordinateCLM_apply, V, baseIndex_toList, iteratedPartialDeriv]
        using hy i)
  let W (j : ℕ) : W^{k,2}(ℝ^n) :=
    mkWkpSpaceOnOfContDiff (f ∘ v j) (hf.comp (hv j)) ((hc j).comp_left hf0)
  have hWbase (j : ℕ) : wkpBaseCoordinateCLM (W j) = hg.compLp hg0 (Vbase j) := by
    apply Lp.ext
    have he := mkWkpSpaceOnOfContDiff_apply_ae (k := k) (p := (2 : ℝ≥0∞)) (Ω := univ)
      (f ∘ v j) (hf.comp (hv j)) ((hc j).comp_left hf0) (baseIndex n k)
    filter_upwards [he, hg.coeFn_compLp hg0 (Vbase j), hVae j] with x hx hy hz
    change (W j).val (baseIndex n k) x = _
    simp only [baseIndex_toList, iteratedPartialDeriv, Function.comp_apply] at hx hy
    exact hx.trans ((hgf (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hvpoint j x)).trans
      ((congrArg g hz).symm.trans hy.symm))
  have hWlim : Tendsto (fun j ↦ wkpBaseCoordinateCLM (W j)) atTop (𝓝 (hg.compLp hg0 Ubase)) := by
    simpa only [hWbase, Function.comp_def] using
      (hg.continuous_compLp hg0).continuousAt.tendsto.comp hVbase
  obtain ⟨w, hwnorm, hwbase⟩ := exists_hk_of_tendsto_base W _ hWnorm hWlim
  refine ⟨w, ?_, hwnorm⟩
  have he : baseRepresentative w =ᵐ[domainMeasure n univ]
      fun x ↦ g (fun i ↦ baseRepresentative (U i) x) := by
    change (wkpBaseCoordinateCLM w : ℝ^n → ℝ) =ᵐ[_] _
    rw [hwbase]
    filter_upwards [hg.coeFn_compLp hg0 Ubase,
      finiteTupleL2_ae _ (fun i ↦ wkpBaseCoordinateCLM (U i))] with x hx hy
    exact hx.trans (congrArg g hy)
  simp only [domainMeasure, Measure.restrict_univ] at he
  filter_upwards [he, hUpoint] with x hx hy
  exact hx.trans (hgf (by simpa only [Metric.mem_closedBall, dist_zero_right] using hy)).symm

/-- Evans §12.2.2, Theorem 2(ii): if `n < 2k`, `f` is smooth and `f 0 = 0`, there is a continuous,
coordinatewise nondecreasing `Φ` such that for every `U : Fin m → Hᵏ(ℝ^n)` some `W ∈ Hᵏ(ℝ^n)`
represents `f ∘ U` almost everywhere and `‖W‖ ≤ Φ (fun i ↦ ‖U i‖)`. -/
theorem exists_finite_composition_bound (hk : (n : ℝ) < 2 * (k : ℝ))
    {f : (Fin m → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) :
    ∃ Φ : (Fin m → ℝ) → ℝ, Continuous Φ ∧ Monotone Φ ∧
      ∀ U : Fin m → W^{k,2}(ℝ^n), ∃ W : W^{k,2}(ℝ^n),
        baseRepresentative W =ᵐ[volume] (fun x ↦ f (fun i ↦ baseRepresentative (U i) x)) ∧
        ‖W‖ ≤ Φ (fun i ↦ ‖U i‖) := by
  classical
  obtain ⟨A₁, hA₁, hsmooth⟩ := Product.exists_smooth_derivative_bound hk
  obtain ⟨A₂, hA₂, hweak⟩ := Product.exists_coordinate_lpNorm_bound hk
  let A := max A₁ A₂
  have hA : 0 ≤ A := (zero_le_one.trans hA₁).trans (le_max_left _ _)
  let radius (t : Fin m → ℝ) := 1 + ∑ i, max (t i) 0
  let Φ (t : Fin m → ℝ) := finiteCompositionBound hf n k A (radius t)
  have hrad : Continuous radius := continuous_const.add
    (continuous_finsetSum Finset.univ (fun i _ ↦ (continuous_apply i).max continuous_const))
  have hradmono : Monotone radius := by
    intro t s hts
    exact add_le_add le_rfl (Finset.sum_le_sum fun i _ ↦ max_le_max_right 0 (hts i))
  refine ⟨Φ, (continuous_finiteCompositionBound hf n k A).comp hrad,
    (monotone_finiteCompositionBound hf n k hA).comp hradmono, ?_⟩
  intro U
  let R := radius (fun i ↦ ‖U i‖)
  have hR0 : 0 ≤ R := by dsimp [R, radius]; positivity
  have hRi (i : Fin m) : ‖U i‖ + 1 ≤ R := by
    have h := Finset.single_le_sum (fun l _ ↦ norm_nonneg (U l)) (Finset.mem_univ i)
    have he : R = 1 + ∑ j, ‖U j‖ := by
      dsimp only [R, radius]
      congr 1
      exact Finset.sum_congr rfl (fun j _ ↦ max_eq_left (norm_nonneg (U j)))
    calc
      ‖U i‖ + 1 ≤ (∑ j, ‖U j‖) + 1 := add_le_add h le_rfl
      _ = R := by rw [he]; ring
  obtain ⟨v, hv, hc, hvR, hlim⟩ := exists_finite_smooth_approximation U
  let V (j : ℕ) (i : Fin m) : W^{k,2}(ℝ^n) :=
    mkWkpSpaceOnOfContDiff (fun x ↦ v j x i) ((contDiff_apply ℝ (fun _ ↦ ℝ) i).comp (hv j))
      ((hc j).comp_left (g := fun y : Fin m → ℝ ↦ y i) rfl)
  have hVR (j : ℕ) (i : Fin m) : ‖V j i‖ ≤ max R 0 :=
    (hvR j i).trans ((hRi i).trans (le_max_left _ _))
  have hinterp (w : ℝ^n → ℝ) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
      (hwc : HasCompactSupport w) (d : ℕ) (hd : d ≤ k)
      (α : List (Fin n)) (hα : α.length ≤ d) :
      lpNorm (iteratedPartialDeriv α w) (derivativeExponent d α.length) volume ≤
        A * ‖mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) w hw hwc‖ :=
    (hsmooth w hw hwc d hd α hα).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hvpoint (j : ℕ) (x : ℝ^n) : ‖v j x‖ ≤ A * R := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hA hR0)).mpr
    intro i
    have h := hinterp (fun x ↦ v j x i) ((contDiff_apply ℝ (fun _ ↦ ℝ) i).comp (hv j))
      ((hc j).comp_left (g := fun y : Fin m → ℝ ↦ y i) rfl) 0 (Nat.zero_le k) [] (by simp)
    simp only [List.length_nil, iteratedPartialDeriv, derivativeExponent_zero] at h
    apply (Product.norm_le_lpNorm_top_of_continuous
      ((contDiff_apply ℝ (fun _ ↦ ℝ) i).comp (hv j)).continuous
      (((contDiff_apply ℝ (fun _ ↦ ℝ) i).comp (hv j)).continuous.memLp_of_hasCompactSupport
        ((hc j).comp_left (g := fun y : Fin m → ℝ ↦ y i) rfl)) x).trans
    exact h.trans (mul_le_mul_of_nonneg_left ((hvR j i).trans (hRi i)) hA)
  have hUpoint : ∀ᵐ x ∂volume, ‖fun i ↦ baseRepresentative (U i) x‖ ≤ A * R := by
    have hi (i : Fin m) : ∀ᵐ x ∂volume, ‖baseRepresentative (U i) x‖ ≤ A * R := by
      have hm := Product.memLp_coordinate_derivativeExponent hk (Nat.zero_le k)
        (baseIndex n 0) (U i)
      have hb := hweak 0 (Nat.zero_le k) (baseIndex n 0) (U i)
      simp only [baseIndex_toList, List.length_nil, derivativeExponent_zero,
        DerivIndex.castOrder_baseIndex, domainMeasure, Measure.restrict_univ] at hm hb
      filter_upwards [ae_le_lpNorm_exponent_top hm] with x hx
      apply hx.trans (hb.trans _)
      apply mul_le_mul (le_max_right _ _) ((le_add_of_nonneg_right zero_le_one).trans (hRi i))
        (norm_nonneg (U i)) hA
    filter_upwards [ae_all_iff.mpr hi] with x hx
    exact (pi_norm_le_iff_of_nonneg (mul_nonneg hA hR0)).mpr hx
  exact exists_finite_composition_of_approximation hf hf0 U v hv hc hlim
    (mul_nonneg hA hR0) hvpoint hUpoint (fun j ↦
      norm_smooth_finite_composition_le hk hf hf0 (hv j) (hc j) hA hinterp (hVR j))

end SobolevSpace.Composition
