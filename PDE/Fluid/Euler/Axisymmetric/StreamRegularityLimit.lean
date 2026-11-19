/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Euler.Axisymmetric.StreamRegularityBounds

/-!
# Stream functions of limits of smooth sources

Let `Ω_j` be smooth vorticity profiles, odd and `L`-periodic in `z`, converging pointwise to `Ω₀`,
and Cauchy for the derivatives `∂_s^l ∂_z^{2n}`, `l ≤ n`, uniformly on the collar, for some
`n ≥ 2`. By the bound `norm_iteratedFDeriv_streamProfile_le` the stream profiles
`Ψ_j = streamProfile L Ω_j` are Cauchy in `Cⁿ` uniformly on the plane, so they converge with their
derivatives of order at most `n` to a `Cⁿ` function `Ψ₀` (`contDiff_and_tendsto_of_cauchy`) that
solves `-(8 Ψ_s + 4 s Ψ_ss + Ψ_zz) = Ω₀` on `0 < s < 1`, vanishes at `s = 1`, and is odd and
periodic in `z`. Then `φ(r, z) = r Ψ₀(r², z)` is a `Cⁿ` stream function of `r Ω₀(r², z)` in the
cylinder (`exists_isStreamFunction_of_tendsto`). This is how the stream function is obtained for
sources of finite regularity, from smooth approximants.

## Main results

* `streamOperator_mul_comp_squaredRadiusMap`: the stream operator of `r Ψ(r², z)` for a `C²`
  profile solving the reduced equation.
* `exists_tendstoUniformly_of_cauchy`: uniform limits of uniformly Cauchy sequences.
* `contDiff_and_tendsto_of_cauchy`: limits of sequences that are Cauchy in `Cⁿ`.
* `exists_isStreamFunction_of_tendsto`: the stream function of the limit source.
-/

@[expose] public section

namespace Euler.Cylinder

open Set Filter PDE.Analysis.Fourier.SineSeries EuclideanSpace
open AxisymmetricFlow (squaredRadiusMap contDiff_squaredRadiusMap)
open scoped Topology Real

set_option linter.missingDocs true

noncomputable section

variable {L : ℝ}

/-- **The stream operator of an axis-regular stream function.** If `Ψ` is `C²` at `(r², z)` and
solves `8 Ψ_s + 4 s Ψ_ss + Ψ_zz = -Ω` there, with `0 < r`, then `φ(r, z) = r Ψ(r², z)` satisfies
`-(φ_rr + φ_r / r + φ_zz) + φ / r² = r Ω(r², z)` at `(r, z)`. -/
theorem streamOperator_mul_comp_squaredRadiusMap {Ψ : ℝ^2 → ℝ} {Ω : ℝ × ℝ → ℝ} {x : ℝ^2}
    (hx : 0 < x 0) (hΨ : ContDiffAt ℝ 2 Ψ (squaredRadiusMap x))
    (heq : 8 * (∂[(0 : Fin 2)] Ψ) (squaredRadiusMap x) +
        4 * squaredRadiusMap x 0 * (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] Ψ)) (squaredRadiusMap x) +
        (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] Ψ)) (squaredRadiusMap x) =
      -Ω (squaredRadiusMap x 0, squaredRadiusMap x 1)) :
    streamOperator (fun y ↦ y 0 * Ψ (squaredRadiusMap y)) x = meridianVorticity Ω x := by
  set A := profileProjection
  set Ω₃ : ℝ^3 → ℝ := fun q ↦ Ω (q 1, q 2)
  set q := meridianProfilePoint 0 x
  have hAq : A q = squaredRadiusMap x := profileProjection_meridianProfilePoint 0 x
  have hΨA : ContDiffAt ℝ 2 Ψ (A q) := by rw [hAq]; exact hΨ
  have hΨ3 : ContDiffAt ℝ 2 (Ψ ∘ A) q := hΨA.comp q A.contDiff.contDiffAt
  have hres := streamResidual_ofProfiles (U := 0) (Ω := Ω₃) (Ψ := Ψ ∘ A) (t := 0)
    (ne_of_gt hx) hΨ3
  have hfun : (fun y ↦ (ofProfiles 0 Ω₃ (Ψ ∘ A)).streamFunction y 0) =
      fun y ↦ y 0 * Ψ (squaredRadiusMap y) := by
    funext y
    simp [ofProfiles, profileProjection_meridianProfilePoint, A]
  rw [hfun] at hres
  have hA1 : A (single (1 : Fin 3) 1) = (1 : ℝ) • single (0 : Fin 2) 1 := by
    ext i
    fin_cases i <;> simp [A, profileProjection]
  have hA2 : A (single (2 : Fin 3) 1) = (1 : ℝ) • single (1 : Fin 2) 1 := by
    ext i
    fin_cases i <;> simp [A, profileProjection]
  have hdiff : AxisymmetricFlow.spacetimeSquaredRadiusDiffusion (Ψ ∘ A) q = -Ω₃ q := by
    unfold AxisymmetricFlow.spacetimeSquaredRadiusDiffusion
    rw [PDE.CoordinateSystems.partialDeriv_comp_clm_of_eq A hA1
        (hΨA.differentiableAt (by norm_num)),
      PDE.CoordinateSystems.secondPartialDeriv_comp_clm_of_eq A hA1 hΨA,
      PDE.CoordinateSystems.secondPartialDeriv_comp_clm_of_eq A hA2 hΨA, hAq]
    have hq1 : q 1 = squaredRadiusMap x 0 := by
      simp [q, meridianProfilePoint, profilePoint, squaredRadiusMap]
    rw [hq1]
    have hΩq : Ω₃ q = Ω (squaredRadiusMap x 0, squaredRadiusMap x 1) := by
      simp [Ω₃, q, meridianProfilePoint, profilePoint, squaredRadiusMap]
    rw [hΩq, ← heq]
    ring
  rw [hdiff, neg_neg, sub_self, mul_zero, sub_eq_zero] at hres
  rw [hres]
  simp [ofProfiles, meridianVorticity, Ω₃, meridianProfilePoint, profilePoint]

/-- A sequence of functions that is uniformly Cauchy converges uniformly, and pointwise, to a
limit. -/
theorem exists_tendstoUniformly_of_cauchy {X β : Type*} [NormedAddCommGroup β] [CompleteSpace β]
    {F : ℕ → X → β} (h : ∀ ε > 0, ∃ N, ∀ i ≥ N, ∀ j ≥ N, ∀ x, ‖F i x - F j x‖ ≤ ε) :
    ∃ G : X → β, TendstoUniformly F G atTop ∧ ∀ x, Tendsto (fun j ↦ F j x) atTop (𝓝 (G x)) := by
  have hc : ∀ x, CauchySeq fun j ↦ F j x := by
    intro x
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
    exact ⟨N, fun n hn ↦ by rw [dist_eq_norm]; linarith [hN n hn N le_rfl x]⟩
  choose G hG using fun x ↦ cauchySeq_tendsto_of_complete (hc x)
  refine ⟨G, ?_, hG⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
  filter_upwards [eventually_ge_atTop N] with i hi x
  have hlim : Tendsto (fun j ↦ ‖F i x - F j x‖) atTop (𝓝 ‖F i x - G x‖) :=
    (tendsto_const_nhds.sub (hG x)).norm
  have hle : ‖F i x - G x‖ ≤ ε / 2 :=
    le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun j hj ↦ hN i hi j hj x⟩)
  rw [dist_eq_norm, norm_sub_rev]
  linarith

/-- **Limits of sequences that are Cauchy in `Cⁿ`.** If the functions `f j` are `Cⁿ`, converge
pointwise to `g`, and the derivatives of order at most `n` of `f i - f j` are uniformly small for
large `i, j`, then `g` is `Cⁿ` and the derivatives of order at most `n` of `f j` converge
pointwise to those of `g`. -/
theorem contDiff_and_tendsto_of_cauchy {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (n : ℕ) {f : ℕ → E → F}
    {g : E → F} (hf : ∀ j, ContDiff ℝ n (f j))
    (hg : ∀ x, Tendsto (fun j ↦ f j x) atTop (𝓝 (g x)))
    (hc : ∀ ε > 0, ∃ N, ∀ i ≥ N, ∀ j ≥ N, ∀ k ≤ n, ∀ x,
      ‖iteratedFDeriv ℝ k (fun y ↦ f i y - f j y) x‖ ≤ ε) :
    ContDiff ℝ n g ∧ ∀ k ≤ n, ∀ x,
      Tendsto (fun j ↦ iteratedFDeriv ℝ k (f j) x) atTop (𝓝 (iteratedFDeriv ℝ k g x)) := by
  induction n generalizing F with
  | zero =>
    obtain ⟨G, hGu, hG⟩ := exists_tendstoUniformly_of_cauchy (F := f) fun ε hε ↦ by
      obtain ⟨N, hN⟩ := hc ε hε
      exact ⟨N, fun i hi j hj x ↦ by
        simpa [norm_iteratedFDeriv_zero] using hN i hi j hj 0 le_rfl x⟩
    have hGg : G = g := funext fun x ↦ tendsto_nhds_unique (hG x) (hg x)
    rw [hGg] at hGu
    refine ⟨?_, fun k hk x ↦ ?_⟩
    · rw [Nat.cast_zero, contDiff_zero]
      exact hGu.continuous (Frequently.of_forall fun j ↦ (hf j).continuous)
    · obtain rfl : k = 0 := by omega
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact ((continuousMultilinearCurryFin0 ℝ E F).symm.continuous.tendsto _).comp (hg x)
  | succ n ih =>
    have hd : ∀ j, Differentiable ℝ (f j) := fun j ↦ (hf j).differentiable (by simp)
    have hf' : ∀ j, ContDiff ℝ n (fderiv ℝ (f j)) := fun j ↦
      (hf j).fderiv_right (m := n) (by push_cast; exact le_rfl)
    have hc' : ∀ ε > 0, ∃ N, ∀ i ≥ N, ∀ j ≥ N, ∀ k ≤ n, ∀ x,
        ‖iteratedFDeriv ℝ k (fun y ↦ fderiv ℝ (f i) y - fderiv ℝ (f j) y) x‖ ≤ ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hc ε hε
      refine ⟨N, fun i hi j hj k hk x ↦ ?_⟩
      have hfun : (fun y ↦ fderiv ℝ (f i) y - fderiv ℝ (f j) y) =
          fderiv ℝ (fun y ↦ f i y - f j y) :=
        funext fun y ↦ (fderiv_fun_sub (hd i y) (hd j y)).symm
      rw [hfun, norm_iteratedFDeriv_fderiv]
      exact hN i hi j hj (k + 1) (by omega) x
    obtain ⟨G', hG'u, hG'⟩ := exists_tendstoUniformly_of_cauchy
        (F := fun j ↦ fderiv ℝ (f j)) fun ε hε ↦ by
      obtain ⟨N, hN⟩ := hc' ε hε
      exact ⟨N, fun i hi j hj x ↦ by
        simpa [norm_iteratedFDeriv_zero] using hN i hi j hj 0 (Nat.zero_le _) x⟩
    obtain ⟨hG'n, hjets⟩ := ih hf' hG' hc'
    have hgd : ∀ x, HasFDerivAt g (G' x) x := hasFDerivAt_of_tendstoUniformly hG'u
      (fun j x ↦ (hd j x).hasFDerivAt) hg
    have hfg : fderiv ℝ g = G' := funext fun x ↦ (hgd x).fderiv
    refine ⟨?_, fun k hk x ↦ ?_⟩
    · have h := (contDiff_succ_iff_hasFDerivAt (n := n)).2 ⟨G', hG'n, hgd⟩
      exact_mod_cast h
    · rcases k with _ | k
      · simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
        exact ((continuousMultilinearCurryFin0 ℝ E F).symm.continuous.tendsto _).comp (hg x)
      · have hrw : ∀ φ : E → F, iteratedFDeriv ℝ (k + 1) φ x =
            (continuousMultilinearCurryRightEquiv' ℝ k E F).symm
              (iteratedFDeriv ℝ k (fun y ↦ fderiv ℝ φ y) x) := fun φ ↦
          iteratedFDeriv_succ_eq_comp_right
        rw [hrw g, hfg]
        simp only [hrw]
        exact ((continuousMultilinearCurryRightEquiv' ℝ k E F).symm.continuous.tendsto _).comp
          (hjets k (by omega) x)

/-- For a `C²` function the second partial derivative in one coordinate is the second Fréchet
derivative on the coordinate vector. -/
theorem secondPartialDeriv_eq_fderiv_fderiv {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin 2)
    (p : ℝ^2) :
    (∂[i] (∂[i] f)) p = fderiv ℝ (fderiv ℝ f) p (single i 1) (single i 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) p
  unfold PDE.partialDeriv
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- For a `C²` function the second partial derivative in one coordinate is the second iterated
derivative on the coordinate vector. -/
theorem secondPartialDeriv_eq_iteratedFDeriv_two {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 2 f)
    (i : Fin 2) (p : ℝ^2) :
    (∂[i] (∂[i] f)) p = iteratedFDeriv ℝ 2 f p (fun _ ↦ single i 1) := by
  rw [secondPartialDeriv_eq_fderiv_fderiv hf, iteratedFDeriv_two_apply]

/-- **The stream function of a limit source.** Let `n ≥ 2` and `Ω_j` be smooth vorticity
profiles, odd and `L`-periodic in `z`, converging pointwise to `Ω₀`, such that the derivatives
`∂_s^l ∂_z^{2n} (Ω_i - Ω_j)`, `l ≤ n`, are uniformly small on the collar for large `i, j`. Then
`r Ω₀(r², z)` has a `Cⁿ` stream function in the cylinder with period `L`, odd in `z`, of the
axis-regular form `r Ψ₀(r², z)` with `Ψ₀` a `Cⁿ` function. -/
theorem exists_isStreamFunction_of_tendsto (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
    {Ω : ℕ → ℝ × ℝ → ℝ} {Ω₀ : ℝ × ℝ → ℝ} (hΩ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (Ω j))
    (hper : ∀ j s z, Ω j (s, z + L) = Ω j (s, z)) (hodd : ∀ j s z, Ω j (s, -z) = -Ω j (s, z))
    (hlim : ∀ q, Tendsto (fun j ↦ Ω j q) atTop (𝓝 (Ω₀ q)))
    (hcauchy : ∀ ε > 0, ∃ N, ∀ i ≥ N, ∀ j ≥ N, ∀ l ≤ n, ∀ s ∈ modeCollar L, ∀ z ∈ Icc 0 L,
      |(sDeriv^[l] (zDeriv^[2 * n] (fun q ↦ Ω i q - Ω j q))) (s, z)| ≤ ε) :
    ∃ φ : ℝ^2 → ℝ, IsStreamFunction L (meridianVorticity Ω₀) φ ∧ ContDiff ℝ n φ ∧
      (∀ x, φ (axialReflection x) = -φ x) ∧
      ∃ Ψ₀ : ℝ^2 → ℝ, ContDiff ℝ n Ψ₀ ∧ ∀ x, φ x = x 0 * Ψ₀ (squaredRadiusMap x) := by
  set Ψ : ℕ → ℝ^2 → ℝ := fun j ↦ streamProfile L (Ω j) with hΨdef
  have hΨ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (Ψ j) := fun j ↦ contDiff_streamProfile hL (hΩ j) (hper j)
  have hΨn : ∀ j, ContDiff ℝ n (Ψ j) := fun j ↦
    (hΨ j).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hΨ2 : ∀ j, ContDiff ℝ 2 (Ψ j) := fun j ↦
    (hΨ j).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hdiff : ∀ i j, (fun p ↦ Ψ i p - Ψ j p) = streamProfile L (fun q ↦ Ω i q - Ω j q) :=
    fun i j ↦ funext fun p ↦ (streamProfile_sub hL (hΩ i) (hΩ j) (hper i) (hper j) p).symm
  have hDs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun q ↦ Ω i q - Ω j q) := fun i j ↦ (hΩ i).sub (hΩ j)
  have hDp : ∀ i j s z, (fun q ↦ Ω i q - Ω j q) (s, z + L) = (fun q ↦ Ω i q - Ω j q) (s, z) :=
    fun i j s z ↦ by simp only [hper i, hper j]
  set K : ℝ := ∑ m ∈ Finset.range (n + 1), profileBoundConst L n m + 1
  have hsum0 : 0 ≤ ∑ m ∈ Finset.range (n + 1), profileBoundConst L n m :=
    Finset.sum_nonneg fun m _ ↦ profileBoundConst_nonneg L n m
  have hKpos : 0 < K := by linarith
  have hKn : ∀ m ≤ n, profileBoundConst L n m ≤ K := fun m hm ↦
    (Finset.single_le_sum (f := fun m ↦ profileBoundConst L n m)
      (fun m _ ↦ profileBoundConst_nonneg L n m) (Finset.mem_range.2 (Nat.lt_succ_of_le hm))).trans
      (by linarith)
  have hbd : ∀ ε > 0, ∃ N, ∀ i ≥ N, ∀ j ≥ N, ∀ m ≤ n, ∀ p,
      ‖iteratedFDeriv ℝ m (fun p ↦ Ψ i p - Ψ j p) p‖ ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy (ε / K) (div_pos hε hKpos)
    refine ⟨N, fun i hi j hj m hm p ↦ ?_⟩
    rw [hdiff]
    refine (norm_iteratedFDeriv_streamProfile_le hL (hDs i j) (hDp i j) hm
      (fun l hl s hs z hz ↦ hN i hi j hj l (hl.trans hm) s hs z hz) p).trans
      ((mul_le_mul_of_nonneg_right (hKn m hm) (by positivity)).trans_eq (by field_simp))
  -- the limit profile and the convergence of its derivatives
  obtain ⟨Ψ₀, -, hΨ₀⟩ := exists_tendstoUniformly_of_cauchy (F := Ψ) fun ε hε ↦ by
    obtain ⟨N, hN⟩ := hbd ε hε
    exact ⟨N, fun i hi j hj p ↦ by
      simpa only [norm_iteratedFDeriv_zero] using hN i hi j hj 0 (Nat.zero_le _) p⟩
  obtain ⟨hΨ₀n, hjets⟩ := contDiff_and_tendsto_of_cauchy n hΨn hΨ₀ hbd
  have hΨ₀2 : ContDiff ℝ 2 Ψ₀ := hΨ₀n.of_le (by exact_mod_cast hn)
  -- the reduced equation passes to the limit
  have hlim1 : ∀ (i : Fin 2) x,
      Tendsto (fun j ↦ (∂[i] (Ψ j)) x) atTop (𝓝 ((∂[i] Ψ₀) x)) := fun i x ↦ by
    simp only [partialDeriv_eq_iteratedFDeriv_one]
    have hc : Continuous fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 1 ↦ ℝ^2) ℝ ↦
        T ![single i 1] := by fun_prop
    exact (hc.tendsto _).comp (hjets 1 (by omega) x)
  have hlim2 : ∀ (i : Fin 2) x,
      Tendsto (fun j ↦ (∂[i] (∂[i] (Ψ j))) x) atTop (𝓝 ((∂[i] (∂[i] Ψ₀)) x)) := fun i x ↦ by
    simp only [secondPartialDeriv_eq_iteratedFDeriv_two (hΨ2 _),
      secondPartialDeriv_eq_iteratedFDeriv_two hΨ₀2]
    have hc : Continuous fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ ℝ^2) ℝ ↦
        T (fun _ ↦ single i 1) := by fun_prop
    exact (hc.tendsto _).comp (hjets 2 hn x)
  have hprof : ∀ p : ℝ^2, p 0 ∈ Ioo (0 : ℝ) 1 →
      8 * (∂[(0 : Fin 2)] Ψ₀) p + 4 * p 0 * (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] Ψ₀)) p +
        (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] Ψ₀)) p = -Ω₀ (p 0, p 1) := by
    intro p hp
    have hL1 := ((tendsto_const_nhds (x := (8 : ℝ))).mul (hlim1 0 p)).add
      ((tendsto_const_nhds (x := 4 * p 0)).mul (hlim2 0 p)) |>.add (hlim2 1 p)
    refine tendsto_nhds_unique (hL1.congr fun j ↦ ?_) (hlim (p 0, p 1)).neg
    exact streamProfile_equation hL (hΩ j) (hper j) (hodd j) hp
  have hwall : ∀ p : ℝ^2, p 0 = 1 → Ψ₀ p = 0 := fun p hp ↦
    tendsto_nhds_unique (hΨ₀ p) (tendsto_const_nhds.congr fun j ↦ (streamProfile_wall hp).symm)
  have hperΨ : ∀ p : ℝ^2, Ψ₀ (p + single (1 : Fin 2) L) = Ψ₀ p := fun p ↦
    tendsto_nhds_unique (hΨ₀ _) ((hΨ₀ p).congr fun j ↦ (streamProfile_periodic hL p).symm)
  have hoddΨ : ∀ p : ℝ^2, Ψ₀ (axialReflection p) = -Ψ₀ p := fun p ↦
    tendsto_nhds_unique (hΨ₀ _) ((hΨ₀ p).neg.congr fun j ↦ (streamProfile_odd p).symm)
  -- the stream function
  have hφn : ContDiff ℝ n (fun x : ℝ^2 ↦ x 0 * Ψ₀ (squaredRadiusMap x)) :=
    (proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).contDiff.mul
      (hΨ₀n.comp (contDiff_squaredRadiusMap.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)))
  have hφ2 : ContDiff ℝ 2 (fun x : ℝ^2 ↦ x 0 * Ψ₀ (squaredRadiusMap x)) :=
    hφn.of_le (by exact_mod_cast hn)
  refine ⟨fun x ↦ x 0 * Ψ₀ (squaredRadiusMap x), ⟨fun x _ ↦ hφ2.contDiffAt,
    hφ2.continuous.continuousOn, fun x hx ↦ ?_, fun z ↦ by simp, fun z ↦ ?_, fun x ↦ ?_⟩,
    hφn, fun x ↦ ?_, Ψ₀, hΨ₀n, fun x ↦ rfl⟩
  · have hsr : squaredRadiusMap x 0 ∈ Ioo (0 : ℝ) 1 := by
      have h : squaredRadiusMap x 0 = x 0 ^ 2 := by simp [squaredRadiusMap]
      rw [h]
      exact ⟨pow_pos hx.1 2, by nlinarith [hx.1, hx.2]⟩
    exact streamOperator_mul_comp_squaredRadiusMap hx.1 hΨ₀2.contDiffAt
      (hprof _ hsr)
  · simp only [meridianPoint_apply_zero, one_mul]
    exact hwall _ (by simp [squaredRadiusMap])
  · simp only
    have h0 : axialTranslate L x 0 = x 0 := by simp [axialTranslate]
    have hsq : squaredRadiusMap (axialTranslate L x) =
        squaredRadiusMap x + single (1 : Fin 2) L := by
      ext i
      fin_cases i <;> simp [squaredRadiusMap, axialTranslate]
    rw [h0, hsq, hperΨ]
  · simp only
    have h0 : axialReflection x 0 = x 0 := axialReflection_apply_zero x
    have hsq : squaredRadiusMap (axialReflection x) =
        axialReflection (squaredRadiusMap x) := by
      ext i
      fin_cases i <;> simp [squaredRadiusMap]
    rw [h0, hsq, hoddΨ]
    ring

end

end Euler.Cylinder
