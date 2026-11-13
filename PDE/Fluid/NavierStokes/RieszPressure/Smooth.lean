/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.RieszPressure
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.WholeSpaceRegularity

/-!
# Smoothness of the Riesz pressure

Let `u` be a smooth velocity field on `ℝⁿ` with bounded derivatives of every order, `u ∈ L⁴`,
and derivatives of positive order in `L²`. By the Leibniz bound every derivative of a product
`uᵢuⱼ` is a sum of products of a square-integrable factor and a bounded factor, so
`uᵢuⱼ ∈ W^{m,2}(ℝⁿ)` for every `m`. The double Riesz transforms preserve these spaces, so the
Riesz pressure class lies in every `W^{m,2}(ℝⁿ)`. The Morrey embedding gives a `C^k` member of
the class for every `k`; continuous members of a class coincide, so `rieszPressure u` is that
function, hence smooth, and its derivatives are the square-integrable weak derivatives.
-/

@[expose] public section

noncomputable section

namespace NavierStokes

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional
open scoped ENNReal Sobolev

variable {n : ℕ}

/-- Products of components of a smooth field with bounded derivatives, in `L⁴`, and with
square-integrable derivatives of positive order, have square-integrable derivatives of every
order. -/
theorem memLp_iteratedFDeriv_mul_component {u : ℝ^n → ℝ^n} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hu4 : MemLp u 4 volume) (hbd : ∀ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k u x‖ ≤ C)
    (hd2 : ∀ k, 1 ≤ k → MemLp (iteratedFDeriv ℝ k u) 2 volume) (i j : Fin n) (m : ℕ) :
    MemLp (iteratedFDeriv ℝ m (fun x ↦ u x i * u x j)) 2 volume := by
  have hui (l : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ u x l) :=
    (EuclideanSpace.proj (𝕜 := ℝ) l).contDiff.comp hu
  have hprod : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ u x i * u x j) := (hui i).mul (hui j)
  have hmeas : AEStronglyMeasurable (iteratedFDeriv ℝ m (fun x ↦ u x i * u x j)) volume :=
    (hprod.continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine (memLp_two_mul_of_memLp_four hu4 i j).of_le hmeas
      (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [norm_iteratedFDeriv_zero]
  -- the Leibniz bound, term by term
  have hterm (l : ℕ) (hl : l ∈ Finset.range (m + 1)) :
      MemLp (fun x ↦ (m.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fun y ↦ u y i) x‖ *
        ‖iteratedFDeriv ℝ (m - l) (fun y ↦ u y j) x‖) 2 volume := by
    have hlm : l ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hc (a : ℕ) (k : Fin n) : Continuous (fun x ↦ ‖iteratedFDeriv ℝ a (fun y ↦ u y k) x‖) :=
      ((hui k).continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
    have hm' : AEStronglyMeasurable (fun x ↦ (m.choose l : ℝ) *
        ‖iteratedFDeriv ℝ l (fun y ↦ u y i) x‖ *
        ‖iteratedFDeriv ℝ (m - l) (fun y ↦ u y j) x‖) volume :=
      ((continuous_const.mul (hc l i)).mul (hc (m - l) j)).aestronglyMeasurable
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · obtain ⟨C, hC⟩ := hbd 0
      refine ((hd2 m hm).norm.const_mul ((m.choose 0 : ℝ) * |C|)).of_le hm'
        (Filter.Eventually.of_forall fun x ↦ ?_)
      have h0 : ‖iteratedFDeriv ℝ 0 (fun y ↦ u y i) x‖ ≤ |C| :=
        (PDE.norm_iteratedFDeriv_component_le hu i 0 x).trans ((hC x).trans (le_abs_self C))
      have h1 := PDE.norm_iteratedFDeriv_component_le hu j m x
      simp only [Nat.sub_zero, norm_mul, norm_norm, Real.norm_natCast, Real.norm_of_nonneg
        (abs_nonneg C)]
      calc (m.choose 0 : ℝ) * ‖iteratedFDeriv ℝ 0 (fun y ↦ u y i) x‖ *
            ‖iteratedFDeriv ℝ m (fun y ↦ u y j) x‖
          ≤ (m.choose 0 : ℝ) * |C| * ‖iteratedFDeriv ℝ m u x‖ := by gcongr
        _ = _ := by ring
    · obtain ⟨C, hC⟩ := hbd (m - l)
      refine ((hd2 l hl0).norm.const_mul ((m.choose l : ℝ) * |C|)).of_le hm'
        (Filter.Eventually.of_forall fun x ↦ ?_)
      have h0 : ‖iteratedFDeriv ℝ (m - l) (fun y ↦ u y j) x‖ ≤ |C| :=
        (PDE.norm_iteratedFDeriv_component_le hu j (m - l) x).trans ((hC x).trans (le_abs_self C))
      have h1 := PDE.norm_iteratedFDeriv_component_le hu i l x
      simp only [norm_mul, norm_norm, Real.norm_natCast, Real.norm_of_nonneg (abs_nonneg C)]
      calc (m.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fun y ↦ u y i) x‖ *
            ‖iteratedFDeriv ℝ (m - l) (fun y ↦ u y j) x‖
          ≤ (m.choose l : ℝ) * ‖iteratedFDeriv ℝ l u x‖ * |C| := by gcongr
        _ = _ := by ring
  refine (memLp_finsetSum _ hterm).of_le hmeas (Filter.Eventually.of_forall fun x ↦ ?_)
  refine (norm_iteratedFDeriv_mul_le (hui i) (hui j) x (by exact_mod_cast le_top)).trans ?_
  refine le_trans (le_of_eq ?_) (Real.le_norm_self _)
  rfl

/-- **Smoothness of the Riesz pressure.** For a smooth velocity field `u` on `ℝⁿ`, `n ≥ 1`, with
`u ∈ L⁴`, bounded derivatives of every order, and derivatives of positive order in `L²`, the
Riesz pressure `rieszPressure u` is smooth and all of its derivatives are square integrable. -/
theorem contDiff_rieszPressure [Fact (0 < n)] {u : ℝ^n → ℝ^n}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hu4 : MemLp u 4 volume)
    (hbd : ∀ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k u x‖ ≤ C)
    (hd2 : ∀ k, 1 ≤ k → MemLp (iteratedFDeriv ℝ k u) 2 volume) :
    ContDiff ℝ (⊤ : ℕ∞) (rieszPressure u) ∧
      ∀ k, MemLp (iteratedFDeriv ℝ k (rieszPressure u)) 2 volume := by
  have hbL2 {m : ℕ} (U : W^{m,2}(ℝ^n)) : (baseL2 U : ℝ^n → ℂ) =ᵐ[volume]
      fun x ↦ (baseRepresentative U x : ℂ) :=
    MemLp.coeFn_toLp (SobolevSpace.Fractional.memLp_coordFun U (baseIndex n m)).ofReal
  have hui (l : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ u x l) :=
    (EuclideanSpace.proj (𝕜 := ℝ) l).contDiff.comp hu
  -- the products in every `W^{m,2}`
  have hF (m : ℕ) (i j : Fin n) : ∃ U : W^{m,2}(ℝ^n), baseL2 U = velocityProductL2 u i j := by
    refine ⟨wkpOfContDiff (fun x ↦ u x i * u x j) ((hui i).mul (hui j))
      fun m' _ ↦ memLp_iteratedFDeriv_mul_component hu hu4 hbd hd2 i j m', Lp.ext ?_⟩
    filter_upwards [hbL2 (wkpOfContDiff (fun x ↦ u x i * u x j) ((hui i).mul (hui j))
        fun m' _ ↦ memLp_iteratedFDeriv_mul_component hu hu4 hbd hd2 i j m'),
      baseRepresentative_wkpOfContDiff (fun x ↦ u x i * u x j) ((hui i).mul (hui j))
        fun m' _ ↦ memLp_iteratedFDeriv_mul_component hu hu4 hbd hd2 i j m',
      coeFn_velocityProductL2 (memLp_two_mul_of_memLp_four hu4 i j)] with x h1 h2 h3
    rw [h1, h2, h3]
  have hV (m : ℕ) : ∃ V : W^{m,2}(ℝ^n), baseL2 V = rieszPressureL2 u := by
    choose F hF' using hF m
    exact exists_wkpSpace_rieszPressureL2 F hF'
  choose V hVQ using hV
  have hVP (m : ℕ) : rieszPressure u =ᵐ[volume] baseRepresentative (V m) := by
    filter_upwards [hbL2 (V m), rieszPressure_ae_eq u] with x h1 h2
    rw [h2, ← hVQ m, h1, Complex.ofReal_re]
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (rieszPressure u) :=
    contDiff_continuousRepresentative_of_forall_wkpSpace fun m ↦
      ⟨V m, (hVP m).symm.trans (rieszPressure_ae_eq u)⟩
  exact ⟨hsmooth, fun k ↦ memLp_iteratedFDeriv_of_ae_eq_baseRepresentative (V k) hsmooth
    (hVP k) le_rfl⟩

/-- The gradient of the Riesz pressure of a smooth velocity field with bounded derivatives,
`u ∈ L⁴` and derivatives of positive order in `L²`, is square integrable. -/
theorem memLp_fderiv_rieszPressure [Fact (0 < n)] {u : ℝ^n → ℝ^n}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hu4 : MemLp u 4 volume)
    (hbd : ∀ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k u x‖ ≤ C)
    (hd2 : ∀ k, 1 ≤ k → MemLp (iteratedFDeriv ℝ k u) 2 volume) :
    MemLp (fderiv ℝ (rieszPressure u)) 2 volume := by
  obtain ⟨hP, hD⟩ := contDiff_rieszPressure hu hu4 hbd hd2
  refine (hD 1).of_le ((hP.continuous_fderiv (by simp)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [norm_iteratedFDeriv_one]

end NavierStokes
