/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.Hypersurface.Analytic
public import PDE.Analysis.Calculus.Jet.CoordinateChange
public import PDE.Analysis.Calculus.MultiIndex.CoordinateJet.Operations

/-!
# Analytic normal Cauchy data

Multiplication by powers of a defining function gives a triangular interpolation
of ordinary normal derivatives. The diagonal coefficient at order `j` is
`j! * ‖∇φ‖^j`, including order zero.
-/

@[expose] public noncomputable section

open scoped Gradient

open Filter Set
open scoped Topology ContDiff

namespace PDE.Analysis.Cauchy

open MultiIndex Hypersurface

variable {n : ℕ}

/-- Normal derivatives of an analytic function form analytic value
data when the prescribed normal field is analytic. -/
theorem analyticAt_normalData {u : ℝ^n → ℝ} {ν : ℝ^n → ℝ^n} {x : ℝ^n}
    (hu : AnalyticAt ℝ u x) (hν : AnalyticAt ℝ ν x) (j : ℕ) :
    AnalyticAt ℝ (fun y ↦ normalData j u (ν y) y) x := by
  have hU : AnalyticOnNhd ℝ u {x} := by
    intro y hy
    have h : y = x := mem_singleton_iff.mp hy
    subst y
    exact hu
  have hD := hU.iteratedFDeriv j x (mem_singleton x)
  exact (ContinuousLinearMap.id ℝ
    ((ℝ^n) [×j]→L[ℝ] ℝ)).analyticAt_uncurry_of_multilinear.comp
      (hD.prod (AnalyticAt.pi fun _ ↦ hν))

/-- At a zero of the defining function, the leading normal derivative of
an amplitude times a power is its value times the diagonal factor `j! ‖∇φ‖^j`. -/
theorem normalData_mul_pow {a φ : ℝ^n → ℝ} {x : ℝ^n}
    (ha : AnalyticAt ℝ a x) (hφ : AnalyticAt ℝ φ x)
    (hx : φ x = 0) (j : ℕ) :
    normalData j (fun y ↦ a y * φ y ^ j) (levelNormal φ x) x =
      a x * (j.factorial : ℝ) * ‖∇ φ x‖ ^ j := by
  classical
  unfold normalData
  simp only [Jet.iteratedFDeriv_mul_pow_of_eq_zero ha hφ hx le_rfl, ↓reduceIte]
  by_cases hreg : fderiv ℝ φ x = 0
  · have hg : ∇ φ x = 0 := by simp [gradient, hreg]
    simp [hreg, hg]
  simp only [fderiv_eq_norm_mul_inner_levelNormal hreg, real_inner_self_eq_norm_sq,
    norm_levelNormal hreg, one_pow, mul_one, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- Arbitrary finite analytic value data have one analytic scalar extension
with precisely the prescribed ordinary normal derivatives on the level.
Compatibility between the different data is constructed, not assumed. -/
theorem exists_analytic_normalData {φ : ℝ^n → ℝ} {p : ℝ^n}
    (hφ : AnalyticAt ℝ φ p) (hreg : fderiv ℝ φ p ≠ 0)
    (k : ℕ) (g : Fin k → ℝ^n → ℝ) (hg : ∀ i, AnalyticAt ℝ (g i) p) :
    ∃ G : ℝ^n → ℝ, AnalyticAt ℝ G p ∧
      ∀ᶠ x in 𝓝 p, φ x = 0 →
        ∀ i : Fin k, normalData (i : ℕ) G (levelNormal φ x) x = g i x := by
  induction k with
  | zero =>
    exact ⟨fun _ ↦ 0, analyticAt_const,
      Filter.Eventually.of_forall fun _ _ i ↦ Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨G, hG, hdata⟩ := ih (fun i ↦ g i.castSucc) (fun i ↦ hg i.castSucc)
    -- A multiple of `φ^k` corrects order `k` and leaves all lower jets unchanged.
    let a := fun y ↦ (g (Fin.last k) y - normalData k G (levelNormal φ y) y) /
      ((k.factorial : ℝ) * ‖∇ φ y‖ ^ k)
    have hgrad : AnalyticAt ℝ (∇ φ) p :=
      ((InnerProductSpace.toDual ℝ (ℝ^n)).symm.toContinuousLinearEquiv.analyticAt _).comp
        hφ.fderiv
    have hnorm : AnalyticAt ℝ (fun y ↦ ‖∇ φ y‖) p :=
      ((hgrad.contDiffAt : ContDiffAt ℝ ω (∇ φ) p).norm ℝ
        (gradient_ne_zero hreg)).analyticAt
    have ha : AnalyticAt ℝ a p :=
      ((hg (Fin.last k)).sub
        (analyticAt_normalData hG (analyticAt_levelNormal hφ hreg) k)).div
          (analyticAt_const.mul (hnorm.pow k))
          (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))
            (pow_ne_zero _ (norm_ne_zero_iff.mpr (gradient_ne_zero hreg))))
    let C := fun y ↦ a y * φ y ^ k
    have hC : AnalyticAt ℝ C p := ha.mul (hφ.pow k)
    refine ⟨G + C, hG.add hC, ?_⟩
    have hr : ∀ᶠ x in 𝓝 p, fderiv ℝ φ x ≠ 0 :=
      hφ.fderiv.continuousAt.eventually_ne hreg
    filter_upwards [hdata, hφ.eventually_analyticAt, hG.eventually_analyticAt,
      ha.eventually_analyticAt, hr] with x hdatax hφx hGx hax hrx
    intro hx i
    have hCx : AnalyticAt ℝ C x := hax.mul (hφx.pow k)
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · change normalData k (G + C) (levelNormal φ x) x = g (Fin.last k) x
      rw [normalData_add hGx.contDiffAt hCx.contDiffAt,
        normalData_mul_pow hax hφx hx]
      dsimp [a]
      rw [mul_assoc, div_mul_cancel₀ _ (mul_ne_zero
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))
        (pow_ne_zero _ (norm_ne_zero_iff.mpr (gradient_ne_zero hrx))))]
      ring
    · have hnormal : normalData (j : ℕ) C (levelNormal φ x) x = 0 := by
        simp [normalData, C,
          Jet.iteratedFDeriv_mul_pow_of_eq_zero hax hφx hx j.isLt.le, j.isLt.ne]
      change normalData (j : ℕ) (G + C) (levelNormal φ x) x = g j.castSucc x
      rw [normalData_add hGx.contDiffAt hCx.contDiffAt, hnormal, add_zero]
      exact hdatax hx j

end PDE.Analysis.Cauchy
