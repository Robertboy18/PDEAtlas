/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.AveragedFDeriv

/-!
# Cubic residuals when joining two solution strips

Two strips solve the same speed-dependent field `f - μ • id`. If their difference
has a smooth cubic factor in speed, a smooth time interpolation has a residual
with the same factor. The averaged derivative gives the exact nonlinear increment,
including at speed zero. On either constant part of the time cutoff the residual
vanishes, so a later state-space extension can have strict support collars.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace PDE.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Joining two solutions with a smooth time cutoff preserves a cubic factor
in their speed discrepancy. The returned factor is jointly smooth on the given
set and vanishes wherever the cutoff is constant zero or constant one to first
order. The differential identity uses the actual physical field with the same
minus-speed term on both strips; no residual estimate is an assumption. -/
theorem exists_contDiffOn_cubic_interpolation_residual
    {f : E → E} {u v a : ℝ × ℝ → E} {θ : ℝ → ℝ} {Ω : Set (ℝ × ℝ)}
    (hf : ContDiff ℝ ∞ f)
    (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (ha : ContDiffOn ℝ ∞ a Ω) (hθ : ContDiff ℝ ∞ θ)
    (hfactor : ∀ p ∈ Ω, v p - u p = p.2 ^ 3 • a p)
    (hodeU : ∀ p ∈ Ω, HasDerivAt (fun t ↦ u (t, p.2))
      (f (u p) - p.2 • u p) p.1)
    (hodeV : ∀ p ∈ Ω, HasDerivAt (fun t ↦ v (t, p.2))
      (f (v p) - p.2 • v p) p.1) :
    let w : ℝ × ℝ → E := fun p ↦ u p + θ p.1 • (v p - u p)
    ∃ R : ℝ × ℝ → E, ContDiffOn ℝ ∞ R Ω ∧
      (∀ p ∈ Ω, HasDerivAt (fun t ↦ w (t, p.2))
        (f (w p) - p.2 • w p + p.2 ^ 3 • R p) p.1) ∧
      ∀ p ∈ Ω, (θ p.1 = 0 ∨ θ p.1 = 1) → deriv θ p.1 = 0 → R p = 0 := by
  intro w
  let A : ℝ × ℝ → E →L[ℝ] E := fun p ↦ averagedFDeriv f (u p) (v p)
  let B : ℝ × ℝ → E →L[ℝ] E := fun p ↦ averagedFDeriv f (u p) (w p)
  let R : ℝ × ℝ → E := fun p ↦
    deriv θ p.1 • a p + θ p.1 • ((A p - B p) (a p))
  have hw : ContDiffOn ℝ ∞ w Ω :=
    hu.add ((hθ.comp contDiff_fst).contDiffOn.smul (hv.sub hu))
  have havg : ContDiff ℝ ∞ (fun z : E × E ↦ averagedFDeriv f z.1 z.2) :=
    contDiff_averagedFDeriv_joint (by simpa using hf)
  have hA : ContDiffOn ℝ ∞ A Ω := havg.comp_contDiffOn (hu.prodMk hv)
  have hB : ContDiffOn ℝ ∞ B Ω := havg.comp_contDiffOn (hu.prodMk hw)
  have hθ' : ContDiff ℝ ∞ (deriv θ) := (contDiff_infty_iff_deriv.mp hθ).2
  refine ⟨R, ((hθ'.comp contDiff_fst).contDiffOn.smul ha).add
    ((hθ.comp contDiff_fst).contDiffOn.smul ((hA.sub hB).clm_apply ha)), ?_, ?_⟩
  · intro p hp
    have hdiff : HasDerivAt (fun t ↦ w (t, p.2))
        (f (u p) - p.2 • u p + deriv θ p.1 • (v p - u p) +
          θ p.1 • ((f (v p) - p.2 • v p) - (f (u p) - p.2 • u p))) p.1 := by
      convert (hodeU p hp).add
        (((hθ.differentiable (by simp) p.1).hasDerivAt).smul
          ((hodeV p hp).sub (hodeU p hp))) using 1
      simp only [Pi.sub_apply]
      abel
    have hAv : A p (v p - u p) = f (v p) - f (u p) :=
      averagedFDeriv_apply_sub (hf.of_le (by simp)) _ _
    have hBw : θ p.1 • B p (v p - u p) = f (w p) - f (u p) := by
      have h := averagedFDeriv_apply_sub (hf.of_le (by simp)) (u p) (w p)
      simpa only [w, add_sub_cancel_left, map_smul] using h
    have hnonlinear : f (w p) + θ p.1 • (A p - B p) (v p - u p) =
        f (u p) + θ p.1 • (f (v p) - f (u p)) := by
      simp only [sub_apply, smul_sub, hAv]
      rw [hBw]
      abel
    apply hdiff.congr_deriv
    symm
    calc
      f (w p) - p.2 • w p + p.2 ^ 3 • R p =
          f (w p) - p.2 • w p + deriv θ p.1 • (v p - u p) +
            θ p.1 • (A p - B p) (v p - u p) := by
        dsimp only [R]
        rw [hfactor p hp]
        simp only [smul_add, map_smul]
        rw [smul_comm (p.2 ^ 3) (deriv θ p.1), smul_comm (p.2 ^ 3) (θ p.1)]
        abel
      _ = (f (w p) + θ p.1 • (A p - B p) (v p - u p)) -
          p.2 • w p + deriv θ p.1 • (v p - u p) := by abel
      _ = (f (u p) + θ p.1 • (f (v p) - f (u p))) -
          p.2 • w p + deriv θ p.1 • (v p - u p) := by rw [hnonlinear]
      _ = f (u p) - p.2 • u p + deriv θ p.1 • (v p - u p) +
          θ p.1 • ((f (v p) - p.2 • v p) - (f (u p) - p.2 • u p)) := by
        simp only [w, smul_add, smul_sub, smul_comm (p.2)]
        abel
  · intro p _ hcut hderiv
    rcases hcut with hzero | hone
    · simp only [R, hderiv, hzero, zero_smul, add_zero]
    · have hwv : w p = v p := by simp only [w, hone, one_smul, add_sub_cancel]
      simp only [R, hderiv, zero_smul, hone, one_smul, A, B, hwv, sub_self,
        zero_apply, zero_add]

end PDE.Analysis.ODE
