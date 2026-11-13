/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Composition
public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.Smooth

/-!
# Scalar wave composition and finite Sobolev composition

The scalar higher reaction is the one-coordinate specialization of the finite
Sobolev composition operator. Almost-everywhere identification transports
operator regularity without changing the reaction lift used by the wave theory.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ}

/-- The one-coordinate finite composition agrees with the scalar wave lift. -/
theorem finiteComposition_unit_eq_higherComposition (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hk' : (n : ℝ) < 2 * (k : ℝ)) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (u : W^{k,2}(ℝ^n)) :
    Composition.finiteComposition (ι := Unit) hk' (hf.comp (contDiff_apply ℝ (fun _ ↦ ℝ) ())) hf0
      (fun _ ↦ u) = higherComposition hk hf hf0 u := by
  apply WkpSpaceOn.ext_of_base_ae isOpen_univ
  change baseRepresentative _ =ᵐ[domainMeasure n univ] baseRepresentative _
  simp only [domainMeasure, Measure.restrict_univ]
  exact (Composition.finiteComposition_ae hk'
    (hf.comp (contDiff_apply ℝ (fun _ ↦ ℝ) ())) hf0 (fun _ : Unit ↦ u)).trans
      (higherComposition_ae hk hf hf0 u).symm

/-- Smoothness of finite composition passes to the scalar higher wave reaction. -/
theorem contDiff_higherComposition (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf0 : f 0 = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (higherComposition hk hf hf0) := by
  have hk' : (n : ℝ) < 2 * (k : ℝ) := by linarith
  have hfinite := Composition.contDiff_finiteComposition (ι := Unit) hk'
    (hf.comp (contDiff_apply ℝ (fun _ ↦ ℝ) ())) hf0
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun u : W^{k,2}(ℝ^n) ↦ fun _ : Unit ↦ u) :=
    contDiff_pi.mpr (fun _ ↦ contDiff_id)
  have heq : higherComposition hk hf hf0 = fun u ↦ Composition.finiteComposition (ι := Unit) hk'
        (hf.comp (contDiff_apply ℝ (fun _ ↦ ℝ) ())) hf0 (fun _ ↦ u) := by
    funext u
    exact (finiteComposition_unit_eq_higherComposition hk hk' hf hf0 u).symm
  rw [heq]
  exact hfinite.comp hd

end PDE.Hyperbolic.NonlinearWave.Cauchy
