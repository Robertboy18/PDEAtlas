/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.FirstOrder
public import PDE.Analysis.MeasureTheory.Integral.LowerBounded

/-!
# Extended energies of finite Sobolev systems

The nonnegative shifted integral uses the Euclidean value and full
matrix gradient of the finite Sobolev product. It retains infinite
values and imposes no separability of the density across components.
The signed energy uses the positive and negative parts of the original
density, and agrees with the real integral whenever that density is integrable.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

namespace PDE.CalculusOfVariations

/-- The extended integral of a coupled density after adding a spatial lower
bound. If the added function is integrable, this is a finite constant shift
of the original lower-bounded energy. -/
def vectorWkpLIntegral {m n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ) (b : ℝ^n → ℝ)
    (u : Fin m → W^{1,p}(Ω)) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (F x (vectorWkpValueCLM u x, ∇ u x) + b x)
    ∂domainMeasure n Ω

/-- The signed extended energy of the original coupled density, defined by
its positive and negative parts on the Sobolev value and gradient. -/
def vectorWkpIntegral {m n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ)
    (u : Fin m → W^{1,p}(Ω)) : EReal :=
  PDE.Analysis.lowerBoundedIntegral (domainMeasure n Ω)
    (fun x ↦ F x (vectorWkpValueCLM u x, ∇ u x))

/-- The signed Sobolev energy equals the ordinary real integral whenever
the original density evaluated on the Sobolev field is integrable. -/
theorem vectorWkpIntegral_eq_integral
    {m n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ} {u : Fin m → W^{1,p}(Ω)}
    (hF : Integrable
      (fun x ↦ F x (vectorWkpValueCLM u x, ∇ u x))
      (domainMeasure n Ω)) :
    vectorWkpIntegral F u =
      ((∫ x, F x (vectorWkpValueCLM u x, ∇ u x)
        ∂domainMeasure n Ω : ℝ) : EReal) :=
  PDE.Analysis.lowerBoundedIntegral_eq_integral hF

end PDE.CalculusOfVariations
