/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.CompactByParts
public import PDE.FDeriv.Operators
import PDE.FDeriv.PartialDeriv.Support

/-!
# Transferring two derivatives onto a compact test

Second coordinate derivatives can be transferred onto a compactly supported
test with no boundary term. The differentiated field needs regularity only
near the support of that test. This allows distributional identities to be
deduced from equations holding solely in an open physical domain.
-/

@[expose] public section

namespace PDE.Analysis

open EuclideanSpace MeasureTheory

set_option linter.missingDocs true

/-- Transfer two coordinate derivatives onto a compact `C²` scalar test.
The other factor is only required to be `C²` near the support of the test. -/
theorem integral_mul_secondPartialDeriv_eq_of_contDiffAt {n : ℕ}
    {φ f : ℝ^n → ℝ} (i j : Fin n) (hφ : ContDiff ℝ 2 φ)
    (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x) (hc : HasCompactSupport φ) :
    (∫ x, φ x * (∂[i] (∂[j] f)) x) =
      ∫ x, (∂[j] (∂[i] φ)) x * f x := by
  rw [integral_mul_partialDeriv_eq_neg_of_contDiffAt i (hφ.of_le (by norm_num))
    (fun x hx ↦ (hf x hx).partialDeriv j (k := 1) (by norm_num)) hc]
  rw [integral_mul_partialDeriv_eq_neg_of_contDiffAt j
    (hφ.partialDeriv i (k := 1) (by norm_num))
    (fun x hx ↦ (hf x ((tsupport_partialDeriv_subset (f := φ) i) hx)).of_le (by norm_num))
    (hc.partialDeriv i), neg_neg]

end PDE.Analysis
