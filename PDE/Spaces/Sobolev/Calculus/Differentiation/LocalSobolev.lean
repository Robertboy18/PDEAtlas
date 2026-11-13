/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData
public import PDE.Spaces.Sobolev.GraphSpace.Local.Definitions

/-!
# Local Sobolev regularity of classical functions

On a relatively compact subdomain, continuity of the classical derivatives gives
uniform continuity and boundedness. The classical-to-weak construction therefore
gives local Sobolev membership at every exponent, including infinity.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace

variable {n k : ℕ} {Ω V : Set (ℝ^n)} {f : ℝ^n → ℝ}

/-- Interior classical regularity gives regularity up to the boundary of every
relatively compact subdomain. No regularity of that subdomain's boundary is needed. -/
theorem contDiffUpToBoundary_of_contDiffOn
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ k f Ω)
    (hcompact : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) :
    ContDiffUpToBoundary k f V := by
  refine ⟨hf.mono (subset_closure.trans hVΩ), fun α hα ↦ ?_⟩
  apply (hcompact.uniformContinuousOn_of_continuous ?_).mono subset_closure
  intro x hx
  exact (contDiffAt_iteratedPartialDeriv_of_le
    (hf.contDiffAt (hΩ.mem_nhds (hVΩ hx))) α hα).continuousAt.continuousWithinAt

/-- A locally classical `C^k` function belongs to `W^{k,p}` locally for every `p`. -/
theorem isLocallyWkpOn_of_contDiffOn
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ k f Ω) (p : ℝ≥0∞) :
    GraphSpace.IsLocallyWkpOn k p Ω f := by
  intro V hV hcompact hVΩ
  have h := contDiffUpToBoundary_of_contDiffOn hΩ hf hcompact hVΩ
  refine ⟨h.toWkpSpaceOn hV (hcompact.isBounded.subset subset_closure) p, ?_⟩
  simpa only [GraphSpace.baseRepresentative, GraphSpace.baseIndex_toList,
    iteratedPartialDeriv] using
    h.toWkpSpaceOn_apply_ae hV (hcompact.isBounded.subset subset_closure) p
      (GraphSpace.baseIndex n k)

end SobolevSpace
