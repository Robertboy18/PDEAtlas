/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Local.Definitions
public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction

/-!
# Local Sobolev membership and the order

A function of `W^{m,p}_loc(Ω)` lies in `W^{k,p}_loc(Ω)` for every `k ≤ m`. On each relatively
compact open subset of `Ω` it is represented by an element of `W^{m,p}`, and forgetting the
derivatives of order above `k` (`lowerOrderCLM`) gives an element of `W^{k,p}` with the same
function (`baseRepresentative_lowerOrderCLM`).

## Main results

* `IsLocallyWkpOn.of_le`: local membership passes to lower orders, for every exponent `p ≥ 1`
  and every set `Ω`.
-/

@[expose] public section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n k m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)} {u : ℝ^n → ℝ}

/-- Local Sobolev membership passes to lower orders: a function of `W^{m,p}_loc(Ω)` lies in
`W^{k,p}_loc(Ω)` for every `k ≤ m`. On each subdomain the lower-order graph retains the rows
through order `k`. -/
theorem IsLocallyWkpOn.of_le (hu : IsLocallyWkpOn m p Ω u) (hkm : k ≤ m) :
    IsLocallyWkpOn k p Ω u := fun V hV hc hVΩ ↦ by
  obtain ⟨U, hU⟩ := hu V hV hc hVΩ
  exact ⟨lowerOrderCLM hkm U, by rwa [baseRepresentative_lowerOrderCLM]⟩

end SobolevSpace.GraphSpace
