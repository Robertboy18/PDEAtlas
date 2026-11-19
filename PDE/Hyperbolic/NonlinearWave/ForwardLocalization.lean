/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.ForwardLocalization
public import PDE.Hyperbolic.NonlinearWave.EnergyIdentity

/-!
# Localization of semilinear waves

A field is often replaced by another one with the same germ at the points of interest: an ambient
extension of a field given on the closed forward half-space `{t ≥ 0}`, a global representative of
a local solution, a radial model on an annulus. The lemmas here say what such a replacement keeps,
for every pair of fields:

* `waveOperator_add_congr_nhds`: the expression `□u + f(u)` at a point depends only on the germ
  of `u` at that point, for every reaction `f`.
* `semilinearWaveOperator_congr_nhds`: the same for the semilinear wave operator `□u + V'(u)`,
  for every potential `V`. It is the case `f = V'`.
* `slice_eq_of_eqOn_forward`: two fields that agree on a closed forward half-space `{t ≥ a}`
  have the same time slices at the times `t ≥ a`, so support and integrability hypotheses on
  slices transfer.

With `eventuallyEq_of_eqOn_forward` the first two transfer an equation at every time after `a`.
The statements are elementary and follow no source. Their linear counterpart is
`waveOperator_congr_nhds`.
-/

@[expose] public section

namespace WaveEquation

open Filter PDE.Common Set
open scoped Topology

variable {n : ℕ}

/-- The expression `□u + f(u)` at a point depends only on the germ of the field `u` at that
point, for every reaction `f`. -/
theorem waveOperator_add_congr_nhds (f : ℝ → ℝ) {u v : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)}
    (h : u =ᶠ[𝓝 p] v) : waveOperator u p + f (u p) = waveOperator v p + f (v p) := by
  rw [waveOperator_congr_nhds h, h.eq_of_nhds]

/-- The semilinear wave operator `□u + V'(u)` at a point depends only on the germ of the field
`u` at that point, for every potential `V`. -/
theorem semilinearWaveOperator_congr_nhds (V : ℝ → ℝ) {u v : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)}
    (h : u =ᶠ[𝓝 p] v) : semilinearWaveOperator V u p = semilinearWaveOperator V v p :=
  waveOperator_add_congr_nhds (deriv V) h

/-- Two fields that agree on the closed forward half-space `{t ≥ a}` have the same time slices at
every time `t ≥ a`. -/
theorem slice_eq_of_eqOn_forward {u v : ℝ^(n + 1) → ℝ} {a : ℝ} (h : EqOn u v {p | a ≤ p 0})
    {t : ℝ} (ht : a ≤ t) : (fun x : ℝ^n ↦ u (timeSpaceCons t x)) = fun x ↦ v (timeSpaceCons t x) :=
  funext fun x ↦ h (by simpa only [mem_ofPred_eq, timeSpaceCons_zero] using ht)

end WaveEquation
