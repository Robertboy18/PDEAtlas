/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.InverseFunction.Parameter
public import PDE.Analysis.Calculus.Jacobian.Calculus

/-!
# The field induced by a local transformation of its graph

For a jointly `C²` spatial family `Φ` with `Φ(0,·)` locally the identity, the inverse
function theorem supplies a jointly `C²` inverse `χ(t,·)` near `(0,x)`. The transformed
field is `U(t,z) = Ψ(t,χ(t,z),u(χ(t,z)))`. Its graph law and local regularity follow from
the inverse theorem and composition. No transformed field or graph law is supplied
by the caller, and no global smooth extension is required.

To recover `u` at parameter zero, only `Ψ(0,y,u(y)) = u(y)` near `x` is needed.
The field transformation may be nonlinear and position dependent.
-/

@[expose] public noncomputable section

open scoped Topology

namespace PDE.CalculusOfVariations.Noether

open Analysis

variable {n m : ℕ} {u : ℝ^n → ℝ^m} {Φ : ℝ → ℝ^n → ℝ^n}
  {Ψ : ℝ → ℝ^n → ℝ^m → ℝ^m} {x : ℝ^n}

/-- The field obtained by applying `Ψ` to the original graph and expressing it in
the coordinates transformed by `Φ`. Only its germ near `(0,x)` is used. -/
def inducedField (u : ℝ^n → ℝ^m) (Ψ : ℝ → ℝ^n → ℝ^m → ℝ^m)
    (hΦ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ Φ p.1 p.2) (0, x))
    (hΦ₀ : Φ 0 =ᶠ[𝓝 x] id) (t : ℝ) (z : ℝ^n) : ℝ^m :=
  let y := localSpatialInverse hΦ hΦ₀ t z
  Ψ t y (u y)

/-- The induced field satisfies the graph transformation law jointly near `(0,x)`. -/
theorem inducedField_graph
    (hΦ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ Φ p.1 p.2) (0, x))
    (hΦ₀ : Φ 0 =ᶠ[𝓝 x] id) :
    ∀ᶠ p : ℝ × ℝ^n in 𝓝 (0, x),
      inducedField u Ψ hΦ hΦ₀ p.1 (Φ p.1 p.2) = Ψ p.1 p.2 (u p.2) := by
  filter_upwards [localSpatialInverse_left_inverse hΦ hΦ₀] with p hp
  simp only [inducedField, hp]

/-- Composing the local inverse with the original graph and field transformation
preserves joint `C²` regularity. All three hypotheses are regularity at single points. -/
theorem contDiffAt_inducedField
    (hu : ContDiffAt ℝ 2 u x)
    (hΦ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ Φ p.1 p.2) (0, x))
    (hΦ₀ : Φ 0 =ᶠ[𝓝 x] id)
    (hΨ : ContDiffAt ℝ 2
      (fun p : ℝ × (ℝ^n × ℝ^m) ↦ Ψ p.1 p.2.1 p.2.2) (0, (x, u x))) :
    ContDiffAt ℝ 2
      (fun p : ℝ × ℝ^n ↦ inducedField u Ψ hΦ hΦ₀ p.1 p.2) (0, x) := by
  have hχ := contDiffAt_localSpatialInverse hΦ hΦ₀
  have huχ : ContDiffAt ℝ 2 u (localSpatialInverse hΦ hΦ₀ 0 x) := by
    simpa only [localSpatialInverse_zero_apply] using hu
  have hΨχ : ContDiffAt ℝ 2
      (fun p : ℝ × (ℝ^n × ℝ^m) ↦ Ψ p.1 p.2.1 p.2.2)
      (0, (localSpatialInverse hΦ hΦ₀ 0 x, u (localSpatialInverse hΦ hΦ₀ 0 x))) := by
    simpa only [localSpatialInverse_zero_apply] using hΨ
  exact hΨχ.comp (0, x) (contDiffAt_fst.prodMk (hχ.prodMk (huχ.comp (0, x) hχ)))

/-- If the field transformation fixes the original graph at parameter zero, the
induced field at zero agrees with the original field on a neighborhood of `x`. -/
theorem inducedField_zero
    (hΦ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ Φ p.1 p.2) (0, x))
    (hΦ₀ : Φ 0 =ᶠ[𝓝 x] id)
    (hΨ₀ : (fun y ↦ Ψ 0 y (u y)) =ᶠ[𝓝 x] u) :
    inducedField u Ψ hΦ hΦ₀ 0 =ᶠ[𝓝 x] u := by
  filter_upwards [localSpatialInverse_zero hΦ hΦ₀, hΨ₀] with y hy hbase
  simpa only [inducedField, hy, id_eq] using hbase

end PDE.CalculusOfVariations.Noether
