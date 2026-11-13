/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Noether.FieldSpace
public import PDE.CalculusOfVariations.Noether.InducedField
public import PDE.CalculusOfVariations.Noether.Locality

/-!
# Noether conservation from local field and space transformations

The inputs are the original field `u`, a spatial transformation `Φ`, and a field
transformation `Ψ`. The induced field is constructed by the inverse function theorem;
its graph law and joint `C²` regularity are proved. The localized field-space theorem
then turns finite invariance of the transformed density into conservation of the
current with generators `η = ∂ₜΨ(t,y,u(y))|₀` and `X = ∂ₜΦ(t,y)|₀`.

All regularity assumptions are local at the relevant points. The transformations fix
the original graph near `x` at parameter zero. No global inverse, global extension,
infinitesimal invariance identity, or current-divergence relation is assumed.

Compare Noether's theorem, Evans, §8.6.2, Theorem 1, where the variations are a domain variation
with generator (2) and a function variation (4) with multiplier (5); here both come from `Φ`
and `Ψ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.6.1, (2)-(5), p. 512, and §8.6.2, Theorem 1
  (Noether's Theorem), p. 513.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Elementwise Topology

namespace PDE.CalculusOfVariations.Noether

open Analysis

variable {n m : ℕ} {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ}
  {u : ℝ^n → ℝ^m} {Φ : ℝ → ℝ^n → ℝ^n}
  {Ψ : ℝ → ℝ^n → ℝ^m → ℝ^m} {x : ℝ^n}

/-- Local Noether conservation from raw jointly `C²` field and space maps.
The family in the invariance hypothesis is the field constructed by local inversion,
not an additional input. Invariance is equality of densities with the
spatial Jacobian determinant. The resulting current is expressed entirely in the
original field and the parameter derivatives of `Φ` and `Ψ`. -/
theorem noether_of_field_space_maps
    (hL : ContDiffAt ℝ 2
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix u x, (u x, x)))
    (hu : ContDiffAt ℝ 2 u x)
    (hΦ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ Φ p.1 p.2) (0, x))
    (hΦ₀ : Φ 0 =ᶠ[𝓝 x] id)
    (hΨ : ContDiffAt ℝ 2
      (fun p : ℝ × (ℝ^n × ℝ^m) ↦ Ψ p.1 p.2.1 p.2.2) (0, (x, u x)))
    (hΨ₀ : (fun y ↦ Ψ 0 y (u y)) =ᶠ[𝓝 x] u)
    (hinvariant : (fun t ↦
      L (jacobianMatrix (inducedField u Ψ hΦ hΦ₀ t) (Φ t x)) (Ψ t x (u x)) (Φ t x) *
        (jacobianMatrix (Φ t) x).det) =ᶠ[𝓝 0] (fun _ ↦ fieldDensity L u x))
    (hEL : ∀ k, classicalEulerLagrange L u x k = 0) :
    ∇· (noetherCurrent L u
      (fun y ↦ deriv (fun t ↦ Ψ t y (u y)) 0 -
        fderiv ℝ u y (deriv (fun t ↦ Φ t y) 0))
      (fun y ↦ deriv (fun t ↦ Φ t y) 0)) x = 0 := by
  let U := inducedField u Ψ hΦ hΦ₀
  have hU : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (0, x) :=
    contDiffAt_inducedField hu hΦ hΦ₀ hΨ
  have hU₀ : U 0 =ᶠ[𝓝 x] u := inducedField_zero hΦ hΦ₀ hΨ₀
  have hL' : ContDiffAt ℝ 2
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix (U 0) x, (U 0 x, x)) := by
    rw [jacobianMatrix_eq_of_eventuallyEq hU₀, hU₀.eq_of_nhds]
    exact hL
  have hgraphΨ : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ^n ↦ Ψ p.1 p.2 (u p.2)) (0, x) :=
    hΨ.comp (0, x)
      (contDiffAt_fst.prodMk (contDiffAt_snd.prodMk (hu.comp (0, x) contDiffAt_snd)))
  have hΨ' : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun t ↦ Ψ t y (U 0 y)) 0 := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually
      (hgraphΨ.eventually (by norm_num)), hU₀] with y hy hbase
    rw [hbase]
    exact (hy.comp 0 (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt
      (by norm_num)
  have hgraph' : ∀ᶠ y in 𝓝 x,
      (fun t ↦ U t (Φ t y)) =ᶠ[𝓝 0] (fun t ↦ Ψ t y (U 0 y)) := by
    have h := inducedField_graph (u := u) (Ψ := Ψ) hΦ hΦ₀
    rw [nhds_prod_eq] at h
    filter_upwards [(Filter.eventually_swap_iff.mp h).curry, hU₀] with y hy hbase
    change (fun t ↦ U t (Φ t y)) =ᶠ[𝓝 0] (fun t ↦ Ψ t y (u y)) at hy
    simpa only [hbase] using hy
  have hinvariant' : (fun t ↦
      L (jacobianMatrix (U t) (Φ t x)) (Ψ t x (U 0 x)) (Φ t x) *
        (jacobianMatrix (Φ t) x).det) =ᶠ[𝓝 0] (fun _ ↦ fieldDensity L (U 0) x) := by
    simpa only [hU₀.eq_of_nhds, fieldDensity_eq_of_eventuallyEq hU₀] using hinvariant
  have hEL' (k : Fin m) : classicalEulerLagrange L (U 0) x k = 0 :=
    (classicalEulerLagrange_eq_of_eventuallyEq hU₀ k).trans (hEL k)
  have hcurrent : noetherCurrent L (U 0)
      (fun y ↦ deriv (fun t ↦ Ψ t y (U 0 y)) 0 -
        fderiv ℝ (U 0) y (deriv (fun t ↦ Φ t y) 0))
      (fun y ↦ deriv (fun t ↦ Φ t y) 0) =ᶠ[𝓝 x]
      noetherCurrent L u
        (fun y ↦ deriv (fun t ↦ Ψ t y (u y)) 0 -
          fderiv ℝ u y (deriv (fun t ↦ Φ t y) 0))
        (fun y ↦ deriv (fun t ↦ Φ t y) 0) := by
    filter_upwards [hU₀.eventuallyEq_nhds] with y hy
    rw [noetherCurrent_eq_of_eventuallyEq hy]
    unfold noetherCurrent
    simp only [hy.eq_of_nhds, hy.fderiv_eq]
  rw [← hcurrent.divergence_eq]
  exact noether_field_space hL' hU hΦ hΦ₀ hΨ' hgraph' hinvariant' hEL'

end PDE.CalculusOfVariations.Noether
