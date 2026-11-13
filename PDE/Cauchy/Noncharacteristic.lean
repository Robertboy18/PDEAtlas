/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Cauchy.Noncharacteristic.Local
public import PDE.Analysis.Calculus.Cauchy.NormalData.LowerJet

/-!
# Cauchy-jet determination for quasilinear equations

A smooth solution of a scalar equation of order `k` has all its jets
determined on a noncharacteristic hypersurface by its lower normal Cauchy data.
The equation and the data use ordinary coordinate partials. Coefficients may
depend smoothly on position and every derivative below order `k`, only where
the position belongs to the given open neighborhood.

The normal may be any nonzero conormal vector field, so the unit normal is a
special case. Only local parametrizations of the hypersurface are used, and the
solutions need only be smooth on the given open neighborhood.

`iteratedFDeriv_eq_on_of_cauchy_data` is Evans, §4.6.1, Theorem 1 (Cauchy data and
noncharacteristic surfaces), stated as uniqueness: two smooth solutions with the same Cauchy
data have the same derivatives of every order on the hypersurface. Its symbol hypothesis is
the noncharacteristic condition (8) for all values of the lower-order arguments, with a nonzero
conormal field in place of the unit normal as in the Remark (13).
`iteratedFDeriv_eq_on_of_cauchy_data_of_symbol_at_jet` needs the condition only at the lower
jet of one solution. Our proof uses conormal tensors. `normalData` is the ordinary derivative
along the fixed normal line; coordinate expansions include multinomial weights.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.1, Theorem 1, (8) and (13).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology ContDiff
open PDE.Analysis PDE.Analysis.MultiIndex

namespace PDE.Cauchy.Quasilinear

/-- The lower normal Cauchy data determine every ordinary derivative of a
smooth solution on a noncharacteristic hypersurface.

The principal symbol is evaluated only at the solution’s lower jet on the
hypersurface. The common normal data determine this jet. Empty hypersurfaces
are allowed; in dimension zero the nonzero-normal premise forces this case. -/
theorem iteratedFDeriv_eq_on_of_cauchy_data_of_symbol_at_jet
    {n k : ℕ} (hk : 0 < k)
    (a : Sym (Fin n) k → ℝ^n × (∀ i : Fin k, Sym (Fin n) (i : ℕ) → ℝ) → ℝ)
    (b : ℝ^n × (∀ i : Fin k, Sym (Fin n) (i : ℕ) → ℝ) → ℝ)
    {Γ Ω : Set (ℝ^n)} (hΩ : IsOpen Ω) (hΓΩ : Γ ⊆ Ω)
    (ha : ∀ α, ContDiffOn ℝ ∞ (a α) (Ω ×ˢ univ))
    (hb : ContDiffOn ℝ ∞ b (Ω ×ˢ univ))
    (ν : ℝ^n → ℝ^n) (hν : ∀ x ∈ Γ, ν x ≠ 0)
    (hΓ : HasConormalParametrizations (ℝ^(n - 1)) Γ
      (fun x ↦ (innerSL ℝ (ν x)).toLinearMap))
    {u v : ℝ^n → ℝ}
    (hsymbol : ∀ x ∈ Γ,
      ∑ α, a α (x, coordinateJetLT k u x) * monomial α (ν x) ≠ 0)
    (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (hdata : ∀ j < k, ∀ x ∈ Γ, normalData j u (ν x) x = normalData j v (ν x) x)
    (hPu : ∀ x ∈ Ω,
      ∑ α, a α (x, coordinateJetLT k u x) * coordinateDeriv α u x =
        b (x, coordinateJetLT k u x))
    (hPv : ∀ x ∈ Ω,
      ∑ α, a α (x, coordinateJetLT k v x) * coordinateDeriv α v x =
        b (x, coordinateJetLT k v x)) :
    ∀ j, EqOn (iteratedFDeriv ℝ j u) (iteratedFDeriv ℝ j v) Γ := by
  classical
  let C : ℝ^n × (∀ i : Fin k, (ℝ^n) [×(i : ℕ)]→L[ℝ] ℝ) →
      ℝ^n × (∀ i : Fin k, Sym (Fin n) (i : ℕ) → ℝ) :=
    fun z ↦ (z.1, coordinateJetMap n k z.2)
  have hC : ContDiff ℝ ∞ C :=
    contDiff_fst.prodMk ((coordinateJetMap n k).contDiff.comp contDiff_snd)
  let e : ℝ^n → ℝ^n := fun x ↦ (‖ν x‖ ^ 2)⁻¹ • ν x
  have he (x : ℝ^n) (hx : x ∈ Γ) :
      (innerSL ℝ (ν x)).toLinearMap (e x) = 1 := by
    change inner ℝ (ν x) ((‖ν x‖ ^ 2)⁻¹ • ν x) = 1
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    exact inv_mul_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr (hν x hx)))
  apply PDE.Analysis.Cauchy.iteratedFDeriv_eq_on_of_normal_data_contDiffOn
    (fun _ ↦ directions) (fun α ↦ a α ∘ C) (b ∘ C)
    hΩ hΓΩ
    (fun α x hx p ↦
      ((ha α).contDiffAt ((hΩ.prod isOpen_univ).mem_nhds
        ⟨hΓΩ hx, mem_univ _⟩)).comp (x, p) hC.contDiffAt)
    (fun x hx p ↦
      (hb.contDiffAt ((hΩ.prod isOpen_univ).mem_nhds
        ⟨hΓΩ hx, mem_univ _⟩)).comp (x, p) hC.contDiffAt)
    hΓ e he ?_ hu hv ?_ ?_ ?_ ?_ ?_
  · intro j _ _ x hx
    obtain ⟨α, hα⟩ := exists_monomial_ne_zero (hν x hx) j
    exact ⟨α, by simpa only [monomial_eq_prod_inner,
      ContinuousLinearMap.coe_coe, innerSL_apply_apply] using hα⟩
  · intro x hx
    simpa only [normalData_zero] using hdata 0 hk x hx
  · intro j _ hj x hx
    rw [PDE.Analysis.Cauchy.iteratedFDeriv_eq_on_lt_of_normal_data
      hΩ hΓΩ ν hν hΓ hu hv hdata j hj hx]
  · intro x hx
    filter_upwards [hΩ.mem_nhds (hΓΩ hx)] with y hy
    exact hPu y hy
  · intro x hx
    filter_upwards [hΩ.mem_nhds (hΓΩ hx)] with y hy
    exact hPv y hy
  · intro x hx
    simpa only [Function.comp_def, C, coordinateJetLT, monomial_eq_prod_inner,
      ContinuousLinearMap.coe_coe, innerSL_apply_apply] using
      hsymbol x hx


/-- If the principal symbol is nonzero at every lower jet, common lower normal
Cauchy data determine all derivatives of smooth solutions on the hypersurface. -/
theorem iteratedFDeriv_eq_on_of_cauchy_data
    {n k : ℕ} (hk : 0 < k)
    (a : Sym (Fin n) k → ℝ^n × (∀ i : Fin k, Sym (Fin n) (i : ℕ) → ℝ) → ℝ)
    (b : ℝ^n × (∀ i : Fin k, Sym (Fin n) (i : ℕ) → ℝ) → ℝ)
    {Γ Ω : Set (ℝ^n)} (hΩ : IsOpen Ω) (hΓΩ : Γ ⊆ Ω)
    (ha : ∀ α, ContDiffOn ℝ ∞ (a α) (Ω ×ˢ univ))
    (hb : ContDiffOn ℝ ∞ b (Ω ×ˢ univ))
    (ν : ℝ^n → ℝ^n) (hν : ∀ x ∈ Γ, ν x ≠ 0)
    (hΓ : HasConormalParametrizations (ℝ^(n - 1)) Γ
      (fun x ↦ (innerSL ℝ (ν x)).toLinearMap))
    (hsymbol : ∀ x ∈ Γ, ∀ p : ∀ i : Fin k, Sym (Fin n) (i : ℕ) → ℝ,
      ∑ α, a α (x, p) * monomial α (ν x) ≠ 0)
    {u v : ℝ^n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (hdata : ∀ j < k, ∀ x ∈ Γ, normalData j u (ν x) x = normalData j v (ν x) x)
    (hPu : ∀ x ∈ Ω,
      ∑ α, a α (x, coordinateJetLT k u x) * coordinateDeriv α u x =
        b (x, coordinateJetLT k u x))
    (hPv : ∀ x ∈ Ω,
      ∑ α, a α (x, coordinateJetLT k v x) * coordinateDeriv α v x =
        b (x, coordinateJetLT k v x)) :
    ∀ j, EqOn (iteratedFDeriv ℝ j u) (iteratedFDeriv ℝ j v) Γ := by
  exact iteratedFDeriv_eq_on_of_cauchy_data_of_symbol_at_jet hk a b hΩ hΓΩ ha hb ν hν hΓ
    (fun x hx ↦ hsymbol x hx (coordinateJetLT k u x)) hu hv hdata hPu hPv

end PDE.Cauchy.Quasilinear
