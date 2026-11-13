/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Cauchy.Noncharacteristic.PrincipalJet
public import PDE.Analysis.Calculus.Jet.Hypersurface
public import PDE.LinearAlgebra.Multilinear.Conormal.Contraction

/-!
# Noncharacteristic determination of all jets

Tangential differentiation leaves only one conormal component at each order.
Below the order of the equation the normal Cauchy data determine it; at every
higher order the principal symbol determines it. The induction concerns actual
iterated Fréchet derivatives of the given smooth solutions.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace PDE.Analysis.Cauchy

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- All derivatives of two smooth solutions agree on a noncharacteristic
hypersurface when their lower normal Cauchy data agree. The coordinate
observations may be any finite family detecting a conormal tensor. -/
theorem iteratedFDeriv_eq_on_of_normal_data
    {ι : ℕ → Type*} [∀ j, Fintype (ι j)]
    {k : ℕ} (d : ∀ j, ι j → Fin j → E)
    (a : ι k → E × (∀ i : Fin k, E [×(i : ℕ)]→L[ℝ] ℝ) → ℝ)
    (b : E × (∀ i : Fin k, E [×(i : ℕ)]→L[ℝ] ℝ) → ℝ)
    {Γ : Set E} {ℓ : E → E →ₗ[ℝ] ℝ}
    (ha : ∀ α, ∀ x ∈ Γ, ∀ p, ContDiffAt ℝ ∞ (a α) (x, p))
    (hb : ∀ x ∈ Γ, ∀ p, ContDiffAt ℝ ∞ b (x, p))
    (hΓ : HasConormalParametrizations H Γ ℓ)
    (e : E → E) (he : ∀ x ∈ Γ, ℓ x (e x) = 1)
    (hdetect : ∀ j, 0 < j → j < k → ∀ x ∈ Γ,
      ∃ α, (∏ i, ℓ x (d j α i)) ≠ 0)
    {u v : E → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hvalue : EqOn u v Γ)
    (hdata : ∀ j, 0 < j → j < k → ∀ x ∈ Γ,
      ∑ α, iteratedFDeriv ℝ j u x (d j α) * ∏ i, ℓ x (d j α i) =
        ∑ α, iteratedFDeriv ℝ j v x (d j α) * ∏ i, ℓ x (d j α i))
    (hPu : ∀ x ∈ Γ, ∀ᶠ y in 𝓝 x,
      ∑ α, a α (y, jetLT ℝ k u y) * iteratedFDeriv ℝ k u y (d k α) =
        b (y, jetLT ℝ k u y))
    (hPv : ∀ x ∈ Γ, ∀ᶠ y in 𝓝 x,
      ∑ α, a α (y, jetLT ℝ k v y) * iteratedFDeriv ℝ k v y (d k α) =
        b (y, jetLT ℝ k v y))
    (hsymbol : ∀ x ∈ Γ,
      ∑ α, a α (x, jetLT ℝ k u x) * ∏ i, ℓ x (d k α i) ≠ 0) :
    ∀ j, EqOn (iteratedFDeriv ℝ j u) (iteratedFDeriv ℝ j v) Γ := by
  classical
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero =>
      intro x hx
      ext w
      simp [iteratedFDeriv_zero_apply, hvalue hx]
    | succ n =>
      intro x hx
      let A := iteratedFDeriv ℝ (n + 1) u x - iteratedFDeriv ℝ (n + 1) v x
      let c : ℝ := A (fun _ ↦ e x)
      have hA (w : Fin (n + 1) → E) :
          A w = (∏ i, ℓ x (w i)) * c := by
        exact hΓ.iteratedFDeriv_sub_eq_prod_smul hu hv
          (ih n (by omega)) hx (he x hx) w
      have hAzero : A = 0 := by
        by_cases hlow : n + 1 < k
        · have hz := A.toMultilinearMap.eq_zero_of_conormal_normal_sum_eq_zero
            (ℓ x) hA (d (n + 1)) (hdetect _ (by omega) hlow x hx) ?_
          · exact ContinuousMultilinearMap.toMultilinearMap_injective hz
          · change ∑ α, A (d (n + 1) α) * ∏ i, ℓ x (d (n + 1) α i) = 0
            simp only [A, sub_apply, sub_mul,
              Finset.sum_sub_distrib, hdata _ (by omega) hlow x hx, sub_self]
        · let r := n + 1 - k
          have hr : r + k = n + 1 := by omega
          have hA' : ∀ w : Fin (r + k) → E,
              (iteratedFDeriv ℝ (r + k) u x - iteratedFDeriv ℝ (r + k) v x) w =
                (∏ i, ℓ x (w i)) * c := by
            rw [hr]
            exact hA
          have hp := principal_jet_difference_eq_zero (r := r) (d k) a b
            hu hv x (e x) (fun α ↦ ha α x hx) (hb x hx) (hPu x hx) (hPv x hx)
            (fun i hi ↦ ih i (by omega) hx)
          have hprod (α : ι k) :
              (∏ i, ℓ x (Fin.append (fun _ : Fin r ↦ e x) (d k α) i)) =
                ∏ i, ℓ x (d k α i) := by
            simp [Fin.prod_univ_add, he x hx]
          have hc : c = 0 := by
            apply (mul_eq_zero.mp ?_).resolve_left (hsymbol x hx)
            rw [Finset.sum_mul]
            convert hp using 1
            apply Finset.sum_congr rfl
            intro α _
            rw [← sub_apply, hA', hprod, mul_assoc]
          ext w
          simp [hA, hc]
      exact sub_eq_zero.mp hAzero

end PDE.Analysis.Cauchy
