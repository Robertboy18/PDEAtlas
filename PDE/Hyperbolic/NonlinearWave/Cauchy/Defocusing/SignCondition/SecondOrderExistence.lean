/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.ReactionLimit
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.ReactionPairing

/-!
# Weak displacement solutions for sign-condition reactions

H¹ × L² data with integrable initial potential give a displacement on the whole forward half-line.
Its H¹ bound is local in time, while its gradient and L² time Lipschitz bounds are global. On every
finite cylinder a joint representative satisfies the second-order weak wave equation with the
original reaction and both initial-data terms. Reaction integrability is a conclusion of the
truncation, energy, compactness and uniform-integrability argument.

The H¹ bound holds on each finite time interval. The weak equation is the limit equation (10) of
step 6 of the proof of Theorem 1 of Evans, §12.3.1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.1, step 6 of the proof of Theorem 1, equation (10).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution
open scoped ENNReal Topology InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert
open PDE.Analysis (primitive)

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- Uniform convergence of Hilbert pairings on all natural time windows gives
uniform convergence of every continuous linear observation on a finite window. -/
theorem tendstoUniformlyOn_dual_IciExtend {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {u : ℕ → ℝ → H} {q : Ici (0 : ℝ) → H}
    (hweak : ∀ k : ℕ, ∀ v : H, TendstoUniformly (fun i (t : Icc (0 : ℝ) (k : ℝ)) ↦ inner ℝ v
      (u i t)) (fun t : Icc (0 : ℝ) (k : ℝ) ↦ inner ℝ v (q ⟨t.val, t.property.1⟩)) atTop)
    (T : ℝ) (ell : StrongDual ℝ H) :
    TendstoUniformlyOn (fun i t ↦ ell (u i t)) (fun t ↦ ell (IciExtend q t)) atTop (Icc 0 T) := by
  obtain ⟨k, hk⟩ := exists_nat_ge T
  have hnat : TendstoUniformlyOn (fun i t ↦ ell (u i t))
      (fun t ↦ ell (IciExtend q t)) atTop (Icc 0 (k : ℝ)) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have hlim (t : Icc (0 : ℝ) (k : ℝ)) :
        IciExtend q t = q ⟨t.val, t.property.1⟩ := IciExtend_of_mem q t.property.1
    simpa only [Function.comp_def, hlim, InnerProductSpace.toDual_symm_apply] using
      hweak k ((InnerProductSpace.toDual ℝ H).symm ell)
  exact hnat.mono (Icc_subset_Icc le_rfl hk)

/-- Sign-preserving Lipschitz approximation constructs a weak displacement
solution with the original reaction and both Cauchy data. The spatial tests are H¹ classes with a
bounded, compactly supported representative. -/
theorem exists_second_order_weak_solution {n : ℕ} {m : ℕ∞} {f : ℝ → ℝ} (hf : ContDiff ℝ m f)
    (hm : m ≠ 0) (hs : ∀ z, 0 ≤ z * f z) (x : H¹(ℝ^n) × DerivLp n 2 univ)
    (hF :
      Integrable (fun y ↦ primitive f ((energyTriple n).inclusion x.1 y)) (domainMeasure n univ)) :
    ∃ q : Ici (0 : ℝ) → H¹(ℝ^n),
      q ⟨0, le_rfl⟩ = x.1 ∧
      Continuous (fun t ↦ toWeakSpace ℝ H¹(ℝ^n) (q t)) ∧
      LipschitzWith ⟨Real.sqrt (2 * physicalEnergy f x), Real.sqrt_nonneg _⟩
        (fun t ↦ (energyTriple n).inclusion (q t)) ∧
      (∀ t, ‖q t‖ ≤ ‖(energyTriple n).inclusion x.1‖ +
        (t.val + 1) * Real.sqrt (2 * physicalEnergy f x)) ∧
      (∀ t, gradientForm n (q t) (q t) ≤ 2 * physicalEnergy f x) ∧
      ∀ T : ℝ, 0 ≤ T → ∃ V : ℝ × (ℝ^n) → ℝ,
        StronglyMeasurable V ∧
        MemLp V 2 ((volume.restrict (Ioc 0 T)).prod (domainMeasure n univ)) ∧
        (∀ᵐ t ∂volume.restrict (Ioc 0 T),
          (fun y ↦ V (t, y)) =ᵐ[domainMeasure n univ]
            (energyTriple n).inclusion (IciExtend q t)) ∧
        (∀ s : Set (ℝ^n), IsCompact s → Integrable (fun z ↦ f (V z))
          ((volume.restrict (Ioc 0 T)).prod ((domainMeasure n univ).restrict s))) ∧
        ∀ s : Set (ℝ^n), IsCompact s → ∀ w : H¹(ℝ^n), ∀ ψ : (ℝ^n) → ℝ,
          StronglyMeasurable ψ → ∀ C : NNReal, (∀ y, ‖ψ y‖ ≤ C) →
          (∀ y, y ∉ s → ψ y = 0) →
          (((energyTriple n).inclusion w : (ℝ^n) → ℝ) =ᵐ[domainMeasure n univ] ψ) →
          ∀ τ σ : TimeTest 0 T, σ.toFun = τ.derivFun →
          (∫ t in (0 : ℝ)..T, ⟪(energyTriple n).inclusion (IciExtend q t),
            (energyTriple n).inclusion w⟫_ℝ * σ.derivFun t) +
            (∫ t in (0 : ℝ)..T, gradientForm n (IciExtend q t) w * τ.toFun t) +
            (∫ t in (0 : ℝ)..T,
              (∫ y, f (V (t, y)) * ψ y ∂domainMeasure n univ) * τ.toFun t) =
            ⟪x.2, (energyTriple n).inclusion w⟫_ℝ * τ.toFun 0 -
              ⟪(energyTriple n).inclusion x.1, (energyTriple n).inclusion w⟫_ℝ * σ.toFun 0 := by
  obtain ⟨g, K, hg, hg0, u, htr, hu, _, _, he, _, _⟩ := exists_energy_approximations hf hm hs x hF
  have hr : Tendsto (fun k : ℕ ↦ (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  obtain ⟨q, φ, _, hq0, hqc, hqlip, hqb, hqg, hweak, _, hlocal⟩ :=
    exists_energy_displacement_reaction_limit
      (g := g) (K := K) (E := physicalEnergy f x) hf.continuous hg
      (fun k ↦ (htr k).2.2.2.1) (fun k ↦ (htr k).2.2.2.2.1) (fun k ↦ (htr k).2.2.1) hr x u hu he
  refine ⟨q, hq0, hqc, hqlip, hqb, hqg, fun T hT ↦ ?_⟩
  obtain ⟨U, V, _, hV, hU, hVm, hUsec, hVsec, hlim⟩ := hlocal T hT
  refine ⟨V, hV, hVm, hVsec, fun s hs ↦ (hlim s hs).2.1, fun s hs w ψ hψ C hb hsupp hw τ σ hσ ↦ ?_⟩
  have : IsFiniteMeasure ((domainMeasure n univ).restrict s) :=
    isFiniteMeasure_restrict.mpr hs.measure_ne_top
  exact second_order_weak_pde_of_joint_convergence (g := fun i ↦ g (φ i)) (K := fun i ↦ K (φ i))
    (hg := fun i ↦ hg (φ i)) (hg0 := fun i ↦ hg0 (φ i)) (x := x)
    (u := fun i ↦ u (φ i)) (q := IciExtend q) (U := U) (V := V)
    (f := f) (s := s) (ψ := ψ) (C := C) (fun i ↦ hu (φ i)) hT (tendstoUniformlyOn_dual_IciExtend
      (u := fun i t ↦ (u (φ i) t).1) (q := q) hweak T) hU hUsec
    (hlim s hs).2.1 (hlim s hs).2.2 w hψ hb hsupp hw τ σ hσ

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
