/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.WeakCauchy.Coefficients
public import PDE.Parabolic.Heat.Spectral.HilbertEvolution
public import PDE.Analysis.Evolution.Time.WeakDerivative.Bochner
import PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.Completion
import PDE.Analysis.Evolution.LionsMagenes.Regularity.OpenInterval

/-!
# Identification of weak Dirichlet heat solutions with the spectral orbit

Lions–Magenes supplies the integrated dual derivative from the natural Bochner
regularity. Testing against the eigenfunctions determines every Hilbert coordinate,
and hence the continuous pivot representative, including both endpoint times.

The competitor has an H⁻¹ weak time derivative. No strong L² time derivative,
energy inequality, or spectral representation is assumed.
-/

@[expose] public noncomputable section

namespace HeatEquation.DirichletHeatSpectrum

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution MeasureTheory Set
open scoped Sobolev InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} (S : DirichletHeatSpectrum n Ω)

/-- A Lions–Magenes heat evolution is the Hilbert-basis heat series at every closed time. -/
theorem representative_eq_spectralHeatEvolution (hopen : IsOpen Ω)
    {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → H¹₀(Ω)} {g : ℝ → StrongDual ℝ (H¹₀(Ω))}
    (E : ContinuousPivotEvolutionOn (h10L2GelfandTriple hopen) u g a b)
    (heq : ∀ v : H¹₀(Ω), ∀ᵐ t ∂volume.restrict (Ioc a b),
      g t v + dirichletForm (u t) v = 0)
    {t : ℝ} (ht : t ∈ Icc a b) :
    E.representative t =
      spectralHeatEvolution S.basis S.eigenvalue S.eigenvalue_nonneg
        (E.representative a) (t - a).toNNReal := by
  apply S.basis.repr.injective
  ext i
  rw [spectralHeatEvolution_repr, Real.coe_toNNReal _ (sub_nonneg.mpr ht.1),
    HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply,
    real_inner_comm (E.representative t) (S.basis i),
    real_inner_comm (E.representative a) (S.basis i)]
  exact S.coefficient_eq_exp hopen hab E heq i ht

/-- Every continuous L² representative with L²(H¹₀) slices and an L²(H⁻¹) weak
time derivative satisfying the Dirichlet heat equation is the constructed
spectral orbit. Spatial tests may have different exceptional time null sets. -/
theorem eq_spectralHeatEvolution_of_weak_equation (hopen : IsOpen Ω)
    {a b : ℝ} (hab : a < b)
    {u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))}
    {g : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))}
    (hg : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ (h10L2GelfandTriple hopen).energyToDual (u t)) g)
    {w : ℝ → DerivLp n 2 Ω} (hw : ContinuousOn w (Icc a b))
    (hwae : w =ᵐ[volume.restrict (Ioc a b)] fun t ↦ baseCoordCLM (u t))
    (heq : ∀ v : H¹₀(Ω), ∀ᵐ t ∂volume.restrict (Ioc a b),
      g t v + dirichletForm (u t) v = 0)
    {f : DerivLp n 2 Ω} (hinit : w a = f) :
    EqOn w (fun t ↦ spectralHeatEvolution S.basis S.eigenvalue S.eigenvalue_nonneg
      f (t - a).toNNReal) (Icc a b) := by
  obtain ⟨Eopen⟩ := hg.nonempty_continuousPivotEvolutionOnOpen hab
  obtain ⟨E⟩ := Eopen.toContinuousPivotEvolutionOn (h10L2GelfandTriple hopen) hab
    (Lp.memLp u) (Lp.memLp g)
  have hwae' : w =ᵐ[volume.restrict (Icc a b)] fun t ↦ baseCoordCLM (u t) := by
    rwa [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b))]
  have hEae : E.representative =ᵐ[volume.restrict (Icc a b)] w := by
    have hE := E.ae_eq_inclusion
    rw [uIcc_of_le hab.le] at hE
    exact hE.trans hwae'.symm
  have hEq := Measure.eqOn_Icc_of_ae_eq volume hab.ne hEae
    (by simpa only [uIcc_of_le hab.le] using E.continuousOn) hw
  intro t ht
  rw [← hEq ht, S.representative_eq_spectralHeatEvolution hopen hab.le E heq ht,
    hEq ⟨le_rfl, hab.le⟩, hinit]

end HeatEquation.DirichletHeatSpectrum
