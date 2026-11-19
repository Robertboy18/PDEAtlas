/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Operator
public import PDE.Analysis.Asymptotics.OscillatoryIntegral.Calculus
public import PDE.FDeriv.PartialDeriv.Transforms
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Geometric-optics wave packets and their exact residual

For real amplitude `a` and phase `p`, the complex field is `exp(i p / ε) a`.
It inherits their regularity for every fixed parameter. Local C² data give the
expansion of the coordinate wave operator into amplitude, transport and
squared-eikonal terms. The time coordinate is zero; the remaining coordinates
are spatial.

For nonzero ε the exact wave equation is equivalent to the real balance
`a E = ε² □a` and the transport equation `T = 0`. This is an exact identity for
the ansatz.

The ansatz is (28) of Evans, §4.5.3(a), Example 3, and the real balance is (29) there. Evans
keeps only the real part of the expansion; our calculation also keeps the imaginary transport
term.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.3(a), Example 3, equations (27)-(29).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE PDE.Analysis Filter
open scoped Topology

namespace WaveEquation.GeometricOptics

variable {n : ℕ}

/-- The real-amplitude complex wave ansatz. Coordinate zero is time. -/
def wavePacket (ε : ℝ) (a p : ℝ^(n + 1) → ℝ) (z : ℝ^(n + 1)) : ℂ :=
  osc ε⁻¹ (p z) * (a z : ℂ)

/-- A wave packet inherits the local regularity of its amplitude and phase within a set.
The parameter is arbitrary, including zero under the total inverse convention. -/
theorem contDiffWithinAt_wavePacket {m : WithTop ℕ∞} {S : Set (ℝ^(n + 1))} {a p : ℝ^(n + 1) → ℝ}
    {z : ℝ^(n + 1)} (ha : ContDiffWithinAt ℝ m a S z) (hp : ContDiffWithinAt ℝ m p S z) (ε : ℝ) :
    ContDiffWithinAt ℝ m (wavePacket ε a p) S z := by
  have hac : ContDiffWithinAt ℝ m (fun y ↦ (a y : ℂ)) S z :=
    Complex.ofRealCLM.contDiff.comp_contDiffWithinAt ha
  have hpc : ContDiffWithinAt ℝ m (fun y ↦ (p y : ℂ)) S z :=
    Complex.ofRealCLM.contDiff.comp_contDiffWithinAt hp
  unfold wavePacket osc
  exact (Complex.contDiff_exp.comp_contDiffWithinAt
    ((contDiffWithinAt_const.mul hpc).mul contDiffWithinAt_const)).mul hac

/-- A wave packet inherits local regularity, in particular classical C² regularity. -/
theorem contDiffAt_wavePacket {m : WithTop ℕ∞} {a p : ℝ^(n + 1) → ℝ}
    {z : ℝ^(n + 1)} (ha : ContDiffAt ℝ m a z) (hp : ContDiffAt ℝ m p z) (ε : ℝ) :
    ContDiffAt ℝ m (wavePacket ε a p) z :=
  contDiffWithinAt_wavePacket ha hp ε

/-- A wave packet inherits regularity on the same domain. -/
theorem contDiffOn_wavePacket {m : WithTop ℕ∞} {S : Set (ℝ^(n + 1))}
    {a p : ℝ^(n + 1) → ℝ} (ha : ContDiffOn ℝ m a S) (hp : ContDiffOn ℝ m p S) (ε : ℝ) :
    ContDiffOn ℝ m (wavePacket ε a p) S :=
  fun z hz ↦ contDiffWithinAt_wavePacket (ha z hz) (hp z hz) ε

/-- A wave packet inherits global regularity for every fixed parameter. -/
theorem contDiff_wavePacket {m : WithTop ℕ∞} {a p : ℝ^(n + 1) → ℝ}
    (ha : ContDiff ℝ m a) (hp : ContDiff ℝ m p) (ε : ℝ) :
    ContDiff ℝ m (wavePacket ε a p) := by
  rw [contDiff_iff_contDiffAt]
  exact fun z ↦ contDiffAt_wavePacket ha.contDiffAt hp.contDiffAt ε

/-- The difference between the squared time and spatial phase derivatives. -/
def eikonalDefect (p : ℝ^(n + 1) → ℝ) (z : ℝ^(n + 1)) : ℝ :=
  (∂[0] p) z ^ 2 - ∑ i : Fin n, (∂[i.succ] p) z ^ 2

/-- The first-order transport expression in the amplitude-phase expansion. -/
def transportTerm (a p : ℝ^(n + 1) → ℝ) (z : ℝ^(n + 1)) : ℝ :=
  a z * waveOperator p z +
    2 * ((∂[0] p) z * (∂[0] a) z -
      ∑ i : Fin n, (∂[i.succ] p) z * (∂[i.succ] a) z)

/-- First derivative of the wave ansatz, using the shared oscillatory chain rule. -/
theorem partialDeriv_wavePacket {a p : ℝ^(n + 1) → ℝ} {z : ℝ^(n + 1)} (ha : DifferentiableAt ℝ a z)
    (hp : DifferentiableAt ℝ p z) (ε : ℝ) (i : Fin (n + 1)) :
    (∂[i] (wavePacket ε a p)) z = osc ε⁻¹ (p z) *
      (((∂[i] a) z : ℂ) + (ε⁻¹ : ℝ) * Complex.I * ((∂[i] p) z : ℂ) * (a z : ℂ)) := by
  have hosc : DifferentiableAt ℝ (fun y ↦ osc ε⁻¹ (p y)) z :=
    ((hasDerivAt_osc ε⁻¹ (p z)).hasFDerivAt.comp z hp.hasFDerivAt).differentiableAt
  have hac : DifferentiableAt ℝ (fun y ↦ (a y : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z ha
  unfold wavePacket
  rw [partialDeriv_mul hosc hac, PDE.Analysis.partialDeriv_osc_comp hp, partialDeriv_ofReal]
  simp only [Complex.real_smul]
  ring

/-- Local second-coordinate expansion before replacing the imaginary frequency square. -/
theorem secondPartialDeriv_wavePacket {a p : ℝ^(n + 1) → ℝ} {z : ℝ^(n + 1)}
    (ha : ContDiffAt ℝ 2 a z) (hp : ContDiffAt ℝ 2 p z) (ε : ℝ) (i : Fin (n + 1)) :
    (∂[i] (fun y ↦ (∂[i] (wavePacket ε a p)) y)) z =
      osc ε⁻¹ (p z) *
        (((∂[i] (fun y ↦ (∂[i] a) y)) z : ℂ) +
          ((ε⁻¹ : ℝ) * Complex.I) *
            ((a z : ℂ) * ((∂[i] (fun y ↦ (∂[i] p) y)) z : ℂ) +
              2 * ((∂[i] p) z : ℂ) * ((∂[i] a) z : ℂ)) +
          ((ε⁻¹ : ℝ) * Complex.I) ^ 2 * (a z : ℂ) * ((∂[i] p) z : ℂ) ^ 2) := by
  let q : ℂ := (ε⁻¹ : ℝ) * Complex.I
  let B : ℝ^(n + 1) → ℂ := fun y ↦ ((∂[i] a) y : ℂ) + q * ((∂[i] p) y : ℂ) * (a y : ℂ)
  have ha₁ := ha.differentiableAt (by norm_num)
  have hp₁ := hp.differentiableAt (by norm_num)
  have hda := (contDiffAt_partialDeriv 1 ha i).differentiableAt (by norm_num)
  have hdp := (contDiffAt_partialDeriv 1 hp i).differentiableAt (by norm_num)
  have hac : DifferentiableAt ℝ (fun y ↦ (a y : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z ha₁
  have hdac : DifferentiableAt ℝ (fun y ↦ ((∂[i] a) y : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z hda
  have hdpc : DifferentiableAt ℝ (fun y ↦ ((∂[i] p) y : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z hdp
  have hq : DifferentiableAt ℝ (fun _ : ℝ^(n + 1) ↦ q) z := differentiableAt_const q
  have hqp : DifferentiableAt ℝ (fun y ↦ q * ((∂[i] p) y : ℂ)) z := hq.mul hdpc
  have hprod : DifferentiableAt ℝ (fun y ↦ q * ((∂[i] p) y : ℂ) * (a y : ℂ)) z := hqp.mul hac
  have hB : DifferentiableAt ℝ B z := hdac.add hprod
  have hosc : DifferentiableAt ℝ (fun y ↦ osc ε⁻¹ (p y)) z :=
    ((hasDerivAt_osc ε⁻¹ (p z)).hasFDerivAt.comp z hp₁.hasFDerivAt).differentiableAt
  have hfirst : (fun y ↦ (∂[i] (wavePacket ε a p)) y) =ᶠ[𝓝 z]
      (fun y ↦ osc ε⁻¹ (p y) * B y) := by
    filter_upwards [ha.eventually (by simp), hp.eventually (by simp)] with y hay hpy
    simpa only [B, q] using partialDeriv_wavePacket
      (hay.differentiableAt (by norm_num)) (hpy.differentiableAt (by norm_num)) ε i
  have hBderiv : (∂[i] B) z = ((∂[i] (fun y ↦ (∂[i] a) y)) z : ℂ) +
        q * ((∂[i] (fun y ↦ (∂[i] p) y)) z : ℂ) * (a z : ℂ) +
        q * ((∂[i] p) z : ℂ) * ((∂[i] a) z : ℂ) := by
    dsimp only [B]
    rw [partialDeriv_add hdac hprod, partialDeriv_mul hqp hac, partialDeriv_mul hq hdpc]
    simp only [partialDeriv_const, partialDeriv_ofReal, zero_mul, zero_add]
    ring
  rw [partialDeriv_eq_of_fderiv_eq (hfirst.fderiv_eq (𝕜 := ℝ)) i,
    partialDeriv_mul hosc hB, PDE.Analysis.partialDeriv_osc_comp hp₁, hBderiv]
  simp only [B, q, Complex.real_smul]
  ring

/-- Expansion of the wave operator, retaining the squared imaginary frequency. -/
theorem waveOperator_wavePacket_frequency {a p : ℝ^(n + 1) → ℝ} {z : ℝ^(n + 1)}
    (ha : ContDiffAt ℝ 2 a z) (hp : ContDiffAt ℝ 2 p z) (ε : ℝ) :
    waveOperator (wavePacket ε a p) z = osc ε⁻¹ (p z) * (((waveOperator a z : ℝ) : ℂ) +
      ((ε⁻¹ : ℝ) * Complex.I) * (transportTerm a p z : ℂ) + ((ε⁻¹ : ℝ) * Complex.I) ^ 2 *
      (a z : ℂ) * (eikonalDefect p z : ℂ)) := by
  unfold waveOperator
  simp_rw [secondPartialDeriv_wavePacket ha hp]
  rw [← Finset.mul_sum, ← mul_sub]
  congr 1
  unfold transportTerm eikonalDefect waveOperator
  push_cast
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.mul_sum]
  ring_nf

/-- Scaling the residual displays its real and imaginary coefficients. -/
theorem scaled_waveOperator_wavePacket {a p : ℝ^(n + 1) → ℝ} {z : ℝ^(n + 1)}
    (ha : ContDiffAt ℝ 2 a z) (hp : ContDiffAt ℝ 2 p z) {ε : ℝ} (hε : ε ≠ 0) :
    (ε : ℂ) ^ 2 * waveOperator (wavePacket ε a p) z = osc ε⁻¹ (p z) *
      (((ε ^ 2 * waveOperator a z - a z * eikonalDefect p z : ℝ) : ℂ) + Complex.I *
      ((ε * transportTerm a p z : ℝ) : ℂ)) := by
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  rw [waveOperator_wavePacket_frequency ha hp]
  push_cast
  simp only [mul_pow, Complex.I_sq]
  field_simp [hεc]
  ring

/-- The wave ansatz solves the equation exactly when both coefficients vanish. -/
theorem waveOperator_wavePacket_eq_zero_iff {a p : ℝ^(n + 1) → ℝ} {z : ℝ^(n + 1)}
    (ha : ContDiffAt ℝ 2 a z) (hp : ContDiffAt ℝ 2 p z) {ε : ℝ} (hε : ε ≠ 0) :
    waveOperator (wavePacket ε a p) z = 0 ↔
      a z * eikonalDefect p z = ε ^ 2 * waveOperator a z ∧ transportTerm a p z = 0 := by
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  have hosc : osc ε⁻¹ (p z) ≠ 0 := Complex.exp_ne_zero _
  constructor
  · intro hsol
    have hid := scaled_waveOperator_wavePacket ha hp hε
    rw [hsol, mul_zero] at hid
    have hbracket := (mul_eq_zero.mp hid.symm).resolve_left hosc
    have hreal : ε ^ 2 * waveOperator a z - a z * eikonalDefect p z = 0 := by
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero,
        sub_zero, add_zero, Complex.zero_re] using congrArg Complex.re hbracket
    have himag : ε * transportTerm a p z = 0 := by
      simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul,
        zero_add, Complex.zero_im] using congrArg Complex.im hbracket
    exact ⟨(sub_eq_zero.mp hreal).symm, (mul_eq_zero.mp himag).resolve_left hε⟩
  · rintro ⟨hreal, himag⟩
    have hid := scaled_waveOperator_wavePacket ha hp hε
    rw [← hreal, sub_self, himag, mul_zero] at hid
    have hzero : (ε : ℂ) ^ 2 * waveOperator (wavePacket ε a p) z = 0 := by
      simpa using hid
    exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hεc)

/-- The local wave characterization at each point of an open domain. -/
theorem waveOperator_wavePacket_eq_zero_iff_on_open {U : Set (ℝ^(n + 1))} (hU : IsOpen U)
    {a p : ℝ^(n + 1) → ℝ} (ha : ContDiffOn ℝ 2 a U) (hp : ContDiffOn ℝ 2 p U) {z : ℝ^(n + 1)}
    (hz : z ∈ U) {ε : ℝ} (hε : ε ≠ 0) :
    waveOperator (wavePacket ε a p) z = 0 ↔
      a z * eikonalDefect p z = ε ^ 2 * waveOperator a z ∧ transportTerm a p z = 0 :=
  waveOperator_wavePacket_eq_zero_iff
    (ha.contDiffAt (hU.mem_nhds hz)) (hp.contDiffAt (hU.mem_nhds hz)) hε

end WaveEquation.GeometricOptics
