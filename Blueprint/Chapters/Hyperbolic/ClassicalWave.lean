/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Hyperbolic.Transport
import Blueprint.Commands.Figures
import PDE.Hyperbolic.Classical.DAlembertFinitePropagation
import PDE.Hyperbolic.Classical.Dirichlet.Uniqueness
import PDE.Hyperbolic.Classical.EnergyIdentity
import PDE.Hyperbolic.Classical.ForwardFinitePropagation
import PDE.Hyperbolic.Classical.MovingBallTransport
import PDE.Hyperbolic.Models.Wave.DAlembert.ClassicalSolution
import PDE.Hyperbolic.Models.Wave.DAlembert.Derivatives
import PDE.Hyperbolic.Models.Wave.DAlembert.Formula
import PDE.Hyperbolic.Models.Wave.Duhamel.Existence
import PDE.Hyperbolic.Models.Wave.Equation
import PDE.Hyperbolic.Models.Wave.InitialValueProblem
import PDE.Hyperbolic.Models.Wave.Kirchhoff
import PDE.Hyperbolic.Models.Wave.Kirchhoff.ClassicalSolution
import PDE.Hyperbolic.Models.Wave.OddDimensions
import PDE.Hyperbolic.Models.Wave.OddDimensions.ClassicalSolution
import PDE.Hyperbolic.Models.Wave.EvenDimensions.ClassicalSolution
import PDE.Hyperbolic.Models.Wave.Operator
import PDE.Hyperbolic.Models.Wave.Poisson
import PDE.Hyperbolic.Models.Wave.Poisson.ClassicalSolution

/-!
# Classical wave equation

Classical wave solutions, representation formulas, and propagation.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Classical Wave Equations" =>

:::group "hyperbolic.classical_wave"
Classical wave equations
:::

# Why Characteristics Organize Hyperbolic Theory

For the wave equation $`u_{tt}-\Delta u=0` in one spatial dimension the
characteristics are the lines $`x\pm t=\text{const}`, and the general solution
decomposes into left- and right-traveling waves. A point disturbance in higher dimensions
propagates along expanding spheres, and the sharp Huygens principle (in odd
dimensions $`\geq 3`) says that the influence of a localized disturbance
passes through each point in a thin shell rather than lingering forever.

Physically, the wave equation models vibrating strings ($`n=1`),
membranes ($`n=2`), and acoustic or electromagnetic waves ($`n=3`). The
characteristic speed $`c=1` (in our normalization) is the speed of sound or
light. The d'Alembert, Kirchhoff, and Poisson formulas give the
explicit solution in dimensions 1, 3, and 2 respectively. Evans's Section 2.4
develops this material; {Informal.citet "courant-hilbert-1962"}[] (Vol. II,
Ch. VI) give the classical geometric perspective.

## Example: The d'Alembert Formula and Finite Propagation

For $`n=1`, the wave equation $`u_{tt}-u_{xx}=0` with initial displacement
$`g` and velocity $`h` has the explicit solution

$$`u(x,t)=\frac{g(x+t)+g(x-t)}{2}+\frac{1}{2}\int_{x-t}^{x+t}h(y)\,dy.`

*What the formula says.* The displacement term
$`\frac12[g(x+t)+g(x-t)]` is the average of two copies of the initial
shape, one shifted left by $`t` and one shifted right by $`t`. A bump in
$`g` thus splits into two counter-propagating half-sized copies, each
moving at unit speed.

{leanpde_figure "dalembert"}

The bump panels isolate the displacement term by taking zero initial velocity.
The cone panel records the interval needed for both terms of the formula.
The {ref "symbolic-sine-example"}[traveling-sine checks] from
the chapter introduction verify the derivatives of a translated profile;
compact support is the additional information that makes the bump's finite
propagation visible here.

The velocity term $`\frac{1}{2}\int_{x-t}^{x+t}h` integrates the initial
velocity over the interval of dependence.

*Finite propagation in practice.* Suppose both $`g` and $`h` vanish whenever
$`|x|>R`. Then $`u(x,t)=0` whenever $`|x|>R+t`. The support
expands at speed 1 and no faster. A disturbance localized near the origin
cannot influence a detector at distance $`L` until time $`t\geq L-R`.

:::definition "hyperbolic.wave.operator" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.waveOperator, WaveEquation.waveEquation, WaveEquation.nonhomogeneousWaveEquation, WaveEquation.nonhomogeneousWaveEquation_iff") (uses := "foundations.derivatives.partial, foundations.pde_problems.problem")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "65-66"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On $`\mathbb R^{n+1}` with time in coordinate zero, the wave operator is the
coordinate expression

$$`
\Box u=\partial_0\partial_0u-\sum_{i=1}^n\partial_i\partial_iu
=u_{tt}-\Delta u,
`

built from total partial derivatives, so classical use requires $`C^2`
hypotheses that are stated separately. The homogeneous and nonhomogeneous
wave equations on a domain $`U` are the single-equation problems $`\Box u=0`
and $`\Box u=f` on $`U` with no side conditions, and each bundled problem is
equivalent to the pointwise residual identity on $`U`.
:::

Since the operator is second order in time, a Cauchy problem must prescribe
both the displacement $`u(0,\cdot)=g` and the velocity $`u_t(0,\cdot)=h`. This
two-data problem is the wave counterpart of the one-datum transport problem.

:::definition "hyperbolic.wave.ivp" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.waveResidualAssignedCauchyDataProblem") (uses := "hyperbolic.wave.operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "66-68"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The residual-and-assigned-data problem records $`u_{tt}-\Delta u=0` at positive times,
initial displacement $`g`, and initial velocity $`h`. It is stated in $`n`
spatial dimensions with time in coordinate zero. Lean's derivative
operations are total, so the problem by itself implies neither $`C^2`
regularity nor convergence to the initial data.
:::

Both the residual and the assigned data are linear in $`u`, exactly as for
transport, but here the $`C^2` hypothesis enters even for the sum rule: a
second partial derivative of $`u+v` splits into two only when the first
partials are themselves differentiable.

:::theorem "hyperbolic.wave.superposition" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.waveOperator_add, WaveEquation.waveOperator_const_mul, WaveEquation.waveOperator_sub, WaveEquation.nonhomogeneousWaveEquation_add, WaveEquation.nonhomogeneousWaveEquation_const_mul, WaveEquation.nonhomogeneousWaveEquation_linear_combination, WaveEquation.nonhomogeneousWaveEquation_difference_same_source_zero") (uses := "hyperbolic.wave.operator")
The wave operator is linear. If $`u` and $`v` are $`C^2` at a point, then at
that point

$$`
\Box(u+v)=\Box u+\Box v,\qquad \Box(u-v)=\Box u-\Box v,
`

and $`\Box(cu)=c\,\Box u` holds for every constant $`c` with no regularity
hypothesis. Consequently, if $`u,v\in C^2(\mathbb R^{n+1})` satisfy
$`\Box u=f` and $`\Box v=g` on $`U`, then for all constants $`c_1,c_2`

$$`
\Box(c_1u+c_2v)=c_1f+c_2g\quad\text{on }U,
`

two witnesses with the same source have a difference solving the homogeneous
equation on $`U`, and homogeneous residual witnesses are closed under linear
combinations. The conclusions are pointwise residual identities.
:::

:::proof "hyperbolic.wave.superposition" (uses := "foundations.derivatives.linearity")
Under the local $`C^2` hypotheses the first partial derivatives of the sum
are differentiable, so the sum rule for partial derivatives applies twice and
gives the second-order identity coordinate by coordinate. The total Fréchet
derivative commutes with scalar multiplication without any hypothesis. The
problem-level statements combine these operator identities with the residual
identities of the two witnesses.
:::

In one space dimension the wave operator factors as
$`(\partial_t-\partial_x)(\partial_t+\partial_x)`, so solutions are sums of a
left-moving and a right-moving profile. Matching the two profiles to the
Cauchy data yields d'Alembert's formula.

:::definition "hyperbolic.wave.dalembert_formula" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.dAlembertFormula, WaveEquation.dAlembertSolution1D")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "67-68"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For initial displacement $`g` and velocity $`h`, the one-dimensional
d'Alembert field is

$$`
u(t,x)=\frac{g(x+t)+g(x-t)}2
+\frac12\int_{x-t}^{x+t}h(y)\,dy.
`

The spacetime form uses coordinate zero for $`t` and coordinate one for
$`x`, matching the residual-and-assigned-data problem.
:::

The formula evaluates $`g` at two translated points and integrates $`h` over
the interval between them, so two derivatives of $`g` and one of $`h` are
exactly what differentiating it twice requires.

:::theorem "hyperbolic.wave.dalembert_solution" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.contDiff_two_dAlembertFormula, WaveEquation.contDiff_two_dAlembertSolution1D, WaveEquation.dAlembertSolution1D_satisfiesResidualAssignedCauchyData, WaveEquation.tendsto_dAlembertSolution1D_initial_position, WaveEquation.tendsto_partialDeriv_dAlembertSolution1D_initial_velocity") (uses := "hyperbolic.wave.ivp, hyperbolic.wave.dalembert_formula")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "68-69"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`g` of class $`C^2` and $`h` of class $`C^1`, d'Alembert's
one-dimensional field is globally $`C^2`, satisfies the residual and assigned
Cauchy equalities in {uses "hyperbolic.wave.ivp"}[], and converges jointly in
spacetime to the prescribed displacement and velocity at the initial surface.
Both initial limits allow approach from either time direction.
:::

:::proof "hyperbolic.wave.dalembert_solution"
Differentiate the two translated copies of $`g` and the interval integral
of $`h`, then check the wave residual, the displacement trace, and the
velocity trace in turn.
:::

Take $`g(x)=x^2` and $`h(x)=0`. The hypotheses of
{bpref "hyperbolic.wave.dalembert_solution"}[the formula theorem] hold, and
the two characteristic translates give

$$`
u(x,t)=\frac{(x+t)^2+(x-t)^2}{2}=x^2+t^2.
`

Hence $`u_{tt}=u_{xx}=2`, $`u(x,0)=x^2`, and $`u_t(x,0)=0`.
The mixed terms cancel when the left- and right-moving contributions are
added. The data are smooth but neither compactly supported nor of finite
energy, so this is an example of the classical formula theorem.

The one-dimensional factorization into two scalar directional derivatives
does not extend to higher dimensions. The explicit formulas instead average
the data over spheres or
disks rather than evaluating them at two points.

:::definition "hyperbolic.wave.higher_dimensional_formulas" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.kirchhoffFormula, WaveEquation.poissonFormula") (uses := "hyperbolic.wave.ivp")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "70-74"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`t>0`, the three-dimensional Kirchhoff expression is defined by

$$`
u(t,x)=\frac{1}{4\pi t^2}\int_{\partial B_t(x)}
\bigl(g(y)+t\,h(y)+Dg(y)\cdot(y-x)\bigr)\,dS(y),
`

while the two-dimensional Poisson expression integrates
$`g(y)+t\,h(y)+Dg(y)\cdot(y-x)` over $`B_t(x)` with kernel
$`(2\pi t\sqrt{t^2-\lVert x-y\rVert^2})^{-1}`. Evans treats these
constructions in §2.4.1.
:::

:::theorem "hyperbolic.wave.kirchhoff_poisson_solution" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.contDiff_two_kirchhoffFormula, WaveEquation.kirchhoffFormula_satisfiesResidualAssignedCauchyData, WaveEquation.tendsto_kirchhoffFormula_initial_position, WaveEquation.tendsto_partialDeriv_kirchhoffFormula_initial_velocity, WaveEquation.contDiff_two_poissonFormula, WaveEquation.poissonFormula_satisfiesResidualAssignedCauchyData, WaveEquation.tendsto_poissonFormula_initial_position, WaveEquation.tendsto_partialDeriv_poissonFormula_initial_velocity") (uses := "hyperbolic.wave.higher_dimensional_formulas, hyperbolic.wave.ivp")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "67"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 11, endLine := 21 }
    }
  ]
}
%%%
Let $`g\in C^3(\mathbb R^n)` and $`h\in C^2(\mathbb R^n)`, with
$`n=3` for Kirchhoff and $`n=2` for Poisson. The signed-time formula defines
a jointly $`C^2` spacetime field, satisfies $`u_{tt}-\Delta u=0` for
$`t>0`, and has $`u(0,x)=g(x)` and $`u_t(0,x)=h(x)`. Moreover,

$$`
u(t,y)\longrightarrow g(x),\qquad u_t(t,y)\longrightarrow h(x)
\quad\text{as }(t,y)\longrightarrow(0,x).
`

These are joint traces, including approach through positive times. Neither
compact support nor a growth bound on the data is required.
:::

:::proof "hyperbolic.wave.kirchhoff_poisson_solution"
In three dimensions the radius times the spherical mean solves the wave
equation. Differentiate the displacement potential once in time and add the
velocity potential. Its signed-radius regularity justifies the second
spacetime derivatives and identifies both values at zero. For the planar
formula, lift the data constantly in a third coordinate and descend the
Kirchhoff solution. Independence of that coordinate removes its second
spatial derivative. The sphere-to-disk identity gives Poisson's kernel, and
joint continuity gives the stated traces.
:::

Evans reaches the spherical formulas by averaging the solution itself.
Averaging $`u(t,\cdot)` over spheres centered at $`x` reduces
the spatial variable to a single radius, at the cost of a coefficient that is
singular at $`r=0`.

:::definition "hyperbolic.wave.spherical_mean" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.waveSphericalMean")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "74-76"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a spacetime field $`u` in $`n` spatial dimensions, its signed-radius
spherical mean about $`x` is

$$`
M_u(t,x,r)=\frac1{|S^{n-1}|}
  \int_{S^{n-1}}u(t,x+r\omega)\,dS(\omega).
`

The signed-radius convention makes $`M_u` even in $`r`; in positive
dimension its value at $`r=0` is $`u(t,x)`.
:::

For a classical solution the spherical mean inherits a one-dimensional
equation in $`(t,r)` from the wave equation, because averaging commutes with
$`\partial_t` and turns the Laplacian into the radial operator
$`\partial_{rr}+\frac{n-1}r\partial_r`.

:::theorem "hyperbolic.wave.euler_poisson_darboux" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.waveSphericalMean_eulerPoissonDarboux") (uses := "hyperbolic.wave.spherical_mean")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "74-76"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n>0`, let $`u\in C^2(\mathbb R^{n+1})` satisfy
$`u_{tt}-\Delta u=0`, and let $`r>0`. Then its spherical mean satisfies the
Euler–Poisson–Darboux equation

$$`
\partial_{tt}M_u(t,x,r)
=\partial_{rr}M_u(t,x,r)
 +\frac{n-1}{r}\,\partial_rM_u(t,x,r).
`
:::

:::proof "hyperbolic.wave.euler_poisson_darboux"
Differentiate the fixed-sphere average twice in time and replace
$`u_{tt}` by $`\Delta u`. The radial Laplacian identity for spherical means
turns the average of $`\Delta u` into
$`\partial_{rr}M+(n-1)r^{-1}\partial_rM`.
:::

When $`n=2m+3` is odd, applying $`(r^{-1}\partial_r)^m` to $`r^{2m+1}M_u`
removes the singular first-order term from the Euler–Poisson–Darboux equation
and leaves the one-dimensional wave equation in $`(t,r)`. This is what
makes odd dimensions tractable: the transformed profile is governed by
d'Alembert's formula, and evaluating at the center recovers $`u`.

:::definition "hyperbolic.wave.odd_dimensional_formula" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.evansOddDimensionalFormula, WaveEquation.oddSphericalProfile, PDE.Analysis.oddRadialTransform") (uses := "hyperbolic.wave.spherical_mean")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "75-77"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Write the odd space dimension as $`n=2m+3` and set

$$`
P_m[f,x](r)=
\left(\frac1r\frac d{dr}\right)^m
\left(r^{2m+1}\frac1{|S^{n-1}|}
  \int_{S^{n-1}}f(x+r\omega)\,dS(\omega)\right).
`

For positive time, Evans's representation is

$$`
\mathcal E_m[g,h](x,t)
=\frac{\partial_rP_m[g,x](t)+P_m[h,x](t)}{(2m+1)!!}.
`

The Lean radial transform is a total function, including at $`r=0`.
:::

The representation theorem has the logical shape of a uniqueness statement. It
starts from a given $`C^2` solution and shows that it must equal
$`\mathcal E_m[g,h]` at positive times.

:::theorem "hyperbolic.wave.odd_dimensional_representation" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.eq_evansOddDimensionalFormula_of_wave") (uses := "hyperbolic.wave.ivp, hyperbolic.wave.odd_dimensional_formula")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "75-77"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n=2m+3`, fix $`x\in\mathbb R^n`, and let
$`u\in C^2(\mathbb R^{n+1})` solve the wave Cauchy problem with displacement
$`g` and velocity $`h`. For each positive time, assume its spherical mean
is $`C^{m+2}` on the whole signed-radius line. Assume also
$`P_m[g,x]\in C^2(\mathbb R)` and $`P_m[h,x]\in C^1(\mathbb R)`.
For every $`0\leq k\leq m`, require the specified totalized function

$$`
(q,r)\longmapsto
\left(\frac1r\frac d{dr}\right)^k
\left(r^{2m+1}M_u(q,x,r)\right)
`

to be $`C^3` on all of $`\mathbb R^2`, including the axis $`r=0`.
Then for every $`t>0`,

$$`u(t,x)=\mathcal E_m[g,h](x,t).`

These hypotheses are the removable-singularity input for the radial
reduction; the reduced wave equation and the representation identity are
proved from them. When $`g\in C^{m+3}` and $`h\in C^{m+2}`, the
{bpref "hyperbolic.wave.odd_dimensional_solution"}[solution theorem]
removes them: every $`C^2` solution then equals $`\mathcal E_m[g,h]`.
:::

:::proof "hyperbolic.wave.odd_dimensional_representation" (uses := "hyperbolic.wave.euler_poisson_darboux, hyperbolic.wave.dalembert_solution")
Euler–Poisson–Darboux and the radial intertwining identity reduce the
transformed spherical profile to a one-dimensional wave. Joint regularity
justifies commuting the radial transform with time differentiation and
controls its specified values and derivatives at the center. The assigned
Cauchy data identify the transformed initial profiles, one-dimensional
uniqueness gives d'Alembert's solution, and the center derivative recovers
$`u(t,x)` with normalization $`(2m+1)!!`.
:::

:::theorem "hyperbolic.wave.odd_dimensional_solution" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.contDiff_two_oddWaveSolution, WaveEquation.oddWaveSolution_eq_evansOddDimensionalFormula, WaveEquation.oddWaveSolution_satisfiesResidualAssignedCauchyData, WaveEquation.tendsto_oddWaveSolution_initial_position, WaveEquation.tendsto_partialDeriv_oddWaveSolution_initial_velocity, WaveEquation.eq_oddWaveSolution_of_satisfiesResidualAssignedCauchyData, WaveEquation.eq_evansOddDimensionalFormula_of_satisfiesResidualAssignedCauchyData") (uses := "hyperbolic.wave.odd_dimensional_formula, hyperbolic.wave.ivp")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "67"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 11, endLine := 21 }
    }
  ]
}
%%%
For $`n=2m+3`, $`g\in C^{m+3}(\mathbb R^n)` and
$`h\in C^{m+2}(\mathbb R^n)`, the constructed field is jointly $`C^2`
on all signed times and equals $`\mathcal E_m[g,h]` at positive times.
It solves $`u_{tt}-\Delta u=0` there, has the assigned displacement and
velocity at zero, and both $`u` and $`u_t` converge jointly to those data at
every point of the initial surface. There are no support or growth assumptions.
Every globally $`C^2` field satisfying the same positive-time wave equation
and assigned Cauchy data agrees with this field at all nonnegative times,
and so equals $`\mathcal E_m[g,h]` at positive times with no hypothesis on its
spherical means.
:::

:::proof "hyperbolic.wave.odd_dimensional_solution"
Integral formulas for the weighted radial derivatives extend the potential
smoothly across zero. Their finite-order bounds give a $`C^3` displacement
potential and a $`C^2` velocity potential. The radial identity proves the
wave equation; taking one time derivative of the displacement potential
produces the formula with normalization $`(2m+1)!!`. Its values and first
time derivative at zero identify the traces.
The energy domain-of-dependence theorem gives uniqueness among globally
$`C^2` fields with the same Cauchy data.
:::

Even dimensions are reached by descent from the next odd dimension.

:::theorem "hyperbolic.wave.even_dimensional_solution" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.evenWaveSolution_satisfiesResidualAssignedCauchyData, WaveEquation.evenBallProfile, WaveEquation.evansEvenDimensionalFormula, WaveEquation.contDiff_two_evenWaveSolution, WaveEquation.evenWaveSolution_eq_evansEvenDimensionalFormula, WaveEquation.tendsto_evenWaveSolution_initial_position, WaveEquation.tendsto_partialDeriv_evenWaveSolution_initial_velocity, WaveEquation.eq_evenWaveSolution_of_satisfiesResidualAssignedCauchyData") (uses := "hyperbolic.wave.odd_dimensional_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "67"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 11, endLine := 21 }
    }
  ]
}
%%%
For $`n=2m+2`, $`g\in C^{m+3}(\mathbb R^n)` and
$`h\in C^{m+2}(\mathbb R^n)`, set, for $`r>0`,

$$`
Q_m[f,x](r)=\left(\frac1r\frac d{dr}\right)^m
\left(\frac{r^{2m+2}}{|B_r(x)|}\int_{B_r(x)}
 \frac{f(y)}{\sqrt{r^2-\lVert y-x\rVert^2}}\,dy\right).
`

The field constructed by descent is jointly $`C^2` on all signed times and,
for $`t>0`, equals

$$`u(t,x)=\frac{\partial_rQ_m[g,x](t)+Q_m[h,x](t)}{(2m+2)!!}.`

It satisfies the wave equation at positive times, the assigned initial
position and velocity, and both joint Cauchy traces. The statement includes
$`m=0`, hence the planar formula, without support or growth hypotheses.
Every globally $`C^2` field with the same positive-time wave equation and
assigned Cauchy data agrees with the constructed field at nonnegative times.
:::

:::proof "hyperbolic.wave.even_dimensional_solution"
Apply the odd-dimensional construction to the lifted data. Independence of
the extra coordinate holds before differentiation, so the extra Laplacian
term vanishes. Sphere projection proves integrability of the weighted ball
kernel and gives the ratio $`(2m+1)!!/(2m+2)!!`. Equality of the profiles on
the open positive-radius interval passes to their radial derivatives.
Restriction of the signed-time field preserves regularity and both traces.
Uniqueness follows from the energy domain-of-dependence theorem.
:::

:::theorem "hyperbolic.wave.poisson_positive_time" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.poissonFormula_of_pos") (uses := "hyperbolic.wave.higher_dimensional_formulas")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "73-74"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
At positive time, the total two-dimensional definition reduces to Evans's
ordinary disk-integral formula with coefficient $`1/(2\pi t)`.
:::

:::proof "hyperbolic.wave.poisson_positive_time"
For $`t>0`, substitute $`|t|=t` and discard the zero-radius branch.
The defining disk integral and its coefficient then have exactly the
stated positive-time form.
:::

In three dimensions the Kirchhoff expression integrates over the sphere of
radius $`t` about $`x` and nowhere inside it. Once that sphere has moved
entirely beyond the support of the data every term vanishes; this is the sharp
Huygens principle, read off directly from the geometry of the formula.

:::theorem "hyperbolic.wave.kirchhoff_huygens" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.kirchhoffFormula_eq_zero_after_wavefront") (uses := "hyperbolic.wave.higher_dimensional_formulas")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "72"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "78-80"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
If $`R\geq0` and
$`\operatorname{supp}g\cup\operatorname{supp}h\subseteq\overline B_R(0)`,
then at a fixed point $`x` the three-dimensional Kirchhoff expression obeys

$$`
u(t,x)=0\qquad\text{whenever }t>\lVert x\rVert+R.
`

This conclusion uses only the support geometry of the formula, with no
regularity of the data. For $`C^3` displacement and $`C^2`
velocity, the {bpref "hyperbolic.wave.kirchhoff_poisson_solution"}[Kirchhoff
solution theorem] identifies it with a classical wave having both joint
initial traces.
:::

:::proof "hyperbolic.wave.kirchhoff_huygens"
If $`t>\lVert x\rVert+R`, every point on the integration sphere lies
strictly outside $`\overline B_R(0)` by the reverse triangle inequality.
Both data vanish there, and $`g` vanishes on a neighborhood of each such
point, so its spatial gradient is zero there as well. Every term of the
Kirchhoff integrand therefore vanishes.
:::

The planar formula has no such property, and the reason is visible in its
domain of integration: Poisson's integral runs over the whole disc
$`B(x,t)`, not over its rim, so the data the front has already passed keep
contributing. The figure takes one radial velocity bump and evaluates
both formulas. In $`\mathbb R^3` the signal at a fixed point is a pulse that
stops once the sphere of radius $`t` has cleared the support. In
$`\mathbb R^2`, the nonnegative velocity bump continues to contribute
through the positive weight $`1/\sqrt{t^2-|x-y|^2}` inside the expanding
disc, leaving a decaying tail after the front has passed. The planar tail
is computed from Poisson's formula; the formalized statement is the
three-dimensional vanishing theorem.

{leanpde_figure "wave-huygens"}

The same kind of support argument is available in one dimension, where it is
completely elementary because d'Alembert's formula involves only the interval
$`[x-t,x+t]`.

:::theorem "hyperbolic.wave.dalembert_domain_of_dependence" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.dAlembertFormula_eq_of_eqOn_domainOfDependence, WaveEquation.dAlembertFormula_eq_zero_of_vanishes_on_domainOfDependence") (uses := "hyperbolic.wave.dalembert_formula")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "68"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "78-80"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
At nonnegative time, d'Alembert's value at $`(x,t)` depends only on the two
initial data restricted to $`[x-t,x+t]`. No differentiability assumptions
are needed because this is a theorem about the representation formula itself.
:::

:::proof "hyperbolic.wave.dalembert_domain_of_dependence"
The two translated displacement values are the endpoints of
$`[x-t,x+t]`, and the velocity term integrates only over that interval.
Agreement of both data there makes all three terms agree; vanishing data is
the special case compared with zero.
:::

Read in the other direction, dependence on $`[x-t,x+t]` alone bounds where the
formula can be nonzero.

:::theorem "hyperbolic.wave.dalembert_finite_propagation" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.support_dAlembertFormula_subset_expandingInterval") (uses := "hyperbolic.wave.dalembert_domain_of_dependence")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "68"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "78-80"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
If both one-dimensional initial data are supported in $`[-R,R]`, then at
nonnegative time $`t` the support of d'Alembert's formula is contained in
$`[-R-t,R+t]`.
:::

:::proof "hyperbolic.wave.dalembert_finite_propagation"
For a point outside the enlarged interval, the entire backward characteristic
interval misses the support of both initial data. Both translated endpoint
terms and the integral term therefore vanish.
:::

Support arguments of this kind depend on having an explicit formula. The
energy method proves finite propagation in every space dimension $`n\geq1`
without one, by tracking $`\frac12(u_t^2+|D_xu|^2)` and its flux.

:::definition "hyperbolic.wave.energy_density" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.classicalWaveEnergyDensity, WaveEquation.classicalWaveEnergyFlux, WaveEquation.classicalWaveEnergyBalanceResidual, WaveEquation.classicalWaveEnergyDensity_nonneg") (uses := "foundations.derivatives.partial")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "83-84"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a spacetime field $`u` on $`\mathbb R^{n+1}`, the classical wave-energy
density, the spatial energy-flux components, and the local energy-balance
residual are

$$`
e(u)=\frac12\bigl(u_t^2+|D_xu|^2\bigr),\qquad
F_i(u)=u_t\,\partial_{x_i}u\quad(1\le i\le n),
`

$$`
R(u)=\partial_te(u)-\sum_{i=1}^n\partial_{x_i}F_i(u).
`

Here $`D_xu` collects the spatial partial derivatives. The density is
nonnegative, and the residual is the pointwise defect in the conservation law
$`\partial_te-\operatorname{div}_x(u_tD_xu)=0`.
:::

:::theorem "hyperbolic.wave.local_energy_identity" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.classicalWaveEnergyBalanceResidual_eq_mul_waveOperator, WaveEquation.classicalWaveEnergyBalanceResidual_eq_zero") (uses := "hyperbolic.wave.energy_density, hyperbolic.wave.operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "83-84"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`u` is $`C^2` at a spacetime point $`p`, then at $`p`

$$`
\partial_te(u)-\operatorname{div}_x\bigl(u_tD_xu\bigr)
=u_t\,\bigl(u_{tt}-\Delta u\bigr).
`

In particular a field that is $`C^2` at $`p` with $`\Box u(p)=0` has zero
local energy residual there. This is the pointwise computation behind
Evans's energy proofs of uniqueness and of the domain of dependence; it
involves no integration.
:::

:::proof "hyperbolic.wave.local_energy_identity" (uses := "foundations.derivatives.mixed_commutation")
Differentiate the density with the product rule,
$`\partial_te=u_tu_{tt}+\sum_iu_{x_i}\,\partial_tu_{x_i}`, and each flux
component, $`\partial_{x_i}(u_tu_{x_i})=u_{x_i}\,\partial_{x_i}u_t+u_tu_{x_ix_i}`.
Since $`u` is $`C^2` at $`p`, the mixed partial derivatives commute,
$`\partial_tu_{x_i}=\partial_{x_i}u_t`, so the cross terms cancel in the
difference and what remains is $`u_t\,(u_{tt}-\sum_iu_{x_ix_i})`.
:::

Integrating the pointwise identity over a ball whose radius shrinks at unit
speed gives the energy inside a backward cone as a function of time.

:::theorem "hyperbolic.wave.moving_ball_energy" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.hasDerivAt_backwardConeEnergy") (uses := "hyperbolic.wave.energy_density")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "83-84"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\geq1`, $`u\in C^2(\mathbb R^{n+1})`, and fix a center $`x_0`
and terminal time $`T`. At every $`t<T`, the derivative of the energy on
$`B_{T-t}(x_0)` is the integral of the local energy-balance residual over
that ball plus the surface integral of $`u_tD_xu\cdot\nu-e`.
:::

:::proof "hyperbolic.wave.moving_ball_energy" (uses := "hyperbolic.wave.local_energy_identity")
Differentiate the integral over the shrinking ball with Reynolds transport:
the moving boundary contributes minus the energy density. By the definition
of the energy-balance residual, the density derivative is that residual
plus a spatial divergence. Gauss's theorem converts that divergence to the
remaining lateral flux.
:::

For a solution the volume term vanishes, and the lateral flux has a sign: by
Cauchy–Schwarz, $`u_tD_xu\cdot\nu\le\frac12(u_t^2+|D_xu|^2)`, so the cone
energy is nonincreasing.

The figure shows the mechanism in one space dimension, where d'Alembert's
formula makes the energy density explicit. Each half of the initial bump
carries its share of the energy along a characteristic strip. The edges of
the backward cone move at the same unit speed, so a strip can cross an edge
only outward, and the cone energy drops each time a half-wave leaves and is
flat in between. The theorems are stated for every $`n\geq1`; the
one-dimensional picture is the case that can be drawn.

{leanpde_figure "cone-energy"}

:::theorem "hyperbolic.wave.finite_propagation" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.eq_zero_on_closed_backwardCone")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "83-84"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\ge1` and $`R>0`. Let $`u` be $`C^2` and solve the wave equation in the
cone $`t_0\le t<t_0+R`, $`\lVert x-x_0\rVert<R-(t-t_0)`. If
$`u(t_0,\cdot)=u_t(t_0,\cdot)=0` on $`\overline B_R(x_0)`, then

$$`
u(t,x)=0
\quad\text{whenever}\quad
t_0\leq t\leq t_0+R,\qquad
\lVert x-x_0\rVert\leq R-(t-t_0).
`

Thus zero Cauchy data on the base ball force vanishing throughout the
corresponding closed backward cone.
:::

:::proof "hyperbolic.wave.finite_propagation" (uses := "hyperbolic.wave.moving_ball_energy")
The wave equation kills the volume residual in
{uses "hyperbolic.wave.moving_ball_energy"}[]. The lateral flux is
nonpositive, so the nonnegative shrinking-cone energy cannot increase from
its zero initial value. Vanishing energy yields vanishing time and spatial
derivatives in the cone, and the initial trace fixes the remaining constant.
:::

Linearity turns the vanishing theorem into a comparison theorem: the value of a
solution inside the closed cone is determined by the data on its base.

:::theorem "hyperbolic.wave.domain_of_dependence" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.eq_on_closed_backwardCone_of_eq_initialData")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "83-84"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\ge1` and $`R>0`. Let $`u` and $`v` be $`C^2` and solve the wave
equation in the cone $`t_0\le t<t_0+R`, $`\lVert x-x_0\rVert<R-(t-t_0)`. If
$`u(t_0,\cdot)=v(t_0,\cdot)` and
$`u_t(t_0,\cdot)=v_t(t_0,\cdot)` on $`\overline B_R(x_0)`, then

$$`
u(t,x)=v(t,x)
\quad\text{for}\quad
\ t_0\leq t\leq t_0+R,\qquad
\lVert x-x_0\rVert\leq R-(t-t_0).
`

This is the closed-cone domain-of-dependence statement.
:::

:::proof "hyperbolic.wave.domain_of_dependence" (uses := "hyperbolic.wave.finite_propagation")
Apply finite propagation to the difference of the two waves. Linearity gives
the homogeneous wave equation, and equality of the two initial traces makes
the displacement and velocity of the difference vanish on the base ball.
:::

The same energy argument runs on the forward half-space alone, where the data
sit on the initial slice and nothing is assumed at negative times.

:::theorem "hyperbolic.wave.forward_finite_propagation" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.eq_zero_on_closed_backwardCone_forward") (uses := "hyperbolic.wave.finite_propagation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "83-84"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\ge1` and $`T>0`. Let $`u` be $`C^2` on $`\{t>0\}` and $`C^1` on
$`\{t\ge0\}`, and let $`u` solve the wave equation for $`0<t<T`,
$`\lVert x-x_0\rVert<T-t`. If $`u(0,x)=0` and the right time derivative
$`u_t(0^+,x)` vanishes for $`\lVert x-x_0\rVert<T`, then $`u(t,x)=0` for
$`0\le t\le T` and $`\lVert x-x_0\rVert\le T-t`, including the lateral boundary
and the vertex.
:::

:::proof "hyperbolic.wave.forward_finite_propagation"
For each positive start time the moving-ball identity makes the cone energy
nonincreasing, and the $`C^1` regularity up to the initial slice makes that
energy tend to zero as the start time decreases to zero. So the energy
vanishes on every positive slice, $`u_t` vanishes inside the cone, and
integrating along vertical segments from the zero initial value gives
$`u=0`. Continuity extends this to the closed cone.
:::

On a bounded spatial domain the lateral boundary replaces the cone. Evans's
energy uniqueness theorem compares two solutions with the same data.

:::theorem "hyperbolic.wave.dirichlet_uniqueness" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.eq_on_closedCylinder_of_initial_eq") (uses := "hyperbolic.wave.local_energy_identity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "83"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subseteq\mathbb R^n` be open and bounded with $`C^1` graph
boundary, and let $`a<b`. Let $`u` and $`v` be $`C^2` up to the boundary of
$`\Omega\times(a,b)`, continuous on its closure, and solve
$`u_{tt}-\Delta u=f` there with the same forcing $`f`. If $`u=v` on
$`\partial\Omega\times[a,b]`, and $`u(a,\cdot)=v(a,\cdot)` and
$`u_t(a^+,\cdot)=v_t(a^+,\cdot)` on $`\Omega`, then $`u=v` on
$`\overline\Omega\times[a,b]`.
:::

:::proof "hyperbolic.wave.dirichlet_uniqueness"
The difference $`w=u-v` solves the homogeneous equation with zero lateral,
displacement, and velocity data. The wave equation cancels the time
derivative of the cylinder energy $`\int_\Omega(w_t^2+\lvert Dw\rvert^2)`,
the boundary term vanishing because $`w=0` on the lateral boundary. The energy
starts at zero, so $`w_t` and $`Dw` vanish, and the zero initial value gives
$`w=0` on the closed cylinder.
:::

## Duhamel's Principle: Forcing with Zero Cauchy Data

A source acting at time $`s` contributes a homogeneous wave with zero initial
displacement and initial velocity $`f(s,\cdot)`. At time $`t` that contribution
has evolved for $`t-s`. Duhamel's principle integrates these delayed responses
over $`0\leq s\leq t`, using the homogeneous formulas.

:::theorem "hyperbolic.wave.duhamel_solution" (parent := "hyperbolic.classical_wave") (lean := "WaveEquation.exists_contDiff_forcedWave_zeroCauchyData") (uses := "hyperbolic.wave.operator, hyperbolic.wave.odd_dimensional_solution, hyperbolic.wave.even_dimensional_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§2.4.2"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\geq1`, put $`m=\lfloor n/2\rfloor+1`, and let
$`f:\mathbb R^{n+1}\to\mathbb R` be $`C^m` within the closed forward
halfspace $`\{(t,x):t\geq0\}`. Then there exists
$`u\in C^2(\mathbb R^{n+1})` satisfying

$$`
u_{tt}-\Delta_xu=f\quad(t>0),\qquad u(0,x)=u_t(0,x)=0.
`

For every $`x\in\mathbb R^n`, both initial traces hold jointly in space and
time:

$$`
\lim_{(s,y)\to(0,x)}u(s,y)=0,\qquad
\lim_{(s,y)\to(0,x)}u_t(s,y)=0.
`

The $`C^2` field is defined on all signed times. The forcing regularity
assumption is only within the forward halfspace; no support or growth
condition is imposed.
:::

:::proof "hyperbolic.wave.duhamel_solution"
In dimension one, integrate the retarded d'Alembert formula. In higher
dimensions, write $`n=2k+2` or $`n=2k+3`; in either case $`m=k+2` and use
the corresponding mean formula. For nonnegative time, the witness has the form

$$`u(t,x)=\int_0^t W_s(t-s,x)\,ds,`

where $`W_s` is the corresponding homogeneous wave
with displacement zero and velocity $`f(s,\cdot)`. Clipping the forcing
index to $`\max(0,s)` extends the construction to signed times. The retarded
integral regularity and equation theorems give joint $`C^2` regularity and
the forced residual. The collapsed integral and its first derivative give
zero Cauchy data; continuity of the field and its time derivative gives
the two joint traces.
:::
