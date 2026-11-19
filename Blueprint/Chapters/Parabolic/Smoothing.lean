/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.MaximumPrinciples
import Blueprint.Commands.Figures
import PDE.Parabolic.Heat.BackwardUniqueness.Energy
import PDE.Parabolic.Heat.BackwardUniqueness.Classical
import PDE.Parabolic.Heat.Interior.Smoothness
import PDE.Parabolic.Heat.Interior.Estimates.Local

/-!
# Energy, backward uniqueness, and interior smoothness

The energy identities for heat flow with zero lateral values, the
log-convexity inequality, backward uniqueness on bounded cylinders, interior
smoothness of classical solutions, and the local derivative estimates.
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
#doc (Manual) "Energy and Smoothing" =>

The maximum principle compares values. A second family of arguments measures
the solution in $`L^2`. On a bounded domain with zero lateral values, the
energy $`E(t)=\int_\Omega u(x,t)^2\,dx` can only decrease, and the rate at
which it decreases is the Dirichlet energy. Differentiating once more and
applying the Cauchy–Schwarz inequality shows that $`\log E` is convex. A
convex function that is finite at the start cannot reach $`-\infty` in finite
time unless it was $`-\infty` all along, and this is backward uniqueness: a
heat solution that vanishes at a later time vanished at every earlier time.
The argument follows §2.3.4 of {Informal.citet "evans-2010"}[].

Throughout, $`\Omega\subset\mathbb R^n`, $`n\geq1`, is a bounded open set with
a $`C^1` graph boundary, and $`u` is $`C^2` up to the boundary of the
cylinder $`\Omega\times(a,b)` and continuous on its closure. The boundary
regularity is used only for integration by parts in space.

:::theorem "parabolic.energy_decay" (parent := "parabolic.classical") (lean := "HeatEquation.hasDerivAt_squareEnergy_of_zero_boundary, HeatEquation.hasDerivAt_dirichletEnergy_of_zero_boundary") (uses := "parabolic.heat_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§2.3.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`u` solve $`u_t-\Delta u=0` in $`\Omega\times(a,b)` and vanish on
$`\partial\Omega\times[a,b]`. Then for every $`t\in(a,b)`,

$$`\frac{d}{dt}\int_\Omega u^2\,dx=-2\int_\Omega|\nabla u|^2\,dx,
\qquad
\frac{d}{dt}\int_\Omega|\nabla u|^2\,dx=-2\int_\Omega u_t^2\,dx.`
:::

:::proof "parabolic.energy_decay" (uses := "parabolic.heat_operator")
Differentiate under the integral and replace $`u_t` by $`\Delta u`. Green's
first identity with the zero boundary values turns
$`2\int_\Omega u\,\Delta u` into $`-2\int_\Omega|\nabla u|^2`. For the second
identity, the time derivative of $`|\nabla u|^2` is $`2\nabla u\cdot\nabla u_t`,
and integrating by parts gives $`-2\int_\Omega\Delta u\,u_t`, which is
$`-2\int_\Omega u_t^2` by the equation. The boundary term vanishes because
$`u_t=0` on the lateral boundary, which follows from $`u=0` there for all
times. The proof commutes the mixed second derivatives of $`u`; it never
differentiates $`\Delta u` in time, so $`C^2` regularity is enough.
:::

The first identity gives the familiar energy decay. The second shows that
the Dirichlet energy decreases as well, so the rate of decay slows down.
Log-convexity of the energy makes this precise.

:::theorem "parabolic.energy_log_convexity" (parent := "parabolic.classical") (lean := "HeatEquation.squareEnergy_derivative_sq_le") (uses := "parabolic.energy_decay")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§2.3.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Under the hypotheses of {bpref "parabolic.energy_decay"}[], write
$`E(t)=\int_\Omega u^2\,dx`. Then $`E'(t)=-2\int_\Omega|\nabla u|^2` and
$`E''(t)=4\int_\Omega u_t^2` satisfy

$$`\Bigl(-2\int_\Omega|\nabla u|^2\,dx\Bigr)^2
\leq\int_\Omega u^2\,dx\cdot4\int_\Omega u_t^2\,dx,
\qquad\text{that is,}\qquad (E')^2\leq E\,E''.`
:::

:::proof "parabolic.energy_log_convexity" (uses := "parabolic.energy_decay")
By the first energy identity, $`E'=2\int_\Omega u\,u_t`. The Cauchy–Schwarz
inequality gives
$`(E')^2\leq4\int_\Omega u^2\int_\Omega u_t^2`, and the right side is
$`E\,E''` by the second identity.
:::

Where $`E>0` the inequality says $`(\log E)''=(EE''-(E')^2)/E^2\geq0`. The
quotient $`-E'/2E=\int|\nabla u|^2/\int u^2` is the frequency of the solution.
Log-convexity says the frequency never increases: a solution with its energy
in high modes loses them first and settles toward the lowest mode it contains.

{leanpde_figure "heat-log-convexity"}

:::theorem "parabolic.backward_uniqueness" (parent := "parabolic.classical") (lean := "HeatEquation.eq_on_closedCylinder_of_terminal_eq, HeatEquation.eq_zero_on_closedCylinder_of_terminal_eq_zero") (uses := "parabolic.energy_log_convexity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§2.3.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`a<b`, and let $`u` and $`v` solve $`u_t-\Delta u=0=v_t-\Delta v` in
$`\Omega\times(a,b)`. If $`u=v` on $`\partial\Omega\times[a,b]` and
$`u(\cdot,b)=v(\cdot,b)` in $`\Omega`, then $`u=v` on
$`\overline\Omega\times[a,b]`. In particular a solution with zero lateral
values that vanishes at time $`b` vanishes on the whole closed cylinder.
:::

:::proof "parabolic.backward_uniqueness" (uses := "parabolic.energy_log_convexity")
The difference $`w=u-v` satisfies the hypotheses of
{bpref "parabolic.energy_decay"}[] with zero lateral values, so it suffices to
treat $`w`. Its energy $`E` is continuous on $`[a,b]`, nonnegative, has
$`E''\geq0`, satisfies $`(E')^2\leq EE''`, and $`E(b)=0`. For $`\varepsilon>0`
the function $`\log(E+\varepsilon)` is convex, because
$`(E+\varepsilon)E''-(E')^2\geq EE''-(E')^2\geq0`. Convexity on $`[a,b]` gives

$$`E(t)+\varepsilon\leq(E(a)+\varepsilon)^{(b-t)/(b-a)}(E(b)+\varepsilon)^{(t-a)/(b-a)},`

and letting $`\varepsilon\to0` gives $`E(t)=0` for $`a<t<b`. Continuity of $`w`
then gives $`w=0` on each slice and on the closure.

The regularization by $`\varepsilon` avoids a case analysis on the set where
$`E>0`, and it is where the sign condition $`E''\geq0` is used. The
statement holds on any interval $`[a,b]` and for every bounded open
$`\Omega` with $`C^1` graph boundary.
:::

Forward uniqueness also follows from energy decay, since $`E(0)=0` and
$`E'\leq0` force $`E=0`, or from the maximum principle in {bpref "parabolic.classical_uniqueness"}[]. Backward uniqueness
requires a different argument: the forward maximum principle takes data
from the parabolic boundary, which excludes the terminal face.

The second theme is smoothing. A solution with only two spatial derivatives
and one time derivative is automatically smooth in the interior, and every
derivative is controlled by the $`L^1` norm of the solution on a slightly
larger cylinder. This is Theorem 8 and Theorem 9 of Evans's §2.3.3.

:::theorem "parabolic.interior_smoothness" (parent := "parabolic.classical") (lean := "HeatEquation.contDiffOn_of_heat_equation, HeatEquation.exists_smooth_extension_of_heat_equation") (uses := "parabolic.initial_convolution, parabolic.duhamel_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§2.3.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subset\mathbb R^n` be open and $`T>0`. Suppose $`u` is
continuous on $`\Omega\times(0,T]`, has continuous first and second spatial
derivatives there and a continuous time derivative taken within $`(0,T]`, and
solves $`u_t-\Delta u=0` on $`\Omega\times(0,T]`. Then $`u` is $`C^\infty` on
$`\Omega\times(0,T]`. Near every point of this set, including points with
$`t=T`, $`u` agrees with a function that is $`C^\infty` on an open
neighborhood of the point.
:::

:::proof "parabolic.interior_smoothness" (uses := "parabolic.initial_convolution, parabolic.duhamel_solution")
Fix $`(x_0,t_0)` and a cutoff $`\chi\in C_c^\infty(\Omega)` equal to $`1` near
$`x_0`. Restart the clock at $`a=t_0/2`. The product $`\chi u` solves the
heat equation with forcing $`R`, which involves $`\nabla\chi` and
$`\Delta\chi` and is therefore supported away from $`x_0`. Duhamel's
principle represents $`\chi u` on $`[a,T]` as the Gaussian convolution of
$`\chi u(\cdot,a)` at age $`t-a` plus the integral in time of the Gaussian
convolutions of $`R(\cdot,s)` at age $`t-s`. The first term is smooth because
its age is bounded away from zero near $`t_0`. In the second term, the kernel is
evaluated only at spatial offsets bounded away from zero, where
$`\Gamma_n(x,t)` extended by $`0` for $`t\leq0` is smooth. Hence the second term is
smooth in $`(x,t)` near $`(x_0,t_0)`, also when $`t_0=T`.

As in Evans, the proof localizes with a cutoff, writes the result as a
heat-kernel integral, and integrates by parts to remove $`\nabla u`. It keeps
the terminal time: the extension is smooth on an open set around
$`(x_0,T)`, while $`u` itself is only asserted smooth within
$`\Omega\times(0,T]`. No mixed derivative and no second time derivative are
assumed.
:::

The parabolic cylinder of radius $`r` ending at $`(x,t)` is
$`C(x,t;r)=\overline B(x,r)\times[t-r^2,t]`. Its spatial radius is $`r` and
its height is $`r^2`, matching the scaling $`u(x,t)\mapsto u(\lambda x,\lambda^2t)`
of the heat equation. That scaling fixes the power of $`r` in the estimate: each
spatial derivative costs $`r^{-1}`, each time derivative costs $`r^{-2}`, and
the $`L^1` norm over a cylinder of volume comparable to $`r^{n+2}` costs
$`r^{-n-2}`.

:::theorem "parabolic.local_derivative_estimate" (parent := "parabolic.classical") (lean := "HeatEquation.exists_local_derivative_bound") (uses := "parabolic.interior_smoothness")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§2.3.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For all $`n,k,l\geq0` there is a constant $`C=C_{n,k,l}>0` with the following
property. Let $`u` satisfy the hypotheses of
{bpref "parabolic.interior_smoothness"}[] on $`\Omega\times(0,T]`, and let
$`r>0` with $`C(x,t;r)\subset\Omega\times(0,T]`. Then $`u` is integrable on
$`C(x,t;r)`, the norm of the mixed derivative $`D_x^kD_t^lu` attains its
maximum on $`C(x,t;r/2)`, and

$$`\max_{C(x,t;r/2)}\bigl\|D_x^kD_t^lu\bigr\|
\leq\frac{C}{r^{k+2l+n+2}}\int_{C(x,t;r)}|u|\,dy\,ds.`

The derivatives are taken within $`\Omega\times(0,T]`, so the cylinder may
touch the terminal time, and the norm is the operator norm of the
$`k`-linear spatial derivative.
:::

:::proof "parabolic.local_derivative_estimate" (uses := "parabolic.interior_smoothness")
By translation and parabolic scaling, it suffices to treat the
unit cylinder ending at $`(0,0)`. There fixed cutoffs in space and time,
equal to $`1` near the half cylinder, localize $`u`. The cutoff residual
contains $`\nabla u`; integrating by parts in space moves those derivatives
onto a single smooth compactly supported kernel that agrees with the Gaussian
on the support of the residual. The representation then expresses $`u` near
the half cylinder as an integral of $`u` alone against that kernel and its
derivatives, and differentiating under the integral bounds
$`D_x^kD_t^lu` by a constant times $`\int|u|`. The constant depends only on the
kernel, hence only on $`n`, $`k` and $`l`. Scaling back produces the factor
$`r^{-(k+2l+n+2)}`. This is Evans's proof, with the fixed kernel as the
representation formula.
:::
