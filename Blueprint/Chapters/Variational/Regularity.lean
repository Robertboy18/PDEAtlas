/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

import Blueprint.Bibliography
import PDE.CalculusOfVariations.LocalMinimizer.Analytic
import PDE.CalculusOfVariations.LocalMinimizer.Holder

/-!
# Regularity of local minimizers

Local minimizers of uniformly convex gradient energies: Hölder continuous
gradients, smoothness, and real analyticity for analytic densities.
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
#doc (Manual) "Regularity of Local Minimizers" =>

:::group "methods.minimizer_regularity"
Regularity of local minimizers of gradient energies
:::

The direct method produces a minimizer in a Sobolev space, and the first
variation makes it a weak solution of its Euler–Lagrange equation. How regular
is it? For an energy

$$`
I(u)=\int_\Omega F(\nabla u)\,dx,
\qquad
\theta|\xi|^2\leq D^2F(p)[\xi,\xi]\leq\Lambda|\xi|^2,\quad\theta>0,
`

the answer is: as regular as the density allows. Evans treats the first steps
in Section 8.3 {Informal.citet "evans-2010"}[]. The main step, Hölder
continuity of the first derivatives, is the theorem of De Giorgi and Nash
{Informal.citet "de-giorgi-1957"}[] {Informal.citet "nash-1958"}[].
Analyticity of sufficiently regular solutions goes back to Bernstein, in two
variables {Informal.citet "bernstein-1904"}[]. Later proofs cover any dimension
and systems, among them Morrey's for nonlinear elliptic systems
{Informal.citet "morrey-1958"}[].

The statements below hold in every dimension and on every open set. Nothing
is assumed at the boundary, and the minimizer is only locally in
$`W^{1,2}`.

:::definition "methods.minimizer_regularity.local_minimizer" (parent := "methods.minimizer_regularity") (lean := "PDE.CalculusOfVariations.IsLocalMinimizerOn")
A function $`u` is a local minimizer of $`\int F(\nabla u)` on $`\Omega` if, on
every open set $`V` with compact closure in $`\Omega`, adding a smooth function
with compact support in $`V` does not lower the energy over $`V`:

$$`
\int_V F(\nabla u)\,dx\leq\int_V F(\nabla u+\nabla\varphi)\,dx
\qquad\text{for every }\varphi\in C_c^\infty(V).
`

The condition is stated for the $`W^{1,2}(V)` representatives of $`u`. The
regularity theorems add the hypothesis that $`u` is locally in $`W^{1,2}`.
:::

The perturbation may be large, and smooth functions with compact support are
the smallest class of competitors in use. So among the notions that compare
$`u` with all perturbations in a class, this is the weakest. For the densities
above, a minimizer with prescribed boundary values on a bounded open set is a
local minimizer, and so is every affine function.

:::theorem "methods.minimizer_regularity.holder_gradient" (parent := "methods.minimizer_regularity") (lean := "PDE.CalculusOfVariations.exists_holder_gradient_of_isLocalMinimizerOn") (uses := "methods.minimizer_regularity.local_minimizer")
For every dimension $`n` and all constants $`\theta>0` and $`\Lambda` there is
an exponent $`\gamma\in(0,1)` with the following property. Let
$`\Omega\subseteq\mathbb R^n` be open, let $`F` be $`C^2` with the two
bounds above, and let $`u\in W^{1,2}_{\mathrm{loc}}(\Omega)` be a local
minimizer. Then $`u` has a representative in $`C^1(\Omega)` whose gradient is
Hölder continuous with exponent $`\gamma` on a ball around each point.
:::

:::proof "methods.minimizer_regularity.holder_gradient"
On a small ball the minimizer is a weak solution of
$`\operatorname{div}(\nabla F(\nabla u))=0`. Difference quotients give second
weak derivatives, and each first derivative solves a linear equation whose
coefficients $`D^2F(\nabla u)` are bounded, elliptic and merely measurable.
The theorem of De Giorgi and Nash makes it Hölder continuous. The
representatives on balls agree on overlaps and glue.
:::

:::theorem "methods.minimizer_regularity.smooth" (parent := "methods.minimizer_regularity") (lean := "PDE.CalculusOfVariations.exists_smooth_of_isLocalMinimizerOn") (uses := "methods.minimizer_regularity.local_minimizer")
Let $`\Omega\subseteq\mathbb R^n` be open and let $`F` be $`C^\infty` with the
two bounds. Every local minimizer $`u\in W^{1,2}_{\mathrm{loc}}(\Omega)` has
a representative $`v\in C^\infty(\Omega)`, and

$$`
\operatorname{div}\bigl(\nabla F(\nabla v)\bigr)=0
\qquad\text{at every point of }\Omega.
`
:::

:::proof "methods.minimizer_regularity.smooth" (uses := "methods.minimizer_regularity.holder_gradient")
Once the gradient is Hölder continuous, so are the coefficients
$`D^2F(\nabla u)` of the linearized equation. Schauder estimates then give
one more derivative of $`u` for each further derivative of $`F`.
:::

:::theorem "methods.minimizer_regularity.analytic" (parent := "methods.minimizer_regularity") (lean := "PDE.CalculusOfVariations.exists_analytic_of_isLocalMinimizerOn, PDE.CalculusOfVariations.isLocalMinimizerOn_iff_exists_analytic") (uses := "methods.minimizer_regularity.local_minimizer")
Let $`\Omega\subseteq\mathbb R^n` be open and let $`F` be real-analytic on
$`\mathbb R^n` with the two bounds. Every local minimizer
$`u\in W^{1,2}_{\mathrm{loc}}(\Omega)` has a representative that is
real-analytic on $`\Omega` and solves
$`\operatorname{div}(\nabla F(\nabla v))=0` there. Conversely, a function with
such a representative is locally in $`W^{1,2}` and is a local minimizer.
:::

:::proof "methods.minimizer_regularity.analytic" (uses := "methods.minimizer_regularity.smooth, methods.minimizer_regularity.analytic_solutions")
The smooth representative of the previous theorem solves the Euler–Lagrange
equation at every point, so the next theorem applies to it. The converse holds
because $`F` is convex: a classical solution minimizes.
:::

A continuous local minimizer is its own representative, so it is analytic as
it stands. The step from smooth to analytic does not use minimality. It is a
statement about smooth solutions of the equation.

:::theorem "methods.minimizer_regularity.analytic_solutions" (parent := "methods.minimizer_regularity") (lean := "PDE.Elliptic.Regularity.Analytic.analyticOnNhd_of_gradientDensity, PDE.Elliptic.Regularity.Analytic.analyticOnNhd_of_autonomous_system")
Let $`u` be smooth on an open set $`\Omega\subseteq\mathbb R^n` with
$`\operatorname{div}(\nabla F(\nabla u))=0` there. If $`F` is real-analytic at
the gradients $`\nabla u(x)`, $`x\in\Omega`, and $`D^2F` is positive definite
at these gradients, then $`u` is real-analytic on $`\Omega`. More generally, a
smooth solution $`v=(v_l)` of a system

$$`
\sum_i\partial_i\Bigl(\sum_j a_{ij}(v)\,\partial_jv_l-f_{li}(v)\Bigr)=0
`

is real-analytic when $`a_{ij}` and $`f_{li}` are real-analytic at the values
of $`v` and the matrix $`a(v(x))` is positive definite at every point.
:::

:::proof "methods.minimizer_regularity.analytic_solutions"
The gradient of $`u` solves a system of the second kind with
$`a_{ij}=\partial_j\partial_iF`. For such a system we show
$`|D^iv|\leq i!\,MK^i` near each point, which makes the Taylor series
converge. Fix a ball with weight $`\eta(x)=R^2-|x-x_0|^2` and consider
$`\eta^{2j}|D^jv|^2+\mu\,\eta^{2j-2}|D^{j-1}v|^2`. At an interior maximum
the operator with coefficients frozen at that point is nonpositive on it,
while a Bernstein-type inequality bounds the operator from below by the
derivatives of order $`j+1` and $`j`. The derivatives of the equation are
estimated by the Leibniz rule and a majorant form of the chain rule, with a
weight on the Taylor coefficients that is closed under convolution. The result
is a bound that improves itself: if the weighted derivatives are at most
$`2M` times the target, they are at most $`M` times the target. Since finitely
many derivatives are bounded on the closed ball, this gives the bounds for all
orders with one pair of constants. The plan, weighted derivatives and a
recursion that absorbs the top order, follows Blatt
{Informal.citet "blatt-2024"}[], with sup norms and the maximum principle in
place of his $`L^2` estimates.
:::

Armstrong and Kempe formalized the De Giorgi–Nash–Moser theory for linear
equations with bounded measurable coefficients in Lean
{Informal.citet "armstrong-kempe-2026"}[]. The theorems here concern
minimizers of nonlinear energies and use the library's own form of the
De Giorgi step.
