/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Symbolic.Calculus
import Blueprint.CodeExamples
import PDE.AutoDiff.Jet.Expression
import PDE.AutoDiff.Jet.Interval
import PDE.AutoDiff.Optimization
import PDE.AutoDiff.ResidualLoss

/-!
## Formal jets and residual losses

Formal multivariate jets, residual energies, sampled losses, and gradient steps.
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
#doc (Manual) "Formal Jets and Residual Losses" =>

:::group "symbolic.autodiff"
Formal jets and residual losses
:::

A residual loss is an ordinary real-valued function, differentiated with
the analytic Fréchet derivative. A formal jet instead stores coefficients;
identifying them with derivatives requires a separate semantic theorem.

*Residual losses are ordinary functions.*

:::definition "symbolic.residual_loss" (parent := "symbolic.autodiff") (lean := "PDE.AutoDiff.ResidualLoss.pointwiseEnergy, PDE.AutoDiff.ResidualLoss.sampledLoss")
A pointwise residual energy is the square of a `LinearPDE`'s totalized residual
expression. A sampled loss sums these energies over a finite list of points.
Interpreting this objective as a classical PDE loss requires a separate
regularity proof for the candidate field. Given a parameterized model
$`\theta \mapsto u_\theta`, its objective is the ordinary composition
$`\theta \mapsto \operatorname{sampledLoss}(u_\theta)`.
:::

A zero sampled loss can still miss the equation between sample points. For
the one-dimensional equation $`u'=0` on $`[0,1]`, choose an integer
$`N\geq1` and $`A>0`, and set

$$`
u(x)=\frac{A}{2\pi N}\bigl(1-\cos(2\pi Nx)\bigr),
\qquad r(x)=u'(x)=A\sin(2\pi Nx).
`

At every grid point $`x_j=j/N`, the residual vanishes, so the sampled
squared loss is zero. Between these points its magnitude reaches $`A`,
which can be arbitrarily large. The candidate is smooth and even has zero
values at both endpoints. A uniform residual enclosure would detect this
oscillation; sampling alone cannot. Converting such a uniform enclosure to
solution accuracy then needs a stability estimate in the relevant norm.

:::definition "symbolic.gradient_step" (parent := "symbolic.autodiff") (uses := "symbolic.residual_loss") (lean := "PDE.AutoDiff.Optimization.gradientDescentStep, PDE.AutoDiff.Optimization.adamStep")
For a differentiable objective $`f:E\to\mathbb R` on a real Hilbert space,
the gradient-descent map is

$$`x^+=x-\eta\,\nabla f(x).`

In Euclidean coordinates, the Adam-style map first sets $`g=\nabla f(x)` and computes

$$`\begin{aligned}
m^+&=\beta_1m+(1-\beta_1)g,\\
v^+&=\beta_2v+(1-\beta_2)(g\odot g),\\
x_i^+&=x_i-\eta\,\frac{m_i^+}{\sqrt{v_i^+}+\varepsilon}.
\end{aligned}`

Both are total update functions defined from the analytic gradient. An
analytic use of the Adam-style map must separately prove the sign and nonvanishing facts it
needs for $`\sqrt{v_i^+}+\varepsilon`.
:::

In applications, `sampledLoss` builds a real-valued objective from an
already defined PDE residual and a finite sample. A gradient step then has
the form

$$`\theta_{\mathrm{new}}
  =\theta-\eta\,\nabla_\theta L(\theta),`

with the analytic `gradient`, so a residual-loss theorem rests on no
automatic-differentiation compiler.

*Higher-order multivariate jets.*

The jet layer uses Mathlib's multivariate formal power series, so variables
may be indexed by an arbitrary type $`\iota` rather than only by `Fin n`.

:::definition "symbolic.taylor_jet" (parent := "symbolic.autodiff") (lean := "PDE.AutoDiff.Jet, PDE.AutoDiff.Jet.coefficient")
For a multi-index $`\alpha:\iota\to_0\mathbb N`, an order-$`N` jet is a
formal coefficient family $`J_\alpha`. When a separate semantic theorem
identifies these coefficients with derivatives, the normalization convention
is

$$`J_\alpha(f,x)=\frac{D^\alpha f(x)}{\alpha!}.`

Formal products use ordinary power-series convolution:

$$`(JK)_\alpha
  =\sum_{\beta+\gamma=\alpha}J_\beta K_\gamma.`

The order index controls finite extraction and finite formal composition.
The underlying representation is a full formal power series: coefficients
above the index may be nonzero, and the carrier itself contains no function,
base point, differentiability proof, or convergence theorem.
:::

:::definition "symbolic.first_order_jet_semantics" (parent := "symbolic.autodiff") (uses := "symbolic.taylor_jet, symbolic.partial_derivative_bridge") (lean := "PDE.AutoDiff.Jet.RepresentsFirstOrderAt")
For a Euclidean scalar function $`f:\mathbb R^n\to\mathbb R`, the proposition
that a formal jet $`J` represents $`f` to first order at $`x` records

$$`\begin{aligned}
&f\text{ is differentiable throughout a neighborhood of }x,\\
&J_0=f(x),\\
&J_{e_i}=\partial_i f(x)\qquad(i=1,\ldots,n).
\end{aligned}`

The function, point, and jet are parameters of the proposition. Only the
value and the first coefficients are constrained.
:::

:::definition "symbolic.expression_jet" (parent := "symbolic.autodiff") (uses := "symbolic.taylor_jet, symbolic.first_order_jet_semantics") (lean := "CAS.Verified.Expr.toJet, CAS.Verified.Expr.toJet_representsFirstOrderAt")
The expression compiler maps every constructor of the verified real
expression language to an arbitrary-order multivariate formal jet. Arithmetic
nodes use formal power-series algebra. A unary elementary function is lifted
by finite formal composition with coefficients computed from normalized
symbolic derivatives of the corresponding one-variable primitive.

Under sufficient differentiability and Taylor-remainder hypotheses, this is the familiar finite
composition formula

$$`\sum_{k=0}^{N}\frac{g^{(k)}(f(x))}{k!}
    \bigl(f(x+h)-f(x)\bigr)^k.`

Compilation is algebraically total, but analytic claims retain the original
`ValidAt` conditions. In particular, division requires a nonzero denominator,
the real logarithm requires a nonzero argument, and the classical square-root
rule requires a positive argument.
:::

For every positive order and Euclidean expression valid at the base point,
the {bpref "symbolic.expression_jet"}[compiled jet] agrees with the
function value and all first-coordinate derivatives, and the function is
differentiable on a neighborhood. Higher coefficients remain formal
power-series coefficients unless another theorem identifies their analytic
meaning. For example, the exponential jet has fourth coefficient

$$`[h_x^4]\,e^{h_x}=\frac1{4!}=\frac1{24}.`

This is a coefficient identity; it does not assert a general higher-order
Taylor remainder theorem.

:::definition "symbolic.interval_jet" (parent := "symbolic.autodiff") (uses := "symbolic.taylor_jet, symbolic.first_order_jet_semantics") (lean := "PDE.AutoDiff.IntervalJet, PDE.AutoDiff.IntervalJet.Encloses, PDE.AutoDiff.IntervalJet.valueAndGradient_mem_of_representsFirstOrderAt")
An interval jet assigns a rational interval to each formal multivariate
coefficient. `Encloses F J` means that every coefficient through the declared
order lies in its interval:

$$`\deg\alpha\le N
  \quad\Longrightarrow\quad
  J_\alpha\in F_\alpha.`

The interval operations are explicit rather than typeclass ring operations.
This is necessary because interval multiplication is sound but not
distributive.
:::

Constants, coordinate seeding, addition, subtraction, negation, and
power-series convolution preserve coefficient enclosures. At positive order,
extracting the constant and first coefficients gives interval values and an
output-first interval Jacobian for a vector residual. These intervals contain
the corresponding exact formal coefficients. For a scalar jet that
{bpref "symbolic.first_order_jet_semantics"}[represents the function to first order],
they also enclose its value and partial derivatives. These guarantees hold
at a single input point.

These pointwise enclosures can supply data for validated root finding. The
{bpref "symbolic.krawczyk_unique_zero"}[Krawczyk certificate] proves existence
and uniqueness of a zero in a closed ball from Jacobian enclosures that hold
throughout the ball, together with self-mapping and strict contraction
inequalities; a jet certificate supplies the corresponding data at one point.

*Relationship to computer-assisted PDE proofs.*

Gómez-Serrano's survey of computer-assisted proofs in PDE describes a pipeline
that combines interval arithmetic, high-order automatic differentiation,
rigorous quadrature, singular-integral decompositions, validated root finding,
and problem-specific analytic estimates. PDEAtlas has checked foundations for
several of these layers:

* exact rational interval arithmetic and scalar elementary-function
  enclosures;
* exact symbolic differentiation with explicit analytic domains;
* arbitrary-index, arbitrary-order exact multivariate jets;
* polynomial interval-jet algebra and certified residual/Jacobian extraction;
* closed-ball Krawczyk certificates with interval-matrix residual bounds;
* Taylor models and derivative-bound automation, chiefly in one real variable;
* rigorous one-dimensional Simpson and Gauss–Legendre quadrature; and
* abstract compact-operator, Fredholm, Hilbert-basis, and spectral theory.

The survey's Muskat and SQG results further use principal-value
singular-integral splitting, multidimensional interval-Newton solvers,
computer-validated spectral gaps, and a quantitative Crandall–Rabinowitz
bifurcation argument.
