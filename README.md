# Projected Gradient Descent in Isabelle/HOL

This repository is a work-in-progress Isabelle/HOL formalization project for first-order methods in smooth convex optimization, with a focus on projected gradient descent.

The long-term goal is to develop a reusable formal library for convex differentiable optimization, Euclidean projection, smoothness inequalities, gradient descent, and projected gradient descent.  The project is designed with an AFP-style structure in mind: definitions should be reusable, theorem statements should be modular, and the development should avoid unnecessary commitment to overly concrete finite-dimensional coordinates whenever the Isabelle/HOL-Analysis library already provides a more general abstraction.

## Project overview

The project aims to formalize a sequence of standard results from convex optimization:

1. gradient preliminaries for real inner product spaces;
2. first-order optimality certificates for convex differentiable functions;
3. smoothness inequalities and the descent lemma;
4. convergence guarantees for gradient descent;
5. Euclidean projection and projection variational inequalities;
6. projected gradient descent for smooth convex minimization;
7. examples illustrating the framework.

The intended final theorem family is centered around projected gradient descent for a smooth convex function over a closed convex feasible set.

Mathematically, the central algorithm is

```text
x_{k+1} = P_C (x_k - \<alpha> \<nabla>f(x_k)),
```

where `C` is a nonempty closed convex set, `P_C` is Euclidean projection onto `C`, `f` is a convex differentiable function with Lipschitz-continuous gradient, and `\<alpha>` is a suitable step size.

## Current status

The current development starts with a theory file:

```text
Gradient_Preliminaries.thy
```

This file introduces a lightweight gradient interface for real-valued functions on real inner product spaces.  It packages Isabelle/HOL's Fréchet derivative infrastructure into optimization-oriented definitions and lemmas, including:

- pointwise gradients;
- gradients on sets;
- uniqueness of gradients;
- elementary gradient rules;
- affine-line restrictions;
- directional derivatives along lines;
- basic norm and inner-product algebra used in convergence proofs.

The next planned theory is:

```text
Convex_Differentiable.thy
```

This file will introduce the first layer of convex optimization language:

- global minimizers on feasible sets;
- first-order variational inequalities;
- supporting affine lower bounds;
- convex differentiable functions with named gradient fields;
- the connection between convex differentiability and first-order lower bounds.

## Planned theory structure

The intended final structure is:

```text
Projected_Gradient_Descent/
  ROOT
  Gradient_Preliminaries.thy
  Convex_Differentiable.thy
  Smooth_Convex.thy
  Gradient_Descent.thy
  Projection_Optimization.thy
  Projected_Gradient_Descent.thy
  Examples.thy
```


A possible description of each file is as follows.

### `Gradient_Preliminaries.thy`

This file provides the basic gradient language used throughout the project.

Main planned components:

- `has_gradient f x g`;
- `gradient f x`;
- `has_gradient_on f S G`;
- elementary gradient rules;
- restriction of a multivariate function to an affine line;
- directional derivative along a line;
- norm-square expansion lemmas.

This theory should remain relatively general and should not depend on convexity.

### `Convex_Differentiable.thy`

This file develops the first-order language of convex differentiable optimization.

Main planned components:

- `global_min_on S f x`;
- `first_order_condition_at S g x`;
- `supports_at S f x g`;
- `supports_on S f G`;
- `gradient_lower_bound_on S f G`;
- `convex_differentiable_on S f G`;
- a locale for convex differentiable functions.

The key theorem planned for this file is the first-order lower bound for differentiable convex functions:

```text
convex_on S f
has_gradient f x g
x \<in> S
y \<in> S
\<Longrightarrow> f x + inner g (y - x) \<le> f y
```

This theorem is the bridge between convex analysis and optimization certificates.

### `Smooth_Convex.thy`

This file will introduce smoothness assumptions and the descent lemma.

Main planned components:

- Lipschitz gradient assumptions;
- smooth upper bounds;
- descent lemma;
- inequalities of the form

```text
f y \<le> f x + inner (\<nabla>f x) (y - x) + (L / 2) * norm (y - x)^2.
```

The descent lemma is expected to be one of the main technical foundations for both gradient descent and projected gradient descent.

### `Gradient_Descent.thy`

This file will formalize unconstrained gradient descent.

Main planned components:

- the gradient descent update;
- objective decrease under suitable step sizes;
- one-step progress inequalities;
- telescoping arguments;
- sublinear convergence for smooth convex functions.

The standard algorithm is

```text
x_{k+1} = x_k - \<alpha> \<nabla>f(x_k).
```

A target convergence statement is an `O(1/k)` objective-value guarantee under convexity and smoothness.

### `Projection_Optimization.thy`

This file will connect Isabelle/HOL's closest-point projection infrastructure with optimization language.

Main planned components:

- projection onto a nonempty closed convex set;
- feasibility of projected points;
- projection variational inequality;
- nonexpansiveness or related projection inequalities;
- fixed-point characterizations of constrained first-order optimality.

The main optimization interpretation is that

```text
x = P_C (x - \<alpha> g)
```

is closely related to the variational inequality

```text
\<forall>y\<in>C. 0 \<le> inner g (y - x).
```

### `Projected_Gradient_Descent.thy`

This file will formalize projected gradient descent.

Main planned components:

- projected gradient descent step;
- feasibility preservation;
- objective decrease;
- one-step progress inequality;
- convergence for smooth convex functions over a closed convex feasible set;
- fixed-point optimality results.

The main update is

```text
x_{k+1} = P_C (x_k - \<alpha> \<nabla>f(x_k)).
```

The main convergence goal is to prove a standard sublinear rate for projected gradient descent under smooth convex assumptions.

### `Examples.thy`

This file will contain small examples showing how the general framework can be instantiated.

Possible examples include:

- quadratic functions;
- affine functions;
- unconstrained minimization examples;
- simple constrained examples such as intervals, balls, or affine constraints, depending on what is convenient in Isabelle/HOL.

The examples are not intended to be the mathematical core of the project, but they should help demonstrate that the definitions are usable.

## Mathematical roadmap

The project is intended to proceed through the following stages.

### Stage 1: Gradient language

Build a stable interface around Fréchet derivatives for real-valued functions on real inner product spaces.

The main design principle is to avoid developing a separate derivative theory.  Instead, the project wraps Isabelle/HOL's existing derivative infrastructure in notation and lemmas that are closer to optimization practice.

### Stage 2: Convex differentiability

Develop the first-order optimality theory for differentiable convex functions.

The main mathematical result is the supporting-hyperplane inequality:

```text
f y \<ge> f x + inner (\<nabla>f x) (y - x).
```

This inequality will later be used to prove global optimality from first-order conditions.

### Stage 3: Smoothness

Introduce Lipschitz-gradient assumptions and prove the descent lemma.

The descent lemma is the basic inequality behind gradient descent:

```text
f (x - \<alpha> \<nabla>f x)
\<le> f x - \<alpha> * norm (\<nabla>f x)^2 + (L / 2) * \<alpha>^2 * norm (\<nabla>f x)^2.
```

For `0 < \<alpha> \<le> 1 / L`, this gives monotone decrease of the objective value.

### Stage 4: Unconstrained gradient descent

Formalize the standard gradient descent method and prove its basic convergence properties.

The intended proof strategy is based on:

- smoothness upper bounds;
- convexity lower bounds;
- norm-square identities;
- telescoping inequalities.

### Stage 5: Projection theory for optimization

Package Euclidean projection results in optimization-friendly form.

The key goal is to show that projection onto a closed convex set satisfies a variational inequality, which is the main tool behind projected gradient descent analysis.

### Stage 6: Projected gradient descent

Formalize projected gradient descent and prove convergence under smooth convex assumptions.

The main theorem should express that the iterates remain feasible and that the objective value converges toward the optimal value with a standard sublinear rate.

## Build instructions

This repository is intended to be built as an Isabelle session.

A minimal `ROOT` file should have the form:

```isabelle
session Projected_Gradient_Descent = "HOL-Analysis" +
  options [document = false]
  theories
    Gradient_Preliminaries
```

As the project grows, more theory files will be added:

```isabelle
session Projected_Gradient_Descent = "HOL-Analysis" +
  options [document = false]
  theories
    Gradient_Preliminaries
    Convex_Differentiable
    Smooth_Convex
    Gradient_Descent
    Projection_Optimization
    Projected_Gradient_Descent
    Examples
```

To build the session locally, run:

```bash
isabelle build -D .
```

## Development principles

This project follows several development principles.

First, the formalization should reuse Isabelle/HOL-Analysis whenever possible.  In particular, existing infrastructure for convexity, derivatives, norms, inner products, limits, and closest-point projection should be used rather than duplicated.

Second, definitions should be modular.  For example, the gradient language should be independent of convexity, and the convex differentiability theory should be independent of any particular algorithm.

Third, theorem statements should be close to standard mathematical optimization statements.  The goal is not only to prove isolated facts, but also to build a small reusable library for first-order convex optimization.

Fourth, the project should remain suitable for a possible AFP-style submission.  This means keeping imports controlled, avoiding unnecessary experimental material in the main session, and documenting the mathematical role of each theory file.

## Long-term goals

The final project should provide a formal foundation for projected gradient descent in Isabelle/HOL.

Possible extensions after the core development include:

- strongly convex convergence rates;
- proximal gradient methods;
- projected gradient mappings;
- normal cone formulations;
- KKT-style certificates for simple convex constraints;
- applications to quadratic minimization or least-squares problems.

These extensions are not part of the initial target.  The first goal is a clean and reusable formalization of smooth convex projected gradient descent.

## Repository status

This repository is currently under active development.