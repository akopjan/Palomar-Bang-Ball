module

public import BallPlank.Planks
public import BallPlank.ShiftedPlanks
public import BallPlank.BallPlankFinal

public section

/-!
# Ball's Plank Theorem

Formalization in Lean 4 of the paper:
**"A Short Proof of Ball's Plank Theorem"**
by Arseniy Akopyan and Alexander Polyanskii (2026), [arXiv:2609.36163](https://arxiv.org/abs/2609.36163).
Formalized by Arseniy Akopyan with the assistance of ChatGPT, Aristotle (Harmonic), and Gemini.

This library provides:
* `Planks`: The core variational argument (minimizer of `F(Y) = ∑ pᵢ²`, rotation identity
  `pᵢ³ ℓᵢ(yⱼ) = pⱼ³ ℓⱼ(yᵢ)`, and sign choice maximizing `Q(ε)`).
* `ShiftedPlanks`: Affine version with shifts `cᵢ`.
* `PlankProblem`: The geometric reductions and main theorems:
  - `PlankProblem.ball_plank_theorem`: Ball's theorem for centrally symmetric convex bodies.
  - `PlankProblem.core_theorem`: Planks through an orthonormal basis do not cover `√n · B₂ⁿ`.
  - `PlankProblem.davenport_conjecture`: Davenport's problem for centrally symmetric bodies.
  - `PlankProblem.BangPlankConjecture`: Bang's open conjecture for general convex bodies.
-/
