# A Short Proof of Ball's Plank Theorem

A formalization in Lean 4 of the paper:
> **A Short Proof of Ball's Plank Theorem**  
> Arseniy Akopyan and Alexander Polyanskii (2026)  
> [arXiv:2609.36163 [math.MG]](https://arxiv.org/abs/2609.36163)

## Overview

In 1951, Thøger Bang conjectured that if a convex body $K \subset \mathbb{R}^d$ is covered by finitely many planks, the sum of their relative widths with respect to $K$ is at least 1. In 1991, Keith Ball proved Bang's conjecture for all **centrally symmetric** convex bodies. Bang's general conjecture remains open.

Akopyan and Polyanskii give a new, short variational proof of Ball's theorem.

The core theorem also yields a short proof of **Davenport's problem** for centrally symmetric convex bodies:
for a symmetric convex body $K$ and $n$ hyperplanes in a Euclidean space, there is a homothet $K/(n+1)$ inside $K$ whose interior is disjoint from all of the hyperplanes. 

This project was formalized by **Arseniy Akopyan** with the assistance of **ChatGPT**, **Aristotle** (Harmonic), and **Gemini**.

* Paper: Arseniy Akopyan, Alexander Polyanskii, *A short proof of Ball's plank theorem*, [arXiv:2609.36163](https://arxiv.org/abs/2609.36163) [math.MG] (2026).

---

## Formalized Results

All proofs are machine-checked in **Lean 4.35.0-rc2** with **Mathlib**, with **zero `sorry`s**, and rely solely on the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

* **`PlankProblem.ball_plank_theorem`** (`Solution.lean`, `BallPlank/BallPlankFinal.lean`):  
  Ball's Plank Theorem for centrally symmetric convex bodies: if $K \subseteq \mathbb{R}^n$ is a centrally symmetric convex body covered by finitely many planks $P_i$, then $\sum_i \mathrm{relativeWidth}(K, P_i) \ge 1$.

* **`PlankProblem.core_theorem`** (`Solution.lean`, `BallPlank/BallPlankFinal.lean`):  
  The core variational theorem for shifted planks through an orthonormal basis.

* **`PlankProblem.davenport_conjecture`** (`Solution.lean`, `BallPlank/BallPlankFinal.lean`):  
  Davenport's problem: existence of a homothetic copy $K/(n+1) \subseteq K$ whose interior is disjoint from $n$ given hyperplanes.

* **`PlankProblem.BangPlankConjecture`** (`Challenge.lean`, `BallPlank/BallPlankFinal.lean`):  
  Bang's affine plank conjecture for general convex bodies, stated as an open `Prop` definition.

---

## Repository Structure

* **`Challenge.lean`**: The small (< 150 lines), human-auditable specification surface. Contains definitions and the headline theorem statements with `sorry`.
* **`Solution.lean`**: The proved solution module re-exporting the fully proved theorems.
* **`comparator.json`**: Comparator configuration specifying the challenge and solution modules, compared theorems, and permitted axioms.
* **`formalization.yaml`**: Standard formalization metadata (v0.4) detailing authorship, classification, sources, automation, review, and alignment.
* **`BallPlank.lean`**: Root library module.
* **`BallPlank/`**: Complete underlying proof development:
  * `Planks.lean`: Variational minimization, rotation identity, and sign vector optimization.
  * `ShiftedPlanks.lean`: Affine extension with shifts.
  * `BallPlankFinal.lean`: Geometric reductions to crosspolytopes and the main theorems.
* **`lakefile.toml`**: Lake build configuration pinned to Lean 4.35.0-rc2 and Mathlib.
* **`lean-toolchain`**: Pinned to `leanprover/lean4:v4.35.0-rc2`.
* **`LICENSE`**: Apache-2.0 license.

---

## Building and Verification

To build and verify the entire project:

```bash
lake update
lake build
```

To verify axioms for the solution theorems:

```bash
lake env lean --run - << 'EOF'
import Solution
#print axioms PlankProblem.ball_plank_theorem
#print axioms PlankProblem.core_theorem
#print axioms PlankProblem.davenport_conjecture
EOF
```

Expected output:
```text
'PlankProblem.ball_plank_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'PlankProblem.core_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'PlankProblem.davenport_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---
