module

public import Mathlib

@[expose] public section

/-!
# Ball's Plank Theorem

This module contains the human-auditable statements of the formalized results from:
**"A Short Proof of Ball's Plank Theorem"** by Arseniy Akopyan and Alexander Polyanskii (2026),
[arXiv:2609.36163](https://arxiv.org/abs/2609.36163).
Formalized by Arseniy Akopyan with the assistance of ChatGPT, Aristotle (Harmonic), and Gemini.

## Informal Summary

Keith Ball (1991) proved that if a centrally symmetric convex body $K \subset \mathbb{R}^d$
is covered by finitely many planks, then the sum of their relative widths with respect to $K$
is at least 1.

A plank is the region between two parallel hyperplanes $\{x \mid \alpha \le \langle x, u \rangle \le \beta\}$.
Its relative width with respect to $K$ is its width divided by the width of $K$ in direction $u$.

The proof by Akopyan and Polyanskii reduces Ball's theorem to a **core theorem** about linear
functionals on $\mathbb{R}^n$:
Given an orthonormal basis $X = (x_1, \dots, x_n)$ and linear functionals $\ell_1, \dots, \ell_n$
satisfying $\ell_i(x_i) = 1$, for any real shifts $c_1, \dots, c_n$, there exists a point $z \in \mathbb{R}^n$
such that $\|z\| \le \sqrt{n}$ and $|\ell_i(z) - c_i| \ge 1$ for all $i$.

The core theorem also yields a short proof of **Davenport's problem** for centrally symmetric convex bodies (interior-disjointness of a homothet $K/(n+1)$ from $n$ hyperplanes).
-/

open Set
open scoped BigOperators InnerProductSpace Pointwise

noncomputable section

namespace PlankProblem

section Planks

variable {n : ℕ}

local notation "Rn" => EuclideanSpace ℝ (Fin n)

/-- A closed plank in `ℝⁿ`: the region between two parallel hyperplanes
perpendicular to a unit normal vector `normal`. -/
structure Plank (n : ℕ) where
  normal : EuclideanSpace ℝ (Fin n)
  lower : ℝ
  upper : ℝ
  normal_is_unit : ‖normal‖ = 1
  lower_le_upper : lower ≤ upper

namespace Plank

/-- The subset of `ℝⁿ` consisting of the points in the plank. -/
def carrier (P : Plank n) : Set Rn :=
  {x | P.lower ≤ ⟪x, P.normal⟫_ℝ ∧
       ⟪x, P.normal⟫_ℝ ≤ P.upper}

/-- The geometric width of the plank: distance between its boundary hyperplanes. -/
def width (P : Plank n) : ℝ :=
  P.upper - P.lower

instance : CoeOut (Plank n) (Set Rn) :=
  ⟨carrier⟩

end Plank

/-- The directional width of a set `K ⊆ ℝⁿ` in direction `u`:
`sup_{x ∈ K} ⟨x, u⟩ - inf_{x ∈ K} ⟨x, u⟩`. -/
def directionalWidth (K : Set Rn) (u : Rn) : ℝ :=
  sSup ((fun x ↦ ⟪x, u⟫_ℝ) '' K) -
  sInf ((fun x ↦ ⟪x, u⟫_ℝ) '' K)

/-- The relative width of a plank `P` with respect to `K`:
the width of `P` divided by the directional width of `K` along the normal of `P`. -/
def relativeWidth (K : Set Rn) (P : Plank n) : ℝ :=
  P.width / directionalWidth K P.normal

/-- A convex body in `ℝⁿ`: a compact convex set with nonempty interior. -/
def IsConvexBody (K : Set Rn) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- A set `K ⊆ ℝⁿ` is centrally symmetric if there is a centre `c` such that
reflection in `c` preserves `K`. -/
def IsCentrallySymmetric (K : Set Rn) : Prop :=
  ∃ c : Rn, ∀ x, x ∈ K ↔ (2 : ℝ) • c - x ∈ K

/-- Homothetic copy of `K`: the set `t + r • K`. -/
def homothet (t : Rn) (r : ℝ) (K : Set Rn) : Set Rn :=
  t +ᵥ r • K

/-- Bang's affine plank conjecture (open problem): if any convex body `K ⊆ ℝⁿ`
(not necessarily centrally symmetric) is covered by finitely many planks,
the sum of their relative widths is at least 1. -/
def BangPlankConjecture : Prop :=
  ∀ {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (_ : IsConvexBody K)
    (P : Fin m → Plank n) (_ : K ⊆ ⋃ i, (P i : Set _)),
    1 ≤ ∑ i, relativeWidth K (P i)

/-- **Ball's plank theorem** for centrally symmetric convex bodies:
If a centrally symmetric convex body `K ⊆ ℝⁿ` is covered by finitely many planks `P i`,
then the sum of their relative widths with respect to `K` is at least 1. -/
theorem ball_plank_theorem
    {m : ℕ}
    (K : Set Rn)
    (hK : IsConvexBody K)
    (hsymm : IsCentrallySymmetric K)
    (P : Fin m → Plank n)
    (hcover : K ⊆ ⋃ i, (P i : Set Rn)) :
    1 ≤ ∑ i, relativeWidth K (P i) := by
  sorry

/-- **The core theorem**:
Let `X = (x₁, …, xₙ)` be an orthonormal basis of `ℝⁿ` and `ℓ₁, …, ℓₙ` linear functionals
with `ℓᵢ(xᵢ) = 1`. Then for any real shifts `c₁, …, cₙ`, there exists a point `z ∈ ℝⁿ`
with `‖z‖ ≤ √n` such that `|ℓᵢ(z) - cᵢ| ≥ 1` for all `i`. -/
theorem core_theorem
    (X : OrthonormalBasis (Fin n) ℝ Rn)
    (ℓ : Fin n → (Rn →ₗ[ℝ] ℝ))
    (hℓ : ∀ i, ℓ i (X i) = 1)
    (c : Fin n → ℝ) :
    ∃ z : Rn,
      ‖z‖ ≤ Real.sqrt (n : ℝ) ∧
      ∀ i, 1 ≤ |ℓ i z - c i| := by
  sorry

/-- **Davenport's problem** for centrally symmetric convex bodies:
Let `K` be a centrally symmetric convex body in `ℝⁿ`, and let `f₁, …, fₙ` be nonzero linear functionals
and `c₁, …, cₙ` real constants. Then there exists a translation vector `t` such that the homothet
`t + (1/(n+1)) K` is contained in `K` and its interior is disjoint from all hyperplanes `{fᵢ = cᵢ}`. -/
theorem davenport_conjecture
    (K : Set Rn)
    (hK : IsConvexBody K)
    (hsymm : IsCentrallySymmetric K)
    (f : Fin n → (Rn →ₗ[ℝ] ℝ))
    (hf : ∀ i, f i ≠ 0)
    (c : Fin n → ℝ) :
    ∃ t : Rn,
      homothet t (1 / (n + 1 : ℝ)) K ⊆ K ∧
      ∀ i x,
        x ∈ interior (homothet t (1 / (n + 1 : ℝ)) K) →
        f i x ≠ c i := by
  sorry

end Planks

end PlankProblem
