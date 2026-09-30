module

public import Mathlib

/-!
# Planks through an orthonormal basis cannot cover the ball `√n · B₂ⁿ`

Let `x₁, …, xₙ` be an orthonormal basis of `ℝⁿ` and let `ℓ₁, …, ℓₙ` be linear functionals
with `ℓᵢ(xᵢ) = 1`. Then the planks `Pᵢ = {x : |ℓᵢ(x)| < 1}` do not cover the closed Euclidean
ball of radius `√n`.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Classical

noncomputable section

namespace Planks

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι]

/-- The (open, symmetric) plank of a linear functional `ℓ`: the set `{x | |ℓ x| < 1}`. -/
def plank {V : Type*} [AddCommGroup V] [Module ℝ V] (ℓ : Module.Dual ℝ V) : Set V :=
  {x | |ℓ x| < 1}

/-- The objective `F(Y) = ∑ᵢ (1 / ℓᵢ(yᵢ))²`. -/
def objF (ℓ : ι → E →L[ℝ] ℝ) (y : ι → E) : ℝ := ∑ i, ((ℓ i (y i))⁻¹) ^ 2

/-- Admissible families: orthonormal, with `1 ≤ 2 |ι| ℓᵢ(yᵢ)²` for all `i`. -/
def admissible (ℓ : ι → E →L[ℝ] ℝ) : Set (ι → E) :=
  {y | Orthonormal ℝ y ∧ ∀ i, 1 ≤ 2 * (Fintype.card ι : ℝ) * (ℓ i (y i)) ^ 2}

/-- Rotation of `yᵢ, yⱼ` by angle `t` in their plane. -/
def rot (y : ι → E) (i j : ι) (t : ℝ) : ι → E := fun k =>
  if k = i then Real.cos t • y i + Real.sin t • y j
  else if k = j then (-Real.sin t) • y i + Real.cos t • y j
  else y k

/-- Sign of a boolean. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

lemma exists_minimizer (ℓ : ι → E →L[ℝ] ℝ) (x : ι → E) (hx : Orthonormal ℝ x)
    (h : ∀ i, ℓ i (x i) = 1) :
    ∃ y ∈ admissible ℓ, IsMinOn (objF ℓ) (admissible ℓ) y ∧
      objF ℓ y ≤ Fintype.card ι := by
  have hxS : x ∈ admissible ℓ := ⟨hx, fun i => by
    have : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
    rw [h i]; nlinarith⟩
  have hcl : IsClosed (admissible ℓ) := by
    have : admissible ℓ = (⋂ a, ⋂ b, {y : ι → E | inner ℝ (y a) (y b) = if a = b then 1 else 0}) ∩
        ⋂ i, {y : ι → E | 1 ≤ 2 * (Fintype.card ι : ℝ) * (ℓ i (y i)) ^ 2} := by
      ext y; simp [admissible, orthonormal_iff_ite]
    rw [this]
    exact IsClosed.inter (isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq (by fun_prop) continuous_const)
      (isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop))
  have hbdd : Bornology.IsBounded (admissible ℓ) := by
    refine (Metric.isBounded_closedBall (x := (0 : ι → E)) (r := 1)).subset ?_
    intro y hy
    rw [mem_closedBall_zero_iff]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => (hy.1.1 i).le
  have hcpt : IsCompact (admissible ℓ) := Metric.isCompact_of_isClosed_isBounded hcl hbdd
  have hcont : ContinuousOn (objF ℓ) (admissible ℓ) := by
    unfold objF
    refine continuousOn_finsetSum _ fun i _ => ?_
    refine ContinuousOn.pow (ContinuousOn.inv₀ (by fun_prop) fun y hy => ?_) 2
    intro h0
    have := hy.2 i
    rw [h0] at this
    norm_num at this
  obtain ⟨y, hy, hmin⟩ := hcpt.exists_isMinOn ⟨x, hxS⟩ hcont
  refine ⟨y, hy, hmin, ?_⟩
  calc objF ℓ y ≤ objF ℓ x := hmin hxS
    _ = Fintype.card ι := by simp [objF, h]

omit [FiniteDimensional ℝ E] [Fintype ι] in
lemma rot_zero (y : ι → E) (i j : ι) : rot y i j 0 = y := by
  funext k
  by_cases hki : k = i
  · subst hki; simp [rot]
  · by_cases hkj : k = j
    · subst hkj; simp [rot, hki]
    · simp [rot, hki, hkj]

omit [FiniteDimensional ℝ E] [Fintype ι] in
lemma rot_orthonormal (y : ι → E) (hy : Orthonormal ℝ y) (i j : ι) (hij : i ≠ j) (t : ℝ) :
    Orthonormal ℝ (rot y i j t) := by
  rw [orthonormal_iff_ite] at hy ⊢
  have hc := Real.cos_sq_add_sin_sq t
  have hji : j ≠ i := Ne.symm hij
  intro a b
  by_cases hai : a = i
  · subst hai
    by_cases hbi : b = a
    · subst hbi
      simp only [rot, ↓reduceIte, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hy, hij, hji]
      linarith
    · by_cases hbj : b = j
      · subst hbj
        simp only [rot, ↓reduceIte, inner_add_left, inner_add_right, real_inner_smul_left,
          real_inner_smul_right, hy, hij, hji]
        ring
      · simp only [rot, ↓reduceIte, inner_add_left, real_inner_smul_left, hy, hbi, hbj,
          Ne.symm hbi, Ne.symm hbj]
        ring
  · by_cases haj : a = j
    · subst haj
      by_cases hbi : b = i
      · subst hbi
        simp only [rot, ↓reduceIte, inner_add_left, inner_add_right, real_inner_smul_left,
          real_inner_smul_right, hy, hij, hji]
        ring
      · by_cases hbj : b = a
        · subst hbj
          simp only [rot, ↓reduceIte, inner_add_left, inner_add_right, real_inner_smul_left,
            real_inner_smul_right, hy, hij, hji]
          linarith
        · simp only [rot, ↓reduceIte, inner_add_left, real_inner_smul_left, hy, hji, hbi, hbj,
            Ne.symm hbi, Ne.symm hbj]
          ring
    · by_cases hbi : b = i
      · subst hbi
        simp only [rot, ↓reduceIte, inner_add_right, real_inner_smul_right, hy, hai, haj]
        ring
      · by_cases hbj : b = j
        · subst hbj
          simp only [rot, ↓reduceIte, inner_add_right, real_inner_smul_right, hy, hji, hai, haj]
          ring
        · simp [rot, hy, hai, haj, hbi, hbj]

omit [FiniteDimensional ℝ E] in
lemma stationary (ℓ : ι → E →L[ℝ] ℝ) (y : ι → E) (hy : y ∈ admissible ℓ)
    (hmin : IsMinOn (objF ℓ) (admissible ℓ) y) (hF : objF ℓ y ≤ Fintype.card ι)
    (i j : ι) (hij : i ≠ j) :
    ((ℓ i (y i))⁻¹) ^ 3 * ℓ i (y j) = ((ℓ j (y j))⁻¹) ^ 3 * ℓ j (y i) := by
  have hji : j ≠ i := Ne.symm hij
  let du : ι → ℝ := fun k => if k = i then ℓ i (y j) else if k = j then -ℓ j (y i) else 0
  have hu : ∀ k, HasDerivAt (fun t => ℓ k (rot y i j t k)) (du k) 0 := by
    intro k
    by_cases hki : k = i
    · subst hki
      have e : (fun t => ℓ k (rot y k j t k)) =
          (fun t => Real.cos t * ℓ k (y k)) + fun t => Real.sin t * ℓ k (y j) := by
        ext t; simp [rot]
      rw [e]
      have := ((Real.hasDerivAt_cos 0).mul_const (ℓ k (y k))).add
        ((Real.hasDerivAt_sin 0).mul_const (ℓ k (y j)))
      simpa [du] using this
    · by_cases hkj : k = j
      · subst hkj
        have e : (fun t => ℓ k (rot y i k t k)) =
            (-fun t => Real.sin t * ℓ k (y i)) + fun t => Real.cos t * ℓ k (y k) := by
          ext t; simp [rot, hki]
        rw [e]
        have := (((Real.hasDerivAt_sin 0).mul_const (ℓ k (y i))).neg).add
          ((Real.hasDerivAt_cos 0).mul_const (ℓ k (y k)))
        simpa [du, hki] using this
      · have e : (fun t => ℓ k (rot y i j t k)) = fun _ => ℓ k (y k) := by
          funext t; simp [rot, hki, hkj]
        rw [e]
        simpa [du, hki, hkj] using hasDerivAt_const (0 : ℝ) (ℓ k (y k))
  have hy0 : ∀ k, ℓ k (y k) ≠ 0 := fun k h0 => by
    have := hy.2 k
    rw [h0] at this
    norm_num at this
  have hr0 : ∀ k, rot y i j 0 k = y k := fun k => by rw [rot_zero]
  have hg : ∀ k, HasDerivAt (fun t => ((ℓ k (rot y i j t k))⁻¹) ^ 2)
      (((2 : ℕ) : ℝ) * ((ℓ k (rot y i j 0 k))⁻¹) ^ (2 - 1) *
        (-(du k) / (ℓ k (rot y i j 0 k)) ^ 2)) 0 := fun k =>
    ((hu k).inv (by rw [hr0]; exact hy0 k)).pow 2
  have hFd : HasDerivAt (fun t => objF ℓ (rot y i j t)) (∑ k, (((2 : ℕ) : ℝ) *
      ((ℓ k (rot y i j 0 k))⁻¹) ^ (2 - 1) * (-(du k) / (ℓ k (rot y i j 0 k)) ^ 2))) 0 :=
    HasDerivAt.fun_sum fun k _ => hg k
  have hmem : ∀ᶠ t in nhds (0 : ℝ), rot y i j t ∈ admissible ℓ := by
    have hk : ∀ k, ∀ᶠ t in nhds (0 : ℝ),
        1 < 2 * (Fintype.card ι : ℝ) * (ℓ k (rot y i j t k)) ^ 2 := by
      intro k
      have hc : ContinuousAt (fun t => 2 * (Fintype.card ι : ℝ) * (ℓ k (rot y i j t k)) ^ 2) 0 :=
        ((hu k).continuousAt.pow 2).const_mul _
      have hv : 1 < 2 * (Fintype.card ι : ℝ) * (ℓ k (rot y i j 0 k)) ^ 2 := by
        rw [hr0]
        have hle : ((ℓ k (y k))⁻¹) ^ 2 ≤ Fintype.card ι :=
          le_trans (Finset.single_le_sum (f := fun k => ((ℓ k (y k))⁻¹) ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ k)) hF
        have hpos : 0 < (ℓ k (y k)) ^ 2 := by have := hy0 k; positivity
        have : ((ℓ k (y k))⁻¹) ^ 2 * (ℓ k (y k)) ^ 2 = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ (hy0 k), one_pow]
        nlinarith
      exact Filter.Tendsto.eventually hc (lt_mem_nhds hv)
    filter_upwards [Filter.eventually_all.mpr hk] with t ht
    exact ⟨rot_orthonormal y hy.1 i j hij t, fun k => (ht k).le⟩
  have hlm : IsLocalMin (fun t => objF ℓ (rot y i j t)) 0 := by
    filter_upwards [hmem] with t ht
    simp only [rot_zero]
    exact hmin ht
  have h0 := hlm.hasDerivAt_eq_zero hFd
  rw [Fintype.sum_eq_add i j hij (fun k hk => by simp [du, hk.1, hk.2])] at h0
  simp [hr0, du, hji] at h0
  linear_combination (-1 / 2 : ℝ) * h0

omit [FiniteDimensional ℝ E] in
lemma flip_quad (M : ι → ι → ℝ) (hM : ∀ i j, M i j = M j i) (s s' : ι → ℝ) (k : ι)
    (hs' : ∀ i, s' i = if i = k then -s k else s i) :
    ∑ i, ∑ j, s' i * s' j * M i j =
      ∑ i, ∑ j, s i * s j * M i j - 4 * s k * ∑ j, s j * M k j + 4 * s k ^ 2 * M k k := by
  have hu : ∀ i, s' i = s i + (if i = k then -2 * s k else 0) := by
    intro i; rw [hs']; by_cases h : i = k
    · subst h; simp; ring
    · simp [h]
  have hsw : ∑ i, s i * M i k = ∑ j, s j * M k j :=
    Finset.sum_congr rfl fun i _ => by rw [hM]
  have e : ∀ i j, s' i * s' j * M i j = s i * s j * M i j
      + (if i = k then -2 * s k else 0) * (s j * M i j)
      + (if j = k then -2 * s k else 0) * (s i * M i j)
      + (if i = k then -2 * s k else 0) * ((if j = k then -2 * s k else 0) * M i j) := by
    intro i j; rw [hu i, hu j]; ring
  simp only [e, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum, hsw]
  ring

omit [FiniteDimensional ℝ E] in
lemma bang (ℓ : ι → E →L[ℝ] ℝ) (y : ι → E) (hy0 : ∀ i, ℓ i (y i) ≠ 0)
    (hsym : ∀ i j, ((ℓ i (y i))⁻¹) ^ 3 * ℓ i (y j) = ((ℓ j (y j))⁻¹) ^ 3 * ℓ j (y i)) :
    ∃ ε : ι → Bool, ∀ k,
      1 ≤ |ℓ k (∑ i, (sgn (ε i) * (ℓ i (y i))⁻¹) • y i)| := by
  set p : ι → ℝ := fun i => (ℓ i (y i))⁻¹ with hp
  let M : ι → ι → ℝ := fun i j => p i ^ 4 * p j * ℓ i (y j)
  have hM : ∀ i j, M i j = M j i := by
    intro i j
    have := hsym i j
    calc p i ^ 4 * p j * ℓ i (y j) = p i * p j * (p i ^ 3 * ℓ i (y j)) := by ring
      _ = p i * p j * (p j ^ 3 * ℓ j (y i)) := by rw [this]
      _ = _ := by ring
  let Q : (ι → Bool) → ℝ := fun ε => ∑ i, ∑ j, sgn (ε i) * sgn (ε j) * M i j
  obtain ⟨ε, -, hε⟩ := Finset.exists_max_image Finset.univ Q Finset.univ_nonempty
  refine ⟨ε, fun k => ?_⟩
  have hle := hε (Function.update ε k (!ε k)) (Finset.mem_univ _)
  have key := flip_quad M hM (fun i => sgn (ε i)) (fun i => sgn (Function.update ε k (!ε k) i)) k
    (by
      intro i
      by_cases h : i = k
      · subst h; simp only [Function.update_self, ite_true]; cases ε i <;> simp [sgn]
      · simp [h])
  have hz : ℓ k (∑ i, (sgn (ε i) * p i) • y i) = ∑ j, sgn (ε j) * p j * ℓ k (y j) := by
    simp [map_sum, map_smul]
  have hrow : ∑ j, sgn (ε j) * M k j = p k ^ 4 * ℓ k (∑ i, (sgn (ε i) * p i) • y i) := by
    rw [hz, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [M]; ring
  have hkk : M k k = p k ^ 4 := by
    simp only [M, hp]
    field_simp [hy0 k]
  have hsk : sgn (ε k) ^ 2 = 1 := by unfold sgn; split_ifs <;> norm_num
  have hpk : 0 < p k ^ 4 := by
    have : p k ≠ 0 := inv_ne_zero (hy0 k)
    positivity
  change ∑ i, ∑ j, _ ≤ ∑ i, ∑ j, _ at hle
  rw [key, hrow, hkk, hsk] at hle
  have h1 : 1 ≤ sgn (ε k) * ℓ k (∑ i, (sgn (ε i) * p i) • y i) := by
    nlinarith
  show 1 ≤ |ℓ k (∑ i, (sgn (ε i) * p i) • y i)|
  set w := ℓ k (∑ i, (sgn (ε i) * p i) • y i)
  cases hεk : ε k <;> simp only [sgn, hεk, ite_true, Bool.false_eq_true, ite_false] at h1
  · linarith [neg_le_abs w]
  · linarith [le_abs_self w]

omit [FiniteDimensional ℝ E] in
lemma norm_sq_sum (y : ι → E) (hy : Orthonormal ℝ y) (c : ι → ℝ) :
    ‖∑ i, c i • y i‖ ^ 2 = ∑ i, c i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right, orthonormal_iff_ite.mp hy]
  simp [sq]

/-- General version: for an orthonormal basis `x` of a finite-dimensional real inner product
space and continuous linear functionals with `ℓᵢ(xᵢ) = 1`, some point of norm `≤ √|ι|`
satisfies `|ℓᵢ(z)| ≥ 1` for all `i`. -/
theorem exists_point_outside_planks (ℓ : ι → E →L[ℝ] ℝ) (x : ι → E) (hx : Orthonormal ℝ x)
    (h : ∀ i, ℓ i (x i) = 1) :
    ∃ z : E, ‖z‖ ≤ Real.sqrt (Fintype.card ι) ∧ ∀ i, 1 ≤ |ℓ i z| := by
  obtain ⟨y, hyS, hmin, hF⟩ := exists_minimizer ℓ x hx h
  have hy0 : ∀ i, ℓ i (y i) ≠ 0 := fun i hi => by
    have := hyS.2 i
    rw [hi] at this
    norm_num at this
  have hsym : ∀ i j, ((ℓ i (y i))⁻¹) ^ 3 * ℓ i (y j) = ((ℓ j (y j))⁻¹) ^ 3 * ℓ j (y i) :=
    fun i j => if hij : i = j then by subst hij; rfl else stationary ℓ y hyS hmin hF i j hij
  obtain ⟨ε, hε⟩ := bang ℓ y hy0 hsym
  refine ⟨_, ?_, hε⟩
  rw [← Real.sqrt_sq (norm_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [norm_sq_sum y hyS.1]
  calc ∑ i, (sgn (ε i) * (ℓ i (y i))⁻¹) ^ 2 = objF ℓ y := by
        unfold objF
        refine Finset.sum_congr rfl fun i _ => ?_
        have : sgn (ε i) ^ 2 = 1 := by unfold sgn; split_ifs <;> norm_num
        rw [mul_pow, this, one_mul]
    _ ≤ _ := hF

/-- **Main theorem.** Let `x₁, …, xₙ` be an orthonormal basis of `ℝⁿ` and `ℓ₁, …, ℓₙ` linear
functionals with `ℓᵢ(xᵢ) = 1`. Then the planks `Pᵢ = {z : |ℓᵢ(z)| < 1}` do not cover the
closed Euclidean ball of radius `√n` centred at the origin. -/
theorem planks_not_cover_ball (n : ℕ)
    (x : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (ℓ : Fin n → Module.Dual ℝ (EuclideanSpace ℝ (Fin n)))
    (h : ∀ i, ℓ i (x i) = 1) :
    ¬ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n) ⊆ ⋃ i, plank (ℓ i)) := by
  intro hcov
  obtain ⟨z, hz, hz'⟩ := exists_point_outside_planks
    (fun i => LinearMap.toContinuousLinearMap (ℓ i)) x x.orthonormal (by simpa using h)
  have hmem := hcov (mem_closedBall_zero_iff.mpr (by simpa using hz))
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
  have := hz' i
  simp only [plank, Set.mem_ofPred_eq] at hi
  simp at this
  linarith

end Planks

end
