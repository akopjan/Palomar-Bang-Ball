module

public import BallPlank.ShiftedPlanks

/-!
# Ball's Plank Theorem and Related Problems

This module formalizes Ball's Plank Theorem for centrally symmetric convex bodies,
the core theorem on linear functionals through an orthonormal basis, and Davenport's problem.
-/

@[expose] public section

open Set
open scoped BigOperators InnerProductSpace Pointwise

noncomputable section

namespace PlankProblem

section Planks

variable {n : ℕ}

local notation "Rn" => EuclideanSpace ℝ (Fin n)

/-- A closed plank in `ℝⁿ`. -/
structure Plank (n : ℕ) where
  normal : EuclideanSpace ℝ (Fin n)
  lower : ℝ
  upper : ℝ
  normal_is_unit : ‖normal‖ = 1
  lower_le_upper : lower ≤ upper

namespace Plank

def carrier (P : Plank n) : Set Rn :=
  {x | P.lower ≤ ⟪x, P.normal⟫_ℝ ∧
       ⟪x, P.normal⟫_ℝ ≤ P.upper}

def width (P : Plank n) : ℝ :=
  P.upper - P.lower

instance : CoeOut (Plank n) (Set Rn) :=
  ⟨carrier⟩

end Plank

/-- Width of `K` in direction `u`. -/
def directionalWidth (K : Set Rn) (u : Rn) : ℝ :=
  sSup ((fun x ↦ ⟪x, u⟫_ℝ) '' K) -
  sInf ((fun x ↦ ⟪x, u⟫_ℝ) '' K)

/-- Relative width of a plank with respect to `K`. -/
def relativeWidth (K : Set Rn) (P : Plank n) : ℝ :=
  P.width / directionalWidth K P.normal

def IsConvexBody (K : Set Rn) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

def IsCentrallySymmetric (K : Set Rn) : Prop :=
  ∃ c : Rn, ∀ x, x ∈ K ↔ (2 : ℝ) • c - x ∈ K

/-- Bang's affine plank conjecture (open problem): if any convex body `K ⊆ ℝⁿ`
is covered by finitely many planks, then the sum of their relative widths is at least 1.
This is stated as an open conjecture definition; it is not proved here. -/
def BangPlankConjecture : Prop :=
  ∀ {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (_ : IsConvexBody K)
    (P : Fin m → Plank n) (_ : K ⊆ ⋃ i, (P i : Set _)),
    1 ≤ ∑ i, relativeWidth K (P i)

/-- The core theorem: if `X` is an orthonormal basis of `ℝⁿ` and `ℓᵢ(Xᵢ) = 1`, then for any
centres `cᵢ` there is a point `z` of the ball `√n · B₂ⁿ` with `|ℓᵢ(z) - cᵢ| ≥ 1` for all `i`,
i.e. the planks `{|ℓᵢ - cᵢ| < 1}` do not cover `√n · B₂ⁿ`. -/
theorem core_theorem
    (X : OrthonormalBasis (Fin n) ℝ Rn)
    (ℓ : Fin n → (Rn →ₗ[ℝ] ℝ))
    (hℓ : ∀ i, ℓ i (X i) = 1)
    (c : Fin n → ℝ) :
    ∃ z : Rn,
      ‖z‖ ≤ Real.sqrt (n : ℝ) ∧
      ∀ i, 1 ≤ |ℓ i z - c i| := by
  obtain ⟨z, hz, hz'⟩ := Planks.exists_point_outside_shifted_planks
    (fun i => LinearMap.toContinuousLinearMap (ℓ i)) c X X.orthonormal (by simpa using hℓ)
  exact ⟨z, by simpa using hz, fun i => by simpa using hz' i⟩

def homothet (t : Rn) (r : ℝ) (K : Set Rn) : Set Rn :=
  t +ᵥ r • K

/-! ### Auxiliary lemmas for Davenport's problem -/

/-- A combination `∑ aᵢ vᵢ` with `∑ |aᵢ| ≤ 1` of points of a symmetric convex set containing `0`
stays in the set. -/
lemma sum_smul_mem_of_abs_sum_le {ι : Type*} [Fintype ι] {S : Set Rn} (hS : Convex ℝ S)
    (h0 : (0 : Rn) ∈ S) (hneg : ∀ x ∈ S, -x ∈ S) (v : ι → Rn) (hv : ∀ i, v i ∈ S)
    (a : ι → ℝ) (ha : ∑ i, |a i| ≤ 1) : ∑ i, a i • v i ∈ S := by
  classical
  set W := ∑ i, |a i| with hW
  let u : ι → Rn := fun i => if 0 ≤ a i then v i else -v i
  have hu : ∀ i, u i ∈ S := fun i => by
    simp only [u]; split_ifs
    · exact hv i
    · exact hneg _ (hv i)
  have hau : ∀ i, a i • v i = |a i| • u i := fun i => by
    simp only [u]; split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h), smul_neg, neg_smul, neg_neg]
  simp_rw [hau]
  by_cases hW0 : W = 0
  · have : ∀ i, |a i| = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg (a i))).mp hW0 i (Finset.mem_univ _)
    simp [this, h0]
  have hWpos : 0 < W := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => abs_nonneg _) (Ne.symm hW0)
  have hmem : ∑ i, (|a i| / W) • u i ∈ S := by
    refine hS.sum_mem (fun i _ => div_nonneg (abs_nonneg _) hWpos.le) ?_ (fun i _ => hu i)
    rw [← Finset.sum_div, div_self hW0]
  have : ∑ i, |a i| • u i = W • ∑ i, (|a i| / W) • u i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_div_cancel₀ _ hW0]
  rw [this]
  exact hS.smul_mem_of_zero_mem h0 hmem ⟨hWpos.le, ha⟩

/-- If a set lies in the closed half-space `{c ≤ f}` of a nonzero functional, then its interior
misses the hyperplane `{f = c}`. -/
lemma ne_of_mem_interior_of_subset_halfspace {A : Set Rn} {f : Rn →ₗ[ℝ] ℝ} (hf : f ≠ 0) {c : ℝ}
    (hA : A ⊆ {x | c ≤ f x}) {x : Rn} (hx : x ∈ interior A) : f x ≠ c := by
  intro hfx
  obtain ⟨u, hu⟩ : ∃ u, f u ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (LinearMap.ext h)
  have hnhds : A ∈ nhds x := mem_interior_iff_mem_nhds.mp hx
  have ht : Filter.Tendsto (fun t : ℝ => x + (t * -(f u)⁻¹) • u) (nhds 0) (nhds x) := by
    have : Continuous (fun t : ℝ => x + (t * -(f u)⁻¹) • u) := by fun_prop
    simpa using this.tendsto 0
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), x + (t * -(f u)⁻¹) • u ∈ A :=
    (ht.eventually hnhds).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, htA, htpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have := hA htA
  simp only [mem_ofPred_eq, map_add, map_smul, smul_eq_mul] at this
  rw [hfx] at this
  have : t * -(f u)⁻¹ * f u = -t := by field_simp
  have htp : (0 : ℝ) < t := htpos
  linarith

/-- Davenport's problem for centrally symmetric convex bodies. -/
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
  classical
  obtain ⟨c0, hc0⟩ := hsymm
  obtain ⟨hKc, hKconv, p, hp⟩ := hK
  -- the body centred at the origin
  set K0 : Set Rn := {x | c0 + x ∈ K} with hK0
  have hK0conv : Convex ℝ K0 := by
    intro a ha b hb α β hα hβ hab
    have := hKconv ha hb hα hβ hab
    show c0 + (α • a + β • b) ∈ K
    convert this using 1
    calc c0 + (α • a + β • b) = (α + β) • c0 + (α • a + β • b) := by rw [hab, one_smul]
      _ = α • (c0 + a) + β • (c0 + b) := by module
  have hK0neg : ∀ x ∈ K0, -x ∈ K0 := by
    intro x hx
    have := (hc0 _).mp hx
    show c0 + -x ∈ K
    convert this using 1
    module
  have hpK : p ∈ K := interior_subset hp
  have hq : p - c0 ∈ K0 := by show c0 + (p - c0) ∈ K; simpa using hpK
  have hK00 : (0 : Rn) ∈ K0 := by
    have := hK0conv hq (hK0neg _ hq) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    convert this using 1
    module
  have hK0c : IsCompact K0 := (Homeomorph.addLeft c0).isCompact_preimage.mpr hKc
  -- support points
  have hsupp : ∀ i, ∃ v ∈ K0, 0 < f i v ∧ ∀ k ∈ K0, |f i k| ≤ f i v := by
    intro i
    obtain ⟨v, hv, hmax⟩ := hK0c.exists_isMaxOn ⟨0, hK00⟩
      (LinearMap.continuous_of_finiteDimensional (f i)).continuousOn
    have habs : ∀ k ∈ K0, |f i k| ≤ f i v := by
      intro k hk
      have h1 : f i k ≤ f i v := hmax hk
      have h2 : f i (-k) ≤ f i v := hmax (hK0neg k hk)
      rw [map_neg] at h2
      exact abs_le.mpr ⟨by linarith, h1⟩
    refine ⟨v, hv, ?_, habs⟩
    obtain ⟨u, hu⟩ : ∃ u, f i u ≠ 0 := by
      by_contra h
      push Not at h
      exact hf i (LinearMap.ext h)
    have ht : Filter.Tendsto (fun t : ℝ => p + t • u) (nhds 0) (nhds p) := by
      have : Continuous (fun t : ℝ => p + t • u) := by fun_prop
      simpa using this.tendsto 0
    have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, p + t • u ∈ K :=
      (ht.eventually (mem_interior_iff_mem_nhds.mp hp)).filter_mono nhdsWithin_le_nhds
    obtain ⟨t, htK, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
    have ht0' : t ≠ 0 := ht0
    have hq' : p + t • u - c0 ∈ K0 := by show c0 + (p + t • u - c0) ∈ K; simpa using htK
    have hdiff : f i (p + t • u - c0) - f i (p - c0) = t * f i u := by
      simp only [map_sub, map_add, map_smul, smul_eq_mul]; ring
    have hne : f i (p + t • u - c0) ≠ 0 ∨ f i (p - c0) ≠ 0 := by
      by_contra h
      push Not at h
      rw [h.1, h.2] at hdiff
      exact mul_ne_zero ht0' hu (by linarith)
    rcases hne with h | h
    · exact lt_of_lt_of_le (abs_pos.mpr h) (habs _ hq')
    · exact lt_of_lt_of_le (abs_pos.mpr h) (habs _ hq)
  choose v hvK0 hvpos hvmax using hsupp
  -- the linear map sending the standard basis to the support points
  let A : Rn →ₗ[ℝ] Rn := ∑ j, (EuclideanSpace.proj j : Rn →L[ℝ] ℝ).toLinearMap.smulRight (v j)
  have hA : ∀ z, A z = ∑ j, z j • v j := fun z => by simp [A]
  have hAe : ∀ i, A (EuclideanSpace.basisFun (Fin n) ℝ i) = v i := fun i => by
    simp [hA]
  let ℓ : Fin n → (Rn →ₗ[ℝ] ℝ) := fun i => (f i (v i))⁻¹ • ((f i).comp A)
  have hℓ : ∀ i, ℓ i (EuclideanSpace.basisFun (Fin n) ℝ i) = 1 := fun i => by
    simp only [ℓ, LinearMap.smul_apply, LinearMap.comp_apply, hAe, smul_eq_mul]
    exact inv_mul_cancel₀ (hvpos i).ne'
  set r : ℝ := 1 / (n + 1 : ℝ) with hr
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hrpos : 0 < r := by positivity
  have hrn : r * (n + 1) = 1 := by rw [hr]; field_simp
  obtain ⟨z, hz, hzℓ⟩ := core_theorem (EuclideanSpace.basisFun (Fin n) ℝ) ℓ hℓ
    (fun i => (n + 1) * (c i - f i c0) / f i (v i))
  -- `∑ |zⱼ| ≤ n`
  have hzsum : ∑ j, |z j| ≤ n := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => |z j|)
    have h2 : ‖z‖ ^ 2 = ∑ j, |z j| ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      simp
    have h3 : ‖z‖ ^ 2 ≤ n := by
      calc ‖z‖ ^ 2 ≤ (Real.sqrt n) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
        _ = n := Real.sq_sqrt (Nat.cast_nonneg _)
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    rw [← h2] at h1
    have h4 : (∑ j, |z j|) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    exact (abs_le_of_sq_le_sq' h4 (Nat.cast_nonneg n)).2
  -- the centre of the homothet
  refine ⟨c0 + r • A z - r • c0, ?_, ?_⟩
  all_goals
    have hdesc : ∀ x ∈ homothet (c0 + r • A z - r • c0) (1 / (n + 1 : ℝ)) K,
        ∃ k0 ∈ K0, x = c0 + r • (A z + k0) := by
      intro x hx
      obtain ⟨y, ⟨k, hk, rfl⟩, rfl⟩ := hx
      refine ⟨k - c0, by show c0 + (k - c0) ∈ K; simpa using hk, ?_⟩
      simp only [vadd_eq_add]
      module
  · -- the homothet lies in `K`
    intro x hx
    obtain ⟨k0, hk0, rfl⟩ := hdesc x hx
    show c0 + r • (A z + k0) ∈ K
    have hmem := sum_smul_mem_of_abs_sum_le hK0conv hK00 hK0neg
      (Sum.elim v (fun _ : Unit => k0)) (by rintro (j | _) <;> simp [hvK0, hk0])
      (Sum.elim (fun j => r * z j) (fun _ : Unit => r)) (by
        simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
          Finset.sum_singleton, abs_mul, abs_of_pos hrpos]
        rw [← Finset.mul_sum]
        nlinarith)
    have heq : ∑ s, Sum.elim (fun j => r * z j) (fun _ : Unit => r) s •
        Sum.elim v (fun _ : Unit => k0) s = r • (A z + k0) := by
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
        Finset.sum_singleton, hA, smul_add, Finset.smul_sum, mul_smul]
    rw [heq] at hmem
    exact hmem
  · -- the interior of the homothet misses every hyperplane
    intro i x hx
    set g := ℓ i z - (n + 1) * (c i - f i c0) / f i (v i) with hg
    have hgi : 1 ≤ |g| := hzℓ i
    have hval : ∀ k0 ∈ K0,
        f i (c0 + r • (A z + k0)) - c i = r * f i (v i) * g + r * f i k0 := by
      intro k0 _
      have hv0 := (hvpos i).ne'
      have e : f i (v i) * (f i (v i))⁻¹ = 1 := mul_inv_cancel₀ hv0
      simp only [hg, ℓ, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, map_add,
        map_smul, div_eq_mul_inv]
      linear_combination (-r * f i (A z) + r * (n + 1) * (c i - f i c0)) * e +
        (c i - f i c0) * hrn
    have hfv := hvpos i
    rcases le_abs'.mp hgi with hneg | hpos
    · have hsub : homothet (c0 + r • A z - r • c0) (1 / (n + 1 : ℝ)) K ⊆
          {x | (-c i) ≤ (-f i) x} := by
        intro y hy
        obtain ⟨k0, hk0, rfl⟩ := hdesc y hy
        have h1 := hval k0 hk0
        have h2 := (abs_le.mp (hvmax i k0 hk0)).2
        simp only [mem_ofPred_eq, LinearMap.neg_apply]
        nlinarith [mul_le_mul_of_nonneg_left h2 hrpos.le,
          mul_le_mul_of_nonneg_left hneg (mul_pos hrpos hfv).le]
      have := ne_of_mem_interior_of_subset_halfspace (neg_ne_zero.mpr (hf i)) hsub hx
      intro h
      apply this
      simp [h]
    · have hsub : homothet (c0 + r • A z - r • c0) (1 / (n + 1 : ℝ)) K ⊆
          {x | c i ≤ f i x} := by
        intro y hy
        obtain ⟨k0, hk0, rfl⟩ := hdesc y hy
        have h1 := hval k0 hk0
        have h2 := (abs_le.mp (hvmax i k0 hk0)).1
        simp only [mem_ofPred_eq]
        nlinarith [mul_le_mul_of_nonneg_left h2 hrpos.le,
          mul_le_mul_of_nonneg_left hpos (mul_pos hrpos hfv).le]
      exact ne_of_mem_interior_of_subset_halfspace (hf i) hsub hx

/-! ### Reduction of Ball's plank theorem to the core theorem -/

/-- Grid covering: the closed interval `[α, α + k s]` is covered by the `k` closed intervals of
radius `s/2` centred at `α + (t + 1/2) s`, `t < k`. -/
lemma exists_nat_near_grid {x α s : ℝ} {k : ℕ} (hk : 1 ≤ k) (hs : 0 ≤ s) (hα : α ≤ x)
    (hx : x ≤ α + k * s) : ∃ t : ℕ, t < k ∧ |x - (α + (t + 1 / 2) * s)| ≤ s / 2 := by
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨0, hk, ?_⟩
    have : x = α := le_antisymm (by simpa using hx) hα
    simp [this]
  · set q := (x - α) / s with hqdef
    have hq0 : 0 ≤ q := div_nonneg (by linarith) hpos.le
    have hxq : x - α = q * s := by rw [hqdef]; field_simp
    have hqk : q ≤ k := by rw [hqdef, div_le_iff₀ hpos]; linarith
    refine ⟨min ⌊q⌋₊ (k - 1), by omega, ?_⟩
    rw [abs_le]
    rcases le_total ⌊q⌋₊ (k - 1) with h | h
    · rw [min_eq_left h]
      have h1 := Nat.floor_le hq0
      have h2 := Nat.lt_floor_add_one q
      constructor <;> nlinarith
    · rw [min_eq_right h]
      have h1 : ((k - 1 : ℕ) : ℝ) ≤ q := le_trans (by exact_mod_cast h) (Nat.floor_le hq0)
      push_cast [Nat.cast_sub hk] at h1 ⊢
      constructor <;> nlinarith

/-- Cauchy–Schwarz: `∑ |zⱼ| ≤ card ι` whenever `‖z‖ ≤ √(card ι)`. -/
lemma sum_abs_le_card_of_norm_le {ι : Type*} [Fintype ι] (z : EuclideanSpace ℝ ι)
    (hz : ‖z‖ ≤ Real.sqrt (Fintype.card ι)) : ∑ j, |z j| ≤ Fintype.card ι := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => |z j|)
  have h2 : ‖z‖ ^ 2 = ∑ j, |z j| ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp
  have h3 : ‖z‖ ^ 2 ≤ Fintype.card ι := by
    calc ‖z‖ ^ 2 ≤ (Real.sqrt (Fintype.card ι)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      _ = Fintype.card ι := Real.sq_sqrt (Nat.cast_nonneg _)
  simp only [Finset.card_univ] at h1
  rw [← h2] at h1
  have h4 : (∑ j, |z j|) ^ 2 ≤ ((Fintype.card ι : ℕ) : ℝ) ^ 2 := by nlinarith
  exact (abs_le_of_sq_le_sq' h4 (Nat.cast_nonneg _)).2

/-- The normalised form of Ball's theorem, obtained from the core theorem as in the warm-up.
Let `K0` be a convex set symmetric about `0`, and let `φᵢ` be linear functionals with points
`vᵢ ∈ K0` such that `φᵢ(vᵢ) = 1`.  If the closed slabs
`{αᵢ ≤ φᵢ ≤ βᵢ}` have total half-length `∑ (βᵢ - αᵢ)/2 < 1`, then some point of `K0` lies outside
all of them.

Proof: split slab `i` into `kᵢ = ⌊wᵢ N⌋ + 1` overlapping slabs of relative width `≤ 1/N`
(with `wᵢ = (βᵢ-αᵢ)/2`), where `N` is so large that the total number `M = ∑ kᵢ ≤ N`.
Pull back along `T : ℝ^M → ℝⁿ`, `T eⱼ = v_{i(j)} / M`; the ball of radius `√M` is mapped into the
cross-polytope `conv{±vᵢ} ⊆ K0`, and the core theorem gives a point avoiding all small slabs. -/
theorem exists_point_outside_normalized_planks {m : ℕ} {K0 : Set Rn} (hconv : Convex ℝ K0)
    (h0 : (0 : Rn) ∈ K0) (hneg : ∀ x ∈ K0, -x ∈ K0)
    (φ : Fin m → (Rn →ₗ[ℝ] ℝ)) (v : Fin m → Rn) (hv : ∀ i, v i ∈ K0)
    (hφv : ∀ i, φ i (v i) = 1)
    (α β : Fin m → ℝ) (hαβ : ∀ i, α i ≤ β i) (hsum : ∑ i, (β i - α i) / 2 < 1) :
    ∃ y ∈ K0, ∀ i, φ i y < α i ∨ β i < φ i y := by
  classical
  set w : Fin m → ℝ := fun i => (β i - α i) / 2 with hw
  have hw0 : ∀ i, 0 ≤ w i := fun i => by simp only [w]; linarith [hαβ i]
  set W := ∑ i, w i with hW
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (m : ℝ) ≤ N * (1 - W) := by
    obtain ⟨N, hN⟩ := exists_nat_ge ((m : ℝ) / (1 - W))
    exact ⟨N, by rwa [div_le_iff₀ (by linarith)] at hN⟩
  set k : Fin m → ℕ := fun i => ⌊w i * N⌋₊ + 1 with hk
  have hkpos : ∀ i, 1 ≤ k i := fun i => by simp [k]
  have hkgt : ∀ i, w i * N < k i := fun i => by
    simp only [k]; push_cast; exact Nat.lt_floor_add_one _
  let ι := Σ i : Fin m, Fin (k i)
  have hcard : ((Fintype.card ι : ℕ) : ℝ) ≤ N := by
    simp only [ι, Fintype.card_sigma, Fintype.card_fin]
    push_cast
    have : ∀ i, ((k i : ℕ) : ℝ) ≤ w i * N + 1 := fun i => by
      simp only [k]; push_cast
      linarith [Nat.floor_le (mul_nonneg (hw0 i) (Nat.cast_nonneg N))]
    calc ∑ i, (k i : ℝ) ≤ ∑ i, (w i * N + 1) := Finset.sum_le_sum fun i _ => this i
      _ = W * N + m := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, hW]; simp
      _ ≤ N := by linarith
  set M : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hM
  have hMpos : ∀ _ : ι, 0 < M := fun j => Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨j⟩)
  let s : Fin m → ℝ := fun i => 2 * w i / k i
  let γ : ι → ℝ := fun j => α j.1 + (((j.2 : ℕ) : ℝ) + 1 / 2) * s j.1
  let T : EuclideanSpace ℝ ι →ₗ[ℝ] Rn :=
    ∑ j, (EuclideanSpace.proj j : EuclideanSpace ℝ ι →L[ℝ] ℝ).toLinearMap.smulRight (v j.1)
  have hT : ∀ z, T z = ∑ j, z j • v j.1 := fun z => by simp [T]
  let ℓ : ι → (EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
    fun j => LinearMap.toContinuousLinearMap ((φ j.1).comp T)
  have hℓ : ∀ j, ℓ j (EuclideanSpace.basisFun ι ℝ j) = 1 := fun j => by
    simp only [ℓ, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply, hT,
      EuclideanSpace.basisFun_apply, PiLp.single_apply]
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
    simp [hφv]
  obtain ⟨z, hz, hzℓ⟩ := Planks.exists_point_outside_shifted_planks ℓ (fun j => M * γ j)
    (EuclideanSpace.basisFun ι ℝ) (EuclideanSpace.basisFun ι ℝ).orthonormal hℓ
  have hzsum := sum_abs_le_card_of_norm_le z hz
  refine ⟨M⁻¹ • T z, ?_, ?_⟩
  · rw [hT, Finset.smul_sum]
    simp_rw [smul_smul]
    apply sum_smul_mem_of_abs_sum_le hconv h0 hneg _ (fun j => hv _)
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨j⟩⟩
    · simp
    · simp only [abs_mul, ← Finset.mul_sum]
      rw [abs_of_pos (inv_pos.mpr (hMpos j)), inv_mul_le_iff₀ (hMpos j)]
      simpa using hzsum
  · intro i
    by_contra hcon
    push Not at hcon
    rw [map_smul, smul_eq_mul] at hcon
    have hs0 : 0 ≤ s i := by
      simp only [s]; exact div_nonneg (by linarith [hw0 i]) (Nat.cast_nonneg _)
    have hks : α i + (k i : ℝ) * s i = β i := by
      have : (k i : ℝ) ≠ 0 := by have := hkpos i; positivity
      simp only [s, w]; field_simp; ring
    obtain ⟨t, htk, ht⟩ := exists_nat_near_grid (hkpos i) hs0 hcon.1 (hks ▸ hcon.2)
    let j : ι := ⟨i, ⟨t, htk⟩⟩
    have h1 : 1 ≤ |φ i (T z) - M * γ j| := hzℓ j
    have hMj := hMpos j
    have e : φ i (T z) - M * γ j = M * (M⁻¹ * φ i (T z) - γ j) := by
      field_simp
    rw [e, abs_mul, abs_of_pos hMj] at h1
    have hγ : γ j = α i + ((t : ℝ) + 1 / 2) * s i := rfl
    rw [hγ] at h1
    -- M * (s i / 2) < 1
    have hkpos' : (0 : ℝ) < k i := by have := hkpos i; positivity
    have hlt : M * (s i / 2) < 1 := by
      have : M * (s i / 2) = M * w i / k i := by simp only [s]; ring
      rw [this, div_lt_one hkpos']
      nlinarith [hkgt i, hw0 i]
    nlinarith [mul_le_mul_of_nonneg_left ht hMj.le]


/-- **Ball's plank theorem** for centrally symmetric convex bodies: if `K` is covered by finitely
many planks, the sum of their relative widths with respect to `K` is at least `1`. -/
theorem ball_plank_theorem
    {m : ℕ}
    (K : Set Rn)
    (hK : IsConvexBody K)
    (hsymm : IsCentrallySymmetric K)
    (P : Fin m → Plank n)
    (hcover : K ⊆ ⋃ i, (P i : Set Rn)) :
    1 ≤ ∑ i, relativeWidth K (P i) := by
  classical
  obtain ⟨c0, hc0⟩ := hsymm
  obtain ⟨hKc, hKconv, p, hp⟩ := hK
  set K0 : Set Rn := {x | c0 + x ∈ K} with hK0
  have hK0conv : Convex ℝ K0 := by
    intro a ha b hb α β hα hβ hab
    have := hKconv ha hb hα hβ hab
    show c0 + (α • a + β • b) ∈ K
    convert this using 1
    calc c0 + (α • a + β • b) = (α + β) • c0 + (α • a + β • b) := by rw [hab, one_smul]
      _ = α • (c0 + a) + β • (c0 + b) := by module
  have hK0neg : ∀ x ∈ K0, -x ∈ K0 := by
    intro x hx
    have := (hc0 _).mp hx
    show c0 + -x ∈ K
    convert this using 1
    module
  have hpK : p ∈ K := interior_subset hp
  have hq : p - c0 ∈ K0 := by show c0 + (p - c0) ∈ K; simpa using hpK
  have hK00 : (0 : Rn) ∈ K0 := by
    have := hK0conv hq (hK0neg _ hq) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    convert this using 1
    module
  have hK0c : IsCompact K0 := (Homeomorph.addLeft c0).isCompact_preimage.mpr hKc
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, Metric.ball (p - c0) ε ⊆ K0 := by
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
    refine ⟨ε, hε, fun x hx => hb ?_⟩
    show c0 + x ∈ Metric.ball p ε
    rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
    convert hx using 2
    abel
  have hsupp : ∀ i, ∃ v ∈ K0, 0 < ⟪v, (P i).normal⟫_ℝ ∧
      ∀ k ∈ K0, |⟪k, (P i).normal⟫_ℝ| ≤ ⟪v, (P i).normal⟫_ℝ := by
    intro i
    set u := (P i).normal
    obtain ⟨v, hv, hmax⟩ := hK0c.exists_isMaxOn ⟨0, hK00⟩
      (f := fun x : Rn => ⟪x, u⟫_ℝ) (by fun_prop : Continuous fun x : Rn => ⟪x, u⟫_ℝ).continuousOn
    have habs : ∀ k ∈ K0, |⟪k, u⟫_ℝ| ≤ ⟪v, u⟫_ℝ := by
      intro k hk
      have h1 : ⟪k, u⟫_ℝ ≤ ⟪v, u⟫_ℝ := hmax hk
      have h2 : ⟪-k, u⟫_ℝ ≤ ⟪v, u⟫_ℝ := hmax (hK0neg k hk)
      rw [inner_neg_left] at h2
      exact abs_le.mpr ⟨by linarith, h1⟩
    refine ⟨v, hv, ?_, habs⟩
    have hmem : p - c0 + (ε / 2) • u ∈ K0 := hball (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, (P i).normal_is_unit,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith)
    have h1 := abs_le.mp (habs _ hmem)
    have h2 := abs_le.mp (habs _ hq)
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      (P i).normal_is_unit] at h1
    norm_num at h1
    linarith [h1.1, h1.2, h2.1, h2.2]
  choose v hvK0 hvpos hvmax using hsupp
  set h : Fin m → ℝ := fun i => ⟪v i, (P i).normal⟫_ℝ with hh
  have hdw : ∀ i, directionalWidth K (P i).normal = 2 * h i := by
    intro i
    set u := (P i).normal
    have hG : IsGreatest ((fun x ↦ ⟪x, u⟫_ℝ) '' K) (⟪c0, u⟫_ℝ + h i) := by
      refine ⟨⟨c0 + v i, hvK0 i, by simp [h, u, inner_add_left]⟩, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      have := (abs_le.mp (hvmax i (x - c0) (show c0 + (x - c0) ∈ K by simpa using hx))).2
      rw [inner_sub_left] at this
      simp only [h]
      linarith
    have hL : IsLeast ((fun x ↦ ⟪x, u⟫_ℝ) '' K) (⟪c0, u⟫_ℝ - h i) := by
      refine ⟨⟨c0 + -v i, hK0neg _ (hvK0 i), by
        simp [h, u, inner_add_left, inner_neg_left, sub_eq_add_neg]⟩, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      have := (abs_le.mp (hvmax i (x - c0) (show c0 + (x - c0) ∈ K by simpa using hx))).1
      rw [inner_sub_left] at this
      simp only [h]
      linarith
    unfold directionalWidth
    rw [hG.csSup_eq, hL.csInf_eq]
    ring
  by_contra hlt
  push Not at hlt
  let φ : Fin m → (Rn →ₗ[ℝ] ℝ) := fun i => (h i)⁻¹ • (innerSL ℝ (P i).normal).toLinearMap
  have hφ : ∀ i x, φ i x = ⟪x, (P i).normal⟫_ℝ / h i := fun i x => by
    simp [φ, real_inner_comm, div_eq_inv_mul]
  obtain ⟨y, hy, hyout⟩ := exists_point_outside_normalized_planks hK0conv hK00 hK0neg φ v hvK0
    (fun i => by rw [hφ]; exact div_self (hvpos i).ne')
    (fun i => ((P i).lower - ⟪c0, (P i).normal⟫_ℝ) / h i)
    (fun i => ((P i).upper - ⟪c0, (P i).normal⟫_ℝ) / h i)
    (fun i => div_le_div_of_nonneg_right (by linarith [(P i).lower_le_upper]) (hvpos i).le)
    (by
      have heq : (∑ i : Fin m, (((P i).upper - ⟪c0, (P i).normal⟫_ℝ) / h i -
          ((P i).lower - ⟪c0, (P i).normal⟫_ℝ) / h i) / 2) = ∑ i, relativeWidth K (P i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have := (hvpos i).ne'
        simp only [relativeWidth, Plank.width, hdw i]
        field_simp
        ring
      rw [heq]
      exact hlt)
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (show c0 + y ∈ K from hy))
  have hi' : c0 + y ∈ Plank.carrier (P i) := hi
  obtain ⟨hl, hu⟩ := hi'
  rw [inner_add_left] at hl hu
  rcases hyout i with h1 | h1 <;> rw [hφ] at h1
  · rw [div_lt_div_iff_of_pos_right (hvpos i)] at h1; linarith
  · rw [div_lt_div_iff_of_pos_right (hvpos i)] at h1; linarith

end Planks

end PlankProblem

end
