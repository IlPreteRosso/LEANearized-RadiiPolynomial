/-
Lean 4.24.0-rc1 (arm64-apple-darwin), Mathlib4 (commit near 919e2972…)
Tip: run `lake exe cache get` once to prefetch Mathlib artifacts.
-/

import Mathlib

open scoped Topology
open Metric Set Filter

section RadiiPolynomial

/-
NormedAddCommGroup: A *normed* group is an additive group endowed with a norm for which `dist x y = ‖x - y‖` defines a *metric space structure*.

NormedSpace ℝ E: A normed space over the reals is a *vector space over the real numbers* equipped with a norm that satisfies the properties of a norm (non-negativity, definiteness, homogeneity, and triangle inequality).

CompleteSpace E: A *complete* space is a metric space in which every Cauchy sequence converges to a limit within the space.

⇒ E is a Banach space over ℝ.
-/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

#synth MetricSpace E

/--
Newton-like map `T x = x - A (f x)` on a Banach space.
f is the nonlinear map, A is an approximate inverse of its derivative at some point.

A more decipherable to put it is E is an commutative R-module and A is an R-module homomorphism.
-/
def T (f : E → E) (A : E →L[ℝ] E) (x : E) : E := x - A (f x)

/-
`closedBall x ε` is the set of all points `y` with `dist y x ≤ ε`
`S` returns a value of type `Set E`, which is the (collection of points in the) closed ball centered at `xBar` with radius `r`.
`Set E` is the type of all elements of `E`
-/
def S (xBar : E) (r : ℝ) : Set E := closedBall xBar r

/-- Radii-polynomial data (used nonneg of norm) -/
structure RadiiData : Type where
  Y0  : ℝ
  Z0  : ℝ
  Z2  : ℝ → ℝ
  Y0_nonneg : 0 ≤ Y0
  Z0_nonneg : 0 ≤ Z0
  Z2_nonneg : ∀ {r}, 0 < r → 0 ≤ Z2 r



namespace RadiiData

/--
Z(r) := Z₀ + Z₂(r)·r - (2.18)
-/
def Z_of_r (data : RadiiData) (r : ℝ) : ℝ := data.Z0 + (data.Z2 r) * r

/--
p(r) := Z₂(r) r² − (1 − Z₀) r + Y₀ = (Z(r) − 1) r + Y₀ - (2.17)
-/
def p (data : RadiiData) (r : ℝ) : ℝ :=
  (data.Z2 r) * r^2 - (1 - data.Z0) * r + data.Y0

/--
Rewrite `p(r)` using `Z(r)`
LEAN sees `data.p r` as `RadiiData.p data r`,
where RadiiData is the namespace and data is an instance of type RadiiData
Just a notation trick. Won't work if the names are not the same
-/
lemma p_rewrite (data : RadiiData) (r : ℝ) :
    data.p r = (data.Z_of_r r - 1) * r + data.Y0 := by
  dsimp [p, Z_of_r]
  ring

/--
From `p(r) < 0` and `r>0` we get `Z(r) < 1` and `Z(r)·r + Y₀ ≤ r` - (2.13)
The second statement connects to the norm bound through Mean Value Theorem
-/
lemma p_lt_conds {data : RadiiData} {r : ℝ}
    (rpos : 0 < r) (hp : data.p r < 0) :
    let Prop1 := data.Z_of_r r < 1; let Prop2 := (data.Z_of_r r) * r + data.Y0 ≤ r;
    Prop1 ∧ Prop2 := by
  -- rewrite proposition hp using p(r) = (Z(r) − 1) r + Y₀ (expand the ineq)
  rw [p_rewrite] at hp
  -- From `hp : (Z(r) - 1) * r + Y0 < 0`, we get `hp1: Z(r) * r + Y0 < r`
  -- have hp1 : (data.Z_of_r r) * r + data.Y0 < r := by linarith [hp]
  -- Below is a more explicit proof of the same fact
  have hp1 : (data.Z_of_r r) * r + data.Y0 < r := by
    -- The `calc` block shows the steps explicitly.
    calc
      (data.Z_of_r r) * r + data.Y0 = ((data.Z_of_r r - 1) * r + data.Y0) + r := by ring
      _ < 0 + r := by linarith [hp]
      _ = r := by ring

  /-
  `constructor` splits the goal (Prop 1 ∧ Prop 2) into two subgoals, corresponding to the two parts of the conjunction.
  · `data.Z_of_r r < 1`,
  · `(data.Z_of_r r) * r + data.Y0 ≤ r`.
  -/
  constructor
  · -- Prove `Z(r) < 1`
    -- Have `(Z(r) - 1) * r < 0` and we know `r > 0`
    have h_Y0_nonneg : 0 ≤ data.Y0 := data.Y0_nonneg
    have hZr : (data.Z_of_r r - 1) * r < 0 := by linarith [hp, h_Y0_nonneg]
    -- A product is negative, and one factor is positive, so the other must be negative.
    have h_lt_one : data.Z_of_r r - 1 < 0 := by
      -- Prove this by contradiction.
      -- If `Z(r) ≥ 1 ⇒ Z(r) - 1 ≥ 0`, since `r > 0`, their product must be `≥ 0`.
      -- This contradicts `hZr: (Z(r) - 1) * r < 0`.
      by_contra h_not_lt
      have h_nonneg : 0 ≤ data.Z_of_r r - 1 := by linarith [h_not_lt]
      have h_prod_nonneg := mul_nonneg h_nonneg rpos.le
      -- `h_prod_nonneg` contradicts `hZr`.
      linarith [h_prod_nonneg, hZr]
    -- The goal `data.Z_of_r r < 1` is equivalent to `data.Z_of_r r - 1 < 0`.
    linarith [h_lt_one]

  · -- Prove `(data.Z_of_r r) * r + data.Y0 ≤ r`
    exact le_of_lt hp1


end RadiiData



/-- Mapping-into-ball certificate using the residual/lipschitz bounds. -/
theorem T_maps_ball_into_itself
    (f : E → E) (A : E →L[ℝ] E) (xBar : E) (r : ℝ) (data : RadiiData)
    (hfC1 : DifferentiableOn ℝ f (S xBar r))
    (rpos : 0 < r)
    (hY0 : ‖A (f xBar)‖ ≤ data.Y0)
    (hZ0 : ‖(ContinuousLinearMap.id ℝ E - A.comp (fderiv ℝ f xBar))‖ ≤ data.Z0)
    (hZ2 : ∀ c ∈ S xBar r,
      ‖A.comp (fderiv ℝ f c - fderiv ℝ f xBar)‖ ≤ (data.Z2 r) * r)
    (hrad : (data.Z_of_r r) * r + data.Y0 ≤ r) :
    MapsTo (T f A) (S xBar r) (S xBar r) := by
  intro x hx
  -- Standard “insert linearization + MVT on convex ball + triangle” bound:
  have : ‖T f A x - xBar‖ ≤ (data.Z_of_r r) * r + data.Y0 := by
    /- Sketch:
       T x - xBar = (x - xBar) - A(f x - f xBar) - A(f xBar).
       Add/subtract (Id - A ∘ f' xBar)(x - xBar) and use:
         ‖Id - A ∘ f' xBar‖ ≤ Z0,
         sup_{c in ball} ‖A ∘ (f' c - f' xBar)‖ ≤ Z2(r) r,
         ‖A(f xBar)‖ ≤ Y0,
       then mean value inequality on the convex ball to bound the remainder.
    -/
    sorry
  have hx' : dist (T f A x) xBar ≤ r := by
    have : (data.Z_of_r r) * r + data.Y0 ≤ r := hrad
    exact (le_trans (by simpa [dist_eq_norm] using this) this)
  simpa [S] using (mem_closedBall.2 hx')

/-- Lipschitz (contraction) of `T` on the ball with constant `Z(r)`. -/
theorem T_lipschitz_on_ball
    (f : E → E) (A : E →L[ℝ] E) (xBar : E) (r : ℝ) (data : RadiiData)
    (hfC1 : DifferentiableOn ℝ f (S xBar r))
    (hZ0 : ‖(ContinuousLinearMap.id ℝ E - A.comp (fderiv ℝ f xBar))‖ ≤ data.Z0)
    (hZ2 : ∀ c ∈ S xBar r,
      ‖A.comp (fderiv ℝ f c - fderiv ℝ f xBar)‖ ≤ (data.Z2 r) * r) :
    ∀ {x y}, x ∈ S xBar r → y ∈ S xBar r →
      dist (T f A x) (T f A y) ≤ (data.Z_of_r r) * dist x y := by
  intro x y hx hy
  /- As usual,
       ‖T x - T y‖ = ‖(Id - A∘f' xBar)(x - y) - A( (f x - f y) - f' xBar (x - y) )‖
     ≤ Z0 ‖x - y‖ + sup_{c∈ball} ‖A∘(f' c - f' xBar)‖ ‖x - y‖
     = (Z0 + Z2(r) r) ‖x - y‖.
  -/
  have : ‖T f A x - T f A y‖ ≤ (data.Z_of_r r) * ‖x - y‖ := by
    sorry
  simpa [dist_eq_norm] using this

/-- Existence & uniqueness of the fixed point in `closedBall xBar r`. -/
theorem radii_polynomial_fixed_point
    (f : E → E) (A : E →L[ℝ] E) (xBar : E) (r : ℝ) (data : RadiiData)
    (hfC1 : DifferentiableOn ℝ f (S xBar r))
    (rpos : 0 < r)
    (hY0 : ‖A (f xBar)‖ ≤ data.Y0)
    (hZ0 : ‖(ContinuousLinearMap.id ℝ E - A.comp (fderiv ℝ f xBar))‖ ≤ data.Z0)
    (hZ2 : ∀ c ∈ S xBar r,
      ‖A.comp (fderiv ℝ f c - fderiv ℝ f xBar)‖ ≤ (data.Z2 r) * r)
    (hp : data.p r < 0) :
    ∃! xTilde ∈ S xBar r, T f A xTilde = xTilde := by
  have S_complete : IsComplete (S xBar r) := isClosed_closedBall.isComplete
  have ⟨hKlt, hSelf⟩ := RadiiData.p_lt_conds (data := data) (r := r) rpos hp
  have hMap : MapsTo (T f A) (S xBar r) (S xBar r) :=
    T_maps_ball_into_itself f A xBar r data hfC1 rpos hY0 hZ0 hZ2 hSelf
  -- Build a contraction on the restricted map, with constant K := Z_of_r data r
  -- We avoid `ENNReal` by staying in the metric-space `dist` formulation.
  have hLip : ∀ {x y}, x ∈ S xBar r → y ∈ S xBar r →
      dist ((hMap.restrict (T f A) (S xBar r) (S xBar r)) x)
           ((hMap.restrict (T f A) (S xBar r) (S xBar r)) y)
      ≤ (data.Z_of_r r) * dist x y := by
    intro x y hx hy
    simpa [MapsTo.restrict, Function.comp] using
      T_lipschitz_on_ball f A xBar r data hfC1 hZ0 hZ2 hx hy
  -- Package the Lipschitz constant as `ContractingWith` (metric version).
  have hContr :
      ContractingWith (⟨data.Z_of_r r, by exact_mod_cast (le_of_lt hKlt)⟩)
        (hMap.restrict (T f A) (S xBar r) (S xBar r)) := by
    refine ⟨?Klt, ?Lip⟩
    · -- K < 1
      simpa using hKlt
    · -- LipschitzWith K
      intro x y; exact hLip
  classical
  -- Apply Banach fixed-point theorem on the complete subset S
  obtain ⟨xTilde, hTtildeS, hTtildefix, _conv, _bounds⟩ :=
    ContractingWith.exists_fixedPoint' (α := E)
      (K := ⟨data.Z_of_r r, by exact_mod_cast (le_of_lt hKlt)⟩)
      (f := T f A) (s := S xBar r) S_complete hMap hContr
      (x := xBar) (hxs := by simpa [S] using mem_closedBall_self rpos.le)
      (hx := by simpa using edist_ne_top xBar (T f A xBar))
  -- Uniqueness of fixed point in S
  refine ⟨xTilde, hTtildeS, hTtildefix, ?uniq⟩
  intro y hyS hyfix
  -- Standard uniqueness under contraction (or use `fixedPoint_unique'`).
  -- I’ll appeal to the uniqueness lemma:
  have := ContractingWith.fixedPoint_unique' (α := E)
      (K := ⟨data.Z_of_r r, by exact_mod_cast (le_of_lt hKlt)⟩)
      (f := hMap.restrict (T f A) (S xBar r) (S xBar r)) hContr
      (x := ⟨xTilde, hTtildeS⟩) (y := ⟨y, hyS⟩)
  -- Convert `IsFixedPt` on the restricted map:
  have hTtilde' : IsFixedPt (hMap.restrict (T f A) (S xBar r) (S xBar r)) ⟨xTilde, hTtildeS⟩ := by
    simpa [MapsTo.restrict] using (show T f A xTilde = xTilde from hTtildefix)
  have hy' : IsFixedPt (hMap.restrict (T f A) (S xBar r) (S xBar r)) ⟨y, hyS⟩ := by
    simpa [MapsTo.restrict] using (show T f A y = y from hyfix)
  have : ⟨xTilde, hTtildeS⟩ = ⟨y, hyS⟩ := this hTtilde' hy'
  simpa using congrArg Subtype.val this

end RadiiPolynomial
