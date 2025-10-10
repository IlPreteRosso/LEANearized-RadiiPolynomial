import Mathlib.Analysis.Calculus.Deriv.Mul


open scoped Topology BigOperators
open Metric Set Filter ContinuousLinearMap


/-
NormedAddCommGroup: A *normed* group is an additive group endowed with a norm for which `dist x y = ‖x - y‖` defines a *metric space structure*.

NormedSpace ℝ E: A normed space over the reals is a *vector space over the real numbers* equipped with a norm that satisfies the properties of a norm (non-negativity, definiteness, homogeneity, and triangle inequality).

CompleteSpace E: A *complete* space is a metric space in which every Cauchy sequence converges to a limit within the space.

⇒ E is a Banach space over ℝ.
-/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Nontrivial E]

abbrev I := ContinuousLinearMap.id ℝ E


/--
Newton-like map `T x = x - A (f x)` on a Banach space.
From equation (2.7) in the informal proof.
- `f` is the nonlinear map whose zeros we seek
- `A` is a linear operator (approximate inverse of Df at some point)
-/
def NewtonLikeMap (f : E → E) (A : E →L[ℝ] E) (x : E) : E := x - A (f x)

/--
`closedBall x ε` is the set of all points `y` with `dist y x ≤ ε`.
This defines the domain where we'll prove T is a contraction.
-/
def WorkingDomain (xBar : E) (r : ℝ) : Set E := closedBall xBar r



section NeumannSeries
omit [CompleteSpace E] in
/--
First lemma: nth powers norm submultiplicativity
of the operator norm.
-/
lemma norm_pow_le_pow_norm (X : E →L[ℝ] E) (n : ℕ) :
  ‖X ^ n‖ ≤ ‖X‖ ^ n := by
  induction n with
  | zero =>
    -- Base case: ‖X^0‖ = ‖I‖ = 1 = ‖X‖^0
    calc
      ‖X ^ 0‖
        -- Can I do rw here instead of simp???????
        = ‖ContinuousLinearMap.id ℝ E‖ := by simp [pow_zero]
      -- Since E is nontrivial, we have ‖I‖ = 1
      _ = 1                            := by rw [ContinuousLinearMap.norm_id]
      _ = ‖X‖ ^ 0                      := by rw [pow_zero]
      _ ≤ ‖X‖ ^ 0                      := by exact le_rfl

  | succ m _ =>
    -- Inductive step: use submultiplicativity ‖A B‖ ≤ ‖A‖ ‖B‖
    calc ‖X ^ (m + 1)‖ = ‖X ^ m * X‖ := by rw [pow_succ]
      _ ≤ ‖X ^ m‖ * ‖X‖ := by
        -- ContinuousLinearMap forms a normed algebra where norm is submultiplicative
        -- The standard lemma for this is norm_mul_le
        exact norm_mul_le (X ^ m) X
      _ ≤ ‖X‖ ^ m * ‖X‖ := by
        gcongr
      _ = ‖X‖ ^ (m + 1) := by
        rw [pow_succ]



omit [CompleteSpace E] in
/--
Second lemma: If ‖X‖ < 1, then the series ∑ ‖X^n‖ is summable.
This follows by comparison with the geometric series ∑ ‖X‖^n.
-/
lemma norm_series_summable_of_norm_lt_one {X : E →L[ℝ] E} (h : ‖X‖ < 1) :
  Summable (fun n : ℕ => ‖X ^ n‖) := by
  -- First, get the geometric series to converge
  -- Since ‖X‖ is a nonnegative real, we can use it directly
  haveI h_geometric : Summable (fun n : ℕ => (‖X‖ : ℝ) ^ n) := by
    -- Apply the geometric series test
    rw [summable_geometric_iff_norm_lt_one]
    -- ‖X‖ is already nonnegative, so ‖‖X‖‖ = ‖X‖
    simp only [norm_norm]
    exact h
    -- simpa
    -- simpa using h
  -- Now use comparison: ‖X^n‖ ≤ ‖X‖^n
  refine Summable.of_nonneg_of_le ?_ (norm_pow_le_pow_norm X) h_geometric
  -- Show each term is nonnegative (norms are always nonnegative)
  intro n
  exact norm_nonneg _



/--
Third lemma: If ‖X‖ < 1, then the operator series ∑ X^n is summable
in the Banach space of continuous linear maps.
This uses the completeness of the space.
-/
lemma operator_series_summable_of_norm_lt_one {X : E →L[ℝ] E} (h : ‖X‖ < 1) :
  Summable (fun n : ℕ => X ^ n) := by
  -- In a Banach space, absolute convergence implies convergence
  -- `Summable.of_norm` turns goal from `Summable (X^n)` to `Summable (‖X^n‖)`.
  apply Summable.of_norm
  exact norm_series_summable_of_norm_lt_one h



/--
Helper definition: The Neumann series sum S = ∑ X^n exists when ‖X‖ < 1.
This sum will be shown to be the inverse of (I - X).
-/
noncomputable def neumannSeriesSum {X : E →L[ℝ] E} (h : ‖X‖ < 1) : E →L[ℝ] E :=
  haveI : Summable (fun n : ℕ => X ^ n) :=
    operator_series_summable_of_norm_lt_one h
  -- `∑' i, f i` is the sum of f if it exists and is unconditionally convergent, or 0 otherwise.
  ∑' n : ℕ, X ^ n



omit [CompleteSpace E] [Nontrivial E] in
/--
Finite telescoping: (I - X) ∘ (∑_{n=0}^{N-1} X^n) = I - X^N
-/
lemma finite_telescoping {X : E →L[ℝ] E} (N : ℕ) :
  (I - X).comp (∑ n ∈ Finset.range N, X ^ n) =
   I - X ^ N := by
  -- Prove equality of linear maps by showing they agree on all inputs
  ext x
  simp

  calc
    -- WTS: ((I - X) ∘ S) x = (I - X) (S x)
    -- where S = ∑_{n=0}^{N-1} X^n.
    -- Distribute X over the sum using linearity: X(∑X^n x) = ( ∑X^{n+1} x )
    ∑ n ∈ Finset.range N, (X ^ n) x - ∑ x_1 ∈ Finset.range N, X ((X ^ x_1) x) =
    (∑ n ∈ Finset.range N, X ^ n) x - (∑ n ∈ Finset.range N, X ^ (n + 1)) x := by
        -- The first term is unchanged, removed from the goal by `congr 1` (`rfl`)
        congr 1
        -- Move X inside the sum
        simp only [coe_sum', Finset.sum_apply]
        -- Rewrite X ∘ (X^n) as X^{n+1}
        haveI {n : ℕ} {x : E}: X ((X ^ n) x) = (X ^ (n + 1)) x := by
          rw [pow_succ', ← comp_apply]
          rfl
        simp [this]

    -- The telescoping: ∑_{n=0}^{N-1} X^n x - ∑_{n=0}^{N-1} X^{n+1} x = x - X^N x
    _ = x - (X ^ N) x := by
        have telescope : ∀ M : ℕ,
          ∑ n ∈ Finset.range M, (X ^ n) x - ∑ n ∈ Finset.range M, (X ^ (n + 1)) x =
          (X ^ 0) x - (X ^ M) x := by
          intro M
          induction M with
          | zero      => simp
          | succ k ih =>
            -- break down a sum over k+1 terms into
            -- a sum over k terms plus the final term
            rw [Finset.sum_range_succ, Finset.sum_range_succ]
            simp only [pow_zero, one_apply]
            calc
              (∑ n ∈ Finset.range k, (X ^ n) x) + (X ^ k) x -
              ((∑ n ∈ Finset.range k, (X ^ (n + 1)) x) +
              (X ^ (k + 1)) x)
              = (∑ n ∈ Finset.range k, (X ^ n) x) -
                (∑ n ∈ Finset.range k, (X ^ (n + 1)) x) +
                ((X ^ k) x - (X ^ (k + 1)) x)
              := by abel
              _ = ((X ^ 0) x - (X ^ k) x) + ((X ^ k) x - (X ^ (k + 1)) x)
                := by rw [ih]
              _ = (X ^ 0) x - (X ^ (k + 1)) x
                := by abel

        simp [telescope N]



-- Partial sum convergence: ∀ ε > 0, ∃ N, ∀ n ≥ N: ‖S_n - S‖ < ε
lemma h_partial {X : E →L[ℝ] E} (h : ‖X‖ < 1) : ∀ ε > 0, ∃ N, ∀ n ≥ N,
  ‖(∑ k ∈ Finset.range n, X ^ k) - ∑' k, X ^ k‖ < ε := by
  intro ε hε
  have h_summable := operator_series_summable_of_norm_lt_one h
  -- `HasSum.tendsto_sum_nat` :
  -- (fun n => ∑ i in Finset.range n, f i) tends to a as n → ∞
  have := h_summable.hasSum.tendsto_sum_nat
  -- `Metric.tendsto_atTop` :
  -- expands the definition of `tendsto` using ε/δ language w/ a distance function
  rw [Metric.tendsto_atTop] at this
  exact this ε hε

-- Power vanishing: ‖X‖ < 1 ⟹ ‖X^n‖ ≤ ‖X‖^n → 0
omit [CompleteSpace E] in
lemma h_zero_lim {X : E →L[ℝ] E} (h : ‖X‖ < 1) : ∀ ε > 0, ∃ N, ∀ n ≥ N, ‖X ^ n‖ < ε := by
  intro ε hε
  -- `atTop` is the filter representing the limit `→ ∞` on an ordered set
  -- `Tendsto` : {α β : Type*} → (α → β) → Filter α → Filter β → Prop
  /-
  `α = ℕ` (domain type)
  `β = ℝ` (codomain type)
  `f = (fun n => ‖X‖ ^ n)` (the function)
  `l₁ = atTop` (filter on ℕ representing "as n → ∞")
  `l₂ = (𝓝 0)` (filter on ℝ representing "neighborhoods of 0")
  -/
  have h_geom : @Tendsto ℕ ℝ (fun n => ‖X‖ ^ n) atTop (𝓝 0) :=
    -- have `h: ‖X‖ < 1`, `norm_nonneg X : 0 ≤ ‖X‖`
    -- `Tendsto.pow_atTop_nhds_zero_of_lt_one` : `‖X‖^n` tends to 0 as n → ∞
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg X) h

  -- Again expand `tendsto` into ε/δ language
  rw [Metric.tendsto_atTop] at h_geom
  -- `h_geom` : ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (‖X‖ ^ n) 0 < ε
  -- `h_geom ε hε` : ∃ N, ∀ n ≥ N, dist (‖X‖ ^ n) 0 < ε
  -- `obtain ⟨N, hN⟩ := h_geom ε hε` : extracts the *witness* `N` and the property `hN` from the existential quantifier
  -- where `hN` is ∀ n ≥ N, dist (‖X‖ ^ n) 0 < ε
  -- In human language,
  -- `obtain` extracts variables from an existing hypothesis
  -- `intro` introduces new variables from the goal
  obtain ⟨N, hN⟩ := h_geom ε hε
  -- `use N` : chooses the witness `N` for the existential quantifier in the goal
  use N
  intro n hn
  -- Debug: Check what hN n hn produces
  have debug_result := hN n hn
  calc ‖X ^ n‖ ≤ ‖X‖ ^ n := by exact norm_pow_le_pow_norm X n
      _ < ε :=
      by simpa using hN n hn



/-
**Telescoping Left Identity for Neumann Series**

Goal: (I - X) ∘ (∑_{n=0}^∞ X^n) = I when ‖X‖ < 1.

Proof: Contradiction via ‖(I - X) ∘ S - I‖ = 0, using finite telescoping
(I - X) ∘ (∑_{n=0}^{N-1} X^n) = I - X^N and limits X^N → 0, S_N → S.
-/
lemma telescoping_left {X : E →L[ℝ] E} (h : ‖X‖ < 1) :
  (I - X).comp (neumannSeriesSum h) =
  I := by
  -- S = ∑_{n=0}^∞ X^n
  unfold neumannSeriesSum
  simp only [sub_comp]
  -- If ‖X‖ < 1, then the operator series ∑ X^n is summable in the Banach space of continuous linear maps
  have h_summable := operator_series_summable_of_norm_lt_one h

  -- -- ‖(I - X) ∘ S - I‖ = 0 ↔ (I - X) ∘ S - I = 0
  -- suffices ‖(I - X).comp (∑' n, X ^ n) - ContinuousLinearMap.id ℝ E‖ = 0 by
  --   have : (I - X).comp (∑' n, X ^ n) - I = 0 :=
  --     -- ‖x‖ = 0 ↔ x = 0
  --     norm_eq_zero.mp this
  --   exact eq_of_sub_eq_zero this
  -- -- Rewrite the goal from ‖·‖ = 0 to · = 0
  -- rw [norm_eq_zero]

  -- ‖(I - X) ∘ S - I‖ = 0 ↔ (I - X) ∘ S - I = 0
  suffices (I - X).comp (∑' n, X ^ n) - I = 0 by
    exact eq_of_sub_eq_zero this

  -- Proof by contradiction
  -- Turn the goal into (I - X) ∘ S - I ≠ 0
  by_contra h_nonzero
  have h_pos : 0 < ‖(I - X).comp (∑' n, X ^ n) - ContinuousLinearMap.id ℝ E‖ := by
    -- `norm_pos_iff` : ‖x‖ > 0 ↔ x ≠ 0
    -- `rwa` is a combination of `rw` and `assumption`
    -- Equivalently we may write
    -- rw [norm_pos_iff]
    -- exact h_nonzero
    rwa [norm_pos_iff]

  -- Set ε := ‖(I - X) ∘ S - I‖ / 3; derive 3ε ≤ 2ε for contradiction
  set ε := ‖(I - X).comp (∑' n, X ^ n) - ContinuousLinearMap.id ℝ E‖ / 3
  have hε_pos : 0 < ε := by
    unfold ε
    -- `div_pos` : a/b > 0 if a > 0 and b > 0
    apply div_pos h_pos
    -- norm_num also works
    linarith

  -- Choose N s.t. ‖S_N - S‖ small and ‖X^N‖ small
  -- `specialize` plugs in specific values into a universally quantified hypothesis
  -- `div_pos` : a/b > 0 if a > 0 and b > 0
  -- `hε_pos` : 0 < ε
  -- `lt_max_of_lt_right zero_lt_one` : {a b c : α} (h : a < c) : a < max b c
  -- which yields 0 < max ‖I-X‖ 1
  set ε' := ε / max ‖ContinuousLinearMap.id ℝ E - X‖ 1
  have h_partial_local := h_partial h ε' (div_pos hε_pos (lt_max_of_lt_right zero_lt_one))
  have h_zero_lim_local := h_zero_lim h ε hε_pos
  obtain ⟨N₁, hN₁⟩ := h_partial_local -- hN₁ : ∀ n ≥ N₁, ‖S_N - S‖ < ε/(max ‖I-X‖ 1)
  obtain ⟨N₂, hN₂⟩ := h_zero_lim_local -- hN₂ : ∀ n ≥ N₂, ‖X^N‖ < ε

  set N := max N₁ N₂
  have h_approx := hN₁ N (le_max_left _ _)   -- ‖S_N - S‖ < ε/(max ‖I-X‖ 1)
  have h_small := hN₂ N (le_max_right _ _)    -- ‖X^N‖ < ε

  -- 3ε = ‖(I - X) ∘ S - I‖
  have : 3 * ε = ‖(I - X).comp (∑' n, X ^ n) - ContinuousLinearMap.id ℝ E‖ := by
    unfold ε
    field_simp

  -- Main inequality: 3ε ≤ 2ε via triangle inequality and telescoping
  have h_ineq : 3 * ε ≤ 2 * ε := by
    calc 3 * ε = ‖(I - X).comp (∑' n, X ^ n) - ContinuousLinearMap.id ℝ E‖
              := by exact this
        -- ‖A - C‖ ≤ ‖A - B‖ + ‖B - C‖ where A = (I-X)∘S, B = (I-X)∘S_N, C = I
        _ ≤ ‖(I - X).comp (∑' n, X ^ n) -
              (I - X).comp (∑ n ∈ Finset.range N, X ^ n)‖ +
            ‖(I - X).comp (∑ n ∈ Finset.range N, X ^ n) -
              ContinuousLinearMap.id ℝ E‖ := by
          have h_tri : ∀ (x y z : E →L[ℝ] E), ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
            intros x y z
            calc ‖x - z‖ = ‖(x - y) + (y - z)‖ := by abel_nf
                  _ ≤ ‖x - y‖ + ‖y - z‖ := by exact norm_add_le _ _
          exact h_tri _ _ _
        -- Linearity: (I-X)∘(S - S_N); finite telescoping: (I-X)∘S_N = I - X^N
        _ = ‖(I - X).comp ((∑' n, X ^ n) - ∑ n ∈ Finset.range N, X ^ n)‖ +
            ‖ContinuousLinearMap.id ℝ E - X ^ N - ContinuousLinearMap.id ℝ E‖ := by
          -- `comp_sub` : f.comp (g - h) = f.comp g - f.comp h
          rw [←comp_sub, finite_telescoping N]
        -- Submultiplicativity: ‖A ∘ B‖ ≤ ‖A‖ · ‖B‖; ‖-X^N‖ = ‖X^N‖
        _ ≤ ‖ContinuousLinearMap.id ℝ E - X‖ * ‖(∑' n, X ^ n) - ∑ n ∈ Finset.range N, X ^ n‖ +
            ‖X ^ N‖ := by
          gcongr
            -- `opNorm_comp_le` : ‖f ∘ g‖ ≤ ‖f‖ · ‖g‖
          · exact ContinuousLinearMap.opNorm_comp_le _ _
            -- `norm_neg` : ‖-x‖ = ‖x‖
          · simp [norm_neg]
        -- Apply convergence bounds: ‖S - S_N‖ < ε/(max ‖I-X‖ 1), ‖X^N‖ < ε
        _ ≤ ‖ContinuousLinearMap.id ℝ E - X‖ *
            (ε / max ‖ContinuousLinearMap.id ℝ E - X‖ 1) +
            ε := by
          gcongr
          · rw [norm_sub_rev]
            exact le_of_lt h_approx
        -- ‖I-X‖ · (ε/max ‖I-X‖ 1) ≤ ε
        _ ≤ ε + ε := by
          -- cancels the ε from both sides
          gcongr
          -- ‖I - X‖ * (ε / max ‖I - X‖ 1) ≤ ε
          calc ‖ContinuousLinearMap.id ℝ E - X‖ * (ε / max ‖ContinuousLinearMap.id ℝ E - X‖ 1)
              ≤ max ‖ContinuousLinearMap.id ℝ E - X‖ 1 * (ε / max ‖ContinuousLinearMap.id ℝ E - X‖ 1) := by
                -- change the goal to · ≤ max · ·
                gcongr
                exact le_max_left _ _
            _ = ε := by
              field_simp
        _ = 2 * ε := by ring

  -- The fact are we are contradicting
  have : 3 * ε > 2 * ε := by
    linarith [hε_pos]

  linarith [h_ineq, this]




/--
**Commutativity of Neumann Series**: (I - X) ∘ S = S ∘ (I - X) where S = ∑_{n=0}^∞ X^n.

Proof: Both sides equal the identity by telescoping_left, hence they're equal.
-/
lemma neumann_comm {X : E →L[ℝ] E} {N : ℕ} (h : ‖X‖ < 1) :
  (I - X).comp (neumannSeriesSum h) =
  (neumannSeriesSum h).comp (I - X) := by
  -- unfold neumannSeriesSum
  have h_summable := operator_series_summable_of_norm_lt_one h
  simp only [sub_comp, id_comp, comp_sub, comp_id, sub_right_inj]

  -- Turn operator = zero to norm = zero in the goal
  suffices ‖X.comp (neumannSeriesSum h) - (neumannSeriesSum h).comp X‖ = 0 by
    haveI : X.comp (neumannSeriesSum h) - (neumannSeriesSum h).comp X = 0 :=
      norm_eq_zero.mp this
    exact eq_of_sub_eq_zero this


  -- Rewrite goal to apply `rw h_parts`, which implcicitly rewrite it back
  -- have goal_rewrite : ‖X ((∑' (n : ℕ), X ^ n) x) - (∑' (n : ℕ), X ^ n) (X x)‖ =
  --                  ‖X ((neumannSeriesSum h) x) - (neumannSeriesSum h) (X x)‖ := by
  --   unfold neumannSeriesSum
  --   rfl
  -- rw [goal_rewrite]

  -- Break series into partial sums + tail, unfold `neumannSeriesSum`
  -- uses `{N : ℕ}`
  have h_parts : neumannSeriesSum h =
    (∑ n ∈ Finset.range N, X ^ n) +
    (∑' n : ℕ, X ^ (n + N)) := by
    unfold neumannSeriesSum
    -- (∑ i ∈ range k, f i) + ∑' i, f (i + k) = ∑' i, f i
    rw [← h_summable.sum_add_tsum_nat_add N]
    -- Or equivalently
    -- exact (hSummable.sum_add_tsum_nat_add N).symm
  rw [h_parts]


  have X_commutes_with_powers {X : E →L[ℝ] E} (n : ℕ) (x : E) :
    X ((X ^ n) x) = (X ^ n) (X x) := by
    induction n with
    | zero => simp [pow_zero]
    | succ m ih =>
      simp only [pow_succ', coe_mul, Function.comp_apply]
      rw [ih]

  -- First lift your pointwise lemma to operator level
  have X_comm_pow_op : ∀ n : ℕ, X.comp (X ^ n) = (X ^ n).comp X := by
    intro n
    ext x
    exact X_commutes_with_powers n x


  haveI : X.comp (∑ n ∈ Finset.range N, X ^ n + ∑' (n : ℕ), X ^ (n + N)) -
    (∑ n ∈ Finset.range N, X ^ n + ∑' (n : ℕ), X ^ (n + N)).comp X =
      X.comp (∑ n ∈ Finset.range N, X ^ n) + X.comp (∑' (n : ℕ), X ^ (n + N)) -
      ((∑ n ∈ Finset.range N, X ^ n).comp X + (∑' (n : ℕ), X ^ (n + N)).comp X) := by
    rw [comp_add, add_comp]
  rw [this]

  haveI : X.comp (∑ n ∈ Finset.range N, X ^ n) + X.comp (∑' (n : ℕ), X ^ (n + N)) -
    ((∑ n ∈ Finset.range N, X ^ n).comp X + (∑' (n : ℕ), X ^ (n + N)).comp X) =
      (X.comp (∑ n ∈ Finset.range N, X ^ n) - (∑ n ∈ Finset.range N, X ^ n).comp X) +
      (X.comp (∑' (n : ℕ), X ^ (n + N)) - (∑' (n : ℕ), X ^ (n + N)).comp X) := by
    abel
  rw [this]

  -- Step 3: Show each difference is zero
  haveI : X.comp (∑ n ∈ Finset.range N, X ^ n) - (∑ n ∈ Finset.range N, X ^ n).comp X = 0 := by
    rw [comp_finset_sum, finset_sum_comp]
    simp_rw [sub_eq_zero]
    ext x
    simp only [coe_sum', Finset.sum_apply, comp_apply]
    -- Use your X_commutes_with_powers lemma
    simp only [X_commutes_with_powers]
  rw [this]
  simp only [zero_add]

  -- convert the goal back
  rw [norm_eq_zero]


  have h_summable_shifted : Summable fun n => X ^ (n + N) := by
    -- The tail of a summable series is summable
    rw [summable_nat_add_iff N]
    exact h_summable

  ext x

  -- Need pointwise summability for x
  have h_summable_shifted_x : Summable (fun n => (X ^ (n + N)) x) := by
    apply Summable.of_norm
    -- Just use that ‖X^(n+N) x‖ ≤ ‖X‖^(n+N) ‖x‖
    have h_bound : ∀ n, ‖(X ^ (n + N)) x‖ ≤ ‖X‖ ^ (n + N) * ‖x‖ := fun n =>
      calc ‖(X ^ (n + N)) x‖
        ≤ ‖X ^ (n + N)‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖X‖ ^ (n + N) * ‖x‖ := by gcongr; exact norm_pow_le_pow_norm X (n + N)

    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_bound
    -- The geometric series ∑ ‖X‖^(n+N) * ‖x‖ is summable
    have : Summable fun n => ‖X‖ ^ (n + N) * ‖x‖ := by
      apply Summable.mul_right
      -- Cloude kept using `← summable_nat_add_iff N` instead of `summable_nat_add_iff N` ..confusing
      rw [summable_nat_add_iff N]
      rw [summable_geometric_iff_norm_lt_one]
      simpa using h
    exact this

  -- Goal ⊢ ∑' (n : ℕ), (X ^ (n + N)) (X x) = (∑' (n : ℕ), X ^ (n + N)) (X x)
  simp only [comp_apply, sub_apply, zero_apply]


  have h_step1 : X (∑' n, (X ^ (n + N)) x) = ∑' n, X ((X ^ (n + N)) x) := by
        -- Use HasSum.map for continuous linear maps
        have h_hassum := h_summable_shifted_x.hasSum
        have h_mapped := h_hassum.map X (ContinuousLinearMap.continuous X)
        exact h_mapped.tsum_eq.symm

  have h_step2 : ∑' n, X ((X ^ (n + N)) x) = ∑' n, (X ^ (n + N)) (X x) := by
      congr 1
      ext n
      exact X_commutes_with_powers (n + N) x

  have h_summable : Summable (fun n => X ^ n) :=
      operator_series_summable_of_norm_lt_one (X := X) h

  have h_summable_shifted : Summable (fun n => X ^ (n + N)) :=
    (summable_nat_add_iff N).2 h_summable

  -- evaluate the operator-valued tsum at x using the evaluation CLM, not `.apply`
  have h_eval :
    ((∑' n, X ^ (n + N)) : E →L[ℝ] E) x
      = ∑' n, (X ^ (n + N)) x :=
    (ContinuousLinearMap.map_tsum
      (φ := ContinuousLinearMap.apply (𝕜 := ℝ) (E := E) (Fₗ := E) x)
      (hf := h_summable_shifted))

  have tsum_apply_op :
  (∑' n, X ^ (n + N)) x = ∑' n, (X ^ (n + N)) x := by
    -- goal is just “lhs − rhs = 0”
    rw [h_eval]
    -- simp only [sub_self]

  have h_summable_alias {X : E →L[ℝ] E} (h : ‖X‖ < 1): Summable (fun n => X ^ n) :=
      operator_series_summable_of_norm_lt_one (X := X) h

  have h_summable_shifted_alias {X : E →L[ℝ] E} (h : ‖X‖ < 1): Summable (fun n => X ^ (n + N)) := by
    -- The tail of a summable series is summable
    rw [summable_nat_add_iff N]
    exact h_summable_alias h

  have h_eval_alias {X : E →L[ℝ] E} {x : E} (h : ‖X‖ < 1):
    ((∑' n, X ^ (n + N)) : E →L[ℝ] E) x
      = ∑' n, (X ^ (n + N)) x :=
    (ContinuousLinearMap.map_tsum
      (φ := ContinuousLinearMap.apply (𝕜 := ℝ) (E := E) (Fₗ := E) x)
      (hf := h_summable_shifted_alias h))

  have tsum_apply_op_alias {X : E →L[ℝ] E} {x : E} (h : ‖X‖ < 1):
    (∑' n, X ^ (n + N)) x = ∑' n, (X ^ (n + N)) x := by
    rw [h_eval_alias h]

  -- rw [sub_eq_zero] at tsum_apply_op
  rw [sub_eq_zero]
  -- Now the calculation works
  calc X ((∑' n, X ^ (n + N)) x)
      = X (∑' n, (X ^ (n + N)) x) := by rw [tsum_apply_op]
      _ = ∑' n, X ((X ^ (n + N)) x) := ContinuousLinearMap.map_tsum X h_summable_shifted_x
      _ = ∑' n, (X ^ (n + N)) (X x) := by
        -- Explicitly provide X when using X_commutes_with_powers
        congr 1
      _ = (∑' n, X ^ (n + N)) (X x) := by
        -- `{X : E →L[ℝ] E} {x : E} (h : ‖X‖ < 1)` in `tsum_apply_op` allows us to use it here
        rw [tsum_apply_op_alias h]



-- Not used, also defined inline in `neumann_comm`
-- Key lemma: X commutes with its powers
omit [CompleteSpace E] [Nontrivial E] in
lemma X_commutes_with_powers {X : E →L[ℝ] E} (n : ℕ) (x : E) :
  X ((X ^ n) x) = (X ^ n) (X x) := by
  induction n with
  | zero => simp [pow_zero]
  | succ m ih =>
    simp only [pow_succ', coe_mul, Function.comp_apply]
    rw [ih]

-- Not used
lemma tail_series_small {X : E →L[ℝ] E} (h : ‖X‖ < 1) (ε : ℝ) (hε : 0 < ε) :
  ∃ N : ℕ, ∀ n ≥ N, ‖∑' (k : ℕ), X ^ (k + n)‖ < ε := by
  -- The series ∑ X^k is summable
  have h_summable := operator_series_summable_of_norm_lt_one h

  -- Key insight: ∑' k, X^(k+n) = ∑' j, X^j - ∑_{k=0}^{n-1} X^k
  -- As n → ∞, the finite sum ∑_{k=0}^{n-1} X^k → ∑' k, X^k
  -- Therefore the tail ∑' k, X^(k+n) → 0

  -- Use the convergence of partial sums to the infinite sum
  have h_conv : Tendsto (fun n => ∑ k ∈ Finset.range n, X ^ k) atTop (𝓝 (∑' k, X ^ k)) :=
    h_summable.hasSum.tendsto_sum_nat

  -- This means the tail gets arbitrarily small
  rw [Metric.tendsto_atTop] at h_conv
  obtain ⟨N, hN⟩ := h_conv ε hε

  use N
  intro n hn

  -- Key equality: tail series = total series - partial sum
  have tail_eq : ∑' (k : ℕ), X ^ (k + n) = ∑' k, X ^ k - ∑ k ∈ Finset.range n, X ^ k := by
    rw [← h_summable.sum_add_tsum_nat_add n]
    abel

  rw [tail_eq]
  -- hN gives us: dist (∑ k ∈ Finset.range n, X ^ k) (∑' k, X ^ k) < ε
  -- We need: ‖∑' k, X ^ k - ∑ k ∈ Finset.range n, X ^ k‖ < ε
  rw [norm_sub_rev]  -- Flip the order to match hN
  exact hN n hn



lemma telescoping_right {X : E →L[ℝ] E} {N : ℕ} (h : ‖X‖ < 1) :
  (neumannSeriesSum h).comp (I - X) =
  I := by
  rw [← neumann_comm (N:=N) h]
  exact telescoping_left h



/--
**Main Neumann Series Theorem (IsUnit version)**

If `‖I - B‖ < 1` for a continuous linear map B on a Banach space, then `B` is a unit (invertible).
We construct the unit explicitly using the Neumann series as the inverse.
-/
theorem isUnit_of_norm_sub_id_lt_one {B : E →L[ℝ] E} {N : ℕ}
  (h : ‖I - B‖ < 1) :
  IsUnit B := by
  classical
  -- set `X := id - B`; the inverse will be `S := ∑ X^n`, and `B = id - X`
  set X := (I - B)
  have hX : ‖X‖ < 1 := by simpa [X]
  have hB : B = I - X := by
    simp only [sub_sub_cancel, X]
  -- Candidate inverse:
  let S := neumannSeriesSum hX
  -- Show left/right inverse identities using the telescoping lemmas.
  have hL : (I - X).comp S = I := by
    simpa using telescoping_left (X := X) hX
  have hR : S.comp (I - X) = I := by
    simpa using telescoping_right (X := X) (N := N) hX
  -- Build a `Units` structure explicitly.
  refine ⟨⟨B, S, ?_, ?_⟩, rfl⟩
  · -- `B * S = 1` (multiplication is composition)
    -- `hL : (id - X) ∘ S = id`, and `B = id - X`.
    -- Convert composition equality to `*` equality.
    -- `ext` to compare as maps.
    have : (B.comp S) = (I) := by simpa [hB]
      using hL
    -- turn equality of maps into equality of elements in the monoid
    simpa using this
  · -- `S * B = 1`
    have : (S.comp B) = (I) := by
      simpa [hB] using hR
    simpa using this

/--
Alternative version with explicit inverse construction
-/
theorem invertible_of_norm_sub_id_lt_one {B : E →L[ℝ] E} {N : ℕ}
  (h : ‖(1 : E →L[ℝ] E) - B‖ < 1) :
  ∃ (B_inv : E →L[ℝ] E),
    B * B_inv = 1 ∧ B_inv * B = 1 := by
  have hu := isUnit_of_norm_sub_id_lt_one h (N:=N)
  obtain ⟨u, rfl⟩ := hu
  exact ⟨u.inv, u.val_inv, u.inv_val⟩



omit [Nontrivial E] in
theorem isUnit_of_norm_sub_id_lt_one_LEAN_built_in {B : E →L[ℝ] E}
  (h : ‖I - B‖ < 1) :
  IsUnit B := by
  have eq : B = I - (I - B) := by
    ext x
    simp only [sub_sub_cancel]
  rw [eq]
  exact isUnit_one_sub_of_norm_lt_one h

end NeumannSeries
