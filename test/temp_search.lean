import Mathlib

-- Try different approach: use tsum_eq_sum directly on the subtype
-- The subtype {n : ℕ // N < n} is the index type, and we need
-- a Finset of that subtype.

-- Approach: tsum_eq_sum on the subtype directly
example (N M : ℕ) (f : ℕ → ℝ) (hM : N < M)
    (hf : ∀ n, M < n → f n = 0) :
    ∑' (n : {n : ℕ // N < n}), f ↑n = ∑ n ∈ Finset.Icc (N + 1) M, f n := by
  -- Use tsum_subtype with exact, then tsum_eq_sum
  have h1 : ∑' (n : {n : ℕ // N < n}), f ↑n = ∑' n, (Set.Ioi N).indicator f n :=
    tsum_subtype (Set.Ioi N) f
  rw [h1]
  rw [tsum_eq_sum (s := Finset.Icc (N + 1) M)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Set.indicator_apply, Set.mem_Ioi]
    split_ifs with h
    · rfl
    · omega
  · intro n hn
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    simp only [Set.indicator_apply, Set.mem_Ioi]
    split_ifs with h
    · cases hn with
      | inl h2 => omega
      | inr h2 => exact hf n h2
    · rfl
