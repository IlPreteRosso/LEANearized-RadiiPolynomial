import RadiiPolynomial.SystemTaylorODE.ScaledReal
import RadiiPolynomial.SystemTaylorODE.CauchyProduct
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Weighted sequence-space infrastructure for `SystemTaylorODE`

This file provides the concrete weighted spaces used by the system-level API:
- `lpWeighted ν p`
- `l1Weighted ν`
- norm/membership bridge lemmas (`norm_eq_tailTsum_of_fin_zero`, `tailTsum_le_norm_of_eq`, `norm_mk_le_of_pointwise`)
- finite weighted matrix norms and array-backed column formulas
- coefficient truncation for the `Setup82.SeqModel` backend
-/

open scoped BigOperators Topology NNReal ENNReal Matrix

noncomputable section

namespace SystemTaylorODE

/-- Weighted `ℓᵖ` space realized as `lp` with scaled fibers. -/
abbrev lpWeighted (ν : PosReal) (p : ℝ≥0∞) := lp (ScaledReal ν) p

/-- Weighted `ℓ¹` specialization. -/
abbrev l1Weighted (ν : PosReal) := lpWeighted ν 1

namespace lpWeighted

variable {ν : PosReal} {p : ℝ≥0∞}

instance instUniformSpace [Fact (1 ≤ p)] : UniformSpace (lpWeighted ν p) := by
  change UniformSpace (lp (ScaledReal ν) p)
  infer_instance

instance instCompleteSpace [Fact (1 ≤ p)] : CompleteSpace (lpWeighted ν p) := by
  change CompleteSpace (lp (ScaledReal ν) p)
  infer_instance

/-- Underlying real sequence. -/
def toSeq (a : lpWeighted ν p) : ℕ → ℝ := fun n => ScaledReal.toReal (a n)

/-- Extensionality through coefficients. -/
lemma ext {a b : lpWeighted ν p} (h : ∀ n, toSeq a n = toSeq b n) : a = b :=
  lp.ext (funext h)

/-- Membership predicate for weighted `ℓᵖ`. -/
def Mem (ν : PosReal) (p : ℝ≥0∞) (a : ℕ → ℝ) : Prop :=
  Memℓp (fun n => ScaledReal.ofReal (a n) : ∀ n, ScaledReal ν n) p

/-- Construct an element from a sequence with finite weighted norm. -/
def mk (a : ℕ → ℝ) (ha : Mem ν p a) : lpWeighted ν p :=
  ⟨fun n => ScaledReal.ofReal (a n), ha⟩

@[simp] lemma toSeq_apply (a : lpWeighted ν p) (n : ℕ) : toSeq a n = a n := rfl
@[simp] lemma mk_apply (a : ℕ → ℝ) (ha : Mem ν p a) (n : ℕ) : toSeq (mk a ha) n = a n := rfl
@[simp] lemma zero_toSeq (n : ℕ) : toSeq (0 : lpWeighted ν p) n = 0 := rfl
@[simp] lemma neg_toSeq (a : lpWeighted ν p) (n : ℕ) : toSeq (-a) n = -toSeq a n := rfl
@[simp] lemma add_toSeq (a b : lpWeighted ν p) (n : ℕ) : toSeq (a + b) n = toSeq a n + toSeq b n := rfl
@[simp] lemma sub_toSeq (a b : lpWeighted ν p) (n : ℕ) : toSeq (a - b) n = toSeq a n - toSeq b n := rfl
@[simp] lemma smul_toSeq (c : ℝ) (a : lpWeighted ν p) (n : ℕ) : toSeq (c • a) n = c * toSeq a n := rfl

lemma norm_eq_tsum_rpow (hp : 0 < p.toReal) (a : lpWeighted ν p) :
    ‖a‖ = (∑' n, (|toSeq a n| * (ν : ℝ) ^ n) ^ p.toReal) ^ (1 / p.toReal) := by
  rw [lp.norm_eq_tsum_rpow hp]
  simp only [one_div, toSeq_apply]
  rfl

lemma mem_iff_summable (hp : 0 < p.toReal) (a : ℕ → ℝ) (hp' : p ≠ ⊤) :
    Mem ν p a ↔ Summable (fun n => (|a n| * (ν : ℝ) ^ n) ^ p.toReal) := by
  simp only [Mem, Memℓp, ScaledReal.ofReal_apply, ne_eq]
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp
  simp only [hp0, hp', ↓reduceIte, ScaledReal.norm_def, ScaledReal.toReal_apply]

end lpWeighted

namespace l1Weighted

variable {ν : PosReal}

instance : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩

abbrev toSeq (a : l1Weighted ν) := lpWeighted.toSeq a

lemma norm_eq_tsum (a : l1Weighted ν) :
    ‖a‖ = ∑' n, |toSeq a n| * (ν : ℝ) ^ n := by
  have h := lpWeighted.norm_eq_tsum_rpow (ν := ν)
    (p := (1 : ℝ≥0∞)) (by norm_num : 0 < (1 : ℝ≥0∞).toReal) a
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one] at h
  exact h

lemma norm_eq_Icc_sum_of_support (a : l1Weighted ν) (M : ℕ)
    (hsupp : ∀ n, M < n → lpWeighted.toSeq a n = 0) :
    ‖a‖ = ∑ n ∈ Finset.Icc 0 M, |toSeq a n| * (ν : ℝ) ^ n := by
  rw [norm_eq_tsum]
  refine tsum_eq_sum ?_
  intro n hn
  simp only [Finset.mem_Icc, not_and_or, not_le] at hn
  have hzero : lpWeighted.toSeq a n = 0 := hsupp n (by omega)
  simpa [lpWeighted.toSeq] using hzero

lemma mem_iff (a : ℕ → ℝ) :
    lpWeighted.Mem ν 1 a ↔ Summable (fun n => |a n| * (ν : ℝ) ^ n) := by
  have h := @lpWeighted.mem_iff_summable ν 1 (by norm_num : 0 < (1 : ℝ≥0∞).toReal) a ENNReal.one_ne_top
  simp only [ENNReal.toReal_one, Real.rpow_one] at h
  exact h

/-- Finite weighted prefix bound:
the first `N+1` weighted terms are bounded by the full `ℓ¹_ν` norm. -/
lemma finSum_weighted_toSeq_le_norm (a : l1Weighted ν) (N : ℕ) :
    ∑ k : Fin (N + 1), |toSeq a k| * (ν : ℝ) ^ (k : ℕ) ≤ ‖a‖ := by
  have hsum : Summable (fun n => |toSeq a n| * (ν : ℝ) ^ n) := by
    exact (mem_iff (ν := ν) (a := toSeq a)).mp a.2
  have hrange :
      ∑ n ∈ Finset.range (N + 1), |toSeq a n| * (ν : ℝ) ^ n ≤
        ∑' n, |toSeq a n| * (ν : ℝ) ^ n := by
    exact hsum.sum_le_tsum (Finset.range (N + 1))
      (by
        intro n hn
        exact mul_nonneg (abs_nonneg _) (pow_nonneg ν.coe_nonneg _))
  have hleft :
      ∑ k : Fin (N + 1), |toSeq a k| * (ν : ℝ) ^ (k : ℕ) =
        ∑ n ∈ Finset.range (N + 1), |toSeq a n| * (ν : ℝ) ^ n := by
    exact Fin.sum_univ_eq_sum_range (fun n => |toSeq a n| * (ν : ℝ) ^ n) (N + 1)
  exact (hleft.trans_le hrange).trans_eq (norm_eq_tsum (ν := ν) a).symm

/-- Norm splitting: `‖a‖ = ∑_{n ∈ range k} f(n) + ∑' n, f(n+k)` where `f(n) = |a_n| ν^n`.
Used for finite/tail decomposition of block-diagonal operators (Exercise 2.7.2). -/
lemma norm_eq_finRangeSum_add_tailTsum (a : l1Weighted ν) (k : ℕ) :
    ‖a‖ = ∑ n ∈ Finset.range k, |toSeq a n| * (ν : ℝ) ^ n +
      ∑' n, |toSeq a (n + k)| * (ν : ℝ) ^ (n + k) := by
  rw [norm_eq_tsum]
  exact (((mem_iff (ν := ν) (a := toSeq a)).mp a.2).sum_add_tsum_nat_add k).symm

/-- If `toSeq a n = 0` for `n < k`, then `‖a‖` equals the tail tsum from index `k`. -/
lemma norm_eq_tailTsum_of_fin_zero (a : l1Weighted ν) (k : ℕ)
    (hfin : ∀ n, n < k → toSeq a n = 0) :
    ‖a‖ = ∑' n, |toSeq a (n + k)| * (ν : ℝ) ^ (n + k) := by
  rw [norm_eq_finRangeSum_add_tailTsum a k]
  have h_zero : ∑ n ∈ Finset.range k, |toSeq a n| * (ν : ℝ) ^ n = 0 :=
    Finset.sum_eq_zero fun n hn => by
      rw [hfin n (Finset.mem_range.mp hn)]; simp
  rw [h_zero, zero_add]

/-- If tail coefficients of `a` match `b` from index `k`, then `tail_tsum(a, k) ≤ ‖b‖`. -/
lemma tailTsum_le_norm_of_eq (a b : l1Weighted ν) (k : ℕ)
    (heq : ∀ n, k ≤ n → toSeq a n = toSeq b n) :
    ∑' n, |toSeq a (n + k)| * (ν : ℝ) ^ (n + k) ≤ ‖b‖ := by
  have h_eq : ∀ n, |toSeq a (n + k)| = |toSeq b (n + k)| :=
    fun n => by rw [heq _ (by omega)]
  simp_rw [h_eq]
  rw [norm_eq_finRangeSum_add_tailTsum b k]
  linarith [Finset.sum_nonneg (fun n (_ : n ∈ Finset.range k) =>
    mul_nonneg (abs_nonneg (toSeq b n)) (pow_nonneg ν.coe_nonneg n))]

/-- Pointwise-dominated norm bound: if `|f n| ≤ C * |toSeq a n|`,
then `‖mk f hf‖ ≤ C * ‖a‖`. -/
lemma norm_mk_le_of_pointwise (f : ℕ → ℝ) (hf : lpWeighted.Mem ν 1 f)
    (a : l1Weighted ν) (C : ℝ) (hle : ∀ n, |f n| ≤ C * |toSeq a n|) :
    ‖lpWeighted.mk f hf‖ ≤ C * ‖a‖ := by
  rw [norm_eq_tsum, norm_eq_tsum, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun n =>
    calc |f n| * (ν : ℝ) ^ n
        ≤ C * |toSeq a n| * (ν : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (hle n) (pow_nonneg ν.coe_nonneg n)
      _ = C * (|toSeq a n| * (ν : ℝ) ^ n) := by ring)
    ((mem_iff f).mp hf) (((mem_iff (toSeq a)).mp a.2).mul_left C)

/-- Sequence with value `x` at index `n` and zero elsewhere. -/
def single (n : ℕ) (x : ℝ) : l1Weighted ν :=
  lpWeighted.mk (fun k => if k = n then x else 0) (by
    rw [mem_iff]
    have h : (fun k => |if k = n then x else 0| * (ν : ℝ) ^ k) =
        fun k => if k = n then |x| * (ν : ℝ) ^ n else 0 := by
      ext k
      split_ifs with hk <;> simp [hk]
    rw [h]
    exact summable_of_ne_finset_zero (s := {n}) (fun k hk => by simp at hk; simp [hk]))

@[simp] lemma single_toSeq_self (n : ℕ) (x : ℝ) :
    toSeq (single n x : l1Weighted ν) n = x := by
  simp [single, lpWeighted.mk]

@[simp] lemma single_toSeq_ne (n k : ℕ) (x : ℝ) (h : k ≠ n) :
    toSeq (single n x : l1Weighted ν) k = 0 := by
  simp [single, lpWeighted.mk, h]

lemma norm_single (n : ℕ) (x : ℝ) :
    ‖(single n x : l1Weighted ν)‖ = |x| * (ν : ℝ) ^ n := by
  rw [norm_eq_tsum]
  have h : (fun k => |toSeq (single n x : l1Weighted ν) k| * (ν : ℝ) ^ k) =
      fun k => if k = n then |x| * (ν : ℝ) ^ n else 0 := by
    ext k
    split_ifs with hk <;> simp [hk, single, lpWeighted.mk]
  rw [h, tsum_ite_eq]

section FiniteNorms

variable {N : ℕ}

/-- Finite weighted `ℓ¹` norm on `Fin (N+1)`. -/
def finl1WeightedNorm (ν : ℝ≥0) (x : Fin (N + 1) → ℝ) : ℝ :=
  ∑ n : Fin (N + 1), |x n| * (ν : ℝ) ^ (n : ℕ)

/-- Weighted matrix column norm. -/
def matrixColNorm (ν : PosReal)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (j : Fin (N + 1)) : ℝ :=
  (1 / (ν : ℝ) ^ (j : ℕ)) * ∑ i : Fin (N + 1), |A i j| * (ν : ℝ) ^ (i : ℕ)

/-- Finite weighted matrix norm: max of weighted column norms. -/
def finWeightedMatrixNorm (ν : PosReal)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (fun j => matrixColNorm ν A j)

lemma weighted_term_nonneg (a : ℝ) (n : ℕ) : 0 ≤ |a| * (ν : ℝ) ^ n :=
  mul_nonneg (abs_nonneg _) (pow_nonneg ν.coe_nonneg _)

lemma matrixColNorm_nonneg (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (j : Fin (N + 1)) :
    0 ≤ matrixColNorm ν A j := by
  unfold matrixColNorm
  apply mul_nonneg
  · exact div_nonneg zero_le_one (pow_nonneg ν.coe_nonneg _)
  · exact Finset.sum_nonneg (fun _ _ => weighted_term_nonneg _ _)

lemma finWeightedMatrixNorm_nonneg (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    0 ≤ finWeightedMatrixNorm ν A := by
  apply Finset.le_sup'_of_le _ (Finset.mem_univ 0)
  exact matrixColNorm_nonneg (ν := ν) A 0

@[simp]
lemma matrixColNorm_mul_pow (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (j : Fin (N + 1)) :
    matrixColNorm ν A j * (ν : ℝ) ^ (j : ℕ) =
      ∑ i : Fin (N + 1), |A i j| * (ν : ℝ) ^ (i : ℕ) := by
  rw [matrixColNorm]
  field_simp [pow_ne_zero _ (PosReal.coe_ne_zero ν)]

/-- Weighted matrix/mulVec estimate in finite dimensions:
`‖Mv‖_{1,ν} ≤ ‖M‖_{1,ν} ‖v‖_{1,ν}` in expanded finite-sum form. -/
lemma finWeightedMatrixNorm_mulVec_le
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (v : Fin (N + 1) → ℝ) :
    ∑ n : Fin (N + 1), |∑ k : Fin (N + 1), A n k * v k| * (ν : ℝ) ^ (n : ℕ) ≤
      finWeightedMatrixNorm ν A * ∑ k : Fin (N + 1), |v k| * (ν : ℝ) ^ (k : ℕ) := by
  have h₁ :
      ∑ n : Fin (N + 1), |∑ k : Fin (N + 1), A n k * v k| * (ν : ℝ) ^ (n : ℕ) ≤
        ∑ n : Fin (N + 1), (∑ k : Fin (N + 1), |A n k| * |v k|) * (ν : ℝ) ^ (n : ℕ) := by
    refine Finset.sum_le_sum ?_
    intro n _
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg ν.coe_nonneg _)
    exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp_rw [abs_mul])
  have h₂ :
      ∑ n : Fin (N + 1), (∑ k : Fin (N + 1), |A n k| * |v k|) * (ν : ℝ) ^ (n : ℕ) =
        ∑ k : Fin (N + 1), ∑ n : Fin (N + 1), |A n k| * |v k| * (ν : ℝ) ^ (n : ℕ) := by
    simp_rw [Finset.sum_mul]
    exact Finset.sum_comm
  have h₃ :
      ∑ k : Fin (N + 1), ∑ n : Fin (N + 1), |A n k| * |v k| * (ν : ℝ) ^ (n : ℕ) =
        ∑ k : Fin (N + 1), |v k| * ∑ n : Fin (N + 1), |A n k| * (ν : ℝ) ^ (n : ℕ) := by
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n _
    ring
  have h₄ :
      ∑ k : Fin (N + 1), |v k| * ∑ n : Fin (N + 1), |A n k| * (ν : ℝ) ^ (n : ℕ) =
        ∑ k : Fin (N + 1), |v k| * (matrixColNorm ν A k * (ν : ℝ) ^ (k : ℕ)) := by
    simp only [matrixColNorm_mul_pow]
  have h₅ :
      ∑ k : Fin (N + 1), |v k| * (matrixColNorm ν A k * (ν : ℝ) ^ (k : ℕ)) ≤
        finWeightedMatrixNorm ν A * ∑ k : Fin (N + 1), |v k| * (ν : ℝ) ^ (k : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro k _
    have hcol :
        matrixColNorm ν A k * (ν : ℝ) ^ (k : ℕ) ≤
          finWeightedMatrixNorm ν A * (ν : ℝ) ^ (k : ℕ) := by
      exact mul_le_mul_of_nonneg_right
        (Finset.le_sup' (f := fun j : Fin (N + 1) => matrixColNorm ν A j) (Finset.mem_univ k))
        (pow_nonneg ν.coe_nonneg _)
    exact (mul_le_mul_of_nonneg_left hcol (abs_nonneg _)).trans_eq (mul_left_comm _ _ _)
  have h₃₄ :
      ∑ k : Fin (N + 1), ∑ n : Fin (N + 1), |A n k| * |v k| * (ν : ℝ) ^ (n : ℕ) =
        ∑ k : Fin (N + 1), |v k| * (matrixColNorm ν A k * (ν : ℝ) ^ (k : ℕ)) := by
    exact h₃.trans h₄
  have h₂₃₄ :
      ∑ n : Fin (N + 1), (∑ k : Fin (N + 1), |A n k| * |v k|) * (ν : ℝ) ^ (n : ℕ) =
        ∑ k : Fin (N + 1), |v k| * (matrixColNorm ν A k * (ν : ℝ) ^ (k : ℕ)) := by
    exact h₂.trans h₃₄
  exact h₁.trans (h₂₃₄.trans_le h₅)

lemma finWeightedMatrixNorm_le_of_matrixColNorm_le
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (C : ℝ)
    (hcol : ∀ j : Fin (N + 1), matrixColNorm ν A j ≤ C) :
    finWeightedMatrixNorm ν A ≤ C := by
  unfold finWeightedMatrixNorm
  exact Finset.sup'_le Finset.univ_nonempty (fun j => matrixColNorm ν A j) (by
    intro j _
    exact hcol j)

lemma matrixColNorm_eq (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (j : Fin (N + 1)) :
    matrixColNorm ν A j =
      (∑ i : Fin (N + 1), |A i j| * (ν : ℝ) ^ (i : ℕ)) / (ν : ℝ) ^ (j : ℕ) := by
  unfold matrixColNorm
  ring

lemma matrixColNorm_eq_sum_div (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (j : Fin (N + 1)) :
    matrixColNorm ν A j =
      ∑ i : Fin (N + 1), |A i j| * (ν : ℝ) ^ (i : ℕ) / (ν : ℝ) ^ (j : ℕ) := by
  rw [matrixColNorm_eq, Finset.sum_div]

/-- Array-backed finite column formula over `Icc 0 N`. -/
noncomputable def arrayColNormIccSum (ν : PosReal) (N : ℕ)
    (col : Array ℚ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (0 : ℕ) N,
    |(col.getD k 0 : ℝ)| * (ν : ℝ) ^ k / (ν : ℝ) ^ j

lemma matrixColNorm_eq_arrayColNormIccSum
    (ν : PosReal) (N : ℕ)
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (col : Array ℚ) (j : Fin (N + 1))
    (hM : ∀ i : Fin (N + 1), M i j = ((col).getD (i : ℕ) 0 : ℝ)) :
    matrixColNorm ν M j = arrayColNormIccSum ν N col j := by
  rw [matrixColNorm_eq_sum_div, arrayColNormIccSum]
  simp_rw [hM]
  rw [Fin.sum_univ_eq_sum_range
    (f := fun k => |(col.getD k 0 : ℝ)| * (ν : ℝ) ^ k / (ν : ℝ) ^ (j : ℕ))]
  have hRange : Finset.range (N + 1) = Finset.Icc (0 : ℕ) N := by
    simpa [Nat.add_sub_cancel] using
      (Nat.range_eq_Icc_zero_sub_one (n := N + 1) (Nat.succ_ne_zero N))
  rw [hRange]

lemma matrixColNorm_le_of_arrayColNormIccSum
    (ν : PosReal) (N : ℕ)
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (col : Array ℚ) (j : Fin (N + 1)) (C : ℝ)
    (hM : ∀ i : Fin (N + 1), M i j = ((col).getD (i : ℕ) 0 : ℝ))
    (hcol : arrayColNormIccSum ν N col j ≤ C) :
    matrixColNorm ν M j ≤ C := by
  rw [matrixColNorm_eq_arrayColNormIccSum ν N M col j hM]
  exact hcol

end FiniteNorms

section Truncation

/-- Coefficient truncation at order `N` in `ℓ¹_ν`. -/
def trunc (N : ℕ) (a : l1Weighted ν) : l1Weighted ν :=
  lpWeighted.mk (fun n => if n ≤ N then lpWeighted.toSeq a n else 0) (by
    rw [mem_iff]
    have h : (fun n => |(if n ≤ N then lpWeighted.toSeq a n else 0 : ℝ)| * (ν : ℝ) ^ n) =
        fun n => if n ≤ N then |lpWeighted.toSeq a n| * (ν : ℝ) ^ n else 0 := by
      ext n
      split_ifs with hn
      · simp
      · simp
    rw [h]
    exact summable_of_ne_finset_zero (s := Finset.Icc 0 N) (fun n hn => by
      have hnot : ¬ n ≤ N := by
        intro hle
        exact hn (by simp [Finset.mem_Icc, hle])
      simp [hnot]))

lemma coeff_trunc (N : ℕ) (a : l1Weighted ν) (n : ℕ) :
    lpWeighted.toSeq (trunc N a) n = if n ≤ N then lpWeighted.toSeq a n else 0 := by
  simp [trunc, lpWeighted.mk]

end Truncation

end l1Weighted

end SystemTaylorODE
