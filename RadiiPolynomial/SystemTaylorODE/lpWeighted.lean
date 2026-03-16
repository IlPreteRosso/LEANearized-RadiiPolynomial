import RadiiPolynomial.SystemTaylorODE.ScaledReal
import RadiiPolynomial.SystemTaylorODE.CauchyProduct
import RadiiPolynomial.SystemTaylorODE.NormHelpers
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Weighted sequence-space infrastructure for `SystemTaylorODE`

This file provides the concrete weighted spaces used by the system-level API:
- `lpWeighted ν p`
- `l1Weighted ν`
- norm/membership bridge lemmas (`norm_eq_tailTsum_of_fin_zero`, `tailTsum_le_norm_of_eq`, `norm_mk_le_of_pointwise`)
- finite weighted matrix norms and array-backed column formulas
- coefficient truncation
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

/-- Bridge: the `lp` coercion of `mk` gives `ScaledReal.ofReal ∘ f` at each index.
Useful for `simp_rw` when the goal has `↑(mk f hf) n` instead of `toSeq`. -/
@[simp] lemma mk_val_apply (a : ℕ → ℝ) (ha : Mem ν p a) (n : ℕ) :
    (mk a ha).val n = ScaledReal.ofReal (a n) := rfl
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

/-- Direct summability of weighted terms for `a ∈ ℓ¹_ν`.
Avoids the `(mem_iff _).mp a.2` pattern and ensures the result uses `toSeq` (not raw `.1`). -/
lemma summable_weighted (a : l1Weighted ν) :
    Summable (fun n => |toSeq a n| * (ν : ℝ) ^ n) :=
  (mem_iff (toSeq a)).mp a.2

/-- Coordinate evaluation `toSeq · n` as a CLM on `l1Weighted ν`.
`|toSeq a n| ≤ ν⁻ⁿ · ‖a‖` since `|a_n| · ν^n ≤ ‖a‖`. -/
noncomputable def toSeq_CLM (n : ℕ) : l1Weighted ν →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun a => toSeq a n
      map_add' := fun a b => by simp
      map_smul' := fun r a => by simp }
    ((ν : ℝ) ^ n)⁻¹
    (fun a => by
      have hle : |toSeq a n| * (ν : ℝ) ^ n ≤ ‖a‖ := by
        rw [norm_eq_tsum]
        exact (summable_weighted a).le_tsum n (fun k _ =>
          mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _))
      calc |toSeq a n| = |toSeq a n| * (ν : ℝ) ^ n * ((ν : ℝ) ^ n)⁻¹ := by
            rw [mul_inv_cancel_right₀ (pow_ne_zero _ ν.2.ne')]
        _ ≤ ‖a‖ * ((ν : ℝ) ^ n)⁻¹ := by
            exact mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr (pow_nonneg ν.2.le _))
        _ = ((ν : ℝ) ^ n)⁻¹ * ‖a‖ := mul_comm _ _)

/-- `toSeq · n` is differentiable (it's a CLM). -/
@[fun_prop]
lemma differentiable_toSeq (n : ℕ) : Differentiable ℝ (fun a : l1Weighted ν => toSeq a n) :=
  (toSeq_CLM n).differentiable

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

/-- If `a` kills modes below `k` and matches `b` on modes ≥ `k`, then `‖a‖ ≤ ‖b‖`.
Combines `norm_eq_tailTsum_of_fin_zero` + `tailTsum_le_norm_of_eq`. -/
lemma norm_le_of_fin_zero_tail_eq (a b : l1Weighted ν) (k : ℕ)
    (hfin : ∀ n, n < k → toSeq a n = 0)
    (htail : ∀ n, k ≤ n → toSeq a n = toSeq b n) :
    ‖a‖ ≤ ‖b‖ :=
  (norm_eq_tailTsum_of_fin_zero a k hfin).symm ▸ tailTsum_le_norm_of_eq a b k htail

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

/-- Shifted weighted summability: if `b ∈ ℓ¹_ν`, then `Σ |b(n-1)| · ν^n` is summable.
Key identity: `Σ_{n≥1} |b_{n-1}| · ν^n = ν · Σ_m |b_m| · ν^m`. -/
lemma summable_shifted_weighted (b : l1Weighted ν) :
    Summable (fun n => |toSeq b (n - 1)| * (ν : ℝ) ^ n) := by
  rw [← summable_nat_add_iff (k := 1)]
  exact (summable_weighted b).mul_left (ν : ℝ) |>.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _))
    fun n => le_of_eq (by simp only [Nat.add_sub_cancel, pow_succ]; ring)

/-- Membership via eventual domination with shifted index.
If `|f(n)| ≤ |a(n)| + |b(n-1)|` for all sufficiently large `n`,
where `a, b ∈ ℓ¹_ν`, then `f ∈ ℓ¹_ν`. -/
lemma mem_of_eventually_le_add_shift (f : ℕ → ℝ) (a b : l1Weighted ν) (N : ℕ)
    (htail : ∀ n, N < n → |f n| ≤ |toSeq a n| + |toSeq b (n - 1)|) :
    lpWeighted.Mem ν 1 f := by
  rw [mem_iff]
  exact Summable.of_norm_bounded_eventually_nat
    (((summable_weighted a).add (summable_shifted_weighted b)).congr
      fun n => (add_mul ..).symm)
    (Filter.eventually_atTop.mpr ⟨N + 1, fun n hn => by
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (pow_nonneg ν.2.le _)]
      exact mul_le_mul_of_nonneg_right (htail n (by omega)) (pow_nonneg ν.2.le _)⟩)

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

@[simp] lemma single_toSeq (idx n : ℕ) (x : ℝ) :
    toSeq (single (ν := ν) idx x) n = if n = idx then x else 0 := by
  simp only [single, lpWeighted.mk_apply]

@[simp] lemma single_toSeq_self (n : ℕ) (x : ℝ) :
    toSeq (single n x : l1Weighted ν) n = x := by simp [single, lpWeighted.mk]
lemma single_toSeq_ne (n k : ℕ) (x : ℝ) (h : k ≠ n) :
    toSeq (single n x : l1Weighted ν) k = 0 := by simp [single, lpWeighted.mk, h]

lemma norm_single (n : ℕ) (x : ℝ) :
    ‖(single n x : l1Weighted ν)‖ = |x| * (ν : ℝ) ^ n := by
  rw [norm_eq_tsum]
  have h : (fun k => |toSeq (single n x : l1Weighted ν) k| * (ν : ℝ) ^ k) =
      fun k => if k = n then |x| * (ν : ℝ) ^ n else 0 := by
    ext k
    split_ifs with hk <;> simp [hk, single, lpWeighted.mk]
  rw [h, tsum_ite_eq]

/-- `single n` as a CLM: embeds `ℝ` into `ℓ¹_ν` at index `n`. -/
noncomputable def single_CLM (n : ℕ) : ℝ →L[ℝ] l1Weighted ν :=
  LinearMap.mkContinuous
    { toFun := single n
      map_add' := fun x y => by
        apply lpWeighted.ext; intro k
        simp only [single, lpWeighted.mk_apply, lpWeighted.add_toSeq]
        split_ifs <;> simp
      map_smul' := fun r x => by
        apply lpWeighted.ext; intro k
        simp only [single, lpWeighted.mk_apply, lpWeighted.smul_toSeq, RingHom.id_apply]
        split_ifs <;> simp [mul_comm] }
    ((ν : ℝ) ^ n)
    (fun x => by show ‖single n x‖ ≤ _; rw [norm_single, Real.norm_eq_abs, mul_comm])

/-- `toSeq` distributes over finite sums. -/
@[simp] lemma toSeq_finset_sum {ι : Type*} (s : Finset ι) (g : ι → l1Weighted ν) (n : ℕ) :
    toSeq (∑ i ∈ s, g i) n = ∑ i ∈ s, toSeq (g i) n := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => simp [Finset.sum_cons]

@[simp] lemma single_CLM_apply (n : ℕ) (x : ℝ) :
    (single_CLM (ν := ν) n) x = single n x := rfl

@[simp] lemma single_CLM_toSeq_self (n : ℕ) (x : ℝ) :
    toSeq (single_CLM (ν := ν) n x) n = x := single_toSeq_self n x

@[simp] lemma single_CLM_toSeq_ne (n k : ℕ) (x : ℝ) (h : k ≠ n) :
    toSeq (single_CLM (ν := ν) n x) k = 0 := single_toSeq_ne n k x h

/-- A finitely-supported function into `l1Weighted ν` is differentiable if each
coefficient function is differentiable. Decomposes as `Σ_k single_CLM k (f_k(a))`.
This is the key API for proving differentiability through `lpWeighted.mk`. -/
lemma differentiable_mk_of_finSupp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℕ → ℝ) (M : ℕ) (hsupp : ∀ a n, M < n → f a n = 0)
    (hf : ∀ a, lpWeighted.Mem ν 1 (f a))
    (hd : ∀ k : Fin (M + 1), Differentiable ℝ (fun a => f a k)) :
    Differentiable ℝ (fun a => lpWeighted.mk (f a) (hf a)) := by
  -- mk(f a) = Σ_k single_CLM k (f a k): both agree at each toSeq index.
  have hsum_eq : ∀ a, lpWeighted.mk (f a) (hf a) =
      ∑ k : Fin (M + 1), single_CLM (ν := ν) (k : ℕ) (f a k) := by
    intro a; apply lpWeighted.ext; intro n
    simp only [lpWeighted.mk_apply, toSeq_finset_sum, single_CLM_apply]
    simp only [single_toSeq]
    -- Goal: f a n = ∑ k : Fin (M+1), if n = ↑k then f a ↑k else 0
    by_cases hn : n ≤ M
    · -- Exactly one k has ↑k = n: the sum collapses to f a n
      rw [Finset.sum_eq_single ⟨n, by omega⟩
        (fun k _ hk => if_neg (by intro h; exact hk (Fin.ext h.symm)))
        (fun h => absurd (Finset.mem_univ _) h)]
      simp
    · -- n > M: no k has ↑k = n, so sum = 0 = f a n
      rw [hsupp a n (by omega)]
      exact (Finset.sum_eq_zero fun k _ => if_neg (by intro h; omega)).symm
  intro a; show DifferentiableAt ℝ (fun a => lpWeighted.mk (f a) (hf a)) a
  rw [show (fun a => lpWeighted.mk (f a) (hf a)) =
      fun a => ∑ k : Fin (M + 1), single_CLM (ν := ν) (↑k) (f a ↑k) from funext hsum_eq]
  exact DifferentiableAt.fun_sum fun (k : Fin (M + 1)) _ =>
    ((single_CLM (ν := ν) (↑k)).differentiable.comp (hd k)) a

/-- Fderiv of finitely-supported `lpWeighted.mk` vanishes on tail modes.
If `f a n = 0` for `n > M` and each `f · k` is differentiable, then
`toSeq((fderiv (mk ∘ f)) x h) n = 0` for `n > M`. -/
lemma fderiv_mk_of_finSupp_toSeq_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℕ → ℝ) (M : ℕ) (hsupp : ∀ a n, M < n → f a n = 0)
    (hf : ∀ a, lpWeighted.Mem ν 1 (f a))
    (hd : ∀ k : Fin (M + 1), Differentiable ℝ (fun a => f a k))
    (x h : E) (n : ℕ) (hn : M < n) :
    toSeq ((fderiv ℝ (fun a => lpWeighted.mk (f a) (hf a)) x) h) n = 0 := by
  -- The function is identically zero at mode n > M (since f a n = 0)
  -- So the coordinate function `a ↦ toSeq(mk(f a)) n` is constant 0
  have hzero_fn : (fun a => toSeq (lpWeighted.mk (f a) (hf a)) n) = fun _ => 0 :=
    funext fun a => by simp [lpWeighted.mk_apply, hsupp a n hn]
  -- fderiv of constant = 0
  have hfderiv_zero : (fderiv ℝ (fun a => toSeq (lpWeighted.mk (f a) (hf a)) n) x) h = 0 := by
    rw [hzero_fn]; simp
  -- Connect: toSeq((fderiv (mk ∘ f) x) h) n = fderiv(a ↦ toSeq(mk(f a)) n) x h
  have hchain : toSeq ((fderiv ℝ (fun a => lpWeighted.mk (f a) (hf a)) x) h) n =
      (fderiv ℝ (fun a => toSeq (lpWeighted.mk (f a) (hf a)) n) x) h := by
    have : (fun a => toSeq (lpWeighted.mk (f a) (hf a)) n) =
        ⇑(toSeq_CLM (ν := ν) n) ∘ (fun a => lpWeighted.mk (f a) (hf a)) := rfl
    rw [this, fderiv_comp x (toSeq_CLM n).differentiableAt
      (differentiable_mk_of_finSupp f M hsupp hf hd x),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv]; rfl
  rw [hchain, hfderiv_zero]

section FiniteNorms

variable {N : ℕ}

/-- Finite weighted `ℓ¹` norm on `Fin (N+1)`. -/
def finl1WeightedNorm (ν : ℝ≥0) (x : Fin (N + 1) → ℝ) : ℝ :=
  ∑ n : Fin (N + 1), |x n| * (ν : ℝ) ^ (n : ℕ)

/-- Weighted matrix column norm: `‖col_j(A)‖_{1,ν} / ν^j`. -/
def matrixColNorm (ν : PosReal)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (j : Fin (N + 1)) : ℝ :=
  finl1WeightedNorm (ν : ℝ≥0) (fun i => A i j) / (ν : ℝ) ^ (j : ℕ)

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
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => weighted_term_nonneg _ _))
    (pow_nonneg ν.coe_nonneg _)

lemma finWeightedMatrixNorm_nonneg (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    0 ≤ finWeightedMatrixNorm ν A := by
  apply Finset.le_sup'_of_le _ (Finset.mem_univ 0)
  exact matrixColNorm_nonneg (ν := ν) A 0

@[simp]
lemma matrixColNorm_mul_pow (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (j : Fin (N + 1)) :
    matrixColNorm ν A j * (ν : ℝ) ^ (j : ℕ) =
      ∑ i : Fin (N + 1), |A i j| * (ν : ℝ) ^ (i : ℕ) := by
  simp [matrixColNorm, finl1WeightedNorm, div_mul_cancel₀ _
    (pow_ne_zero _ (PosReal.coe_ne_zero ν))]

/-- Weighted matrix/mulVec submultiplicativity:
`‖Mv‖_{1,ν} ≤ ‖M‖_{1,ν} · ‖v‖_{1,ν}`, stated symbolically via
`finl1WeightedNorm` and `Matrix.mulVec`.

Proof: `show` reduces to expanded sums (definitional), then
`weighted_sum_abs_sum_le` (triangle + sum swap) →
`simp_rw` (factor `|v k|`, recognize `matrixColNorm_mul_pow`) →
`Finset.le_sup'` (column norm ≤ matrix norm). -/
lemma finWeightedMatrixNorm_mulVec_le
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (v : Fin (N + 1) → ℝ) :
    finl1WeightedNorm (ν : ℝ≥0) (A *ᵥ v) ≤
      finWeightedMatrixNorm ν A * finl1WeightedNorm (ν : ℝ≥0) v := by
  show ∑ n : Fin (N + 1), |∑ k : Fin (N + 1), A n k * v k| * (ν : ℝ) ^ (n : ℕ) ≤
      finWeightedMatrixNorm ν A * ∑ k : Fin (N + 1), |v k| * (ν : ℝ) ^ (k : ℕ)
  -- Triangle + sum swap
  refine (SystemTaylorODE.weighted_sum_abs_sum_le (fun n => (ν : ℝ) ^ (n : ℕ))
    (fun _ => pow_nonneg ν.coe_nonneg _) (fun k n => A n k * v k)).trans ?_
  -- Factor |v k|, recognize matrixColNorm
  simp_rw [abs_mul, show ∀ (k n : Fin (N + 1)),
    |A n k| * |v k| * (ν : ℝ) ^ (n : ℕ) =
      |v k| * (|A n k| * (ν : ℝ) ^ (n : ℕ)) from fun _ _ => by ring,
    ← Finset.mul_sum, ← matrixColNorm_mul_pow]
  -- Bound matrixColNorm ≤ finWeightedMatrixNorm
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ =>
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (Finset.le_sup' _ (Finset.mem_univ k))
        (pow_nonneg ν.coe_nonneg _)) (abs_nonneg _)).trans_eq (mul_left_comm _ _ _)

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
  simp [matrixColNorm, finl1WeightedNorm]

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

private lemma trunc_add (N : ℕ) (a b : l1Weighted ν) :
    trunc N (a + b) = trunc N a + trunc N b := by
  apply lpWeighted.ext; intro n
  simp only [coeff_trunc, lpWeighted.add_toSeq]
  split_ifs <;> simp

private lemma trunc_smul (N : ℕ) (c : ℝ) (a : l1Weighted ν) :
    trunc N (c • a) = c • trunc N a := by
  apply lpWeighted.ext; intro n
  simp only [coeff_trunc, lpWeighted.smul_toSeq]
  split_ifs <;> simp

private lemma trunc_norm_le (N : ℕ) (a : l1Weighted ν) :
    ‖trunc N a‖ ≤ 1 * ‖a‖ := by
  rw [one_mul, norm_eq_tsum, norm_eq_tsum]
  exact ((mem_iff _).mp (trunc N a).2).tsum_le_tsum (fun n => by
    simp only [coeff_trunc]
    split_ifs <;> simp [mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) _)])
    ((mem_iff _).mp a.2)

/-- Truncation as a continuous linear map on `ℓ¹_ν`. -/
noncomputable def trunc_CLM (N : ℕ) : l1Weighted ν →L[ℝ] l1Weighted ν :=
  LinearMap.mkContinuous
    { toFun := trunc N
      map_add' := trunc_add N
      map_smul' := fun c a => by simp [trunc_smul] }
    1
    (trunc_norm_le N)

@[simp] lemma trunc_CLM_apply (N : ℕ) (a : l1Weighted ν) :
    trunc_CLM N a = trunc N a := rfl

end Truncation

end l1Weighted

end SystemTaylorODE
