import RadiiPolynomial.SystemTaylorODE.lpWeighted

/-!
# Omega-weighted sequence space for IVP problems

The IVP zero-finding map `F(a)_k = k·a_k − φ(a)_{k−1}` does not map `ℓ¹_ν → ℓ¹_ν`
because the factor `k` breaks summability. The book (Proposition 8.1.5) resolves this
with range space `Y = ℓ¹_ω` where `ω_n = ν^{n+1}/(n+1)`.

This file provides:
- `OmegaScaledReal ν n`: `ℝ` with norm `|x| * ν^(n+1) / (n+1)`
- `l1Omega ν`: omega-weighted `ℓ¹` space
- Key embedding/summability lemmas connecting `l1Weighted` and `l1Omega`
-/

open scoped BigOperators Topology NNReal ENNReal

noncomputable section

namespace SystemTaylorODE

/-- `OmegaScaledReal ν n` is `ℝ` equipped with norm `|x| * ν^(n+1) / (n+1)`.
Ref: §8.1, Proposition 8.1.5 — weight sequence `ω_n = ν^{n+1}/(n+1)`. -/
def OmegaScaledReal (_ν : PosReal) (_n : ℕ) := ℝ

namespace OmegaScaledReal

variable {ν : PosReal} {n : ℕ}

instance : AddCommGroup (OmegaScaledReal ν n) := inferInstanceAs (AddCommGroup ℝ)
instance : Module ℝ (OmegaScaledReal ν n) := inferInstanceAs (Module ℝ ℝ)
instance : Lattice (OmegaScaledReal ν n) := inferInstanceAs (Lattice ℝ)
instance : LinearOrder (OmegaScaledReal ν n) := inferInstanceAs (LinearOrder ℝ)
instance : AddLeftMono (OmegaScaledReal ν n) := inferInstanceAs (AddLeftMono ℝ)

/-- Identity map to `ℝ`. -/
@[coe] def toReal (x : OmegaScaledReal ν n) : ℝ := x

instance : CoeOut (OmegaScaledReal ν n) ℝ := ⟨toReal⟩

/-- The omega weight at mode `n`: `ν^(n+1) / (n+1)`. -/
def omegaWeight (ν : PosReal) (n : ℕ) : ℝ := (ν : ℝ) ^ (n + 1) / (↑(n + 1) : ℝ)

lemma omegaWeight_pos : 0 < omegaWeight ν n := by
  unfold omegaWeight
  exact div_pos (pow_pos ν.coe_pos _) (Nat.cast_pos.mpr (Nat.succ_pos n))

lemma omegaWeight_nonneg : 0 ≤ omegaWeight ν n := le_of_lt omegaWeight_pos

instance instNorm : Norm (OmegaScaledReal ν n) where
  norm x := |toReal x| * omegaWeight ν n

lemma norm_def (x : OmegaScaledReal ν n) :
    ‖x‖ = |toReal x| * omegaWeight ν n := rfl

lemma norm_nonneg' (x : OmegaScaledReal ν n) : 0 ≤ ‖x‖ :=
  mul_nonneg (abs_nonneg _) omegaWeight_nonneg

@[simp] lemma norm_zero' : ‖(0 : OmegaScaledReal ν n)‖ = 0 := by
  simp [norm_def, toReal]

@[simp] lemma norm_neg' (x : OmegaScaledReal ν n) : ‖-x‖ = ‖x‖ := by
  simp [norm_def, toReal, abs_neg]

lemma norm_add_le' (x y : OmegaScaledReal ν n) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  simp only [norm_def]
  have h : toReal (x + y) = toReal x + toReal y := rfl
  calc |toReal (x + y)| * omegaWeight ν n
      ≤ (|toReal x| + |toReal y|) * omegaWeight ν n := by
        rw [h]
        exact mul_le_mul_of_nonneg_right (abs_add_le _ _) omegaWeight_nonneg
    _ = |toReal x| * omegaWeight ν n + |toReal y| * omegaWeight ν n := by ring

lemma norm_smul' (c : ℝ) (x : OmegaScaledReal ν n) : ‖c • x‖ = |c| * ‖x‖ := by
  simp only [norm_def]
  have h : toReal (c • x) = c * toReal x := rfl
  rw [h, abs_mul, mul_assoc]

lemma norm_eq_zero' (x : OmegaScaledReal ν n) : ‖x‖ = 0 ↔ x = 0 := by
  simp only [norm_def, mul_eq_zero]
  constructor
  · intro h
    cases h with
    | inl h => exact (abs_eq_zero (a := (toReal x))).mp h
    | inr h => exact absurd h (ne_of_gt omegaWeight_pos)
  · intro h; left; simp [h, toReal]

instance instNormedAddCommGroup : NormedAddCommGroup (OmegaScaledReal ν n) where
  dist x y := ‖x - y‖
  dist_self x := by simp [norm_zero']
  dist_comm x y := by
    simp only [norm_def]
    rw [show toReal (x - y) = toReal x - toReal y from rfl,
        show toReal (y - x) = toReal y - toReal x from rfl,
        abs_sub_comm]
  dist_triangle x y z := by
    have h : x - z = (x - y) + (y - z) := by abel_nf
    rw [h]; exact norm_add_le' _ _
  edist_dist x y := by simp only [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg' _)]
  eq_of_dist_eq_zero h := by rwa [norm_eq_zero', sub_eq_zero] at h
  norm := (‖·‖)
  dist_eq _ _ := rfl

instance instNormedSpace : NormedSpace ℝ (OmegaScaledReal ν n) where
  norm_smul_le c x := by rw [norm_smul']; rfl

instance instFiniteDimensional : FiniteDimensional ℝ (OmegaScaledReal ν n) :=
  inferInstanceAs (FiniteDimensional ℝ ℝ)

instance instCompleteSpace : CompleteSpace (OmegaScaledReal ν n) := by
  simpa using (FiniteDimensional.complete (𝕜 := ℝ) (E := OmegaScaledReal ν n))

/-- Additive equivalence from `ℝ`. -/
def ofReal : ℝ ≃+ OmegaScaledReal ν n := AddEquiv.refl ℝ

@[simp] lemma toReal_apply (x : OmegaScaledReal ν n) : toReal x = x := rfl
@[simp] lemma ofReal_apply (x : ℝ) : (ofReal x : OmegaScaledReal ν n) = x := rfl

@[simp] lemma coe_zero : ((0 : OmegaScaledReal ν n) : ℝ) = 0 := rfl
@[simp] lemma coe_add (x y : OmegaScaledReal ν n) :
    ((x + y : OmegaScaledReal ν n) : ℝ) = x + y := rfl
@[simp] lemma coe_sub (x y : OmegaScaledReal ν n) :
    ((x - y : OmegaScaledReal ν n) : ℝ) = x - y := rfl
@[simp] lemma coe_neg (x : OmegaScaledReal ν n) :
    ((-x : OmegaScaledReal ν n) : ℝ) = -x := rfl

end OmegaScaledReal

/-- Omega-weighted `ℓ¹` space: `ℓ¹_ω` with `ω_n = ν^{n+1}/(n+1)`. -/
abbrev l1Omega (ν : PosReal) := lp (OmegaScaledReal ν) 1

namespace l1Omega

variable {ν : PosReal}

instance : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩

instance instUniformSpace : UniformSpace (l1Omega ν) := by
  change UniformSpace (lp (OmegaScaledReal ν) 1); infer_instance

instance instCompleteSpace : CompleteSpace (l1Omega ν) := by
  change CompleteSpace (lp (OmegaScaledReal ν) 1); infer_instance

/-- Underlying real sequence. -/
def toSeq (a : l1Omega ν) : ℕ → ℝ := fun n => OmegaScaledReal.toReal (a n)

/-- Extensionality through coefficients. -/
lemma ext {a b : l1Omega ν} (h : ∀ n, toSeq a n = toSeq b n) : a = b :=
  lp.ext (funext h)

/-- Membership predicate for omega-weighted `ℓ¹`. -/
def Mem (ν : PosReal) (a : ℕ → ℝ) : Prop :=
  Memℓp (fun n => OmegaScaledReal.ofReal (a n) : ∀ n, OmegaScaledReal ν n) 1

/-- Construct an element from a sequence with finite omega-weighted norm. -/
def mk (a : ℕ → ℝ) (ha : Mem ν a) : l1Omega ν :=
  ⟨fun n => OmegaScaledReal.ofReal (a n), ha⟩

@[simp] lemma toSeq_apply (a : l1Omega ν) (n : ℕ) : toSeq a n = a n := rfl
@[simp] lemma mk_apply (a : ℕ → ℝ) (ha : Mem ν a) (n : ℕ) : toSeq (mk a ha) n = a n := rfl
@[simp] lemma zero_toSeq (n : ℕ) : toSeq (0 : l1Omega ν) n = 0 := rfl
@[simp] lemma neg_toSeq (a : l1Omega ν) (n : ℕ) : toSeq (-a) n = -toSeq a n := rfl
@[simp] lemma add_toSeq (a b : l1Omega ν) (n : ℕ) :
    toSeq (a + b) n = toSeq a n + toSeq b n := rfl
@[simp] lemma sub_toSeq (a b : l1Omega ν) (n : ℕ) :
    toSeq (a - b) n = toSeq a n - toSeq b n := rfl
@[simp] lemma smul_toSeq (c : ℝ) (a : l1Omega ν) (n : ℕ) :
    toSeq (c • a) n = c * toSeq a n := rfl

lemma norm_eq_tsum (a : l1Omega ν) :
    ‖a‖ = ∑' n, |toSeq a n| * OmegaScaledReal.omegaWeight ν n := by
  have h := lp.norm_eq_tsum_rpow (p := (1 : ℝ≥0∞)) (by norm_num : 0 < (1 : ℝ≥0∞).toReal) a
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one] at h
  exact h

lemma mem_iff (a : ℕ → ℝ) :
    Mem ν a ↔ Summable (fun n => |a n| * OmegaScaledReal.omegaWeight ν n) := by
  simp only [Mem, Memℓp, OmegaScaledReal.ofReal_apply, ne_eq]
  simp only [show (1 : ℝ≥0∞) ≠ 0 from one_ne_zero, ENNReal.one_ne_top, ↓reduceIte,
    OmegaScaledReal.norm_def, OmegaScaledReal.toReal_apply, ENNReal.toReal_one, Real.rpow_one]

end l1Omega

section Bridges

variable {ν : PosReal}

/-- Key weight identity: `(n+1) * ω_n = ν^{n+1}`, i.e., multiplying by the mode index
is exactly compensated by the omega weight. This is the fundamental property
that makes IVP maps well-typed. Ref: Proposition 8.1.5. -/
lemma omegaWeight_mul_index (n : ℕ) :
    (↑(n + 1) : ℝ) * OmegaScaledReal.omegaWeight ν n = (ν : ℝ) ^ (n + 1) := by
  unfold OmegaScaledReal.omegaWeight
  rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))]

/-- Omega weight bounded by geometric weight: `ω_n ≤ ν^n` for all `n`.
Since `ω_n = ν^{n+1}/(n+1) ≤ ν^{n+1} ≤ ν^n` only when `ν ≤ 1`, we use a
weaker but unconditional bound: `ω_n ≤ ν · ν^n` (factor of ν). -/
lemma omegaWeight_le_nu_mul_pow (n : ℕ) :
    OmegaScaledReal.omegaWeight ν n ≤ (ν : ℝ) * (ν : ℝ) ^ n := by
  unfold OmegaScaledReal.omegaWeight
  rw [pow_succ, mul_comm ((ν : ℝ) ^ n) (ν : ℝ)]
  exact div_le_self (mul_nonneg ν.coe_nonneg (pow_nonneg ν.coe_nonneg _))
    (Nat.one_le_cast.mpr (Nat.succ_pos n))

/-- If `a ∈ ℓ¹_ν`, then the derivative-shifted sequence `{(n+1)·a_{n+1}}` belongs to `ℓ¹_ω`.
This is the key membership lemma for IVP zero-finding maps.
Ref: Proposition 8.1.5 — `b = {(n+1)a_{n+1}} ∈ ℓ¹_ω`. -/
lemma l1Omega.deriv_shift_mem (a : l1Weighted ν) :
    l1Omega.Mem ν (fun (n : ℕ) => ((n : ℝ) + 1) * l1Weighted.toSeq a (n + 1)) := by
  rw [l1Omega.mem_iff]
  -- |b_n| · ω_n = |(n+1) · a_{n+1}| · ν^{n+1}/(n+1) = |a_{n+1}| · ν^{n+1}
  have h : ∀ (n : ℕ), |((n : ℝ) + 1) * l1Weighted.toSeq a (n + 1)| *
      OmegaScaledReal.omegaWeight ν n =
      |l1Weighted.toSeq a (n + 1)| * (ν : ℝ) ^ (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [abs_mul, abs_of_pos hpos, mul_comm ((n : ℝ) + 1) _, mul_assoc,
      show (n : ℝ) + 1 = ↑(n + 1) from by push_cast; ring, omegaWeight_mul_index]
  simp_rw [h]
  exact ((l1Weighted.mem_iff (ν := ν) (l1Weighted.toSeq a)).mp a.2).comp_injective
    (fun (n m : ℕ) (h : n + 1 = m + 1) => by omega)

/-- If `a ∈ ℓ¹_ν`, then `a ∈ ℓ¹_ω` (with norm bounded by `ν · ‖a‖_ν`).
Since `ω_n ≤ ν · ν^n`, geometric summability implies omega summability. -/
lemma l1Omega.geom_to_omega_mem (a : l1Weighted ν) :
    l1Omega.Mem ν (l1Weighted.toSeq a) := by
  rw [l1Omega.mem_iff]
  apply Summable.of_nonneg_of_le
  · intro n; exact mul_nonneg (abs_nonneg _) OmegaScaledReal.omegaWeight_nonneg
  · intro n
    exact mul_le_mul_of_nonneg_left (omegaWeight_le_nu_mul_pow n) (abs_nonneg _)
  · have hsm := ((l1Weighted.mem_iff (ν := ν) (l1Weighted.toSeq a)).mp a.2).mul_left (ν : ℝ)
    simp_rw [show ∀ n, (ν : ℝ) * (|l1Weighted.toSeq a n| * (ν : ℝ) ^ n) =
      |l1Weighted.toSeq a n| * ((ν : ℝ) * (ν : ℝ) ^ n) from fun n => by ring] at hsm
    exact hsm

/-- Finite-support sequences belong to `ℓ¹_ω` (for constructing F_lorenz(ābar)). -/
lemma l1Omega.mem_of_finite_support (a : ℕ → ℝ) (M : ℕ) (hsupp : ∀ n, M < n → a n = 0) :
    l1Omega.Mem ν a := by
  rw [l1Omega.mem_iff]
  exact summable_of_ne_finset_zero (s := Finset.Icc 0 M) fun n hn => by
    have : M < n := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hn; omega
    simp [hsupp n this]

/-- `ℓ¹_ω` membership is closed under subtraction. -/
lemma l1Omega.mem_sub {f g : ℕ → ℝ} (hf : l1Omega.Mem ν f) (hg : l1Omega.Mem ν g) :
    l1Omega.Mem ν (fun n => f n - g n) := by
  rw [l1Omega.mem_iff] at hf hg ⊢
  refine (hf.add hg).of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) OmegaScaledReal.omegaWeight_nonneg)
    fun n => ?_
  have hab : |f n - g n| ≤ |f n| + |g n| :=
    abs_le.mpr ⟨by linarith [neg_abs_le (f n), le_abs_self (g n)],
      by linarith [le_abs_self (f n), neg_abs_le (g n)]⟩
  exact (mul_le_mul_of_nonneg_right hab OmegaScaledReal.omegaWeight_nonneg).trans_eq
    (add_mul _ _ _)

/-- IVP zero-finding map membership: the sequence
  `{c₀, 1·a₁ - φ₀, 2·a₂ - φ₁, 3·a₃ - φ₂, ...}` belongs to `ℓ¹_ω`.
This is the standard structure of `F(a)_l` in IVP problems (Proposition 8.1.5).
The derivative-shift `(n+1)·a_{n+1}` is omega-summable, and φ ∈ ℓ¹_ν ↪ ℓ¹_ω. -/
lemma l1Omega.mem_ivp_zero_finding (a : l1Weighted ν) (φ : l1Weighted ν) (c₀ : ℝ) :
    l1Omega.Mem ν (fun n => match n with
      | 0 => c₀
      | n + 1 => ((n : ℝ) + 1) * l1Weighted.toSeq a (n + 1) -
          l1Weighted.toSeq φ n) := by
  rw [l1Omega.mem_iff, ← summable_nat_add_iff (k := 1)]
  -- Comparison: |f(n+1)| * ω_{n+1} ≤ ν·|a_{n+1}|·ν^{n+1} + ν²·|φ_n|·ν^n
  have ha := (l1Weighted.mem_iff (l1Weighted.toSeq a)).mp a.2
  have hφ := (l1Weighted.mem_iff (l1Weighted.toSeq φ)).mp φ.2
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) OmegaScaledReal.omegaWeight_nonneg)
    (fun n => ?_)
    (((summable_nat_add_iff (k := 1)).mpr ha).mul_left (ν : ℝ) |>.add
      (hφ.mul_left ((ν : ℝ) ^ 2)))
  -- Pointwise: |((n+1)*a_{n+1} - φ_n)| * ω_{n+1} ≤ ν*|a_{n+1}|*ν^{n+1} + ν²*|φ_n|*ν^n
  simp only [OmegaScaledReal.omegaWeight]
  have hne : (↑(n + 2) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [show (n + 1 + 1 : ℕ) = n + 2 from by omega]
  -- Triangle inequality: |x - y| ≤ |x| + |y| where x = (n+1)*a_{n+1}
  have h1 : |((n : ℝ) + 1) * l1Weighted.toSeq a (n + 1) - l1Weighted.toSeq φ n| ≤
      ((n : ℝ) + 1) * |l1Weighted.toSeq a (n + 1)| + |l1Weighted.toSeq φ n| := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  -- ω_{n+1} = ν^{n+2}/(n+2), and (n+1)/(n+2) ≤ 1, 1/(n+2) ≤ 1
  have hω_nn : (0 : ℝ) ≤ (ν : ℝ) ^ (n + 2) / (↑(n + 2) : ℝ) :=
    div_nonneg (pow_nonneg ν.2.le _) (by positivity)
  have hdiv1 : ((n : ℝ) + 1) / (↑(n + 2) : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; push_cast; linarith
  have hdiv2 : (1 : ℝ) / (↑(n + 2) : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; push_cast; linarith
  calc _ ≤ (((n : ℝ) + 1) * |l1Weighted.toSeq a (n + 1)| + |l1Weighted.toSeq φ n|) *
            ((ν : ℝ) ^ (n + 2) / ↑(n + 2)) :=
          mul_le_mul_of_nonneg_right h1 hω_nn
    _ ≤ (ν : ℝ) * (|l1Weighted.toSeq a (n + 1)| * (ν : ℝ) ^ (n + 1)) +
        (ν : ℝ) ^ 2 * (|l1Weighted.toSeq φ n| * (ν : ℝ) ^ n) := by
      -- Split into two terms and bound each
      rw [add_mul]
      apply add_le_add
      · -- (n+1)*|a|*(ν^{n+2}/(n+2)) ≤ |a|*ν^{n+2} = ν*|a|*ν^{n+1}
        have hb := mul_nonneg (abs_nonneg (l1Weighted.toSeq a (n + 1))) (pow_nonneg ν.2.le (n + 2))
        calc _ = (↑n + 1) / ↑(n + 2) * (|l1Weighted.toSeq a (n + 1)| * (ν : ℝ) ^ (n + 2)) := by ring
          _ ≤ 1 * (|l1Weighted.toSeq a (n + 1)| * (ν : ℝ) ^ (n + 2)) :=
              mul_le_mul_of_nonneg_right hdiv1 hb
          _ = (ν : ℝ) * (|l1Weighted.toSeq a (n + 1)| * (ν : ℝ) ^ (n + 1)) := by
              rw [one_mul, pow_succ]; ring
      · -- |φ|*(ν^{n+2}/(n+2)) ≤ |φ|*ν^{n+2} = ν²*|φ|*ν^n
        have hb := mul_nonneg (abs_nonneg (l1Weighted.toSeq φ n)) (pow_nonneg ν.2.le (n + 2))
        calc _ = 1 / ↑(n + 2) * (|l1Weighted.toSeq φ n| * (ν : ℝ) ^ (n + 2)) := by ring
          _ ≤ 1 * (|l1Weighted.toSeq φ n| * (ν : ℝ) ^ (n + 2)) :=
              mul_le_mul_of_nonneg_right hdiv2 hb
          _ = (ν : ℝ) ^ 2 * (|l1Weighted.toSeq φ n| * (ν : ℝ) ^ n) := by
              rw [one_mul, pow_succ, pow_succ]; ring

end Bridges

section ShiftDivN

variable {ν : PosReal}

/-- The shift-and-divide operator: maps sequence `b` to `{0, b_0/1, b_1/2, b_2/3, ...}`.
This is the key IVP tail operator: `(shift_div_n b)_n = b_{n-1}/n` for `n ≥ 1`, zero at `n = 0`.
Bounded: `‖shift_div_n b‖ ≤ ν · ‖b‖` since `|b_{n-1}|/n · ν^n ≤ |b_{n-1}| · ν^n ≤ ν · |b_{n-1}| · ν^{n-1}`. -/
def shiftDivN_seq (b : l1Weighted ν) : ℕ → ℝ
  | 0 => 0
  | n + 1 => l1Weighted.toSeq b n / (↑(n + 1) : ℝ)

private lemma shiftDivN_shifted_term_le (b : l1Weighted ν) (n : ℕ) :
    |shiftDivN_seq b (n + 1)| * (ν : ℝ) ^ (n + 1) ≤
    (ν : ℝ) * (|l1Weighted.toSeq b n| * (ν : ℝ) ^ n) := by
  simp only [shiftDivN_seq]
  have hn1 : (1 : ℝ) ≤ (↑(n + 1) : ℝ) := by exact_mod_cast Nat.succ_pos n
  rw [abs_div, abs_of_nonneg (le_of_lt (lt_of_lt_of_le one_pos hn1))]
  rw [div_mul_eq_mul_div, pow_succ, ← mul_assoc]
  exact (div_le_self (mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _)) ν.2.le) hn1).trans_eq (by ring)

lemma shiftDivN_mem (b : l1Weighted ν) : lpWeighted.Mem ν 1 (shiftDivN_seq b) := by
  rw [l1Weighted.mem_iff]
  have hb : Summable (fun n => |l1Weighted.toSeq b n| * (ν : ℝ) ^ n) :=
    (l1Weighted.mem_iff (l1Weighted.toSeq b)).mp b.2
  -- Suffices to show the shifted series n ↦ f(n+1) is summable
  let f : ℕ → ℝ := fun n => |shiftDivN_seq b n| * (ν : ℝ) ^ n
  show Summable f
  rw [← summable_nat_add_iff (k := 1)]
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _))
    (shiftDivN_shifted_term_le b)
    (hb.mul_left (ν : ℝ))

/-- The shift-and-divide operator as an element of `l1Weighted ν`. -/
noncomputable def shiftDivN (b : l1Weighted ν) : l1Weighted ν :=
  lpWeighted.mk (shiftDivN_seq b) (shiftDivN_mem b)

@[simp] lemma shiftDivN_zero_mode (b : l1Weighted ν) :
    l1Weighted.toSeq (shiftDivN b) 0 = 0 := by
  simp [shiftDivN, shiftDivN_seq, l1Weighted.toSeq, lpWeighted.toSeq, lpWeighted.mk]

@[simp] lemma shiftDivN_succ_mode (b : l1Weighted ν) (n : ℕ) :
    l1Weighted.toSeq (shiftDivN b) (n + 1) =
      l1Weighted.toSeq b n / (↑(n + 1) : ℝ) := by
  simp [shiftDivN, shiftDivN_seq, l1Weighted.toSeq, lpWeighted.toSeq, lpWeighted.mk]

private lemma shiftDivN_toSeq (b : l1Weighted ν) (n : ℕ) :
    lpWeighted.toSeq (shiftDivN b) n = shiftDivN_seq b n := by
  simp [shiftDivN, lpWeighted.toSeq, lpWeighted.mk]

/-- Bridge `l1Weighted.toSeq` to `shiftDivN_seq` (the abbrev-safe version). -/
@[simp] lemma l1_toSeq_shiftDivN (b : l1Weighted ν) (n : ℕ) :
    l1Weighted.toSeq (shiftDivN b) n = shiftDivN_seq b n :=
  shiftDivN_toSeq b n

lemma shiftDivN_linear_add (b c : l1Weighted ν) :
    shiftDivN (b + c) = shiftDivN b + shiftDivN c := by
  apply lpWeighted.ext; intro n
  simp only [shiftDivN_toSeq, lpWeighted.add_toSeq]
  cases n with
  | zero => simp [shiftDivN_seq]
  | succ n => simp [shiftDivN_seq, add_div]

lemma shiftDivN_linear_smul (r : ℝ) (b : l1Weighted ν) :
    shiftDivN (r • b) = r • shiftDivN b := by
  apply lpWeighted.ext; intro n
  simp only [shiftDivN_toSeq, lpWeighted.smul_toSeq]
  cases n with
  | zero => simp [shiftDivN_seq]
  | succ n => simp [shiftDivN_seq, mul_div_assoc]

lemma shiftDivN_norm_le (b : l1Weighted ν) :
    ‖shiftDivN b‖ ≤ (ν : ℝ) * ‖b‖ := by
  rw [l1Weighted.norm_eq_tsum, l1Weighted.norm_eq_tsum]
  -- Bridge: toSeq (shiftDivN b) n = shiftDivN_seq b n (via simp lemmas)
  conv_lhs => arg 1; ext n; rw [show l1Weighted.toSeq (shiftDivN b) n = shiftDivN_seq b n
    from shiftDivN_toSeq b n]
  have hsumm : Summable (fun n => |shiftDivN_seq b n| * (ν : ℝ) ^ n) :=
    (l1Weighted.mem_iff _).mp (shiftDivN_mem b)
  have hb : Summable (fun n => |l1Weighted.toSeq b n| * (ν : ℝ) ^ n) :=
    (l1Weighted.mem_iff _).mp b.2
  -- Split: Σ f(n) = f(0) + Σ f(n+1), then bound shifted terms by ν * g(n)
  rw [hsumm.tsum_eq_zero_add]
  simp only [shiftDivN_seq, abs_zero, zero_mul, zero_add]
  rw [← tsum_mul_left]
  exact ((summable_nat_add_iff (k := 1)).mpr hsumm).tsum_le_tsum
    (shiftDivN_shifted_term_le b) (hb.mul_left _)

/-- Tail of `shiftDivN b` starting from mode `N+1` is bounded by `ν/(N+1) · ‖b‖`.
This is tighter than the full norm bound `‖shiftDivN b‖ ≤ ν · ‖b‖` because
on tail modes `1/n ≤ 1/(N+1)`. Used for IVP Z₁ tail error bounds. -/
private lemma shiftDivN_shifted_term_tight_le (b : l1Weighted ν) (N n : ℕ) :
    |shiftDivN_seq b (n + (N + 1))| * (ν : ℝ) ^ (n + (N + 1)) ≤
    (ν : ℝ) / (↑N + 1) * (|l1Weighted.toSeq b (n + N)| * (ν : ℝ) ^ (n + N)) := by
  -- Rewrite n + (N+1) = n + N + 1 to enable pattern match
  rw [(Nat.add_assoc n N 1).symm]
  -- Now shiftDivN_seq b (n + N + 1) reduces since n+N+1 = (n+N).succ
  simp only [shiftDivN_seq]
  -- Goal: |toSeq b (n+N) / ↑(n+N+1)| * ν^(n+N+1) ≤ ν/(N+1) * (|toSeq b (n+N)| * ν^(n+N))
  have hn1 : (1 : ℝ) ≤ ↑(n + N + 1) := by exact_mod_cast Nat.succ_pos (n + N)
  rw [abs_div, abs_of_nonneg (le_of_lt (lt_of_lt_of_le one_pos hn1))]
  rw [div_mul_eq_mul_div, pow_succ, ← mul_assoc]
  -- LHS: |b_m| * ν^m * ν / (m+1);  RHS: ν/(N+1) * (|b_m| * ν^m)
  -- Factor: both are |b_m| * ν^m * (ν / denominator)
  have hterm := mul_nonneg (mul_nonneg (abs_nonneg (l1Weighted.toSeq b (n + N)))
    (pow_nonneg ν.2.le (n + N))) ν.2.le
  exact (div_le_div_of_nonneg_left hterm (by positivity : (0 : ℝ) < ↑N + 1)
    (by exact_mod_cast (show N + 1 ≤ n + N + 1 by omega))).trans_eq (by ring)

/-- Tail of `shiftDivN b` starting from mode `N+1` is bounded by `ν/(N+1) · ‖b‖`.
Tighter than `shiftDivN_norm_le` (`≤ ν · ‖b‖`) because `1/n ≤ 1/(N+1)` on tail.
Used for IVP Z₁ tail error bounds. -/
lemma shiftDivN_tailTsum_le_div (b : l1Weighted ν) (N : ℕ) :
    ∑' n, |l1Weighted.toSeq (shiftDivN b) (n + (N + 1))| * (ν : ℝ) ^ (n + (N + 1)) ≤
      (ν : ℝ) / (↑N + 1) * ‖b‖ := by
  simp only [l1_toSeq_shiftDivN]
  have hsumm := (summable_nat_add_iff (k := N + 1)).mpr
    ((l1Weighted.mem_iff _).mp (shiftDivN_mem b))
  have hb_shift := ((summable_nat_add_iff (k := N)).mpr
    (l1Weighted.summable_weighted b)).mul_left ((ν : ℝ) / (↑N + 1))
  calc ∑' n, |shiftDivN_seq b (n + (N + 1))| * (ν : ℝ) ^ (n + (N + 1))
      ≤ ∑' n, ((ν : ℝ) / (↑N + 1) * (|l1Weighted.toSeq b (n + N)| * (ν : ℝ) ^ (n + N))) :=
        hsumm.tsum_le_tsum (shiftDivN_shifted_term_tight_le b N) hb_shift
    _ = (ν : ℝ) / (↑N + 1) * ∑' n, (|l1Weighted.toSeq b (n + N)| * (ν : ℝ) ^ (n + N)) :=
        tsum_mul_left
    _ ≤ (ν : ℝ) / (↑N + 1) * ‖b‖ :=
        mul_le_mul_of_nonneg_left (l1Weighted.tailTsum_le_norm_of_eq b b N (fun _ _ => rfl))
          (div_nonneg ν.2.le (by positivity))

/-- The shift-and-divide operator as a CLM on `l1Weighted ν`. -/
noncomputable def shiftDivN_CLM : l1Weighted ν →L[ℝ] l1Weighted ν :=
  LinearMap.mkContinuous
    { toFun := shiftDivN
      map_add' := shiftDivN_linear_add
      map_smul' := fun r b => by simp [shiftDivN_linear_smul] }
    (ν : ℝ)
    shiftDivN_norm_le

@[simp] lemma shiftDivN_CLM_apply (b : l1Weighted ν) :
    shiftDivN_CLM b = shiftDivN b := rfl

end ShiftDivN

/-- Omega-weighted system space `(ℓ¹_ω)^L`. -/
abbrev YOmega (ν : PosReal) (L : ℕ) := Fin L → l1Omega ν

end SystemTaylorODE
