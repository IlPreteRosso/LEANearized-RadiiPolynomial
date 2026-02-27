import RadiiPolynomial.SystemTaylorODE.BlockDiagSystem.Base

/-!
# BlockDiagSystem Concrete

Concrete `l1Weighted` realization of `SystemBlockDiagData`:
- coefficient extraction/reconstruction
- linearity and summability helpers
- `toLinearMap` / `toCLM` with explicit norm bound
- residual and `Z₀` bridge lemmas
- Section 9: Z₁ infrastructure for general L (composition norm bounds when the inner operator kills finite modes)
-/

open scoped Topology
open Metric Set Filter ContinuousLinearMap

noncomputable section

namespace SystemTaylorODE

/-! ## 5. Concrete `ℓ¹_ν` Realization And CLM Lift -/

section SystemBlockDiagConcrete

variable {ν : PosReal} {L N : ℕ}

/-- Concrete sequence family for SystemTaylorODE: weighted `ℓ¹_ν`. -/
abbrev SeqL1 := fun ν : PosReal => ↥(l1Weighted ν)

/-- Concrete system space `(ℓ¹_ν)^L`. -/
abbrev XL1 (ν : PosReal) (L : ℕ) := X SeqL1 ν L

/-! Pointwise algebraic structures on `(ℓ¹_ν)^L` (inherited from `l1Weighted ν`). -/

instance instXL1Ring : Ring (XL1 ν L) := inferInstance
instance instXL1CommRing : CommRing (XL1 ν L) := inferInstance
instance instXL1NormedRing : NormedRing (XL1 ν L) := inferInstance
instance instXL1NormOneClass [NeZero L] : NormOneClass (XL1 ν L) := inferInstance
instance instXL1Algebra : Algebra ℝ (XL1 ν L) := inferInstance
instance instXL1NormedAlgebra : NormedAlgebra ℝ (XL1 ν L) := inferInstance

/-- Extract coefficient functions from a concrete system state. -/
def toCoeff (x : XL1 ν L) : SystemCoeff L :=
  fun l n => lpWeighted.toSeq (x l) n

/-- Build a concrete system state from coefficients with per-component membership proofs. -/
def ofCoeff (c : SystemCoeff L) (hc : ∀ l : Fin L, lpWeighted.Mem ν 1 (c l)) : XL1 ν L :=
  fun l => lpWeighted.mk (c l) (hc l)

lemma toCoeff_mem (x : XL1 ν L) (l : Fin L) :
    lpWeighted.Mem ν 1 (toCoeff x l) := by
  change Memℓp (fun n => ScaledReal.ofReal (lpWeighted.toSeq (x l) n)) 1
  simpa [toCoeff, lpWeighted.toSeq, ScaledReal.ofReal_apply] using (lp.memℓp (x l))

@[simp] lemma toCoeff_ofCoeff
    (c : SystemCoeff L) (hc : ∀ l : Fin L, lpWeighted.Mem ν 1 (c l))
    (l : Fin L) (n : ℕ) :
    toCoeff (ofCoeff (ν := ν) c hc) l n = c l n := by
  simp [toCoeff, ofCoeff, lpWeighted.mk]

@[simp] lemma ofCoeff_apply
    (c : SystemCoeff L) (hc : ∀ l : Fin L, lpWeighted.Mem ν 1 (c l))
    (l : Fin L) :
    ofCoeff (ν := ν) c hc l = lpWeighted.mk (c l) (hc l) := rfl

lemma SystemBlockDiagData.actionFinite_mem
    (A : SystemBlockDiagData L N) (c : SystemCoeff L) (l : Fin L) :
    lpWeighted.Mem ν 1 (A.actionFinite c l) := by
  rw [l1Weighted.mem_iff]
  refine summable_of_ne_finset_zero (s := Finset.Icc 0 N) ?_
  intro n hn
  have hnot : ¬ n ≤ N := by
    intro hle
    exact hn (by simp [Finset.mem_Icc, hle])
  have hn' : N < n := Nat.lt_of_not_ge hnot
  simp [SystemBlockDiagData.actionFinite, Nat.not_le.mpr hn']

/-- Pointwise weighted tail estimate used in summability/norm bounds. -/
lemma SystemBlockDiagData.tail_weighted_term_le
    (A : SystemBlockDiagData L N) (c : SystemCoeff L) (l : Fin L) (n : ℕ) :
    |A.actionTail c l n| * (ν : ℝ) ^ n ≤
      A.tailBound * (|c l n| * (ν : ℝ) ^ n) := by
  by_cases hn : n ≤ N
  · rw [SystemBlockDiagData.actionTail_finite (A := A) (b := c) (l := l) (n := n) hn]
    have hnonneg :
        0 ≤ A.tailBound * (|c l n| * (ν : ℝ) ^ n) := by
      exact mul_nonneg (A.tailBound_nonneg_at l) (l1Weighted.weighted_term_nonneg (c l n) n)
    simpa using hnonneg
  · have hlt : N < n := Nat.lt_of_not_ge hn
    rw [SystemBlockDiagData.actionTail_tail (A := A) (b := c) (l := l) (n := n) hlt]
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_right (A.tailBound_spec l n hlt)
      (l1Weighted.weighted_term_nonneg (c l n) n)

/-- If a component is in `ℓ¹_ν`, its tail-transformed component is also in `ℓ¹_ν`. -/
lemma SystemBlockDiagData.actionTail_mem_of_mem
    (A : SystemBlockDiagData L N) (c : SystemCoeff L) (l : Fin L)
    (hc : lpWeighted.Mem ν 1 (c l)) :
    lpWeighted.Mem ν 1 (A.actionTail c l) := by
  rw [l1Weighted.mem_iff] at hc ⊢
  have h_rhs : Summable (fun n => A.tailBound * (|c l n| * (ν : ℝ) ^ n)) :=
    (hc.mul_left A.tailBound)
  refine h_rhs.of_nonneg_of_le ?_ ?_
  · intro n
    exact l1Weighted.weighted_term_nonneg (A.actionTail c l n) n
  · intro n
    exact A.tail_weighted_term_le (ν := ν) c l n

/-! ### Linearity helpers for finite/tail decomposition -/

/-- Additivity of the finite-mode action. -/
lemma SystemBlockDiagData.actionFinite_add
    (A : SystemBlockDiagData L N) (c d : SystemCoeff L) :
    A.actionFinite (fun l n => c l n + d l n) =
      fun l n => A.actionFinite c l n + A.actionFinite d l n := by
  funext l n
  by_cases hn : n ≤ N
  · simp [SystemBlockDiagData.actionFinite, hn]
    trans ∑ j : Fin L, ∑ k : Fin (N + 1),
        (A.finBlock l j ⟨n, Nat.lt_succ_of_le hn⟩ k * c j k +
          A.finBlock l j ⟨n, Nat.lt_succ_of_le hn⟩ k * d j k)
    · apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_add_distrib]
  · simp [SystemBlockDiagData.actionFinite, hn]

/-- Additivity of the tail action. -/
lemma SystemBlockDiagData.actionTail_add
    (A : SystemBlockDiagData L N) (c d : SystemCoeff L) :
    A.actionTail (fun l n => c l n + d l n) =
      fun l n => A.actionTail c l n + A.actionTail d l n := by
  funext l n
  by_cases hn : n ≤ N
  · simp [SystemBlockDiagData.actionTail, hn]
  · simp [SystemBlockDiagData.actionTail, hn]
    ring

/-- Homogeneity of the finite-mode action. -/
lemma SystemBlockDiagData.actionFinite_smul
    (A : SystemBlockDiagData L N) (r : ℝ) (c : SystemCoeff L) :
    A.actionFinite (fun l n => r * c l n) =
      fun l n => r * A.actionFinite c l n := by
  funext l n
  by_cases hn : n ≤ N
  · simp [SystemBlockDiagData.actionFinite, hn]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · simp [SystemBlockDiagData.actionFinite, hn]

/-- Homogeneity of the tail action. -/
lemma SystemBlockDiagData.actionTail_smul
    (A : SystemBlockDiagData L N) (r : ℝ) (c : SystemCoeff L) :
    A.actionTail (fun l n => r * c l n) =
      fun l n => r * A.actionTail c l n := by
  funext l n
  by_cases hn : n ≤ N
  · simp [SystemBlockDiagData.actionTail, hn]
  · simp [SystemBlockDiagData.actionTail, hn]
    ring

lemma SystemBlockDiagData.action_mem_of_mem
    (A : SystemBlockDiagData L N) (c : SystemCoeff L)
    (hc : ∀ l : Fin L, lpWeighted.Mem ν 1 (c l)) :
    ∀ l : Fin L, lpWeighted.Mem ν 1 (A.action c l) := by
  intro l
  rw [l1Weighted.mem_iff]
  have hfin := (l1Weighted.mem_iff (A.actionFinite c l)).mp (A.actionFinite_mem (ν := ν) c l)
  have htail := (l1Weighted.mem_iff (A.actionTail c l)).mp
    (A.actionTail_mem_of_mem (ν := ν) c l (hc l))
  let g := fun n => |A.action c l n| * (ν : ℝ) ^ n
  let f := fun n => |A.actionFinite c l n| * (ν : ℝ) ^ n
  let t := fun n => |A.actionTail c l n| * (ν : ℝ) ^ n
  have hs : Summable (fun n => f n + t n) := hfin.add htail
  refine hs.of_nonneg_of_le ?_ ?_
  · intro n
    exact l1Weighted.weighted_term_nonneg (A.action c l n) n
  · intro n
    have hpow : 0 ≤ (ν : ℝ) ^ n := pow_nonneg ν.coe_nonneg n
    have h_abs : |A.action c l n| ≤ |A.actionFinite c l n| + |A.actionTail c l n| := by
      simpa [SystemBlockDiagData.action_eq_actionFinite_add_actionTail] using
        (abs_add_le (A.actionFinite c l n) (A.actionTail c l n))
    have hmul := mul_le_mul_of_nonneg_right h_abs hpow
    have hsum :
        (|A.actionFinite c l n| + |A.actionTail c l n|) * (ν : ℝ) ^ n =
          f n + t n := by
      simp [f, t, right_distrib]
    exact hmul.trans_eq hsum

/-- Concrete action of `SystemBlockDiagData` on `(ℓ¹_ν)^L`. -/
def SystemBlockDiagData.applyX
    (A : SystemBlockDiagData L N) (x : XL1 ν L) : XL1 ν L :=
  ofCoeff (ν := ν) (A.action (toCoeff x))
    (A.action_mem_of_mem (ν := ν) (toCoeff x) (toCoeff_mem (ν := ν) x))

@[simp]
lemma SystemBlockDiagData.toCoeff_applyX
    (A : SystemBlockDiagData L N) (x : XL1 ν L) :
    toCoeff (A.applyX (ν := ν) x) = A.action (toCoeff x) := by
  funext l n; simp [SystemBlockDiagData.applyX, toCoeff, ofCoeff, lpWeighted.mk]

lemma SystemBlockDiagData.action_add
    (A : SystemBlockDiagData L N) (c d : SystemCoeff L) :
    A.action (fun l n => c l n + d l n) =
      fun l n => A.action c l n + A.action d l n := by
  ext l n
  simp [SystemBlockDiagData.action_eq_actionFinite_add_actionTail,
    SystemBlockDiagData.actionFinite_add, SystemBlockDiagData.actionTail_add, add_assoc, add_left_comm]

lemma SystemBlockDiagData.action_smul
    (A : SystemBlockDiagData L N) (r : ℝ) (c : SystemCoeff L) :
    A.action (fun l n => r * c l n) =
      fun l n => r * A.action c l n := by
  ext l n
  simp [SystemBlockDiagData.action_eq_actionFinite_add_actionTail,
    SystemBlockDiagData.actionFinite_smul, SystemBlockDiagData.actionTail_smul, left_distrib]

lemma SystemBlockDiagData.applyX_add
    (A : SystemBlockDiagData L N) (x y : XL1 ν L) :
    A.applyX (ν := ν) (x + y) = A.applyX (ν := ν) x + A.applyX (ν := ν) y := by
  funext l; apply lpWeighted.ext; intro n
  have : toCoeff (ν := ν) (A.applyX (ν := ν) (x + y)) l n =
      toCoeff (ν := ν) (A.applyX (ν := ν) x) l n +
      toCoeff (ν := ν) (A.applyX (ν := ν) y) l n := by
    simp only [toCoeff_applyX]
    simp only [show toCoeff (ν := ν) (x + y) = fun l n => toCoeff (ν := ν) x l n +
      toCoeff (ν := ν) y l n from funext fun i => funext fun k => by simp [toCoeff]]
    exact congrArg (fun f => f l n)
      (SystemBlockDiagData.action_add (A := A) (c := toCoeff (ν := ν) x) (d := toCoeff (ν := ν) y))
  simpa [toCoeff] using this

lemma SystemBlockDiagData.applyX_smul
    (A : SystemBlockDiagData L N) (r : ℝ) (x : XL1 ν L) :
    A.applyX (ν := ν) (r • x) = r • A.applyX (ν := ν) x := by
  funext l; apply lpWeighted.ext; intro n
  have : toCoeff (ν := ν) (A.applyX (ν := ν) (r • x)) l n =
      r * toCoeff (ν := ν) (A.applyX (ν := ν) x) l n := by
    simp only [toCoeff_applyX]
    simp only [show toCoeff (ν := ν) (r • x) = fun l n => r * toCoeff (ν := ν) x l n
      from funext fun i => funext fun k => by simp [toCoeff]]
    exact congrArg (fun f => f l n)
      (SystemBlockDiagData.action_smul (A := A) (r := r) (c := toCoeff (ν := ν) x))
  simpa [toCoeff] using this

/-- Linear-map lift of the 8.2 block operator data on `(ℓ¹_ν)^L`. -/
def SystemBlockDiagData.toLinearMap
    (A : SystemBlockDiagData L N) : XL1 ν L →ₗ[ℝ] XL1 ν L where
  toFun := A.applyX (ν := ν)
  map_add' := A.applyX_add (ν := ν)
  map_smul' := A.applyX_smul (ν := ν)

lemma finiteMatrix_weighted_l1_bound
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (v : Fin (N + 1) → ℝ) :
    ∑ n : Fin (N + 1), |∑ k : Fin (N + 1), M n k * v k| * (ν : ℝ) ^ (n : ℕ) ≤
      l1Weighted.finWeightedMatrixNorm ν M *
        ∑ k : Fin (N + 1), |v k| * (ν : ℝ) ^ (k : ℕ) := by
  simpa using l1Weighted.finWeightedMatrixNorm_mulVec_le (ν := ν) (A := M) (v := v)

lemma SystemBlockDiagData.finiteCoeffNorm_le_component_norm
    (x : XL1 ν L) (j : Fin L) :
    ∑ k : Fin (N + 1), |toCoeff (ν := ν) x j k| * (ν : ℝ) ^ (k : ℕ) ≤ ‖x j‖ := by
  simpa [toCoeff, l1Weighted.toSeq] using
    l1Weighted.finSum_weighted_toSeq_le_norm (ν := ν) (a := x j) (N := N)

lemma SystemBlockDiagData.actionFinite_component_norm_le_row
    (A : SystemBlockDiagData L N) (x : XL1 ν L) (l : Fin L) :
    ‖lpWeighted.mk (A.actionFinite (toCoeff (ν := ν) x) l)
      (A.actionFinite_mem (ν := ν) (toCoeff (ν := ν) x) l)‖ ≤
      blockRowNorm ν A.finBlock l * ‖x‖ := by
  let finPart : l1Weighted ν :=
    lpWeighted.mk (A.actionFinite (toCoeff (ν := ν) x) l)
      (A.actionFinite_mem (ν := ν) (toCoeff (ν := ν) x) l)
  have hnorm_support :
      ‖finPart‖ =
        ∑ n ∈ Finset.Icc 0 N, |lpWeighted.toSeq finPart n| * (ν : ℝ) ^ n := by
    refine l1Weighted.norm_eq_Icc_sum_of_support (a := finPart) (M := N) ?_
    intro n hn
    change A.actionFinite (toCoeff (ν := ν) x) l n = 0
    simp [SystemBlockDiagData.actionFinite, Nat.not_le.mpr hn]
  have hRange : Finset.range (N + 1) = Finset.Icc (0 : ℕ) N := by
    simpa [Nat.add_sub_cancel] using
      (Nat.range_eq_Icc_zero_sub_one (n := N + 1) (Nat.succ_ne_zero N))
  have hnorm_fin :
      ‖finPart‖ =
        ∑ n : Fin (N + 1),
          |∑ j : Fin L,
              ∑ k : Fin (N + 1),
                A.finBlock l j n k * toCoeff (ν := ν) x j k| * (ν : ℝ) ^ (n : ℕ) := by
    rw [hnorm_support, ← hRange]
    rw [← Fin.sum_univ_eq_sum_range
      (f := fun n => |lpWeighted.toSeq finPart n| * (ν : ℝ) ^ n) (n := N + 1)]
    refine Finset.sum_congr rfl ?_
    intro n _
    change |A.actionFinite (toCoeff (ν := ν) x) l n| * (ν : ℝ) ^ (n : ℕ) =
      |∑ j : Fin L, ∑ k : Fin (N + 1), A.finBlock l j n k * toCoeff (ν := ν) x j k| *
        (ν : ℝ) ^ (n : ℕ)
    simp [SystemBlockDiagData.actionFinite, Fin.is_le]
  have habs :
      ∑ n : Fin (N + 1),
          |∑ j : Fin L, ∑ k : Fin (N + 1), A.finBlock l j n k * toCoeff (ν := ν) x j k| *
            (ν : ℝ) ^ (n : ℕ) ≤
        ∑ j : Fin L,
          ∑ n : Fin (N + 1),
            |∑ k : Fin (N + 1), A.finBlock l j n k * toCoeff (ν := ν) x j k| *
              (ν : ℝ) ^ (n : ℕ) := by
    exact weighted_sum_abs_sum_le (N := N) (L := L)
      (w := fun n => (ν : ℝ) ^ (n : ℕ))
      (hw := fun n => pow_nonneg ν.coe_nonneg _)
      (f := fun j n => ∑ k : Fin (N + 1), A.finBlock l j n k * toCoeff (ν := ν) x j k)
  have hperj :
      ∀ j : Fin L,
        ∑ n : Fin (N + 1),
            |∑ k : Fin (N + 1), A.finBlock l j n k * toCoeff (ν := ν) x j k| *
              (ν : ℝ) ^ (n : ℕ) ≤
          blockEntryNorm ν A.finBlock l j *
            ∑ k : Fin (N + 1), |toCoeff (ν := ν) x j k| * (ν : ℝ) ^ (k : ℕ) := by
    intro j
    simpa [blockEntryNorm] using
      finiteMatrix_weighted_l1_bound (ν := ν) (M := A.finBlock l j)
        (v := fun k => toCoeff (ν := ν) x j k)
  have hsumj :
      ∑ j : Fin L,
          ∑ n : Fin (N + 1),
            |∑ k : Fin (N + 1), A.finBlock l j n k * toCoeff (ν := ν) x j k| *
              (ν : ℝ) ^ (n : ℕ) ≤
        ∑ j : Fin L,
          blockEntryNorm ν A.finBlock l j *
            ∑ k : Fin (N + 1), |toCoeff (ν := ν) x j k| * (ν : ℝ) ^ (k : ℕ) := by
    refine Finset.sum_le_sum ?_
    intro j _
    exact hperj j
  have hcoeff :
      ∀ j : Fin L,
        ∑ k : Fin (N + 1), |toCoeff (ν := ν) x j k| * (ν : ℝ) ^ (k : ℕ) ≤ ‖x‖ := by
    intro j
    exact (SystemBlockDiagData.finiteCoeffNorm_le_component_norm (ν := ν) (N := N) (x := x) j).trans
      (norm_le_pi_norm x j)
  have hrow :
      ∑ j : Fin L,
          blockEntryNorm ν A.finBlock l j *
            ∑ k : Fin (N + 1), |toCoeff (ν := ν) x j k| * (ν : ℝ) ^ (k : ℕ) ≤
        blockRowNorm ν A.finBlock l * ‖x‖ := by
    have hsum :
        ∑ j : Fin L,
            blockEntryNorm ν A.finBlock l j *
              ∑ k : Fin (N + 1), |toCoeff (ν := ν) x j k| * (ν : ℝ) ^ (k : ℕ) ≤
          (∑ j : Fin L, blockEntryNorm ν A.finBlock l j) * ‖x‖ := by
      exact sum_mul_le_sum_mul_const (L := L)
        (a := fun j => blockEntryNorm ν A.finBlock l j)
        (b := fun j => ∑ k : Fin (N + 1), |toCoeff (ν := ν) x j k| * (ν : ℝ) ^ (k : ℕ))
        (C := ‖x‖)
        (ha := fun j => blockEntryNorm_nonneg (ν := ν) A.finBlock l j)
        (hb := hcoeff)
    simpa [blockRowNorm] using hsum
  have hsum_bound :
      ∑ n : Fin (N + 1),
          |∑ j : Fin L, ∑ k : Fin (N + 1), A.finBlock l j n k * toCoeff (ν := ν) x j k| *
            (ν : ℝ) ^ (n : ℕ) ≤
        blockRowNorm ν A.finBlock l * ‖x‖ := by
    exact habs.trans (hsumj.trans hrow)
  exact hnorm_fin.trans_le hsum_bound

lemma SystemBlockDiagData.actionTail_component_norm_le
    (A : SystemBlockDiagData L N) (x : XL1 ν L) (l : Fin L) :
    ‖lpWeighted.mk (A.actionTail (toCoeff (ν := ν) x) l)
      (A.actionTail_mem_of_mem (ν := ν) (toCoeff (ν := ν) x) l (toCoeff_mem (ν := ν) x l))‖ ≤
      A.tailBound * ‖x l‖ := by
  refine l1Weighted.norm_mk_le_of_pointwise _ _ (x l) A.tailBound (fun n => ?_)
  change |A.actionTail (toCoeff (ν := ν) x) l n| ≤ A.tailBound * |toCoeff (ν := ν) x l n|
  by_cases hn : n ≤ N
  · rw [SystemBlockDiagData.actionTail_finite A _ l n hn, abs_zero]
    exact mul_nonneg (A.tailBound_nonneg_at l) (abs_nonneg _)
  · rw [SystemBlockDiagData.actionTail_tail A _ l n (Nat.lt_of_not_ge hn), abs_mul]
    exact mul_le_mul_of_nonneg_right (A.tailBound_spec l n (Nat.lt_of_not_ge hn)) (abs_nonneg _)

lemma SystemBlockDiagData.applyX_component_eq_finite_add_tail
    (A : SystemBlockDiagData L N) (x : XL1 ν L) (l : Fin L) :
    A.applyX (ν := ν) x l =
      lpWeighted.mk (A.actionFinite (toCoeff (ν := ν) x) l)
        (A.actionFinite_mem (ν := ν) (toCoeff (ν := ν) x) l) +
      lpWeighted.mk (A.actionTail (toCoeff (ν := ν) x) l)
        (A.actionTail_mem_of_mem (ν := ν) (toCoeff (ν := ν) x) l (toCoeff_mem (ν := ν) x l)) := by
  apply lpWeighted.ext
  intro n
  change A.action (toCoeff (ν := ν) x) l n =
      A.actionFinite (toCoeff (ν := ν) x) l n + A.actionTail (toCoeff (ν := ν) x) l n
  simp [SystemBlockDiagData.action_eq_actionFinite_add_actionTail]

lemma SystemBlockDiagData.applyX_component_norm_le
    (A : SystemBlockDiagData L N) (x : XL1 ν L) (l : Fin L) :
    ‖A.applyX (ν := ν) x l‖ ≤ (blockRowNorm ν A.finBlock l + A.tailBound) * ‖x‖ := by
  let finPart : l1Weighted ν :=
    lpWeighted.mk (A.actionFinite (toCoeff (ν := ν) x) l)
      (A.actionFinite_mem (ν := ν) (toCoeff (ν := ν) x) l)
  let tailPart : l1Weighted ν :=
    lpWeighted.mk (A.actionTail (toCoeff (ν := ν) x) l)
      (A.actionTail_mem_of_mem (ν := ν) (toCoeff (ν := ν) x) l (toCoeff_mem (ν := ν) x l))
  have hdecomp : A.applyX (ν := ν) x l = finPart + tailPart := by
    simpa [finPart, tailPart] using A.applyX_component_eq_finite_add_tail (ν := ν) x l
  have hfin : ‖finPart‖ ≤ blockRowNorm ν A.finBlock l * ‖x‖ := by
    simpa [finPart] using A.actionFinite_component_norm_le_row (ν := ν) x l
  have hC_nonneg : 0 ≤ A.tailBound := A.tailBound_nonneg_at l
  have htail_component : ‖tailPart‖ ≤ A.tailBound * ‖x l‖ := by
    simpa [tailPart] using A.actionTail_component_norm_le (ν := ν) x l
  have htail : ‖tailPart‖ ≤ A.tailBound * ‖x‖ := by
    exact htail_component.trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm x l) hC_nonneg)
  have h₁ : ‖A.applyX (ν := ν) x l‖ ≤ ‖finPart‖ + ‖tailPart‖ := by
    rw [hdecomp]
    exact norm_add_le _ _
  have h₂ :
      ‖finPart‖ + ‖tailPart‖ ≤ blockRowNorm ν A.finBlock l * ‖x‖ + A.tailBound * ‖x‖ := by
    exact add_le_add hfin htail
  have h₃ :
      blockRowNorm ν A.finBlock l * ‖x‖ + A.tailBound * ‖x‖ =
        (blockRowNorm ν A.finBlock l + A.tailBound) * ‖x‖ := by
    ring
  exact h₁.trans (h₂.trans_eq h₃)

lemma SystemBlockDiagData.tailBound_nonneg [NeZero L] (A : SystemBlockDiagData L N) :
    0 ≤ A.tailBound := by
  let l0 : Fin L := ⟨0, Nat.pos_of_ne_zero (NeZero.ne L)⟩
  exact A.tailBound_nonneg_at l0

lemma SystemBlockDiagData.toLinearMap_bound [NeZero L]
    (A : SystemBlockDiagData L N) :
    ∀ x : XL1 ν L,
      ‖A.toLinearMap (ν := ν) x‖ ≤
        (finiteBlockMatrixNorm ν A.finBlock + A.tailBound) * ‖x‖ := by
  intro x
  have hC_nonneg :
      0 ≤ (finiteBlockMatrixNorm ν A.finBlock + A.tailBound) * ‖x‖ := by
    exact mul_nonneg
      (add_nonneg (finiteBlockMatrixNorm_nonneg (ν := ν) A.finBlock) (A.tailBound_nonneg))
      (norm_nonneg x)
  refine (pi_norm_le_iff_of_nonneg hC_nonneg).2 ?_
  intro l
  have hcomp :
      ‖A.applyX (ν := ν) x l‖ ≤ (blockRowNorm ν A.finBlock l + A.tailBound) * ‖x‖ := by
    exact A.applyX_component_norm_le (ν := ν) x l
  have hrow :
      blockRowNorm ν A.finBlock l + A.tailBound ≤
        finiteBlockMatrixNorm ν A.finBlock + A.tailBound := by
    exact add_le_add
      (Finset.le_sup' (f := fun i : Fin L => blockRowNorm ν A.finBlock i) (Finset.mem_univ l))
      le_rfl
  exact hcomp.trans (mul_le_mul_of_nonneg_right hrow (norm_nonneg x))

/-- Continuous-linear lift of the 8.2 block operator data on `(ℓ¹_ν)^L`,
with explicit operator bound `max_l Σ_j ‖A_{l,j}‖ + tailBound`. -/
def SystemBlockDiagData.toCLM [NeZero L]
    (A : SystemBlockDiagData L N) : XL1 ν L →L[ℝ] XL1 ν L :=
  LinearMap.mkContinuous (A.toLinearMap (ν := ν))
    (finiteBlockMatrixNorm ν A.finBlock + A.tailBound)
    (A.toLinearMap_bound (ν := ν))

@[simp]
lemma SystemBlockDiagData.toCLM_apply [NeZero L]
    (A : SystemBlockDiagData L N) (x : XL1 ν L) :
    A.toCLM (ν := ν) x = A.applyX (ν := ν) x := by
  simp [SystemBlockDiagData.toCLM, SystemBlockDiagData.toLinearMap]

@[simp]
lemma SystemBlockDiagData.toCoeff_toCLM [NeZero L]
    (A : SystemBlockDiagData L N) (x : XL1 ν L) (l : Fin L) (n : ℕ) :
    toCoeff (ν := ν) (A.toCLM (ν := ν) x) l n = A.action (toCoeff (ν := ν) x) l n := by
  simp

@[simp]
lemma SystemBlockDiagData.toCoeff_comp_toCLM [NeZero L]
    (A B : SystemBlockDiagData L N) (x : XL1 ν L) (l : Fin L) (n : ℕ) :
    toCoeff (ν := ν) ((A.toCLM (ν := ν)).comp (B.toCLM (ν := ν)) x) l n =
      A.action (B.action (toCoeff (ν := ν) x)) l n := by
  simp

/-! ## 6. CLM Composition And Residual Bridges -/

/-- Function-level coefficient identity for CLM composition. -/
lemma SystemBlockDiagData.toCoeff_comp_toCLM_eq_action [NeZero L]
    (A B : SystemBlockDiagData L N) (x : XL1 ν L) :
    toCoeff (ν := ν) ((A.toCLM (ν := ν)).comp (B.toCLM (ν := ν)) x) =
      A.action (B.action (toCoeff (ν := ν) x)) := by
  funext l n
  exact SystemBlockDiagData.toCoeff_comp_toCLM
    (ν := ν) (A := A) (B := B) (x := x) (l := l) (n := n)

/-- Coefficient identity for the residual operator `id - A ∘ B`. -/
lemma SystemBlockDiagData.toCoeff_id_sub_comp_toCLM [NeZero L]
    (A B : SystemBlockDiagData L N) (x : XL1 ν L) (l : Fin L) (n : ℕ) :
    toCoeff (ν := ν) ((ContinuousLinearMap.id ℝ (XL1 ν L) -
      (A.toCLM (ν := ν)).comp (B.toCLM (ν := ν))) x) l n =
      toCoeff (ν := ν) x l n - A.action (B.action (toCoeff (ν := ν) x)) l n := by
  rw [ContinuousLinearMap.sub_apply]
  change lpWeighted.toSeq
      ((x - ((A.toCLM (ν := ν)).comp (B.toCLM (ν := ν)) x)) l) n =
      toCoeff (ν := ν) x l n - A.action (B.action (toCoeff (ν := ν) x)) l n
  rw [Pi.sub_apply, lpWeighted.sub_toSeq]
  change toCoeff (ν := ν) x l n -
      toCoeff (ν := ν) (((A.toCLM (ν := ν)).comp (B.toCLM (ν := ν)) x)) l n =
    toCoeff (ν := ν) x l n - A.action (B.action (toCoeff (ν := ν) x)) l n
  rw [SystemBlockDiagData.toCoeff_comp_toCLM_eq_action
    (ν := ν) (A := A) (B := B) (x := x)]

/-- Finite-mode coefficient form of `(id - A ∘ B)x` (`n ≤ N`). -/
lemma SystemBlockDiagData.toCoeff_id_sub_comp_toCLM_finite [NeZero L]
    (A B : SystemBlockDiagData L N) (x : XL1 ν L)
    (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    toCoeff (ν := ν) ((ContinuousLinearMap.id ℝ (XL1 ν L) -
      (A.toCLM (ν := ν)).comp (B.toCLM (ν := ν))) x) l n =
      toCoeff (ν := ν) x l n -
        ∑ j : Fin L, ∑ k : Fin (N + 1),
          A.finBlock l j ⟨n, Nat.lt_succ_of_le hn⟩ k * (B.action (toCoeff (ν := ν) x) j k) := by
  rw [SystemBlockDiagData.toCoeff_id_sub_comp_toCLM (ν := ν) (A := A) (B := B) (x := x) (l := l) (n := n)]
  rw [SystemBlockDiagData.action_comp_finite
    (A := A) (B := B) (b := toCoeff (ν := ν) x) (l := l) (n := n) hn]

/-- Tail-mode coefficient form of `(id - A ∘ B)x` (`N < n`). -/
lemma SystemBlockDiagData.toCoeff_id_sub_comp_toCLM_tail [NeZero L]
    (A B : SystemBlockDiagData L N) (x : XL1 ν L)
    (l : Fin L) (n : ℕ) (hn : N < n) :
    toCoeff (ν := ν) ((ContinuousLinearMap.id ℝ (XL1 ν L) -
      (A.toCLM (ν := ν)).comp (B.toCLM (ν := ν))) x) l n =
      (1 - A.tailDiag l n * B.tailDiag l n) * toCoeff (ν := ν) x l n := by
  rw [SystemBlockDiagData.toCoeff_id_sub_comp_toCLM (ν := ν) (A := A) (B := B) (x := x) (l := l) (n := n)]
  rw [SystemBlockDiagData.action_comp_tail
    (A := A) (B := B) (b := toCoeff (ν := ν) x) (l := l) (n := n) hn]
  ring

lemma SystemBlockDiagData.norm_toCLM_le [NeZero L]
    (A : SystemBlockDiagData L N) :
    ‖A.toCLM (ν := ν)‖ ≤ finiteBlockMatrixNorm ν A.finBlock + A.tailBound := by
  exact LinearMap.mkContinuous_norm_le _
    (add_nonneg (finiteBlockMatrixNorm_nonneg (ν := ν) A.finBlock) (A.tailBound_nonneg))
    (A.toLinearMap_bound (ν := ν))

lemma toCLM_ext_of_toCoeff_eq [NeZero L]
    (T S : XL1 ν L →L[ℝ] XL1 ν L)
    (hcoeff : ∀ x : XL1 ν L, ∀ l : Fin L, ∀ n : ℕ,
      toCoeff (ν := ν) (T x) l n = toCoeff (ν := ν) (S x) l n) :
    T = S := by
  ext x l n
  simpa [toCoeff] using hcoeff x l n

/-- Reusable norm transfer:
if `id - A∘B` is identified with a block-diagonal defect CLM `D.toCLM`,
its norm is bounded by the defect's finite+tail structural bound. -/
lemma SystemBlockDiagData.norm_id_sub_comp_le_of_eq_defect [NeZero L]
    (A B D : SystemBlockDiagData L N)
    (hD : ContinuousLinearMap.id ℝ (XL1 ν L) -
        (A.toCLM (ν := ν)).comp (B.toCLM (ν := ν)) = D.toCLM (ν := ν)) :
    Z₀_norm (A.toCLM (ν := ν)) (B.toCLM (ν := ν)) ≤
      finiteBlockMatrixNorm ν D.finBlock + D.tailBound := by
  show ‖_‖ ≤ _; rw [hD]
  exact D.norm_toCLM_le (ν := ν)

/-- `Z₀` bound transfer to the canonical Core API from a defect CLM identity. -/
lemma SystemBlockDiagData.Z₀_norm_le_of_eq_defect [NeZero L]
    (A B D : SystemBlockDiagData L N)
    (hD : ContinuousLinearMap.id ℝ (XL1 ν L) -
        (A.toCLM (ν := ν)).comp (B.toCLM (ν := ν)) = D.toCLM (ν := ν)) :
    Z₀_norm (A.toCLM (ν := ν)) (B.toCLM (ν := ν)) ≤
      finiteBlockMatrixNorm ν D.finBlock + D.tailBound := by
  exact SystemBlockDiagData.norm_id_sub_comp_le_of_eq_defect
    (ν := ν) (A := A) (B := B) (D := D) hD

/-- General injectivity transfer from coefficient-level finite/tail hypotheses.

`h_fin` states injectivity of the finite-mode block action on coefficients `0..N`.
`h_tail` states nonvanishing tail diagonal on modes `N+1..∞`.
Together they imply injectivity of the lifted CLM `A.toCLM`. -/
lemma SystemBlockDiagData.injective_toCLM_of_finite_part_injective [NeZero L]
    (A : SystemBlockDiagData L N)
    (h_fin :
      ∀ d : SystemCoeff L,
        (∀ l : Fin L, ∀ n : Fin (N + 1),
          (∑ j : Fin L, ∑ k : Fin (N + 1), A.finBlock l j n k * d j k) = 0) →
        (∀ l : Fin L, ∀ n : Fin (N + 1), d l n = 0))
    (h_tail : ∀ l n, N < n → A.tailDiag l n ≠ 0) :
    Function.Injective (A.toCLM (ν := ν)) := by
  intro x y hxy
  have hdiff : A.toCLM (ν := ν) (x - y) = 0 := by
    have hsub : A.toCLM (ν := ν) x - A.toCLM (ν := ν) y = 0 := by
      simpa [sub_eq_zero] using hxy
    simpa [map_sub] using hsub
  have h_tail_zero : ∀ l : Fin L, ∀ n : ℕ, N < n → toCoeff (ν := ν) (x - y) l n = 0 := by
    intro l n hn
    have hcoeff :
        toCoeff (ν := ν) (A.toCLM (ν := ν) (x - y)) l n = 0 := by
      rw [hdiff]
      simp [toCoeff]
    rw [SystemBlockDiagData.toCoeff_toCLM (ν := ν) (A := A) (x := x - y) (l := l) (n := n)] at hcoeff
    rw [SystemBlockDiagData.action_tail
      (A := A) (b := toCoeff (ν := ν) (x - y)) (l := l) (n := n) hn] at hcoeff
    exact (mul_eq_zero.mp hcoeff).resolve_left (h_tail l n hn)
  have h_fin_eq :
      ∀ l : Fin L, ∀ n : Fin (N + 1),
        (∑ j : Fin L, ∑ k : Fin (N + 1),
          A.finBlock l j n k * toCoeff (ν := ν) (x - y) j k) = 0 := by
    intro l n
    have hcoeff :
        toCoeff (ν := ν) (A.toCLM (ν := ν) (x - y)) l n = 0 := by
      rw [hdiff]
      simp [toCoeff]
    rw [SystemBlockDiagData.toCoeff_toCLM (ν := ν) (A := A) (x := x - y) (l := l) (n := n)] at hcoeff
    rw [SystemBlockDiagData.action_fin
      (A := A) (b := toCoeff (ν := ν) (x - y)) (l := l) (n := n)] at hcoeff
    exact hcoeff
  have h_fin_zero :
      ∀ l : Fin L, ∀ n : Fin (N + 1), toCoeff (ν := ν) (x - y) l n = 0 :=
    h_fin (toCoeff (ν := ν) (x - y)) h_fin_eq
  have hxy_zero : x - y = 0 := by
    funext l
    apply lpWeighted.ext
    intro n
    by_cases hn : n ≤ N
    · exact h_fin_zero l ⟨n, Nat.lt_succ_of_le hn⟩
    · exact h_tail_zero l n (Nat.lt_of_not_ge hn)
  exact sub_eq_zero.mp hxy_zero

/-! ## 7. Block Identity Action

Helper: `x_{l,n} = ∑_j ∑_k (if l = j then I else 0)_{n,k} * x_{j,k}`. -/

private lemma block_identity_action
    (c : SystemCoeff L) (l : Fin L) (n : Fin (N + 1)) :
    c l n = ∑ j : Fin L, ∑ k : Fin (N + 1),
      (if l = j then (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) else 0) n k * c j k := by
  rw [Finset.sum_eq_single l]
  · simp [Matrix.one_apply]
  · intro j _ hj; simp [Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ l) h

/-! ## 8. Defect Construction For Tail-Canceling Pairs (General L) -/

/-- Defect data for pairs where componentwise tail diagonals multiply to 1.
The residual `I - A∘B` has zero tail, so `tailBound = 0`. -/
def SystemBlockDiagData.defectOfTailCancel [NeZero L]
    (A B : SystemBlockDiagData L N)
    (_ : ∀ l, ∀ n, N < n → A.tailDiag l n * B.tailDiag l n = 1) :
    SystemBlockDiagData L N where
  finBlock := fun l j =>
    (if l = j then (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) else 0) -
      ∑ m, A.finBlock l m * B.finBlock m j
  tailDiag := fun _ _ => 0
  tailBound := 0
  tailBound_spec := by intro l n _; simp

/-- The defect CLM equals `I - A.toCLM ∘ B.toCLM` when tail diagonals cancel. -/
lemma SystemBlockDiagData.id_sub_comp_eq_defect_toCLM [NeZero L]
    (A B : SystemBlockDiagData L N)
    (htail : ∀ l, ∀ n, N < n → A.tailDiag l n * B.tailDiag l n = 1) :
    ContinuousLinearMap.id ℝ (XL1 ν L) -
      (A.toCLM (ν := ν)).comp (B.toCLM (ν := ν)) =
    (A.defectOfTailCancel B htail).toCLM (ν := ν) := by
  apply toCLM_ext_of_toCoeff_eq
  intro x l n
  rw [SystemBlockDiagData.toCoeff_id_sub_comp_toCLM (ν := ν) A B x l n,
      ← SystemBlockDiagData.comp_action_eq_action_comp A B (toCoeff (ν := ν) x),
      SystemBlockDiagData.toCoeff_toCLM (ν := ν) _ x l n]
  by_cases hn : n ≤ N
  · -- Finite mode
    rw [SystemBlockDiagData.action_finite _ _ _ _ hn,
        SystemBlockDiagData.action_finite _ _ _ _ hn]
    -- x_{l,n} - ∑_j ∑_k (AB)_{l,j,n,k} * x_{j,k} = ∑_j ∑_k D_{l,j,n,k} * x_{j,k}
    -- where D_{l,j} = (δ_{l,j}·I - (AB)_{l,j}). Use x = I·x at block level.
    simp only [SystemBlockDiagData.comp_finBlock, defectOfTailCancel, Matrix.sub_apply, sub_mul]
    simp_rw [Finset.sum_sub_distrib]
    have h := block_identity_action (toCoeff (ν := ν) x) l ⟨n, Nat.lt_succ_of_le hn⟩
    linarith
  · -- Tail mode: (1 - tail_A * tail_B) * x = 0
    have hlt : N < n := Nat.lt_of_not_ge hn
    rw [SystemBlockDiagData.action_tail _ _ _ _ hlt,
        SystemBlockDiagData.action_tail _ _ _ _ hlt]
    simp only [defectOfTailCancel, SystemBlockDiagData.comp_tailDiag]
    simp [htail l n hlt]

/-- Z₀ bound for tail-canceling pairs (general L):
`‖I - A.toCLM ∘ B.toCLM‖ ≤ finiteBlockMatrixNorm(defect.finBlock)`. -/
lemma SystemBlockDiagData.Z₀_le_of_tailCancel [NeZero L]
    (A B : SystemBlockDiagData L N)
    (htail : ∀ l, ∀ n, N < n → A.tailDiag l n * B.tailDiag l n = 1) :
    Z₀_norm (A.toCLM (ν := ν)) (B.toCLM (ν := ν)) ≤
    finiteBlockMatrixNorm ν (A.defectOfTailCancel B htail).finBlock := by
  have hD := A.id_sub_comp_eq_defect_toCLM (ν := ν) B htail
  show ‖_‖ ≤ _; rw [hD]
  have h := (A.defectOfTailCancel B htail).norm_toCLM_le (ν := ν)
  have htb : (A.defectOfTailCancel B htail).tailBound = 0 := rfl
  rwa [htb, add_zero] at h

/-! ## 9. Z₁ Infrastructure (General L)

Composition norm bounds when the inner operator kills finite modes.
General-L versions of the scalar APIs in `Scalar.lean`.
-/

/-- Composition norm bound when the inner operator `T` kills finite modes (general L).
If `toCoeff(T h) l n = 0` for all `l`, `n ≤ N`, then `A.toCLM` acts on `T(h)` purely
via its tail diagonal, giving `‖A.toCLM.comp T‖ ≤ A.tailBound * ‖T‖`. -/
lemma SystemBlockDiagData.norm_comp_of_fin_kill [NeZero L]
    (A : SystemBlockDiagData L N) (T : XL1 ν L →L[ℝ] XL1 ν L)
    (hfin : ∀ h, ∀ l : Fin L, ∀ n, n ≤ N → toCoeff (ν := ν) (T h) l n = 0) :
    ‖(A.toCLM (ν := ν)).comp T‖ ≤ A.tailBound * ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg A.tailBound_nonneg (ContinuousLinearMap.opNorm_nonneg T))
  intro h
  show ‖A.toCLM (ν := ν) (T h)‖ ≤ _
  -- Pi norm: suffices to bound each component
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg
    (mul_nonneg A.tailBound_nonneg (ContinuousLinearMap.opNorm_nonneg T))
    (norm_nonneg h))).2 ?_
  intro l
  -- Decompose ‖(A(Th))_l‖ into finite + tail
  have hdecomp := A.applyX_component_eq_finite_add_tail (ν := ν) (T h) l
  change ‖A.applyX (ν := ν) (T h) l‖ ≤ _
  rw [hdecomp]
  -- Finite part: all input coefficients are zero → actionFinite = 0
  have h_fin_zero :
      lpWeighted.mk (A.actionFinite (toCoeff (ν := ν) (T h)) l)
        (A.actionFinite_mem (ν := ν) (toCoeff (ν := ν) (T h)) l) = 0 :=
    lpWeighted.ext fun n => by
      simp only [lpWeighted.mk_apply, lpWeighted.zero_toSeq]
      exact A.actionFinite_eq_zero_of_coeff_fin_zero _
        (fun j k => hfin h j k (Nat.lt_succ_iff.mp k.2)) l n
  rw [h_fin_zero, zero_add]
  -- Tail part: ≤ tailBound * ‖(Th)_l‖ ≤ tailBound * ‖Th‖ ≤ tailBound * ‖T‖ * ‖h‖
  have h_tail := A.actionTail_component_norm_le (ν := ν) (T h) l
  have h_comp_le : ‖(T h) l‖ ≤ ‖T h‖ := norm_le_pi_norm (T h) l
  have h_op : ‖T h‖ ≤ ‖T‖ * ‖h‖ := ContinuousLinearMap.le_opNorm T h
  exact h_tail.trans (mul_le_mul_of_nonneg_left
    (h_comp_le.trans h_op) A.tailBound_nonneg) |>.trans_eq (by ring)

/-- Operator norm domination at system level: if `D` kills finite modes per component
and agrees with `E` on tail modes per component, then `‖D‖ ≤ ‖E‖`.
General-L version of `l1Weighted.opNorm_le_of_fin_kill_tail_eq`. -/
lemma XL1.opNorm_le_of_fin_kill_tail_eq [NeZero L] (N : ℕ)
    (D E : XL1 ν L →L[ℝ] XL1 ν L)
    (hfin : ∀ h, ∀ l : Fin L, ∀ n, n ≤ N → toCoeff (ν := ν) (D h) l n = 0)
    (htail : ∀ h, ∀ l : Fin L, ∀ n, N < n →
      toCoeff (ν := ν) (D h) l n = toCoeff (ν := ν) (E h) l n) :
    ‖D‖ ≤ ‖E‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg E)
  intro h
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg
    (ContinuousLinearMap.opNorm_nonneg E) (norm_nonneg h))).2 ?_
  intro l
  -- ‖(Dh)_l‖ = tail_tsum since finite part is zero
  rw [l1Weighted.norm_eq_tailTsum_of_fin_zero ((D h) l) (N + 1)
    (fun n hn => hfin h l n (by omega))]
  -- Tail of D = tail of E ≤ ‖(Eh)_l‖ ≤ ‖Eh‖ ≤ ‖E‖ * ‖h‖
  exact (l1Weighted.tailTsum_le_norm_of_eq ((D h) l) ((E h) l) (N + 1)
    (fun n hn => htail h l n (by omega))).trans
    ((norm_le_pi_norm (E h) l).trans (ContinuousLinearMap.le_opNorm E h))

/-- Z₁ pipeline (general L): if `T` kills finite modes and is dominated by `E` on tail,
then `‖A.toCLM.comp T‖ ≤ A.tailBound * ‖E‖ ≤ C`. Equation-independent. -/
lemma SystemBlockDiagData.Z₁_le_of_fin_kill_tail_dom [NeZero L] (N : ℕ)
    (A : SystemBlockDiagData L N)
    (T E : XL1 ν L →L[ℝ] XL1 ν L)
    (hfin : ∀ h, ∀ l : Fin L, ∀ n, n ≤ N → toCoeff (ν := ν) (T h) l n = 0)
    (htail : ∀ h, ∀ l : Fin L, ∀ n, N < n →
      toCoeff (ν := ν) (T h) l n = toCoeff (ν := ν) (E h) l n)
    (C : ℝ) (hC : A.tailBound * ‖E‖ ≤ C) :
    ‖(A.toCLM (ν := ν)).comp T‖ ≤ C :=
  (A.norm_comp_of_fin_kill T hfin).trans
    ((mul_le_mul_of_nonneg_left (XL1.opNorm_le_of_fin_kill_tail_eq N T E hfin htail)
      A.tailBound_nonneg).trans hC)

end SystemBlockDiagConcrete

end SystemTaylorODE
