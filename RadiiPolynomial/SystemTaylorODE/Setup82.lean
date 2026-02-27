import RadiiPolynomial.SystemTaylorODE.Core
import RadiiPolynomial.SystemTaylorODE.lpWeighted
import RadiiPolynomial.SystemTaylorODE.WitnessSpec

/-!
# SystemTaylorODE Setup (Section 8.2, pages 195-201)

Bookkeeping layer for the 8.2 system setup:

- component projections `πˡ`
- truncation/finite-tail projections `π_N`, `π_{N,∞}`
- finite/tail subsets `X_N`, `X_{N,∞}`, `Y_N`, `Y_{N,∞}`
- coefficient-level shift and diagonal-tail maps matching equations (8.25), (8.26)

This file stays abstract over a sequence-space model (`Seq`) and does not
depend on `TaylorODE_Direct`.

Reference scope:
- IVP class and coefficient encoding from (8.13)-(8.15).
- Finite/tail operator bookkeeping used for the split in (8.19)-(8.21).

## File map

1. Abstract sequence model interface (`SeqModel`)
2. Projection/splitting layer (`π_N`, `π_{N,∞}`, `X_N`, `X_{N,∞}`, ...)
3. Coefficient-level operators from (8.25), (8.26)
4. Concrete backend instance for `l1Weighted`
-/

open scoped Topology

noncomputable section

namespace SystemTaylorODE

variable {Seq : PosReal → Type*}
variable [∀ ν, NormedAddCommGroup (Seq ν)]

/-- Minimal sequence-space interface used for Chapter 8 bookkeeping.
Reference: abstraction layer for the coefficient-space manipulations used around
Section 8.2 (pages 195-201). -/
class SeqModel (Seq : PosReal → Type*) [∀ ν, NormedAddCommGroup (Seq ν)] where
  /-- Coefficient extraction. -/
  coeff : ∀ {ν}, Seq ν → ℕ → ℝ
  /-- Coefficient truncation at order `N`. -/
  trunc : ∀ {ν}, ℕ → Seq ν → Seq ν
  /-- Truncation formula on coefficients. -/
  coeff_trunc : ∀ {ν} (N : ℕ) (a : Seq ν) (n : ℕ),
      coeff (trunc N a) n = if n ≤ N then coeff a n else 0
  /-- Coefficient behavior under subtraction. -/
  coeff_sub : ∀ {ν} (a b : Seq ν) (n : ℕ),
      coeff (a - b) n = coeff a n - coeff b n

variable [SeqModel Seq]

/-! ## 1. Projection And Finite/Tail Set Layer -/

section Projections

variable {ν ν' : PosReal} {L : ℕ}

/-- Component projection `πˡ : X -> Seq ν`.
Reference: Section 8.2, page 196 ("Let πˡ : (`ℓ¹_ν)^L → `ℓ¹_ν denote projection"). -/
def piComponent (l : Fin L) (a : X Seq ν L) : Seq ν := a l

/-- Scalar truncation operator `π_N : Seq ν -> Seq ν`.
Reference: Section 8.2, page 196 definition of `π_N`. -/
def piNScalar (N : ℕ) (a : Seq ν) : Seq ν := SeqModel.trunc N a

/-- System-level truncation `π_N : X -> X` applied componentwise.
Reference: Section 8.2, page 196, componentwise `π_N^L`. -/
def piN (N : ℕ) (a : X Seq ν L) : X Seq ν L :=
  fun l => piNScalar N (a l)

/-- System-level tail projection `π_{N,∞} = I - π_N`.
Reference: Section 8.2, page 196 definition of `π_{N,∞}` and `π_{N,∞}^L`. -/
def piNInf (N : ℕ) (a : X Seq ν L) : X Seq ν L :=
  fun l => a l - piNScalar N (a l)

/-- Finite-support subset `X_N` (all coefficients above `N` vanish).
Reference: Section 8.2, page 196 (`X_N` definition). -/
def XN (ν : PosReal) (L N : ℕ) : Set (X Seq ν L) :=
  {a | ∀ l n, N < n → SeqModel.coeff (a l) n = 0}

/-- Tail subset `X_{N,∞}` (all coefficients up to `N` vanish).
Reference: Section 8.2, page 196 (`X_{N,∞}` definition). -/
def XNInf (ν : PosReal) (L N : ℕ) : Set (X Seq ν L) :=
  {a | ∀ l n, n ≤ N → SeqModel.coeff (a l) n = 0}

/-- Finite-support subset `Y_N` for `Y = (Seq ν')^L`.
Reference: Section 8.2, page 197 (range-side finite/tail decomposition). -/
def YN (ν' : PosReal) (L N : ℕ) : Set (Y Seq ν' L) :=
  {a | ∀ l n, N < n → SeqModel.coeff (a l) n = 0}

/-- Tail subset `Y_{N,∞}` for `Y = (Seq ν')^L`.
Reference: Section 8.2, page 197 (range-side finite/tail decomposition). -/
def YNInf (ν' : PosReal) (L N : ℕ) : Set (Y Seq ν' L) :=
  {a | ∀ l n, n ≤ N → SeqModel.coeff (a l) n = 0}

/-- Helper lemma: truncated object lies in `X_N`.
Reference: immediate formal consequence of the `X_N` definition (page 196). -/
lemma piN_mem_XN (N : ℕ) (a : X Seq ν L) :
    piN N a ∈ XN (Seq := Seq) ν L N := by
  intro l n hn
  change SeqModel.coeff (piNScalar N (a l)) n = 0
  simp [piNScalar, SeqModel.coeff_trunc, Nat.not_le.mpr hn]

/-- Helper lemma: tail projection lies in `X_{N,∞}`.
Reference: immediate formal consequence of the `X_{N,∞}` definition (page 196). -/
lemma piNInf_mem_XNInf (N : ℕ) (a : X Seq ν L) :
    piNInf N a ∈ XNInf (Seq := Seq) ν L N := by
  intro l n hn
  change SeqModel.coeff (a l - piNScalar N (a l)) n = 0
  simp [piNScalar, SeqModel.coeff_sub, SeqModel.coeff_trunc, hn]

end Projections

/-! ## 2. Coefficient-Level Operators (8.25), (8.26) -/

section CoefficientOperators

/-- Coefficient-level shift operator (equation 8.25, page 201):
`(Sa)_0 = 0`, `(Sa)_k = a_{k-1}` for `k >= 1`. -/
def shiftCoeff (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => a k

/-- Coefficient-level diagonal tail operator (equation 8.26, page 201):
`(Λ_N a)_k = 0` for `k <= N`, `(Λ_N a)_k = (1/k) a_k` for `k >= N+1`. -/
def lambdaNCoeff (N : ℕ) (a : ℕ → ℝ) : ℕ → ℝ := fun k =>
  if k ≤ N then 0 else (1 / (k : ℝ)) * a k

/-! Reference note:
The simp lemmas below are definitional consequences of (8.25)-(8.26). -/

@[simp] lemma shiftCoeff_zero (a : ℕ → ℝ) : shiftCoeff a 0 = 0 := rfl
@[simp] lemma shiftCoeff_succ (a : ℕ → ℝ) (k : ℕ) : shiftCoeff a (k + 1) = a k := rfl

lemma lambdaNCoeff_eq_zero_of_le (N : ℕ) (a : ℕ → ℝ) {k : ℕ} (hk : k ≤ N) :
    lambdaNCoeff N a k = 0 := by simp [lambdaNCoeff, hk]

lemma lambdaNCoeff_eq_inv_mul_of_lt (N : ℕ) (a : ℕ → ℝ) {k : ℕ} (hk : N < k) :
    lambdaNCoeff N a k = (1 / (k : ℝ)) * a k := by
  simp [lambdaNCoeff, Nat.not_le.mpr hk]

end CoefficientOperators

/-! ## 3. Concrete `l1Weighted` Backend -/

section ConcreteInstances

/-! Concrete backend for Section 8.2 using weighted `ℓ¹_ν` sequences. -/

/-- Concrete `SeqModel` instance for `Seq ν = l1Weighted ν`.
This instantiates the abstract projection/truncation API used in the
8.2 finite/tail setup ((8.19)-(8.21)). -/
instance instSeqModel_l1Weighted :
    SeqModel (fun ν => ↥(l1Weighted ν)) := by
  refine
    { coeff := fun {_ν} a n => lpWeighted.toSeq a n
      trunc := fun {_ν} N a => l1Weighted.trunc N a
      coeff_trunc := ?_
      coeff_sub := ?_ }
  · intro ν N a n
    exact l1Weighted.coeff_trunc (ν := ν) N a n
  · intro ν a b n
    simp

end ConcreteInstances

end SystemTaylorODE
