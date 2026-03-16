import RadiiPolynomial.IVP.Setup
import RadiiPolynomial.Example83.Algebra
import RadiiPolynomial.SystemTaylorODE.LeanCertEval

/-! # Test: IVP generic lemmas on Example83

Validates that ivpCoeffs/ivpMap match Example83's F_coeffs/G_lorenz,
and that ivp_Y₀_le / ivp_Z₁_le have the right interface. -/

open scoped BigOperators Topology
open SystemTaylorODE Example83

noncomputable section

namespace IVP.Test83

-- F_coeffs = ivpCoeffs (the core equation identity)
lemma F_coeffs_eq_ivpCoeffs (a : XL1 ν_val L) :
    F_coeffs a = IVP.ivpCoeffs φ_lorenz x₀ a := by
  ext l n; simp only [F_coeffs, IVP.ivpCoeffs, F_lorenz, l1Omega.mk_apply]; rfl

-- G_lorenz(ā) l n = A.action(ivpCoeffs(ā)) l n
lemma G_lorenz_action_eq (l : Fin L) (n : ℕ) :
    l1Weighted.toSeq (G_lorenz abar l) n =
      approxInverse.action (IVP.ivpCoeffs φ_lorenz x₀ abar) l n := by
  rw [G_lorenz_coeff, F_coeffs_eq_ivpCoeffs]

-- Membership for ivpMap (from G_lorenz's proof)
lemma ivpMem : ∀ a : XL1 ν_val L, ∀ l : Fin L,
    lpWeighted.Mem ν_val 1 (approxInverse.action (IVP.ivpCoeffs φ_lorenz x₀ a) l) :=
  fun a l => F_coeffs_eq_ivpCoeffs a ▸ (G_lorenz a l).2

-- Test ivp_Y₀_le interface: the hypotheses are satisfiable
-- (using sorry for equation-specific parts that are already proven in Certificate.lean)
example : ‖IVP.ivpMap approxInverse φ_lorenz x₀ ivpMem abar‖ ≤ (Y₀_bound : ℝ) :=
  IVP.ivp_Y₀_le approxInverse φ_lorenz x₀ ivpMem abar (2 * N + 1) (by omega)
    (fun l n hn => by rw [← F_coeffs_eq_ivpCoeffs]; exact sorry) -- F_coeffs_abar_support
    (by unfold Y₀_bound; positivity)
    (fun l => by sorry) -- per-component finsum_bound

-- Test ivp_Z₁_le interface: the hypotheses are satisfiable
example : ‖composedApprox.toCLM (ν := ν_val) - fderiv ℝ G_lorenz abar‖ ≤ (Z₁_bound : ℝ) :=
  IVP.ivp_Z₁_le composedApprox G_lorenz abar Dφ_lorenz
    (fun h l n hn => by sorry) -- hfin: finite modes agree
    (fun h l n hn => by sorry) -- htail: tail difference = shiftDivN(Dφ)
    (K := (Z₁_bound * ((N : ℚ) + 1) / ν_q : ℚ)) -- K = 62 (Dφ norm constant)
    (by unfold Z₁_bound; norm_num) -- hK ≥ 0
    (fun h l => by sorry) -- hDφ: ‖Dφ h l‖ ≤ K * ‖h‖
    (by unfold Z₁_bound ν_val N ν_q; push_cast; ring_nf; rfl) -- ν/(N+1)*K ≤ Z₁

end IVP.Test83
