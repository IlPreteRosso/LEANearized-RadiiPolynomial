/-
  §2.1 Contraction Mapping — wrappers delegating to mathlib.
  We expose RP.* names used by the blueprint while reusing mathlib’s `ContractingWith`.
-/
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.NNReal.Basic


/-
  Defaults definitions to noncomputable type unless otherwise specified.
  This is needed for `ContractingWith` and `CompleteSpace` from mathlib.
-/
noncomputable section

/-
  Enables notation like ∑ and ∏.
  For iterations we use `Nat.iterate` from Lean core.
-/
open scoped BigOperators



namespace RP

/-- Completeness as a Prop alias so `checkdecls` finds `RP.CM_Complete`. -/
abbrev CM_Complete (X : Type*) [MetricSpace X] : Prop := CompleteSpace X


/-- `RP.CM_Contraction κ T` delegates to mathlib's `ContractingWith κ T`. -/
abbrev CM_Contraction {X : Type*} [MetricSpace X] (κ : NNReal) (T : X → X) : Prop :=
  ContractingWith κ T

/-- Picard iterates (n-fold iterate of `T` at `x0`). -/
abbrev CM_PicardIter {X : Type*} (T : X → X) (n : ℕ) (x0 : X) : X :=
  (Nat.iterate T n) x0


#check ContractingWith.exists_fixedPoint
#check ContractingWith.apriori_edist_iterate_efixedPoint_le

/- Thin wrappers delegating to mathlib so blueprint can reference RP.* names. -/

/- Wrapper TODOs for this snapshot:
   • CM_existsUnique should delegate to the mathlib lemma on contractions
     (e.g. `ContractingWith.exists_unique_fixedPoint`). Once the exact
     lemma name is confirmed in this toolchain, re-enable the wrapper as:
       theorem CM_existsUnique ... := by simpa using ...
   • CM_rate should similarly delegate to the geometric inequality lemma
     (e.g. `ContractingWith.dist_iterate_fixedPoint_le_geometric`). -/

-- Geometric rate wrapper (CM_rate): to be re-enabled with the exact lemma
-- name from this snapshot (likely `ContractingWith.dist_iterate_fixedPoint_le_geometric`).

-- /-- Convergence with geometric rate (distance version).
--     Many mathlib lemmas are stated with `edist` in `ℝ≥0∞`.
--     The version below uses the `dist` inequality provided by `ContractingWith`. -/
-- theorem CM_rate
--   {X : Type*} [MetricSpace X] [CompleteSpace X]
--   {κ : NNReal} {T : X → X}
--   (h : CM_Contraction (X:=X) κ T) (x0 : X) (n : ℕ) :
--   dist ((Nat.iterate T n) x0) (h.fst.fixedPoint) ≤
--     (Real.ofNNReal (κ.toNNReal))^n / (1 - Real.ofNNReal (κ.toNNReal)) *
--       dist (T x0) x0 := by
--   rcases h with ⟨hCT, hκ⟩
--   -- ✳︎ mathlib lemma (name may differ slightly by snapshot):
--   -- `ContractingWith.dist_iterate_fixedPoint_le_geometric : ...`
--   -- Replace the next line with that lemma in your version if the name differs.
--   exact hCT.dist_iterate_fixedPoint_le_geometric x0 n hκ

-- /-- Convenience corollary: `(iterate T n) x0 → fixedPoint`. -/
-- theorem CM_tendsto
--   {X : Type*} [MetricSpace X] [CompleteSpace X]
--   {κ : ℝ≥0∞} {T : X → X}
--   (h : CM_Contraction (X:=X) κ T) (x0 : X) :
--   Tendsto (fun n ↦ (Nat.iterate T n) x0) atTop (𝓝 h.fst.fixedPoint) := by
--   rcases h with ⟨hCT, hκ⟩
--   -- mathlib: `ContractingWith.tendsto_iterate_fixedPoint : ...`
--   simpa using hCT.tendsto_iterate_fixedPoint x0 hκ

end RP



-- namespace RP
-- /-- Metric space (placeholder). -/
-- def MetricSpace : Prop := True

-- /-- Complete metric space (placeholder). -/
-- def Complete : Prop := True

-- /-- Lipschitz map (placeholder). -/
-- def Lipschitz : Prop := True

-- /-- Contraction map (placeholder). -/
-- def Contraction : Prop := True

-- /-- Picard iterates (placeholder). -/
-- def PicardIterates : Prop := True

-- /-- Geometric series bound (placeholder). -/
-- theorem GeometricSeriesBound : True := True.intro

-- /-- Picard iterates are Cauchy (placeholder). -/
-- theorem PicardIsCauchy : True := True.intro

-- /-- Uniqueness of fixed points for contractions (placeholder). -/
-- theorem FixedPointUnique : True := True.intro

-- /-- Contraction Mapping Theorem (placeholder). -/
-- theorem ContractionMapping : True := True.intro
-- end RP
