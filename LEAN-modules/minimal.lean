import mathlib

open scoped Topology
open Metric Set Filter ContinuousLinearMap
open BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma tsum_apply_op {X : E →L[ℝ] E} {x : E} :
    (∑' n, X ^ (n + N)) x = ∑' n, (X ^ (n + N)) x := by
    -- Use the HasSum characterization directly
    sorry
