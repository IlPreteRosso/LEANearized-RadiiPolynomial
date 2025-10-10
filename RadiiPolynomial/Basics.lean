import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Algebra.Module.LinearMap.Defs


open scoped Topology BigOperators
open Metric Set Filter ContinuousLinearMap



/-
NormedAddCommGroup: A *normed* group is an additive group endowed with a norm for which `dist x y = ‖x - y‖` defines a *metric space structure*.

NormedSpace ℝ E: A normed space over the reals is a *vector space over the real numbers* equipped with a norm that satisfies the properties of a norm (non-negativity, definiteness, homogeneity, and triangle inequality).

CompleteSpace E: A *complete* space is a metric space in which every Cauchy sequence converges to a limit within the space.

⇒ E is a Banach space over ℝ.
-/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
