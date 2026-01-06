/-
# MWE: `rw [hsigma.tsum_sigma' h1]` causes heartbeat timeout

When using `Summable.tsum_sigma'` inside `rw`, Lean times out.
Workaround: compute result via `have` first, then use `▸` substitution.
-/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpSpace

open scoped ENNReal

variable {M : Type*} {R : Type*}

set_option maxHeartbeats 10000

/-- Multiplication map for fiber partition. -/
def mulMap [Mul M] : M × M → M := Function.uncurry (· * ·)

/-- Fiber over x under multiplication. -/
def mulFiber [Mul M] (x : M) : Set (M × M) := mulMap ⁻¹' {x}

example [Monoid M] [NormedRing R] (f g : lp (fun _ : M => R) 1)
    (hprod : Summable fun ab : M × M => ‖f ab.1‖ * ‖g ab.2‖)
    (hsigma : Summable fun p : Σ x, mulFiber x => ‖f p.2.1.1‖ * ‖g p.2.1.2‖)
    (h1 : ∀ m, Summable fun ab : mulFiber m => ‖(f : M → R) ab.1.1‖ * ‖g ab.1.2‖) :
    ∑' (p : Σ x, mulFiber x), ‖f p.2.1.1‖ * ‖g p.2.1.2‖ =
    ∑' x, ∑' ab : mulFiber x, ‖f ab.1.1‖ * ‖g ab.1.2‖ := by
  -- This works: compute result first
  have h2 : ∑' (p : Σ x, mulFiber x), ‖f p.2.1.1‖ * ‖g p.2.1.2‖ =
      ∑' x, ∑' ab : mulFiber x, ‖f ab.1.1‖ * ‖g ab.1.2‖ := hsigma.tsum_sigma' h1
  exact h2

set_option profiler.threshold 1 in  -- show anything taking >1ms
set_option trace.profiler true in
example [Monoid M] [NormedRing R] (f g : lp (fun _ : M => R) 1)
    (hprod : Summable fun ab : M × M => ‖f ab.1‖ * ‖g ab.2‖)
    (hsigma : Summable fun p : Σ x, mulFiber x => ‖f p.2.1.1‖ * ‖g p.2.1.2‖)
    (h1 : ∀ m, Summable fun ab : mulFiber m => ‖(f : M → R) ab.1.1‖ * ‖g ab.1.2‖) :
    ∑' x, ∑' ab : mulFiber x, ‖f ab.1.1‖ * ‖g ab.1.2‖ =
    ∑' (p : Σ x, mulFiber x), ‖f p.2.1.1‖ * ‖g p.2.1.2‖ := by
  -- TIMEOUT: using rw directly causes heartbeat exceeded
  rw [hsigma.tsum_sigma' h1]
  -- (deterministic) timeout at `whnf`, maximum number of heartbeats (10000) has been reached

set_option maxHeartbeats 200000
example [Monoid M] [NormedRing R] (f g : lp (fun _ : M => R) 1)
    (hprod : Summable fun ab : M × M => ‖f ab.1‖ * ‖g ab.2‖)
    (hsigma : Summable fun p : Σ x, mulFiber x => ‖f p.2.1.1‖ * ‖g p.2.1.2‖)
    (h1 : ∀ m, Summable fun ab : mulFiber m => ‖(f : M → R) ab.1.1‖ * ‖g ab.1.2‖) :
    ∑' x, ∑' ab : mulFiber x, ‖f ab.1.1‖ * ‖g ab.1.2‖ =
    ∑' (p : Σ x, mulFiber x), ‖f p.2.1.1‖ * ‖g p.2.1.2‖ := by
  rw [hsigma.tsum_sigma' h1]
  -- Now this works with increased heartbeat limit

/-
###### Question ######

Why does `rw [hsigma.tsum_sigma' h1]` timeout, while computing `have h2 := hsigma.tsum_sigma' h1`
and then using `exact h2` (or `▸` substitution) works fine?

Is this a known issue with `rw` and dependent types / sigma types?

## Workaround

Instead of:
rw [hsigma.tsum_sigma' h1]

Use:
have h2 := hsigma.tsum_sigma' h1
exact h2.symm  -- or use ▸ for substitution
-/
