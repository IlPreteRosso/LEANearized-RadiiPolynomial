/-
Minimal test to trace vec_simp! behavior
-/
import LeanCert

set_option trace.VecSimp.debug true

-- Simple test that should definitely trigger the simproc
example : (Matrix.vecCons (1 : ℕ) (fun i => Matrix.vecCons 2 (fun _ => 3) i) : Fin 3 → ℕ) 2 = 3 := by
  vec_simp!

-- Test without type annotation (the failing case)
example : (Matrix.vecCons (1 : ℕ) (fun i => Matrix.vecCons 2 (fun _ => (3 : ℕ)) i)) 2 = 3 := by
  simp only [VecSimp.vecConsFinMk]
