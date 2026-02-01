/-
Test file to debug colNorm_0_eq step by step
-/
import RadiiPolynomial.TaylorODE.lpWeighted
import LeanCert

open l1Weighted

-- Simplified test case
noncomputable def A_diag : ℝ := 8660/10000
noncomputable def A_sub1 : ℝ := -12990/10000
noncomputable def A_sub2 : ℝ := 29240/10000
noncomputable def ν_val : PosReal := ⟨1/4, by norm_num⟩

noncomputable def A_mat : Matrix (Fin 3) (Fin 3) ℝ :=
  !![A_diag, 0, 0;
     A_sub1, A_diag, 0;
     A_sub2, A_sub1, A_diag]

-- Step by step proof: trace after each step
example :
    l1Weighted.matrixColNorm ν_val A_mat 0 = |A_diag| + |A_sub1| * ν_val + |A_sub2| * ν_val^2 := by
  -- Step 1: Unfold definitions
  unfold l1Weighted.matrixColNorm A_mat A_diag A_sub1 A_sub2 ν_val
  -- Step 2: Simplify ν^0 = 1
  simp only [Fin.val_zero, pow_zero, div_one]
  -- Step 3: Expand the Fin 3 sum
  finsum_expand!
  -- Step 4: Matrix.of_apply needed to convert matrix notation
  simp only [Matrix.of_apply]
  -- Step 5: vec_simp!
  vec_simp!
  -- Now try ring
  ring

-- Test: matrix literal indexing should work with vec_simp!
example : !![1, 2, 3; 4, 5, 6; 7, 8, 9] 1 0 = (4 : ℕ) := by
  vec_simp!

-- Test: what about with Real?
example : !![1, 2, 3; 4, 5, 6; 7, 8, 9] 1 0 = (4 : ℝ) := by
  vec_simp!

-- Test: the EXACT failing expression from the goal
example : (Matrix.vecCons (433 / 500 : ℝ)
    (fun i => Matrix.vecCons (-(1299 / 1000) : ℝ) (fun i => (731 / 250 : ℝ)) i) : Fin 3 → ℝ) 2
    = 731 / 250 := by
  vec_simp!

-- Same but with explicit type annotation on the lambda
example : (Matrix.vecCons (433 / 500 : ℝ)
    (fun (i : Fin 2) => Matrix.vecCons (-(1299 / 1000) : ℝ) (fun (_ : Fin 1) => (731 / 250 : ℝ)) i) : Fin 3 → ℝ) 2
    = 731 / 250 := by
  vec_simp!

-- The issue: abs is wrapped around - can vec_simp! pierce through abs?
example : |(Matrix.vecCons (433 / 500 : ℝ)
    (fun i => Matrix.vecCons (-(1299 / 1000) : ℝ) (fun i => (731 / 250 : ℝ)) i) : Fin 3 → ℝ) 2|
    = 731 / 250 := by
  vec_simp!

-- Test the EXACT goal structure from the failure (with proper type annotations)
example : (4763 : ℝ) / 4000 +
      |(Matrix.vecCons (433 / 500 : ℝ)
        (fun (i : Fin 2) => Matrix.vecCons (-1299 / 1000 : ℝ) (fun (_ : Fin 1) => (731 / 250 : ℝ)) i) : Fin 3 → ℝ) 2| * (1 / 16) =
    2747 / 2000 := by
  vec_simp!
  ring

-- What if we apply simp with vecConsFinMk directly?
example : (4763 : ℝ) / 4000 +
      |(Matrix.vecCons (433 / 500 : ℝ)
        (fun (i : Fin 2) => Matrix.vecCons (-1299 / 1000 : ℝ) (fun (_ : Fin 1) => (731 / 250 : ℝ)) i) : Fin 3 → ℝ) 2| * (1 / 16) =
    2747 / 2000 := by
  simp only [VecSimp.vecConsFinMk]
  ring

-- Check: does the simproc work without the arithmetic context?
example : |(Matrix.vecCons (433 / 500 : ℝ)
        (fun (i : Fin 2) => Matrix.vecCons (-1299 / 1000 : ℝ) (fun (_ : Fin 1) => (731 / 250 : ℝ)) i) : Fin 3 → ℝ) 2| = 731/250 := by
  simp only [VecSimp.vecConsFinMk]
  norm_num

-- KEY QUESTION: In the real proof, how does the expression look?
-- Let me trace the actual structure after finsum_expand!
set_option trace.VecSimp.debug true in
example :
    l1Weighted.matrixColNorm ν_val A_mat 0 = |A_diag| + |A_sub1| * ν_val + |A_sub2| * ν_val^2 := by
  unfold l1Weighted.matrixColNorm A_mat A_diag A_sub1 A_sub2 ν_val
  simp only [Fin.val_zero, pow_zero, div_one]
  finsum_expand!
  simp only [Matrix.of_apply]
  vec_simp!
  ring
