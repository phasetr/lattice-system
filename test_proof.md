# Proof Plan for spinHalfRot3_eq_exp

## Goal
Prove: `spinHalfRot3 θ = exp ℂ ((-Complex.I * (θ : ℂ)) • spinHalfOp3)`

## Step-by-step approach:

### 1. Unfold definitions
- `spinHalfRot3 θ := rotOf spinHalfOp3 θ`
- `rotOf S θ := cos(θ/2) • 1 - (2*I*sin(θ/2)) • S`
- `spinHalfOp3 := (1/2 : ℂ) • pauliZ`
- `pauliZ := [[1, 0], [0, -1]]`

So: `spinHalfRot3 θ = cos(θ/2) • 1 - (2*I*sin(θ/2)) • ((1/2) • pauliZ)`
                    = `cos(θ/2) • 1 - (I*sin(θ/2)) • pauliZ`
                    = `cos(θ/2) • [[1, 0], [0, 1]] - (I*sin(θ/2)) • [[1, 0], [0, -1]]`
                    = `[[cos(θ/2) - I*sin(θ/2), 0], [0, cos(θ/2) + I*sin(θ/2)]]`

### 2. Compute RHS using Matrix.exp_diagonal
- RHS: `exp ((-I*θ) • spinHalfOp3)`
- `(-I*θ) • ((1/2) • pauliZ) = ((-I*θ)/2) • pauliZ`
- `= ((-I*θ)/2) • [[1, 0], [0, -1]]`
- `= [[-I*θ/2, 0], [0, I*θ/2]]`
- This is a diagonal matrix with entries `[-I*θ/2, I*θ/2]`

By `Matrix.exp_diagonal`:
- `exp (diagonal v) = diagonal (exp v)`
- `exp [[-I*θ/2, 0], [0, I*θ/2]] = [[exp(-I*θ/2), 0], [0, exp(I*θ/2)]]`

### 3. Apply Complex.exp_mul_I to each entry
- `exp(-I*θ/2) = exp((-θ/2) * I) = cos(-θ/2) + sin(-θ/2)*I`
- `= cos(θ/2) - sin(θ/2)*I`  (using cos(-x) = cos(x), sin(-x) = -sin(x))

- `exp(I*θ/2) = exp((θ/2) * I) = cos(θ/2) + sin(θ/2)*I`

So: `[[cos(θ/2) - sin(θ/2)*I, 0], [0, cos(θ/2) + sin(θ/2)*I]]`

### 4. Show LHS = RHS
Both sides equal `[[cos(θ/2) - I*sin(θ/2), 0], [0, cos(θ/2) + I*sin(θ/2)]]` ✓

## Required Mathlib lemmas:
1. `Matrix.exp_diagonal` - exponential of diagonal matrix
2. `Complex.exp_mul_I` - exp(x*I) = cos(x) + sin(x)*I
3. Properties of cos and sin for negative angles
4. Matrix operations and smul

## Potential proof structure:
```lean
theorem spinHalfRot3_eq_exp (θ : ℝ) :
    spinHalfRot3 θ = exp ℂ ((-Complex.I * (θ : ℂ)) • spinHalfOp3) := by
  unfold spinHalfRot3 rotOf spinHalfOp3
  simp [Matrix.diagonal_mul_diagonal, Matrix.exp_diagonal]
  -- Matrix operations and casting
  ext i j
  fin_cases i <;> fin_cases j
  -- For each matrix entry, apply exp_mul_I
  sorry
```
