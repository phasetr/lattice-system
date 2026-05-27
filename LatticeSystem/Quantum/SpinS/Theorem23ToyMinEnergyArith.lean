import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# Arithmetic core of the toy-Hamiltonian minimum-energy bound

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3).

This file isolates the purely real-arithmetic step of the toy minimum-energy bound
(option (a); see `.self-local/tex/3716-tasaki-2-5-toy-min-energy-bound.tex`).

On the joint sublattice-Casimir eigenspace `W_{a,b}` (sublattice spins `a ≤ s_A`,
`b ≤ s_B` with `s_B ≤ s_A`) the toy Hamiltonian
`Ĥ_toy = (Ŝ_tot)² − (Ŝ_A)² − (Ŝ_¬A)²` is bounded below by
`f(a,b) := |a−b|(|a−b|+1) − a(a+1) − b(b+1)` once the coupled total-spin lower bound
`(Ŝ_tot)² ≥ |a−b|(|a−b|+1)` is supplied (the Clebsch–Gordan triangle inequality).
This file proves the remaining arithmetic fact `f(a,b) ≥ f(s_A, s_B)`, i.e.\ the
minimum of `f` over the box `0 ≤ a ≤ s_A`, `0 ≤ b ≤ s_B ≤ s_A` is attained at the
corner `(s_A, s_B)` — the predicted minimum energy `f(s_A, s_B) = E`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

/-- **Arithmetic core of the toy minimum-energy bound**: for real spin values
`0 ≤ a ≤ s_A`, `0 ≤ b ≤ s_B ≤ s_A`, the quantity
`f(a,b) = |a−b|(|a−b|+1) − a(a+1) − b(b+1)` is minimised at the corner `(s_A, s_B)`:
`f(s_A, s_B) ≤ f(a, b)`.

Since `f(a, b) = −2·min(a,b)·(max(a,b)+1)` (whichever of `a, b` is smaller times the
other plus one), the value is most negative when both factors are largest, i.e.\ at
`a = s_A`, `b = s_B`. -/
theorem tasaki23_toy_min_energy_arith (a b sA sB : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haA : a ≤ sA) (hbB : b ≤ sB) (hBA : sB ≤ sA) :
    (sA - sB) * ((sA - sB) + 1) - sA * (sA + 1) - sB * (sB + 1) ≤
      |a - b| * (|a - b| + 1) - a * (a + 1) - b * (b + 1) := by
  rcases le_total b a with hba | hab
  · -- a ≥ b: |a − b| = a − b, f(a,b) = −2 b (a + 1).
    rw [abs_of_nonneg (by linarith)]
    nlinarith [mul_le_mul hbB (by linarith : a + 1 ≤ sA + 1) (by linarith) (by linarith : (0:ℝ) ≤ sB)]
  · -- a < b: |a − b| = b − a, f(a,b) = −2 a (b + 1).
    rw [abs_of_nonpos (by linarith)]
    have hasB : a ≤ sB := le_trans hab hbB
    nlinarith [mul_le_mul hasB (by linarith : b + 1 ≤ sA + 1) (by linarith) (by linarith : (0:ℝ) ≤ sB)]

end LatticeSystem.Quantum
