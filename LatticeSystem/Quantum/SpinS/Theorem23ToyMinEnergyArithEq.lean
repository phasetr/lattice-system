import LatticeSystem.Quantum.SpinS.Theorem23ToyMinEnergyArith

/-!
# Strict (equality) form of the arithmetic core

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), option (a) —
the equality case of `tasaki23_toy_min_energy_arith` (see
`.self-local/tex/3716-tasaki-2-5-toy-min-energy-bound.tex`).

When the toy energy attains its minimum, the arithmetic inequality
`f(s_A,s_B) ≤ f(a,b)` is an equality, and (for a non-degenerate `s_B > 0`) the
minimiser is the corner `(a,b) = (s_A,s_B)`.  This pins the toy ground state to the
maximal sublattice spins, hence to the predicted total Casimir.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

/-- **Strict arithmetic core**: if `f(a,b) = f(s_A,s_B)` on the box
`0 ≤ a ≤ s_A`, `0 ≤ b ≤ s_B ≤ s_A` with `s_B > 0`, then `(a,b) = (s_A,s_B)`. -/
theorem tasaki23_toy_min_energy_arith_eq (a b sA sB : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haA : a ≤ sA) (hbB : b ≤ sB) (hsB : 0 < sB)
    (heq : |a - b| * (|a - b| + 1) - a * (a + 1) - b * (b + 1) =
      (sA - sB) * ((sA - sB) + 1) - sA * (sA + 1) - sB * (sB + 1)) :
    a = sA ∧ b = sB := by
  rcases le_total b a with hba | hab
  · -- a ≥ b: f(a,b) = −2 b (a+1) = −2 s_B (s_A+1).
    rw [abs_of_nonneg (by linarith)] at heq
    -- b (a+1) = s_B (s_A+1); with b ≤ s_B, a+1 ≤ s_A+1, conclude b = s_B and a = s_A.
    have hbeq : b = sB := by nlinarith [heq, haA, hbB, hsB, ha, hb]
    refine ⟨?_, hbeq⟩
    nlinarith [heq, hbeq, hsB]
  · -- a < b ≤ s_B ≤ s_A: f = −2 a (b+1); equality with the corner forces a = s_B, but
    -- a < b ≤ s_B contradicts a = s_B (when s_B > 0). So this case collapses to a = b.
    rw [abs_of_nonpos (by linarith)] at heq
    have hasB : a ≤ sB := le_trans hab hbB
    -- a (b+1) = s_B (s_A+1) with a ≤ s_B, b+1 ≤ s_A+1 ⟹ a = s_B ∧ b = s_A; but a ≤ b ≤ s_B = a
    -- forces a = b = s_B, then a = s_A from b = s_A.
    have haeq : a = sB := by nlinarith [heq, hasB, hbB, hsB, ha, hb]
    have hbeq : b = sB := le_antisymm hbB (by linarith [hab, haeq])
    exact ⟨by nlinarith [heq, haeq, hbeq, hsB], hbeq⟩

end LatticeSystem.Quantum
