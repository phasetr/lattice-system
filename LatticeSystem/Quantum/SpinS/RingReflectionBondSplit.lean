/-
The ring Heisenberg Hamiltonian split into left, right, and crossing bonds
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 21).

The nearest-neighbor bonds `(x, x+1)` of the even ring `Fin (2n)` fall into four disjoint classes by
the value of `x`:

* **left bonds** `x ≤ n−2` (both endpoints in `{0,…,n−1}`),
* the **crossing bond** at `x = n−1` (the bond `(n−1, n)`),
* **right bonds** `n ≤ x ≤ 2n−2` (both endpoints in `{n,…,2n−1}`),
* the **crossing bond** at `x = 2n−1` (the bond `(2n−1, 0)`).

Summing the bond form `∑_x Ŝ_x · Ŝ_{x+1}` over this partition gives
`heisenbergHamiltonianS (ringCoupling (2n)) = H_L + H_R + (crossing bond at n−1) + (crossing bond at
2n−1)`, where `H_L = ringLeftHamiltonian` and `H_R = ringRightBondSum` are the left and right bond
Hamiltonians.  Identifying `H_R` with `θ(H_L)` and the crossing bonds with the gauged interaction is
the next step.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionLeftBondSum

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- The **right bond Hamiltonian** of the ring: the sum of the bonds `(x, x+1)` entirely inside the
right half `{n, …, 2n−1}`. -/
noncomputable def ringRightBondSum (n N : ℕ) : ManyBodyOpS (Fin (2 * n)) N :=
  ∑ x : Fin (2 * n),
    (if n ≤ (x : ℕ) ∧ (x : ℕ) + 1 < 2 * n then spinSDot x (ringBondSucc n x) N else 0)

/-- The per-bond four-way decomposition: each bond term equals the sum of its four indicator
contributions (left / crossing-`n−1` / right / crossing-`2n−1`; exactly one is nonzero). -/
theorem bondTerm_four_way (x : Fin (2 * n)) :
    spinSDot x (ringBondSucc n x) N
      = (if (x : ℕ) + 1 < n then spinSDot x (ringBondSucc n x) N else 0)
        + (if (x : ℕ) = n - 1 then spinSDot x (ringBondSucc n x) N else 0)
        + (if n ≤ (x : ℕ) ∧ (x : ℕ) + 1 < 2 * n then spinSDot x (ringBondSucc n x) N else 0)
        + (if (x : ℕ) = 2 * n - 1 then spinSDot x (ringBondSucc n x) N else 0) := by
  have hlt := x.isLt
  by_cases h1 : (x : ℕ) + 1 < n
  · rw [if_pos h1, if_neg (show ¬ (x : ℕ) = n - 1 by omega),
      if_neg (show ¬ (n ≤ (x : ℕ) ∧ (x : ℕ) + 1 < 2 * n) by omega),
      if_neg (show ¬ (x : ℕ) = 2 * n - 1 by omega)]
    simp
  · by_cases h2 : (x : ℕ) = n - 1
    · rw [if_neg h1, if_pos h2,
        if_neg (show ¬ (n ≤ (x : ℕ) ∧ (x : ℕ) + 1 < 2 * n) by omega),
        if_neg (show ¬ (x : ℕ) = 2 * n - 1 by omega)]
      simp
    · by_cases h4 : (x : ℕ) = 2 * n - 1
      · rw [if_neg h1, if_neg h2,
          if_neg (show ¬ (n ≤ (x : ℕ) ∧ (x : ℕ) + 1 < 2 * n) by omega), if_pos h4]
        simp
      · rw [if_neg h1, if_neg h2,
          if_pos (show n ≤ (x : ℕ) ∧ (x : ℕ) + 1 < 2 * n by omega), if_neg h4]
        simp

/-- A single-condition indicator sum `∑_x (if x.val = k then f x else 0)` picks out the unique site
with value `k`. -/
theorem sum_ite_val_eq {k : ℕ} (hk : k < 2 * n) (f : Fin (2 * n) → ManyBodyOpS (Fin (2 * n)) N) :
    (∑ x : Fin (2 * n), if (x : ℕ) = k then f x else 0) = f ⟨k, hk⟩ := by
  rw [Finset.sum_eq_single ⟨k, hk⟩]
  · rw [if_pos rfl]
  · intro y _ hy
    rw [if_neg (fun h => hy (Fin.ext h))]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The ring Heisenberg Hamiltonian split into left, right, and crossing bonds.** -/
theorem heisenbergHamiltonianS_ringCoupling_bond_split (n N : ℕ) [NeZero n] :
    heisenbergHamiltonianS (ringCoupling (2 * n)) N
      = ringLeftHamiltonian n N + ringRightBondSum n N
        + spinSDot (⟨n - 1, by have := Nat.pos_of_ne_zero (NeZero.ne n); omega⟩ : Fin (2 * n))
            (ringBondSucc n ⟨n - 1, by have := Nat.pos_of_ne_zero (NeZero.ne n); omega⟩) N
        + spinSDot (⟨2 * n - 1, by have := Nat.pos_of_ne_zero (NeZero.ne n); omega⟩ : Fin (2 * n))
            (ringBondSucc n ⟨2 * n - 1, by have := Nat.pos_of_ne_zero (NeZero.ne n); omega⟩) N := by
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [heisenbergHamiltonianS_ringCoupling_eq_bondSum]
  rw [Finset.sum_congr rfl (fun x _ => bondTerm_four_way x)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← ringLeftHamiltonian_eq_leftBondSum, ← ringRightBondSum,
    sum_ite_val_eq (by omega), sum_ite_val_eq (by omega)]
  abel

end LatticeSystem.Quantum
