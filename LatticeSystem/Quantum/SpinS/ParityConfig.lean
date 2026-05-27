import LatticeSystem.Quantum.SpinS.Magnetization

/-!
# Magnetization-parity configuration subtypes

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The configuration space splits by the magnetization parity `magSumS σ % 2 ∈ {0, 1}`.  This file
sets up the subtype `parityConfigS Λ N p = {σ // magSumS σ % 2 = p}` (with `Fintype` /
`DecidableEq`), paralleling `magConfigS`, as the index type on which the Marshall-dressed `Ĥ'`
restricts to a parity block (the Perron–Frobenius blocks of Theorem 2.4, PR5).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The subtype of configurations whose magnetization sum has parity `p`. -/
def parityConfigS (Λ : Type*) [Fintype Λ] (N : ℕ) (p : ℕ) :=
  { σ : Λ → Fin (N + 1) // magSumS σ % 2 = p }

omit [DecidableEq Λ] in
/-- A `parityConfigS` element has the tagged magnetization parity. -/
theorem parityConfigS_magSumS_parity {p : ℕ} (σ : parityConfigS Λ N p) :
    magSumS σ.1 % 2 = p := σ.2

instance parityConfigS_instDecidableEq {p : ℕ} :
    DecidableEq (parityConfigS Λ N p) := fun _ _ => Subtype.instDecidableEq _ _

instance parityConfigS_instFintype {p : ℕ} : Fintype (parityConfigS Λ N p) := by
  unfold parityConfigS
  classical
  apply Subtype.fintype

omit [DecidableEq Λ] in
/-- The magnetization parity of a configuration is `0` or `1`. -/
theorem magSumS_parity_lt_two (σ : Λ → Fin (N + 1)) : magSumS σ % 2 < 2 :=
  Nat.mod_lt _ (by norm_num)

end LatticeSystem.Quantum
