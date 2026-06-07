import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHalfFillingKinetic

/-!
# Tasaki 11.5.3: at half-filling the t-J Hamiltonian reduces to its exchange part (Thm 11.26 PR2)

Building on the half-filling kinetic vanishing
(`tJ_kinetic_sandwich_mulVec_tJConfigOf_eq_zero_of_full`, #4315), on a fully occupied hard-core
sector state `|Φ_s⟩` the t-J Hamiltonian acts purely through its exchange (Heisenberg) term:

`Ĥ_tJ |Φ_s⟩ = J · (Σ_{⟨x,y⟩} (n̂_x n̂_y / 4 − Ŝ_x·Ŝ_y)) |Φ_s⟩`.

* `tJExchange` — the exchange operator `Σ_{x,y} [G.Adj] (n̂_x n̂_y/4 − Ŝ_x·Ŝ_y)` (the second
  summand of `tJHamiltonian`);
* `tJHamiltonian_mulVec_tJConfigOf_eq_of_full` — the reduction `Ĥ_tJ |Φ_s⟩ = J · tJExchange |Φ_s⟩`
  at half-filling.

This is the ferromagnetic Heisenberg model whose maximal-spin ground multiplet supplies the
`Ne = K+1` boundary case of Theorem 11.26.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, Theorem 11.26.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- **The t-J exchange (Heisenberg) operator** `Σ_{x,y} [G.Adj x y] (n̂_x n̂_y/4 − Ŝ_x·Ŝ_y)`, the
second summand of `tJHamiltonian` (the spin–spin interaction with its charge correction). -/
noncomputable def tJExchange (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj] :
    ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
    (if G.Adj x y then
        (1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y) - fermionSpinDot N x y
      else 0)

/-- **Half-filling reduction.**  On a fully occupied hard-core sector state `|Φ_s⟩`
(`∀ k, s k ≠ 0`), the t-J Hamiltonian acts through its exchange term:
`Ĥ_tJ |Φ_s⟩ = J · tJExchange |Φ_s⟩` (the kinetic term vanishes, #4315).  At half-filling `Ĥ_tJ` is
the ferromagnetic Heisenberg model. -/
theorem tJHamiltonian_mulVec_tJConfigOf_eq_of_full (N : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) (s : Fin (N + 1) → Fin 3) (hfull : ∀ k, s k ≠ 0) :
    (tJHamiltonian N G τ J).mulVec (basisVec (tJConfigOf N s)) =
      (J : ℂ) • (tJExchange N G).mulVec (basisVec (tJConfigOf N s)) := by
  unfold tJHamiltonian tJExchange
  rw [Matrix.add_mulVec, Matrix.smul_mulVec,
    tJ_kinetic_sandwich_mulVec_tJConfigOf_eq_zero_of_full N G s hfull, smul_zero, zero_add,
    Matrix.smul_mulVec]

end LatticeSystem.Fermion
