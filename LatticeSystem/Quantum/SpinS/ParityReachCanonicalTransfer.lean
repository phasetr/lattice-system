import LatticeSystem.Quantum.SpinS.ParityReachTransferIter

/-!
# Canonical-to-canonical reachability at the same total magnetization

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Starting from a two-site canonical config (mass concentrated at `(a₀, b₀)`), applying the iterated
transverse at the canonical bond `(a₀, b₀)` (#3801) shifts mass between `a₀` and `b₀`.  The
resulting config is again a two-site canonical, with different `(m_A, m_B)` splits but the same
total `m_A + m_B`.

Combined with the AB-concentration (#3806), this gives reachability between any two configs with
the same total magnetization (within the parity block).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [Fintype V] in
/-- **Canonical-to-canonical reachability at the same total magnetization**.  At the canonical
bond `(a₀, b₀)`, an iterated transverse transfers `n` units between `a₀` and `b₀`, preserving
the canonical shape (`= 0` elsewhere) and the total `m_A + m_B`. -/
theorem parityReachableS_canonical_transfer
    (A : V → Bool) {a₀ b₀ : V}
    (hadj : (bipartiteCompleteGraphOf A).Adj a₀ b₀)
    {σ : V → Fin (N + 1)} (n : ℕ)
    (hka₀ : n ≤ (σ a₀).val) (hkb₀ : (σ b₀).val + n ≤ N) :
    ParityReachableS (bipartiteCompleteGraphOf A) σ
      (configUpdateTwo σ a₀ b₀
        ⟨(σ a₀).val - n, by have := (σ a₀).isLt; omega⟩
        ⟨(σ b₀).val + n, by omega⟩) :=
  parityReachableS_transfer_n_units A hadj n hka₀ hkb₀

end LatticeSystem.Quantum
