import LatticeSystem.Quantum.SpinS.ParityReachCanonicalTransfer

/-!
# Canonical magSum change via single-ion ±2 step

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

For the canonical bond endpoints `(a₀, b₀)`, a single-ion `±2`-move at either endpoint changes
the total magnetization by `±2` (preserving parity).  These wrappers package the
`SingleIonStepS` witnesses (#3798) as `ParityReachableS` steps to be used in the canonical
chain of (d) reachability totality.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [Fintype V] in
/-- **Canonical `+2` magSum shift via single-ion raise at `a₀`**. -/
theorem parityReachableS_canonical_singleIonRaise_a
    (G : SimpleGraph V) {a₀ : V} {σ : V → Fin (N + 1)}
    (hka : (σ a₀).val + 2 ≤ N) :
    ParityReachableS G σ (configUpdateOne σ a₀ ⟨(σ a₀).val + 2, by omega⟩) :=
  ParityReachableS.of_singleIon (singleIonStepS_raise a₀ hka)

omit [Fintype V] in
/-- **Canonical `−2` magSum shift via single-ion lower at `a₀`**. -/
theorem parityReachableS_canonical_singleIonLower_a
    (G : SimpleGraph V) {a₀ : V} {σ : V → Fin (N + 1)}
    (hka : 2 ≤ (σ a₀).val) :
    ParityReachableS G σ
      (configUpdateOne σ a₀ ⟨(σ a₀).val - 2, by have := (σ a₀).isLt; omega⟩) :=
  ParityReachableS.of_singleIon (singleIonStepS_lower a₀ hka)

omit [Fintype V] in
/-- **Canonical `+2` magSum shift via single-ion raise at `b₀`**. -/
theorem parityReachableS_canonical_singleIonRaise_b
    (G : SimpleGraph V) {b₀ : V} {σ : V → Fin (N + 1)}
    (hkb : (σ b₀).val + 2 ≤ N) :
    ParityReachableS G σ (configUpdateOne σ b₀ ⟨(σ b₀).val + 2, by omega⟩) :=
  ParityReachableS.of_singleIon (singleIonStepS_raise b₀ hkb)

omit [Fintype V] in
/-- **Canonical `−2` magSum shift via single-ion lower at `b₀`**. -/
theorem parityReachableS_canonical_singleIonLower_b
    (G : SimpleGraph V) {b₀ : V} {σ : V → Fin (N + 1)}
    (hkb : 2 ≤ (σ b₀).val) :
    ParityReachableS G σ
      (configUpdateOne σ b₀ ⟨(σ b₀).val - 2, by have := (σ b₀).isLt; omega⟩) :=
  ParityReachableS.of_singleIon (singleIonStepS_lower b₀ hkb)

end LatticeSystem.Quantum
