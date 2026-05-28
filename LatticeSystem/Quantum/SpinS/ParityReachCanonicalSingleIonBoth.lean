import LatticeSystem.Quantum.SpinS.ParityReachCanonicalSingleIonIter

/-!
# Both-endpoint single-ion iter compositions at the canonical bond

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Composing two `ParityReachableS` single-ion iter moves at the canonical bond endpoints `(a₀, b₀)`
yields a single `ParityReachableS` step that shifts both site values independently by even
amounts.  Four sign combinations are exported (raise/lower at `a₀` × raise/lower at `b₀`):

* `parityReachableS_canonical_singleIon_both_raise_iter`
* `parityReachableS_canonical_singleIon_both_lower_iter`
* `parityReachableS_canonical_singleIon_raise_a_lower_b_iter`
* `parityReachableS_canonical_singleIon_lower_a_raise_b_iter`

Each is `ParityReachableS.trans` of the two per-endpoint iter theorems
`parityReachableS_canonical_singleIon_{raise,lower}_iter_{a,b}` (#3809 + #3811), followed by the
helper `configUpdateOne_configUpdateOne_eq_configUpdateTwo` to rewrite nested
`configUpdateOne ∘ configUpdateOne` as a single `configUpdateTwo`.

This is the (d.2.d) layer of (d) reachability totality (parity-aligned independent shifts at both
endpoints); the bridge to (d.2.e) (arbitrary same-parity-total canonical-to-canonical) combines
this with `parityReachableS_canonical_transfer` (#3807) for a one-step parity adjustment.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [Fintype V] in
/-- **Helper**: at distinct sites `a ≠ b`, two nested single-site updates equal one two-site
update.  The order `configUpdateOne (configUpdateOne σ a va) b vb` puts the `b`-update *outer*,
which matches `configUpdateTwo`'s `if k = a ... else if k = b ...` at distinct sites. -/
theorem configUpdateOne_configUpdateOne_eq_configUpdateTwo
    (σ : V → Fin (N + 1)) {a b : V} (hab : a ≠ b) (va vb : Fin (N + 1)) :
    configUpdateOne (configUpdateOne σ a va) b vb = configUpdateTwo σ a b va vb := by
  funext j
  by_cases hjb : j = b
  · subst hjb
    rw [configUpdateOne_at, configUpdateTwo_at_b _ hab]
  · rw [configUpdateOne_agree _ _ _ _ hjb]
    by_cases hja : j = a
    · subst hja
      rw [configUpdateOne_at, configUpdateTwo_at_a]
    · rw [configUpdateOne_agree _ _ _ _ hja,
          configUpdateTwo_agree _ _ _ _ _ _ hja hjb]

omit [Fintype V] in
/-- **Lift `raise iter` at `b₀` to start from a configUpdateOne at `a₀`**, ending at a
`configUpdateTwo`.  Used to assemble the four both-endpoint sign-combinations. -/
private theorem parityReachableS_singleIon_raise_iter_b_after_a
    (G : SimpleGraph V) {a₀ b₀ : V} (hab : a₀ ≠ b₀)
    {σ : V → Fin (N + 1)} (vA : Fin (N + 1)) (k_b : ℕ)
    (hkb : (σ b₀).val + 2 * k_b ≤ N) :
    ParityReachableS G (configUpdateOne σ a₀ vA)
      (configUpdateTwo σ a₀ b₀ vA ⟨(σ b₀).val + 2 * k_b, by omega⟩) := by
  have hb : ((configUpdateOne σ a₀ vA) b₀).val = (σ b₀).val := by
    congr 1; exact configUpdateOne_agree _ _ _ _ hab.symm
  have hkb' : ((configUpdateOne σ a₀ vA) b₀).val + 2 * k_b ≤ N := by rw [hb]; exact hkb
  have h := parityReachableS_canonical_singleIon_raise_iter_b (b₀ := b₀) G k_b hkb'
  have heq :
      configUpdateOne (configUpdateOne σ a₀ vA) b₀
          ⟨((configUpdateOne σ a₀ vA) b₀).val + 2 * k_b, by rw [hb]; omega⟩ =
        configUpdateTwo σ a₀ b₀ vA ⟨(σ b₀).val + 2 * k_b, by omega⟩ := by
    rw [configUpdateOne_configUpdateOne_eq_configUpdateTwo _ hab]
    congr 1
    ext
    change ((configUpdateOne σ a₀ vA) b₀).val + 2 * k_b = (σ b₀).val + 2 * k_b
    rw [hb]
  rw [← heq]
  exact h

omit [Fintype V] in
/-- **Lift `lower iter` at `b₀` to start from a configUpdateOne at `a₀`**, ending at a
`configUpdateTwo`. -/
private theorem parityReachableS_singleIon_lower_iter_b_after_a
    (G : SimpleGraph V) {a₀ b₀ : V} (hab : a₀ ≠ b₀)
    {σ : V → Fin (N + 1)} (vA : Fin (N + 1)) (k_b : ℕ)
    (hkb : 2 * k_b ≤ (σ b₀).val) :
    ParityReachableS G (configUpdateOne σ a₀ vA)
      (configUpdateTwo σ a₀ b₀ vA
        ⟨(σ b₀).val - 2 * k_b, by have := (σ b₀).isLt; omega⟩) := by
  have hb : ((configUpdateOne σ a₀ vA) b₀).val = (σ b₀).val := by
    congr 1; exact configUpdateOne_agree _ _ _ _ hab.symm
  have hkb' : 2 * k_b ≤ ((configUpdateOne σ a₀ vA) b₀).val := by rw [hb]; exact hkb
  have h := parityReachableS_canonical_singleIon_lower_iter_b (b₀ := b₀) G k_b hkb'
  have heq :
      configUpdateOne (configUpdateOne σ a₀ vA) b₀
          ⟨((configUpdateOne σ a₀ vA) b₀).val - 2 * k_b,
            by have := ((configUpdateOne σ a₀ vA) b₀).isLt; omega⟩ =
        configUpdateTwo σ a₀ b₀ vA
          ⟨(σ b₀).val - 2 * k_b, by have := (σ b₀).isLt; omega⟩ := by
    rw [configUpdateOne_configUpdateOne_eq_configUpdateTwo _ hab]
    congr 1
    ext
    change ((configUpdateOne σ a₀ vA) b₀).val - 2 * k_b = (σ b₀).val - 2 * k_b
    rw [hb]
  rw [← heq]
  exact h

omit [Fintype V] in
/-- **Both-endpoint raise iter**: shift `σ a₀` by `+2k_a` and `σ b₀` by `+2k_b`, simultaneously.
Chains `parityReachableS_canonical_singleIon_raise_iter_a` (#3809) and
`parityReachableS_canonical_singleIon_raise_iter_b` (#3811) via `ParityReachableS.trans`. -/
theorem parityReachableS_canonical_singleIon_both_raise_iter
    (G : SimpleGraph V) {a₀ b₀ : V} (hab : a₀ ≠ b₀)
    {σ : V → Fin (N + 1)} (k_a k_b : ℕ)
    (hka : (σ a₀).val + 2 * k_a ≤ N)
    (hkb : (σ b₀).val + 2 * k_b ≤ N) :
    ParityReachableS G σ
      (configUpdateTwo σ a₀ b₀
        ⟨(σ a₀).val + 2 * k_a, by omega⟩
        ⟨(σ b₀).val + 2 * k_b, by omega⟩) :=
  ParityReachableS.trans
    (parityReachableS_canonical_singleIon_raise_iter_a (a₀ := a₀) G k_a hka)
    (parityReachableS_singleIon_raise_iter_b_after_a G hab
      ⟨(σ a₀).val + 2 * k_a, by omega⟩ k_b hkb)

omit [Fintype V] in
/-- **Both-endpoint lower iter**: shift `σ a₀` by `−2k_a` and `σ b₀` by `−2k_b`, simultaneously. -/
theorem parityReachableS_canonical_singleIon_both_lower_iter
    (G : SimpleGraph V) {a₀ b₀ : V} (hab : a₀ ≠ b₀)
    {σ : V → Fin (N + 1)} (k_a k_b : ℕ)
    (hka : 2 * k_a ≤ (σ a₀).val)
    (hkb : 2 * k_b ≤ (σ b₀).val) :
    ParityReachableS G σ
      (configUpdateTwo σ a₀ b₀
        ⟨(σ a₀).val - 2 * k_a, by have := (σ a₀).isLt; omega⟩
        ⟨(σ b₀).val - 2 * k_b, by have := (σ b₀).isLt; omega⟩) :=
  ParityReachableS.trans
    (parityReachableS_canonical_singleIon_lower_iter_a (a₀ := a₀) G k_a hka)
    (parityReachableS_singleIon_lower_iter_b_after_a G hab
      ⟨(σ a₀).val - 2 * k_a, by have := (σ a₀).isLt; omega⟩ k_b hkb)

omit [Fintype V] in
/-- **Mixed iter (raise `a₀`, lower `b₀`)**. -/
theorem parityReachableS_canonical_singleIon_raise_a_lower_b_iter
    (G : SimpleGraph V) {a₀ b₀ : V} (hab : a₀ ≠ b₀)
    {σ : V → Fin (N + 1)} (k_a k_b : ℕ)
    (hka : (σ a₀).val + 2 * k_a ≤ N)
    (hkb : 2 * k_b ≤ (σ b₀).val) :
    ParityReachableS G σ
      (configUpdateTwo σ a₀ b₀
        ⟨(σ a₀).val + 2 * k_a, by omega⟩
        ⟨(σ b₀).val - 2 * k_b, by have := (σ b₀).isLt; omega⟩) :=
  ParityReachableS.trans
    (parityReachableS_canonical_singleIon_raise_iter_a (a₀ := a₀) G k_a hka)
    (parityReachableS_singleIon_lower_iter_b_after_a G hab
      ⟨(σ a₀).val + 2 * k_a, by omega⟩ k_b hkb)

omit [Fintype V] in
/-- **Mixed iter (lower `a₀`, raise `b₀`)**. -/
theorem parityReachableS_canonical_singleIon_lower_a_raise_b_iter
    (G : SimpleGraph V) {a₀ b₀ : V} (hab : a₀ ≠ b₀)
    {σ : V → Fin (N + 1)} (k_a k_b : ℕ)
    (hka : 2 * k_a ≤ (σ a₀).val)
    (hkb : (σ b₀).val + 2 * k_b ≤ N) :
    ParityReachableS G σ
      (configUpdateTwo σ a₀ b₀
        ⟨(σ a₀).val - 2 * k_a, by have := (σ a₀).isLt; omega⟩
        ⟨(σ b₀).val + 2 * k_b, by omega⟩) :=
  ParityReachableS.trans
    (parityReachableS_canonical_singleIon_lower_iter_a (a₀ := a₀) G k_a hka)
    (parityReachableS_singleIon_raise_iter_b_after_a G hab
      ⟨(σ a₀).val - 2 * k_a, by have := (σ a₀).isLt; omega⟩ k_b hkb)

end LatticeSystem.Quantum
