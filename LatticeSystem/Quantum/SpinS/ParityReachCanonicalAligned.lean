import LatticeSystem.Quantum.SpinS.ParityReachCanonicalSingleIonBoth

/-!
# Aligned canonical-to-canonical reachability (per-endpoint parity-matched)

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

This file establishes the *aligned* case of canonical-to-canonical reachability: given an
adjacent canonical bond `(a₀, b₀)` and target endpoint values `(m_A', m_B')` with `m_A'` and
`(σ a₀).val` of the same parity (and likewise for `b₀`), the config that updates `σ` at the two
endpoints to `(m_A', m_B')` is `ParityReachableS`-reachable.  This is a thin dispatcher around
the four both-endpoint single-ion iter compositions from #3812: depending on the sign of each
endpoint shift (raise / lower), one of the four `parityReachableS_canonical_singleIon_*_iter`
variants applies directly.

The non-aligned case (`m_A'` flipped parity from `(σ a₀).val`) is handled in a follow-up PR by
prepending a single bond-parity or transverse move (#3813 / #3801) to convert to the aligned
case proved here.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [Fintype V] in
/-- **Aligned both-raise sub-case**: `(σ a₀).val ≤ m_A'`, `(σ b₀).val ≤ m_B'`, with both
endpoint shifts even. -/
theorem parityReachableS_canonical_to_canonical_aligned_both_raise
    (G : SimpleGraph V) {a₀ b₀ : V} (hab : a₀ ≠ b₀)
    {σ : V → Fin (N + 1)} {m_A' m_B' : ℕ}
    (hmA' : m_A' ≤ N) (hmB' : m_B' ≤ N)
    (h_a_le : (σ a₀).val ≤ m_A') (h_b_le : (σ b₀).val ≤ m_B')
    (h_a_par : (m_A' + (σ a₀).val) % 2 = 0)
    (h_b_par : (m_B' + (σ b₀).val) % 2 = 0) :
    ParityReachableS G σ
      (configUpdateTwo σ a₀ b₀ ⟨m_A', by omega⟩ ⟨m_B', by omega⟩) := by
  set k_a := (m_A' - (σ a₀).val) / 2 with hka_def
  set k_b := (m_B' - (σ b₀).val) / 2 with hkb_def
  have hka_val : (σ a₀).val + 2 * k_a = m_A' := by rw [hka_def]; omega
  have hkb_val : (σ b₀).val + 2 * k_b = m_B' := by rw [hkb_def]; omega
  have hka : (σ a₀).val + 2 * k_a ≤ N := by rw [hka_val]; exact hmA'
  have hkb : (σ b₀).val + 2 * k_b ≤ N := by rw [hkb_val]; exact hmB'
  have h := parityReachableS_canonical_singleIon_both_raise_iter G hab k_a k_b hka hkb
  convert h using 2
  · exact Fin.ext hka_val.symm
  · exact Fin.ext hkb_val.symm

omit [Fintype V] in
/-- **Aligned both-lower sub-case**: `m_A' ≤ (σ a₀).val`, `m_B' ≤ (σ b₀).val`. -/
theorem parityReachableS_canonical_to_canonical_aligned_both_lower
    (G : SimpleGraph V) {a₀ b₀ : V} (hab : a₀ ≠ b₀)
    {σ : V → Fin (N + 1)} {m_A' m_B' : ℕ}
    (hmA' : m_A' ≤ N) (hmB' : m_B' ≤ N)
    (h_a_ge : m_A' ≤ (σ a₀).val) (h_b_ge : m_B' ≤ (σ b₀).val)
    (h_a_par : (m_A' + (σ a₀).val) % 2 = 0)
    (h_b_par : (m_B' + (σ b₀).val) % 2 = 0) :
    ParityReachableS G σ
      (configUpdateTwo σ a₀ b₀ ⟨m_A', by omega⟩ ⟨m_B', by omega⟩) := by
  set k_a := ((σ a₀).val - m_A') / 2 with hka_def
  set k_b := ((σ b₀).val - m_B') / 2 with hkb_def
  have hka_val : (σ a₀).val - 2 * k_a = m_A' := by rw [hka_def]; omega
  have hkb_val : (σ b₀).val - 2 * k_b = m_B' := by rw [hkb_def]; omega
  have hka : 2 * k_a ≤ (σ a₀).val := by rw [hka_def]; omega
  have hkb : 2 * k_b ≤ (σ b₀).val := by rw [hkb_def]; omega
  have h := parityReachableS_canonical_singleIon_both_lower_iter G hab k_a k_b hka hkb
  convert h using 2
  · exact Fin.ext hka_val.symm
  · exact Fin.ext hkb_val.symm

omit [Fintype V] in
/-- **Aligned raise-`a` lower-`b` sub-case**: `(σ a₀).val ≤ m_A'`, `m_B' ≤ (σ b₀).val`. -/
theorem parityReachableS_canonical_to_canonical_aligned_raise_a_lower_b
    (G : SimpleGraph V) {a₀ b₀ : V} (hab : a₀ ≠ b₀)
    {σ : V → Fin (N + 1)} {m_A' m_B' : ℕ}
    (hmA' : m_A' ≤ N) (hmB' : m_B' ≤ N)
    (h_a_le : (σ a₀).val ≤ m_A') (h_b_ge : m_B' ≤ (σ b₀).val)
    (h_a_par : (m_A' + (σ a₀).val) % 2 = 0)
    (h_b_par : (m_B' + (σ b₀).val) % 2 = 0) :
    ParityReachableS G σ
      (configUpdateTwo σ a₀ b₀ ⟨m_A', by omega⟩ ⟨m_B', by omega⟩) := by
  set k_a := (m_A' - (σ a₀).val) / 2 with hka_def
  set k_b := ((σ b₀).val - m_B') / 2 with hkb_def
  have hka_val : (σ a₀).val + 2 * k_a = m_A' := by rw [hka_def]; omega
  have hkb_val : (σ b₀).val - 2 * k_b = m_B' := by rw [hkb_def]; omega
  have hka : (σ a₀).val + 2 * k_a ≤ N := by rw [hka_val]; exact hmA'
  have hkb : 2 * k_b ≤ (σ b₀).val := by rw [hkb_def]; omega
  have h := parityReachableS_canonical_singleIon_raise_a_lower_b_iter G hab k_a k_b hka hkb
  convert h using 2
  · exact Fin.ext hka_val.symm
  · exact Fin.ext hkb_val.symm

omit [Fintype V] in
/-- **Aligned lower-`a` raise-`b` sub-case**: `m_A' ≤ (σ a₀).val`, `(σ b₀).val ≤ m_B'`. -/
theorem parityReachableS_canonical_to_canonical_aligned_lower_a_raise_b
    (G : SimpleGraph V) {a₀ b₀ : V} (hab : a₀ ≠ b₀)
    {σ : V → Fin (N + 1)} {m_A' m_B' : ℕ}
    (hmA' : m_A' ≤ N) (hmB' : m_B' ≤ N)
    (h_a_ge : m_A' ≤ (σ a₀).val) (h_b_le : (σ b₀).val ≤ m_B')
    (h_a_par : (m_A' + (σ a₀).val) % 2 = 0)
    (h_b_par : (m_B' + (σ b₀).val) % 2 = 0) :
    ParityReachableS G σ
      (configUpdateTwo σ a₀ b₀ ⟨m_A', by omega⟩ ⟨m_B', by omega⟩) := by
  set k_a := ((σ a₀).val - m_A') / 2 with hka_def
  set k_b := (m_B' - (σ b₀).val) / 2 with hkb_def
  have hka_val : (σ a₀).val - 2 * k_a = m_A' := by rw [hka_def]; omega
  have hkb_val : (σ b₀).val + 2 * k_b = m_B' := by rw [hkb_def]; omega
  have hka : 2 * k_a ≤ (σ a₀).val := by rw [hka_def]; omega
  have hkb : (σ b₀).val + 2 * k_b ≤ N := by rw [hkb_val]; exact hmB'
  have h := parityReachableS_canonical_singleIon_lower_a_raise_b_iter G hab k_a k_b hka hkb
  convert h using 2
  · exact Fin.ext hka_val.symm
  · exact Fin.ext hkb_val.symm

omit [Fintype V] in
/-- **Aligned canonical-to-canonical dispatcher**: given the per-endpoint parity alignment
hypotheses, dispatches to the appropriate sign sub-case (both-raise / both-lower / mixed). -/
theorem parityReachableS_canonical_to_canonical_aligned
    (G : SimpleGraph V) {a₀ b₀ : V} (hab : a₀ ≠ b₀)
    {σ : V → Fin (N + 1)} {m_A' m_B' : ℕ}
    (hmA' : m_A' ≤ N) (hmB' : m_B' ≤ N)
    (h_a_par : (m_A' + (σ a₀).val) % 2 = 0)
    (h_b_par : (m_B' + (σ b₀).val) % 2 = 0) :
    ParityReachableS G σ
      (configUpdateTwo σ a₀ b₀ ⟨m_A', by omega⟩ ⟨m_B', by omega⟩) := by
  by_cases h_a_le : (σ a₀).val ≤ m_A'
  · by_cases h_b_le : (σ b₀).val ≤ m_B'
    · exact parityReachableS_canonical_to_canonical_aligned_both_raise G hab hmA' hmB'
        h_a_le h_b_le h_a_par h_b_par
    · exact parityReachableS_canonical_to_canonical_aligned_raise_a_lower_b G hab hmA' hmB'
        h_a_le (Nat.le_of_lt (Nat.lt_of_not_le h_b_le)) h_a_par h_b_par
  · by_cases h_b_le : (σ b₀).val ≤ m_B'
    · exact parityReachableS_canonical_to_canonical_aligned_lower_a_raise_b G hab hmA' hmB'
        (Nat.le_of_lt (Nat.lt_of_not_le h_a_le)) h_b_le h_a_par h_b_par
    · exact parityReachableS_canonical_to_canonical_aligned_both_lower G hab hmA' hmB'
        (Nat.le_of_lt (Nat.lt_of_not_le h_a_le))
        (Nat.le_of_lt (Nat.lt_of_not_le h_b_le)) h_a_par h_b_par

end LatticeSystem.Quantum
