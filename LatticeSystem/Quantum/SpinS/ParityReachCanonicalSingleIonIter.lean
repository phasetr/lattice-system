import LatticeSystem.Quantum.SpinS.ParityReachCanonicalMagShift

/-!
# Iterated `±2k` single-ion magSum shifts at the canonical bond endpoints `a₀`, `b₀`

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Composing the canonical single-ion `±2` move (#3808) at the canonical bond endpoints by induction
on `k` shifts the corresponding site's magnetization by `±2k` while keeping all other sites fixed.
These four iterates (`raise_iter_a`, `lower_iter_a`, `raise_iter_b`, `lower_iter_b`) form the
magnitude-iterating layer of (d.1) reachability totality: they let the canonical chain change
`magSumS` by any `±2k` (parity preserved) at either bond endpoint, while leaving the rest of the
configuration intact.

This parallels the iterated transverse shuffle (#3800) and the iterated cross-sublattice transfer
(#3801).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [Fintype V] in
/-- **Iterated `+2k` single-ion raise at `a₀`**: composing the canonical `+2` raise (#3808) `k`
times.  From `σ` with `σ a₀ + 2k ≤ N`, the config obtained by setting `σ a₀ := σ a₀ + 2k` (with
all other sites unchanged) is `ParityReachableS`-reachable.

Proven by induction on `k` chaining `parityReachableS_canonical_singleIonRaise_a` (#3808). -/
theorem parityReachableS_canonical_singleIon_raise_iter_a
    (G : SimpleGraph V) {a₀ : V} {σ : V → Fin (N + 1)} (k : ℕ)
    (hka : (σ a₀).val + 2 * k ≤ N) :
    ParityReachableS G σ
      (configUpdateOne σ a₀ ⟨(σ a₀).val + 2 * k, by omega⟩) := by
  induction k generalizing σ with
  | zero =>
    have hself : configUpdateOne σ a₀ ⟨(σ a₀).val + 2 * 0, by omega⟩ = σ := by
      funext j
      unfold configUpdateOne
      by_cases hja : j = a₀
      · rw [hja, if_pos rfl]
        ext
        change (σ a₀).val + 2 * 0 = (σ a₀).val
        omega
      · rw [if_neg hja]
    rw [hself]
    exact ParityReachableS.refl _ _
  | succ m ih =>
    have hka_one : (σ a₀).val + 2 ≤ N := by omega
    have hstep1 := parityReachableS_canonical_singleIonRaise_a (a₀ := a₀) G hka_one
    set σ_one : V → Fin (N + 1) := configUpdateOne σ a₀ ⟨(σ a₀).val + 2, by omega⟩
      with hsig_one
    have hsig_one_a_val : (σ_one a₀).val = (σ a₀).val + 2 := by
      rw [hsig_one, configUpdateOne_at]
    have hsig_one_off : ∀ j, j ≠ a₀ → σ_one j = σ j := by
      intro j hja
      rw [hsig_one]; exact configUpdateOne_agree _ _ _ j hja
    have hka_ih : (σ_one a₀).val + 2 * m ≤ N := by rw [hsig_one_a_val]; omega
    have hreach_m := ih hka_ih
    have htarget_eq :
        configUpdateOne σ_one a₀ ⟨(σ_one a₀).val + 2 * m, by omega⟩ =
        configUpdateOne σ a₀ ⟨(σ a₀).val + 2 * (m + 1), by omega⟩ := by
      funext j
      unfold configUpdateOne
      by_cases hja : j = a₀
      · rw [hja, if_pos rfl, if_pos rfl]
        ext
        change (σ_one a₀).val + 2 * m = (σ a₀).val + 2 * (m + 1)
        rw [hsig_one_a_val]
        omega
      · rw [if_neg hja, if_neg hja]
        exact hsig_one_off j hja
    rw [← htarget_eq]
    exact ParityReachableS.trans hstep1 hreach_m

omit [Fintype V] in
/-- **Iterated `−2k` single-ion lower at `a₀`**: composing the canonical `−2` lower (#3808) `k`
times.  From `σ` with `2k ≤ σ a₀`, the config obtained by setting `σ a₀ := σ a₀ − 2k` (with all
other sites unchanged) is `ParityReachableS`-reachable. -/
theorem parityReachableS_canonical_singleIon_lower_iter_a
    (G : SimpleGraph V) {a₀ : V} {σ : V → Fin (N + 1)} (k : ℕ)
    (hka : 2 * k ≤ (σ a₀).val) :
    ParityReachableS G σ
      (configUpdateOne σ a₀
        ⟨(σ a₀).val - 2 * k, by have := (σ a₀).isLt; omega⟩) := by
  induction k generalizing σ with
  | zero =>
    have hself :
        configUpdateOne σ a₀ ⟨(σ a₀).val - 2 * 0, by have := (σ a₀).isLt; omega⟩ = σ := by
      funext j
      unfold configUpdateOne
      by_cases hja : j = a₀
      · rw [hja, if_pos rfl]
        ext
        change (σ a₀).val - 2 * 0 = (σ a₀).val
        omega
      · rw [if_neg hja]
    rw [hself]
    exact ParityReachableS.refl _ _
  | succ m ih =>
    have hka_one : 2 ≤ (σ a₀).val := by omega
    have hstep1 := parityReachableS_canonical_singleIonLower_a (a₀ := a₀) G hka_one
    set σ_one : V → Fin (N + 1) :=
      configUpdateOne σ a₀ ⟨(σ a₀).val - 2, by have := (σ a₀).isLt; omega⟩
      with hsig_one
    have hsig_one_a_val : (σ_one a₀).val = (σ a₀).val - 2 := by
      rw [hsig_one, configUpdateOne_at]
    have hsig_one_off : ∀ j, j ≠ a₀ → σ_one j = σ j := by
      intro j hja
      rw [hsig_one]; exact configUpdateOne_agree _ _ _ j hja
    have hka_ih : 2 * m ≤ (σ_one a₀).val := by rw [hsig_one_a_val]; omega
    have hreach_m := ih hka_ih
    have htarget_eq :
        configUpdateOne σ_one a₀
          ⟨(σ_one a₀).val - 2 * m, by have := (σ_one a₀).isLt; omega⟩ =
        configUpdateOne σ a₀
          ⟨(σ a₀).val - 2 * (m + 1), by have := (σ a₀).isLt; omega⟩ := by
      funext j
      unfold configUpdateOne
      by_cases hja : j = a₀
      · rw [hja, if_pos rfl, if_pos rfl]
        ext
        change (σ_one a₀).val - 2 * m = (σ a₀).val - 2 * (m + 1)
        rw [hsig_one_a_val]
        omega
      · rw [if_neg hja, if_neg hja]
        exact hsig_one_off j hja
    rw [← htarget_eq]
    exact ParityReachableS.trans hstep1 hreach_m

omit [Fintype V] in
/-- **Iterated `+2k` single-ion raise at `b₀`**: composing the canonical `+2` raise (#3808) `k`
times.  From `σ` with `σ b₀ + 2k ≤ N`, the config obtained by setting `σ b₀ := σ b₀ + 2k` (with
all other sites unchanged) is `ParityReachableS`-reachable. -/
theorem parityReachableS_canonical_singleIon_raise_iter_b
    (G : SimpleGraph V) {b₀ : V} {σ : V → Fin (N + 1)} (k : ℕ)
    (hkb : (σ b₀).val + 2 * k ≤ N) :
    ParityReachableS G σ
      (configUpdateOne σ b₀ ⟨(σ b₀).val + 2 * k, by omega⟩) := by
  induction k generalizing σ with
  | zero =>
    have hself : configUpdateOne σ b₀ ⟨(σ b₀).val + 2 * 0, by omega⟩ = σ := by
      funext j
      unfold configUpdateOne
      by_cases hjb : j = b₀
      · rw [hjb, if_pos rfl]
        ext
        change (σ b₀).val + 2 * 0 = (σ b₀).val
        omega
      · rw [if_neg hjb]
    rw [hself]
    exact ParityReachableS.refl _ _
  | succ m ih =>
    have hkb_one : (σ b₀).val + 2 ≤ N := by omega
    have hstep1 := parityReachableS_canonical_singleIonRaise_b (b₀ := b₀) G hkb_one
    set σ_one : V → Fin (N + 1) := configUpdateOne σ b₀ ⟨(σ b₀).val + 2, by omega⟩
      with hsig_one
    have hsig_one_b_val : (σ_one b₀).val = (σ b₀).val + 2 := by
      rw [hsig_one, configUpdateOne_at]
    have hsig_one_off : ∀ j, j ≠ b₀ → σ_one j = σ j := by
      intro j hjb
      rw [hsig_one]; exact configUpdateOne_agree _ _ _ j hjb
    have hkb_ih : (σ_one b₀).val + 2 * m ≤ N := by rw [hsig_one_b_val]; omega
    have hreach_m := ih hkb_ih
    have htarget_eq :
        configUpdateOne σ_one b₀ ⟨(σ_one b₀).val + 2 * m, by omega⟩ =
        configUpdateOne σ b₀ ⟨(σ b₀).val + 2 * (m + 1), by omega⟩ := by
      funext j
      unfold configUpdateOne
      by_cases hjb : j = b₀
      · rw [hjb, if_pos rfl, if_pos rfl]
        ext
        change (σ_one b₀).val + 2 * m = (σ b₀).val + 2 * (m + 1)
        rw [hsig_one_b_val]
        omega
      · rw [if_neg hjb, if_neg hjb]
        exact hsig_one_off j hjb
    rw [← htarget_eq]
    exact ParityReachableS.trans hstep1 hreach_m

omit [Fintype V] in
/-- **Iterated `−2k` single-ion lower at `b₀`**: composing the canonical `−2` lower (#3808) `k`
times.  From `σ` with `2k ≤ σ b₀`, the config obtained by setting `σ b₀ := σ b₀ − 2k` (with all
other sites unchanged) is `ParityReachableS`-reachable. -/
theorem parityReachableS_canonical_singleIon_lower_iter_b
    (G : SimpleGraph V) {b₀ : V} {σ : V → Fin (N + 1)} (k : ℕ)
    (hkb : 2 * k ≤ (σ b₀).val) :
    ParityReachableS G σ
      (configUpdateOne σ b₀
        ⟨(σ b₀).val - 2 * k, by have := (σ b₀).isLt; omega⟩) := by
  induction k generalizing σ with
  | zero =>
    have hself :
        configUpdateOne σ b₀ ⟨(σ b₀).val - 2 * 0, by have := (σ b₀).isLt; omega⟩ = σ := by
      funext j
      unfold configUpdateOne
      by_cases hjb : j = b₀
      · rw [hjb, if_pos rfl]
        ext
        change (σ b₀).val - 2 * 0 = (σ b₀).val
        omega
      · rw [if_neg hjb]
    rw [hself]
    exact ParityReachableS.refl _ _
  | succ m ih =>
    have hkb_one : 2 ≤ (σ b₀).val := by omega
    have hstep1 := parityReachableS_canonical_singleIonLower_b (b₀ := b₀) G hkb_one
    set σ_one : V → Fin (N + 1) :=
      configUpdateOne σ b₀ ⟨(σ b₀).val - 2, by have := (σ b₀).isLt; omega⟩
      with hsig_one
    have hsig_one_b_val : (σ_one b₀).val = (σ b₀).val - 2 := by
      rw [hsig_one, configUpdateOne_at]
    have hsig_one_off : ∀ j, j ≠ b₀ → σ_one j = σ j := by
      intro j hjb
      rw [hsig_one]; exact configUpdateOne_agree _ _ _ j hjb
    have hkb_ih : 2 * m ≤ (σ_one b₀).val := by rw [hsig_one_b_val]; omega
    have hreach_m := ih hkb_ih
    have htarget_eq :
        configUpdateOne σ_one b₀
          ⟨(σ_one b₀).val - 2 * m, by have := (σ_one b₀).isLt; omega⟩ =
        configUpdateOne σ b₀
          ⟨(σ b₀).val - 2 * (m + 1), by have := (σ b₀).isLt; omega⟩ := by
      funext j
      unfold configUpdateOne
      by_cases hjb : j = b₀
      · rw [hjb, if_pos rfl, if_pos rfl]
        ext
        change (σ_one b₀).val - 2 * m = (σ b₀).val - 2 * (m + 1)
        rw [hsig_one_b_val]
        omega
      · rw [if_neg hjb, if_neg hjb]
        exact hsig_one_off j hjb
    rw [← htarget_eq]
    exact ParityReachableS.trans hstep1 hreach_m

end LatticeSystem.Quantum
