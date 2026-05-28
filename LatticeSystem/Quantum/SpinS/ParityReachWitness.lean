import LatticeSystem.Quantum.SpinS.ParityReachable
import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraph

/-!
# Concrete witness constructors for `ParityReachableS` on the bipartite complete graph

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Foundational building blocks for (d) reachability totality.  These provide explicit
configurations `σ'` and short proofs that `ParityStepS (bipartiteCompleteGraphOf A) σ σ'` holds:

* **`raiseLowerStepS_pair_shift`**: from `σ` with `σ a ≥ 1`, `σ b ≤ N − 1`, `a ≠ b`,
  `A a ≠ A b`, the move that *lowers* `a` and *raises* `b` by `1` each is a `RaiseLowerStepS`.
* **`parityBondStepS_pair_raise`** / **`parityBondStepS_pair_lower`**: pair-parity raise / lower
  moves at `(a, b)` are `ParityBondStepS`.
* **`singleIonStepS_raise`** / **`singleIonStepS_lower`**: same-site `±2` moves are
  `SingleIonStepS`.

These wrap raw move constructions into reusable witnesses for building reachability chains.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [Fintype V] in
/-- The config obtained from `σ` by adjusting `σ a := σ a + da` and `σ b := σ b + db` (with `Fin`
arithmetic), leaving everything else unchanged. -/
noncomputable def configUpdateTwo (σ : V → Fin (N + 1)) (a b : V) (va vb : Fin (N + 1)) :
    V → Fin (N + 1) :=
  fun k => if k = a then va else if k = b then vb else σ k

omit [Fintype V] in
/-- Off-`{a, b}` agreement with `σ` (when `a ≠ b`). -/
theorem configUpdateTwo_agree (σ : V → Fin (N + 1)) (a b : V)
    (va vb : Fin (N + 1)) :
    ∀ k, k ≠ a → k ≠ b → configUpdateTwo σ a b va vb k = σ k := by
  intro k hka hkb
  simp [configUpdateTwo, hka, hkb]

omit [Fintype V] in
/-- Value at `a` for `configUpdateTwo`. -/
theorem configUpdateTwo_at_a (σ : V → Fin (N + 1)) (a b : V) (va vb : Fin (N + 1)) :
    configUpdateTwo σ a b va vb a = va := by
  simp [configUpdateTwo]

omit [Fintype V] in
/-- Value at `b` for `configUpdateTwo` (when `a ≠ b`). -/
theorem configUpdateTwo_at_b (σ : V → Fin (N + 1)) {a b : V} (hab : a ≠ b)
    (va vb : Fin (N + 1)) :
    configUpdateTwo σ a b va vb b = vb := by
  simp [configUpdateTwo, hab.symm]

omit [Fintype V] in
/-- **Transverse pair shift on the bipartite complete graph**: from `σ` with `σ a ≥ 1`,
`σ b ≤ N − 1`, and `(a, b)` bipartite-adjacent, the move *lowering `a` by 1, raising `b` by 1* is
a `RaiseLowerStepS`. -/
theorem raiseLowerStepS_pair_shift_lower_a_raise_b
    (A : V → Bool) {a b : V} (hadj : (bipartiteCompleteGraphOf A).Adj a b)
    {σ : V → Fin (N + 1)}
    (hka : 1 ≤ (σ a).val) (hkb : (σ b).val + 1 ≤ N) :
    RaiseLowerStepS (bipartiteCompleteGraphOf A) σ
      (configUpdateTwo σ a b ⟨(σ a).val - 1, by have := (σ a).isLt; omega⟩
        ⟨(σ b).val + 1, by omega⟩) := by
  refine ⟨a, b, hadj, ?_, ?_⟩
  · right
    refine ⟨?_, ?_⟩
    · rw [configUpdateTwo_at_a]; show (σ a).val - 1 + 1 = (σ a).val; omega
    · rw [configUpdateTwo_at_b _ hadj.ne]
  · exact configUpdateTwo_agree _ _ _ _ _

omit [Fintype V] in
/-- **Transverse pair shift the other direction**: from `σ` with `σ a ≤ N − 1`, `σ b ≥ 1`, the
move *raising `a` by 1, lowering `b` by 1* is a `RaiseLowerStepS`. -/
theorem raiseLowerStepS_pair_shift_raise_a_lower_b
    (A : V → Bool) {a b : V} (hadj : (bipartiteCompleteGraphOf A).Adj a b)
    {σ : V → Fin (N + 1)}
    (hka : (σ a).val + 1 ≤ N) (hkb : 1 ≤ (σ b).val) :
    RaiseLowerStepS (bipartiteCompleteGraphOf A) σ
      (configUpdateTwo σ a b ⟨(σ a).val + 1, by omega⟩
        ⟨(σ b).val - 1, by have := (σ b).isLt; omega⟩) := by
  refine ⟨a, b, hadj, ?_, ?_⟩
  · left
    refine ⟨?_, ?_⟩
    · rw [configUpdateTwo_at_a]
    · rw [configUpdateTwo_at_b _ hadj.ne]; show (σ b).val - 1 + 1 = (σ b).val; omega
  · exact configUpdateTwo_agree _ _ _ _ _

omit [Fintype V] in
/-- **ParityBondStepS witness (both raise)** on a bipartite edge. -/
theorem parityBondStepS_pair_raise
    (A : V → Bool) {a b : V} (hadj : (bipartiteCompleteGraphOf A).Adj a b)
    {σ : V → Fin (N + 1)}
    (hka : (σ a).val + 1 ≤ N) (hkb : (σ b).val + 1 ≤ N) :
    ParityBondStepS (bipartiteCompleteGraphOf A) σ
      (configUpdateTwo σ a b ⟨(σ a).val + 1, by omega⟩
        ⟨(σ b).val + 1, by omega⟩) := by
  refine ⟨a, b, hadj, ?_, ?_⟩
  · left
    refine ⟨?_, ?_⟩
    · rw [configUpdateTwo_at_a]
    · rw [configUpdateTwo_at_b _ hadj.ne]
  · exact configUpdateTwo_agree _ _ _ _ _

omit [Fintype V] in
/-- **ParityBondStepS witness (both lower)** on a bipartite edge. -/
theorem parityBondStepS_pair_lower
    (A : V → Bool) {a b : V} (hadj : (bipartiteCompleteGraphOf A).Adj a b)
    {σ : V → Fin (N + 1)}
    (hka : 1 ≤ (σ a).val) (hkb : 1 ≤ (σ b).val) :
    ParityBondStepS (bipartiteCompleteGraphOf A) σ
      (configUpdateTwo σ a b ⟨(σ a).val - 1, by have := (σ a).isLt; omega⟩
        ⟨(σ b).val - 1, by have := (σ b).isLt; omega⟩) := by
  refine ⟨a, b, hadj, ?_, ?_⟩
  · right
    refine ⟨?_, ?_⟩
    · rw [configUpdateTwo_at_a]; show (σ a).val - 1 + 1 = (σ a).val; omega
    · rw [configUpdateTwo_at_b _ hadj.ne]; show (σ b).val - 1 + 1 = (σ b).val; omega
  · exact configUpdateTwo_agree _ _ _ _ _

/-- Update at a single site. -/
noncomputable def configUpdateOne (σ : V → Fin (N + 1)) (a : V) (va : Fin (N + 1)) :
    V → Fin (N + 1) :=
  fun k => if k = a then va else σ k

omit [Fintype V] in
/-- Off-`a` agreement. -/
theorem configUpdateOne_agree (σ : V → Fin (N + 1)) (a : V) (va : Fin (N + 1)) :
    ∀ k, k ≠ a → configUpdateOne σ a va k = σ k := by
  intro k hka
  simp [configUpdateOne, hka]

omit [Fintype V] in
/-- Value at `a`. -/
theorem configUpdateOne_at (σ : V → Fin (N + 1)) (a : V) (va : Fin (N + 1)) :
    configUpdateOne σ a va a = va := by
  simp [configUpdateOne]

omit [Fintype V] in
/-- **SingleIonStepS witness (raise by 2)**. -/
theorem singleIonStepS_raise
    {σ : V → Fin (N + 1)} (a : V) (hka : (σ a).val + 2 ≤ N) :
    SingleIonStepS σ (configUpdateOne σ a ⟨(σ a).val + 2, by omega⟩) := by
  refine ⟨a, ?_, ?_⟩
  · left
    rw [configUpdateOne_at]
  · exact configUpdateOne_agree _ _ _

omit [Fintype V] in
/-- **SingleIonStepS witness (lower by 2)**. -/
theorem singleIonStepS_lower
    {σ : V → Fin (N + 1)} (a : V) (hka : 2 ≤ (σ a).val) :
    SingleIonStepS σ (configUpdateOne σ a ⟨(σ a).val - 2, by have := (σ a).isLt; omega⟩) := by
  refine ⟨a, ?_, ?_⟩
  · right
    rw [configUpdateOne_at]; show (σ a).val - 2 + 2 = (σ a).val; omega
  · exact configUpdateOne_agree _ _ _

end LatticeSystem.Quantum
