import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeel

/-!
# Néel state and the bipartite imbalance weight (Tasaki §2.5 Theorem 2.3 foundation)

For a bipartite graph `(Λ, A)` with `A : Λ → Bool` partitioning the
vertex set, the **bipartite imbalance weight** is

  `bipartiteImbalanceWeight A N := (|A| − |¬A|) · N / 2 : ℂ`.

In Tasaki §2.5 Theorem 2.3 (`|A| ≠ |¬A|` case), this is the
predicted ground-state total-spin eigenvalue `S_tot = (|A| − |¬A|)·S`
under the standard convention `S = N/2`.

This file packages three foundational facts about this weight that
underpin the formalisation of Theorem 2.3 (γ-4):

1. **Bridge with `magEigenvalueS`**: the Néel configuration's
   `Ŝ_tot^{(3)}` eigenvalue equals the imbalance weight (already
   proven as `magEigenvalueS_neelConfigOfS`; this file restates
   the result against the named weight).
2. **Néel state lives in the predicted magnetization sector**:
   `neelStateOfS A N ∈ magSubspaceS Λ N (bipartiteImbalanceWeight A N)`.
3. **Edge case** (balanced bipartite `|A| = |¬A|`): the imbalance
   weight is zero. Edge case (saturated `|¬A| = 0`): the imbalance
   weight equals `m_max = |V|·N/2`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] {N : ℕ}

/-- **Bipartite imbalance weight**: the predicted ground-state
total-spin eigenvalue in Tasaki §2.5 Theorem 2.3, given by
`(|A| − |¬A|) · N / 2`. For balanced bipartite (`|A| = |¬A|`) this
is zero; for saturated bipartite (`|¬A| = 0`) this equals
`m_max = |V|·N/2`. -/
noncomputable def bipartiteImbalanceWeight (A : Λ → Bool) (N : ℕ) : ℂ :=
  (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
    ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) *
    ((N : ℂ) / 2)

/-- Unfold lemma for `bipartiteImbalanceWeight`. -/
theorem bipartiteImbalanceWeight_def (A : Λ → Bool) (N : ℕ) :
    bipartiteImbalanceWeight (Λ := Λ) A N =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) *
        ((N : ℂ) / 2) := rfl

/-- **Bridge**: the `Ŝ_tot^{(3)}` eigenvalue of the Néel
configuration on sublattice `A` equals
`bipartiteImbalanceWeight A N`. Restates
`magEigenvalueS_neelConfigOfS` against the named weight. -/
theorem magEigenvalueS_neelConfigOfS_eq_bipartiteImbalanceWeight
    (A : Λ → Bool) (N : ℕ) :
    magEigenvalueS (neelConfigOfS A N) =
      bipartiteImbalanceWeight (Λ := Λ) A N := by
  unfold bipartiteImbalanceWeight
  exact magEigenvalueS_neelConfigOfS A N

variable [DecidableEq Λ]

/-- **Néel state lives in the imbalance-weight magnetization sector**:
`neelStateOfS A N ∈ magSubspaceS Λ N (bipartiteImbalanceWeight A N)`.

Direct combination of `basisVecS_mem_magSubspaceS` (every basis
state lives in the magnetization subspace at its eigenvalue) and the
bridge above. -/
theorem neelStateOfS_mem_magSubspaceS_bipartiteImbalanceWeight
    (A : Λ → Bool) (N : ℕ) :
    (neelStateOfS A N : (Λ → Fin (N + 1)) → ℂ) ∈
      magSubspaceS Λ N (bipartiteImbalanceWeight (Λ := Λ) A N) := by
  unfold neelStateOfS
  rw [← magEigenvalueS_neelConfigOfS_eq_bipartiteImbalanceWeight]
  exact basisVecS_mem_magSubspaceS (neelConfigOfS A N)

omit [DecidableEq Λ] in
/-- **Balanced bipartite edge case**: when `|A| = |¬A|`, the imbalance
weight is zero. The Néel state then lies in `H_0`, recovering the
spin-`1/2` Tasaki §2.5 (2.5.4) sector. -/
theorem bipartiteImbalanceWeight_eq_zero_of_card_eq
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card =
         (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    bipartiteImbalanceWeight (Λ := Λ) A N = 0 := by
  unfold bipartiteImbalanceWeight
  rw [h]; ring

omit [DecidableEq Λ] in
/-- **Saturated bipartite edge case**: when `|¬A| = 0`, the
imbalance weight equals `m_max = |V|·N/2`. The Néel state at this
weight reduces to the all-up state `|σ_⊤⟩`. -/
theorem bipartiteImbalanceWeight_eq_mMax_of_cardNotA_zero
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    bipartiteImbalanceWeight (Λ := Λ) A N =
      (Fintype.card Λ : ℂ) * (N : ℂ) / 2 := by
  classical
  unfold bipartiteImbalanceWeight
  rw [h]
  have hA : (Finset.univ.filter (fun x : Λ => A x = true)).card = Fintype.card Λ := by
    have h_sum : (Finset.univ.filter (fun x : Λ => A x = true)).card +
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = Fintype.card Λ := by
      have hfilter_eq : Finset.univ.filter (fun x : Λ => (! A x) = true) =
          Finset.univ.filter (fun x : Λ => ¬ (A x = true)) := by
        congr 1
        funext x
        by_cases hA : A x = true
        · simp [hA]
        · simp [hA]
      rw [hfilter_eq, ← Finset.card_univ]
      exact Finset.card_filter_add_card_filter_not (fun x : Λ => A x = true)
    rw [h] at h_sum
    omega
  rw [hA]
  push_cast; ring

omit [DecidableEq Λ] in
/-- **Non-negativity in the asymmetric case**: when `|A| ≥ |¬A|`,
the imbalance weight is a non-negative real number. Useful as a
sanity check and as input to total-spin lower-bound arguments
(Theorem 2.3). -/
theorem bipartiteImbalanceWeight_re_nonneg_of_cardA_ge_cardNotA
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
         (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    0 ≤ (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  unfold bipartiteImbalanceWeight
  have hreal :
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) =
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) : ℝ) := by
    push_cast; ring
  have hN : (N : ℂ) / 2 = (((N : ℝ) / 2) : ℝ) := by push_cast; ring
  rw [hreal, hN, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h1 : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) ≤
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
    exact_mod_cast h
  have h2 : 0 ≤ (N : ℝ) / 2 := by positivity
  nlinarith

end LatticeSystem.Quantum
