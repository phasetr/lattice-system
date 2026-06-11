import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaConnectivity
import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaStateQuiver

/-!
# Connectivity condition: classification (Tasaki §11.2.2, Theorem 11.8 and Lemma 11.9)

After **Definition 11.6** (`nagaokaConnectivity`) and **Theorem 11.7**
(`nagaoka_theorem_11_7`, proven in `NagaokaConnectivity.lean`), Tasaki §11.2.2
gives two criteria for *verifying* the connectivity condition on a concrete
bond graph `(Λ, B)`, `B = {{x, y} : t_{x,y} ≠ 0}`:

* **Theorem 11.8** (Bobrow–Stubis–Li): the connectivity condition holds *iff*
  `(Λ, B)` is biconnected and is not a simple loop (periodic chain) with more
  than four sites.
* **Lemma 11.9**: if `(Λ, B)` is connected by *exchange bonds*, the connectivity
  condition holds.

The graph predicates live in `NagaokaBondGraph.lean`; this module holds the two
statements in book order.

## Status

* **Theorem 11.8** is recorded as an **`axiom`**: Tasaki's text *explicitly
  leaves the proof to the original papers* — Bobrow, Stubis and Li, and Wilson's
  graph-theoretic analysis of the "15-puzzle" (Tasaki 1st ed., §11.2.2, p. 387,
  refs [4], [81]). The book itself provides no proof, so it is a *cited external
  classification theorem*. Rather than reproduce Wilson's theorem we axiomatize
  its statement.

* **Lemma 11.9** was initially axiomatized here (project decision, 2026-06-04)
  and is now a **proved theorem** `nagaoka_lemma_11_9`, at its original module
  path: the full "15-puzzle" hole-motion machinery (loop-trip spin swaps,
  exchange-bond generation, hole parking, mismatch reduction) lives in
  `NagaokaStateQuiver.lean`, whose zero-diagonal capstone
  (`nagaokaConnectivity_of_connectedByExchangeBonds`) is transferred here to the
  general symmetric `t ≥ 0` by diagonal zeroing (`tasakiEffReMatrix_zeroDiag`,
  `nagaokaBondGraph_zeroDiag` — neither the Tasaki matrix nor the bond graph
  reads the diagonal of `t`).

**Theorem 11.7 itself (`NagaokaConnectivity.lean`) is `sorry`-free and does not
depend on the Theorem 11.8 axiom** — it is isolated in this file so that the
proven core stays axiom-clean.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.2.2, Theorem 11.8 and Lemma 11.9, pp. 386–388.
-/

namespace LatticeSystem.Fermion

/-- **Tasaki Theorem 11.8 (necessary and sufficient condition for connectivity).**
A Hubbard model with `U = ∞`, `N = |Λ| − 1` and `t ≥ 0` satisfies the
connectivity condition (Definition 11.6, `nagaokaConnectivity`) if and only if
its bond graph is biconnected and is not a simple loop with more than four sites.

**AXIOMATIZED (deferred to future implementation).**  Tasaki leaves the proof to
Bobrow–Stubis–Li and Wilson's "15-puzzle" theorem (1st ed., §11.2.2, p. 387,
refs [4], [81]); the book gives no proof, so this is a cited external
classification result.  See the module docstring for the rationale.  (`1 ≤ N`
excludes the degenerate single-site case, where there are no electrons to order.)
-/
axiom nagaoka_theorem_11_8 (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (hN : 1 ≤ N) (htsym : ∀ i j, t i j = t j i) (hpos : ∀ i j, 0 ≤ t i j) :
    nagaokaConnectivity N t ↔
      (IsBiconnected (nagaokaBondGraph N t) ∧
        ¬ IsSimpleLoopGTFour (nagaokaBondGraph N t))

/-- **Tasaki Lemma 11.9 (a sufficient condition for the connectivity), PROVED.**  If the bond
graph is connected by exchange bonds, the connectivity condition (Definition 11.6,
`nagaokaConnectivity`) holds.  This is the full 15-puzzle argument of Tasaki §11.2.2, pp. 387–388
(formerly an `axiom` here, now discharged): exchange bonds yield in-place spin swaps via
length-3/4 loop trips (Figs. 11.8, 11.9 and footnote 14), the swaps propagate along exchange-bond
walks (footnote 13), parking the hole at a farthest vertex of the exchange-bond graph makes every
pair swappable, and the mismatch-reduction induction connects any two same-magnetization
configurations — see `NagaokaStateQuiver.lean` for the machinery.  The general (not necessarily
zero-diagonal) hopping reduces to the zero-diagonal capstone
`nagaokaConnectivity_of_connectedByExchangeBonds` because neither the Tasaki matrix nor the bond
graph reads the diagonal of `t` (`tasakiEffReMatrix_zeroDiag`, `nagaokaBondGraph_zeroDiag`). -/
theorem nagaoka_lemma_11_9 (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (hN : 1 ≤ N) (htsym : ∀ i j, t i j = t j i) (hpos : ∀ i j, 0 ≤ t i j) :
    ConnectedByExchangeBonds (nagaokaBondGraph N t) → nagaokaConnectivity N t := by
  intro hconn
  -- run the zero-diagonal capstone on the diagonal-zeroed hopping and transfer back
  set t₀ : Fin (N + 1) → Fin (N + 1) → ℝ := fun i j => if i = j then 0 else t i j with ht₀
  have htsym₀ : ∀ i j, t₀ i j = t₀ j i := by
    intro i j
    by_cases h : i = j
    · simp [ht₀, h]
    · simp [ht₀, h, Ne.symm h, htsym i j]
  have htdiag₀ : ∀ i, t₀ i i = 0 := fun i => by simp [ht₀]
  have hpos₀ : ∀ i j, 0 ≤ t₀ i j := by
    intro i j
    by_cases h : i = j
    · simp [ht₀, h]
    · simp [ht₀, h, hpos i j]
  have hconn₀ : ConnectedByExchangeBonds (nagaokaBondGraph N t₀) := by
    rw [ht₀, nagaokaBondGraph_zeroDiag]; exact hconn
  have hcap := nagaokaConnectivity_of_connectedByExchangeBonds N t₀ hN htsym₀ htdiag₀ hpos₀ hconn₀
  intro m
  have hPF : nagaokaPFMatrixOnSector N t m = nagaokaPFMatrixOnSector N t₀ m := by
    unfold nagaokaPFMatrixOnSector tasakiEffReMatrixOnSector
    rw [ht₀, tasakiEffReMatrix_zeroDiag]
  rw [hPF]
  exact hcap m

end LatticeSystem.Fermion
