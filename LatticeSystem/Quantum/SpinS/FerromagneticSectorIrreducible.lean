import LatticeSystem.Quantum.SpinS.FerromagneticHeisenbergSign
import LatticeSystem.Quantum.SpinS.ConnectedDressedPF
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorMarshallCore

/-!
# Tasaki §2.4, p. 34: Perron-Frobenius irreducibility on a magnetization sector

The graph-theoretic half of the Theorem 2.1 uniqueness argument.  Tasaki's Theorem A.18 (p. 475)
applies to a real symmetric matrix whose off-diagonal entries are non-positive and whose indices
are all connected through non-vanishing entries.  The first condition is the ferromagnetic sign
structure; the second is property (iii) of the Proof of Theorem 2.2 (stated p. 40, proved
pp. 41-42): on a connected graph any two configurations of equal magnetization are joined by a
finite chain of `Ŝ⁺_x Ŝ⁻_y` moves along edges.

The shift `c` is not constructed here: it enters as the hypothesis that `c` lies strictly above
every diagonal entry, and the caller supplies it.  This module assembles the sign lemmas and the
raise/lower reachability into `Matrix.IsIrreducible` for `c·1 - Ĥ` restricted to a magnetization
sector, the form in which the repo's Perron-Frobenius machinery consumes them.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.4 Theorem 2.1, p. 34; Proof of Theorem 2.2, property (iii), stated p. 40, proved
pp. 41-42; solution of Problem 2.4.a, p. 496; Theorem A.18, p. 475.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Connected-graph sector irreducibility of the ferromagnetic Heisenberg matrix**
(Tasaki §2.4, p. 34; Proof of Theorem 2.2, property (iii), stated p. 40, proved pp. 41-42;
Theorem A.18, p. 475).

On a connected graph `G` with a real, symmetric coupling supported on the edges of `G`
(`hJ_supp`) and strictly ferromagnetic there (`hJ_ferro`), the shifted matrix `c·1 - Ĥ`
restricted to the magnetization-`M` sector is Perron-Frobenius irreducible, for any `c` strictly
above the diagonal.

Non-negativity of the shifted matrix is the off-diagonal sign structure
(`heisenbergHamiltonianS_apply_re_nonpos_of_ne`) together with the strict diagonal bound; strong
connectivity of its support digraph is the strict negativity along one ladder step
(`heisenbergHamiltonianS_apply_re_neg_of_raiseLowerStepS_witness`) transported along the chains of
`raiseLowerReachableSMagSector_of_connected`.  No Marshall sign dressing and no bipartiteness of
`G` are involved. -/
theorem isIrreducible_shiftedHeisenbergSReMatrixOnMagSector_connected_ferro
    {G : SimpleGraph V} {J : V → V → ℂ} {c : ℝ} {M : ℕ}
    (hGconn : G.Connected)
    (hJ_supp : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJ_ferro : ∀ x y, G.Adj x y → (J x y).re < 0)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hc_strict : ∀ σ, heisenbergHamiltonianSReMatrix J N σ σ < c) :
    (c • (1 : Matrix (magConfigS V N M) (magConfigS V N M) ℝ)
        - heisenbergHamiltonianSReMatrixOnMagSector J N M).IsIrreducible := by
  classical
  set B : Matrix (magConfigS V N M) (magConfigS V N M) ℝ :=
    c • (1 : Matrix (magConfigS V N M) (magConfigS V N M) ℝ)
      - heisenbergHamiltonianSReMatrixOnMagSector J N M with hB
  have hJ_nonpos : ∀ x y, (J x y).re ≤ 0 := by
    intro x y
    by_cases hadj : G.Adj x y
    · exact (hJ_ferro x y hadj).le
    · rw [hJ_supp x y hadj, Complex.zero_re]
  have hentry : ∀ σ τ : magConfigS V N M,
      B σ τ = c * (1 : Matrix (magConfigS V N M) (magConfigS V N M) ℝ) σ τ
        - (heisenbergHamiltonianS J N σ.1 τ.1).re := by
    intro σ τ
    rw [hB, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      heisenbergHamiltonianSReMatrixOnMagSector_apply, heisenbergHamiltonianSReMatrix_apply]
  have hoffdiag : ∀ σ τ : magConfigS V N M, σ ≠ τ →
      B σ τ = -(heisenbergHamiltonianS J N σ.1 τ.1).re := by
    intro σ τ hστ
    rw [hentry σ τ, Matrix.one_apply_ne hστ, mul_zero, zero_sub]
  have hdiag : ∀ σ : magConfigS V N M, 0 < B σ σ := by
    intro σ
    rw [hentry σ σ, Matrix.one_apply_eq, mul_one]
    have h := hc_strict σ.1
    rw [heisenbergHamiltonianSReMatrix_apply] at h
    linarith
  have hnn : ∀ σ τ : magConfigS V N M, 0 ≤ B σ τ := by
    intro σ τ
    by_cases hστ : σ = τ
    · subst hστ
      exact (hdiag σ).le
    · rw [hoffdiag σ τ hστ, neg_nonneg]
      exact heisenbergHamiltonianS_apply_re_nonpos_of_ne hJ_real hJ_nonpos
        (fun heq => hστ (Subtype.ext heq))
  have hstep : ∀ σ τ : magConfigS V N M, RaiseLowerStepSMagSector G σ τ → 0 < B τ σ := by
    intro σ τ hst
    obtain ⟨x, y, hadj, hsh, hagree⟩ := hst
    have hne : τ.1 ≠ σ.1 := by
      intro heq
      have hx : (τ.1 x).val = (σ.1 x).val := by rw [heq]
      rcases hsh with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    rw [hoffdiag τ σ (fun heq => hne (congrArg Subtype.val heq)), neg_pos]
    exact heisenbergHamiltonianS_apply_re_neg_of_raiseLowerStepS_witness N hadj
      (hJ_real x y) (hJ_ferro x y hadj) (hJ_sym x y) hsh hagree
  rw [Matrix.isIrreducible_iff_exists_pow_pos hnn]
  intro σ τ
  by_cases hστ : σ = τ
  · subst hστ
    exact ⟨1, Nat.one_pos, by rw [pow_one]; exact hdiag σ⟩
  · obtain ⟨k, hpos⟩ : ∃ k : ℕ, 0 < (B ^ k) σ τ := by
      apply exists_matrixPow_apply_pos_of_raiseLowerReachableSMagSector (G := G) hnn
      · intro σ₀ τ₀ hst
        exact hstep σ₀ τ₀ hst
      · exact raiseLowerReachableSMagSector_of_connected hGconn τ σ
    refine ⟨k, ?_, hpos⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [pow_zero, Matrix.one_apply, if_neg hστ] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact hk

end LatticeSystem.Quantum
