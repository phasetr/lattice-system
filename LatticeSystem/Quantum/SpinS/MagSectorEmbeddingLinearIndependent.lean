import LatticeSystem.Quantum.SpinS.MagSectorEmbedding

/-!
# Linear independence of magnetization-sector-embedded vectors

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) IVT crossing argument
brick (2-IVT-e).

Sector-embedded vectors `magSectorEmbedding Φ_i` indexed by **distinct**
magnetization values `M_i` are linearly independent in the full Hilbert space
`(V → Fin (N + 1)) → ℂ`. Proof: each embedded vector is supported on its own
magnetization sector, and the sectors are pairwise disjoint, so a linear
combination vanishing identically forces each coefficient to be zero on the
support of the corresponding vector.

This is used by the obligation (2) IVT crossing argument: at a hypothetical
crossing point `p* = γ(t*)` where `E_0(p*) = E_M(p*) = E_{-M}(p*)`, the three
sector ground eigenvectors lie in distinct magnetization sectors `0, M, -M`,
and their embeddings span a `≥ 3`-dimensional subspace of `ker(H(p*) - E_min)`,
contradicting the obligation (1) bound `dim ≤ 2`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] {N : ℕ}

/-- **Pairwise LI from disjoint magnetization-sector support**: if `Φ₁ ≠ 0`
and `Φ₂ ≠ 0` are sector vectors at distinct magnetization values `M₁ ≠ M₂`,
then `magSectorEmbedding Φ₁` and `magSectorEmbedding Φ₂` are linearly
independent in the full Hilbert space.

Proof: for `a • embedding Φ₁ + b • embedding Φ₂ = 0`, evaluate at any
sector-`M₁` configuration where `Φ₁ ≠ 0` to force `a = 0`; symmetrically
for `b`. -/
theorem linearIndependent_pair_magSectorEmbedding
    {M₁ M₂ : ℕ} (hM : M₁ ≠ M₂)
    {Φ₁ : magConfigS V N M₁ → ℂ} {Φ₂ : magConfigS V N M₂ → ℂ}
    (hΦ₁ : Φ₁ ≠ 0) (hΦ₂ : Φ₂ ≠ 0) :
    LinearIndependent ℂ ![magSectorEmbedding Φ₁, magSectorEmbedding Φ₂] := by
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ : magConfigS V N M₁, Φ₁ τ ≠ 0 := by
    by_contra h
    push Not at h
    exact hΦ₁ (funext h)
  obtain ⟨τ₂, hτ₂⟩ : ∃ τ : magConfigS V N M₂, Φ₂ τ ≠ 0 := by
    by_contra h
    push Not at h
    exact hΦ₂ (funext h)
  refine Fintype.linearIndependent_iff.mpr (fun c hc => ?_)
  intro i
  -- For each i, evaluate the combination at the corresponding sector witness.
  fin_cases i
  · -- c 0 = 0: evaluate at τ₁.1.
    have heval := congrFun hc τ₁.1
    -- heval : (∑ i, c i • ![embed Φ₁, embed Φ₂] i) τ₁.1 = 0.
    rw [show (∑ i, c i • ![magSectorEmbedding Φ₁, magSectorEmbedding Φ₂] i)
        = c 0 • magSectorEmbedding Φ₁ + c 1 • magSectorEmbedding Φ₂ from by
      simp [Fin.sum_univ_two]] at heval
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        magSectorEmbedding_apply_subtype Φ₁ τ₁,
        magSectorEmbedding_apply_of_not_mem Φ₂ (by rw [τ₁.2]; exact hM),
        mul_zero, add_zero] at heval
    exact (mul_eq_zero.mp heval).resolve_right hτ₁
  · -- c 1 = 0: evaluate at τ₂.1.
    have heval := congrFun hc τ₂.1
    rw [show (∑ i, c i • ![magSectorEmbedding Φ₁, magSectorEmbedding Φ₂] i)
        = c 0 • magSectorEmbedding Φ₁ + c 1 • magSectorEmbedding Φ₂ from by
      simp [Fin.sum_univ_two]] at heval
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        magSectorEmbedding_apply_of_not_mem Φ₁ (by rw [τ₂.2]; exact Ne.symm hM),
        magSectorEmbedding_apply_subtype Φ₂ τ₂,
        mul_zero, zero_add] at heval
    exact (mul_eq_zero.mp heval).resolve_right hτ₂

/-- **Three-vector LI from pairwise distinct magnetization sectors**: if
`Φ₀, Φ₁, Φ₂` are nonzero sector vectors at pairwise distinct magnetization
values `M₀, M₁, M₂`, then the three embeddings are linearly independent in
the full Hilbert space.

Proof: same disjoint-support argument as the two-vector case, evaluating at
a configuration in each sector where the corresponding `Φ_i` is non-zero. -/
theorem linearIndependent_triple_magSectorEmbedding
    {M₀ M₁ M₂ : ℕ} (h01 : M₀ ≠ M₁) (h02 : M₀ ≠ M₂) (h12 : M₁ ≠ M₂)
    {Φ₀ : magConfigS V N M₀ → ℂ}
    {Φ₁ : magConfigS V N M₁ → ℂ}
    {Φ₂ : magConfigS V N M₂ → ℂ}
    (hΦ₀ : Φ₀ ≠ 0) (hΦ₁ : Φ₁ ≠ 0) (hΦ₂ : Φ₂ ≠ 0) :
    LinearIndependent ℂ
      ![magSectorEmbedding Φ₀, magSectorEmbedding Φ₁, magSectorEmbedding Φ₂] := by
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ : magConfigS V N M₀, Φ₀ τ ≠ 0 := by
    by_contra h
    push Not at h
    exact hΦ₀ (funext h)
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ : magConfigS V N M₁, Φ₁ τ ≠ 0 := by
    by_contra h
    push Not at h
    exact hΦ₁ (funext h)
  obtain ⟨τ₂, hτ₂⟩ : ∃ τ : magConfigS V N M₂, Φ₂ τ ≠ 0 := by
    by_contra h
    push Not at h
    exact hΦ₂ (funext h)
  refine Fintype.linearIndependent_iff.mpr (fun c hc => ?_)
  intro i
  -- Unfold the three-term sum to c 0 • v₀ + c 1 • v₁ + c 2 • v₂.
  have hexpand :
      (∑ i, c i • ![magSectorEmbedding Φ₀,
                    magSectorEmbedding Φ₁,
                    magSectorEmbedding Φ₂] i) =
      c 0 • magSectorEmbedding Φ₀ + c 1 • magSectorEmbedding Φ₁ +
        c 2 • magSectorEmbedding Φ₂ := by
    simp [Fin.sum_univ_three]
  fin_cases i
  · -- c 0 = 0: evaluate at τ₀.1.
    have heval := congrFun hc τ₀.1
    rw [hexpand] at heval
    rw [Pi.add_apply, Pi.add_apply,
        Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
        smul_eq_mul, smul_eq_mul, smul_eq_mul,
        magSectorEmbedding_apply_subtype Φ₀ τ₀,
        magSectorEmbedding_apply_of_not_mem Φ₁ (by rw [τ₀.2]; exact h01),
        magSectorEmbedding_apply_of_not_mem Φ₂ (by rw [τ₀.2]; exact h02),
        mul_zero, mul_zero, add_zero, add_zero] at heval
    exact (mul_eq_zero.mp heval).resolve_right hτ₀
  · -- c 1 = 0: evaluate at τ₁.1.
    have heval := congrFun hc τ₁.1
    rw [hexpand] at heval
    rw [Pi.add_apply, Pi.add_apply,
        Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
        smul_eq_mul, smul_eq_mul, smul_eq_mul,
        magSectorEmbedding_apply_of_not_mem Φ₀ (by rw [τ₁.2]; exact Ne.symm h01),
        magSectorEmbedding_apply_subtype Φ₁ τ₁,
        magSectorEmbedding_apply_of_not_mem Φ₂ (by rw [τ₁.2]; exact h12),
        mul_zero, mul_zero, zero_add, add_zero] at heval
    exact (mul_eq_zero.mp heval).resolve_right hτ₁
  · -- c 2 = 0: evaluate at τ₂.1.
    have heval := congrFun hc τ₂.1
    rw [hexpand] at heval
    rw [Pi.add_apply, Pi.add_apply,
        Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
        smul_eq_mul, smul_eq_mul, smul_eq_mul,
        magSectorEmbedding_apply_of_not_mem Φ₀ (by rw [τ₂.2]; exact Ne.symm h02),
        magSectorEmbedding_apply_of_not_mem Φ₁ (by rw [τ₂.2]; exact Ne.symm h12),
        magSectorEmbedding_apply_subtype Φ₂ τ₂,
        mul_zero, mul_zero, zero_add, zero_add] at heval
    exact (mul_eq_zero.mp heval).resolve_right hτ₂

end LatticeSystem.Quantum
