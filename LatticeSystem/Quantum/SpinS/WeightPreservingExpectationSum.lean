import LatticeSystem.Quantum.SpinS.MagSectorEmbedding
import LatticeSystem.Quantum.SpinS.SaturatedFullLadderOrthogonality

/-!
# Weight-preserving operator expectation = sum over `Ŝ³`-weight sectors
(Tasaki §2.5 spin-`S` infrastructure, Issue #4617 step 3)

For an operator `O : ManyBodyOpS V N` that commutes with the total
magnetization operator `Ŝ_tot^{(3)}` (so it preserves `Ŝ³`-weight), the
standard-inner-product expectation `⟨Φ, O Φ⟩ = star Φ ⬝ᵥ (O Φ)`
decomposes as the finite sum of the per-magnetization-sector diagonal
expectations.

Writing `Φ = Σ_M Φ_M` with
`Φ_M := magSectorEmbedding (magSectorRestriction (M := M) Φ)`
(`eq_sum_magSectorEmbedding_magSectorRestriction`), each `Φ_M` is a
`Ŝ_tot^{(3)}`-eigenvector with eigenvalue `c − M`, where
`c = |V| · N / 2` (`magSectorEmbedding_mem_magSubspaceS`). Bilinear
expansion of the dot product gives a double sum, and the off-diagonal
terms (`M ≠ M'`) vanish: because `O` commutes with `Ŝ_tot^{(3)}`, the
vector `O Φ_{M'}` is again a `Ŝ_tot^{(3)}`-eigenvector with eigenvalue
`c − M'`, and the Hermitian operator `Ŝ_tot^{(3)}` has orthogonal
eigenvectors at distinct (real) eigenvalues. Only the diagonal
`M = M'` terms survive.

The `Hermitian`-hypothesis on `O` is **not** required: the cross-term
vanishing relies only on the weight-preservation (`Commute`) and the
Hermiticity of `Ŝ_tot^{(3)}`, not of `O`.

Tracked in #4617.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- Abbreviation for the magnetization-`M` sector component of a full
spin-`S` configuration vector `Φ`: the zero-extension of the restriction
of `Φ` to the `magSumS = M` sector. -/
private noncomputable def weightComponent (Φ : (V → Fin (N + 1)) → ℂ)
    (M : ℕ) : (V → Fin (N + 1)) → ℂ :=
  magSectorEmbedding (magSectorRestriction (M := M) Φ)

/-- The abbreviation `c := |V| · N / 2` for the maximal `Ŝ_tot^{(3)}`
eigenvalue (cast into `ℂ`). -/
private noncomputable def weightCenter (V : Type*) [Fintype V] (N : ℕ) : ℂ :=
  (Fintype.card V : ℂ) * (N : ℂ) / 2

/-- Each weight component `Φ_M` is a `Ŝ_tot^{(3)}`-eigenvector with
eigenvalue `c − M`. -/
private theorem totalSpinSOp3_mulVec_weightComponent
    (Φ : (V → Fin (N + 1)) → ℂ) (M : ℕ) :
    (totalSpinSOp3 V N).mulVec (weightComponent Φ M)
      = (weightCenter V N - (M : ℂ)) • weightComponent Φ M := by
  have h := magSectorEmbedding_mem_magSubspaceS
    (magSectorRestriction (M := M) Φ)
  rw [mem_magSubspaceS_iff] at h
  simpa only [weightComponent, weightCenter] using h

omit [DecidableEq V] in
/-- `c − M` is real, i.e. fixed by complex conjugation. -/
private theorem star_weightCenter_sub_cast (M : ℕ) :
    star (weightCenter V N - (M : ℂ)) = weightCenter V N - (M : ℂ) := by
  unfold weightCenter
  simp only [star_sub, star_div₀, star_mul', RCLike.star_def,
    Complex.conj_natCast, map_ofNat]

omit [DecidableEq V] in
/-- For `M ≠ M'`, the eigenvalues `c − M` and `c − M'` are distinct. -/
private theorem weightCenter_sub_cast_ne {M M' : ℕ} (h : M ≠ M') :
    weightCenter V N - (M : ℂ) ≠ weightCenter V N - (M' : ℂ) := by
  intro heq
  apply h
  have hcast : (M : ℂ) = (M' : ℂ) := by linear_combination -heq
  exact Nat.cast_injective hcast

/-- If `O` commutes with `Ŝ_tot^{(3)}`, then `O Φ_{M'}` is again a
`Ŝ_tot^{(3)}`-eigenvector with eigenvalue `c − M'`. -/
private theorem totalSpinSOp3_mulVec_O_weightComponent
    (O : ManyBodyOpS V N) (hO_comm : Commute O (totalSpinSOp3 V N))
    (Φ : (V → Fin (N + 1)) → ℂ) (M : ℕ) :
    (totalSpinSOp3 V N).mulVec (O.mulVec (weightComponent Φ M))
      = (weightCenter V N - (M : ℂ)) • O.mulVec (weightComponent Φ M) := by
  rw [Matrix.mulVec_mulVec, ← hO_comm, ← Matrix.mulVec_mulVec,
    totalSpinSOp3_mulVec_weightComponent, Matrix.mulVec_smul]

/-- The cross term `star Φ_M ⬝ᵥ (O Φ_{M'})` vanishes for `M ≠ M'`,
because `Φ_M` and `O Φ_{M'}` are eigenvectors of the Hermitian operator
`Ŝ_tot^{(3)}` at distinct real eigenvalues. -/
private theorem crossTerm_eq_zero
    (O : ManyBodyOpS V N) (hO_comm : Commute O (totalSpinSOp3 V N))
    (Φ : (V → Fin (N + 1)) → ℂ) {M M' : ℕ} (h : M ≠ M') :
    star (weightComponent Φ M) ⬝ᵥ (O.mulVec (weightComponent Φ M')) = 0 :=
  Matrix.IsHermitian.dotProduct_eq_zero_of_eigenvalues_ne
    (totalSpinSOp3_isHermitian V N)
    (star_weightCenter_sub_cast M) (star_weightCenter_sub_cast M')
    (totalSpinSOp3_mulVec_weightComponent Φ M)
    (totalSpinSOp3_mulVec_O_weightComponent O hO_comm Φ M')
    (weightCenter_sub_cast_ne h)

/-- **Weight-preserving expectation decomposition**: for an operator `O`
on the spin-`S` many-body Hilbert space that commutes with the total
magnetization operator `Ŝ_tot^{(3)}` (so it preserves `Ŝ³`-weight), the
standard-inner-product expectation `⟨Φ, O Φ⟩ = star Φ ⬝ᵥ (O Φ)`
decomposes as the finite sum, over attainable magnetizations `M`, of the
diagonal expectations of `O` on the weight components
`Φ_M := magSectorEmbedding (magSectorRestriction (M := M) Φ)`.

The Hermiticity of `O` is **not** needed: only weight-preservation
(`hO_comm`) and the Hermiticity of `Ŝ_tot^{(3)}` enter the cross-term
vanishing argument. -/
theorem weightPreserving_expectation_eq_sum_sector (O : ManyBodyOpS V N)
    (hO_comm : Commute O (totalSpinSOp3 V N))
    (Φ : (V → Fin (N + 1)) → ℂ) :
    star Φ ⬝ᵥ (O.mulVec Φ)
      = ∑ M ∈ Finset.range (Fintype.card V * N + 1),
          star (magSectorEmbedding (magSectorRestriction (M := M) Φ)) ⬝ᵥ
            (O.mulVec (magSectorEmbedding (magSectorRestriction (M := M) Φ))) := by
  -- Decompose `Φ` as the finite sum of its weight components.
  set s : Finset ℕ := Finset.range (Fintype.card V * N + 1) with hs
  have hΦ : Φ = ∑ M ∈ s, weightComponent Φ M :=
    eq_sum_magSectorEmbedding_magSectorRestriction Φ
  -- Expand the dot product bilinearly into a double sum.
  calc
    star Φ ⬝ᵥ (O.mulVec Φ)
        = ∑ M ∈ s, ∑ M' ∈ s,
            star (weightComponent Φ M) ⬝ᵥ
              (O.mulVec (weightComponent Φ M')) := by
          conv_lhs => rw [hΦ]
          rw [Matrix.mulVec_sum, star_sum, sum_dotProduct]
          refine Finset.sum_congr rfl (fun M _ => ?_)
          rw [dotProduct_sum]
    _ = ∑ M ∈ s,
            star (weightComponent Φ M) ⬝ᵥ
              (O.mulVec (weightComponent Φ M)) := by
          refine Finset.sum_congr rfl (fun M hM => ?_)
          rw [Finset.sum_eq_single M]
          · intro M' _ hM'
            exact crossTerm_eq_zero O hO_comm Φ (Ne.symm hM')
          · intro hMnot
            exact absurd hM hMnot
    _ = _ := by
          simp only [weightComponent]

end LatticeSystem.Quantum
