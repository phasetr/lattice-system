import LatticeSystem.Quantum.SpinS.MagParityOperator
import LatticeSystem.Quantum.SpinS.ParityConfig
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Block-diagonal submatrix bridge: full eigenspace ⊓ ker(P) → submatrix eigenspace

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(f.4) bridge: for a parity-block-diagonal complex matrix `M` (vanishing on cross-parity entries),
the intersection of its `ν`-eigenspace with the `(-1)^p` eigenspace of `magParityDiagS`
injects (via restriction to the parity-`p` subtype) into the `ν`-eigenspace of the parity-block
submatrix.  Hence `finrank ≤` finrank submatrix.

Combined with `complex_dressed_parity_block_submatrix_eigenspace_finrank_le_one` (#3831, gives
`finrank ℂ submatrix ≤ 1` for the dressed `Ĥ'`), this yields `finrank ℂ (dressed Ĥ'
eigenspace ⊓ ker(P=±1)) ≤ 1` — exactly the per-parity-block bound needed by
`axisSwappedAnisotropicHeisenbergS_eigenspace_finrank_le_two_of_blocks_le_one` (modulo Θ_A
similarity for transferring from dressed to bare).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Module Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **A `(-1)^p` eigenvector of `magParityDiagS` vanishes off parity-`p` configurations**. -/
theorem ker_magParityDiagS_apply_eq_zero_of_parity_ne
    {p : ℕ} {w : (Λ → Fin (N + 1)) → ℂ}
    (hw : Matrix.toLin' (magParityDiagS Λ N) w = ((-1 : ℂ) ^ p) • w)
    {σ : Λ → Fin (N + 1)} (hσ : magSumS σ % 2 ≠ p % 2) :
    w σ = 0 := by
  rw [Matrix.toLin'_apply] at hw
  have hi := congrFun hw σ
  simp only [magParityDiagS, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at hi
  have hne : ((-1 : ℂ) ^ magSumS σ) ≠ ((-1 : ℂ) ^ p) := by
    rcases Nat.even_or_odd (magSumS σ) with hσe | hσo <;>
      rcases Nat.even_or_odd p with hpe | hpo
    · exfalso; apply hσ; rw [Nat.even_iff] at hσe hpe; omega
    · rw [Even.neg_one_pow hσe, Odd.neg_one_pow hpo]; norm_num
    · rw [Odd.neg_one_pow hσo, Even.neg_one_pow hpe]; norm_num
    · exfalso; apply hσ; rw [Nat.odd_iff] at hσo hpo; omega
  have hzero : ((-1 : ℂ) ^ magSumS σ - (-1) ^ p) * w σ = 0 := by
    rw [sub_mul]; linear_combination hi
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)

/-- **Sum reduction**: a sum over `parityConfigS Λ N p` equals a sum over the filtered universe. -/
private theorem sum_parityConfigS_eq_sum_filter {β : Type*} [AddCommMonoid β]
    (p : ℕ) (f : (Λ → Fin (N + 1)) → β) :
    ∑ τ : parityConfigS Λ N p, f τ.1 =
      ∑ τ ∈ (Finset.univ : Finset (Λ → Fin (N + 1))).filter (fun ρ => magSumS ρ % 2 = p), f τ := by
  change ∑ τ : { x : Λ → Fin (N + 1) // magSumS x % 2 = p }, f τ.1 = _
  exact (Finset.sum_subtype (Finset.univ.filter (fun ρ : Λ → Fin (N + 1) => magSumS ρ % 2 = p))
    (fun x => by simp) f).symm

/-- **The restriction-to-parity-block map** is well-defined into the submatrix eigenspace,
for parity-block-diagonal matrices. -/
noncomputable def parityRestrictMap
    {M : Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℂ}
    (_hM_block : ∀ σ τ : Λ → Fin (N + 1), magSumS σ % 2 ≠ magSumS τ % 2 → M σ τ = 0)
    {p : ℕ} (hp : p < 2) (ν : ℂ) :
    ↥(End.eigenspace (Matrix.toLin' M) ν ⊓
      End.eigenspace (Matrix.toLin' (magParityDiagS Λ N)) ((-1 : ℂ) ^ p)) →ₗ[ℂ]
    ↥(End.eigenspace (Matrix.toLin' (M.submatrix
      (fun σ : parityConfigS Λ N p => σ.1)
      (fun σ : parityConfigS Λ N p => σ.1))) ν) where
  toFun w := ⟨fun σ : parityConfigS Λ N p => w.1 σ.1, by
    rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]
    funext σ
    have hM_eig : (Matrix.toLin' M) w.1 = ν • w.1 := End.mem_eigenspace_iff.mp w.2.1
    have hw_eig : (Matrix.toLin' (magParityDiagS Λ N)) w.1 = ((-1 : ℂ) ^ p) • w.1 :=
      End.mem_eigenspace_iff.mp w.2.2
    rw [Matrix.toLin'_apply] at hM_eig
    have hfull := congrFun hM_eig σ.1
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hfull
    change (∑ τ : parityConfigS Λ N p, (M.submatrix
            (fun σ : parityConfigS Λ N p => σ.1)
            (fun σ : parityConfigS Λ N p => σ.1)) σ τ * w.1 τ.1) =
          ν * w.1 σ.1
    simp only [Matrix.submatrix_apply]
    rw [sum_parityConfigS_eq_sum_filter (Λ := Λ) (N := N) p
        (fun ρ => M σ.1 ρ * w.1 ρ)]
    rw [show ∑ τ ∈ (Finset.univ : Finset (Λ → Fin (N + 1))).filter
              (fun ρ => magSumS ρ % 2 = p), M σ.1 τ * w.1 τ =
            ∑ τ : Λ → Fin (N + 1), M σ.1 τ * w.1 τ from ?_]
    · exact hfull
    · -- Extend filter to universe: the complement contributes zero since w vanishes there.
      have hcompl : ∑ τ ∈ (Finset.univ : Finset (Λ → Fin (N + 1))).filter
                      (fun ρ => ¬ (magSumS ρ % 2 = p)), M σ.1 τ * w.1 τ = 0 := by
        refine Finset.sum_eq_zero fun ρ hρ => ?_
        have hρ_par : magSumS ρ % 2 ≠ p := (Finset.mem_filter.mp hρ).2
        have hρ_ne_p : magSumS ρ % 2 ≠ p % 2 := by
          have := Nat.mod_lt (magSumS ρ) (by norm_num : (0 : ℕ) < 2)
          omega
        rw [ker_magParityDiagS_apply_eq_zero_of_parity_ne hw_eig hρ_ne_p, mul_zero]
      have hsum := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Λ → Fin (N + 1)))
                    (fun ρ => magSumS ρ % 2 = p) (fun ρ => M σ.1 ρ * w.1 ρ)
      rw [hcompl, add_zero] at hsum
      exact hsum⟩
  map_add' u v := by ext σ; rfl
  map_smul' c v := by ext σ; rfl

/-- **`(f.4)` block-diag bridge**: the full eigenspace ⊓ `(-1)^p` eigenspace of `magParityDiagS`
injects into the parity-`p` submatrix eigenspace.  Hence the finrank of the former is bounded
by that of the latter. -/
theorem parity_block_full_eigenspace_inter_finrank_le_submatrix
    {M : Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℂ}
    (hM_block : ∀ σ τ : Λ → Fin (N + 1), magSumS σ % 2 ≠ magSumS τ % 2 → M σ τ = 0)
    {p : ℕ} (hp : p < 2) (ν : ℂ) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin' M) ν ⊓
        End.eigenspace (Matrix.toLin' (magParityDiagS Λ N)) ((-1 : ℂ) ^ p)) ≤
      finrank ℂ ↥(End.eigenspace (Matrix.toLin' (M.submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1))) ν) := by
  have hinj : Function.Injective (parityRestrictMap hM_block hp ν) := by
    intro u v huv
    apply Subtype.ext
    funext σ
    by_cases hσ : magSumS σ % 2 = p
    · have huv_σ := congrArg (fun w => w.1 ⟨σ, hσ⟩) huv
      exact huv_σ
    · have hp_ne : magSumS σ % 2 ≠ p % 2 := by
        have := Nat.mod_lt (magSumS σ) (by norm_num : (0 : ℕ) < 2)
        omega
      have hu_eig : (Matrix.toLin' (magParityDiagS Λ N)) u.1 = ((-1 : ℂ) ^ p) • u.1 :=
        End.mem_eigenspace_iff.mp u.2.2
      have hv_eig : (Matrix.toLin' (magParityDiagS Λ N)) v.1 = ((-1 : ℂ) ^ p) • v.1 :=
        End.mem_eigenspace_iff.mp v.2.2
      rw [ker_magParityDiagS_apply_eq_zero_of_parity_ne hu_eig hp_ne,
          ker_magParityDiagS_apply_eq_zero_of_parity_ne hv_eig hp_ne]
  exact LinearMap.finrank_le_finrank_of_injective hinj

end LatticeSystem.Quantum
