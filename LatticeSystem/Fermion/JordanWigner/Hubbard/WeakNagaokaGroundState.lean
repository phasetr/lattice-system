import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaTheorem
import LatticeSystem.Fermion.JordanWigner.Hubbard.HardcoreSpan
import LatticeSystem.Quantum.SpinS.HermitianVariationalEquality
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueEigenvector
import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaGroundStateCore

/-!
# Tasaki Theorem 11.5: existence of the ferromagnetic ground state

The capstone `weakNagaoka_spinMultiplet`
(`Fermion/JordanWigner/Hubbard/WeakNagaokaTheorem.lean`) reduces the weak Nagaoka
theorem to the *existence* of a nonzero highest-weight `Ĥ_eff`-eigenvector — a
ferromagnetic ground state. Following Tasaki's §11.2.1 proof, this is obtained by
the variational (Schwarz) argument, **not** by Perron–Frobenius (PF and the
connectivity/irreducibility condition belong to §11.2.2, Theorem 11.7):

1. Take an arbitrary ground state `|Φ_GS⟩` of `Ĥ_eff`, expanded in the one-hole
   hard-core Tasaki basis with (real) coefficients `ϕ(x, σ)` (eq. (11.2.6)).
2. Ferromagnetize it: `ξ_x = (Σ_σ ϕ(x, σ)²)^{1/2}` (eq. (11.2.7)) and
   `|Φ_↑⟩ = Σ_x ξ_x |Φ_{x,↑}⟩` (eq. (11.2.8)).
3. The Schwarz inequality (eq. (11.2.9), already formalized as
   `hubbardWeakNagaoka_energy_bound`) gives `⟨Φ_↑|Ĥ_eff|Φ_↑⟩ ≤ ⟨Φ_GS|Ĥ_eff|Φ_GS⟩`,
   and `|Φ_↑⟩` has the same norm (`tasakiFerro_normSq_eq`), so `|Φ_↑⟩` is also a
   ground state.
4. `|Φ_↑⟩` is a highest-weight maximal-spin state, so `weakNagaoka_spinMultiplet`
   produces the full `(2 S_max + 1)`-multiplet.

This file builds the ferromagnetic state `|Φ_↑⟩ = Σ_x ξ_x |Φ_{x,↑}⟩` and its
highest-weight (maximal-spin) and nonvanishing properties.

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §11.2.1, Theorem 11.5, pp. 382-385.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
/-! ## The effective Hamiltonian acts as its Tasaki matrix -/

/-- **Operator lift.** The effective Hamiltonian acting on a Tasaki basis state
reassembles its Tasaki-matrix column: `Ĥ_eff |Φ_p⟩ = Σ_q ⟨Φ_q|Ĥ_eff|Φ_p⟩ |Φ_q⟩`.
Because `Ĥ_eff |Φ_p⟩` is hard-core and an `N`-electron eigenstate, it lies in the
one-hole hard-core sector, where the Tasaki basis is complete. This is the bridge
between the operator `Ĥ_eff` and the finite real-symmetric matrix of (11.2.5). -/
theorem hubbardEffectiveHamiltonian_mulVec_tasakiState (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (p : (x : Fin (N + 1)) × HoleSpin N x) :
    (hubbardEffectiveHamiltonian N t U).mulVec (tasakiState N p) =
      ∑ q : (x : Fin (N + 1)) × HoleSpin N x,
        (∑ w, tasakiState N q w *
            ((hubbardEffectiveHamiltonian N t U).mulVec (tasakiState N p)) w) •
          tasakiState N q :=
  tasaki_completeness N _ (fun w hw =>
    mulVec_apply_eq_zero_of_not_oneHole N _
      (hubbardEffectiveHamiltonian_mulVec_mem N t U (tasakiState N p))
      (hubbardEffectiveHamiltonian_mulVec_preserves_number N t U (tasakiState N p) (N : ℂ)
        (fermionTotalNumber_mulVec_tasakiState N p)) w hw)

/-! ## The Tasaki matrix of the effective Hamiltonian -/

/-- The Tasaki-basis embedding matrix: columns are the basis states `Φ_q`
(`T_{w,q} = Φ_q(w)`). -/
noncomputable def tasakiEmbedding (N : ℕ) :
    Matrix (Fin (2 * N + 2) → Fin 2) ((x : Fin (N + 1)) × HoleSpin N x) ℂ :=
  Matrix.of (fun w q => tasakiState N q w)

/-- The Tasaki matrix `M = Tᴴ Ĥ_eff T` of the effective Hamiltonian — the finite
real-symmetric matrix of eq. (11.2.5) representing `Ĥ_eff` in the Tasaki basis. -/
noncomputable def tasakiEffMatrix (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    Matrix ((x : Fin (N + 1)) × HoleSpin N x) ((x : Fin (N + 1)) × HoleSpin N x) ℂ :=
  (tasakiEmbedding N)ᴴ * hubbardEffectiveHamiltonian N t U * tasakiEmbedding N

/-- `M` is Hermitian, being the compression `Tᴴ Ĥ_eff T` of the Hermitian
effective Hamiltonian. -/
theorem tasakiEffMatrix_isHermitian (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (hJ : ∀ i j, star (t i j) = t j i) (hU : star U = U) :
    (tasakiEffMatrix N t U).IsHermitian := by
  change (tasakiEffMatrix N t U)ᴴ = tasakiEffMatrix N t U
  unfold tasakiEffMatrix
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,
    (hubbardEffectiveHamiltonian_isHermitian N hJ hU).eq, Matrix.mul_assoc]

/-- The entries of `M` are the Tasaki matrix elements of `Ĥ_eff`:
`M_{q,p} = ⟨Φ_q | Ĥ_eff | Φ_p⟩ = Σ_w Φ_q(w) (Ĥ_eff Φ_p)(w)` (real-bilinear pairing,
using that the basis states are real-valued). -/
theorem tasakiEffMatrix_apply (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (q p : (x : Fin (N + 1)) × HoleSpin N x) :
    tasakiEffMatrix N t U q p =
      ∑ w, tasakiState N q w *
        ((hubbardEffectiveHamiltonian N t U).mulVec (tasakiState N p)) w := by
  unfold tasakiEffMatrix tasakiEmbedding
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Matrix.conjTranspose_apply, Matrix.of_apply, tasakiState_star]
  congr 1

/-- **The effective Hamiltonian acts as the matrix `M` on Tasaki expansions:**
`Ĥ_eff (Σ_p c_p Φ_p) = Σ_q (M c)_q Φ_q`. Hence an `M`-eigenvector lifts to an
`Ĥ_eff`-eigenvector at the same eigenvalue. -/
theorem hubbardEffectiveHamiltonian_mulVec_tasakiExpansion (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (c : ((x : Fin (N + 1)) × HoleSpin N x) → ℂ) :
    (hubbardEffectiveHamiltonian N t U).mulVec (∑ p, c p • tasakiState N p) =
      ∑ q, ((tasakiEffMatrix N t U).mulVec c) q • tasakiState N q := by
  rw [Matrix.mulVec_sum]
  rw [show (∑ p, (hubbardEffectiveHamiltonian N t U).mulVec (c p • tasakiState N p))
      = ∑ p, ∑ q, (c p * tasakiEffMatrix N t U q p) • tasakiState N q from by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Matrix.mulVec_smul, hubbardEffectiveHamiltonian_mulVec_tasakiState, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [smul_smul, ← tasakiEffMatrix_apply]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl (fun p _ => by ring)

/-- An `M`-eigenvector lifts to an `Ĥ_eff`-eigenvector at the same eigenvalue:
if `M c = λ c` then `Ĥ_eff (Σ_q c_q Φ_q) = λ (Σ_q c_q Φ_q)`. -/
theorem hubbardEffectiveHamiltonian_mulVec_tasakiExpansion_of_eigen (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (c : ((x : Fin (N + 1)) × HoleSpin N x) → ℂ) (lam : ℂ)
    (hc : (tasakiEffMatrix N t U).mulVec c = lam • c) :
    (hubbardEffectiveHamiltonian N t U).mulVec (∑ p, c p • tasakiState N p) =
      lam • (∑ p, c p • tasakiState N p) := by
  rw [hubbardEffectiveHamiltonian_mulVec_tasakiExpansion, hc, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun q _ => by rw [Pi.smul_apply, smul_assoc])

/-! ## Energy of a Tasaki expansion equals the matrix quadratic form -/

/-- The effective-Hamiltonian energy of a Tasaki expansion is the quadratic form
of the Tasaki matrix `M`: `⟨Σ c_q Φ_q | Ĥ_eff | Σ c_q Φ_q⟩ = c · (M c)`. -/
theorem hubbardEffEnergy_tasakiExpansion (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (c : ((x : Fin (N + 1)) × HoleSpin N x) → ℂ) :
    hubbardEffEnergy N t U (∑ p, c p • tasakiState N p) =
      dotProduct c ((tasakiEffMatrix N t U).mulVec c) := by
  rw [hubbardEffEnergy_expand]
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => by
    rw [← tasakiEffMatrix_apply]))]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => by ring))

/-! ## The Tasaki matrix preserves the all-up sector -/

/-- The Tasaki matrix has no transitions out of the all-up sector:
`M ⟨y,τ⟩ ⟨x,↑⟩ = 0` whenever `τ ≠ (↑)`, because hopping the all-up hole keeps the
configuration all-up. -/
theorem tasakiEffMatrix_allUp_off (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (htdiag : ∀ i, t i i = 0) (y x : Fin (N + 1)) (τ : HoleSpin N y)
    (hτ : τ ≠ holeSpinUp N y) :
    tasakiEffMatrix N t U ⟨y, τ⟩ ⟨x, holeSpinUp N x⟩ = 0 := by
  rw [tasakiEffMatrix_apply]
  change (∑ w, hubbardTasakiBasisState N y τ.val w *
    ((hubbardEffectiveHamiltonian N t U) *ᵥ hubbardTasakiBasisState N x (holeSpinUp N x).val) w)
    = 0
  by_cases hxy : x = y
  · subst hxy
    exact hubbardEffective_tasaki_matrixElement_diag N x (holeSpinUp N x).val τ.val t U htdiag
  · rw [hubbardEffective_tasaki_matrixElement N x y (holeSpinUp N x).val τ.val t U hxy,
      if_neg ?_, mul_zero]
    intro hc
    apply hτ
    apply Subtype.ext
    funext z
    change τ.val z = true
    by_cases hzy : z = y
    · subst hzy; exact τ.2
    · have hmove : hubbardSpinMove N (holeSpinUp N x).val x y z = true := by
        simp [hubbardSpinMove, holeSpinUp, Function.update_apply]
      have hsp := oneHoleConfig_spin_eq N y (hubbardSpinMove N (holeSpinUp N x).val x y)
        τ.val hc z hzy
      rw [← hsp]; exact hmove

/-! ## The all-up block of the Tasaki matrix -/

/-- Embed a hole-position weight vector `ξ : Fin (N+1) → ℂ` into the full Tasaki
index by placing it on the all-up states: `(upEmbed ξ) ⟨x,σ⟩ = ξ_x` if `σ = (↑)`,
else `0`. -/
noncomputable def upEmbed (N : ℕ) (ξ : Fin (N + 1) → ℂ) :
    ((x : Fin (N + 1)) × HoleSpin N x) → ℂ :=
  fun p => if p.2 = holeSpinUp N p.1 then ξ p.1 else 0

/-- The all-up state is the Tasaki expansion of the embedded weights. -/
theorem pfFerroState_eq_tasakiExpansion (N : ℕ) (ξ : Fin (N + 1) → ℂ) :
    pfFerroState N ξ = ∑ p, upEmbed N ξ p • tasakiState N p := by
  classical
  rw [pfFerroState, Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single (holeSpinUp N x)
    (fun σ _ hσ => by simp only [upEmbed, if_neg hσ, zero_smul])
    (fun hmem => absurd (Finset.mem_univ _) hmem)]
  simp [upEmbed]

/-- The all-up block of the Tasaki matrix: the single-hole hopping matrix in the
maximal-spin sector, `M_↑ y x = ⟨Φ_{y,↑} | Ĥ_eff | Φ_{x,↑}⟩`. -/
noncomputable def tasakiEffMatrixUp (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun y x => tasakiEffMatrix N t U ⟨y, holeSpinUp N y⟩ ⟨x, holeSpinUp N x⟩

/-- The all-up block is Hermitian (a principal submatrix of the Hermitian `M`). -/
theorem tasakiEffMatrixUp_isHermitian (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (hJ : ∀ i j, star (t i j) = t j i) (hU : star U = U) :
    (tasakiEffMatrixUp N t U).IsHermitian := by
  ext y x
  rw [Matrix.conjTranspose_apply, tasakiEffMatrixUp, tasakiEffMatrixUp,
    ← Matrix.conjTranspose_apply, (tasakiEffMatrix_isHermitian N t U hJ hU).eq]

/-- `M` acting on an embedded weight vector stays in the all-up sector and equals
the embedding of the all-up block acting on the weights:
`M (upEmbed ξ) = upEmbed (M_↑ ξ)`. -/
theorem tasakiEffMatrix_mulVec_upEmbed (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (htdiag : ∀ i, t i i = 0) (ξ : Fin (N + 1) → ℂ) :
    (tasakiEffMatrix N t U).mulVec (upEmbed N ξ) =
      upEmbed N ((tasakiEffMatrixUp N t U).mulVec ξ) := by
  classical
  funext q
  obtain ⟨y, τ⟩ := q
  have hred : (tasakiEffMatrix N t U).mulVec (upEmbed N ξ) ⟨y, τ⟩ =
      ∑ x, tasakiEffMatrix N t U ⟨y, τ⟩ ⟨x, holeSpinUp N x⟩ * ξ x := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_eq_single (holeSpinUp N x)
      (fun σ _ hσ => by simp only [upEmbed, if_neg hσ, mul_zero])
      (fun hmem => absurd (Finset.mem_univ _) hmem)]
    simp [upEmbed]
  rw [hred]
  by_cases hτ : τ = holeSpinUp N y
  · subst hτ
    rw [upEmbed, if_pos rfl]
    simp only [tasakiEffMatrixUp, Matrix.mulVec, dotProduct]
  · rw [upEmbed, if_neg hτ]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [tasakiEffMatrix_allUp_off N t U htdiag y x τ hτ, zero_mul]

/-- For a real coefficient vector, the Rayleigh quotient of `M` equals the real
part of the effective-Hamiltonian energy of the corresponding Tasaki expansion. -/
theorem rayleighOnVec_tasakiEffMatrix_of_real (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ)
    (U : ℂ) (c : ((x : Fin (N + 1)) × HoleSpin N x) → ℂ) (hc : star c = c) :
    rayleighOnVec (tasakiEffMatrix N t U) c =
      (hubbardEffEnergy N t U (∑ p, c p • tasakiState N p)).re := by
  unfold rayleighOnVec
  rw [hc, hubbardEffEnergy_tasakiExpansion]

/-! ## The effective Hamiltonian acts on the all-up state as the all-up block -/

/-- `Ĥ_eff (Σ_x ξ_x Φ_{x,↑}) = Σ_y (M_↑ ξ)_y Φ_{y,↑}`: on the all-up state the
effective Hamiltonian is the all-up block `M_↑`. -/
theorem hubbardEffectiveHamiltonian_mulVec_pfFerroState (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) (htdiag : ∀ i, t i i = 0)
    (ξ : Fin (N + 1) → ℂ) :
    (hubbardEffectiveHamiltonian N t U).mulVec (pfFerroState N ξ) =
      pfFerroState N ((tasakiEffMatrixUp N t U).mulVec ξ) := by
  rw [pfFerroState_eq_tasakiExpansion N ξ,
    hubbardEffectiveHamiltonian_mulVec_tasakiExpansion,
    tasakiEffMatrix_mulVec_upEmbed N t U htdiag,
    ← pfFerroState_eq_tasakiExpansion]

/-- If `ξ` is an eigenvector of the all-up block `M_↑` at eigenvalue `λ`, then the
all-up state `Σ_x ξ_x Φ_{x,↑}` is an `Ĥ_eff`-eigenvector at `λ`. -/
theorem hubbardEffectiveHamiltonian_mulVec_pfFerroState_of_eigen (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) (htdiag : ∀ i, t i i = 0)
    (ξ : Fin (N + 1) → ℂ) (lam : ℂ)
    (hξ : (tasakiEffMatrixUp N t U).mulVec ξ = lam • ξ) :
    (hubbardEffectiveHamiltonian N t U).mulVec (pfFerroState N ξ) =
      lam • pfFerroState N ξ := by
  rw [hubbardEffectiveHamiltonian_mulVec_pfFerroState N t U htdiag, hξ, pfFerroState,
    pfFerroState, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun x _ => by rw [Pi.smul_apply, smul_assoc])

/-! ## Tasaki Theorem 11.5 (weak Nagaoka), effective one-hole sector -/

/-- **Tasaki Theorem 11.5 (weak version of Nagaoka's theorem), effective one-hole
sector.** For a Hubbard model with `t_{x,y} = t_{y,x}`, no self-hopping
(`t_{i,i} = 0`), `N = |Λ| − 1` electrons in the `U ↑ ∞` (effective) limit: there
exist `N + 1 = 2 S_max + 1` linearly independent `Ĥ_eff`-eigenvectors at the
minimum energy of the maximal-spin (all-up) sector, all with total spin
`S_tot = S_max = N/2`.

The ground state `|Φ_↑⟩ = Σ_x ξ_x |Φ_{x,↑}⟩` is the all-up state built from a
minimum eigenvector `ξ` of the all-up hopping block `M_↑`; applying `Ŝ^-_tot`
generates the degenerate multiplet (capstone `weakNagaoka_spinMultiplet`).
(That this all-up minimum is the global ground energy is Tasaki's Schwarz bound
(11.2.9) `hubbardWeakNagaoka_energy_bound`, for `t ≥ 0`.)

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st edition, §11.2.1, Theorem 11.5, pp. 382-385. -/
theorem weakNagaoka_theorem_11_5 (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (hJ : ∀ i j, star (t i j) = t j i) (hU : star U = U) (htdiag : ∀ i, t i i = 0) :
    ∃ (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (E : ℂ),
      v ≠ 0 ∧
      E = ((hermitianMinEigenvalue (tasakiEffMatrixUp_isHermitian N t U hJ hU) : ℝ) : ℂ) ∧
      (hubbardEffectiveHamiltonian N t U).mulVec v = E • v ∧
      (fermionTotalSpinPlus N).mulVec v = 0 ∧
      (fermionTotalSpinZ N).mulVec v = ((N : ℂ) / 2) • v ∧
      LinearIndependent ℂ (fun k : Fin (N + 1) =>
          ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec v) ∧
      (∀ k : Fin (N + 1), (hubbardEffectiveHamiltonian N t U).mulVec
          (((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec v) =
        E • (((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec v)) ∧
      (∀ k : Fin (N + 1), (fermionTotalSpinSquared N).mulVec
          (((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec v) =
        ((N : ℂ) / 2 * ((N : ℂ) / 2 + 1)) •
          (((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec v)) := by
  obtain ⟨ξ, hξ_ne, hξ_eig⟩ :=
    exists_nonzero_eigenvector_hermitianMinEigenvalue
      (tasakiEffMatrixUp_isHermitian N t U hJ hU)
  refine ⟨pfFerroState N ξ,
    ((hermitianMinEigenvalue (tasakiEffMatrixUp_isHermitian N t U hJ hU) : ℝ) : ℂ),
    pfFerroState_ne_zero N ξ hξ_ne, rfl,
    hubbardEffectiveHamiltonian_mulVec_pfFerroState_of_eigen N t U htdiag ξ _ hξ_eig,
    fermionTotalSpinPlus_mulVec_pfFerroState N ξ,
    fermionTotalSpinZ_mulVec_pfFerroState N ξ, ?_, ?_, ?_⟩ <;>
  · obtain ⟨hLI, hdeg, hStot⟩ := weakNagaoka_spinMultiplet N t U hJ hU (pfFerroState N ξ)
      ((hermitianMinEigenvalue (tasakiEffMatrixUp_isHermitian N t U hJ hU) : ℝ) : ℂ)
      (hubbardEffectiveHamiltonian_mulVec_pfFerroState_of_eigen N t U htdiag ξ _ hξ_eig)
      (fermionTotalSpinPlus_mulVec_pfFerroState N ξ)
      (fermionTotalSpinZ_mulVec_pfFerroState N ξ)
      (pfFerroState_ne_zero N ξ hξ_ne)
    first | exact hLI | exact hdeg | exact hStot

end LatticeSystem.Fermion
