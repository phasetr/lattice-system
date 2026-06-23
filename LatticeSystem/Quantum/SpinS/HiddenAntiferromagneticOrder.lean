import LatticeSystem.Quantum.SpinS.HaldaneConjecture
import LatticeSystem.Quantum.SpinS.AndersonTower
import LatticeSystem.Quantum.SpinS.MultiSiteDot
import LatticeSystem.Quantum.SpinS.SubmatrixMinEigenvalue
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueEigenvector
import LatticeSystem.Quantum.SpinS.HermitianVariationalLowerBound
import LatticeSystem.Quantum.SpinS.HermitianVariationalUpperBound
import LatticeSystem.Math.HermitianMaxEigenvalue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Tasaki §6.3: hidden antiferromagnetic order and the `S = 1` chain on `H_HAF` (Proposition 6.5)

The semi-classical "kink" picture of the `S = 1` antiferromagnetic Heisenberg chain views the
ground state as a sea of Néel order (`+, −, +, −, …`) into which an arbitrary number of `0`-spins
are inserted, while the nonzero spins keep their complete alternating order (eq. (6.3.9)).  The
states realizing this picture span a **highly artificial subspace** `H_HAF` (the Hilbert space with
hidden antiferromagnetic order), on which the kink dynamics destroys the Néel long-range order.

For the spin-`1` chain (`N = 2`), a basis configuration `σ : Fin L → Fin 3` encodes the local spin
via `Ŝ_x^{(3)} = 1 − (σ_x).val`, i.e. `σ_x = 0 ↦ +1`, `σ_x = 1 ↦ 0`, `σ_x = 2 ↦ −1`.  A
configuration has **complete hidden antiferromagnetic order** (`IsHiddenAFMConfig`) when, deleting
the `0`-spins (`σ_x = 1`), the surviving `±`-spins (`σ_x ∈ {0, 2}`) strictly alternate
`+, −, +, −, …` around the ring.  `H_HAF` is the span of those basis states; the chain "defined on
`H_HAF`" is the compressed Hamiltonian `P_HAF Ĥ P_HAF`.

**Proposition 6.5**: the `S = 1` antiferromagnetic Heisenberg chain restricted to `H_HAF` has a
unique ground state, a finite energy gap, and an exponentially decaying correlation function — so
the Haldane "conjecture" for `S = 1` is rigorously justified *within this artificial restricted
Hilbert space*.

This was proved (Gómez-Santos' variational picture, via a path-integral / two-dimensional classical
statistical-mechanics representation); following the project policy it is recorded as a documented
axiom.  The `H_HAF` subspace, its projection, and the compressed Hamiltonian are *defined* here.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.3, Proposition 6.5, eqs. (6.3.7)–(6.3.9), pp. 168–170; A. Gómez-Santos, Phys. Rev. Lett.
**63**, 790 (1989).
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

/-- `IsPM σ x`: site `x` carries a nonzero (`±`) spin, i.e. `σ_x ≠ 1` (so `σ_x ∈ {0, 2}`, spin
`±1`). -/
def IsPM {L : ℕ} (σ : Fin L → Fin 3) (x : Fin L) : Prop := σ x ≠ 1

/-- `InCyclicOpen x y z`: the site `z` lies strictly between `x` and `y` along the ring `Fin L`,
going in the increasing-index (cyclic) direction from `x` to `y` (the open arc). -/
def InCyclicOpen {L : ℕ} (x y z : Fin L) : Prop :=
  if x.val < y.val then x.val < z.val ∧ z.val < y.val else x.val < z.val ∨ z.val < y.val

/-- `IsNextPM σ x y`: `y` is the **next** `±`-spin site after `x` around the ring — both `x`, `y`
carry `±` spins, and every site strictly between them (cyclically) is a `0`-spin (`σ_z = 1`). -/
def IsNextPM {L : ℕ} (σ : Fin L → Fin 3) (x y : Fin L) : Prop :=
  x ≠ y ∧ IsPM σ x ∧ IsPM σ y ∧ ∀ z, InCyclicOpen x y z → σ z = 1

/-- **Complete hidden antiferromagnetic order** (eq. (6.3.9)): every pair of *consecutive* `±`-spin
sites carries opposite signs, so the nonzero spins strictly alternate `+, −, +, −, …` around the
ring (with arbitrary `0`-spins inserted between).  Configurations with `0` or `1` nonzero spins
satisfy this vacuously. -/
def IsHiddenAFMConfig {L : ℕ} (σ : Fin L → Fin 3) : Prop :=
  ∀ x y, IsNextPM σ x y → σ x ≠ σ y

/-- The **hidden-antiferromagnetic-order projection** `P_HAF`: the orthogonal projection of the
spin-1 chain onto `H_HAF`, the diagonal operator with entry `1` on hidden-AFM configurations and `0`
otherwise (the computational basis is orthonormal). -/
noncomputable def hhafProjection (L : ℕ) : ManyBodyOpS (Fin L) 2 := by
  classical
  exact Matrix.diagonal (fun σ => if IsHiddenAFMConfig σ then (1 : ℂ) else 0)

/-- The **`S = 1` chain restricted to `H_HAF`**: the compressed Hamiltonian `P_HAF Ĥ P_HAF`, where
`Ĥ = afmHeisenbergChainHamiltonianS L 2` is the spin-1 antiferromagnetic Heisenberg ring. -/
noncomputable def hhafRestrictedChainHamiltonianS (L : ℕ) : ManyBodyOpS (Fin L) 2 :=
  hhafProjection L * afmHeisenbergChainHamiltonianS L 2 * hhafProjection L

/-- The **`H_HAF`-restricted real spectrum**: real eigenvalues of the compressed Hamiltonian whose
eigenvectors lie in `H_HAF` (i.e. are fixed by the projection `P_HAF`).  This isolates the genuine
spectrum of the restricted chain from the zeros from the orthogonal complement of `H_HAF`. -/
def hhafRealSpectrum (L : ℕ) : Set ℝ :=
  {E : ℝ | ∃ Φ : (Fin L → Fin 3) → ℂ, Φ ≠ 0 ∧ (hhafProjection L).mulVec Φ = Φ ∧
    (hhafRestrictedChainHamiltonianS L).mulVec Φ = (E : ℂ) • Φ}

/-- The **ring distance** between sites `x, y` on `Fin L`: the shorter of the two cyclic arc lengths
`(y − x) mod L` and `(x − y) mod L`. -/
def ringDist (L : ℕ) (x y : Fin L) : ℕ :=
  min ((y.val + L - x.val) % L) ((x.val + L - y.val) % L)

/-- The **normalized two-point correlation** `⟨Φ, Ŝ_x · Ŝ_y Φ⟩ / ⟨Φ, Φ⟩` of the spin-1 chain (real
part; `Ŝ_x · Ŝ_y` is Hermitian). -/
noncomputable def chainCorrelation (L : ℕ) (Φ : (Fin L → Fin 3) → ℂ) (x y : Fin L) : ℝ :=
  expectationRatioRe (spinSDot x y 2) Φ

/-! ## Spectral foundations of the `H_HAF`-restricted chain

Structural properties of the hidden-AFM projection and the compressed Hamiltonian that underlie
Proposition 6.5: the projection is a Hermitian idempotent, and the compressed Hamiltonian
`P_HAF Ĥ P_HAF` is Hermitian. -/

/-- The hidden-AFM projection `P_HAF` is Hermitian: it is diagonal with real `0`/`1` entries. -/
theorem hhafProjection_isHermitian (L : ℕ) : (hhafProjection L).IsHermitian := by
  classical
  rw [hhafProjection, Matrix.isHermitian_diagonal_iff]
  intro σ
  by_cases h : IsHiddenAFMConfig σ <;> simp [h]

/-- The hidden-AFM projection `P_HAF` is idempotent: `P_HAF² = P_HAF` (entries are `0` or `1`). -/
theorem hhafProjection_mul_self (L : ℕ) :
    hhafProjection L * hhafProjection L = hhafProjection L := by
  classical
  rw [hhafProjection, Matrix.diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal ?_
  funext σ
  by_cases h : IsHiddenAFMConfig σ <;> simp [h]

/-- The antiferromagnetic Heisenberg ring Hamiltonian is Hermitian (the ring coupling is real). -/
theorem afmHeisenbergChainHamiltonianS_isHermitian (L N : ℕ) :
    (afmHeisenbergChainHamiltonianS L N).IsHermitian := by
  rw [afmHeisenbergChainHamiltonianS]
  refine heisenbergHamiltonianS_isHermitian_of_real (fun x y => ?_) N
  rw [ringCoupling]
  split <;> simp

/-- The `H_HAF`-restricted (compressed) Hamiltonian `P_HAF Ĥ P_HAF` is Hermitian. -/
theorem hhafRestrictedChainHamiltonianS_isHermitian (L : ℕ) :
    (hhafRestrictedChainHamiltonianS L).IsHermitian := by
  rw [hhafRestrictedChainHamiltonianS]
  have hP := (hhafProjection_isHermitian L).eq
  have h := Matrix.isHermitian_conjTranspose_mul_mul
    (A := afmHeisenbergChainHamiltonianS L 2) (hhafProjection L)
    (afmHeisenbergChainHamiltonianS_isHermitian L 2)
  rwa [hP] at h

/-! ## Ground-energy existence on `H_HAF`

The compressed chain restricted to the hidden-AFM configuration subtype is a finite Hermitian
matrix, so it has a minimal eigenvalue; its eigenvector embeds (by zero-extension) back to a genuine
`H_HAF`-restricted ground state. This discharges the ground-energy existence/minimality part of
Proposition 6.5. -/

/-- Complete hidden-AFM order is decidable: it is a finite conjunction/implication of decidable
atoms over the finite ring. -/
instance hhafIsHiddenAFMConfig_decidable {L : ℕ} (σ : Fin L → Fin 3) :
    Decidable (IsHiddenAFMConfig σ) := by
  unfold IsHiddenAFMConfig IsNextPM IsPM InCyclicOpen
  infer_instance

/-- The index type of **hidden-AFM configurations**: spin-1 configurations with complete hidden
antiferromagnetic order. -/
def hhafConfig (L : ℕ) := {σ : Fin L → Fin 3 // IsHiddenAFMConfig σ}

instance hhafConfig_fintype (L : ℕ) : Fintype (hhafConfig L) :=
  Subtype.fintype _

instance hhafConfig_decidableEq (L : ℕ) : DecidableEq (hhafConfig L) :=
  inferInstanceAs (DecidableEq {σ : Fin L → Fin 3 // IsHiddenAFMConfig σ})

/-- The all-`0`-spin configuration (`σ ≡ 1`, every site spin `0`) has no `±` spins, so it is
vacuously hidden-AFM; hence the hidden-AFM configuration type is nonempty. -/
instance hhafConfig_nonempty (L : ℕ) : Nonempty (hhafConfig L) :=
  ⟨⟨fun _ => 1, fun _ _ h => (h.2.1 rfl).elim⟩⟩

/-- The **compressed Hamiltonian restricted to the hidden-AFM configuration subtype**: the
`H_HAF × H_HAF` submatrix of the AFM Heisenberg ring Hamiltonian. -/
noncomputable def hhafRestrictedMatrix (L : ℕ) : Matrix (hhafConfig L) (hhafConfig L) ℂ :=
  (afmHeisenbergChainHamiltonianS L 2).submatrix Subtype.val Subtype.val

/-- The restricted matrix is Hermitian (submatrix of a Hermitian matrix). -/
theorem hhafRestrictedMatrix_isHermitian (L : ℕ) : (hhafRestrictedMatrix L).IsHermitian :=
  (afmHeisenbergChainHamiltonianS_isHermitian L 2).submatrix Subtype.val

/-- **Zero-extension embedding** of an `H_HAF`-supported vector into the full spin-1 Hilbert space:
`v` on hidden-AFM configurations, `0` elsewhere. -/
noncomputable def hhafSubspaceEmbedding (L : ℕ) (v : hhafConfig L → ℂ) :
    (Fin L → Fin 3) → ℂ :=
  fun σ => if h : IsHiddenAFMConfig σ then v ⟨σ, h⟩ else 0

/-- The embedding evaluated on a hidden-AFM configuration. -/
theorem hhafSubspaceEmbedding_apply_subtype (L : ℕ) (v : hhafConfig L → ℂ) (σ : hhafConfig L) :
    hhafSubspaceEmbedding L v σ.1 = v σ := by
  obtain ⟨s, hs⟩ := σ
  simp only [hhafSubspaceEmbedding, dif_pos hs]

/-- The embedding vanishes off the hidden-AFM subspace. -/
theorem hhafSubspaceEmbedding_apply_of_not (L : ℕ) (v : hhafConfig L → ℂ) {σ : Fin L → Fin 3}
    (hσ : ¬ IsHiddenAFMConfig σ) : hhafSubspaceEmbedding L v σ = 0 := by
  rw [hhafSubspaceEmbedding, dif_neg hσ]

/-- The projection `P_HAF` fixes any embedded `H_HAF` vector. -/
theorem hhafProjection_mulVec_hhafSubspaceEmbedding (L : ℕ) (v : hhafConfig L → ℂ) :
    (hhafProjection L).mulVec (hhafSubspaceEmbedding L v) = hhafSubspaceEmbedding L v := by
  funext σ
  rw [hhafProjection, Matrix.mulVec_diagonal]
  by_cases h : IsHiddenAFMConfig σ
  · rw [if_pos h, one_mul]
  · rw [if_neg h, zero_mul, hhafSubspaceEmbedding_apply_of_not L v h]

/-- A nonzero `H_HAF` vector embeds to a nonzero full-space vector. -/
theorem hhafSubspaceEmbedding_ne_zero (L : ℕ) {v : hhafConfig L → ℂ} (hv : v ≠ 0) :
    hhafSubspaceEmbedding L v ≠ 0 := by
  intro h0
  apply hv
  funext σ
  have := congrFun h0 σ.1
  rwa [hhafSubspaceEmbedding_apply_subtype, Pi.zero_apply] at this

/-- **Compression–embedding intertwining**: the compressed Hamiltonian acting on an embedded
`H_HAF` vector equals the embedding of the restricted matrix acting on that vector.  The inner
projection fixes the embedding, and the outer projection picks out exactly the `H_HAF × H_HAF`
block of the ring Hamiltonian. -/
theorem hhafRestrictedChainHamiltonianS_mulVec_hhafSubspaceEmbedding (L : ℕ)
    (v : hhafConfig L → ℂ) :
    (hhafRestrictedChainHamiltonianS L).mulVec (hhafSubspaceEmbedding L v) =
      hhafSubspaceEmbedding L ((hhafRestrictedMatrix L).mulVec v) := by
  classical
  rw [hhafRestrictedChainHamiltonianS, ← Matrix.mulVec_mulVec,
    hhafProjection_mulVec_hhafSubspaceEmbedding, ← Matrix.mulVec_mulVec]
  funext σ
  rw [hhafProjection, Matrix.mulVec_diagonal]
  by_cases hσ : IsHiddenAFMConfig σ
  · rw [if_pos hσ, one_mul, hhafSubspaceEmbedding, dif_pos hσ]
    -- Reduce the RHS subtype sum to `∑ τ', H σ τ'.1 * emb v τ'.1`.
    have hRHS : ((hhafRestrictedMatrix L).mulVec v) ⟨σ, hσ⟩ =
        ∑ τ' : hhafConfig L,
          (afmHeisenbergChainHamiltonianS L 2) σ τ'.1 * hhafSubspaceEmbedding L v τ'.1 := by
      change ∑ τ' : hhafConfig L, (hhafRestrictedMatrix L) ⟨σ, hσ⟩ τ' * v τ' = _
      refine Finset.sum_congr rfl (fun τ' _ => ?_)
      rw [hhafRestrictedMatrix, Matrix.submatrix_apply, hhafSubspaceEmbedding_apply_subtype]
    rw [hRHS]
    -- LHS full sum reduces to the same subtype sum (the embedding vanishes off `H_HAF`).
    change ∑ τ, (afmHeisenbergChainHamiltonianS L 2) σ τ * hhafSubspaceEmbedding L v τ = _
    rw [← Finset.sum_filter_of_ne (p := fun τ => IsHiddenAFMConfig τ)
      (fun τ _ hne => by
        by_contra h
        exact hne (by rw [hhafSubspaceEmbedding_apply_of_not L v h, mul_zero]))]
    exact Finset.sum_subtype
      (Finset.univ.filter (fun τ : Fin L → Fin 3 => IsHiddenAFMConfig τ))
      (fun τ => by simp [Finset.mem_filter])
      (fun τ => (afmHeisenbergChainHamiltonianS L 2) σ τ * hhafSubspaceEmbedding L v τ)
  · rw [if_neg hσ, zero_mul, hhafSubspaceEmbedding_apply_of_not L _ hσ]

/-- The zero-extension embedding is scalar-linear. -/
theorem hhafSubspaceEmbedding_smul (L : ℕ) (c : ℂ) (v : hhafConfig L → ℂ) :
    hhafSubspaceEmbedding L (c • v) = c • hhafSubspaceEmbedding L v := by
  funext σ
  rw [hhafSubspaceEmbedding, Pi.smul_apply, hhafSubspaceEmbedding]
  by_cases h : IsHiddenAFMConfig σ
  · rw [dif_pos h, dif_pos h, Pi.smul_apply]
  · rw [dif_neg h, dif_neg h, smul_zero]

/-- The **candidate `H_HAF` ground energy**: the minimal eigenvalue of the restricted matrix. -/
noncomputable def hhafMinEnergy (L : ℕ) : ℝ :=
  hermitianMinEigenvalue (hhafRestrictedMatrix_isHermitian L)

/-- **The candidate ground energy is a genuine `H_HAF`-restricted eigenvalue** (with a nonzero
ground state in `H_HAF`): the minimal eigenvalue of the restricted matrix lifts via zero-extension
to a member of `hhafRealSpectrum`. -/
theorem hhafMinEnergy_mem_realSpectrum (L : ℕ) : hhafMinEnergy L ∈ hhafRealSpectrum L := by
  obtain ⟨w, hw_ne, hw_eig⟩ :=
    exists_nonzero_eigenvector_hermitianMinEigenvalue (hhafRestrictedMatrix_isHermitian L)
  refine ⟨hhafSubspaceEmbedding L w, hhafSubspaceEmbedding_ne_zero L hw_ne,
    hhafProjection_mulVec_hhafSubspaceEmbedding L w, ?_⟩
  rw [hhafRestrictedChainHamiltonianS_mulVec_hhafSubspaceEmbedding, hw_eig,
    hhafSubspaceEmbedding_smul, hhafMinEnergy]

/-- **Every eigenvalue of the restricted matrix is a genuine `H_HAF`-restricted eigenvalue**: the
`i`-th eigenvector of `hhafRestrictedMatrix` embeds via zero-extension to an `H_HAF` eigenvector of
the compressed Hamiltonian at the same eigenvalue. -/
theorem hhafRestrictedMatrix_eigenvalue_mem_realSpectrum (L : ℕ) (i : hhafConfig L) :
    (hhafRestrictedMatrix_isHermitian L).eigenvalues i ∈ hhafRealSpectrum L := by
  set hM := hhafRestrictedMatrix_isHermitian L with hMdef
  have hne : ((hM.eigenvectorBasis i).ofLp : hhafConfig L → ℂ) ≠ 0 := by
    intro h0
    have h1 := eigenvectorBasis_dotProduct_self_eq_one hM i
    rw [h0] at h1
    simp at h1
  have heig : (hhafRestrictedMatrix L).mulVec ((hM.eigenvectorBasis i).ofLp) =
      ((hM.eigenvalues i : ℝ) : ℂ) • ((hM.eigenvectorBasis i).ofLp) := by
    have h := Matrix.IsHermitian.mulVec_eigenvectorBasis hM i
    convert h using 2
  refine ⟨hhafSubspaceEmbedding L ((hM.eigenvectorBasis i).ofLp),
    hhafSubspaceEmbedding_ne_zero L hne,
    hhafProjection_mulVec_hhafSubspaceEmbedding L _, ?_⟩
  rw [hhafRestrictedChainHamiltonianS_mulVec_hhafSubspaceEmbedding, heig,
    hhafSubspaceEmbedding_smul]

/-- The **maximal `H_HAF`-restricted energy**: the maximal eigenvalue of the restricted matrix. -/
noncomputable def hhafMaxEnergy (L : ℕ) : ℝ :=
  LatticeSystem.Math.hermitianMaxEigenvalue (hhafRestrictedMatrix_isHermitian L)

/-- The maximal restricted eigenvalue is a genuine `H_HAF`-restricted eigenvalue. -/
theorem hhafMaxEnergy_mem_realSpectrum (L : ℕ) : hhafMaxEnergy L ∈ hhafRealSpectrum L := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp
    (LatticeSystem.Math.hermitian_max_eigenvalue_mem_image (hhafRestrictedMatrix_isHermitian L))
  rw [hhafMaxEnergy, ← hi]
  exact hhafRestrictedMatrix_eigenvalue_mem_realSpectrum L i

/-- **The `H_HAF`-restricted spectrum has a least element**, realized by `hhafMinEnergy`: the
minimal restricted eigenvalue is `≤` every `hhafRealSpectrum` element.  This discharges the
ground-energy existence *and minimality* part of Proposition 6.5: there is a genuine `H_HAF` ground
energy `E = hhafMinEnergy L` with a nonzero ground state. -/
theorem exists_hhaf_min_real_eigenvalue (L : ℕ) :
    ∃ E ∈ hhafRealSpectrum L, ∀ E' ∈ hhafRealSpectrum L, E ≤ E' := by
  refine ⟨hhafMinEnergy L, hhafMinEnergy_mem_realSpectrum L, ?_⟩
  rintro E' ⟨Φ, hΦ_ne, hΦ_proj, hΦ_eig⟩
  -- `Φ` is supported on `H_HAF`, so it is the embedding of its restriction `u`.
  set u : hhafConfig L → ℂ := fun τ => Φ τ.1 with hu_def
  have hΦ_emb : Φ = hhafSubspaceEmbedding L u := by
    funext σ
    by_cases hσ : IsHiddenAFMConfig σ
    · rw [hhafSubspaceEmbedding, dif_pos hσ]
    · rw [hhafSubspaceEmbedding, dif_neg hσ]
      have hp := congrFun hΦ_proj σ
      rw [hhafProjection, Matrix.mulVec_diagonal, if_neg hσ, zero_mul] at hp
      exact hp.symm
  -- The restriction `u` is an eigenvector of the restricted matrix at `E'`.
  have hu_eig : (hhafRestrictedMatrix L).mulVec u = (E' : ℂ) • u := by
    have h1 : hhafSubspaceEmbedding L ((hhafRestrictedMatrix L).mulVec u) =
        hhafSubspaceEmbedding L ((E' : ℂ) • u) := by
      rw [← hhafRestrictedChainHamiltonianS_mulVec_hhafSubspaceEmbedding, ← hΦ_emb, hΦ_eig,
        hhafSubspaceEmbedding_smul, hΦ_emb]
    funext τ
    have h2 := congrFun h1 τ.1
    rwa [hhafSubspaceEmbedding_apply_subtype, hhafSubspaceEmbedding_apply_subtype] at h2
  have hu_ne : u ≠ 0 := by
    intro h0
    apply hΦ_ne
    rw [hΦ_emb, h0]
    funext σ
    rw [hhafSubspaceEmbedding]
    split <;> rfl
  -- Rayleigh variational bound: `minEig · ‖u‖² ≤ rayleigh = E' · ‖u‖²`, and `‖u‖² > 0`.
  have hvar := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec
    (hhafRestrictedMatrix_isHermitian L) u
  have hray : rayleighOnVec (hhafRestrictedMatrix L) u =
      E' * (dotProduct (star u) u).re := by
    rw [rayleighOnVec, hu_eig, dotProduct_smul, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hDpos : 0 < (dotProduct (star u) u).re := by
    have hpos : (0 : ℂ) < dotProduct (star u) u := Matrix.dotProduct_star_self_pos_iff.mpr hu_ne
    simpa using (Complex.lt_def.mp hpos).1
  rw [hray] at hvar
  rw [hhafMinEnergy]
  exact le_of_mul_le_mul_right hvar hDpos

/-! ## The restricted spectrum is exactly the restricted-matrix eigenvalue set -/

/-- **Reverse bridge**: any `H_HAF`-restricted eigenvector restricts to an eigenvector of the
restricted matrix at the same eigenvalue.  (An `H_HAF` vector `Φ` fixed by `P_HAF` equals the
embedding of its restriction `u`, so the compression–embedding intertwining transfers the eigenvalue
equation back to `hhafRestrictedMatrix`.) -/
theorem hhafRealSpectrum_restrict (L : ℕ) {E' : ℝ} (hE' : E' ∈ hhafRealSpectrum L) :
    ∃ u : hhafConfig L → ℂ, u ≠ 0 ∧ (hhafRestrictedMatrix L).mulVec u = (E' : ℂ) • u := by
  obtain ⟨Φ, hΦ_ne, hΦ_proj, hΦ_eig⟩ := hE'
  set u : hhafConfig L → ℂ := fun τ => Φ τ.1 with hu_def
  have hΦ_emb : Φ = hhafSubspaceEmbedding L u := by
    funext σ
    by_cases hσ : IsHiddenAFMConfig σ
    · rw [hhafSubspaceEmbedding, dif_pos hσ]
    · rw [hhafSubspaceEmbedding, dif_neg hσ]
      have hp := congrFun hΦ_proj σ
      rw [hhafProjection, Matrix.mulVec_diagonal, if_neg hσ, zero_mul] at hp
      exact hp.symm
  have hu_eig : (hhafRestrictedMatrix L).mulVec u = (E' : ℂ) • u := by
    have h1 : hhafSubspaceEmbedding L ((hhafRestrictedMatrix L).mulVec u) =
        hhafSubspaceEmbedding L ((E' : ℂ) • u) := by
      rw [← hhafRestrictedChainHamiltonianS_mulVec_hhafSubspaceEmbedding, ← hΦ_emb, hΦ_eig,
        hhafSubspaceEmbedding_smul, hΦ_emb]
    funext τ
    have h2 := congrFun h1 τ.1
    rwa [hhafSubspaceEmbedding_apply_subtype, hhafSubspaceEmbedding_apply_subtype] at h2
  have hu_ne : u ≠ 0 := by
    intro h0
    apply hΦ_ne
    rw [hΦ_emb, h0]
    funext σ
    rw [hhafSubspaceEmbedding]
    split <;> rfl
  exact ⟨u, hu_ne, hu_eig⟩

/-- **Spectral completeness**: every element of `hhafRealSpectrum` is an eigenvalue of the
restricted matrix.  (Via the reverse bridge `E'` is a restricted-matrix eigenvalue, hence lies in
`spectrum ℝ`, which for a Hermitian matrix is the range of the eigenvalue function.) -/
theorem hhafRealSpectrum_subset_eigenvalue_range (L : ℕ) {E' : ℝ}
    (hE' : E' ∈ hhafRealSpectrum L) :
    ∃ i, (hhafRestrictedMatrix_isHermitian L).eigenvalues i = E' := by
  obtain ⟨u, hu_ne, hu_eig⟩ := hhafRealSpectrum_restrict L hE'
  have hmem : E' ∈ spectrum ℝ (hhafRestrictedMatrix L) := by
    rw [spectrum.mem_iff]
    intro hunit
    have hAu : (algebraMap ℝ (Matrix (hhafConfig L) (hhafConfig L) ℂ) E').mulVec u =
        (E' : ℂ) • u := by
      funext j
      rw [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul,
        Pi.algebraMap_apply, Complex.coe_algebraMap]
    have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hunit
    apply hu_ne
    apply hinj
    rw [Matrix.mulVec_zero, Matrix.sub_mulVec, hAu, hu_eig, sub_self]
  rw [(hhafRestrictedMatrix_isHermitian L).spectrum_real_eq_range_eigenvalues] at hmem
  exact hmem

/-- The `H_HAF`-restricted spectrum is **finite** (it is contained in the finite eigenvalue image of
the restricted matrix). -/
theorem hhafRealSpectrum_finite (L : ℕ) : (hhafRealSpectrum L).Finite := by
  apply Set.Finite.subset
    (Set.finite_range (hhafRestrictedMatrix_isHermitian L).eigenvalues)
  intro E' hE'
  obtain ⟨i, hi⟩ := hhafRealSpectrum_subset_eigenvalue_range L hE'
  exact ⟨i, hi⟩

/-! ## Diagonal bounds on the restricted ground/top energy -/

/-- The standard basis vector `e_σ : hhafConfig L → ℂ` (entry `1` at `σ`, `0` elsewhere). -/
private noncomputable def hhafBasis (L : ℕ) (σ : hhafConfig L) : hhafConfig L → ℂ :=
  fun τ => if τ = σ then 1 else 0

/-- The complex conjugate of the standard basis vector is itself. -/
private theorem hhaf_star_basis (L : ℕ) (σ : hhafConfig L) :
    star (hhafBasis L σ) = hhafBasis L σ := by
  funext τ
  simp only [Pi.star_apply, hhafBasis]
  split <;> simp

/-- The standard basis vector at `σ` has unit norm. -/
private theorem hhaf_basis_dotProduct_self (L : ℕ) (σ : hhafConfig L) :
    dotProduct (star (hhafBasis L σ)) (hhafBasis L σ) = 1 := by
  rw [hhaf_star_basis, dotProduct, Finset.sum_eq_single_of_mem σ (Finset.mem_univ σ)]
  · simp [hhafBasis]
  · intro j _ hj; simp [hhafBasis, hj]

/-- The action of the restricted matrix on the basis vector is the `σ`-th column. -/
private theorem hhaf_mulVec_basis (L : ℕ) (σ : hhafConfig L) :
    (hhafRestrictedMatrix L).mulVec (hhafBasis L σ) = fun j => (hhafRestrictedMatrix L) j σ := by
  funext j
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single_of_mem σ (Finset.mem_univ σ)]
  · simp [hhafBasis]
  · intro k _ hk; simp [hhafBasis, hk]

/-- The Rayleigh quotient of the restricted matrix at the basis vector `e_σ` is the diagonal entry
`(M σ σ).re`. -/
private theorem hhaf_rayleigh_basis_eq_diag (L : ℕ) (σ : hhafConfig L) :
    rayleighOnVec (hhafRestrictedMatrix L) (hhafBasis L σ) =
      ((hhafRestrictedMatrix L) σ σ).re := by
  unfold rayleighOnVec
  congr 1
  rw [hhaf_star_basis, hhaf_mulVec_basis, dotProduct,
    Finset.sum_eq_single_of_mem σ (Finset.mem_univ σ)]
  · simp [hhafBasis]
  · intro j _ hj; simp [hhafBasis, hj]

/-- **`hhafMinEnergy` is `≤` every diagonal entry** of the restricted matrix (Rayleigh at the basis
vector). -/
theorem hhafMinEnergy_le_diag (L : ℕ) (σ : hhafConfig L) :
    hhafMinEnergy L ≤ ((hhafRestrictedMatrix L) σ σ).re := by
  have h := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec
    (hhafRestrictedMatrix_isHermitian L) (hhafBasis L σ)
  rw [hhaf_basis_dotProduct_self, Complex.one_re, mul_one,
    hhaf_rayleigh_basis_eq_diag] at h
  exact h

/-- **Every diagonal entry is `≤ hhafMaxEnergy`** (Rayleigh at the basis vector). -/
theorem diag_le_hhafMaxEnergy (L : ℕ) (σ : hhafConfig L) :
    ((hhafRestrictedMatrix L) σ σ).re ≤ hhafMaxEnergy L := by
  have h := rayleighOnVec_le_hermitianMaxEigenvalue_mul_dotProduct_re
    (hhafRestrictedMatrix_isHermitian L) (hhafBasis L σ)
  rw [hhaf_basis_dotProduct_self, Complex.one_re, mul_one,
    hhaf_rayleigh_basis_eq_diag] at h
  exact h

/-! ## Concrete diagonal witnesses for non-scalarity -/

/-- The hidden-AFM configuration with every site carrying spin `0` (`σ_x = 1`). -/
def hhafAllZeroSpinConfig (L : ℕ) : hhafConfig L :=
  ⟨fun _ => 1, fun _ _ h => (h.2.1 rfl).elim⟩

/-- The raw domain-wall hidden-AFM configuration: site `0` carries `+1` (`σ = 0`), site `1`
carries `-1` (`σ = 2`), and every other site carries spin `0` (`σ = 1`).  For `L < 2` the
second special site is absent, but the same formula is still a valid vacuous hidden-AFM
configuration. -/
def hhafDomainWallRaw (L : ℕ) : Fin L → Fin 3 :=
  fun x => if x.val = 0 then 0 else if x.val = 1 then 2 else 1

/-- In the domain-wall configuration, a nonzero (`±`) spin can occur only at values `0` or `1`. -/
private theorem hhafDomainWallRaw_pm_val {L : ℕ} (x : Fin L)
    (hx : IsPM (hhafDomainWallRaw L) x) : x.val = 0 ∨ x.val = 1 := by
  by_cases hx0 : x.val = 0
  · exact Or.inl hx0
  · by_cases hx1 : x.val = 1
    · exact Or.inr hx1
    · exfalso
      exact hx (by simp [hhafDomainWallRaw, hx0, hx1])

/-- The domain-wall raw configuration has complete hidden antiferromagnetic order: the only possible
nonzero sites are `0` and `1`, and their spins are opposite. -/
theorem hhafDomainWallRaw_isHiddenAFMConfig (L : ℕ) :
    IsHiddenAFMConfig (hhafDomainWallRaw L) := by
  intro x y hxy
  rcases hxy with ⟨hxy_ne, hxpm, hypm, _⟩
  rcases hhafDomainWallRaw_pm_val x hxpm with hx0 | hx1
  · rcases hhafDomainWallRaw_pm_val y hypm with hy0 | hy1
    · exact (hxy_ne (Fin.ext (by omega))).elim
    · simp [hhafDomainWallRaw, hx0, hy1]
  · rcases hhafDomainWallRaw_pm_val y hypm with hy0 | hy1
    · simp [hhafDomainWallRaw, hx1, hy0]
    · exact (hxy_ne (Fin.ext (by omega))).elim

/-- The domain-wall hidden-AFM configuration used to witness a negative diagonal entry. -/
def hhafDomainWallConfig (L : ℕ) : hhafConfig L :=
  ⟨hhafDomainWallRaw L, hhafDomainWallRaw_isHiddenAFMConfig L⟩

/-- The directed ring coupling has no self-loop when `L ≥ 2`. -/
private theorem ringCoupling_self_eq_zero {L : ℕ} (hL : 2 ≤ L) (x : Fin L) :
    ringCoupling L x x = 0 := by
  rw [ringCoupling]
  apply if_neg
  intro h
  have hxlt : x.val < L := x.isLt
  by_cases hwrap : x.val + 1 < L
  · rw [Nat.mod_eq_of_lt hwrap] at h
    omega
  · have hxle : x.val + 1 ≤ L := by omega
    have hxadd : x.val + 1 = L := by omega
    rw [hxadd, Nat.mod_self] at h
    omega

/-- At the all-zero-spin hidden-AFM configuration, the restricted diagonal entry is `0`. -/
theorem hhafAllZeroSpin_diag_re_eq_zero (L : ℕ) (hL : 2 ≤ L) :
    ((hhafRestrictedMatrix L) (hhafAllZeroSpinConfig L) (hhafAllZeroSpinConfig L)).re = 0 := by
  rw [hhafRestrictedMatrix, Matrix.submatrix_apply, afmHeisenbergChainHamiltonianS,
    heisenbergHamiltonianS_apply_diag]
  change (∑ x : Fin L, ∑ y : Fin L,
    ringCoupling L x y *
      (if x = y then (2 : ℂ) * (2 + 2) / 4
       else ((2 : ℂ) / 2 - ((hhafAllZeroSpinConfig L).1 x).val) *
        ((2 : ℂ) / 2 - ((hhafAllZeroSpinConfig L).1 y).val))).re = 0
  have hsum : (∑ x : Fin L, ∑ y : Fin L,
      ringCoupling L x y *
        (if x = y then (2 : ℂ) * (2 + 2) / 4
         else ((2 : ℂ) / 2 - ((hhafAllZeroSpinConfig L).1 x).val) *
          ((2 : ℂ) / 2 - ((hhafAllZeroSpinConfig L).1 y).val))) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    refine Finset.sum_eq_zero fun y _ => ?_
    by_cases hxy : x = y
    · subst y
      rw [if_pos rfl, ringCoupling_self_eq_zero hL x]
      simp
    · rw [if_neg hxy]
      simp [hhafAllZeroSpinConfig]
  rw [hsum]
  rfl

/-- The successor index value `(x+1) mod L`: it is `0` at the last site, `x+1` otherwise. -/
private theorem hhaf_succ_val {L : ℕ} (_hL : 2 ≤ L) (x : Fin L) :
    (x.val + 1) % L = if x.val + 1 = L then 0 else x.val + 1 := by
  by_cases h : x.val + 1 = L
  · rw [if_pos h, h, Nat.mod_self]
  · rw [Nat.mod_eq_of_lt (by have := x.isLt; omega), if_neg h]

/-- **General restricted-diagonal formula**: for `L ≥ 2`, the diagonal entry collapses (over the
directed ring bond `x → x+1`) to `∑_x (1 - σ_x)(1 - σ_{x+1})`. -/
private theorem hhaf_diag_eq_succ_sum (L : ℕ) (hL : 2 ≤ L) (σ : hhafConfig L) :
    (hhafRestrictedMatrix L) σ σ =
      ∑ x : Fin L, ((1 : ℂ) - ((σ.1 x).val : ℂ)) *
        (1 - ((σ.1 ⟨(x.val + 1) % L, Nat.mod_lt _ (by omega)⟩).val : ℂ)) := by
  rw [hhafRestrictedMatrix, Matrix.submatrix_apply, afmHeisenbergChainHamiltonianS,
    heisenbergHamiltonianS_apply_diag]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single (⟨(x.val + 1) % L, Nat.mod_lt _ (by omega)⟩ : Fin L)]
  · have hne : x ≠ (⟨(x.val + 1) % L, Nat.mod_lt _ (by omega)⟩ : Fin L) := by
      intro h
      have hv := congrArg Fin.val h
      have hxlt := x.isLt
      have hsv := hhaf_succ_val hL x
      simp only [hsv] at hv
      split_ifs at hv with hc <;> omega
    rw [if_neg hne]
    have hcoup : ringCoupling L x ⟨(x.val + 1) % L, Nat.mod_lt _ (by omega)⟩ = 1 := by
      rw [ringCoupling, if_pos rfl]
    rw [hcoup, one_mul]
    norm_num
  · intro y _ hy
    have hcoup0 : ringCoupling L x y = 0 := by
      rw [ringCoupling, if_neg]
      intro h
      exact hy (Fin.ext h)
    rw [hcoup0, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- The `1 - σ` weight of the domain-wall configuration at index value `n`: `1` at `0`, `-1` at `1`,
`0` elsewhere. -/
private def dwWeight (n : ℕ) : ℝ := if n = 0 then 1 else if n = 1 then -1 else 0

private theorem dwWeight_zero : dwWeight 0 = 1 := rfl

private theorem dwWeight_one : dwWeight 1 = -1 := rfl

private theorem dwWeight_ge_two {n : ℕ} (h : 2 ≤ n) : dwWeight n = 0 := by
  unfold dwWeight; rw [if_neg (by omega), if_neg (by omega)]

private theorem dwWeight_eq (L : ℕ) (x : Fin L) :
    (1 - ((hhafDomainWallConfig L).1 x).val : ℝ) = dwWeight x.val := by
  change (1 - ((hhafDomainWallRaw L x).val : ℝ)) = dwWeight x.val
  unfold hhafDomainWallRaw dwWeight
  split_ifs <;> norm_num

private theorem dwWeight_mul_succ_nonpos (L : ℕ) (hL : 2 ≤ L) (x : Fin L) :
    dwWeight x.val * dwWeight ((x.val + 1) % L) ≤ 0 := by
  have hxlt := x.isLt
  rw [hhaf_succ_val hL x]
  by_cases h0 : x.val = 0
  · -- weight 1 at x; successor value 1 (L ≥ 2): weight -1, product -1 ≤ 0
    rw [h0, if_neg (by omega : (0 : ℕ) + 1 ≠ L), dwWeight_zero]
    norm_num [dwWeight_one]
  · by_cases h1 : x.val = 1
    · rw [h1]
      by_cases hL2 : (1 : ℕ) + 1 = L
      · rw [if_pos hL2, dwWeight_one, dwWeight_zero]; norm_num
      · rw [if_neg hL2, dwWeight_one, dwWeight_ge_two (by omega)]; norm_num
    · -- weight 0 at x ⟹ product 0
      rw [dwWeight_ge_two (by omega : 2 ≤ x.val)]; norm_num

/-- The domain-wall hidden-AFM configuration has a strictly negative restricted diagonal entry for
every `L ≥ 2`: the bond `0 → 1` contributes `-1` and every other bond contributes `≤ 0`. -/
theorem hhafDomainWall_diag_re_neg (L : ℕ) (hL : 2 ≤ L) :
    ((hhafRestrictedMatrix L) (hhafDomainWallConfig L) (hhafDomainWallConfig L)).re < 0 := by
  rw [hhaf_diag_eq_succ_sum L hL, Complex.re_sum]
  have hterm : ∀ x : Fin L,
      (((1 : ℂ) - ((hhafDomainWallConfig L).1 x).val) *
        (1 - ((hhafDomainWallConfig L).1
          ⟨(x.val + 1) % L, Nat.mod_lt _ (by omega)⟩).val)).re =
      dwWeight x.val * dwWeight ((x.val + 1) % L) := by
    intro x
    rw [← dwWeight_eq L x, ← dwWeight_eq L ⟨(x.val + 1) % L, Nat.mod_lt _ (by omega)⟩]
    simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  simp_rw [hterm]
  have hlt : (∑ x : Fin L, dwWeight x.val * dwWeight ((x.val + 1) % L)) <
      ∑ _x : Fin L, (0 : ℝ) := by
    refine Finset.sum_lt_sum (fun x _ => dwWeight_mul_succ_nonpos L hL x) ?_
    refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
    have h1 : ((⟨0, by omega⟩ : Fin L).val + 1) % L = 1 := by
      change (0 + 1) % L = 1
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [show (⟨0, by omega⟩ : Fin L).val = 0 from rfl, h1, dwWeight_zero, dwWeight_one]
    norm_num
  simpa using hlt

/-- **Non-scalarity of the hidden-AFM restricted Hamiltonian**: for every even ring with `L ≥ 2`,
the variational lower and upper diagonal witnesses force the minimal restricted energy to be
strictly below the maximal restricted energy. -/
theorem hhafMinEnergy_lt_hhafMaxEnergy (L : ℕ) (_hLeven : Even L) (hL : 2 ≤ L) :
    hhafMinEnergy L < hhafMaxEnergy L := by
  calc
    hhafMinEnergy L ≤
        ((hhafRestrictedMatrix L) (hhafDomainWallConfig L) (hhafDomainWallConfig L)).re :=
      hhafMinEnergy_le_diag L (hhafDomainWallConfig L)
    _ < 0 := hhafDomainWall_diag_re_neg L hL
    _ = ((hhafRestrictedMatrix L) (hhafAllZeroSpinConfig L) (hhafAllZeroSpinConfig L)).re := by
      rw [hhafAllZeroSpin_diag_re_eq_zero L hL]
    _ ≤ hhafMaxEnergy L := diag_le_hhafMaxEnergy L (hhafAllZeroSpinConfig L)

/-! ## Per-`L` exponential decay of the correlation -/

/-- **Finite exponential-decay envelope**: any real-valued two-index family `f` on a finite ring
admits an exponential-decay bound `|f x y| ≤ C e^{−d(x,y)/ξ}`.  On a fixed finite ring the values
are a finite family, so `ξ = 1` and `C = Σ_{x',y'} |f x' y'| e^{d(x',y')}` make the envelope hold
termwise.  (Stated abstractly over `f` so the heavy `chainCorrelation` operator is never
unfolded.) -/
theorem exp_decay_envelope_of_finite {L : ℕ} (f : Fin L → Fin L → ℝ) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x y : Fin L, |f x y| ≤ C * Real.exp (-(ringDist L x y : ℝ) / ξ) := by
  classical
  set C : ℝ := ∑ p : Fin L × Fin L, |f p.1 p.2| * Real.exp (ringDist L p.1 p.2) with hC
  refine ⟨1, one_pos, C, ?_, ?_⟩
  · exact Finset.sum_nonneg fun p _ => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)
  · intro x y
    have hterm : |f x y| * Real.exp (ringDist L x y) ≤ C :=
      Finset.single_le_sum (f := fun p : Fin L × Fin L =>
          |f p.1 p.2| * Real.exp (ringDist L p.1 p.2))
        (fun p _ => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)) (Finset.mem_univ (x, y))
    calc |f x y|
        = (|f x y| * Real.exp (ringDist L x y)) * Real.exp (-(ringDist L x y : ℝ)) := by
          rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ C * Real.exp (-(ringDist L x y : ℝ)) :=
          mul_le_mul_of_nonneg_right hterm (Real.exp_nonneg _)
      _ = C * Real.exp (-(ringDist L x y : ℝ) / 1) := by rw [div_one]

/-- **Exponential-decay envelope (per `L`)** for the spin-1 chain: for *any* state `Φ` on the finite
ring, the two-point correlation `chainCorrelation` admits `|⟨Ŝ_x·Ŝ_y⟩| ≤ C e^{−d(x,y)/ξ}`.  This
supplies the correlation-decay clause of Proposition 6.5 for the (still axiomatic) ground state. -/
theorem hhaf_correlation_exp_decay_exists (L : ℕ) (Φ : (Fin L → Fin 3) → ℂ) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x y : Fin L, |chainCorrelation L Φ x y| ≤
        C * Real.exp (-(ringDist L x y : ℝ) / ξ) :=
  exp_decay_envelope_of_finite (fun x y => chainCorrelation L Φ x y)

/-- **Tasaki Proposition 6.5 (the `S = 1` chain on `H_HAF`), AXIOM.**  For an even ring `Fin L`
(`L > 0`), the spin-`1` antiferromagnetic Heisenberg chain restricted to the
hidden-antiferromagnetic subspace `H_HAF` (the compressed Hamiltonian
`hhafRestrictedChainHamiltonianS`) has:

* a **unique ground state** `Φ ∈ H_HAF` (a nonzero `H_HAF`-eigenvector at the minimal
  `H_HAF`-energy `E`, with every `H_HAF` ground eigenvector a scalar multiple of `Φ`);
* a **finite energy gap** `gap > 0` (a positive gap in the `H_HAF`-restricted spectrum: the first
  excited `H_HAF`-energy `E₁` satisfies `gap = E₁ − E > 0`, with `E₁` minimal above `E`);
* an **exponentially decaying correlation function**:
  `|⟨Φ, Ŝ_x · Ŝ_y Φ⟩ / ⟨Φ, Φ⟩| ≤ C e^{−d(x,y)/ξ}` for some `ξ > 0`, `C ≥ 0`, where `d(x,y)` is the
  ring distance.

Thus the Haldane conjecture for `S = 1` (unique gapped disordered ground state) holds *rigorously
within the artificial restricted Hilbert space* `H_HAF`.  Recorded as a documented axiom. -/
axiom tasaki_prop_6_5_hhaf_spin_one (L : ℕ) (hL : Even L) (hLpos : 0 < L) :
    ∃ (E gap ξ C : ℝ) (Φ : (Fin L → Fin 3) → ℂ),
      (hhafProjection L).mulVec Φ = Φ ∧ Φ ≠ 0 ∧
      (hhafRestrictedChainHamiltonianS L).mulVec Φ = (E : ℂ) • Φ ∧
      (∀ E' ∈ hhafRealSpectrum L, E ≤ E') ∧
      (∀ Ψ : (Fin L → Fin 3) → ℂ, Ψ ≠ 0 → (hhafProjection L).mulVec Ψ = Ψ →
        (hhafRestrictedChainHamiltonianS L).mulVec Ψ = (E : ℂ) • Ψ → ∃ c : ℂ, Ψ = c • Φ) ∧
      0 < gap ∧ (∃ E₁ ∈ hhafRealSpectrum L, E < E₁ ∧ gap = E₁ - E ∧
        ∀ E' ∈ hhafRealSpectrum L, E < E' → E₁ ≤ E') ∧
      0 < ξ ∧ 0 ≤ C ∧
      ∀ x y : Fin L, |chainCorrelation L Φ x y| ≤ C * Real.exp (-(ringDist L x y : ℝ) / ξ)

end LatticeSystem.Quantum
