import LatticeSystem.Fermion.JordanWigner.Hubbard
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiHopActionCore
import LatticeSystem.Math.PosSemidef.Basics
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Spin-reflection foundation for Lieb's theorem (Tasaki §10.2.1)

This file builds the finite-dimensional **spin-reflection positivity (SRP)**
coefficient-matrix language in which Lieb's theorem for the attractive Hubbard
model (Tasaki Theorem 10.2, `theorem_10_2_lieb_attractive_unique_singlet`) is
proved.  It is the first layer (PR1) toward discharging that axiom; it does not
yet touch the Hamiltonian positivity, the Perron–Frobenius uniqueness, or the
singlet argument.

## Main definitions

* `hubbardSpinConfig N` — a single-species occupation configuration
  `Fin (N + 1) → Fin 2` on the `N + 1` sites.
* `hubbardUpConfig` / `hubbardDownConfig` / `hubbardMergeConfig` — the up/down
  projections of a spin-orbital configuration `Fin (2 * N + 2) → Fin 2` (via
  `spinfulIndex`) and their reconstruction.
* `hubbardSpinConfigEquiv` — the resulting bijection
  `(Fin (2 * N + 2) → Fin 2) ≃ hubbardSpinConfig N × hubbardSpinConfig N`
  (the basis-level form of the factorization `H = H↑ ⊗ H↓`).
* `hubbardSpinCoeffLinearEquiv` — the induced linear isomorphism of a state
  vector with its **coefficient matrix** indexed by `(up config, down config)`.
* `flipOccupation` / `particleHoleConfig` / `spinReflectionConfig` /
  `spinReflectionThetaVec` — the spin-reflection `θ` (antiunitary spin-flip ∘
  particle–hole) at the configuration and the state-vector level.
* `spinReflectionCoeff` / `SpinReflectionPositive` — the SRP coefficient matrix
  (down index read as a hole) and its positive-semidefiniteness predicate.

## Main results

* `particleHoleConfig_involutive`, `spinReflectionConfig_involutive` — the
  involutivity of the reflections.
* `spinReflectionThetaVec_smul`, `spinReflectionThetaVec_dotProduct` — `θ` is
  conjugate-linear and preserves the inner product up to conjugation
  (antiunitarity).
* `spinReflectionCoeff_thetaVec` — `θ` acts on the coefficient matrix as the
  conjugate transpose.
* `spinReflection_gramMatrix_nonneg` — the reusable nonnegativity
  `0 ≤ Re tr (C A C Aᴴ)` for `C` positive-semidefinite, the algebraic heart of
  spin-reflection positivity.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1, pp. 348–349; E. H. Lieb, *Phys. Rev. Lett.*
**62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Math
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-! ## Up/down configuration factorization -/

/-- A single-species occupation configuration on the `N + 1` sites. -/
abbrev hubbardSpinConfig (N : ℕ) : Type := Fin (N + 1) → Fin 2

/-- The up-spin part of a spin-orbital configuration `c`: site `i ↦ c (2 i)`. -/
def hubbardUpConfig (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) : hubbardSpinConfig N :=
  fun i => c (spinfulIndex N i 0)

/-- The down-spin part of a spin-orbital configuration `c`: site `i ↦ c (2 i + 1)`. -/
def hubbardDownConfig (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) : hubbardSpinConfig N :=
  fun i => c (spinfulIndex N i 1)

/-- Reconstruct a spin-orbital configuration from its up/down parts:
the orbital `o = 2 i + σ` receives `u i` if `σ = 0` (even) and `d i` if `σ = 1`. -/
def hubbardMergeConfig (N : ℕ) (u d : hubbardSpinConfig N) :
    Fin (2 * N + 2) → Fin 2 :=
  fun o =>
    if o.val % 2 = 0 then u ⟨o.val / 2, by have := o.isLt; omega⟩
    else d ⟨o.val / 2, by have := o.isLt; omega⟩

/-- Merging reads the up part on even orbitals: `merge u d (2 i) = u i`. -/
@[simp]
theorem hubbardMergeConfig_spinfulIndex_zero (N : ℕ) (u d : hubbardSpinConfig N)
    (i : Fin (N + 1)) : hubbardMergeConfig N u d (spinfulIndex N i 0) = u i := by
  have hval : (spinfulIndex N i 0).val = 2 * i.val := by simp [spinfulIndex]
  unfold hubbardMergeConfig
  rw [if_pos (by omega)]
  congr 1
  have hdiv : (spinfulIndex N i 0).val / 2 = i.val := by omega
  exact Fin.ext hdiv

/-- Merging reads the down part on odd orbitals: `merge u d (2 i + 1) = d i`. -/
@[simp]
theorem hubbardMergeConfig_spinfulIndex_one (N : ℕ) (u d : hubbardSpinConfig N)
    (i : Fin (N + 1)) : hubbardMergeConfig N u d (spinfulIndex N i 1) = d i := by
  have hval : (spinfulIndex N i 1).val = 2 * i.val + 1 := by simp [spinfulIndex]
  unfold hubbardMergeConfig
  rw [if_neg (by omega)]
  congr 1
  have hdiv : (spinfulIndex N i 1).val / 2 = i.val := by omega
  exact Fin.ext hdiv

/-- The up projection recovers the up part of a merge: `up (merge u d) = u`. -/
@[simp]
theorem hubbardUpConfig_merge (N : ℕ) (u d : hubbardSpinConfig N) :
    hubbardUpConfig N (hubbardMergeConfig N u d) = u := by
  funext i; simp [hubbardUpConfig]

/-- The down projection recovers the down part of a merge: `down (merge u d) = d`. -/
@[simp]
theorem hubbardDownConfig_merge (N : ℕ) (u d : hubbardSpinConfig N) :
    hubbardDownConfig N (hubbardMergeConfig N u d) = d := by
  funext i; simp [hubbardDownConfig]

/-- Merging the up/down projections recovers the configuration:
`merge (up c) (down c) = c`. -/
@[simp]
theorem hubbardMergeConfig_up_down (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) :
    hubbardMergeConfig N (hubbardUpConfig N c) (hubbardDownConfig N c) = c := by
  funext o
  obtain ⟨i, r, rfl⟩ := exists_spinfulIndex N o
  fin_cases r
  · simp [hubbardUpConfig]
  · simp [hubbardDownConfig]

/-- The basis-level factorization `H = H↑ ⊗ H↓`: a spin-orbital configuration is
the same data as a pair `(up config, down config)`. -/
def hubbardSpinConfigEquiv (N : ℕ) :
    (Fin (2 * N + 2) → Fin 2) ≃ hubbardSpinConfig N × hubbardSpinConfig N where
  toFun c := (hubbardUpConfig N c, hubbardDownConfig N c)
  invFun p := hubbardMergeConfig N p.1 p.2
  left_inv c := by simp
  right_inv p := by obtain ⟨u, d⟩ := p; simp

/-- The induced linear isomorphism between a state vector and its **coefficient
matrix** `M_{u,d} = ψ (merge u d)` indexed by the up/down configurations. -/
noncomputable def hubbardSpinCoeffLinearEquiv (N : ℕ) :
    ((Fin (2 * N + 2) → Fin 2) → ℂ) ≃ₗ[ℂ]
      Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ where
  toFun ψ := fun u d => ψ (hubbardMergeConfig N u d)
  map_add' ψ φ := by funext u d; simp
  map_smul' a ψ := by funext u d; simp
  invFun M := fun c => M (hubbardUpConfig N c) (hubbardDownConfig N c)
  left_inv ψ := by funext c; simp
  right_inv M := by funext u d; simp

/-! ## Sector bookkeeping -/

/-- The total occupation splits into the up and down occupations:
`∑_k c k = ∑_i (up c) i + ∑_i (down c) i`. -/
theorem hubbardConfig_count_eq_up_add_down (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) :
    (∑ k : Fin (2 * N + 2), (c k).val) =
      (∑ i : Fin (N + 1), (hubbardUpConfig N c i).val) +
        (∑ i : Fin (N + 1), (hubbardDownConfig N c i).val) := by
  rw [sum_spinful_reindex N (fun k => (c k).val)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fin.sum_univ_two]
  rfl

/-! ## The spin reflection `θ` -/

/-- Flip an occupation number: `0 ↦ 1`, `1 ↦ 0` (the particle–hole map on one
orbital). -/
def flipOccupation : Fin 2 → Fin 2 := fun a => if a = 0 then 1 else 0

/-- The occupation flip is an involution: `flip (flip a) = a`. -/
@[simp]
theorem flipOccupation_flipOccupation (a : Fin 2) :
    flipOccupation (flipOccupation a) = a := by
  fin_cases a <;> rfl

/-- The particle–hole map on a single-species configuration: flip every
occupation number. -/
def particleHoleConfig (N : ℕ) (c : hubbardSpinConfig N) : hubbardSpinConfig N :=
  fun i => flipOccupation (c i)

/-- The particle–hole map is an involution. -/
theorem particleHoleConfig_involutive (N : ℕ) :
    Function.Involutive (particleHoleConfig N) := by
  intro c; funext i; simp [particleHoleConfig]

/-- The particle–hole map is an involution (simp form). -/
@[simp]
theorem particleHoleConfig_particleHoleConfig (N : ℕ) (c : hubbardSpinConfig N) :
    particleHoleConfig N (particleHoleConfig N c) = c :=
  particleHoleConfig_involutive N c

/-- The configuration-level spin reflection `θ`: swap the up/down species and
apply the particle–hole map to each, i.e. `(n↑, n↓) ↦ (1 − n↓, 1 − n↑)`. -/
def spinReflectionConfig (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) :
    Fin (2 * N + 2) → Fin 2 :=
  hubbardMergeConfig N (particleHoleConfig N (hubbardDownConfig N c))
    (particleHoleConfig N (hubbardUpConfig N c))

/-- The configuration-level spin reflection `θ` is an involution. -/
theorem spinReflectionConfig_involutive (N : ℕ) :
    Function.Involutive (spinReflectionConfig N) := by
  intro c
  simp only [spinReflectionConfig, hubbardUpConfig_merge, hubbardDownConfig_merge,
    particleHoleConfig_particleHoleConfig, hubbardMergeConfig_up_down]

/-- The spin reflection `θ` as a permutation of configurations. -/
def spinReflectionConfigEquiv (N : ℕ) :
    (Fin (2 * N + 2) → Fin 2) ≃ (Fin (2 * N + 2) → Fin 2) :=
  (spinReflectionConfig_involutive N).toPerm

/-- The antiunitary spin reflection `θ` on state vectors:
`(θ ψ) c = conj (ψ (spinReflectionConfig c))`. -/
noncomputable def spinReflectionThetaVec (N : ℕ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) : (Fin (2 * N + 2) → Fin 2) → ℂ :=
  fun c => star (ψ (spinReflectionConfig N c))

/-- `θ` is conjugate-linear in the scalar: `θ (a • ψ) = conj a • θ ψ`. -/
theorem spinReflectionThetaVec_smul (N : ℕ) (a : ℂ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    spinReflectionThetaVec N (a • ψ) = star a • spinReflectionThetaVec N ψ := by
  funext c
  simp only [spinReflectionThetaVec, Pi.smul_apply, smul_eq_mul, star_mul']

/-- `θ` is involutive on state vectors. -/
theorem spinReflectionThetaVec_involutive (N : ℕ) :
    Function.Involutive (spinReflectionThetaVec (N := N)) := by
  intro ψ; funext c
  simp [spinReflectionThetaVec, spinReflectionConfig_involutive N c]

/-- **Antiunitarity of `θ`**: it preserves the Hermitian inner product up to
conjugation, `⟨θ ψ, θ φ⟩ = conj ⟨ψ, φ⟩`. -/
theorem spinReflectionThetaVec_dotProduct (N : ℕ)
    (ψ φ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    dotProduct (star (spinReflectionThetaVec N ψ)) (spinReflectionThetaVec N φ)
      = star (dotProduct (star ψ) φ) := by
  have hL : dotProduct (star (spinReflectionThetaVec N ψ)) (spinReflectionThetaVec N φ)
      = ∑ c, ψ (spinReflectionConfig N c) * star (φ (spinReflectionConfig N c)) := by
    unfold dotProduct
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Pi.star_apply, spinReflectionThetaVec, star_star]
  have hR : star (dotProduct (star ψ) φ) = ∑ x, ψ x * star (φ x) := by
    unfold dotProduct
    rw [star_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Pi.star_apply, star_mul', star_star]
  rw [hL, hR, ← Equiv.sum_comp (spinReflectionConfigEquiv N) (fun x => ψ x * star (φ x))]
  rfl

/-! ## The spin-reflection coefficient matrix -/

/-- The spin-reflection coefficient matrix: the coefficient matrix of `ψ` with
the **down index read as a hole configuration**,
`(spinReflectionCoeff ψ) u h = ψ (merge u (particle-hole h))`. -/
noncomputable def spinReflectionCoeff (N : ℕ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ :=
  fun u h => ψ (hubbardMergeConfig N u (particleHoleConfig N h))

/-- A state vector is **spin-reflection positive** when its coefficient matrix
(with the down hole gauge) is positive-semidefinite. -/
def SpinReflectionPositive (N : ℕ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) : Prop :=
  (spinReflectionCoeff N ψ).PosSemidef

/-- `θ` acts on the coefficient matrix as the conjugate transpose:
`spinReflectionCoeff (θ ψ) = (spinReflectionCoeff ψ)ᴴ`. -/
theorem spinReflectionCoeff_thetaVec (N : ℕ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    spinReflectionCoeff N (spinReflectionThetaVec N ψ)
      = (spinReflectionCoeff N ψ)ᴴ := by
  funext u h
  simp only [spinReflectionCoeff, spinReflectionThetaVec, conjTranspose_apply,
    spinReflectionConfig, hubbardUpConfig_merge, hubbardDownConfig_merge,
    particleHoleConfig_particleHoleConfig]

/-! ## The spin-reflection-positivity nonnegativity -/

/-- **The algebraic heart of spin-reflection positivity.**  For any
positive-semidefinite matrix `C` and any matrix `A`, the trace
`tr (C A C Aᴴ)` has nonnegative real part.  Writing `C = B²` with `B ≥ 0`
Hermitian and `M := B A B`, cyclicity gives `tr (C A C Aᴴ) = tr (M Mᴴ) ≥ 0`. -/
theorem spinReflection_gramMatrix_nonneg {ι : Type*} [Fintype ι]
    {C : Matrix ι ι ℂ} (hC : C.PosSemidef) (A : Matrix ι ι ℂ) :
    0 ≤ (Matrix.trace (C * A * C * Aᴴ)).re := by
  classical
  obtain ⟨B, hB, hBC⟩ := exists_posSemidef_sq_eq_of_posSemidef hC
  have hBH : Bᴴ = B := hB.isHermitian.eq
  have hMMH : (B * A * B) * (B * A * B)ᴴ = (B * A * B * B * Aᴴ) * B := by
    simp only [conjTranspose_mul, hBH]; noncomm_ring
  have htr : Matrix.trace (C * A * C * Aᴴ)
      = Matrix.trace ((B * A * B) * (B * A * B)ᴴ) := by
    rw [hMMH, Matrix.trace_mul_comm (B * A * B * B * Aᴴ) B, hBC]
    congr 1
    noncomm_ring
  rw [htr]
  have hpsd : ((B * A * B) * (B * A * B)ᴴ).PosSemidef :=
    Matrix.posSemidef_self_mul_conjTranspose (B * A * B)
  simpa using (Complex.le_def.mp hpsd.trace_nonneg).1

end LatticeSystem.Fermion
