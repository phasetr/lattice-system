import LatticeSystem.Quantum.SpinS.HermitianGroundStateEigenvalue
import LatticeSystem.Quantum.SpinS.RayleighRitzEquality
import LatticeSystem.Quantum.SpinS.HermitianMinSimilarInvariance

/-!
# Ground energy of a symmetry-breaking field family with a reversal symmetry

Tasaki §3.4 introduces the Hamiltonian with symmetry-breaking field `Ĥ_h = Ĥ − h Ô_L`
(eq. (3.4.19), p. 69) and proves the Kaplan–Horsch–von der Linden theorem from the elementary
variational inequality `⟨Ξ|Ĥ_h|Ξ⟩ ≥ ⟨Φ_{GS,h}|Ĥ_h|Φ_{GS,h}⟩` (eq. (3.4.20), p. 70).  This module
develops the *field-dependence* side of that same inequality, at the abstract `ManyBodyOpS Λ N`
level: `H` is any Hermitian Hamiltonian, `O` any Hermitian order operator, and `Θ` any involution
(`Θ Θ = 1`) that commutes with `H` and reverses `O` (`Θ O Θ = −O`).

`chainGroundEnergy hH hO h` is the ground energy `E(h)` of `H − h·O`, i.e. the minimum eigenvalue
of that Hermitian matrix.  Three properties of it are developed here — the first from invariance of
the spectrum under conjugation by a unit, the other two from the variational principle:

* `chainGroundEnergy_neg` — `E(h) = E(−h)`, since `Θ` conjugates `H − h·O` into `H + h·O` and
  conjugation by a unit preserves the spectrum;
* `chainGroundEnergy_concave` — `E` is concave, being a pointwise minimum of the affine functions
  `h ↦ ⟨Φ, HΦ⟩ − h⟨Φ, OΦ⟩`;
* `chainGroundEnergy_le_zero_field` — `E(h) ≤ E(0)`, i.e. `h = 0` maximises the concave even
  function `E`.

Combining them gives `chainGroundState_order_mean_sandwich`, the two-sided bound
`0 ≤ E(0) − E(h) ≤ h⟨Ô⟩_h ≤ E(0) − E(2h)` on the order-parameter expectation in a normalized
ground state at field `h`.  It converts a statement about ground *states* (with their eigenvector
quantifiers and possible degeneracy) into one about the scalar function `E`, which is what the
Theorem 4.2 reduction in `ShastryNoSSBReduction.lean` consumes.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, eqs. (3.4.19)–(3.4.20), pp. 69–70; §4.1, eqs. (4.1.9)–(4.1.10), pp. 76–77.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **The field-dressed operator `H − h·O` is Hermitian** for real `h` (Tasaki eq. (3.4.19),
p. 69): a difference of a Hermitian operator and a self-adjoint (real) scalar multiple of a
Hermitian operator.  It supplies the `IsHermitian` argument `hermitianMinEigenvalue` demands, in
`chainGroundEnergy` and at each trial-state comparison of `chainGroundEnergy_concave` and
`chainGroundState_order_mean_sandwich`, and is public because the concrete ring instance
`staggeredFieldChainHamiltonianS_isHermitian` (in `ShastryNoSSBReduction.lean`) is *this* lemma
applied to the ring data rather than a second proof of the same fact. -/
theorem fieldOpS_isHermitian {Λ : Type*} {N : ℕ}
    {H O : ManyBodyOpS Λ N} (hH : H.IsHermitian) (hO : O.IsHermitian) (h : ℝ) :
    (H - (h : ℂ) • O).IsHermitian := by
  refine hH.sub (hO.smul ?_)
  rw [isSelfAdjoint_iff]
  exact Complex.conj_ofReal h

/-- **The ground energy `E(h)` of the symmetry-breaking field family `H − h·O`** (Tasaki
eq. (3.4.19), p. 69): the minimum eigenvalue of the Hermitian matrix `H − h·O`.  Only Hermiticity
of `H` and of `O` is assumed — no reversal symmetry, no ring structure, no parity of the volume.
By the Rayleigh–Ritz characterisation this is the infimum of `⟨Φ, HΦ⟩ − h⟨Φ, OΦ⟩` over normalized
`Φ`, which is the quantity compared in Tasaki's variational inequality (3.4.20), p. 70.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, eqs. (3.4.19)–(3.4.20), pp. 69–70. -/
noncomputable def chainGroundEnergy {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    [Nonempty (Λ → Fin (N + 1))] {H O : ManyBodyOpS Λ N}
    (hH : H.IsHermitian) (hO : O.IsHermitian) (h : ℝ) : ℝ :=
  hermitianMinEigenvalue (fieldOpS_isHermitian hH hO h)

/-- **The ground energy is an even function of the field**, `E(h) = E(−h)` (Tasaki
eq. (3.4.19), p. 69, for the staggered field of eq. (4.1.9), p. 76).  The reversal `Θ` is an
involution commuting with `H` and reversing `O`, so it conjugates `H − h·O` into `H + h·O`; as a
unit of the matrix ring it preserves the spectrum, and both matrices being Hermitian their minimum
eigenvalues therefore agree.  No normalisation or unitarity of `Θ` is used — `Θ Θ = 1` alone makes
`Θ` a unit, which is all the spectral argument needs.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, eq. (3.4.19), p. 69; §4.1, eq. (4.1.9), p. 76. -/
theorem chainGroundEnergy_neg {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    [Nonempty (Λ → Fin (N + 1))] {H O Θ : ManyBodyOpS Λ N}
    (hH : H.IsHermitian) (hO : O.IsHermitian)
    (hΘ2 : Θ * Θ = 1) (hΘH : Θ * H * Θ = H) (hΘO : Θ * O * Θ = -O) (h : ℝ) :
    chainGroundEnergy hH hO h = chainGroundEnergy hH hO (-h) := by
  have hconj : Θ * (H - (h : ℂ) • O) * Θ = H - ((-h : ℝ) : ℂ) • O := by
    simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, hΘH, hΘO]
    simp [smul_neg, neg_smul]
  have hspec := spectrum.units_conjugate (R := ℝ) (a := H - (h : ℂ) • O)
    (u := (⟨Θ, Θ, hΘ2, hΘ2⟩ : (ManyBodyOpS Λ N)ˣ))
  simp only [Units.inv_mk, Units.val_mk] at hspec
  rw [hconj] at hspec
  unfold chainGroundEnergy
  exact hermitianMinEigenvalue_eq_of_spectrum_eq _ _ hspec.symm

/-- **The real quadratic form of `H − c·O` splits linearly in the field**,
`⟨Φ, (H − c·O)Φ⟩.re = ⟨Φ, HΦ⟩.re − c·⟨Φ, OΦ⟩.re` for real `c`: the un-normalised numerator of
Tasaki's variational comparison (3.4.20), p. 70, of the field Hamiltonian (3.4.19), p. 69.  Private
because it carries no content beyond `⬝ᵥ`-bilinearity and exists only as the shared algebraic step
of `chainGroundEnergy_concave` and `chainGroundState_order_mean_sandwich` below.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, eqs. (3.4.19)–(3.4.20), pp. 69–70. -/
private theorem fieldOpS_dotProduct_re {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    (H O : ManyBodyOpS Λ N) (c : ℝ) (Φ : (Λ → Fin (N + 1)) → ℂ) :
    (star Φ ⬝ᵥ (H - (c : ℂ) • O).mulVec Φ).re
      = (star Φ ⬝ᵥ H.mulVec Φ).re - c * (star Φ ⬝ᵥ O.mulVec Φ).re := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    Complex.sub_re, Complex.re_ofReal_mul]

/-- **The ground energy is concave in the field**: for `0 ≤ t ≤ 1`,
`t E(h₁) + (1−t) E(h₂) ≤ E(t h₁ + (1−t) h₂)`.  `E` is the pointwise minimum over normalized states
of the affine functions `h ↦ ⟨Φ, HΦ⟩.re − h⟨Φ, OΦ⟩.re` (Tasaki's field Hamiltonian (3.4.19), p. 69,
compared as in (3.4.20), p. 70), and a minimum of affine functions is concave: evaluate the
minimiser at `t h₁ + (1−t) h₂` and bound `E(h₁)`, `E(h₂)` by that same state's energies.  Only
Hermiticity of `H` and `O` is used — no reversal symmetry.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, eqs. (3.4.19)–(3.4.20), pp. 69–70. -/
theorem chainGroundEnergy_concave {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    [Nonempty (Λ → Fin (N + 1))] {H O : ManyBodyOpS Λ N}
    (hH : H.IsHermitian) (hO : O.IsHermitian) (h₁ h₂ t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * chainGroundEnergy hH hO h₁ + (1 - t) * chainGroundEnergy hH hO h₂ ≤
      chainGroundEnergy hH hO (t * h₁ + (1 - t) * h₂) := by
  obtain ⟨Φ, hΦnorm, hΦE⟩ := exists_unit_eigenvector_hermitianMinEigenvalue
    (fieldOpS_isHermitian hH hO (t * h₁ + (1 - t) * h₂))
  have hle : ∀ c : ℝ, chainGroundEnergy hH hO c ≤
      (star Φ ⬝ᵥ H.mulVec Φ).re - c * (star Φ ⬝ᵥ O.mulVec Φ).re := by
    intro c
    have hv := hermitianMinEigenvalue_le_rayleighOnVec_of_unit (fieldOpS_isHermitian hH hO c) hΦnorm
    unfold rayleighOnVec at hv
    rwa [fieldOpS_dotProduct_re] at hv
  have heq : chainGroundEnergy hH hO (t * h₁ + (1 - t) * h₂) =
      (star Φ ⬝ᵥ H.mulVec Φ).re - (t * h₁ + (1 - t) * h₂) * (star Φ ⬝ᵥ O.mulVec Φ).re := by
    have hval : (star Φ ⬝ᵥ (H - ((t * h₁ + (1 - t) * h₂ : ℝ) : ℂ) • O).mulVec Φ).re =
        chainGroundEnergy hH hO (t * h₁ + (1 - t) * h₂) := by
      rw [hΦE, dotProduct_smul, smul_eq_mul, hΦnorm, mul_one, Complex.ofReal_re]
      rfl
    rw [← hval, fieldOpS_dotProduct_re]
  have hA := mul_le_mul_of_nonneg_left (hle h₁) ht0
  have hB := mul_le_mul_of_nonneg_left (hle h₂) (by linarith : (0 : ℝ) ≤ 1 - t)
  have hring : t * ((star Φ ⬝ᵥ H.mulVec Φ).re - h₁ * (star Φ ⬝ᵥ O.mulVec Φ).re) +
      (1 - t) * ((star Φ ⬝ᵥ H.mulVec Φ).re - h₂ * (star Φ ⬝ᵥ O.mulVec Φ).re) =
        (star Φ ⬝ᵥ H.mulVec Φ).re -
          (t * h₁ + (1 - t) * h₂) * (star Φ ⬝ᵥ O.mulVec Φ).re := by ring
  rw [heq]
  linarith [hA, hB, hring]

/-- **Zero field maximises the ground energy**: `E(h) ≤ E(0)`.  `E` is concave
(`chainGroundEnergy_concave`) and even (`chainGroundEnergy_neg`), so the midpoint bound at
`t = 1/2`, `h₁ = h`, `h₂ = −h` reads `½E(h) + ½E(−h) ≤ E(0)`, i.e. `E(h) ≤ E(0)`.  There is no sign
hypothesis on `h`: `0` maximises the even concave function `E` on all of `ℝ`.  This is what makes
the staggered field of eq. (4.1.9), p. 76, lower the ground energy, in either direction.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, eq. (3.4.19), p. 69; §4.1, eq. (4.1.9), p. 76. -/
theorem chainGroundEnergy_le_zero_field {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    [Nonempty (Λ → Fin (N + 1))] {H O Θ : ManyBodyOpS Λ N}
    (hH : H.IsHermitian) (hO : O.IsHermitian)
    (hΘ2 : Θ * Θ = 1) (hΘH : Θ * H * Θ = H) (hΘO : Θ * O * Θ = -O) (h : ℝ) :
    chainGroundEnergy hH hO h ≤ chainGroundEnergy hH hO 0 := by
  have hc := chainGroundEnergy_concave hH hO h (-h) (1 / 2) (by norm_num) (by norm_num)
  have hmid : (1 : ℝ) / 2 * h + (1 - 1 / 2) * -h = 0 := by ring
  rw [hmid] at hc
  have hneg := chainGroundEnergy_neg hH hO hΘ2 hΘH hΘO h
  linarith [hc, hneg]

/-- **Order-parameter sandwich in a ground state at field `h`**:
`0 ≤ E(0) − E(h) ≤ h⟨Ô⟩_h ≤ E(0) − E(2h)` for any normalized ground state `Φ` of `H − h·O`.

This is Tasaki's variational comparison (3.4.20), p. 70, of the field Hamiltonian (3.4.19), p. 69,
run in both directions against the *same* state `Φ`.  Writing `⟨Ĥ⟩ = ⟨Φ, HΦ⟩.re` and
`⟨Ô⟩ = ⟨Φ, OΦ⟩.re`, the eigenvalue equation gives `E(h) = ⟨Ĥ⟩ − h⟨Ô⟩` exactly, while `Φ` is only a
trial state at the other two fields: `E(0) ≤ ⟨Ĥ⟩` yields the middle inequality and
`E(2h) ≤ ⟨Ĥ⟩ − 2h⟨Ô⟩` the right one (after `E(h) ≤ E(0)`); the left one is
`chainGroundEnergy_le_zero_field`.  The point of the chain is that it brackets the state-dependent
`h⟨Ô⟩_h` between two differences of the *scalar* function `E`, eliminating the eigenvector
quantifiers and any ground-state degeneracy.

The hypothesis `0 ≤ h` is retained deliberately, although the algebra never consumes it: all three
inequalities are proved for every real `h`, and the leading underscore of `_hh` records that it goes
unused.  It is kept because it marks the only regime in which the chain carries information — for
`h ≥ 0` the left inequality `0 ≤ E(0) − E(h)` forces `0 ≤ ⟨Ô⟩`, the sign the Theorem 4.2 reduction
consumes — so it is a documented restriction on callers rather than an oversight.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, eqs. (3.4.19)–(3.4.20), pp. 69–70; §4.1, eqs. (4.1.9)–(4.1.10), pp. 76–77. -/
theorem chainGroundState_order_mean_sandwich {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    [Nonempty (Λ → Fin (N + 1))] {H O Θ : ManyBodyOpS Λ N}
    (hH : H.IsHermitian) (hO : O.IsHermitian)
    (hΘ2 : Θ * Θ = 1) (hΘH : Θ * H * Θ = H) (hΘO : Θ * O * Θ = -O)
    (h : ℝ) (_hh : 0 ≤ h) {Φ : (Λ → Fin (N + 1)) → ℂ} (hΦnorm : star Φ ⬝ᵥ Φ = 1)
    (hΦE : (H - (h : ℂ) • O).mulVec Φ = ((chainGroundEnergy hH hO h : ℝ) : ℂ) • Φ) :
    0 ≤ chainGroundEnergy hH hO 0 - chainGroundEnergy hH hO h ∧
      chainGroundEnergy hH hO 0 - chainGroundEnergy hH hO h ≤
        h * (star Φ ⬝ᵥ O.mulVec Φ).re ∧
      h * (star Φ ⬝ᵥ O.mulVec Φ).re ≤
        chainGroundEnergy hH hO 0 - chainGroundEnergy hH hO (2 * h) := by
  have hle : ∀ c : ℝ, chainGroundEnergy hH hO c ≤
      (star Φ ⬝ᵥ H.mulVec Φ).re - c * (star Φ ⬝ᵥ O.mulVec Φ).re := by
    intro c
    have hv := hermitianMinEigenvalue_le_rayleighOnVec_of_unit (fieldOpS_isHermitian hH hO c) hΦnorm
    unfold rayleighOnVec at hv
    rwa [fieldOpS_dotProduct_re] at hv
  have heq : chainGroundEnergy hH hO h =
      (star Φ ⬝ᵥ H.mulVec Φ).re - h * (star Φ ⬝ᵥ O.mulVec Φ).re := by
    have hval : (star Φ ⬝ᵥ (H - (h : ℂ) • O).mulVec Φ).re = chainGroundEnergy hH hO h := by
      rw [hΦE, dotProduct_smul, smul_eq_mul, hΦnorm, mul_one, Complex.ofReal_re]
    rw [← hval, fieldOpS_dotProduct_re]
  have h0 := hle 0
  have h2 := hle (2 * h)
  have hmax := chainGroundEnergy_le_zero_field hH hO hΘ2 hΘH hΘO h
  exact ⟨by linarith, by linarith, by linarith⟩

end LatticeSystem.Quantum
