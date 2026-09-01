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
of that Hermitian matrix.  Three properties follow from nothing but the variational principle:

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
Hermitian operator.  Private because it exists only to supply `chainGroundEnergy` with the
`IsHermitian` argument `hermitianMinEigenvalue` demands; the concrete ring instance of the same
fact is the public `staggeredFieldChainHamiltonianS_isHermitian`. -/
private theorem fieldOpS_isHermitian {Λ : Type*} {N : ℕ}
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

end LatticeSystem.Quantum
