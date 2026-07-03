import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsive
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJModel
import LatticeSystem.Quantum.GibbsState.Duhamel

/-!
# Kubo–Kishi finite-temperature susceptibility bound (Tasaki §10.2.5, Theorem 10.11)

This file formalizes the statement of **Tasaki Theorem 10.11**, the
finite-temperature version of Lieb's theorem due to Kubo and Kishi, from
Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st
ed., Springer 2020, §10.2.5, pp. 368–369, eqs. (10.2.52)–(10.2.56).

For the repulsive Hubbard model at half-filling (grand-canonical chemical
potential `μ = U/2`, the particle–hole-symmetric point), Kubo and Kishi
proved that the charge susceptibility `χ^c_q` and the on-site pairing
(superconducting) susceptibility `χ^p_q` are bounded, uniformly in the
temperature and the wave number, by

  `χ^c_q(β, U/2) ≤ 1/U`,   `χ^p_q(β, U/2) ≤ 2/U`   (eq. (10.2.56)),

so the half-filled model exhibits no charge-density-wave or
superconducting long-range order at any finite temperature.

## Susceptibility framework

Tasaki defines `χ^c_q`, `χ^p_q` as second derivatives (eqs. (10.2.53)/
(10.2.54)) of the grand-canonical thermodynamic function
`J(β, μ, (γ_x), (η_x))` (eq. (10.2.52)) with respect to the Fourier
components of fictitious external fields testing for charge ordering
(`γ_x`, coupled to `n̂_x`) and superconducting ordering (`η_x`, coupled
to `ĉ†_{x↑}ĉ†_{x↓} + ĉ_{x↓}ĉ_{x↑}`). By the fluctuation–dissipation
theorem these second derivatives equal the Duhamel imaginary-time
two-point functions `duhamelStaticSusceptibility`, which is the form used
here: `χ^c_q` (resp. `χ^p_q`) is the Duhamel susceptibility of the charge
(resp. pairing) Fourier mode of wave number `q`.

The wave numbers `q` are genuine characters of a periodic lattice
(eq. (10.2.55): `γ̃_q = |Λ|^{-1/2} Σ_x γ_x e^{iq·x}`, "which we assume to
have a periodic structure"), realized here by the 1D wave-number character
`fourierCharacter N k`, `w_x = exp(2πi k x / (N+1))`.

## Status

Tasaki states Theorem 10.11 **without proof**, citing Kubo–Kishi,
*Phys. Rev. B* **41**, 4866 (1990). Following the project policy for
book theorems that Tasaki records without proof (as with
`mielke_theorem_11_13`), it is recorded here as a faithful documented
`axiom` on the concrete Duhamel susceptibilities defined below.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {N : ℕ}

/-- The **grand-canonical uniform repulsive Hubbard Hamiltonian**
`Ĥ − μ N̂` (the core of Tasaki eq. (10.2.52) at zero external fields), with
`Ĥ` the uniform repulsive Hubbard Hamiltonian (`U > 0`, eq. (10.2.5)) and
`μ` the chemical potential. At the half-filling value `μ = U/2` this is the
particle–hole-symmetric form (eq. (10.2.6)) up to an additive constant,
which leaves the Gibbs state and every susceptibility unchanged. -/
noncomputable def grandCanonicalRepulsiveHubbard (N : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U μ : ℝ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  repulsiveHubbardHamiltonian N T U - (μ : ℂ) • fermionTotalNumber (2 * N + 1)

/-- The **1D wave-number Fourier character** `w_x = exp(2πi k x / (N+1))`
of a periodic lattice of `N + 1` sites (Tasaki eq. (10.2.55), the plane
wave `e^{iq·x}` for wave number `q = 2πk/(N+1)`). Each value has unit
modulus, so this is a genuine lattice character rather than an arbitrary
weight. -/
noncomputable def fourierCharacter (N : ℕ) (k : ℤ) : Fin (N + 1) → ℂ :=
  fun x => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x.val : ℂ)
    / ((N : ℂ) + 1))

/-- The **charge Fourier mode** `ñ_q = |Λ|^{-1/2} Σ_x w_x n̂_x` (Tasaki
eq. (10.2.55) applied to the on-site number operator `n̂_x = n̂_{x↑} +
n̂_{x↓}`), with normalization `|Λ|^{-1/2} = (√(N+1))⁻¹` over the `N + 1`
sites. The weight `w` is the Fourier character of the tested wave number. -/
noncomputable def chargeFourierMode (N : ℕ) (w : Fin (N + 1) → ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  ((Real.sqrt ((N : ℝ) + 1) : ℂ))⁻¹ •
    ∑ x : Fin (N + 1), w x • fermionSiteNumber N x

/-- The **pairing Fourier mode**
`p̂_q = |Λ|^{-1/2} Σ_x w_x (ĉ†_{x↑}ĉ†_{x↓} + ĉ_{x↓}ĉ_{x↑})`
(Tasaki eq. (10.2.55) applied to the Hermitian on-site pair field
coupled to the fictitious field `η_x` in eq. (10.2.52)), with
normalization `|Λ|^{-1/2} = (√(N+1))⁻¹`. -/
noncomputable def pairFieldFourierMode (N : ℕ) (w : Fin (N + 1) → ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  ((Real.sqrt ((N : ℝ) + 1) : ℂ))⁻¹ •
    ∑ x : Fin (N + 1), w x •
      (fermionUpCreation N x * fermionDownCreation N x
        + fermionDownAnnihilation N x * fermionUpAnnihilation N x)

/-- The **charge susceptibility** `χ^c_q(β, μ)` (Tasaki eq. (10.2.53)),
realized as the Duhamel imaginary-time two-point function of the charge
Fourier mode at wave number `q` (weight `w`) and its conjugate at `−q`
(weight `x ↦ conj (w x)`), in the Gibbs state of the grand-canonical
repulsive Hubbard Hamiltonian at `μ`. -/
noncomputable def chargeSusceptibility (N : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U μ β : ℝ)
    (w : Fin (N + 1) → ℂ) : ℂ :=
  duhamelStaticSusceptibility β (grandCanonicalRepulsiveHubbard N T U μ)
    (chargeFourierMode N w) (chargeFourierMode N (fun x => star (w x)))

/-- The **on-site pairing susceptibility** `χ^p_q(β, μ)` (Tasaki
eq. (10.2.54)), realized as the Duhamel imaginary-time two-point function
of the pairing Fourier mode at wave number `q` (weight `w`) and its
conjugate at `−q` (weight `x ↦ conj (w x)`), in the Gibbs state of the
grand-canonical repulsive Hubbard Hamiltonian at `μ`. -/
noncomputable def pairSusceptibility (N : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U μ β : ℝ)
    (w : Fin (N + 1) → ℂ) : ℂ :=
  duhamelStaticSusceptibility β (grandCanonicalRepulsiveHubbard N T U μ)
    (pairFieldFourierMode N w) (pairFieldFourierMode N (fun x => star (w x)))

/-- **Tasaki Theorem 10.11** (Kubo–Kishi finite-temperature susceptibility
bound, 1st ed., Springer 2020, §10.2.5, pp. 368–369, eqs. (10.2.52)–
(10.2.56), **AXIOM**). Consider the uniform repulsive Hubbard model
(eq. (10.2.5), `U > 0`) on a bipartite real symmetric connected hopping
matrix `T` — the conditions for Theorem 10.4 (except the electron-number
condition) — at the half-filling chemical potential `μ = U/2` (the
particle–hole-symmetric point). Then for every inverse temperature
`β > 0` and every wave number `k`, both the charge susceptibility and the
on-site pairing susceptibility are real, and

  `χ^c_k(β, U/2) ≤ 1/U`,   `χ^p_k(β, U/2) ≤ 2/U`   (eq. (10.2.56)),

so the half-filled model has no charge-density-wave or superconducting
long-range order at any finite temperature.

Tasaki states this without proof, citing Kubo–Kishi, *Phys. Rev. B*
**41**, 4866 (1990); following the project policy for book theorems that
Tasaki records without proof (as with `mielke_theorem_11_13`), it is a
faithful documented axiom on the concrete Duhamel susceptibilities. -/
axiom theorem_10_11_kubo_kishi_susceptibility_bound
    {N : ℕ}
    (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (U : ℝ) (hU : 0 < U)
    (hsymm : ∀ x y, T x y = T y x)
    (hbip : HoppingRespectsBipartition A T)
    (hconn : (hoppingSupportGraph T).Preconnected)
    (β : ℝ) (hβ : 0 < β)
    (k : ℤ) :
    (chargeSusceptibility N T U (U / 2) β (fourierCharacter N k)).im = 0 ∧
      (chargeSusceptibility N T U (U / 2) β (fourierCharacter N k)).re ≤ 1 / U ∧
    (pairSusceptibility N T U (U / 2) β (fourierCharacter N k)).im = 0 ∧
      (pairSusceptibility N T U (U / 2) β (fourierCharacter N k)).re ≤ 2 / U

end LatticeSystem.Fermion
