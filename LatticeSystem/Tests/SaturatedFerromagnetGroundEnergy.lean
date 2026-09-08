import LatticeSystem.Quantum.SpinS.SaturatedFerromagnetGroundEnergy

/-!
# Signature pin: the ferromagnetic ground-energy declarations of Tasaki §2.4

Repository-internal regression guard for the four declarations behind the ferromagnetic
ground-state energy `E_GS = −|B| S²`, the input to Tasaki's Theorem 2.1 (p. 34): the per-bond
upper bound `Ŝ_x·Ŝ_y ≤ S²` (F1a on `Fin 2`, F1b on a general `Λ`) and the ground-energy
minimality pair (F2 the frustration-free `PosSemidef` certificate, F3 the eigenvalue-minimality
corollary). The four names live in `LatticeSystem/Quantum/SpinS/SaturatedBondBound.lean` and
`LatticeSystem/Quantum/SpinS/SaturatedFerromagnetGroundEnergy.lean`; any rename, reordering of
arguments or weakening of the hypotheses there breaks this module.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer 2020),
§2.4, p. 32, eq. (2.4.5); Lemma A.9, p. 469.
-/

namespace LatticeSystem.Tests.SaturatedFerromagnetGroundEnergy

open scoped ComplexOrder
open Matrix LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Signature pin (F1a).** On the two-site space `Fin 2`, the per-bond upper bound
`Ŝ₀·Ŝ₁ ≤ S²`, i.e. `S²·1 − Ŝ₀·Ŝ₁ ⪰ 0`, for `1 ≤ N` (the concrete two-site instance used by the
general `Λ` route F1b). -/
example (hN : 1 ≤ N) :
    Matrix.PosSemidef (((((N : ℂ) / 2) * ((N : ℂ) / 2)) • (1 : ManyBodyOpS (Fin 2) N)
        - spinSDot (0 : Fin 2) 1 N : ManyBodyOpS (Fin 2) N)) :=
  spinSDot_maxSpin_sub_posSemidef_two hN

/-- **Signature pin (F1b).** On a general `Λ`, the per-bond upper bound `Ŝ_x·Ŝ_y ≤ S²`, i.e.
`S²·1 − Ŝ_x·Ŝ_y ⪰ 0`, for `x ≠ y` and `1 ≤ N`. -/
example (hN : 1 ≤ N) {x y : V} (hxy : x ≠ y) :
    Matrix.PosSemidef (((((N : ℂ) / 2) * ((N : ℂ) / 2)) • (1 : ManyBodyOpS V N)
        - spinSDot x y N : ManyBodyOpS V N)) :=
  spinSDot_maxSpin_sub_posSemidef hN hxy

/-- **Signature pin (F2).** `H - E_GS.re • 1` is positive semidefinite (the frustration-free
ground-energy certificate), for a real coupling `J` that vanishes on the diagonal (`J x x = 0`)
and has nonpositive (ferromagnetic) real part, with `1 ≤ N`. -/
example {J : V → V → ℂ} (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nonpos : ∀ x y, (J x y).re ≤ 0) (hJ_diag : ∀ x, J x x = 0) (hN : 1 ≤ N) :
    Matrix.PosSemidef ((heisenbergHamiltonianS (Λ := V) J N
        - ((saturatedFerromagnetEigenvalueS (V := V) J N).re : ℂ) • 1 : ManyBodyOpS V N)) :=
  heisenbergHamiltonianS_sub_saturatedFerromagnetEigenvalueS_posSemidef hJ_real hJ_nonpos
    hJ_diag hN

/-- **Signature pin (F3).** The saturated-ferromagnet eigenvalue's real part is a lower bound on
every real eigenvalue `μ` of `heisenbergHamiltonianS J N` witnessed by a nonzero eigenvector. -/
example {J : V → V → ℂ} (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nonpos : ∀ x y, (J x y).re ≤ 0) (hJ_diag : ∀ x, J x x = 0) (hN : 1 ≤ N)
    {μ : ℝ} {Ψ : (V → Fin (N + 1)) → ℂ} (hΨ : Ψ ≠ 0)
    (heig : (heisenbergHamiltonianS (Λ := V) J N).mulVec Ψ = (μ : ℂ) • Ψ) :
    (saturatedFerromagnetEigenvalueS (V := V) J N).re ≤ μ :=
  saturatedFerromagnetEigenvalueS_re_le_of_eigenvector hJ_real hJ_nonpos hJ_diag hN hΨ heig

end LatticeSystem.Tests.SaturatedFerromagnetGroundEnergy
