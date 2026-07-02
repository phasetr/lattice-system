import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveFullSectorUnique
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveTheorem102Witness
import LatticeSystem.Math.SubmoduleFinrankLeOne

/-!
# Lieb's theorem for the attractive Hubbard model: singlet uniqueness (Tasaki §10.2.1, Thm 10.2)

This file **proves** Tasaki Theorem 10.2 (Lieb's theorem for the attractive Hubbard model): for an
even electron number `Ne` with `0 < Ne ≤ 2|Λ|`, connected real symmetric hopping `T` and
site-dependent attraction `U_x > 0`, the ground state of `Ĥ = Ĥhop + Ĥatt-int` in the `Ne`-electron
sector is **unique** and a spin **singlet** (`(Ŝ_tot)² = 0`).

The declaration `theorem_10_2_lieb_attractive_unique_singlet` was previously recorded as a faithful
documented `axiom` (in `LiebAttractive.lean`).  It is now a fully proved theorem, discharged
axiom-free (modulo `propext`/`Classical.choice`/`Quot.sound`), by assembling the plain-space
milestone `attractiveHubbardFullSectorGround_unique_singlet` (the full-`Ne`-sector ground eigenspace
`G_full := (Ĥ = E_full) ⊓ (N̂ = Ne)` is nonempty, `finrank ℂ ≤ 1`, and singlet — proved by Lieb's
spin-reflection-positivity on the balanced block lifted through the SU(2) multiplet engine) into the
Euclidean `IsUniqueGroundStateOn` predicate.

## The assembly

Write `E_full` for the number-sector-compression minimum energy and take a nonzero `φ₀ ∈ G_full`
from the milestone; normalise `φ := ‖toLp φ₀‖⁻¹ • toLp φ₀` (so `‖φ‖ = 1`).  The
`Matrix.toEuclideanLin`/`mulVec` correspondence (definitional, via `WithLp.toLp`/`ofLp`) turns the
plain eigenvector relations `Ĥ φ₀ = E_full φ₀`, `N̂ φ₀ = Ne φ₀`, `Ŝ² φ₀ = 0` into their Euclidean
counterparts on `φ`.  Then:

* **membership / eigenvalue / singlet** come directly from the milestone's `φ₀`.
* **minimality** of `E_full` on the sector `K` follows from
  `configSector_minEnergy_le_of_eigenvector` applied to any competing Euclidean eigenvector, using
  number-sector support (`hubbardNumberSector_supported_of_mem`).
* **uniqueness** (collinearity) follows from `exists_smul_of_mem_of_finrank_le_one` on the
  `finrank ≤ 1` ground eigenspace.

The three `[Nonempty …]` sector hypotheses of the milestone are supplied from the arithmetic
`k ≤ N + 1` by the `LiebAttractiveTheorem102Witness` witnesses.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.1 (Theorem 10.2), §10.2.4; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix Module Module.End LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators ComplexOrder

/-- **Tasaki Theorem 10.2** (Lieb's theorem for the attractive Hubbard model, 1st ed., Springer
2020, §10.2.1, p. 348; **PROVED**, no longer an axiom).  For an arbitrary real symmetric hopping
matrix `T` whose support graph is connected (with arbitrary on-site energies) and site-dependent
attraction `U_x > 0`, and an even electron number `Ne` with `0 < Ne ≤ 2|Λ|`, the ground state of
`Ĥ = Ĥhop + Ĥatt-int` in the `Ne`-electron sector is **unique** and a spin **singlet**
(`(Ŝ_tot)² = 0`).

Proof: the full-`Ne`-sector ground eigenspace is the balanced singlet
(`attractiveHubbardFullSectorGround_unique_singlet`, Lieb's spin-space reflection-positivity lifted
through the SU(2) multiplet engine), assembled into the Euclidean `IsUniqueGroundStateOn` predicate
via the `Matrix.toEuclideanLin`/`mulVec` correspondence. -/
theorem theorem_10_2_lieb_attractive_unique_singlet (N Ne : ℕ)
    (hNe_even : Even Ne) (_hNe_pos : 0 < Ne) (hNe_le : Ne ≤ 2 * (N + 1))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT_symm : ∀ x y, T x y = T y x)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x) :
    ∃ (E : ℝ) (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)),
      IsUniqueGroundStateOn (electronNumberSectorEuclidean N Ne)
          (attractiveHubbardHamiltonian N T U) E φ ∧
        Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = 0 := by
  classical
  obtain ⟨k, hk⟩ := id hNe_even
  have hNe : Ne = 2 * k := by omega
  have hk_le : k ≤ N + 1 := by omega
  haveI := nonempty_hubbardSpinCountSector_of_le (N := N) hk_le
  haveI := nonempty_hubbardBalancedConfig_of_le (N := N) hk_le
  haveI : Nonempty (hubbardSectorConfig N Ne) := by
    rw [hNe]; exact nonempty_hubbardSectorConfig_of_le (N := N) hk_le
  set Efull : ℝ := hermitianMinEigenvalue (configSectorCompress_isHermitian
    (hubbardNumberSectorPred N Ne)
    (attractiveHubbardHamiltonian_isHermitian T U hT_symm)) with hEfull
  -- The plain-space singlet-uniqueness milestone.
  obtain ⟨⟨φ₀, hφ₀mem, hφ₀0⟩, hfin, hsinglet⟩ :=
    attractiveHubbardFullSectorGround_unique_singlet k Ne hNe hNe_even T U hT_symm hU_pos hT_conn
  obtain ⟨hφ₀H, hφ₀N⟩ := (mem_attractiveHubbardFullSectorGround_iff Ne T U hT_symm φ₀).mp hφ₀mem
  have hφ₀S : (fermionTotalSpinSquared N).mulVec φ₀ = 0 := hsinglet φ₀ hφ₀mem hφ₀0
  -- Normalised Euclidean state `φ`.
  set φE : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2) := WithLp.toLp 2 φ₀ with hφEdef
  have hφEne : φE ≠ 0 := by rw [hφEdef, ne_eq, WithLp.toLp_eq_zero]; exact hφ₀0
  set φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2) := (‖φE‖⁻¹ : ℂ) • φE with hφdef
  have hofLp : φ.ofLp = (‖φE‖⁻¹ : ℂ) • φ₀ := rfl
  have hnorm1 : ‖φ‖ = 1 := by
    rw [hφdef, norm_smul, norm_inv, Complex.norm_real, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hφEne)]
  have hφne : φ ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm1; exact one_ne_zero hnorm1.symm
  -- Forward bridge: a plain `φ₀`-eigenvector relation transports to `toEuclideanLin` on `φ`.
  have eigenφ : ∀ (M : Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ) (e : ℂ),
      M.mulVec φ₀ = e • φ₀ → Matrix.toEuclideanLin M φ = e • φ := by
    intro M e hM
    apply WithLp.ofLp_injective (p := 2) (V := (Fin (2 * N + 2) → Fin 2) → ℂ)
    change M.mulVec φ.ofLp = e • φ.ofLp
    rw [hofLp, Matrix.mulVec_smul, hM, smul_comm]
  -- Reverse bridge: a Euclidean `toEuclideanLin`-eigenvector relation transports to `mulVec`.
  have bridgeBack : ∀ (M : Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ) (e : ℂ)
      (x : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)),
      Matrix.toEuclideanLin M x = e • x → M.mulVec x.ofLp = e • x.ofLp := by
    intro M e x hx
    have h := congrArg WithLp.ofLp hx
    simpa using h
  -- Membership, eigenvalue, singlet of `φ`.
  have hφmemK : φ ∈ electronNumberSectorEuclidean N Ne := by
    rw [electronNumberSectorEuclidean, Module.End.mem_eigenspace_iff]
    exact eigenφ (fermionTotalNumber (2 * N + 1)) (Ne : ℂ) hφ₀N
  have hφHeuc : Matrix.toEuclideanLin (attractiveHubbardHamiltonian N T U) φ = (Efull : ℂ) • φ :=
    eigenφ (attractiveHubbardHamiltonian N T U) (Efull : ℂ) hφ₀H
  have hφsinglet : Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = 0 := by
    have h0 : (fermionTotalSpinSquared N).mulVec φ₀ = (0 : ℂ) • φ₀ := by rw [hφ₀S, zero_smul]
    rw [eigenφ (fermionTotalSpinSquared N) (0 : ℂ) h0, zero_smul]
  -- Ground-eigenvalue: `E_full` is realised in `K` and is minimal there.
  have hground : IsGroundEigenvalueOn (electronNumberSectorEuclidean N Ne)
      (attractiveHubbardHamiltonian N T U) Efull := by
    refine ⟨⟨φ, hφmemK, hφne, hφHeuc⟩, ?_⟩
    intro μ hμ
    obtain ⟨ψE, hψmem, hψne, hψeig⟩ := hμ
    have hψ0 : ψE.ofLp ≠ 0 := by
      simp only [ne_eq, WithLp.ofLp_eq_zero]; exact hψne
    have hĤ : (attractiveHubbardHamiltonian N T U).mulVec ψE.ofLp = (μ : ℂ) • ψE.ofLp :=
      bridgeBack _ _ _ hψeig
    have hN : (fermionTotalNumber (2 * N + 1)).mulVec ψE.ofLp = (Ne : ℂ) • ψE.ofLp :=
      bridgeBack _ _ _ ((Module.End.mem_eigenspace_iff).mp hψmem)
    have hsupp : ∀ w, ¬ hubbardNumberSectorPred N Ne w → ψE.ofLp w = 0 :=
      hubbardNumberSector_supported_of_mem Ne ((mem_hubbardSectorWSubmodule_iff Ne).mpr hN)
    exact configSector_minEnergy_le_of_eigenvector (hubbardNumberSectorPred N Ne)
      (attractiveHubbardHamiltonian_isHermitian T U hT_symm) hsupp hψ0 hĤ
  -- Uniqueness: every `E_full`-eigenvector in `K` is collinear with `φ`.
  have huniq : ∀ ψE : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
      ψE ∈ electronNumberSectorEuclidean N Ne →
      Matrix.toEuclideanLin (attractiveHubbardHamiltonian N T U) ψE = (Efull : ℂ) • ψE →
      ∃ c : ℂ, ψE = c • φ := by
    intro ψE hψmem hψeig
    have hĤ : (attractiveHubbardHamiltonian N T U).mulVec ψE.ofLp = (Efull : ℂ) • ψE.ofLp :=
      bridgeBack _ _ _ hψeig
    have hN : (fermionTotalNumber (2 * N + 1)).mulVec ψE.ofLp = (Ne : ℂ) • ψE.ofLp :=
      bridgeBack _ _ _ ((Module.End.mem_eigenspace_iff).mp hψmem)
    have hψmem' : ψE.ofLp ∈ attractiveHubbardFullSectorGround N Ne T U hT_symm :=
      (mem_attractiveHubbardFullSectorGround_iff Ne T U hT_symm ψE.ofLp).mpr ⟨hĤ, hN⟩
    obtain ⟨c, hc⟩ := exists_smul_of_mem_of_finrank_le_one hfin hφ₀mem hψmem' hφ₀0
    have hψE_eq : ψE = (c : ℂ) • φE := by
      apply WithLp.ofLp_injective (p := 2) (V := (Fin (2 * N + 2) → Fin 2) → ℂ)
      change ψE.ofLp = (c : ℂ) • φ₀
      exact hc.symm
    have hnorm_ne : (‖φE‖ : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]; exact norm_ne_zero_iff.mpr hφEne
    have hφE_eq : (‖φE‖ : ℂ) • φ = φE := by
      rw [hφdef, smul_smul, mul_inv_cancel₀ hnorm_ne, one_smul]
    exact ⟨c * (‖φE‖ : ℂ), by rw [hψE_eq, ← smul_smul, hφE_eq]⟩
  exact ⟨Efull, φ, ⟨hφmemK, hnorm1, hφHeuc, hground, huniq⟩, hφsinglet⟩

end LatticeSystem.Fermion
