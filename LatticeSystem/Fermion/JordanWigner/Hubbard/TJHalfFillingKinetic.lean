import LatticeSystem.Fermion.JordanWigner.Hubbard.TJOffDiagonal
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJKineticSector
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJNumberCommute
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJFillingBasis
import LatticeSystem.Fermion.JordanWigner.HopBasisVec

/-!
# Tasaki 11.5.3: the t-J kinetic term vanishes at half-filling (Theorem 11.26 PR1)

At half-filling `Ne = N + 1` (every site occupied) the kinetic part of the t-J Hamiltonian
annihilates the hard-core sector: a single hop `ĉ†_{i,σ} ĉ_{j,σ}` (edge `⟨i,j⟩`, `i ≠ j`) moves the
spin-`σ` electron from `j` to `i`, but at half-filling site `i` already carries an electron — if it
is spin `σ` the creation operator vanishes (Pauli), and if it is spin `σ̄` the hopped configuration
is **doubly occupied** at `i`, hence not a hard-core sector configuration `tJConfigOf s'`.  Either
way the matrix element against any hard-core sector state is `0`.

* `tJ_hop_apply_tJConfigOf_eq_zero_of_full` — the per-hop component vanishes at every sector config.

This is the first step toward `Ĥ_tJ|_{half} = J·(exchange)` (the ferromagnetic Heisenberg model)
and Theorem 11.26.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, Theorem 11.26.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- A configuration occupied at **both** orbitals of some site is not a hard-core sector
configuration `tJConfigOf s'`. -/
private theorem tJConfigOf_ne_of_double (N : ℕ) (s' : Fin (N + 1) → Fin 3)
    (d : Fin (2 * N + 2) → Fin 2) (i : Fin (N + 1))
    (h0 : d (spinfulIndex N i 0) = 1) (h1 : d (spinfulIndex N i 1) = 1) :
    tJConfigOf N s' ≠ d := by
  intro heq
  have g0 : tJConfigOf N s' (spinfulIndex N i 0) = 1 := by rw [heq]; exact h0
  have g1 : tJConfigOf N s' (spinfulIndex N i 1) = 1 := by rw [heq]; exact h1
  rw [tJConfigOf_apply_up] at g0
  rw [tJConfigOf_apply_down] at g1
  have e0 : s' i = 1 := by by_contra h; rw [if_neg h] at g0; exact absurd g0 (by norm_num)
  have e1 : s' i = 2 := by by_contra h; rw [if_neg h] at g1; exact absurd g1 (by norm_num)
  rw [e0] at e1; exact absurd e1 (by decide)

/-- **Per-hop vanishing at half-filling.**  If every site of `s` is occupied (`∀ k, s k ≠ 0`) and
`i ≠ j`, then the hop `ĉ†_{i,σ} ĉ_{j,σ}` applied to `|Φ_s⟩`, evaluated at any sector configuration
`tJConfigOf s'`, is `0`: the only nonzero target of the hop is doubly occupied at site `i`, so it
differs from the hard-core `tJConfigOf s'`. -/
theorem tJ_hop_apply_tJConfigOf_eq_zero_of_full (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (hfull : ∀ k, s k ≠ 0) (i j : Fin (N + 1)) (hij : i ≠ j) (σ : Fin 2) :
    ((fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ)).mulVec
        (basisVec (tJConfigOf N s))) (tJConfigOf N s') = 0 := by
  rw [fermionMultiCreation_mul_Annihilation_mulVec_basisVec]
  split_ifs with hcond
  · rw [Pi.smul_apply, smul_eq_mul]
    obtain ⟨hq1, hp0⟩ := hcond
    fin_cases σ
    · -- σ = ↑
      simp only [Fin.isValue, Fin.zero_eta] at hp0 ⊢
      have hpq : spinfulIndex N i 0 ≠ spinfulIndex N j 0 :=
        fun h => hij (spinfulIndex_up_injective N h)
      rw [Function.update_of_ne hpq] at hp0
      have hsi : s i = 2 := by
        rw [tJConfigOf_apply_up] at hp0
        have hne1 : s i ≠ 1 := fun h => by rw [if_pos h] at hp0; exact absurd hp0 (by norm_num)
        have hv := (s i).isLt
        have a0 : (s i).val ≠ 0 := fun h => (hfull i) (Fin.ext (by rw [h]; rfl))
        have a1 : (s i).val ≠ 1 := fun h => hne1 (Fin.ext (by rw [h]; rfl))
        exact Fin.ext (by omega)
      have hboth0 : (Function.update (Function.update (tJConfigOf N s) (spinfulIndex N j 0) 0)
          (spinfulIndex N i 0) 1) (spinfulIndex N i 0) = 1 := by rw [Function.update_self]
      have hboth1 : (Function.update (Function.update (tJConfigOf N s) (spinfulIndex N j 0) 0)
          (spinfulIndex N i 0) 1) (spinfulIndex N i 1) = 1 := by
        rw [Function.update_of_ne (spinfulIndex_up_ne_down N i i).symm,
          Function.update_of_ne (spinfulIndex_up_ne_down N j i).symm, tJConfigOf_apply_down,
          if_pos hsi]
      rw [basisVec_of_ne (tJConfigOf_ne_of_double N s' _ i hboth0 hboth1), mul_zero]
    · -- σ = ↓
      simp only [Fin.isValue, Fin.mk_one] at hp0 ⊢
      have hpq : spinfulIndex N i 1 ≠ spinfulIndex N j 1 :=
        fun h => hij (spinfulIndex_down_injective N h)
      rw [Function.update_of_ne hpq] at hp0
      have hsi : s i = 1 := by
        rw [tJConfigOf_apply_down] at hp0
        have hne2 : s i ≠ 2 := fun h => by rw [if_pos h] at hp0; exact absurd hp0 (by norm_num)
        have hv := (s i).isLt
        have a0 : (s i).val ≠ 0 := fun h => (hfull i) (Fin.ext (by rw [h]; rfl))
        have a2 : (s i).val ≠ 2 := fun h => hne2 (Fin.ext (by rw [h]; rfl))
        exact Fin.ext (by omega)
      have hboth1 : (Function.update (Function.update (tJConfigOf N s) (spinfulIndex N j 1) 0)
          (spinfulIndex N i 1) 1) (spinfulIndex N i 1) = 1 := by rw [Function.update_self]
      have hboth0 : (Function.update (Function.update (tJConfigOf N s) (spinfulIndex N j 1) 0)
          (spinfulIndex N i 1) 1) (spinfulIndex N i 0) = 1 := by
        rw [Function.update_of_ne (spinfulIndex_up_ne_down N i i),
          Function.update_of_ne (spinfulIndex_up_ne_down N i j), tJConfigOf_apply_up, if_pos hsi]
      rw [basisVec_of_ne (tJConfigOf_ne_of_double N s' _ i hboth0 hboth1), mul_zero]
  · rfl

/-- **The t-J kinetic term annihilates the half-filling hard-core sector.**  For a fully occupied
site state `s` (`∀ k, s k ≠ 0`, i.e. `Ne = N + 1`), `P̂hc · K · P̂hc |Φ_s⟩ = 0`: every hop lands on
an occupied site, producing a doubly occupied (non-hard-core) configuration killed by the
projection.  Hence at half-filling `Ĥ_tJ` reduces to its exchange (Heisenberg) part. -/
theorem tJ_kinetic_sandwich_mulVec_tJConfigOf_eq_zero_of_full (N : ℕ)
    (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj] (s : Fin (N + 1) → Fin 3)
    (hfull : ∀ k, s k ≠ 0) :
    (hubbardHardcoreProjection N * hubbardKineticOnGraph N G 1 *
        hubbardHardcoreProjection N).mulVec (basisVec (tJConfigOf N s)) = 0 := by
  set V := (hubbardHardcoreProjection N * hubbardKineticOnGraph N G 1 *
    hubbardHardcoreProjection N).mulVec (basisVec (tJConfigOf N s)) with hV
  have hhc : V ∈ hubbardHardcoreSubspace N := tJKinetic_sandwich_mulVec_mem N G s
  have hcount : (Finset.univ.filter (fun k => s k = 1)).card +
      (Finset.univ.filter (fun k => s k = 2)).card = N + 1 := by
    have hkey : (Finset.univ.filter (fun k => ¬ s k = 1)) =
        Finset.univ.filter (fun k => s k = 2) := by
      refine Finset.filter_congr fun k _ => ?_
      have hv := (s k).isLt
      have a0 : (s k).val ≠ 0 := fun h => (hfull k) (Fin.ext (by rw [h]; rfl))
      constructor
      · intro h1
        have a1 : (s k).val ≠ 1 := fun h => h1 (Fin.ext (by rw [h]; rfl))
        exact Fin.ext (by omega)
      · intro h2 h1; rw [h2] at h1; exact absurd h1 (by decide)
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (N + 1)))) (p := fun k => s k = 1)
    rw [hkey] at this
    rw [this]; simp
  have hN : (fermionTotalNumber (2 * N + 1)).mulVec V = ((N + 1 : ℕ) : ℂ) • V := by
    rw [hV, Matrix.mulVec_mulVec, (fermionTotalNumber_commute_tJKinetic G).eq,
      ← Matrix.mulVec_mulVec, fermionTotalNumber_mulVec_tJConfigOf_eq N s (N + 1) hcount,
      Matrix.mulVec_smul]
  funext w
  rw [Pi.zero_apply]
  by_cases hw : ∃ s' : TJFillingSector N (N + 1), tJConfigOf N s'.val = w
  · obtain ⟨s', rfl⟩ := hw
    show V (tJConfigOf N s'.val) = 0
    rw [hV, ← basisVec_sum_mul (tJConfigOf N s'.val)
        ((hubbardHardcoreProjection N * hubbardKineticOnGraph N G 1 *
          hubbardHardcoreProjection N).mulVec (basisVec (tJConfigOf N s))),
      tJKinetic_matrixElement_eq N G s s'.val, tJKinetic_matrixElement_expand N G s s'.val]
    refine Finset.sum_eq_zero fun σ _ => Finset.sum_eq_zero fun i _ =>
      Finset.sum_eq_zero fun j _ => ?_
    by_cases hij : i = j
    · subst hij; rw [couplingOf_self, zero_mul]
    · rw [basisVec_sum_mul, tJ_hop_apply_tJConfigOf_eq_zero_of_full N s s'.val hfull i j hij σ,
        mul_zero]
  · exact tJ_mulVec_apply_eq_zero_of_not_filling (N + 1) V hhc hN w hw

end LatticeSystem.Fermion
