import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardFerromagnetismStructure
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowUTrial
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJAllUpProperties
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Tasaki §11.1.1: impossibility of ferromagnetism for small `U` (Theorem 11.3)

For the all-to-all Hubbard model with a Hermitian hopping matrix `t`, ferromagnetism is impossible
when the on-site repulsion `U` is smaller than the single-particle Fermi gap.  Tasaki's
variational argument (the trial state (11.1.6), a single spin flip in the lowest single-particle
level) shows the all-up Slater state is not the unique ground state once `U < ε_N − ε_1`.

This file builds the **single-particle spectrum** of the hopping matrix (its Hermitian eigenvalues)
and the **Fermi gap** (here, at the project's half-filling convention `N + 1` electrons in `N + 1`
sites, the full bandwidth `max ε − min ε`), and records **Theorem 11.3** as a documented axiom (the
variational discharge, which needs the single-particle eigenbasis fermion operators, is deferred).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.1.1, Theorem 11.3, eqs. (11.1.5)–(11.1.6), pp. 378–379.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module

variable {N : ℕ} (t : Fin (N + 1) → Fin (N + 1) → ℂ)

/-- **The single-particle energies** of the hopping matrix `t`: the (real) Hermitian eigenvalues
`{ε_j}` of `t`.  These are the energies of the one-electron eigenstates that the Slater-determinant
ground states fill. -/
noncomputable def hubbardSingleParticleEnergies (ht : Matrix.IsHermitian t) :
    Fin (N + 1) → ℝ :=
  ht.eigenvalues

/-- **The single-particle Fermi gap** of `t` at the half-filling convention (`N + 1` electrons fully
occupying the `N + 1` one-electron levels): the bandwidth `max_j ε_j − min_j ε_j`.  This is the
quantity `ε_N − ε_1` of Tasaki's Theorem 11.3 specialised to the completely filled up-band — the
energy cost of the lowest single spin flip. -/
noncomputable def hubbardFermiGap (ht : Matrix.IsHermitian t) :
    ℝ :=
  Finset.univ.sup' Finset.univ_nonempty ht.eigenvalues -
    Finset.univ.inf' Finset.univ_nonempty ht.eigenvalues

/-! ## Step 1–2: the all-up state is the ground state with energy `Tr t` -/

/-- **A top-weight, `(N+1)`-electron vector is a scalar multiple of the all-up state.**  If
`N̂ v = (N+1) v` and `Ŝ³ v = ((N+1)/2) v`, then `v = (v c_allUp) • |↑…↑⟩`, where `c_allUp` is the
all-up configuration.  Every supported configuration `w` of such a `v` has `N + 1` electrons and
`Ŝ³` count `(N+1)/2`, forcing `N̂_↑ = N+1` and `N̂_↓ = 0`, i.e. `w` is the all-up configuration. -/
theorem topWeight_eq_smul_hubbardAllUpState
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hN : (fermionTotalNumber (2 * N + 1)).mulVec v = ((N + 1 : ℕ) : ℂ) • v)
    (hZ : (fermionTotalSpinZ N).mulVec v = ((((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) • v) :
    v = (v (fun k : Fin (2 * N + 2) => if k.val % 2 = 0 then 1 else 0)) •
      hubbardAllUpState N := by
  set cAllUp : Fin (2 * N + 2) → Fin 2 := fun k => if k.val % 2 = 0 then 1 else 0 with hcAllUp
  funext w
  rw [Pi.smul_apply, smul_eq_mul, hubbardAllUpState]
  by_cases hwAllUp : w = cAllUp
  · rw [hwAllUp, basisVec_self, mul_one]
  · rw [basisVec_of_ne hwAllUp, mul_zero]
    by_cases hNum : (∑ j : Fin (2 * N + 2), ((w j).val : ℂ)) = ((N + 1 : ℕ) : ℂ)
    · refine mulVec_apply_eq_zero_of_spinZ_ne v
        ((((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) hZ w (fun hcount => ?_)
      set aup : ℕ := ∑ i : Fin (N + 1), (w (spinfulIndex N i 0)).val with haup
      set adown : ℕ := ∑ i : Fin (N + 1), (w (spinfulIndex N i 1)).val with hadown
      have hupC : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ)) = (aup : ℂ) := by
        rw [haup, Nat.cast_sum]
      have hdownC : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 1)).val : ℂ)) = (adown : ℂ) := by
        rw [hadown, Nat.cast_sum]
      have hreindex : (∑ j : Fin (2 * N + 2), ((w j).val : ℂ)) = (aup : ℂ) + (adown : ℂ) := by
        rw [sum_spinful_reindex N (fun k => ((w k).val : ℂ)),
          Finset.sum_congr rfl
            (fun i _ => Fin.sum_univ_two (fun r => ((w (spinfulIndex N i r)).val : ℂ))),
          Finset.sum_add_distrib, hupC, hdownC]
      have hsumC : (aup : ℂ) + (adown : ℂ) = ((N + 1 : ℕ) : ℂ) := by rw [← hreindex]; exact hNum
      have hsumN : aup + adown = N + 1 := by exact_mod_cast hsumC
      have hcountC : ((aup : ℂ) - (adown : ℂ)) / 2 = ((((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) := by
        rw [← hupC, ← hdownC]; exact hcount
      have hdiffN : aup = N + 1 ∧ adown = 0 := by
        have hhalf : (((((N + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) = ((N + 1 : ℕ) : ℂ) / 2 := by
          push_cast; ring
        have hdiffC : (aup : ℂ) - (adown : ℂ) = ((N + 1 : ℕ) : ℂ) := by
          have hc2 : (aup : ℂ) - (adown : ℂ) = 2 * (((aup : ℂ) - (adown : ℂ)) / 2) := by ring
          rw [hc2, hcountC, hhalf]; ring
        have : (aup : ℤ) - (adown : ℤ) = (N + 1 : ℤ) := by exact_mod_cast hdiffC
        omega
      refine absurd ?_ hwAllUp
      rw [hcAllUp]
      exact hubbardImpossibilityLowU_config_eq_allUp w (haup ▸ hdiffN.1) (hadown ▸ hdiffN.2)
    · exact mulVec_apply_eq_zero_of_number_ne N v ((N + 1 : ℕ) : ℂ) hN w hNum

/-- **The all-up state lies in a nonzero maximal-spin ground eigenspace.**  If `G ≠ ⊥` (`hne`) and
every ground state is maximal-spin (`hferro`), then the all-up Slater state `|↑…↑⟩` lies in `G`.
The top `Ŝ³`-weight block of `G` is nonzero (every block embeds via `Ŝ⁺` into the next-higher one,
so the top block dominates the nonzero block guaranteed by `G ≠ ⊥`); a nonzero top-weight vector is
a scalar multiple of `|↑…↑⟩` (`topWeight_eq_smul_hubbardAllUpState`), so `|↑…↑⟩ ∈ G`. -/
theorem hubbardAllUpState_mem_of_maxSpin {E₀ : ℂ}
    (hne : hubbardEigenspaceAtFilling t (U : ℂ) E₀ ≠ ⊥)
    (hferro : ∀ v ∈ hubbardEigenspaceAtFilling t (U : ℂ) E₀,
      (fermionTotalSpinSquared N).mulVec v
        = (((N + 1 : ℕ) : ℂ) / 2 * (((N + 1 : ℕ) : ℂ) / 2 + 1)) • v) :
    hubbardAllUpState N ∈ hubbardEigenspaceAtFilling t (U : ℂ) E₀ := by
  classical
  set G := hubbardEigenspaceAtFilling t (U : ℂ) E₀ with hG
  -- the top block is nonzero: some block is nonzero (`G ≠ ⊥`), and every block embeds into the top
  have htopBlockNe : (G ⊓ Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
      ((((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) ≠ ⊥ := by
    intro htopbot
    have hallbot : ∀ a : Fin (N + 1 + 1), (G ⊓ Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
        ((((a : ℝ) - ((N + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ)) = ⊥ := by
      intro a
      rw [← Submodule.finrank_eq_zero]
      have htop0 : finrank ℂ ↥(G ⊓ Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
          ((((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) = 0 := by
        rw [Submodule.finrank_eq_zero]; exact htopbot
      have hchain : ∀ j : ℕ, j ≤ N + 1 →
          finrank ℂ ↥(G ⊓ Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
            (((((N + 1 - j : ℕ) : ℝ)) - ((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) ≤
          finrank ℂ ↥(G ⊓ Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
            ((((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) := by
        intro j
        induction j with
        | zero => intro _; rw [show (((N + 1 - 0 : ℕ) : ℝ) - ((N + 1 : ℕ) : ℝ) / 2)
            = (((N + 1 : ℕ) : ℝ) / 2 : ℝ) from by push_cast; ring]
        | succ j ih =>
          intro hj
          have hjle : j ≤ N + 1 := Nat.le_of_succ_le hj
          have hstep := hubbardEigenspaceAtFilling_block_finrank_le_succ t (U : ℂ) hferro
            (N + 1 - (j + 1)) (by omega)
          have hnat : N + 1 - (j + 1) + 1 = N + 1 - j := by omega
          have hc : ((N + 1 - (j + 1) : ℕ) : ℝ) + 1 = ((N + 1 - j : ℕ) : ℝ) := by
            rw [← hnat]; push_cast; ring
          rw [hc] at hstep
          exact le_trans hstep (ih hjle)
      have hja : (a : ℕ) ≤ N + 1 := Nat.lt_succ_iff.mp a.isLt
      have := hchain (N + 1 - (a : ℕ)) (Nat.sub_le _ _)
      rw [show ((N + 1 - (N + 1 - (a : ℕ)) : ℕ) : ℝ) = ((a : ℕ) : ℝ) from by
        rw [Nat.sub_sub_self hja], htop0, Nat.le_zero] at this
      exact this
    refine hne ?_
    rw [hG, hubbardEigenspaceAtFilling_eq_iSup_weight t (U : ℂ)]
    refine le_antisymm (iSup_le (fun a => ?_)) bot_le
    rw [← hG]
    exact (hallbot a).le
  obtain ⟨u, hutop, hune⟩ := Submodule.exists_mem_ne_zero_of_ne_bot htopBlockNe
  have huG : u ∈ G := (Submodule.mem_inf.mp hutop).1
  have huN : (fermionTotalNumber (2 * N + 1)).mulVec u = ((N + 1 : ℕ) : ℂ) • u :=
    ((mem_hubbardEigenspaceAtFilling t (U : ℂ)).mp huG).2
  have huZ : (fermionTotalSpinZ N).mulVec u = ((((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) • u := by
    have := (Submodule.mem_inf.mp hutop).2
    rwa [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at this
  -- `u = (u cAllUp) • allUp`, and `u ≠ 0`, so `u cAllUp ≠ 0`, so `allUp ∈ G`.
  have hueq := topWeight_eq_smul_hubbardAllUpState huN huZ
  set c : ℂ := u (fun k : Fin (2 * N + 2) => if k.val % 2 = 0 then 1 else 0) with hc
  have hcne : c ≠ 0 := by
    intro hc0
    apply hune
    rw [hueq, hc0, zero_smul]
  have : hubbardAllUpState N = c⁻¹ • u := by
    rw [hueq]; rw [smul_smul, inv_mul_cancel₀ hcne, one_smul]
  rw [hG]
  rw [show hubbardAllUpState N = c⁻¹ • u from this]
  exact Submodule.smul_mem _ _ huG

/-- **The all-up ground energy is the hopping trace.**  If `|↑…↑⟩ ∈ G`, then since
`Ĥ |↑…↑⟩ = (∑ t i i) |↑…↑⟩` and `Ĥ |↑…↑⟩ = E₀ |↑…↑⟩` with `|↑…↑⟩ ≠ 0`, the ground energy is
`E₀ = ∑ i, t i i`, the trace of the hopping matrix (a real number, since `t` is Hermitian). -/
theorem hubbard_groundEnergy_eq_trace {E₀ : ℂ}
    (hmem : hubbardAllUpState N ∈ hubbardEigenspaceAtFilling t (U : ℂ) E₀) :
    E₀ = ∑ i : Fin (N + 1), t i i := by
  have hH : (hubbardHamiltonian N t (U : ℂ)).mulVec (hubbardAllUpState N)
      = E₀ • hubbardAllUpState N :=
    ((mem_hubbardEigenspaceAtFilling t (U : ℂ)).mp hmem).1
  rw [hubbardHamiltonian_mulVec_allUpState_eigenstate] at hH
  have hne : hubbardAllUpState N ≠ 0 := hubbardAllUpState_ne_zero N
  have hsub : ((∑ i : Fin (N + 1), t i i) - E₀) • hubbardAllUpState N = 0 := by
    rw [sub_smul, hH, sub_self]
  rcases smul_eq_zero.mp hsub with h | h
  · exact (sub_eq_zero.mp h).symm
  · exact absurd h hne

/-- **Tasaki Theorem 11.3 (impossibility of ferromagnetism for small `U`), AXIOM.**  Let `E₀` be the
genuine half-filling (`N + 1`-electron) ground energy of the Hubbard model with Hermitian hopping
`t`: its eigenspace is nonzero (`hne`) and `E₀` is minimal among energies with a nonzero
`(N + 1)`-electron eigenspace (`hmin`).  If `0 ≤ U` is strictly below the single-particle Fermi gap
`hubbardFermiGap`, then the ground states are **not** all maximal-spin: some ground state has
`S_tot < S_max`, so the
model is not saturated-ferromagnetic.

The conclusion negates the *pinned* ground-state max-spin property (over
`hubbardEigenspaceAtFilling` at the real ground energy `E₀`), not the vacuously-satisfiable
`isSaturatedFerromagnet`, so the
impossibility statement is sound.

Tasaki's proof: the trial state `|Ψ⟩ = ĉ†_{1,↓} ∏_{j=1}^{N-1} ĉ†_{j,↑}|0⟩` (eq. (11.1.6), one spin
flipped into the lowest single-particle level) has energy `E_ferro − (ε_N − ε_1) + U·‖…‖²`, strictly
below `E_ferro` when `U < ε_N − ε_1`, so the maximal-spin all-up state is not the ground state.  The
variational estimate uses the single-particle eigenbasis fermion operators; it is finite-dimensional
but needs that eigenbasis machinery, so it is recorded here as a documented axiom (to be
discharged), matching the policy for the other deferred Chapter 11 results. -/
axiom hubbard_theorem_11_3
    (ht : Matrix.IsHermitian t) (U : ℝ) (E₀ : ℂ)
    (hne : hubbardEigenspaceAtFilling t (U : ℂ) E₀ ≠ ⊥)
    (hmin : ∀ E : ℂ, hubbardEigenspaceAtFilling t (U : ℂ) E ≠ ⊥ → E₀.re ≤ E.re)
    (hU0 : 0 ≤ U) (hUlt : U < hubbardFermiGap t ht) :
    ¬ ∀ v ∈ hubbardEigenspaceAtFilling t (U : ℂ) E₀,
      (fermionTotalSpinSquared N).mulVec v
        = (((N + 1 : ℕ) : ℂ) / 2 * (((N + 1 : ℕ) : ℂ) / 2 + 1)) • v

end LatticeSystem.Fermion
