import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSMLMEndpoint
import LatticeSystem.Quantum.SpinS.Theorem22Connected
import LatticeSystem.Quantum.SpinS.HermitianGroundStateEigenvalue

/-!
# General spin-S Theorem 2.4 SU(2) boundary endpoint

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

This file exposes the explicit general spin-`S` target endpoint at the SU(2)
point `(lambda, D) = (1, 0)`.  The proof is the direct Heisenberg-to-anisotropic
transport already used by the strict and boundary deformation wrappers, but
without any deformation path or parity-block irreducibility input.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorems 2.3--2.4, pp. 42--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- General spin-`S` target uniqueness at the SU(2) point `(lambda, D) = (1, 0)`
from the Theorem 2.3 MLM/Casimir/Perron-Frobenius endpoint. -/
theorem aHeisS_target_finrank_le_one_of_MLM_casLadder_t23_pf_lam1_D_zero_gen
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (Λ → Fin (N + 1))]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
          ℝ) : ℂ)) ≤ 1 := by
  classical
  have hJ_bipartite_zero : ∀ x y, A x = A y → J x y = 0 := by
    intro x y hAxy
    by_contra hJxy_ne
    exact (hJbip x y hJxy_ne) hAxy
  have hcardA : 1 ≤ (Finset.univ.filter (fun x : Λ => A x = true)).card := by
    obtain ⟨a, ha⟩ := hA_ne
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨a, by simp [ha]⟩)
  have hcardB : 1 ≤ (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
    obtain ⟨b, hb⟩ := hB_ne
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨b, by simp [hb]⟩)
  obtain ⟨μ, hμ_min, _hsectors, huniq_heis⟩ :=
    exists_t23_commonE_and_heisHamS_fullEig_finrank_le_one_of_casLadder_t23_pf
      (V := Λ) A N c_mlm c_toy hT23 hJim hJ_star hJ_sym hJnn hJ_bipartite_zero
      hJpos hc_heis_strict hc_toy_strict h_card_eq hN hcardA hcardB
  exact anisotropicHeisenbergS_SU2_ground_eigenspace_finrank_le_one_of_heisenberg_general
    (Λ := Λ) (N := N) hJ_star hμ_min huniq_heis

/-- General spin-`S` zero total `S^3` magnetization at the SU(2) point
`(lambda, D) = (1, 0)` from the Theorem 2.3 MLM/Casimir/Perron-Frobenius
endpoint. -/
theorem aHeisS_target_zeroMag_of_MLM_casLadder_t23_pf_lam1_D_zero_gen
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (Λ → Fin (N + 1))]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (Φ : (Λ → Fin (N + 1)) → ℂ)
    (hΦ_ne : Φ ≠ 0)
    (hΦ_eig :
      (anisotropicHeisenbergS J 1 0 N).mulVec Φ =
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
            ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
  classical
  have huniq :=
    aHeisS_target_finrank_le_one_of_MLM_casLadder_t23_pf_lam1_D_zero_gen
      A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (Λ := Λ) (N := N) J 1 0
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
        ℝ) : ℂ)
    huniq hΦ_ne hΦ_eig

/-! ## Connected-graph SU(2) endpoints -/

/-- **Connected-graph target uniqueness at the SU(2) point `(lambda, D) = (1, 0)`**.

The analogue of `aHeisS_target_finrank_le_one_of_MLM_casLadder_t23_pf_lam1_D_zero_gen` for an
arbitrary connected graph `G`: the fixed graph `bipartiteCompleteGraphOf A` and the
Theorem 2.3 package (`hT23` together with its two diagonal-shift scalars `c_mlm`, `c_toy` and
the sublattice non-emptiness `hA_ne`/`hB_ne`) are replaced by `hGconn`, the sign gauge
`hGbip`, edge positivity `hJ_pos_G`, and the support condition `hJ_off`.

At `(lambda, D) = (1, 0)` the anisotropic Hamiltonian is the Heisenberg one, so the ground
eigenspace bound is the Marshall--Lieb--Mattis conclusion of
`tasaki_2_5_theorem_2_2_of_connected` (Tasaki §2.5 Theorem 2.2, p. 39) transported by
`anisotropicHeisenbergS_SU2_ground_eigenspace_finrank_le_one_of_heisenberg_general`.  That
transport is phrased at `hermitianMinEigenvalue`, whereas Theorem 2.2 produces an energy `μ`
described by two clauses instead: it is a lower bound for every eigenvalue, and it is attained
by the Marshall-signed sector vector.  The two descriptions are identified here by
antisymmetry — `hermitianMinEigenvalue_le_re_of_eigenpair` applied to that vector
(non-zero by `tasaki23_marshallPositive_magSectorEmbedding_ne_zero`, its coefficients being
strictly positive) gives one inequality, and the lower-bound clause applied to the eigenvector
of `exists_nonzero_eigenvector_hermitianMinEigenvalue` gives the other. -/
theorem aHeisS_target_finrank_le_one_lam1_D_zero_of_connected
    (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hGconn : G.Connected) (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJ_off : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hN : 1 ≤ N)
    [Nonempty (Λ → Fin (N + 1))]
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
          ℝ) : ℂ)) ≤ 1 := by
  classical
  have hJ_bipartite : ∀ x y, A x = A y → J x y = 0 := by
    intro x y hAxy
    by_contra hJxy_ne
    exact (hJbip x y hJxy_ne) hAxy
  obtain ⟨μ, huniq_heis, hlower, v, hv_pos, hv_eig, -⟩ :=
    tasaki_2_5_theorem_2_2_of_connected A G N hGconn hGbip h_card_eq hN hJim hJ_star hJ_sym
      hJnn hJ_bipartite hJ_pos_G hJ_off
  haveI : Nonempty (magConfigS Λ N
      ((Finset.univ.filter (fun x : Λ => A x = true)).card * N)) := by
    refine magConfigS_nonempty_of_le_card_mul (Nat.mul_le_mul ?_ (le_refl N))
    simpa [Finset.card_univ] using
      Finset.card_filter_le (Finset.univ : Finset Λ) (fun x : Λ => A x = true)
  have hHerm := heisenbergHamiltonianS_isHermitian_of_real (Λ := Λ) hJ_star N
  have hmin_le : hermitianMinEigenvalue hHerm ≤ μ := by
    simpa using hermitianMinEigenvalue_le_re_of_eigenpair hHerm
      (tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos) hv_eig
  have hmin_ge : μ ≤ hermitianMinEigenvalue hHerm := by
    obtain ⟨w, hw_ne, hw_eig⟩ := exists_nonzero_eigenvector_hermitianMinEigenvalue hHerm
    exact hlower hw_ne hw_eig
  exact anisotropicHeisenbergS_SU2_ground_eigenspace_finrank_le_one_of_heisenberg_general
    (Λ := Λ) (N := N) hJ_star (le_antisymm hmin_le hmin_ge) huniq_heis

/-- **Connected-graph zero total `S^3` magnetization at the SU(2) point
`(lambda, D) = (1, 0)`**.  The analogue of
`aHeisS_target_zeroMag_of_MLM_casLadder_t23_pf_lam1_D_zero_gen` at an arbitrary connected
graph `G`: the uniqueness endpoint above feeds
`anisotropicHeisenbergS_unique_groundState_has_zero_magnetization`, which turns a
one-dimensional ground eigenspace into `Ŝ³_tot |Φ⟩ = 0` for every non-zero ground state. -/
theorem aHeisS_target_zeroMag_lam1_D_zero_of_connected
    (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hGconn : G.Connected) (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJ_off : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hN : 1 ≤ N)
    [Nonempty (Λ → Fin (N + 1))]
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (Φ : (Λ → Fin (N + 1)) → ℂ)
    (hΦ_ne : Φ ≠ 0)
    (hΦ_eig :
      (anisotropicHeisenbergS J 1 0 N).mulVec Φ =
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
            ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
  classical
  have huniq :=
    aHeisS_target_finrank_le_one_lam1_D_zero_of_connected
      A G hGconn hGbip hJim hJnn hJ_pos_G hJ_off hJbip hJ_star hJ_sym hN h_card_eq
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (Λ := Λ) (N := N) J 1 0
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
        ℝ) : ℂ)
    huniq hΦ_ne hΦ_eig

end LatticeSystem.Quantum
