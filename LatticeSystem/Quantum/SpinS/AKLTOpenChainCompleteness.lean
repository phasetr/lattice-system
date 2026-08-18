/-
# Tasaki §7.2.3 (Problem 7.2.3.b): the open AKLT chain has exactly four ground states

The completeness half of Problem 7.2.3: the ground space of the open `S = 1` AKLT chain is
**exactly** four-dimensional, and is spanned by the four boundary components `Φ_{pq}` of the AKLT
matrix product.  Together with the lower bound of `AKLTOpenChain.lean` (Problem 7.2.3.a) this is
the book's "the ground states are exactly four-fold degenerate": the two free `S = 1/2` spins at
the ends of the chain, and nothing else.

Two ingredients are assembled, mirroring the ring capstone `aklt_ring_ground_state_unique`.

* **Open spectral bridge** (`openGroundSpace_isVBSGroundForm`): a ground state of `Ĥ^open` lies in
  every *open* bond kernel.  The affine identity `Ĥ^open = 2 Ĥ'^open − (2/3)(L − 1)` turns the
  eigen-equation into `Ĥ'^open Ψ = 0`; frustration-freeness over the Finset `openBonds L`
  (Tasaki Lemma A.10) annihilates each bond projection, and Lemma 7.4 gives the VBS singlet form.
* **Polynomial four-dimensionality** (`weylMap_openGroundForm_eq_boundary_smul_prod`, eq. (S.77)):
  the Weyl image of any such state is a boundary quadratic times the open bond product, so the
  injective image of the ground space lies in the span of four polynomials.

The bond sum runs over `openBonds L` throughout: with the wrap bond reinstated the statement would
be the periodic one, whose ground space is one-dimensional.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.3, Problem 7.2.3.a–b, p. 207, solutions pp. 507–508 (eq. (S.77)); §7.1.3, Lemma 7.4,
pp. 186–188; proof due to Kennedy–Lieb–Tasaki [41].
-/
import LatticeSystem.Quantum.SpinS.AKLTOpenChainWeylFactorization

open MvPolynomial Matrix

namespace LatticeSystem.Quantum

open LatticeSystem.Math LatticeSystem.Quantum.AKLTUniqueness
open LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential

variable {L : ℕ}

/-- **Open spectral bridge.**  Every ground state of the open AKLT chain has the VBS
singlet-tensor form at every open bond.  The ground space is the kernel of `Ĥ'^open`
(`openAKLTGroundSpace_eq_ker`), frustration-freeness (`frustration_free_local_eigen`, Tasaki
Lemma A.10, with all local energies `0`) turns that into annihilation by each bond projection, and
Lemma 7.4 identifies each such zero mode with `IsVBSGroundForm`.  Nothing is claimed at the last
site: the open chain has no bond there. -/
theorem openGroundSpace_isVBSGroundForm (hL : 2 ≤ L) {Ψ : (Fin L → Fin 3) → ℂ}
    (hΨ : Ψ ∈ openAKLTGroundSpace L) :
    ∀ x ∈ openBonds L, IsVBSGroundForm L x Ψ := by
  rw [openAKLTGroundSpace_eq_ker (by omega), LinearMap.mem_ker, Matrix.mulVecLin_apply] at hΨ
  have hgs : (∑ x ∈ openBonds L, bondSpin2ProjectionS x (ringSucc x)).mulVec Ψ
      = ((∑ _x ∈ openBonds L, (0 : ℝ) : ℝ) : ℂ) • Ψ := by
    simpa [openProjHamiltonianS] using hΨ
  have hloc := frustration_free_local_eigen (openBonds L)
    (fun x : Fin L => bondSpin2ProjectionS x (ringSucc x)) (fun _ => (0 : ℝ)) Ψ
    (fun x _ => by simpa using bondSpin2ProjectionS_posSemidef (ne_ringSucc (by omega) x)) hgs
  intro x hx
  refine (tasaki_lemma_7_4 (by omega) x Ψ).mp ?_
  simpa using hloc x hx

/-- **Problem 7.2.3.b, the upper bound.**  The ground space of the open AKLT chain has complex
dimension at most `4`.

The Weyl map is injective, so the ground space has the same dimension as its image; eq. (S.77)
(`weylMap_openGroundForm_eq_boundary_smul_prod`) puts that image inside the span of the four
polynomials `X_{(1,a)} X_{(L,b)} · ∏_{openBonds} f_x`, and a span of four vectors has dimension at
most `4`.  This is where the per-site grading pays off: with the total-degree grading of the ring
proof the cofactor would only be known to have degree `2`, which bounds nothing. -/
theorem finrank_openAKLTGroundSpace_le_four (hL : 2 ≤ L) :
    Module.finrank ℂ (openAKLTGroundSpace L) ≤ 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 2 := ⟨L - 2, by omega⟩
  classical
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun ab : Fin 2 × Fin 2 =>
      (X ((0 : Fin (m + 2)), ab.1) * X (Fin.last (m + 1), ab.2))
        * ∏ x ∈ openBonds (m + 2), fBond x)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hmap : Submodule.map weylMap (openAKLTGroundSpace (m + 2))
      ≤ Submodule.span ℂ (Set.range fun ab : Fin 2 × Fin 2 =>
          (X ((0 : Fin (m + 2)), ab.1) * X (Fin.last (m + 1), ab.2))
            * ∏ x ∈ openBonds (m + 2), fBond x) := by
    rw [Submodule.map_le_iff_le_comap]
    intro Ψ hΨ
    obtain ⟨c, hc⟩ := weylMap_openGroundForm_eq_boundary_smul_prod Ψ
      (openGroundSpace_isVBSGroundForm (by omega) hΨ)
    rw [Submodule.mem_comap, hc, Finset.sum_mul]
    refine Submodule.sum_mem _ fun ab _ => ?_
    have hsm : C (c ab) * (X ((0 : Fin (m + 2)), ab.1) * X (Fin.last (m + 1), ab.2))
        * ∏ x ∈ openBonds (m + 2), fBond x
        = c ab • ((X ((0 : Fin (m + 2)), ab.1) * X (Fin.last (m + 1), ab.2))
            * ∏ x ∈ openBonds (m + 2), fBond x) := by
      rw [smul_eq_C_mul, mul_assoc]
    rw [hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ab, rfl⟩)
  have hcard : Module.finrank ℂ (Submodule.span ℂ (Set.range fun ab : Fin 2 × Fin 2 =>
      (X ((0 : Fin (m + 2)), ab.1) * X (Fin.last (m + 1), ab.2))
        * ∏ x ∈ openBonds (m + 2), fBond x)) ≤ 4 := by
    have h := finrank_range_le_card (R := ℂ) (fun ab : Fin 2 × Fin 2 =>
      (X ((0 : Fin (m + 2)), ab.1) * X (Fin.last (m + 1), ab.2))
        * ∏ x ∈ openBonds (m + 2), fBond x)
    rw [Set.finrank] at h
    simpa using h
  rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (weylMap (L := m + 2))
    weylMap_injective (openAKLTGroundSpace (m + 2)))]
  exact le_trans (Submodule.finrank_mono hmap) hcard

/-- **Tasaki Problem 7.2.3.b (1st ed., 2020, p. 207; solution (S.77), p. 508), PROVED.**  The
ground space of the open `S = 1` AKLT chain of `L ≥ 2` sites has complex dimension exactly `4`:
the four boundary components `Φ_{pq}` of the matrix-product state are independent ground states
(Problem 7.2.3.a) and there are no others (this file).  Physically the degeneracy is carried by
the two free `S = 1/2` spins dangling at the ends of the open chain — the hallmark of the
Haldane-phase valence-bond-solid picture — in contrast with the unique ground state of the
periodic chain (`aklt_ring_ground_state_unique`). -/
theorem finrank_openAKLTGroundSpace_eq_four (hL : 2 ≤ L) :
    Module.finrank ℂ (openAKLTGroundSpace L) = 4 :=
  le_antisymm (finrank_openAKLTGroundSpace_le_four hL)
    (four_le_finrank_openAKLTGroundSpace hL)

/-- **The literal book claim**: every ground state of the open AKLT chain is a linear combination
of the four boundary components `Φ_{pq}` (eq. (S.77) read back through the Weyl map).  This
strengthens the numerical statement `dim = 4` to an explicit description of the ground space; the
four states are independent but **not** orthogonal. -/
theorem openAKLTGroundSpace_eq_span_openVBSState (hL : 2 ≤ L) :
    openAKLTGroundSpace L
      = Submodule.span ℂ (Set.range fun r : Fin 2 × Fin 2 => openVBSState L r.1 r.2) :=
  (Submodule.eq_of_le_of_finrank_le (span_openVBSState_le_openAKLTGroundSpace hL)
    (le_of_eq (by
      rw [finrank_openAKLTGroundSpace_eq_four hL, finrank_span_openVBSState hL]))).symm

end LatticeSystem.Quantum
