import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaSector
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaConjugation
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveTheorem102
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveTheorem103

/-!
# Lieb's theorem, symmetric repulsive Hubbard model, spin-`z` sectors (Tasaki §10.2.2, Thm 10.4)

Final assembly (c7) of the axiom-free portion of **Tasaki Theorem 10.4** (Lieb's theorem for the
repulsive Hubbard model), Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.2, pp. 350–352.

For an odd number of sites `N`, a connected real symmetric hopping `T` that respects a bipartition
and on-site repulsion `U_x > 0`, the symmetric (`μ = U/2`) repulsive Hubbard Hamiltonian
`Ĥ^{rep,sym}` has a **unique** ground state on each **balanced spin-`z` sector** `Ŝ³ = m`, where
`m = (Ne − (N+1))/2` is fixed by an even electron number `0 < Ne < 2(N+1)`.  This is obtained by
**transporting** the attractive-model number-sector result (Theorem 10.2) through the Shiba unitary
`Û`.  This general spin-`z`-sector uniqueness `repulsiveSpinZSector_ground_unique` is what
Theorem 10.5 (Shen–Qiu–Tian) consumes; the half-filling / balanced case `Ne = N+1` (so `m = 0`) is
the special case `Ne = N + 1`.

## The transport

The Shiba unitary conjugation (c6, eq. (10.2.10)) gives
`Ûᴴ Ĥ^{rep,sym} Û = Ĥ^{attr}(T + diag(U/2)) − ¼(∑ U) · 1`,
and the Shiba flip **exchanges** the number and spin-`z` charges
(`shibaSignedUnitary_conj_totalNumber` / `_conj_totalSpinZ`):
`Û N̂ Ûᴴ = 2 Ŝ³ + (N+1)·1` and `Ûᴴ Ŝ³ Û = ½(N̂ − (N+1)·1)`.  Consequently the attractive-model
**number** sector `N̂ = Ne` (Theorem 10.2's `electronNumberSectorEuclidean N Ne`, unique ground
state `φ_attr`, energy `E_attr`) transports to the repulsive-model **spin-`z`** sector
`Ŝ³ = (Ne − (N+1))/2`, and `ψ := Û φ_attr` is the unique ground state there with energy
`E := E_attr − ¼(∑ U)`.  (These charge exchanges are pure operator identities, independent of the
sector; only the scalars `Ne`/`m` change.)

Because `Û` maps the spin SU(2) algebra to the η-pseudospin algebra (`Û Ŝ² Ûᴴ ≠ Ŝ²`), the
attractive singlet is **not** transported to a spin singlet; identifying the repulsive total-spin
value needs the (finite-dimensional) degenerate perturbation theory of Lemma 10.1
(`tasaki_lemma_10_1_degenerate_perturbation`, itself proved axiom-free).  Accordingly this capstone
claims the spin-`z`-sector ground-state uniqueness together with the half-filling number eigenvalue
`N̂ φ = (N+1)·φ`, but no total-spin value.  Half-integer `m` (odd `Ne`) is out of scope:
Theorem 10.2 requires `Even Ne`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2 (Theorem 10.4), eqs. (10.2.10)/(10.2.11), pp. 350–352; E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix Module Module.End LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators

variable {N : ℕ}

/-- The **balanced spin-`z` sector** `Ŝ³ = m`, as a subspace of the `EuclideanSpace` of
computational configurations: the `m`-eigenspace of the total spin-`z` operator `Ŝ³`.  The `m = 0`
case is the balanced (`N̂_↑ = N̂_↓`) sector. -/
noncomputable def spinZSectorEuclidean (N : ℕ) (m : ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :=
  Module.End.eigenspace (Matrix.toEuclideanLin (fermionTotalSpinZ N)) m

/-- **The hopping support graph ignores a diagonal shift**:
`hoppingSupportGraph (T + diagonal d) = hoppingSupportGraph T`.  The support graph relates only
distinct vertices, and adding a diagonal changes no off-diagonal entry. -/
theorem hoppingSupportGraph_add_diagonal (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (d : Fin (N + 1) → ℝ) :
    hoppingSupportGraph (T + Matrix.diagonal d) = hoppingSupportGraph T := by
  ext x y
  simp only [hoppingSupportGraph, SimpleGraph.fromRel_adj, Matrix.add_apply, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · simp [hxy]
  · rw [if_neg hxy, if_neg (Ne.symm hxy), add_zero, add_zero]

/-- **Tasaki Theorem 10.4** (Lieb's theorem for the symmetric repulsive Hubbard model, general
spin-`z` sector; 1st ed., Springer 2020, §10.2.2, pp. 350–352; **PROVED**, no axiom).  For any
number of sites `N`, an even electron number `0 < Ne < 2(N+1)`, a connected real symmetric hopping
`T` respecting a bipartition `A`, and on-site repulsion `U_x > 0`, the symmetric (`μ = U/2`)
repulsive Hubbard Hamiltonian `Ĥ^{rep,sym}` has a **unique** ground state on the spin-`z` sector
`Ŝ³ = m` with `m = (Ne − (N+1))/2`.

The total-spin value is **not** claimed: the Shiba unitary sends `Ŝ²` to the η-pseudospin Casimir,
so identifying the repulsive total spin needs the (finite-dimensional) degenerate perturbation
theory of Lemma 10.1 (`tasaki_lemma_10_1_degenerate_perturbation`, proved axiom-free).

Proof: transport the attractive-model number-sector unique ground state (Theorem 10.2,
`theorem_10_2_lieb_attractive_unique_singlet`, applied to `T + diag(U/2)` with electron number
`Ne`) through the Shiba unitary `Û`, using the conjugation
`Ûᴴ Ĥ^{rep,sym} Û = Ĥ^{attr} − ¼(∑ U)·1` (c6, eq. (10.2.10)) and the charge exchange
`Û N̂ Ûᴴ = 2 Ŝ³ + (N+1)·1` / `Ûᴴ Ŝ³ Û = ½(N̂ − (N+1)·1)`.  Under this exchange the number
eigenvalue `Ne` becomes the spin-`z` eigenvalue `m = (Ne − (N+1))/2` (eq. (10.2.11)).

The transported ground state `φ = Û φ_attr` is exposed via `φ.ofLp = Û φ_attr.ofLp` together
with Theorem 10.3's pair-transfer positivity of the underlying attractive ground state `φ_attr`;
this is what Theorem 10.5 (Shen–Qiu–Tian) consumes on the general spin-`z` sector `Ŝ³ = m`.

**Number-operator eigenvalue (PR-1 extension).** Because Theorem 10.2's attractive ground state
`φ_attr` is a spin singlet (`Ŝ² φ_attr = 0`), its spin-`z` eigenvalue is forced to `0`
(`Ŝ³ φ_attr = 0`); transporting this through the Shiba charge exchange
(`Û N̂ Ûᴴ = Ûᴴ N̂ Û = 2 Ŝ³ + (N+1)·1`; the two conjugation orders agree because the Shiba flip is
an **involution** — `shibaPermMatrix` is Hermitian with `P · P = 1`, so the diagonal `N̂` is
reindexed by the *same* map `shibaConfig` either way, the modulus-one sign dressing cancelling in
both orders) gives
`N̂ φ = (N+1) · φ`: **every** transported ground state, on **every** spin-`z` sector `Ŝ³ = m`,
sits in the fixed `(N+1)`-electron (half-filling) sector, independently of the electron number
`Ne` used to select the attractive-model sector it is transported from.  (Note: this is `N+1`,
**not** `Ne` — the two coincide only in the special case `Ne = N+1`.) -/
theorem repulsiveSpinZSector_ground_unique (N Ne : ℕ)
    (hNe_even : Even Ne) (hNe_pos : 0 < Ne) (hNe_lt : Ne < 2 * (N + 1))
    {A : Finset (Fin (N + 1))} (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT_symm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x) :
    ∃ (E : ℝ) (φ φattr : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)),
      IsUniqueGroundStateOn
          (spinZSectorEuclidean N (((Ne : ℂ) - ((N : ℂ) + 1)) / 2))
          (symmetricRepulsiveHubbardHamiltonian N T U) E φ ∧
        φ.ofLp = (shibaSignedUnitary N (shibaSignFn A)).mulVec φattr.ofLp ∧
        (∀ x y : Fin (N + 1),
          0 < (euclideanExpectation (hubbardPairCorrelationOp N x y) φattr).re ∧
            (euclideanExpectation (hubbardPairCorrelationOp N x y) φattr).im = 0) ∧
        Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) φ = ((N : ℂ) + 1) • φ := by
  classical
  -- Abbreviations for the Shiba unitary, the two Hamiltonians and the scalar shift.
  set Ush : Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ :=
    shibaSignedUnitary N (shibaSignFn A) with hUsh
  set Hrep : ManyBodyOp (Fin (2 * N + 2)) := symmetricRepulsiveHubbardHamiltonian N T U with hHrep
  set T' : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := T + Matrix.diagonal (fun x => U x / 2) with hT'
  set Hattr : ManyBodyOp (Fin (2 * N + 2)) := attractiveHubbardHamiltonian N T' U with hHattrDef
  set cR : ℝ := (∑ x : Fin (N + 1), U x) / 4 with hcR
  -- The spin-`z` eigenvalue `m = (Ne − (N+1))/2` fixed by the electron number `Ne` (eq. (10.2.11)).
  set mVal : ℂ := ((Ne : ℂ) - ((N : ℂ) + 1)) / 2 with hmVal
  -- The number/spin-`z` conversion `2·m + (N+1) = Ne`.
  have hNeval : (2 : ℂ) * mVal + ((N : ℂ) + 1) = ((Ne : ℕ) : ℂ) := by
    rw [hmVal]; ring
  have hs : ∀ c, star (shibaSignFn A c) * shibaSignFn A c = 1 := shibaSignFn_star_mul_self A
  -- Unitarity of `Û`.
  have hUU : Matrix.conjTranspose Ush * Ush = 1 :=
    shibaSignedUnitary_conjTranspose_mul_self (shibaSignFn A) hs
  have hUUc : Ush * Matrix.conjTranspose Ush = 1 :=
    shibaSignedUnitary_self_mul_conjTranspose (shibaSignFn A) hs
  -- The Shiba conjugation `Ûᴴ Ĥ^{rep} Û = Ĥ^{attr} − cR·1` (c6, eq. (10.2.10)).
  have hκ : ((∑ x : Fin (N + 1), (U x : ℂ)) / 4) = (cR : ℂ) := by rw [hcR]; push_cast; ring
  have hconj : Matrix.conjTranspose Ush * Hrep * Ush = Hattr - (cR : ℂ) • 1 := by
    rw [hUsh, hHrep, hHattrDef, hT',
      shibaSignedUnitary_conj_symmetricRepulsive_eq_attractive hT_symm hbip U, hκ]
  -- `Ĥ^{rep} Û = Û (Ĥ^{attr} − cR·1)` and `Ĥ^{attr} = Ûᴴ Ĥ^{rep} Û + cR·1`.
  have hHrepU : Hrep * Ush = Ush * (Hattr - (cR : ℂ) • 1) := by
    rw [← hconj, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUUc, Matrix.one_mul]
  have hHattr : Hattr = Matrix.conjTranspose Ush * Hrep * Ush + (cR : ℂ) • 1 := by
    rw [hconj]; abel
  -- `Ĥ^{attr} Ûᴴ = Ûᴴ Ĥ^{rep} + cR·Ûᴴ`.
  have hHU : Hattr * Matrix.conjTranspose Ush
      = Matrix.conjTranspose Ush * Hrep + (cR : ℂ) • Matrix.conjTranspose Ush := by
    rw [hHattr, Matrix.add_mul, Matrix.mul_assoc, hUUc, Matrix.mul_one, Matrix.smul_mul,
      Matrix.one_mul]
  -- `N̂ Ûᴴ = Ûᴴ (2 Ŝ³ + (N+1)·1)` from the number/spin-z exchange (I1).
  have hNU : fermionTotalNumber (2 * N + 1) * Matrix.conjTranspose Ush
      = Matrix.conjTranspose Ush
          * ((2 : ℂ) • fermionTotalSpinZ N + ((N : ℂ) + 1) • 1) := by
    rw [← shibaSignedUnitary_conj_totalNumber (shibaSignFn A) hs, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  -- Forward/reverse bridges between `mulVec` and `toEuclideanLin`.
  have fwd : ∀ (M : Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ) (e : ℂ)
      (x : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)),
      M.mulVec x.ofLp = e • x.ofLp → Matrix.toEuclideanLin M x = e • x := by
    intro M e x h
    apply WithLp.ofLp_injective (p := 2) (V := (Fin (2 * N + 2) → Fin 2) → ℂ)
    change M.mulVec x.ofLp = e • x.ofLp
    exact h
  have bwd : ∀ (M : Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ) (e : ℂ)
      (x : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)),
      Matrix.toEuclideanLin M x = e • x → M.mulVec x.ofLp = e • x.ofLp := by
    intro M e x h
    have := congrArg WithLp.ofLp h
    simpa using this
  -- Apply Theorem 10.2 to the shifted hopping `T' = T + diag(U/2)` at electron number `Ne`.
  have hT'_symm : ∀ x y, T' x y = T' y x := by
    intro x y
    rw [hT', Matrix.add_apply, Matrix.add_apply, Matrix.diagonal_apply, Matrix.diagonal_apply,
      hT_symm x y]
    by_cases hxy : x = y
    · rw [hxy]
    · rw [if_neg hxy, if_neg (fun h => hxy h.symm)]
  have hT'_conn : (hoppingSupportGraph T').Preconnected := by
    rw [hT', hoppingSupportGraph_add_diagonal]; exact hT_conn
  obtain ⟨Eattr, φattr, huniqueAttr, hsinglet⟩ :=
    theorem_10_2_lieb_attractive_unique_singlet N Ne hNe_even hNe_pos (by omega)
      T' hT'_symm hT'_conn U hU_pos
  obtain ⟨hmemφ, hnormφ, hHφ, hgroundφ, huniqφ⟩ := huniqueAttr
  -- Theorem 10.3 (Tian): the attractive ground state has positive pair-transfer correlation.
  have hpair := theorem_10_3_tian_pair_correlation_positive N Ne hNe_even hNe_pos
    hNe_lt T' hT'_symm hT'_conn U hU_pos ⟨hmemφ, hnormφ, hHφ, hgroundφ, huniqφ⟩
  set f : (Fin (2 * N + 2) → Fin 2) → ℂ := φattr.ofLp with hf
  -- Plain-space eigenrelations for `φ_attr`.
  have hHf : Hattr.mulVec f = (Eattr : ℂ) • f := bwd Hattr (Eattr : ℂ) φattr hHφ
  have hNf : (fermionTotalNumber (2 * N + 1)).mulVec f = ((Ne : ℕ) : ℂ) • f :=
    bwd _ _ φattr ((Module.End.mem_eigenspace_iff).mp hmemφ)
  -- `φ_attr` is a spin singlet, hence unpolarised: `Ŝ³ φ_attr = 0`.
  have hCasf : (fermionTotalSpinSquared N).mulVec f = 0 := by
    have h0 : Matrix.toEuclideanLin (fermionTotalSpinSquared N) φattr = (0 : ℂ) • φattr := by
      rw [hsinglet, zero_smul]
    have h1 := bwd (fermionTotalSpinSquared N) (0 : ℂ) φattr h0
    rwa [zero_smul] at h1
  have hS3f : (fermionTotalSpinZ N).mulVec f = 0 := by
    -- `Ŝ² = (Ŝ⁽¹⁾)² + (Ŝ⁽²⁾)² + (Ŝ³)²` is a Cartesian square sum of Hermitian generators, so a
    -- null vector of the Casimir is a null vector of each component (Tasaki Lemma A.11).
    set J : Fin 3 → ManyBodyOp (Fin (2 * N + 2)) :=
      ![tJTotalSpinOne N, tJTotalSpinTwo N, fermionTotalSpinZ N] with hJ
    have hherm : ∀ α ∈ (Finset.univ : Finset (Fin 3)), (J α).IsHermitian := by
      intro α _
      fin_cases α
      · simpa [hJ] using tJTotalSpinOne_isHermitian N
      · simpa [hJ] using tJTotalSpinTwo_isHermitian N
      · simpa [hJ] using fermionTotalSpinZ_isHermitian N
    have hcas : ∑ α ∈ (Finset.univ : Finset (Fin 3)), J α * J α = fermionTotalSpinSquared N := by
      rw [fermionTotalSpinSquared_eq_cartesianSqSum, hJ, Fin.sum_univ_three]
      simp
    have hz := mulVec_eq_zero_of_sq_sum_inner_zero (Φ := f) (Finset.univ : Finset (Fin 3)) J hherm
      (by rw [hcas, hCasf, dotProduct_zero]) 2 (Finset.mem_univ 2)
    simpa [hJ] using hz
  -- The transported state `ψ = Û φ_attr`.
  set ψ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2) := WithLp.toLp 2 (Ush.mulVec f) with hψdef
  have hψofLp : ψ.ofLp = Ush.mulVec f := rfl
  -- `star f ⬝ᵥ f = 1` and hence `‖ψ‖ = 1`.
  have hff : star f ⬝ᵥ f = 1 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) φattr
    rw [EuclideanSpace.inner_eq_star_dotProduct, hnormφ] at h
    rw [dotProduct_comm]
    simpa using h
  have hψnorm : ‖ψ‖ = 1 := by
    have hψdot : star ψ.ofLp ⬝ᵥ ψ.ofLp = 1 := by
      rw [hψofLp, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hUU,
        Matrix.vecMul_one, hff]
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, hψdot] at h
    have h2 : ‖ψ‖ ^ 2 = 1 := by
      have h' : ((‖ψ‖ ^ 2 : ℝ) : ℂ) = 1 := by push_cast; exact h.symm
      exact_mod_cast h'
    rw [← Real.sqrt_sq (norm_nonneg ψ), h2, Real.sqrt_one]
  -- `ψ` is an `E`-eigenvector of `Ĥ^{rep}` with `E = E_attr − cR`.
  have hEeig : Matrix.toEuclideanLin Hrep ψ = ((Eattr - cR : ℝ) : ℂ) • ψ := by
    refine fwd Hrep _ ψ ?_
    rw [hψofLp, Matrix.mulVec_mulVec, hHrepU, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, hHf,
      show (Eattr : ℂ) • f - (cR : ℂ) • f = ((Eattr - cR : ℝ) : ℂ) • f by
        push_cast; rw [sub_smul],
      Matrix.mulVec_smul]
  -- Membership `ψ ∈ (Ŝ³ = m)`.
  have hψmem : ψ ∈ spinZSectorEuclidean N mVal := by
    rw [spinZSectorEuclidean, Module.End.mem_eigenspace_iff]
    refine fwd (fermionTotalSpinZ N) mVal ψ ?_
    have hSU : fermionTotalSpinZ N * Ush
        = Ush * ((1 / 2 : ℂ) • (fermionTotalNumber (2 * N + 1) - ((N : ℂ) + 1) • 1)) := by
      rw [← shibaSignedUnitary_conj_totalSpinZ (shibaSignFn A) hs, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, hUUc, Matrix.one_mul]
    rw [hψofLp, Matrix.mulVec_mulVec, hSU, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
      Matrix.sub_mulVec, hNf, Matrix.smul_mulVec, Matrix.one_mulVec,
      show (1 / 2 : ℂ) • (((Ne : ℕ) : ℂ) • f - ((N : ℂ) + 1) • f) = mVal • f by
        rw [hmVal]; module,
      Matrix.mulVec_smul]
  -- Transport a competitor `ψ'` in the `Ŝ³ = m` sector back to the `N̂ = Ne` sector.
  have transport : ∀ (e : ℝ) (ψ' : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)),
      ψ' ∈ spinZSectorEuclidean N mVal →
      Matrix.toEuclideanLin Hrep ψ' = (e : ℂ) • ψ' →
      (WithLp.toLp 2 ((Matrix.conjTranspose Ush).mulVec ψ'.ofLp) ∈
          electronNumberSectorEuclidean N Ne) ∧
      Matrix.toEuclideanLin Hattr (WithLp.toLp 2 ((Matrix.conjTranspose Ush).mulVec ψ'.ofLp))
        = ((e + cR : ℝ) : ℂ) • WithLp.toLp 2 ((Matrix.conjTranspose Ush).mulVec ψ'.ofLp) := by
    intro e ψ' hψ'mem hψ'eig
    have hS3 : (fermionTotalSpinZ N).mulVec ψ'.ofLp = mVal • ψ'.ofLp :=
      bwd (fermionTotalSpinZ N) mVal ψ' ((Module.End.mem_eigenspace_iff).mp hψ'mem)
    have hHψ' : Hrep.mulVec ψ'.ofLp = (e : ℂ) • ψ'.ofLp := bwd Hrep _ ψ' hψ'eig
    set g : (Fin (2 * N + 2) → Fin 2) → ℂ := (Matrix.conjTranspose Ush).mulVec ψ'.ofLp with hg
    have hgofLp : (WithLp.toLp 2 g).ofLp = g := rfl
    constructor
    · rw [electronNumberSectorEuclidean, Module.End.mem_eigenspace_iff]
      refine fwd (fermionTotalNumber (2 * N + 1)) _ _ ?_
      rw [hgofLp, hg, Matrix.mulVec_mulVec, hNU, ← Matrix.mulVec_mulVec, Matrix.add_mulVec,
        Matrix.smul_mulVec, hS3, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, ← add_smul,
        hNeval, Matrix.mulVec_smul]
    · refine fwd Hattr _ _ ?_
      rw [hgofLp, hg, Matrix.mulVec_mulVec, hHU, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
        hHψ', Matrix.mulVec_smul, Matrix.smul_mulVec]
      push_cast
      rw [add_smul]
  -- Minimality of `E` on the `Ŝ³ = m` sector.
  have hground : IsGroundEigenvalueOn (spinZSectorEuclidean N mVal) Hrep (Eattr - cR) := by
    refine ⟨⟨ψ, hψmem, ?_, hEeig⟩, ?_⟩
    · intro h; rw [h, norm_zero] at hψnorm; exact one_ne_zero hψnorm.symm
    · intro μ hμ
      obtain ⟨ψ', hψ'mem, hψ'ne, hψ'eig⟩ := hμ
      obtain ⟨hmemg, heigg⟩ := transport μ ψ' hψ'mem hψ'eig
      have hgne : WithLp.toLp 2 ((Matrix.conjTranspose Ush).mulVec ψ'.ofLp) ≠ 0 := by
        intro hz
        apply hψ'ne
        have hz' : (Matrix.conjTranspose Ush).mulVec ψ'.ofLp = 0 := by
          have := congrArg WithLp.ofLp hz; simpa using this
        apply WithLp.ofLp_injective (p := 2) (V := (Fin (2 * N + 2) → Fin 2) → ℂ)
        rw [WithLp.ofLp_zero]
        calc ψ'.ofLp = (Ush * Matrix.conjTranspose Ush).mulVec ψ'.ofLp := by
                rw [hUUc, Matrix.one_mulVec]
          _ = Ush.mulVec ((Matrix.conjTranspose Ush).mulVec ψ'.ofLp) := by
                rw [Matrix.mulVec_mulVec]
          _ = 0 := by rw [hz', Matrix.mulVec_zero]
      have hle : Eattr ≤ μ + cR := hgroundφ.2 (μ + cR) ⟨_, hmemg, hgne, heigg⟩
      linarith
  -- Uniqueness on the `Ŝ³ = m` sector.
  have huniq : ∀ ψ' : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
      ψ' ∈ spinZSectorEuclidean N mVal →
      Matrix.toEuclideanLin Hrep ψ' = ((Eattr - cR : ℝ) : ℂ) • ψ' → ∃ c : ℂ, ψ' = c • ψ := by
    intro ψ' hψ'mem hψ'eig
    obtain ⟨hmemg, heigg⟩ := transport (Eattr - cR) ψ' hψ'mem hψ'eig
    have heigg' : Matrix.toEuclideanLin Hattr
        (WithLp.toLp 2 ((Matrix.conjTranspose Ush).mulVec ψ'.ofLp))
          = (Eattr : ℂ) • WithLp.toLp 2 ((Matrix.conjTranspose Ush).mulVec ψ'.ofLp) := by
      rw [heigg]; norm_num
    obtain ⟨c, hc⟩ := huniqφ _ hmemg heigg'
    refine ⟨c, ?_⟩
    have hcofLp : (Matrix.conjTranspose Ush).mulVec ψ'.ofLp = c • f := by
      have := congrArg WithLp.ofLp hc; simpa [hf] using this
    apply WithLp.ofLp_injective (p := 2) (V := (Fin (2 * N + 2) → Fin 2) → ℂ)
    change ψ'.ofLp = c • ψ.ofLp
    rw [hψofLp]
    calc ψ'.ofLp = (Ush * Matrix.conjTranspose Ush).mulVec ψ'.ofLp := by
            rw [hUUc, Matrix.one_mulVec]
      _ = Ush.mulVec ((Matrix.conjTranspose Ush).mulVec ψ'.ofLp) := by rw [Matrix.mulVec_mulVec]
      _ = Ush.mulVec (c • f) := by rw [hcofLp]
      _ = c • Ush.mulVec f := by rw [Matrix.mulVec_smul]
  refine ⟨Eattr - cR, ψ, φattr, ⟨hψmem, hψnorm, hEeig, hground, huniq⟩, hψofLp, hpair, ?_⟩
  -- The Shiba flip is an involution (`shibaPermMatrix` Hermitian, `P · P = 1`), so the diagonal
  -- `N̂` is reindexed by the same map in both orders: `Ûᴴ N̂ Û = Û N̂ Ûᴴ = 2 Ŝ³ + (N+1)·1`.
  have hNsym : Matrix.conjTranspose Ush * fermionTotalNumber (2 * N + 1) * Ush
      = (2 : ℂ) • fermionTotalSpinZ N + ((N : ℂ) + 1) • 1 := by
    rw [← shibaSignedUnitary_conj_totalNumber (shibaSignFn A) hs, fermionTotalNumber_eq_diagonal,
      shibaSignedUnitary_conj_diagonal (shibaSignFn A) hs,
      shibaSignedUnitary_self_conj_diagonal (shibaSignFn A) hs]
  -- `N̂ Û = Û (2 Ŝ³ + (N+1)·1)`.
  have hNUfwd : fermionTotalNumber (2 * N + 1) * Ush
      = Ush * ((2 : ℂ) • fermionTotalSpinZ N + ((N : ℂ) + 1) • 1) := by
    rw [← hNsym, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUUc, Matrix.one_mul]
  have hchargef : ((2 : ℂ) • fermionTotalSpinZ N
      + ((N : ℂ) + 1) • (1 : ManyBodyOp (Fin (2 * N + 2)))).mulVec f = ((N : ℂ) + 1) • f := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, hS3f, smul_zero, zero_add, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  refine fwd (fermionTotalNumber (2 * N + 1)) ((N : ℂ) + 1) ψ ?_
  rw [hψofLp, Matrix.mulVec_mulVec, hNUfwd, ← Matrix.mulVec_mulVec, hchargef, Matrix.mulVec_smul]

/-- **Eq. (10.2.9)** (Tasaki §10.2.2, p. 351): on the fixed `Ne`-electron sector, the symmetric
repulsive interaction with **uniform** on-site repulsion `U_x = U` differs from the uniform
repulsive interaction `Ĥint^{unif} = U Σ_x n̂_{x,↑} n̂_{x,↓}` by the scalar
`c = −(U/2)·Ne + (U/4)·(N+1)`:
`Ĥint^{sym}(U) = Ĥint^{unif}(U) − (U/2) N̂ + (U/4)|Λ|`, so on the `N̂ = Ne` sector
`Ĥ^{rep,sym}(U) = Ĥ^{rep,unif}(U) + c · 1`.  Consequently, for any target energy `E`, the
`E`-ground submodule of the symmetric-interaction Hamiltonian on the `Ne`-electron sector
coincides with the `(E − c)`-ground submodule of the uniform-interaction Hamiltonian on the same
sector: the two variants have the **same** ground submodule (up to the constant energy shift
`c`), supplying the form conversion (10.2.6) → (10.2.5) **at a constant `U`**.

Scope: `hubbardGroundSubmoduleAtElectronNumber` is the `E`-eigenspace intersected with the
`Ne`-electron sector and carries **no** minimality of `E`, so what this transports between the two
variants is the eigenspace equality alone; transporting ground-state minimality (that the shifted
`E − c` is the least sector eigenvalue) is a separate step. -/
theorem symmetricRepulsiveHubbardHamiltonian_groundSubmodule_eq_uniform
    (N : ℕ) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : ℝ) (Ne : ℕ) (E : ℂ) :
    hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T (fun _ => U)) E Ne
      = hubbardGroundSubmoduleAtElectronNumber
          (repulsiveHubbardHamiltonian N T U)
          (E - (-(U : ℂ) / 2 * (Ne : ℂ) + (U : ℂ) / 4 * ((N : ℂ) + 1))) Ne := by
  classical
  -- Per site: `U (n̂↑ − ½)(n̂↓ − ½) = U n̂↑n̂↓ − (U/2)(n̂↑ + n̂↓) + U/4`.
  have hterm : ∀ x : Fin (N + 1),
      (U : ℂ) • ((fermionUpNumber N x - (1 / 2 : ℂ) • (1 : ManyBodyOp (Fin (2 * N + 2))))
          * (fermionDownNumber N x - (1 / 2 : ℂ) • (1 : ManyBodyOp (Fin (2 * N + 2)))))
        = (U : ℂ) • (fermionUpNumber N x * fermionDownNumber N x)
          - (((U : ℂ) / 2) • fermionUpNumber N x + ((U : ℂ) / 2) • fermionDownNumber N x)
          + ((U : ℂ) / 4) • (1 : ManyBodyOp (Fin (2 * N + 2))) := by
    intro x
    rw [symmetricHubbardOnSite_expand]
    module
  -- Eq. (10.2.9): summing over the `N+1` sites, `Ĥint^{sym} = Ĥint^{unif} − (U/2) N̂ + (U/4)|Λ|`.
  have hint : symmetricRepulsiveHubbardInteraction N (fun _ => U)
      = hubbardOnSiteInteractionSite N (fun _ => (U : ℂ))
        - ((U : ℂ) / 2) • fermionTotalNumber (2 * N + 1)
        + ((U : ℂ) / 4 * ((N : ℂ) + 1)) • (1 : ManyBodyOp (Fin (2 * N + 2))) := by
    have hup : ∑ x : Fin (N + 1), ((U : ℂ) / 2) • fermionUpNumber N x
        = ((U : ℂ) / 2) • ∑ x : Fin (N + 1), fermionUpNumber N x := Finset.smul_sum.symm
    have hdn : ∑ x : Fin (N + 1), ((U : ℂ) / 2) • fermionDownNumber N x
        = ((U : ℂ) / 2) • ∑ x : Fin (N + 1), fermionDownNumber N x := Finset.smul_sum.symm
    have hconst : ∑ _x : Fin (N + 1), ((U : ℂ) / 4) • (1 : ManyBodyOp (Fin (2 * N + 2)))
        = ((U : ℂ) / 4 * ((N : ℂ) + 1)) • (1 : ManyBodyOp (Fin (2 * N + 2))) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
        smul_smul]
      congr 1
      push_cast
      ring
    simp only [symmetricRepulsiveHubbardInteraction, hubbardOnSiteInteractionSite,
      fermionTotalNumber_eq_up_add_down, fermionTotalUpNumber, fermionTotalDownNumber]
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, hup, hdn, hconst]
    module
  have hop : symmetricRepulsiveHubbardHamiltonian N T (fun _ => U)
      = repulsiveHubbardHamiltonian N T U
        - ((U : ℂ) / 2) • fermionTotalNumber (2 * N + 1)
        + ((U : ℂ) / 4 * ((N : ℂ) + 1)) • (1 : ManyBodyOp (Fin (2 * N + 2))) := by
    rw [symmetricRepulsiveHubbardHamiltonian, repulsiveHubbardHamiltonian, hint]
    abel
  ext v
  simp only [hubbardGroundSubmoduleAtElectronNumber, Submodule.mem_inf,
    Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨hH, hN⟩
    refine ⟨?_, hN⟩
    rw [hop, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, hN, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_smul] at hH
    linear_combination (norm := module) hH
  · rintro ⟨hH, hN⟩
    refine ⟨?_, hN⟩
    rw [hop, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, hN, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_smul, hH]
    module

end LatticeSystem.Fermion
