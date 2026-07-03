import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaSector
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaConjugation
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveTheorem102
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveTheorem103

/-!
# Lieb's theorem, symmetric repulsive Hubbard model at half filling (Tasaki §10.2.2, Thm 10.4)

Final assembly (c7) of the axiom-free portion of **Tasaki Theorem 10.4** (Lieb's theorem for the
repulsive Hubbard model at half filling), Hal Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, 1st ed., Springer 2020, §10.2.2, pp. 350–352.

For an odd number of sites `N` (so that `Ne = N + 1` is even), a connected real symmetric hopping
`T` that respects a bipartition and on-site repulsion `U_x > 0`, the symmetric (`μ = U/2`,
half-filling) repulsive Hubbard Hamiltonian `Ĥ^{rep,sym}` has a **unique** ground state on the
balanced spin-`z` sector `Ŝ³ = 0`.  This is obtained by **transporting** the attractive-model result
(Theorem 10.2) through the Shiba unitary `Û`.

## The transport

The Shiba unitary conjugation (c6, eq. (10.2.10)) gives
`Ûᴴ Ĥ^{rep,sym} Û = Ĥ^{attr}(T + diag(U/2)) − ¼(∑ U) · 1`,
and the Shiba flip **exchanges** the number and spin-`z` charges
(`shibaSignedUnitary_conj_totalNumber` / `_conj_totalSpinZ`):
`Û N̂ Ûᴴ = 2 Ŝ³ + (N+1)·1` and `Ûᴴ Ŝ³ Û = ½(N̂ − (N+1)·1)`.  Consequently the attractive-model
**number** sector `N̂ = N+1` (Theorem 10.2's `electronNumberSectorEuclidean N (N+1)`, unique ground
state `φ_attr`, energy `E_attr`) transports to the repulsive-model **spin-`z`** sector `Ŝ³ = 0`, and
`ψ := Û φ_attr` is the unique ground state there with energy `E := E_attr − ¼(∑ U)`.

Because `Û` maps the spin SU(2) algebra to the η-pseudospin algebra (`Û Ŝ² Ûᴴ ≠ Ŝ²`), the
attractive singlet is **not** transported to a spin singlet; the repulsive total-spin value
`||A|−|B||/2` requires the degenerate perturbation theory (a deferred axiom).  Accordingly this
capstone claims **only** the balanced-sector ground-state uniqueness, not any total-spin value.

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

/-- **Tasaki Theorem 10.4** (Lieb's theorem for the symmetric repulsive Hubbard model at half
filling, 1st ed., Springer 2020, §10.2.2, pp. 350–352; **PROVED** on the balanced sector, no
axiom).  For odd `N` (so `Ne = N + 1` is even), a connected real symmetric hopping `T` respecting a
bipartition `A`, and on-site repulsion `U_x > 0`, the symmetric (`μ = U/2`, half-filling) repulsive
Hubbard Hamiltonian `Ĥ^{rep,sym}` has a **unique** ground state on the balanced spin-`z` sector
`Ŝ³ = 0`.

The total-spin value (singlet vs. `||A|−|B||/2`) is **not** claimed: the Shiba unitary sends `Ŝ²`
to the η-pseudospin Casimir, so identifying the repulsive total spin needs the deferred degenerate
perturbation theory.

Proof: transport the attractive-model number-sector unique ground state (Theorem 10.2,
`theorem_10_2_lieb_attractive_unique_singlet`, applied to `T + diag(U/2)`) through the Shiba unitary
`Û`, using the conjugation `Ûᴴ Ĥ^{rep,sym} Û = Ĥ^{attr} − ¼(∑ U)·1` (c6, eq. (10.2.10)) and the
charge exchange `Û N̂ Ûᴴ = 2 Ŝ³ + (N+1)·1` / `Ûᴴ Ŝ³ Û = ½(N̂ − (N+1)·1)`.

The transported ground state `φ = Û φ_attr` is exposed via `φ.ofLp = Û φ_attr.ofLp` together
with Theorem 10.3's pair-transfer positivity of the underlying attractive ground state `φ_attr`;
this is what Theorem 10.5 (Shen–Qiu–Tian) consumes. -/
theorem repulsiveHalfFilling_balancedSector_ground_unique (N : ℕ) (hNodd : Odd N)
    {A : Finset (Fin (N + 1))} (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT_symm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x) :
    ∃ (E : ℝ) (φ φattr : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)),
      IsUniqueGroundStateOn (spinZSectorEuclidean N 0)
          (symmetricRepulsiveHubbardHamiltonian N T U) E φ ∧
        φ.ofLp = (shibaSignedUnitary N (shibaSignFn A)).mulVec φattr.ofLp ∧
        ∀ x y : Fin (N + 1),
          0 < (euclideanExpectation (hubbardPairCorrelationOp N x y) φattr).re ∧
            (euclideanExpectation (hubbardPairCorrelationOp N x y) φattr).im = 0 := by
  classical
  -- Abbreviations for the Shiba unitary, the two Hamiltonians and the scalar shift.
  set Ush : Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ :=
    shibaSignedUnitary N (shibaSignFn A) with hUsh
  set Hrep : ManyBodyOp (Fin (2 * N + 2)) := symmetricRepulsiveHubbardHamiltonian N T U with hHrep
  set T' : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := T + Matrix.diagonal (fun x => U x / 2) with hT'
  set Hattr : ManyBodyOp (Fin (2 * N + 2)) := attractiveHubbardHamiltonian N T' U with hHattrDef
  set cR : ℝ := (∑ x : Fin (N + 1), U x) / 4 with hcR
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
  -- Apply Theorem 10.2 to the shifted hopping `T' = T + diag(U/2)`.
  have hT'_symm : ∀ x y, T' x y = T' y x := by
    intro x y
    rw [hT', Matrix.add_apply, Matrix.add_apply, Matrix.diagonal_apply, Matrix.diagonal_apply,
      hT_symm x y]
    by_cases hxy : x = y
    · rw [hxy]
    · rw [if_neg hxy, if_neg (Ne.symm hxy)]
  have hT'_conn : (hoppingSupportGraph T').Preconnected := by
    rw [hT', hoppingSupportGraph_add_diagonal]; exact hT_conn
  obtain ⟨Eattr, φattr, huniqueAttr, _⟩ :=
    theorem_10_2_lieb_attractive_unique_singlet N (N + 1) hNodd.add_one (by omega) (by omega)
      T' hT'_symm hT'_conn U hU_pos
  obtain ⟨hmemφ, hnormφ, hHφ, hgroundφ, huniqφ⟩ := huniqueAttr
  -- Theorem 10.3 (Tian): the attractive ground state has positive pair-transfer correlation.
  have hpair := theorem_10_3_tian_pair_correlation_positive N (N + 1) hNodd.add_one (by omega)
    (by omega) T' hT'_symm hT'_conn U hU_pos ⟨hmemφ, hnormφ, hHφ, hgroundφ, huniqφ⟩
  set f : (Fin (2 * N + 2) → Fin 2) → ℂ := φattr.ofLp with hf
  -- Plain-space eigenrelations for `φ_attr`.
  have hHf : Hattr.mulVec f = (Eattr : ℂ) • f := bwd Hattr (Eattr : ℂ) φattr hHφ
  have hNf : (fermionTotalNumber (2 * N + 1)).mulVec f = ((N + 1 : ℕ) : ℂ) • f :=
    bwd _ _ φattr ((Module.End.mem_eigenspace_iff).mp hmemφ)
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
  -- Membership `ψ ∈ (Ŝ³ = 0)`.
  have hψmem : ψ ∈ spinZSectorEuclidean N 0 := by
    rw [spinZSectorEuclidean, Module.End.mem_eigenspace_iff]
    refine fwd (fermionTotalSpinZ N) 0 ψ ?_
    have hSU : fermionTotalSpinZ N * Ush
        = Ush * ((1 / 2 : ℂ) • (fermionTotalNumber (2 * N + 1) - ((N : ℂ) + 1) • 1)) := by
      rw [← shibaSignedUnitary_conj_totalSpinZ (shibaSignFn A) hs, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, hUUc, Matrix.one_mul]
    rw [hψofLp, zero_smul, Matrix.mulVec_mulVec, hSU, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
      Matrix.sub_mulVec, hNf, Matrix.smul_mulVec, Matrix.one_mulVec,
      show ((N + 1 : ℕ) : ℂ) • f - ((N : ℂ) + 1) • f = 0 by push_cast; rw [sub_self],
      smul_zero, Matrix.mulVec_zero]
  -- Transport a competitor `ψ'` in the `Ŝ³ = 0` sector back to the `N̂ = N+1` sector.
  have transport : ∀ (e : ℝ) (ψ' : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)),
      ψ' ∈ spinZSectorEuclidean N 0 →
      Matrix.toEuclideanLin Hrep ψ' = (e : ℂ) • ψ' →
      (WithLp.toLp 2 ((Matrix.conjTranspose Ush).mulVec ψ'.ofLp) ∈
          electronNumberSectorEuclidean N (N + 1)) ∧
      Matrix.toEuclideanLin Hattr (WithLp.toLp 2 ((Matrix.conjTranspose Ush).mulVec ψ'.ofLp))
        = ((e + cR : ℝ) : ℂ) • WithLp.toLp 2 ((Matrix.conjTranspose Ush).mulVec ψ'.ofLp) := by
    intro e ψ' hψ'mem hψ'eig
    have hS3 : (fermionTotalSpinZ N).mulVec ψ'.ofLp = 0 := by
      have := bwd (fermionTotalSpinZ N) 0 ψ'
        ((Module.End.mem_eigenspace_iff).mp hψ'mem)
      rwa [zero_smul] at this
    have hHψ' : Hrep.mulVec ψ'.ofLp = (e : ℂ) • ψ'.ofLp := bwd Hrep _ ψ' hψ'eig
    set g : (Fin (2 * N + 2) → Fin 2) → ℂ := (Matrix.conjTranspose Ush).mulVec ψ'.ofLp with hg
    have hgofLp : (WithLp.toLp 2 g).ofLp = g := rfl
    constructor
    · rw [electronNumberSectorEuclidean, Module.End.mem_eigenspace_iff]
      refine fwd (fermionTotalNumber (2 * N + 1)) _ _ ?_
      rw [hgofLp, hg, Matrix.mulVec_mulVec, hNU, ← Matrix.mulVec_mulVec, Matrix.add_mulVec,
        Matrix.smul_mulVec, hS3, smul_zero, zero_add, Matrix.smul_mulVec, Matrix.one_mulVec,
        Matrix.mulVec_smul, Nat.cast_add_one]
    · refine fwd Hattr _ _ ?_
      rw [hgofLp, hg, Matrix.mulVec_mulVec, hHU, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
        hHψ', Matrix.mulVec_smul, Matrix.smul_mulVec]
      push_cast
      rw [add_smul]
  -- Minimality of `E` on the `Ŝ³ = 0` sector.
  have hground : IsGroundEigenvalueOn (spinZSectorEuclidean N 0) Hrep (Eattr - cR) := by
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
  -- Uniqueness on the `Ŝ³ = 0` sector.
  have huniq : ∀ ψ' : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
      ψ' ∈ spinZSectorEuclidean N 0 →
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
  exact ⟨Eattr - cR, ψ, φattr, ⟨hψmem, hψnorm, hEeig, hground, huniq⟩, hψofLp, hpair⟩

end LatticeSystem.Fermion
