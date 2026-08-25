import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaSector
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaConjugation
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveTheorem102
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveTheorem103
import LatticeSystem.Math.MatrixAnalysis.UnitaryGroundTransport

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

The transport itself is isolated as `shibaTransport_uniqueGroundStateOn_spinZSector_of_conj`, which
takes a number-sector unique ground state together with its singlet property and the conjugation
identity for the model at hand, and returns the spin-`z`-sector one at unchanged energy.  All that
varies between the §10.2.2 and §10.2.3 uses is that conjugation identity, so both are instances of
it: `shibaTransport_uniqueGroundStateOn_spinZSector` below (plain attractive source, eq. (10.2.10),
energy `E − ¼(∑ U)`), consumed by the capstone as the composition with Theorems 10.2/10.3, and the
symmetric-attractive one of `LiebShenQiuShibaTransport.lean` (eq. (10.2.21), energy unchanged).
The subspace-free part of the argument — that a unitary intertwiner carries a unique ground state
between two subspaces at unchanged energy — lives in
`Math/MatrixAnalysis/UnitaryGroundTransport.lean`.

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

/-- **A diagonal shift preserves the symmetry of the hopping matrix**:
`T + diagonal d` is symmetric whenever `T` is.  Together with
`hoppingSupportGraph_add_diagonal` this is what lets Theorems 10.2/10.3, stated for a plain
hopping matrix, be applied to the chemical-potential-shifted hopping `T + diag(U/2)` produced by
centring the Hubbard interaction. -/
theorem hoppingSymm_add_diagonal (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT : ∀ x y, T x y = T y x) (d : Fin (N + 1) → ℝ) :
    ∀ x y, (T + Matrix.diagonal d) x y = (T + Matrix.diagonal d) y x := by
  intro x y
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.diagonal_apply, Matrix.diagonal_apply, hT x y]
  by_cases hxy : x = y
  · rw [hxy]
  · rw [if_neg hxy, if_neg (fun h => hxy h.symm)]

/-- **Shiba transport of a unique ground state from the electron-number sector to the spin-`z`
sector, at unchanged energy** (Tasaki §10.2.2, eq. (10.2.11), pp. 350–352).  Let the Shiba unitary
`Û` conjugate a Hamiltonian `Ĥ^{rep}` into `Ĥ` (`Ûᴴ Ĥ^{rep} Û = Ĥ`), and let `φ` be the unique
normalized ground state of `Ĥ` on the `N̂ = Ne` sector at energy `E`, with the singlet property
`Ŝ² φ = 0`.  Then `ψ = Û φ` is the unique normalized ground state of `Ĥ^{rep}` on the spin-`z`
sector `Ŝ³ = (Ne − (N+1))/2`, at the **same** energy `E`, and sits in the half-filled sector,
`N̂ ψ = (N+1) ψ`.

Everything model-specific is confined to `hconj`; the transport itself uses only the charge
exchange `Ûᴴ Ŝ³ Û = ½(N̂ − (N+1)·1)` and `Û N̂ Ûᴴ = 2 Ŝ³ + (N+1)·1` (eq. (10.2.11)), which supplies
the two sector-mapping hypotheses of `IsUniqueGroundStateOn.conj_unitary` in both directions, and,
for the number eigenvalue, `Ŝ³ φ = 0` (forced by the singlet property) together with the
involutivity of the Shiba flip, which makes the two conjugation orders `Ûᴴ N̂ Û` and `Û N̂ Ûᴴ`
agree.  Whatever constant the conjugation of the model at hand leaves behind is therefore not this
lemma's business: it is peeled off the source Hamiltonian with
`IsUniqueGroundStateOn.sub_smul_one` before this lemma is applied
(`shibaTransport_uniqueGroundStateOn_spinZSector` below), or absent to begin with
(`shibaTransport_uniqueGroundStateOn_spinZSector_symmetricAttractive`,
`LiebShenQiuShibaTransport.lean`).

Note the number eigenvalue is `N+1`, **not** `Ne`: every transported state sits at half filling
regardless of the electron number of the sector it comes from. -/
theorem shibaTransport_uniqueGroundStateOn_spinZSector_of_conj (N Ne : ℕ)
    {A : Finset (Fin (N + 1))} {H Hrep : ManyBodyOp (Fin (2 * N + 2))}
    (hconj : Matrix.conjTranspose (shibaSignedUnitary N (shibaSignFn A)) * Hrep
      * shibaSignedUnitary N (shibaSignFn A) = H)
    {E : ℝ} {φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn (electronNumberSectorEuclidean N Ne) H E φ)
    (hsinglet : Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = 0) :
    ∃ ψ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
      ψ.ofLp = (shibaSignedUnitary N (shibaSignFn A)).mulVec φ.ofLp ∧
      IsUniqueGroundStateOn (spinZSectorEuclidean N (((Ne : ℂ) - ((N : ℂ) + 1)) / 2)) Hrep E ψ ∧
      Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) ψ = ((N : ℂ) + 1) • ψ := by
  set Ush : Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ :=
    shibaSignedUnitary N (shibaSignFn A) with hUsh
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
  -- `Û` maps the `N̂ = Ne` sector into the `Ŝ³ = m` sector (eq. (10.2.11)).
  have hfwdmem : ∀ v ∈ electronNumberSectorEuclidean N Ne,
      Matrix.toEuclideanLin Ush v ∈ spinZSectorEuclidean N mVal := by
    intro v hv
    have hSU : fermionTotalSpinZ N * Ush
        = Ush * ((1 / 2 : ℂ) • (fermionTotalNumber (2 * N + 1) - ((N : ℂ) + 1) • 1)) := by
      rw [← shibaSignedUnitary_conj_totalSpinZ (shibaSignFn A) hs, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, hUUc, Matrix.one_mul]
    have hNv : (fermionTotalNumber (2 * N + 1)).mulVec v.ofLp = ((Ne : ℕ) : ℂ) • v.ofLp :=
      bwd _ _ v ((Module.End.mem_eigenspace_iff).mp hv)
    have hUv : (Matrix.toEuclideanLin Ush v).ofLp = Ush.mulVec v.ofLp := rfl
    rw [spinZSectorEuclidean, Module.End.mem_eigenspace_iff]
    refine fwd (fermionTotalSpinZ N) mVal _ ?_
    rw [hUv, Matrix.mulVec_mulVec, hSU, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
      Matrix.sub_mulVec, hNv, Matrix.smul_mulVec, Matrix.one_mulVec,
      show (1 / 2 : ℂ) • (((Ne : ℕ) : ℂ) • v.ofLp - ((N : ℂ) + 1) • v.ofLp) = mVal • v.ofLp by
        rw [hmVal]; module,
      Matrix.mulVec_smul]
  -- `Ûᴴ` maps the `Ŝ³ = m` sector back into the `N̂ = Ne` sector (eq. (10.2.11), other direction).
  have hbwdmem : ∀ v ∈ spinZSectorEuclidean N mVal,
      Matrix.toEuclideanLin (Matrix.conjTranspose Ush) v ∈ electronNumberSectorEuclidean N Ne := by
    intro v hv
    have hNU : fermionTotalNumber (2 * N + 1) * Matrix.conjTranspose Ush
        = Matrix.conjTranspose Ush
            * ((2 : ℂ) • fermionTotalSpinZ N + ((N : ℂ) + 1) • 1) := by
      rw [← shibaSignedUnitary_conj_totalNumber (shibaSignFn A) hs, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, hUU, Matrix.one_mul]
    have hS3 : (fermionTotalSpinZ N).mulVec v.ofLp = mVal • v.ofLp :=
      bwd (fermionTotalSpinZ N) mVal v ((Module.End.mem_eigenspace_iff).mp hv)
    have hUcv : (Matrix.toEuclideanLin (Matrix.conjTranspose Ush) v).ofLp
        = (Matrix.conjTranspose Ush).mulVec v.ofLp := rfl
    rw [electronNumberSectorEuclidean, Module.End.mem_eigenspace_iff]
    refine fwd (fermionTotalNumber (2 * N + 1)) _ _ ?_
    rw [hUcv, Matrix.mulVec_mulVec, hNU, ← Matrix.mulVec_mulVec, Matrix.add_mulVec,
      Matrix.smul_mulVec, hS3, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, ← add_smul,
      hNeval, Matrix.mulVec_smul]
  -- Transport along `Û`, at unchanged energy.
  have hGStrans : IsUniqueGroundStateOn (spinZSectorEuclidean N mVal) Hrep E
      (Matrix.toEuclideanLin Ush φ) :=
    IsUniqueGroundStateOn.conj_unitary hUUc hconj hfwdmem hbwdmem hGS
  refine ⟨Matrix.toEuclideanLin Ush φ, rfl, hGStrans, ?_⟩
  -- `φ` is a spin singlet, hence unpolarised: `Ŝ³ φ = 0`.
  have hS3f : (fermionTotalSpinZ N).mulVec φ.ofLp = 0 := by
    refine fermionTotalSpinZ_mulVec_eq_zero_of_fermionTotalSpinSquared_mulVec_eq_zero N ?_
    have h0 : Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = (0 : ℂ) • φ := by
      rw [hsinglet, zero_smul]
    have h1 := bwd (fermionTotalSpinSquared N) (0 : ℂ) φ h0
    rwa [zero_smul] at h1
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
      + ((N : ℂ) + 1) • (1 : ManyBodyOp (Fin (2 * N + 2)))).mulVec φ.ofLp
        = ((N : ℂ) + 1) • φ.ofLp := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, hS3f, smul_zero, zero_add, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have hUφ : (Matrix.toEuclideanLin Ush φ).ofLp = Ush.mulVec φ.ofLp := rfl
  refine fwd (fermionTotalNumber (2 * N + 1)) ((N : ℂ) + 1) _ ?_
  rw [hUφ, Matrix.mulVec_mulVec, hNUfwd, ← Matrix.mulVec_mulVec, hchargef, Matrix.mulVec_smul]

/-- **Shiba transport from the plain attractive model** (Tasaki §10.2.2, eqs. (10.2.10)/(10.2.11),
pp. 350–352).  Given the unique normalized ground state `φ` of the plain attractive Hamiltonian
`Ĥ^{attr}(T + diag(U/2), U)` on the `N̂ = Ne` sector, at energy `E`, together with the singlet
property `Ŝ² φ = 0`, the Shiba unitary `Û` carries `φ` to the unique normalized ground state
`ψ = Û φ` of the symmetric repulsive Hamiltonian `Ĥ^{rep,sym}(T,U)` on the spin-`z` sector
`Ŝ³ = (Ne − (N+1))/2`, at energy `E − ¼(∑ U)`; moreover `ψ` sits in the half-filled sector,
`N̂ ψ = (N+1) ψ`.

This is `shibaTransport_uniqueGroundStateOn_spinZSector_of_conj` at the conjugation
`Ûᴴ Ĥ^{rep,sym} Û = Ĥ^{attr} − ¼(∑ U)·1` (eq. (10.2.10)), whose leftover constant is moved onto
the source Hamiltonian by `IsUniqueGroundStateOn.sub_smul_one` — which is where the `−¼(∑ U)` of
the output energy comes from.  Stating the source in plain-attractive form keeps this §10.2.2
module free of any dependence on the Theorem-10.8 statement layer. -/
theorem shibaTransport_uniqueGroundStateOn_spinZSector (N Ne : ℕ)
    {A : Finset (Fin (N + 1))} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hT_symm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (U : Fin (N + 1) → ℝ) {E : ℝ} {φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn (electronNumberSectorEuclidean N Ne)
      (attractiveHubbardHamiltonian N (T + Matrix.diagonal (fun x => U x / 2)) U) E φ)
    (hsinglet : Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = 0) :
    ∃ ψ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
      ψ.ofLp = (shibaSignedUnitary N (shibaSignFn A)).mulVec φ.ofLp ∧
      IsUniqueGroundStateOn (spinZSectorEuclidean N (((Ne : ℂ) - ((N : ℂ) + 1)) / 2))
        (symmetricRepulsiveHubbardHamiltonian N T U)
        (E - (∑ x : Fin (N + 1), U x) / 4) ψ ∧
      Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) ψ = ((N : ℂ) + 1) • ψ := by
  have hκ : ((∑ x : Fin (N + 1), (U x : ℂ)) / 4)
      = (((∑ x : Fin (N + 1), U x) / 4 : ℝ) : ℂ) := by push_cast; ring
  refine shibaTransport_uniqueGroundStateOn_spinZSector_of_conj N Ne ?_
    (hGS.sub_smul_one (c := (∑ x : Fin (N + 1), U x) / 4)) hsinglet
  rw [shibaSignedUnitary_conj_symmetricRepulsive_eq_attractive hT_symm hbip U, hκ]

/-- **Tasaki Theorem 10.4** (Lieb's theorem for the symmetric repulsive Hubbard model, general
spin-`z` sector; 1st ed., Springer 2020, §10.2.2, pp. 350–352; **PROVED**, no axiom).  For any
number of sites `N`, an even electron number `0 < Ne < 2(N+1)`, a connected real symmetric hopping
`T` respecting a bipartition `A`, and on-site repulsion `U_x > 0`, the symmetric (`μ = U/2`)
repulsive Hubbard Hamiltonian `Ĥ^{rep,sym}` has a **unique** ground state on the spin-`z` sector
`Ŝ³ = m` with `m = (Ne − (N+1))/2`.

The total-spin value is **not** claimed: the Shiba unitary sends `Ŝ²` to the η-pseudospin Casimir,
so identifying the repulsive total spin needs the (finite-dimensional) degenerate perturbation
theory of Lemma 10.1 (`tasaki_lemma_10_1_degenerate_perturbation`, proved axiom-free).

Proof: Theorem 10.2 (`theorem_10_2_lieb_attractive_unique_singlet`, applied to `T + diag(U/2)` with
electron number `Ne`) supplies the attractive-model number-sector unique ground state `φ_attr`
together with its singlet property, and Theorem 10.3 its pair-transfer positivity; feeding both to
`shibaTransport_uniqueGroundStateOn_spinZSector` performs the Shiba transport, which carries the
conjugation `Ûᴴ Ĥ^{rep,sym} Û = Ĥ^{attr} − ¼(∑ U)·1` (c6, eq. (10.2.10)) and the charge exchange
`Û N̂ Ûᴴ = 2 Ŝ³ + (N+1)·1` / `Ûᴴ Ŝ³ Û = ½(N̂ − (N+1)·1)` turning the number eigenvalue `Ne` into
the spin-`z` eigenvalue `m = (Ne − (N+1))/2` (eq. (10.2.11)).

The transported ground state `φ = Û φ_attr` is exposed via `φ.ofLp = Û φ_attr.ofLp` together
with Theorem 10.3's pair-transfer positivity of the underlying attractive ground state `φ_attr`;
this is what Theorem 10.5 (Shen–Qiu–Tian) consumes on the general spin-`z` sector `Ŝ³ = m`.

**Number-operator eigenvalue.** Because Theorem 10.2's attractive ground state `φ_attr` is a spin
singlet (`Ŝ² φ_attr = 0`), its spin-`z` eigenvalue is forced to `0` (`Ŝ³ φ_attr = 0`); transporting
this through the Shiba charge exchange gives `N̂ φ = (N+1) · φ`: **every** transported ground state,
on **every** spin-`z` sector `Ŝ³ = m`, sits in the fixed `(N+1)`-electron (half-filling) sector,
independently of the electron number `Ne` used to select the attractive-model sector it is
transported from.  (Note: this is `N+1`, **not** `Ne` — the two coincide only in the special case
`Ne = N+1`.) -/
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
  -- Theorems 10.2/10.3 are applied to the shifted hopping `T' = T + diag(U/2)`.
  have hT'_symm := hoppingSymm_add_diagonal T hT_symm (fun x => U x / 2)
  have hT'_conn :
      (hoppingSupportGraph (T + Matrix.diagonal (fun x => U x / 2))).Preconnected := by
    rw [hoppingSupportGraph_add_diagonal]; exact hT_conn
  obtain ⟨Eattr, φattr, huniqueAttr, hsinglet⟩ :=
    theorem_10_2_lieb_attractive_unique_singlet N Ne hNe_even hNe_pos (by omega)
      (T + Matrix.diagonal (fun x => U x / 2)) hT'_symm hT'_conn U hU_pos
  have hpair := theorem_10_3_tian_pair_correlation_positive N Ne hNe_even hNe_pos hNe_lt
    (T + Matrix.diagonal (fun x => U x / 2)) hT'_symm hT'_conn U hU_pos huniqueAttr
  obtain ⟨ψ, hψofLp, hGS, hnum⟩ :=
    shibaTransport_uniqueGroundStateOn_spinZSector N Ne hT_symm hbip U huniqueAttr hsinglet
  exact ⟨Eattr - (∑ x : Fin (N + 1), U x) / 4, ψ, φattr, hGS, hψofLp, hpair, hnum⟩

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
