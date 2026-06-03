import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaGlobalMin
import LatticeSystem.Math.PerronFrobenius
import LatticeSystem.Math.PerronFrobeniusFinrank
import LatticeSystem.Math.HermitianMinEqOfShiftPF
import LatticeSystem.Quantum.SpinS.RealComplexEigenspaceBridge
import LatticeSystem.Quantum.SpinS.HermitianMinLeOfEigenvector

/-!
# Magnetization sectors of the one-hole Tasaki basis (Tasaki §11.2.2)

This file begins the formalization of **Tasaki Theorem 11.7** (the uniqueness
half of Nagaoka's theorem): with non-negative hopping `t ≥ 0`, `N = |Λ| - 1`,
`U = ∞`, *and the connectivity condition (Definition 11.6)*, the one-hole
ground states are exactly the `2 S_max + 1` ferromagnetic multiplet members.

The proof of Theorem 11.7 applies Perron–Frobenius to `-M` (the negated Tasaki
matrix `M = `[`tasakiEffReMatrix`]) **separately on each fixed total
`S_z^{(3)}` sector**, where `M` is block-diagonal.  This file sets up that
block structure:

* [`configMag`] — the total `S_z^{(3)}` (doubled, an integer) read off directly
  from an occupation configuration, so configurations with equal occupations
  have equal magnetization by construction.
* [`holeSpinMag`] — the magnetization of a one-hole Tasaki basis index
  `⟨x, σ⟩`, defined through its occupation configuration.
* [`configMag_hubbardSpinMove`] — hopping the hole preserves the magnetization
  (Tasaki (11.2.4); physically the electrons only rearrange).
* [`tasakiEffReMatrix_eq_zero_of_holeSpinMag_ne`] — `M` is block-diagonal with
  respect to `holeSpinMag`: an off-sector matrix element vanishes.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.2.2, Definition 11.6 and Theorem 11.7.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math.PerronFrobenius
  LatticeSystem.Math.CollatzWielandt Module

/-- The (doubled) total `S_z^{(3)}` magnetization read off an occupation
configuration `c : Fin (2N+2) → Fin 2` of the spinful chain: each site `i`
contributes `(occupation of its ↑-orbital) − (occupation of its ↓-orbital)`.
For a singly-occupied site this is `±1`; for an empty (hole) or doubly-occupied
site it is `0`.  Because it depends only on the occupations, two configurations
that are *equal as functions* have equal `configMag`. -/
def configMag (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) : ℤ :=
  ∑ i : Fin (N + 1),
    (((c (spinfulIndex N i 0)).val : ℤ) - ((c (spinfulIndex N i 1)).val : ℤ))

/-- The (doubled) total `S_z^{(3)}` magnetization of the one-hole Tasaki basis
index `⟨x, σ⟩`, defined through its occupation configuration so that it depends
only on that configuration. -/
def holeSpinMag (N : ℕ) (p : (x : Fin (N + 1)) × HoleSpin N x) : ℤ :=
  configMag N (hubbardOneHoleConfig N p.1 p.2.val)

/-- The magnetization of a one-hole configuration, expressed sitewise: the hole
site contributes `0`, every other site contributes `+1` for spin `↑` and `−1`
for spin `↓`. -/
theorem configMag_hubbardOneHoleConfig (N : ℕ) (x : Fin (N + 1))
    (σ : Fin (N + 1) → Bool) :
    configMag N (hubbardOneHoleConfig N x σ) =
      ∑ i : Fin (N + 1), (if i = x then (0 : ℤ) else if σ i then 1 else -1) := by
  unfold configMag
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hubbardOneHoleConfig_apply_up, hubbardOneHoleConfig_apply_down]
  simp only [Fin.val_inj]
  by_cases h : i = x
  · simp [h]
  · rw [if_neg h]
    by_cases hσ : σ i <;> simp [h, hσ]

/-- `holeSpinMag ⟨x, σ⟩ = 2·(electron ↑-count) − N`: each of the `N` occupied
sites contributes `±1` to `S_z^{(3)}`, and `(#↑) + (#↓) = N`.  Hence the
magnetization is determined by the number of up-electrons, which lies in
`{0, …, N}`. -/
theorem holeSpinMag_eq_two_mul_upCount_sub (N : ℕ)
    (p : (x : Fin (N + 1)) × HoleSpin N x) :
    holeSpinMag N p =
      2 * ((Finset.univ.filter (fun i => i ≠ p.1 ∧ p.2.val i = true)).card : ℤ)
        - N := by
  obtain ⟨x, σ⟩ := p
  rw [holeSpinMag, configMag_hubbardOneHoleConfig]
  have hsum : ∑ i : Fin (N + 1), (if i = x then (0 : ℤ) else if σ.val i then 1 else -1)
      = ∑ i ∈ Finset.univ.erase x, (if σ.val i then (1 : ℤ) else -1) := by
    rw [← Finset.sum_erase Finset.univ (a := x) (by simp)]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [if_neg (Finset.ne_of_mem_erase hi)]
  rw [hsum]
  have hsplit : ∑ i ∈ Finset.univ.erase x, (if σ.val i then (1 : ℤ) else -1)
      = ((Finset.univ.erase x).filter (fun i => σ.val i = true)).card
        - ((Finset.univ.erase x).filter (fun i => ¬ σ.val i = true)).card := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    ring
  rw [hsplit]
  have hcard : ((Finset.univ.erase x).filter (fun i => σ.val i = true)).card
      + ((Finset.univ.erase x).filter (fun i => ¬ σ.val i = true)).card
      = N := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem (Finset.mem_univ x),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hfilter : ((Finset.univ.erase x).filter (fun i => σ.val i = true))
      = Finset.univ.filter (fun i => i ≠ x ∧ σ.val i = true) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
  rw [← hfilter]
  omega

/-- **There are at most `N + 1` non-empty magnetization sectors.**  Since
`holeSpinMag = 2·(↑-count) − N` with the `↑`-count in `{0, …, N}`, the set of
magnetization values taken by the one-hole basis has at most `N + 1` elements.
This is the combinatorial bound behind the `2 S_max + 1 = N + 1` ground-state
degeneracy of Theorem 11.7. -/
theorem holeSpinMag_image_card_le (N : ℕ) :
    (Finset.univ.image (holeSpinMag N)).card ≤ N + 1 := by
  have hsub : Finset.univ.image (holeSpinMag N)
      ⊆ (Finset.range (N + 1)).image (fun j : ℕ => 2 * (j : ℤ) - N) := by
    intro m hm
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hm
    rw [Finset.mem_image]
    refine ⟨(Finset.univ.filter (fun i => i ≠ p.1 ∧ p.2.val i = true)).card, ?_,
      (holeSpinMag_eq_two_mul_upCount_sub N p).symm⟩
    rw [Finset.mem_range]
    have hsub2 : Finset.univ.filter (fun i => i ≠ p.1 ∧ p.2.val i = true)
        ⊆ Finset.univ.erase p.1 := by
      intro i hi
      rw [Finset.mem_filter] at hi
      exact Finset.mem_erase.mpr ⟨hi.2.1, Finset.mem_univ i⟩
    have hle : (Finset.univ.filter (fun i => i ≠ p.1 ∧ p.2.val i = true)).card ≤ N := by
      refine le_trans (Finset.card_le_card hsub2) (le_of_eq ?_)
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    omega
  calc (Finset.univ.image (holeSpinMag N)).card
      ≤ ((Finset.range (N + 1)).image (fun j : ℕ => 2 * (j : ℤ) - N)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.range (N + 1)).card := Finset.card_image_le
    _ = N + 1 := Finset.card_range _

/-- **Hopping the hole preserves magnetization** (Tasaki (11.2.4)).  Moving the
electron at `y` into the hole at `x` (turning `|Φ_{x,σ}⟩` into a basis state at
hole `y`) does not change the total `S_z^{(3)}`: the electrons merely rearrange.
-/
theorem configMag_hubbardSpinMove (N : ℕ) (x y : Fin (N + 1))
    (σ : Fin (N + 1) → Bool) (hxy : x ≠ y) :
    configMag N (hubbardOneHoleConfig N y (hubbardSpinMove N σ x y)) =
      configMag N (hubbardOneHoleConfig N x σ) := by
  rw [configMag_hubbardOneHoleConfig, configMag_hubbardOneHoleConfig,
    ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have key : ∀ i : Fin (N + 1),
      ((if i = y then (0 : ℤ) else if hubbardSpinMove N σ x y i then 1 else -1)
        - (if i = x then (0 : ℤ) else if σ i then 1 else -1))
      = (if i = x then (if σ y then (1 : ℤ) else -1) else 0)
        + (if i = y then -(if σ y then (1 : ℤ) else -1) else 0) := by
    intro i
    by_cases hix : i = x <;> by_cases hiy : i = y
    · exact absurd (hix ▸ hiy : x = y) hxy
    · subst hix; simp [hiy, hubbardSpinMove]
    · simp_all
    · simp [hubbardSpinMove, hix, hiy]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ x, Finset.sum_ite_eq' Finset.univ y]
  simp

/-- **The Tasaki matrix is block-diagonal in magnetization.**  A matrix element
`M_{⟨y,τ⟩, ⟨x,σ⟩}` between one-hole basis states of different total `S_z^{(3)}`
vanishes — `Ĥ_eff` conserves `S_z^{(3)}`, so it preserves each magnetization
sector.  (Here `M = `[`tasakiEffReMatrix`].) -/
theorem tasakiEffReMatrix_eq_zero_of_holeSpinMag_ne (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (q p : (x : Fin (N + 1)) × HoleSpin N x)
    (h : holeSpinMag N q ≠ holeSpinMag N p) :
    tasakiEffReMatrix N t q p = 0 := by
  obtain ⟨y, τ⟩ := q
  obtain ⟨x, σ⟩ := p
  unfold tasakiEffReMatrix
  by_cases hxy : x = y
  · -- diagonal block (same hole site) is unreachable here, but the entry is 0
    simp [hxy]
  · rw [if_neg (by simpa using hxy)]
    rw [if_neg ?_, mul_zero]
    intro hcfg
    apply h
    change configMag N (hubbardOneHoleConfig N y τ.val) =
      configMag N (hubbardOneHoleConfig N x σ.val)
    rw [← hcfg, configMag_hubbardSpinMove N x y σ.val hxy]

/-- **The real Tasaki matrix is symmetric.**  For symmetric hopping with zero
diagonal it equals its own transpose (derived from the complex Hermitian form
`tasakiEffMatrix_isHermitian` through `M = M_ℝ.map ofReal`). -/
theorem tasakiEffReMatrix_isSymm (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) :
    (tasakiEffReMatrix N t).IsSymm := by
  have hmap := tasakiEffMatrix_eq_map_tasakiEffReMatrix N t 0 htdiag
  simp only [Complex.ofReal_zero] at hmap
  have hH := tasakiEffMatrix_isHermitian N (fun i j => (t i j : ℂ)) (0 : ℂ)
    (tasakiEffMatrix_hJ_of_real htsym) (by simp)
  rw [hmap] at hH
  ext p q
  rw [Matrix.transpose_apply]
  have h := congr_fun₂ hH p q
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def,
    Complex.conj_ofReal] at h
  exact_mod_cast h

/-- **The off-diagonal entries of `−M` are non-negative** when the hopping is
non-negative (`t ≥ 0`).  Since `M_{q,p} = −t_{x,y}·[indicator] ≤ 0` off the
diagonal and `M` vanishes on the diagonal, `−M` is entrywise non-negative. -/
theorem neg_tasakiEffReMatrix_nonneg (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (hpos : ∀ i j, 0 ≤ t i j)
    (q p : (x : Fin (N + 1)) × HoleSpin N x) :
    0 ≤ (-tasakiEffReMatrix N t) q p := by
  obtain ⟨y, τ⟩ := q
  obtain ⟨x, σ⟩ := p
  rw [Matrix.neg_apply]
  unfold tasakiEffReMatrix
  by_cases hxy : x = y
  · simp [hxy]
  · rw [if_neg (by simpa using hxy), neg_mul, neg_neg]
    apply mul_nonneg (hpos x y)
    split <;> norm_num

/-- The magnetization sector `m`: one-hole Tasaki basis indices whose total
`S_z^{(3)}` (doubled) equals `m`.  `M` is block-diagonal across these sectors
(`tasakiEffReMatrix_eq_zero_of_holeSpinMag_ne`). -/
abbrev HoleMagSector (N : ℕ) (m : ℤ) :=
  {p : (x : Fin (N + 1)) × HoleSpin N x // holeSpinMag N p = m}

/-- The Tasaki matrix `M` restricted to a single magnetization sector `m`. -/
noncomputable def tasakiEffReMatrixOnSector (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ) :
    Matrix (HoleMagSector N m) (HoleMagSector N m) ℝ :=
  (tasakiEffReMatrix N t).submatrix Subtype.val Subtype.val

/-- The matrix `−M` restricted to a sector `m`: the entrywise non-negative
(for `t ≥ 0`) symmetric matrix to which Perron–Frobenius is applied in the
proof of Theorem 11.7. -/
noncomputable def nagaokaPFMatrixOnSector (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ) :
    Matrix (HoleMagSector N m) (HoleMagSector N m) ℝ :=
  -tasakiEffReMatrixOnSector N t m

/-- **Tasaki Definition 11.6 (connectivity condition).**  The one-hole system
is *connected* if, within every fixed total-`S_z^{(3)}` sector `m`, the basis
states are joined through non-vanishing `Ĥ_eff` matrix elements — formalized as
irreducibility (in the Perron–Frobenius sense) of `−M` restricted to that
sector.  This is the hypothesis of Tasaki Theorem 11.7.

Reference: Tasaki §11.2.2, Definition 11.6. -/
def nagaokaConnectivity (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ) : Prop :=
  ∀ m : ℤ, (nagaokaPFMatrixOnSector N t m).IsIrreducible

/-- The sector restriction of `−M` is symmetric. -/
theorem nagaokaPFMatrixOnSector_isSymm (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) :
    (nagaokaPFMatrixOnSector N t m).IsSymm := by
  unfold nagaokaPFMatrixOnSector tasakiEffReMatrixOnSector
  ext p q
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.submatrix_apply]
  rw [(tasakiEffReMatrix_isSymm N t htsym htdiag).apply]

/-- **Per-sector Perron–Frobenius (the heart of Theorem 11.7).**  On a non-empty
magnetization sector `m` satisfying the connectivity condition (Definition
11.6), `−M` has a strictly positive eigenvector at its Perron eigenvalue `μ`,
and that eigenspace is at most one-dimensional — i.e. the sector ground state is
*non-degenerate*.  (Recall `−M v = μ v ↔ M v = −μ v`, so this is the unique
ground state of `M` in the sector.) -/
theorem nagaokaPFMatrixOnSector_exists_pos_eigenvec (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ)
    [Nonempty (HoleMagSector N m)]
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0)
    (hconn : (nagaokaPFMatrixOnSector N t m).IsIrreducible) :
    ∃ (μ : ℝ) (v : HoleMagSector N m → ℝ),
      nagaokaPFMatrixOnSector N t m *ᵥ v = μ • v ∧ (∀ i, 0 < v i) ∧
      finrank ℝ (End.eigenspace
        (Matrix.toLin' (nagaokaPFMatrixOnSector N t m)) μ) ≤ 1 := by
  have hHerm : (nagaokaPFMatrixOnSector N t m).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact nagaokaPFMatrixOnSector_isSymm N t m htsym htdiag
  obtain ⟨μ, v, hAv, _hvne, hv_pos⟩ := exists_pos_eigenvec_max hHerm hconn
  exact ⟨μ, v, hAv, hv_pos,
    eigenspace_finrank_le_one_of_pos_eigenvec hconn hAv hv_pos⟩

/-- The `(-μ)`-eigenspace of `M` (on a sector) coincides with the `μ`-eigenspace
of `−M`: `−M v = μ v ↔ M v = −μ v`. -/
theorem eigenspace_tasakiEffReMatrixOnSector_eq_neg (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ) (μ : ℝ) :
    End.eigenspace (Matrix.toLin' (tasakiEffReMatrixOnSector N t m)) (-μ)
      = End.eigenspace (Matrix.toLin' (nagaokaPFMatrixOnSector N t m)) μ := by
  ext x
  rw [End.mem_eigenspace_iff, End.mem_eigenspace_iff, toLin'_apply, toLin'_apply]
  unfold nagaokaPFMatrixOnSector
  rw [neg_mulVec]
  constructor
  · intro h; rw [h, neg_smul, neg_neg]
  · intro h; rw [neg_smul]; exact neg_eq_iff_eq_neg.mp h

/-- **The sector ground state of `M` is non-degenerate (Theorem 11.7 core).**
On a non-empty connected magnetization sector, `M` has a strictly positive
eigenvector at the eigenvalue `−μ` (`μ` the Perron eigenvalue of `−M`), and that
eigenspace is at most one-dimensional.  Since `−μ = min spec M|_sector`, this is
the unique ground state of `M` within the sector. -/
theorem tasakiEffReMatrixOnSector_ground_finrank_le_one (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ)
    [Nonempty (HoleMagSector N m)]
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0)
    (hconn : (nagaokaPFMatrixOnSector N t m).IsIrreducible) :
    ∃ (lam : ℝ) (v : HoleMagSector N m → ℝ),
      tasakiEffReMatrixOnSector N t m *ᵥ v = lam • v ∧ (∀ i, 0 < v i) ∧
      finrank ℝ (End.eigenspace
        (Matrix.toLin' (tasakiEffReMatrixOnSector N t m)) lam) ≤ 1 := by
  obtain ⟨μ, v, hAv, hv_pos, hfin⟩ :=
    nagaokaPFMatrixOnSector_exists_pos_eigenvec N t m htsym htdiag hconn
  refine ⟨-μ, v, ?_, hv_pos, ?_⟩
  · have hthis : (-tasakiEffReMatrixOnSector N t m) *ᵥ v = μ • v := hAv
    rw [neg_mulVec] at hthis
    rw [neg_smul]; exact neg_eq_iff_eq_neg.mp hthis
  · rw [eigenspace_tasakiEffReMatrixOnSector_eq_neg]; exact hfin

/-- **Block invariance: restricting a coefficient eigenvector to a sector gives a
sector eigenvector.**  If `M c = E c` in the full one-hole coefficient space and
`c|_m` is the restriction of `c` to sector `m`, then `M_m (c|_m) = E (c|_m)` —
because `M` is block-diagonal in magnetization
(`tasakiEffReMatrix_eq_zero_of_holeSpinMag_ne`).  This lets the global
`E`-eigenspace decompose over sectors. -/
theorem tasakiEffReMatrixOnSector_mulVec_restriction_of_eigen (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) {m : ℤ} {E : ℝ}
    {c : (x : Fin (N + 1)) × HoleSpin N x → ℝ}
    (hc : tasakiEffReMatrix N t *ᵥ c = E • c) :
    tasakiEffReMatrixOnSector N t m *ᵥ (fun p : HoleMagSector N m => c p.val) =
      E • (fun p : HoleMagSector N m => c p.val) := by
  classical
  funext q
  have hrhs : (E • fun p : HoleMagSector N m => c p.val) q = E * c q.val := rfl
  rw [hrhs]
  change ∑ p : HoleMagSector N m,
      tasakiEffReMatrixOnSector N t m q p * c p.val = E * c q.val
  have hsec : (∑ p : HoleMagSector N m,
        tasakiEffReMatrixOnSector N t m q p * c p.val) =
      ∑ p' ∈ Finset.univ.filter (fun p' => holeSpinMag N p' = m),
        tasakiEffReMatrix N t q.val p' * c p' := by
    rw [Finset.sum_subtype
      (Finset.univ.filter (fun p' => holeSpinMag N p' = m))
      (p := fun p' => holeSpinMag N p' = m)
      (fun p' => by simp [Finset.mem_filter])
      (fun p' => tasakiEffReMatrix N t q.val p' * c p')]
    refine Finset.sum_congr rfl (fun p' _ => ?_)
    unfold tasakiEffReMatrixOnSector
    rw [Matrix.submatrix_apply]
  rw [hsec]
  have hfull : ∑ p' ∈ Finset.univ.filter (fun p' => holeSpinMag N p' = m),
        tasakiEffReMatrix N t q.val p' * c p' =
      ∑ p' : (x : Fin (N + 1)) × HoleSpin N x,
        tasakiEffReMatrix N t q.val p' * c p' := by
    refine Finset.sum_filter_of_ne (p := fun p' => holeSpinMag N p' = m) ?_
    intro p' _ hne
    by_contra hp'm
    apply hne
    have hmag_ne : holeSpinMag N q.val ≠ holeSpinMag N p' :=
      fun heq => hp'm (heq.symm.trans q.2)
    rw [tasakiEffReMatrix_eq_zero_of_holeSpinMag_ne N t q.val p' hmag_ne, zero_mul]
  rw [hfull]
  change (tasakiEffReMatrix N t *ᵥ c) q.val = _
  rw [hc]
  rfl

/-- Zero-extension of a sector vector to the full one-hole coefficient space:
`sectorEmbed v p = v p` if `p` is in sector `m`, else `0`. -/
def sectorEmbed (N : ℕ) (m : ℤ)
    (v : HoleMagSector N m → ℝ) : (x : Fin (N + 1)) × HoleSpin N x → ℝ :=
  fun p => if h : holeSpinMag N p = m then v ⟨p, h⟩ else 0

/-- **Block invariance, embedding direction: a sector eigenvector lifts to a full
eigenvector.**  If `M_m v = lam v` then `M (sectorEmbed v) = lam (sectorEmbed v)`
— because `M` is block-diagonal in magnetization, the zero-extended vector is a
genuine eigenvector of the full coefficient-space matrix at the same eigenvalue.
Hence every sector eigenvalue is a full-matrix eigenvalue (so `≥ min M`). -/
theorem tasakiEffReMatrix_mulVec_sectorEmbed_of_eigen (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) {m : ℤ} {lam : ℝ}
    {v : HoleMagSector N m → ℝ}
    (hv : tasakiEffReMatrixOnSector N t m *ᵥ v = lam • v) :
    tasakiEffReMatrix N t *ᵥ sectorEmbed N m v = lam • sectorEmbed N m v := by
  classical
  funext q
  change (∑ p', tasakiEffReMatrix N t q p' * sectorEmbed N m v p') = lam * sectorEmbed N m v q
  have hzero : ∀ p' : (x : Fin (N + 1)) × HoleSpin N x,
      holeSpinMag N p' ≠ m → tasakiEffReMatrix N t q p' * sectorEmbed N m v p' = 0 := by
    intro p' hp'
    simp [sectorEmbed, hp']
  by_cases hq : holeSpinMag N q = m
  · -- q in sector m: full sum collapses to the sector sum = (M_m v) ⟨q⟩.
    have hfilter : (∑ p', tasakiEffReMatrix N t q p' * sectorEmbed N m v p') =
        ∑ p' ∈ Finset.univ.filter (fun p' => holeSpinMag N p' = m),
          tasakiEffReMatrix N t q p' * sectorEmbed N m v p' := by
      refine (Finset.sum_filter_of_ne (fun p' _ hne => ?_)).symm
      by_contra h; exact hne (hzero p' h)
    have hsub : (∑ p' ∈ Finset.univ.filter (fun p' => holeSpinMag N p' = m),
          tasakiEffReMatrix N t q p' * sectorEmbed N m v p') =
        ∑ p : HoleMagSector N m, tasakiEffReMatrixOnSector N t m ⟨q, hq⟩ p * v p := by
      rw [Finset.sum_subtype
        (Finset.univ.filter (fun p' => holeSpinMag N p' = m))
        (p := fun p' => holeSpinMag N p' = m)
        (fun p' => by simp [Finset.mem_filter])
        (fun p' => tasakiEffReMatrix N t q p' * sectorEmbed N m v p')]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      simp only [sectorEmbed, dif_pos p.property, Subtype.coe_eta]
      unfold tasakiEffReMatrixOnSector
      rw [Matrix.submatrix_apply]
    rw [hfilter, hsub]
    have heig := congrFun hv ⟨q, hq⟩
    change (∑ p, tasakiEffReMatrixOnSector N t m ⟨q, hq⟩ p * v p) = lam * v ⟨q, hq⟩ at heig
    rw [heig]
    simp [sectorEmbed, dif_pos hq]
  · -- q outside sector m: both sides are 0.
    have hlhs : (∑ p', tasakiEffReMatrix N t q p' * sectorEmbed N m v p') = 0 := by
      refine Finset.sum_eq_zero (fun p' _ => ?_)
      by_cases hp' : holeSpinMag N p' = m
      · rw [tasakiEffReMatrix_eq_zero_of_holeSpinMag_ne N t q p' (by rw [hp']; exact hq),
          zero_mul]
      · exact hzero p' hp'
    rw [hlhs]
    simp [sectorEmbed, dif_neg hq]

/-- The real Tasaki matrix restricted to a sector is symmetric. -/
theorem tasakiEffReMatrixOnSector_isSymm (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) :
    (tasakiEffReMatrixOnSector N t m).IsSymm := by
  unfold tasakiEffReMatrixOnSector
  ext p q
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply]
  rw [(tasakiEffReMatrix_isSymm N t htsym htdiag).apply]

/-- **The sector minimum eigenvalue equals `−μ` (the negated Perron eigenvalue).**
For a non-empty connected sector with `t ≥ 0`, the minimum eigenvalue of the
(complex-cast) sector matrix `M_m` is `−μ`, where `μ` is the Perron eigenvalue of
`−M_m`.  Combines Collatz–Wielandt's `hermitianMinEigenvalue = c − μ_PF` (with
shift `c = 0`) with the per-sector Perron–Frobenius eigenvector. -/
theorem hermitianMinEigenvalue_sector_eq_neg_pf (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ)
    [Nonempty (HoleMagSector N m)]
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0)
    (hpos : ∀ i j, 0 ≤ t i j)
    (hconn : (nagaokaPFMatrixOnSector N t m).IsIrreducible) :
    ∃ (μ : ℝ) (v : HoleMagSector N m → ℝ),
      nagaokaPFMatrixOnSector N t m *ᵥ v = μ • v ∧ (∀ i, 0 < v i) ∧
      LatticeSystem.Quantum.hermitianMinEigenvalue
        (isHermitian_map_ofReal_of_isSymm
          (tasakiEffReMatrixOnSector_isSymm N t m htsym htdiag)) = -μ := by
  obtain ⟨μ, v, hAv, hv_pos, _⟩ :=
    nagaokaPFMatrixOnSector_exists_pos_eigenvec N t m htsym htdiag hconn
  refine ⟨μ, v, hAv, hv_pos, ?_⟩
  have hsymM := tasakiEffReMatrixOnSector_isSymm N t m htsym htdiag
  have hBeq : (0 : ℝ) • (1 : Matrix (HoleMagSector N m) (HoleMagSector N m) ℝ)
      - tasakiEffReMatrixOnSector N t m = nagaokaPFMatrixOnSector N t m := by
    rw [zero_smul, zero_sub]; rfl
  have hBnn : ∀ i j,
      0 ≤ ((0 : ℝ) • (1 : Matrix (HoleMagSector N m) (HoleMagSector N m) ℝ)
        - tasakiEffReMatrixOnSector N t m) i j := by
    intro i j
    rw [hBeq]
    change 0 ≤ (-tasakiEffReMatrixOnSector N t m) i j
    rw [Matrix.neg_apply]
    unfold tasakiEffReMatrixOnSector
    rw [Matrix.submatrix_apply]
    have hfull := neg_tasakiEffReMatrix_nonneg N t hpos i.val j.val
    rwa [Matrix.neg_apply] at hfull
  have hBsymm : ((0 : ℝ) • (1 : Matrix (HoleMagSector N m) (HoleMagSector N m) ℝ)
      - tasakiEffReMatrixOnSector N t m).IsSymm := by
    rw [hBeq]; exact nagaokaPFMatrixOnSector_isSymm N t m htsym htdiag
  have h_eig : ((0 : ℝ) • (1 : Matrix (HoleMagSector N m) (HoleMagSector N m) ℝ)
      - tasakiEffReMatrixOnSector N t m) *ᵥ v = μ • v := by
    rw [hBeq]; exact hAv
  have hmin := hermitianMinEigenvalue_lift_eq_sub_pf hsymM 0 hBnn hBsymm h_eig hv_pos
  rwa [zero_sub] at hmin

/-- **The global one-hole minimum is `≤` each sector minimum.**  For a non-empty
connected sector, a Perron ground eigenvector of `−M_m` lifts (zero-extended,
complexified) to a genuine eigenvector of the full `Ĥ_eff` matrix at the sector
minimum `−μ`, so the global minimum `hermitianMinEigenvalue M` is `≤ −μ`.
Combined with [`hermitianMinEigenvalue_sector_eq_neg_pf`] this gives
`min M ≤ min M_m` — the variational (principal-submatrix) inequality. -/
theorem hermitianMinEigenvalue_tasakiEffMatrix_le_sector (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ)
    [Nonempty (HoleMagSector N m)]
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0)
    (hpos : ∀ i j, 0 ≤ t i j)
    (hconn : (nagaokaPFMatrixOnSector N t m).IsIrreducible) :
    ∃ μ : ℝ,
      LatticeSystem.Quantum.hermitianMinEigenvalue
        (tasakiEffMatrix_isHermitian N (fun i j => (t i j : ℂ)) 0
          (tasakiEffMatrix_hJ_of_real htsym) (by simp)) ≤ -μ ∧
      LatticeSystem.Quantum.hermitianMinEigenvalue
        (isHermitian_map_ofReal_of_isSymm
          (tasakiEffReMatrixOnSector_isSymm N t m htsym htdiag)) = -μ := by
  obtain ⟨μ, v, hAv, hv_pos, hmineq⟩ :=
    hermitianMinEigenvalue_sector_eq_neg_pf N t m htsym htdiag hpos hconn
  refine ⟨μ, ?_, hmineq⟩
  have hMv : tasakiEffReMatrixOnSector N t m *ᵥ v = (-μ) • v := by
    have hneg : (-tasakiEffReMatrixOnSector N t m) *ᵥ v = μ • v := hAv
    rw [neg_mulVec] at hneg
    rw [neg_smul]; exact neg_eq_iff_eq_neg.mp hneg
  have hembed := tasakiEffReMatrix_mulVec_sectorEmbed_of_eigen N t hMv
  have hcx := matrix_eigenvec_map_ofReal hembed
  rw [← tasakiEffMatrix_eq_map_tasakiEffReMatrix N t 0 htdiag] at hcx
  have hw_ne : (fun p => ((sectorEmbed N m v p : ℝ) : ℂ)) ≠ 0 := by
    intro h
    have h0 := congrFun h (Classical.arbitrary (HoleMagSector N m)).val
    simp only [Pi.zero_apply, Complex.ofReal_eq_zero, sectorEmbed,
      dif_pos (Classical.arbitrary (HoleMagSector N m)).property] at h0
    exact absurd h0 (ne_of_gt (hv_pos _))
  exact hermitian_min_eigenvalue_le_of_eigenvector_exists _ hw_ne hcx

/-- **Each sector contributes at most one ground state at the global minimum.**
At any energy `E ≤ min M_m`, the (complex) sector eigenspace is at most
one-dimensional: if `E < min M_m` it is `⊥` (energy below the spectrum); if
`E = min M_m = −μ` it is the Perron ground eigenspace (`finrank ≤ 1`, real PF
bridged to `ℂ`).  Applied at the global minimum `E = min M` (which is `≤` every
sector minimum), this caps every sector's contribution to the `Ĥ_eff` ground
eigenspace at `1`. -/
theorem sector_map_eigenspace_finrank_le_one_at (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ)
    [Nonempty (HoleMagSector N m)]
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0)
    (hpos : ∀ i j, 0 ≤ t i j)
    (hconn : (nagaokaPFMatrixOnSector N t m).IsIrreducible) (E : ℝ)
    (hE : E ≤ LatticeSystem.Quantum.hermitianMinEigenvalue
      (isHermitian_map_ofReal_of_isSymm
        (tasakiEffReMatrixOnSector_isSymm N t m htsym htdiag))) :
    finrank ℂ (End.eigenspace
      (Matrix.toLin' ((tasakiEffReMatrixOnSector N t m).map (algebraMap ℝ ℂ)))
      (E : ℂ)) ≤ 1 := by
  rcases lt_or_eq_of_le hE with hlt | heq
  · rw [hermitian_eigenspace_eq_bot_of_real_lt_min
      (isHermitian_map_ofReal_of_isSymm (tasakiEffReMatrixOnSector_isSymm N t m htsym htdiag))
      hlt]
    simp
  · obtain ⟨μ, v, hAv, hv_pos, hmineq⟩ :=
      hermitianMinEigenvalue_sector_eq_neg_pf N t m htsym htdiag hpos hconn
    have hfin_neg : finrank ℝ (End.eigenspace
        (Matrix.toLin' (tasakiEffReMatrixOnSector N t m)) (-μ)) ≤ 1 := by
      rw [eigenspace_tasakiEffReMatrixOnSector_eq_neg]
      exact eigenspace_finrank_le_one_of_pos_eigenvec hconn hAv hv_pos
    have hcx := matrix_complex_eigenspace_finrank_le_one_of_real
      (tasakiEffReMatrixOnSector N t m) (-μ) hfin_neg
    have hEμ : E = -μ := by rw [heq, hmineq]
    rw [hEμ]
    exact hcx

/-- The complex-cast Tasaki matrix is block-diagonal in magnetization. -/
theorem tasakiEffReMatrix_map_eq_zero_of_holeSpinMag_ne (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (q p : (x : Fin (N + 1)) × HoleSpin N x)
    (h : holeSpinMag N q ≠ holeSpinMag N p) :
    ((tasakiEffReMatrix N t).map (algebraMap ℝ ℂ)) q p = 0 := by
  rw [Matrix.map_apply, tasakiEffReMatrix_eq_zero_of_holeSpinMag_ne N t q p h, map_zero]

/-- **Complex block invariance: restricting a complex eigenvector to a sector.**
If the complex-cast `Ĥ_eff` matrix has `M c = E c`, then the restriction of `c`
to magnetization sector `m` is an eigenvector of the complex sector matrix at
`E`.  (Complex analogue of `tasakiEffReMatrixOnSector_mulVec_restriction_of_eigen`;
uses block-diagonality.) -/
theorem tasakiEffMatrixOnSector_map_mulVec_restriction_of_eigen (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) {m : ℤ} {E : ℂ}
    {c : (x : Fin (N + 1)) × HoleSpin N x → ℂ}
    (hc : (tasakiEffReMatrix N t).map (algebraMap ℝ ℂ) *ᵥ c = E • c) :
    ((tasakiEffReMatrixOnSector N t m).map (algebraMap ℝ ℂ)) *ᵥ
        (fun p : HoleMagSector N m => c p.val) =
      E • (fun p : HoleMagSector N m => c p.val) := by
  classical
  funext q
  change ∑ p : HoleMagSector N m,
      ((tasakiEffReMatrixOnSector N t m).map (algebraMap ℝ ℂ)) q p * c p.val = E * c q.val
  have hsec : (∑ p : HoleMagSector N m,
        ((tasakiEffReMatrixOnSector N t m).map (algebraMap ℝ ℂ)) q p * c p.val) =
      ∑ p' ∈ Finset.univ.filter (fun p' => holeSpinMag N p' = m),
        ((tasakiEffReMatrix N t).map (algebraMap ℝ ℂ)) q.val p' * c p' := by
    rw [Finset.sum_subtype
      (Finset.univ.filter (fun p' => holeSpinMag N p' = m))
      (p := fun p' => holeSpinMag N p' = m)
      (fun p' => by simp [Finset.mem_filter])
      (fun p' => ((tasakiEffReMatrix N t).map (algebraMap ℝ ℂ)) q.val p' * c p')]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    unfold tasakiEffReMatrixOnSector
    rw [Matrix.map_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rw [hsec]
  have hfull : ∑ p' ∈ Finset.univ.filter (fun p' => holeSpinMag N p' = m),
        ((tasakiEffReMatrix N t).map (algebraMap ℝ ℂ)) q.val p' * c p' =
      ∑ p' : (x : Fin (N + 1)) × HoleSpin N x,
        ((tasakiEffReMatrix N t).map (algebraMap ℝ ℂ)) q.val p' * c p' := by
    refine Finset.sum_filter_of_ne (p := fun p' => holeSpinMag N p' = m) ?_
    intro p' _ hne
    by_contra hp'm
    apply hne
    have hmag_ne : holeSpinMag N q.val ≠ holeSpinMag N p' :=
      fun heq => hp'm (heq.symm.trans q.2)
    rw [tasakiEffReMatrix_map_eq_zero_of_holeSpinMag_ne N t q.val p' hmag_ne, zero_mul]
  rw [hfull]
  change ((tasakiEffReMatrix N t).map (algebraMap ℝ ℂ) *ᵥ c) q.val = _
  rw [hc]
  rfl

/-- **The `Ĥ_eff` ground eigenspace is at most `(N+1)`-dimensional.**  Given that
each magnetization sector contributes at most one dimension at energy `E`
(`hsector`, supplied by Perron–Frobenius at the global minimum), the full
coefficient-space `E`-eigenspace embeds (by restriction to sectors) into the
product of the sector eigenspaces over the `≤ N+1` magnetization values, so its
dimension is at most `N + 1 = 2 S_max + 1`.  This is the upper bound matching the
ferromagnetic multiplet (Tasaki Theorem 11.7). -/
theorem tasakiEffMatrix_ground_finrank_le (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (E : ℂ)
    (hsector : ∀ m : ℤ, finrank ℂ (End.eigenspace
      (Matrix.toLin' ((tasakiEffReMatrixOnSector N t m).map (algebraMap ℝ ℂ))) E) ≤ 1) :
    finrank ℂ (End.eigenspace
      (Matrix.toLin' ((tasakiEffReMatrix N t).map (algebraMap ℝ ℂ))) E) ≤ N + 1 := by
  classical
  set img := Finset.univ.image (holeSpinMag N) with himg
  let Vsub := End.eigenspace
    (Matrix.toLin' ((tasakiEffReMatrix N t).map (algebraMap ℝ ℂ))) E
  let Wsub := fun m : ℤ => End.eigenspace
    (Matrix.toLin' ((tasakiEffReMatrixOnSector N t m).map (algebraMap ℝ ℂ))) E
  let L : Vsub →ₗ[ℂ] (∀ i : {m // m ∈ img}, Wsub i.val) := {
    toFun := fun c i => ⟨fun p : HoleMagSector N i.val => c.val p.val, by
      have hc : (tasakiEffReMatrix N t).map (algebraMap ℝ ℂ) *ᵥ c.val = E • c.val := by
        have := End.mem_eigenspace_iff.mp c.2
        rwa [Matrix.toLin'_apply] at this
      rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact tasakiEffMatrixOnSector_map_mulVec_restriction_of_eigen N t hc⟩
    map_add' := fun c c' => by funext i; apply Subtype.ext; funext p; rfl
    map_smul' := fun a c => by funext i; apply Subtype.ext; funext p; rfl }
  have hL_inj : Function.Injective L := by
    intro c c' hcc
    apply Subtype.ext
    funext p
    have hmem : holeSpinMag N p ∈ img := by
      rw [himg, Finset.mem_image]; exact ⟨p, Finset.mem_univ p, rfl⟩
    have := congrFun hcc ⟨holeSpinMag N p, hmem⟩
    have hval := congrFun (Subtype.ext_iff.mp this) ⟨p, rfl⟩
    exact hval
  calc finrank ℂ Vsub
      ≤ finrank ℂ (∀ i : {m // m ∈ img}, Wsub i.val) :=
        LinearMap.finrank_le_finrank_of_injective hL_inj
    _ = ∑ i : {m // m ∈ img}, finrank ℂ (Wsub i.val) := Module.finrank_pi_fintype ℂ
    _ ≤ ∑ _i : {m // m ∈ img}, 1 := Finset.sum_le_sum (fun i _ => hsector i.val)
    _ = img.card := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul,
        mul_one]
    _ ≤ N + 1 := holeSpinMag_image_card_le N

/-- **`min M ≤ min M_m` with the lifted (`.map ofReal`) full witness.**  The
sector minimum `−μ` is an eigenvalue of the full `Ĥ_eff` matrix (Perron ground
of `−M_m`, zero-extended and complexified), so the global minimum is `≤ −μ`. -/
theorem hermitianMinEigenvalue_mapFull_le_sector (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ)
    [Nonempty (HoleMagSector N m)]
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0)
    (hpos : ∀ i j, 0 ≤ t i j)
    (hconn : (nagaokaPFMatrixOnSector N t m).IsIrreducible) :
    LatticeSystem.Quantum.hermitianMinEigenvalue
        (isHermitian_map_ofReal_of_isSymm (tasakiEffReMatrix_isSymm N t htsym htdiag))
      ≤ LatticeSystem.Quantum.hermitianMinEigenvalue
        (isHermitian_map_ofReal_of_isSymm
          (tasakiEffReMatrixOnSector_isSymm N t m htsym htdiag)) := by
  obtain ⟨μ, v, hAv, hv_pos, hmineq⟩ :=
    hermitianMinEigenvalue_sector_eq_neg_pf N t m htsym htdiag hpos hconn
  rw [hmineq]
  have hMv : tasakiEffReMatrixOnSector N t m *ᵥ v = (-μ) • v := by
    have hneg : (-tasakiEffReMatrixOnSector N t m) *ᵥ v = μ • v := hAv
    rw [neg_mulVec] at hneg
    rw [neg_smul]; exact neg_eq_iff_eq_neg.mp hneg
  have hembed := tasakiEffReMatrix_mulVec_sectorEmbed_of_eigen N t hMv
  have hcx := matrix_eigenvec_map_ofReal hembed
  have hw_ne : (fun p => ((sectorEmbed N m v p : ℝ) : ℂ)) ≠ 0 := by
    intro h
    have h0 := congrFun h (Classical.arbitrary (HoleMagSector N m)).val
    simp only [Pi.zero_apply, Complex.ofReal_eq_zero, sectorEmbed,
      dif_pos (Classical.arbitrary (HoleMagSector N m)).property] at h0
    exact absurd h0 (ne_of_gt (hv_pos _))
  exact hermitian_min_eigenvalue_le_of_eigenvector_exists _ hw_ne hcx

/-- **The `Ĥ_eff` ground eigenspace has dimension `≤ N+1` at the global minimum**
(upper-bound half of Tasaki Theorem 11.7).  Under the connectivity condition
(`nagaokaConnectivity`) and `t ≥ 0`, every magnetization sector contributes at
most one ground state: non-empty connected sectors by Perron–Frobenius
(`sector_map_eigenspace_finrank_le_one_at`, using `min M ≤ min M_m`), empty
sectors trivially.  With `≤ N+1` sectors this caps the dimension at `N + 1`. -/
theorem tasakiEffMatrix_ground_finrank_le_N_add_one (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0)
    (hpos : ∀ i j, 0 ≤ t i j)
    (hconn : nagaokaConnectivity N t) :
    finrank ℂ (End.eigenspace
      (Matrix.toLin' ((tasakiEffReMatrix N t).map (algebraMap ℝ ℂ)))
      ((LatticeSystem.Quantum.hermitianMinEigenvalue
        (isHermitian_map_ofReal_of_isSymm (tasakiEffReMatrix_isSymm N t htsym htdiag)) : ℂ)))
      ≤ N + 1 := by
  set E := LatticeSystem.Quantum.hermitianMinEigenvalue
    (isHermitian_map_ofReal_of_isSymm (tasakiEffReMatrix_isSymm N t htsym htdiag)) with hE
  apply tasakiEffMatrix_ground_finrank_le N t (E : ℂ)
  intro m
  by_cases hne : Nonempty (HoleMagSector N m)
  · letI := hne
    exact sector_map_eigenspace_finrank_le_one_at N t m htsym htdiag hpos (hconn m) E
      (hE ▸ hermitianMinEigenvalue_mapFull_le_sector N t m htsym htdiag hpos (hconn m))
  · rw [not_nonempty_iff] at hne
    haveI := hne
    have hcard : finrank ℂ (HoleMagSector N m → ℂ) = 0 := by
      rw [Module.finrank_pi, Fintype.card_eq_zero]
    calc finrank ℂ (End.eigenspace
          (Matrix.toLin' ((tasakiEffReMatrixOnSector N t m).map (algebraMap ℝ ℂ))) (E : ℂ))
        ≤ finrank ℂ (HoleMagSector N m → ℂ) := Submodule.finrank_le _
      _ = 0 := hcard
      _ ≤ 1 := by norm_num

/-! ## Bridge: coefficient eigenvectors ↔ full `Ĥ_eff` ground states -/

/-- The Tasaki coefficient functional `⟨Φ_q, v⟩ = Σ_w Φ_q(w) v(w)`.  On a
one-hole-supported vector this recovers the Tasaki expansion coefficients. -/
noncomputable def tasakiCoeff (N : ℕ) (v : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    ((x : Fin (N + 1)) × HoleSpin N x) → ℂ :=
  fun q => ∑ w, tasakiState N q w * v w

/-- **Left inverse: the coefficient functional inverts the Tasaki expansion.**
`tasakiCoeff (Σ_p c_p Φ_p) = c` — the basis `Φ_q` being orthonormal.  Hence the
expansion `c ↦ Σ_p c_p Φ_p` is injective. -/
theorem tasakiCoeff_expansion (N : ℕ)
    (c : ((x : Fin (N + 1)) × HoleSpin N x) → ℂ) :
    tasakiCoeff N (∑ p, c p • tasakiState N p) = c := by
  funext q
  unfold tasakiCoeff
  have hstep : ∀ w, tasakiState N q w * (∑ p, c p • tasakiState N p) w
      = ∑ p, c p * (tasakiState N q w * tasakiState N p w) := by
    intro w
    rw [Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by rw [Pi.smul_apply, smul_eq_mul]; ring)
  rw [Finset.sum_congr rfl (fun w _ => hstep w), Finset.sum_comm]
  rw [show (∑ p, ∑ w, c p * (tasakiState N q w * tasakiState N p w))
      = ∑ p, c p * (∑ w, tasakiState N q w * tasakiState N p w) from
    Finset.sum_congr rfl (fun p _ => by rw [Finset.mul_sum])]
  rw [Finset.sum_congr rfl (fun p _ => by rw [tasakiState_orthonormal])]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ q (fun p => c p), if_pos (Finset.mem_univ q)]

/-- **Backward bridge (hardest step): a full one-hole `Ĥ_eff`-eigenvector gives a
coefficient `M`-eigenvector.**  If `Ĥ_eff v = E v` and `v` is supported on the
one-hole hard-core sector, then its Tasaki coefficients satisfy `M c = E c`.
Combines completeness (`v = Σ c_q Φ_q`), the operator lift (`Ĥ_eff (Σ c Φ) =
Σ (M c) Φ`) and the left-inverse `tasakiCoeff_expansion`. -/
theorem tasakiCoeff_mulVec_eigen_of_full (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) (E : ℂ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hsupp : ∀ w, ¬ IsOneHoleHardcoreConfig N w → v w = 0)
    (hv : (hubbardEffectiveHamiltonian N t U).mulVec v = E • v) :
    (tasakiEffMatrix N t U).mulVec (tasakiCoeff N v) = E • tasakiCoeff N v := by
  have hexp : v = ∑ q, tasakiCoeff N v q • tasakiState N q := tasaki_completeness N v hsupp
  -- `Ĥ_eff v = Σ (M c) Φ`, and `Ĥ_eff v = E v = Σ (E c) Φ`.
  have hlift : (hubbardEffectiveHamiltonian N t U).mulVec v
      = ∑ q, ((tasakiEffMatrix N t U).mulVec (tasakiCoeff N v)) q • tasakiState N q := by
    conv_lhs => rw [hexp]
    rw [hubbardEffectiveHamiltonian_mulVec_tasakiExpansion]
  have hEv : E • v = ∑ q, (E • tasakiCoeff N v) q • tasakiState N q := by
    conv_lhs => rw [hexp]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun q _ => by rw [Pi.smul_apply, smul_smul, smul_eq_mul])
  have hEq : (∑ q, ((tasakiEffMatrix N t U).mulVec (tasakiCoeff N v)) q • tasakiState N q)
      = ∑ q, (E • tasakiCoeff N v) q • tasakiState N q := by rw [← hlift, hv, hEv]
  -- Apply the left inverse to both Tasaki expansions.
  have hfin := congrArg (tasakiCoeff N) hEq
  rwa [tasakiCoeff_expansion, tasakiCoeff_expansion] at hfin

/-! ## The spin-lowering tower stays in the one-hole sector -/

/-- `Ŝ^-_tot` conserves the total particle number (it is `Σ c†_{i↓} c_{i↑}`). -/
theorem fermionTotalSpinMinus_commute_fermionTotalNumber (N : ℕ) :
    Commute (fermionTotalSpinMinus N) (fermionTotalNumber (2 * N + 1)) := by
  unfold fermionTotalSpinMinus
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  unfold fermionDownCreation fermionUpAnnihilation
  exact (fermionTotalNumber_commute_hopping (2 * N + 1)
    (spinfulIndex N i 1) (spinfulIndex N i 0)).symm

/-- `Ŝ^-_tot` preserves the hard-core (no-double-occupancy) subspace: it commutes
with the hard-core projection (adjoint of the `Ŝ^+_tot` version, using
`(Ŝ^+)ᴴ = Ŝ^-` and the projection's Hermiticity). -/
theorem fermionTotalSpinMinus_commute_hubbardHardcoreProjection (N : ℕ) :
    Commute (fermionTotalSpinMinus N) (hubbardHardcoreProjection N) := by
  have h := fermionTotalSpinPlus_commute_hubbardHardcoreProjection N
  have hP := hubbardHardcoreProjection_isHermitian N
  have hct := congrArg Matrix.conjTranspose h
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    fermionTotalSpinPlus_conjTranspose, hP] at hct
  exact hct.symm

/-- `Ŝ^-_tot` maps the hard-core subspace into itself. -/
theorem fermionTotalSpinMinus_mulVec_mem_hardcore (N : ℕ)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ} (hv : v ∈ hubbardHardcoreSubspace N) :
    (fermionTotalSpinMinus N).mulVec v ∈ hubbardHardcoreSubspace N := by
  have hself : (hubbardHardcoreProjection N).mulVec ((fermionTotalSpinMinus N).mulVec v)
      = (fermionTotalSpinMinus N).mulVec v := by
    rw [Matrix.mulVec_mulVec,
      (fermionTotalSpinMinus_commute_hubbardHardcoreProjection N).symm.eq,
      ← Matrix.mulVec_mulVec, hubbardHardcoreProjection_mulVec_eq_self_of_mem N hv]
  rw [← hself]
  exact hubbardHardcoreProjection_mulVec_mem N _

/-- `Ŝ^-_tot` preserves the total-particle-number eigenvalue. -/
theorem fermionTotalSpinMinus_mulVec_preserves_number (N : ℕ)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : (fermionTotalNumber (2 * N + 1)).mulVec v = (N : ℂ) • v) :
    (fermionTotalNumber (2 * N + 1)).mulVec ((fermionTotalSpinMinus N).mulVec v)
      = (N : ℂ) • ((fermionTotalSpinMinus N).mulVec v) := by
  rw [Matrix.mulVec_mulVec,
    (fermionTotalSpinMinus_commute_fermionTotalNumber N).symm.eq,
    ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

/-- The tower `(Ŝ^-)^k v` stays in the hard-core subspace. -/
theorem fermionTotalSpinMinus_pow_mulVec_mem_hardcore (N : ℕ) (k : ℕ)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ} (hv : v ∈ hubbardHardcoreSubspace N) :
    ((fermionTotalSpinMinus N) ^ k).mulVec v ∈ hubbardHardcoreSubspace N := by
  induction k with
  | zero => rwa [pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact fermionTotalSpinMinus_mulVec_mem_hardcore N ih

/-- The tower `(Ŝ^-)^k v` keeps the total-particle-number eigenvalue `N`. -/
theorem fermionTotalSpinMinus_pow_mulVec_preserves_number (N : ℕ) (k : ℕ)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : (fermionTotalNumber (2 * N + 1)).mulVec v = (N : ℂ) • v) :
    (fermionTotalNumber (2 * N + 1)).mulVec (((fermionTotalSpinMinus N) ^ k).mulVec v)
      = (N : ℂ) • (((fermionTotalSpinMinus N) ^ k).mulVec v) := by
  induction k with
  | zero => rwa [pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact fermionTotalSpinMinus_mulVec_preserves_number N ih

/-- Each Tasaki basis state lies in the hard-core subspace. -/
theorem tasakiState_mem_hardcore (N : ℕ) (p : (x : Fin (N + 1)) × HoleSpin N x) :
    tasakiState N p ∈ hubbardHardcoreSubspace N := by
  rw [tasakiState, hubbardTasakiBasisState_eq_smul_basisVec]
  exact Submodule.smul_mem _ _
    (hubbardHardcoreBasisState_mem_hardcoreSubspace N p.1 p.2.val)

/-- The ferromagnetic ground state `pfFerroState` lies in the hard-core subspace. -/
theorem pfFerroState_mem_hardcore (N : ℕ) (ξ : Fin (N + 1) → ℂ) :
    pfFerroState N ξ ∈ hubbardHardcoreSubspace N := by
  unfold pfFerroState
  exact Submodule.sum_mem _ (fun x _ =>
    Submodule.smul_mem _ _ (tasakiState_mem_hardcore N _))

/-- `pfFerroState` is an `N`-electron state. -/
theorem fermionTotalNumber_mulVec_pfFerroState (N : ℕ) (ξ : Fin (N + 1) → ℂ) :
    (fermionTotalNumber (2 * N + 1)).mulVec (pfFerroState N ξ) =
      (N : ℂ) • pfFerroState N ξ := by
  unfold pfFerroState
  rw [Matrix.mulVec_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.mulVec_smul, fermionTotalNumber_mulVec_tasakiState, smul_comm]

/-- **The spin tower of `pfFerroState` is one-hole supported.**  `(Ŝ^-)^k Φ_↑`
stays in the hard-core `N`-electron sector, hence vanishes off the one-hole
hard-core configurations. -/
theorem spinMinusPow_pfFerroState_oneHole_supported (N : ℕ) (ξ : Fin (N + 1) → ℂ)
    (k : ℕ) (w : Fin (2 * N + 2) → Fin 2) (hw : ¬ IsOneHoleHardcoreConfig N w) :
    (((fermionTotalSpinMinus N) ^ k).mulVec (pfFerroState N ξ)) w = 0 :=
  mulVec_apply_eq_zero_of_not_oneHole N _
    (fermionTotalSpinMinus_pow_mulVec_mem_hardcore N k (pfFerroState_mem_hardcore N ξ))
    (fermionTotalSpinMinus_pow_mulVec_preserves_number N k
      (fermionTotalNumber_mulVec_pfFerroState N ξ)) w hw

/-- The Tasaki embedding's `mulVec` is the Tasaki expansion. -/
theorem tasakiEmbedding_mulVec_eq (N : ℕ)
    (c : ((x : Fin (N + 1)) × HoleSpin N x) → ℂ) :
    (tasakiEmbedding N).mulVec c = ∑ q, c q • tasakiState N q := by
  funext w
  simp only [Matrix.mulVec, dotProduct, tasakiEmbedding, Matrix.of_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun q _ => mul_comm _ _)

/-- **Lower bound (`≥ N+1`) from the ferromagnetic multiplet.**  The `N+1`
linearly independent tower states `(Ŝ^-)^k Φ_↑` are one-hole supported
`Ĥ_eff`-eigenvectors at the minimum `E`, so their Tasaki coefficients are `N+1`
linearly independent `M`-eigenvectors — hence the coefficient ground eigenspace
has dimension `≥ N+1`. -/
theorem tasakiEffMatrix_ground_finrank_ge (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) :
    N + 1 ≤ finrank ℂ (End.eigenspace (Matrix.toLin'
      (tasakiEffMatrix N (fun i j => (t i j : ℂ)) 0))
      (((hermitianMinEigenvalue (tasakiEffMatrixUp_isHermitian N
        (fun i j => (t i j : ℂ)) 0 (tasakiEffMatrix_hJ_of_real htsym)
        (by simp))) : ℝ) : ℂ)) := by
  have hJ := tasakiEffMatrix_hJ_of_real htsym
  have hU0 : star (0 : ℂ) = 0 := by simp
  obtain ⟨ξ, hξ_ne, hξ_eig⟩ := exists_nonzero_eigenvector_hermitianMinEigenvalue
    (tasakiEffMatrixUp_isHermitian N (fun i j => (t i j : ℂ)) 0 hJ hU0)
  set E : ℂ := ((hermitianMinEigenvalue (tasakiEffMatrixUp_isHermitian N
    (fun i j => (t i j : ℂ)) 0 hJ hU0) : ℝ) : ℂ) with hEdef
  have hv0_eig := hubbardEffectiveHamiltonian_mulVec_pfFerroState_of_eigen N
    (fun i j => (t i j : ℂ)) 0 (fun i => by simp [htdiag i]) ξ E hξ_eig
  obtain ⟨hLI, hdeg, _⟩ := weakNagaoka_spinMultiplet N (fun i j => (t i j : ℂ)) 0 hJ hU0
    (pfFerroState N ξ) E hv0_eig (fermionTotalSpinPlus_mulVec_pfFerroState N ξ)
    (fermionTotalSpinZ_mulVec_pfFerroState N ξ) (pfFerroState_ne_zero N ξ hξ_ne)
  set tower : Fin (N + 1) → (Fin (2 * N + 2) → Fin 2) → ℂ :=
    fun k => ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec (pfFerroState N ξ) with htower
  set cfn : Fin (N + 1) → ((x : Fin (N + 1)) × HoleSpin N x) → ℂ :=
    fun k => tasakiCoeff N (tower k) with hcfn
  set W := End.eigenspace (Matrix.toLin'
    (tasakiEffMatrix N (fun i j => (t i j : ℂ)) 0)) E with hWdef
  have hc_mem : ∀ k, cfn k ∈ W := by
    intro k
    rw [hWdef, End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact tasakiCoeff_mulVec_eigen_of_full N (fun i j => (t i j : ℂ)) 0 E (tower k)
      (spinMinusPow_pfFerroState_oneHole_supported N ξ k) (hdeg k)
  have hcLI : LinearIndependent ℂ cfn := by
    have htower_eq : tower = (Matrix.mulVecLin (tasakiEmbedding N)) ∘ cfn := by
      funext k
      rw [Function.comp_apply, Matrix.mulVecLin_apply, tasakiEmbedding_mulVec_eq]
      exact tasaki_completeness N (tower k)
        (spinMinusPow_pfFerroState_oneHole_supported N ξ k)
    rw [htower_eq] at hLI
    exact hLI.of_comp _
  have hWLI : LinearIndependent ℂ (fun k => (⟨cfn k, hc_mem k⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hcLI
  have := hWLI.fintype_card_le_finrank
  simpa using this

/-- **Tasaki Theorem 11.7 (degeneracy).**  Under the connectivity condition
(Definition 11.6) and `t ≥ 0`, the one-hole `Ĥ_eff` ground eigenspace (in the
Tasaki-coefficient representation) has dimension exactly `N + 1 = 2 S_max + 1`:
the ferromagnetic multiplet and nothing more.  Combines the Perron–Frobenius
upper bound (`≤ N+1`) with the spin-multiplet lower bound (`≥ N+1`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.2.2, Theorem 11.7. -/
theorem nagaoka_theorem_11_7_degeneracy (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0)
    (hpos : ∀ i j, 0 ≤ t i j) (hconn : nagaokaConnectivity N t) :
    finrank ℂ (End.eigenspace (Matrix.toLin'
      (tasakiEffMatrix N (fun i j => (t i j : ℂ)) 0))
      (((hermitianMinEigenvalue (tasakiEffMatrixUp_isHermitian N
        (fun i j => (t i j : ℂ)) 0 (tasakiEffMatrix_hJ_of_real htsym)
        (by simp))) : ℝ) : ℂ)) = N + 1 := by
  have hmateq : tasakiEffMatrix N (fun i j => (t i j : ℂ)) 0
      = (tasakiEffReMatrix N t).map (algebraMap ℝ ℂ) :=
    tasakiEffMatrix_eq_map_tasakiEffReMatrix N t 0 htdiag
  have hE_eq : hermitianMinEigenvalue (isHermitian_map_ofReal_of_isSymm
        (tasakiEffReMatrix_isSymm N t htsym htdiag))
      = hermitianMinEigenvalue (tasakiEffMatrixUp_isHermitian N
        (fun i j => (t i j : ℂ)) 0 (tasakiEffMatrix_hJ_of_real htsym) (by simp)) := by
    have h1 : hermitianMinEigenvalue (isHermitian_map_ofReal_of_isSymm
          (tasakiEffReMatrix_isSymm N t htsym htdiag))
        = hermitianMinEigenvalue (tasakiEffMatrix_isHermitian N (fun i j => (t i j : ℂ)) 0
          (tasakiEffMatrix_hJ_of_real htsym) (by simp)) := by
      rw [← rayleighInfMatrix_eq_hermitianMinEigenvalue,
        ← rayleighInfMatrix_eq_hermitianMinEigenvalue, hmateq]
    rw [h1]
    exact (hermitianMinEigenvalue_tasakiEffMatrixUp_eq N t 0 htsym htdiag hpos).symm
  refine le_antisymm ?_ ?_
  · rw [hmateq, ← hE_eq]
    exact tasakiEffMatrix_ground_finrank_le_N_add_one N t htsym htdiag hpos hconn
  · exact tasakiEffMatrix_ground_finrank_ge N t htsym htdiag

end LatticeSystem.Fermion
