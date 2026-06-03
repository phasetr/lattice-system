import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaMagnetizationSector
import LatticeSystem.Math.HermitianMinEqOfShiftPF
import LatticeSystem.Quantum.SpinS.RealComplexEigenspaceBridge
import LatticeSystem.Quantum.SpinS.HermitianMinLeOfEigenvector

/-!
# Per-sector Perron–Frobenius and the `≤ N+1` upper bound (Tasaki §11.2.2)

Spectral identification feeding the upper-bound half of **Tasaki Theorem 11.7**:
the sector minimum eigenvalue equals `−μ` (Collatz–Wielandt), the global minimum
is `≤` every sector minimum (principal-submatrix inequality), each sector
contributes at most one ground state at the global minimum, and the full
coefficient-space ground eigenspace therefore has `finrank ≤ N+1`.

* [`hermitianMinEigenvalue_sector_eq_neg_pf`] — sector min `= −μ`.
* [`hermitianMinEigenvalue_tasakiEffMatrix_le_sector`] — `min M ≤ min M_m`.
* [`sector_map_eigenspace_finrank_le_one_at`] — per-sector `≤ 1` at the min.
* [`tasakiEffMatrix_ground_finrank_le_N_add_one`] — the `≤ N+1` bound.

Split from `NagaokaConnectivity.lean` (refactor, 2026-06-04).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.2.2, Theorem 11.7.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math.PerronFrobenius
  LatticeSystem.Math.CollatzWielandt Module

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

end LatticeSystem.Fermion
