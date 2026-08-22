import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsivePerturbationSetup

/-!
# Superexchange reduced-inverse layer for Theorem 10.4 (Tasaki §10.2.2, PR-6)

Sixth installment of the Theorem 10.4 discharge arc (issue #5320); first of the three-PR
superexchange-identity sub-arc (PR-6 to PR-8). PR-5 built the perturbation family
`Ĥ(λ)|_K = Ĥ₀|_K + λ V̂|_K` on the half-filled fixed-`Ŝ³` sector `K` and its first-order vanishing
`P̂₀ V̂|_K P̂₀ = 0`; this file supplies the two remaining pieces of Tasaki's `λ → 0` deformation
(§10.2.2, p. 353) that are needed *before* the superexchange operator identity itself can be
computed (PR-7/PR-8):

* **`V̂` preserves the half-filled sector** (`liebPerturbationV_preserves_liebHalfFillingPred`):
  every hopping term of `V̂` moves one electron of a fixed spin between two sites, so the total
  electron number and the total spin-up number are both unchanged. This is the entrywise
  sector-preservation hypothesis that
  `LatticeSystem.Fermion.configSectorCompress_mul_of_preserves`
  (`HubbardImpossibilityLowUVariationalCore.lean`) needs to identify the compressed product
  `V̂|_K · V̂|_K` with the compression `(V̂ · V̂)|_K` of the whole-Fock-space product — the step
  PR-8 uses to reduce its target identity to a Fock-space computation.
* **The compressed reduced inverse of `Ĥ₀|_K`** (`liebPerturbationH0InvCompressed`,
  `liebPerturbationH0Compressed_isReducedInverse`): the compression of PR-5's explicit
  whole-Fock-space reduced inverse `Ĥ₀Inv`, discharging PR-5 debt item (a).
* **The crux: intermediate states have weight exactly `1`**
  (`liebPerturbationV_intermediate_weight_eq_one`): Tasaki's "the site `x` is doubly occupied in
  `ĉ†_{x,σ}ĉ_{y,σ}|Φ⟩`" (eq. (10.1.7), p. 344), read at this arc's `U = 1` normalisation as
  "the intermediate interaction weight is exactly `1`" rather than merely `1/U`. A later
  restoration of a general on-site coupling `U` must not silently reuse this statement verbatim.
* **`Ĥ₀⁻¹|_K` acts as the identity on `V̂|_K · P̂₀`**
  (`liebPerturbationH0InvCompressed_mul_V_mul_kernelProjection`) and, consequently, the **PR-6
  capstone** (`secondOrderEffectiveHamiltonian_liebPerturbation_eq`): the second-order effective
  Hamiltonian collapses to `−(P̂₀ · V̂|_K · V̂|_K · P̂₀)`, the object PR-8 computes explicitly as
  the superexchange sum.

Two cheap debt items of PR-5 are cleared alongside this layer, since both are needed by the
Lemma 10.1 application (PR-11 to PR-13) and neither depends on the superexchange identity itself:

* `configSector_liebHalfFillingPred_nonempty` — PR-5 debt (c), an instance hypothesis of
  `tasaki_lemma_10_1_degenerate_perturbation`.
* `homotopyHamiltonian_one_compressed_eq_perturbedHamiltonian` — PR-5 debt (b), the compressed
  bridge to `LatticeSystem.Math.perturbedHamiltonian`. This bridge is pure linearity of
  `configSectorCompress` and does **not** presuppose the sector preservation of `V̂` proved above;
  only its later *interpretation* at assembly does.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.1 (Lemma 10.1, eq. (10.1.20)) and §10.2.2 (eq. (10.1.7), p. 344; p. 353).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math
open scoped ComplexOrder

variable {N : ℕ}

/-! ## A nonzero entry of `V̂` is a single hop -/

/-- **A nonzero matrix element of `V̂` is a single hop.** If the entry `V̂ c' c` does not vanish,
then it is carried by some spin species `σ` and some ordered pair of sites `(i, j)` with
nonvanishing endpoint hopping: the spin orbital `(j, σ)` is occupied in `c`, the orbital `(i, σ)`
is empty once that electron is removed, and `c'` is the hopped configuration. Both the sector
preservation of `V̂` and the intermediate-weight crux read off their conclusion from this single
hopped configuration, so neither needs the Jordan–Wigner signs. -/
private theorem exists_hop_of_liebPerturbationV_apply_ne_zero {N : ℕ} {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {c c' : Fin (2 * N + 2) → Fin 2}
    (h : liebPerturbationV N A T c' c ≠ 0) :
    ∃ (σ : Fin 2) (i j : Fin (N + 1)), liebEndpointHopping A T 1 i j ≠ 0 ∧
      c (spinfulIndex N j σ) = 1 ∧
      (Function.update c (spinfulIndex N j σ) 0) (spinfulIndex N i σ) = 0 ∧
      c' = Function.update (Function.update c (spinfulIndex N j σ) 0) (spinfulIndex N i σ) 1 := by
  by_contra hnex
  push Not at hnex
  apply h
  rw [liebPerturbationV, hubbardKinetic]
  simp only [Matrix.sum_apply]
  refine Finset.sum_eq_zero fun σ _ => Finset.sum_eq_zero fun i _ =>
    Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  by_cases hcoef : liebEndpointHopping A T 1 i j = 0
  · rw [hcoef, Complex.ofReal_zero, zero_mul]
  · refine mul_eq_zero_of_right _ ?_
    rw [← mulVec_basisVec_apply (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ)) c' c,
      fermionMultiCreation_mul_Annihilation_mulVec_basisVec]
    by_cases hcond : c (spinfulIndex N j σ) = 1 ∧
        (Function.update c (spinfulIndex N j σ) 0) (spinfulIndex N i σ) = 0
    · rw [if_pos hcond, Pi.smul_apply, smul_eq_mul, basisVec_apply,
        if_neg (hnex σ i j hcoef hcond.1 hcond.2), mul_zero]
    · rw [if_neg hcond, Pi.zero_apply]

/-- **A hop preserves an occupation count.** Moving the electron of an occupied orbital `q` to an
empty orbital `p` leaves the total occupation `∑ k, (f k).val` unchanged. -/
private theorem sum_val_update_hop {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Fin 2)
    {p q : ι} (hpq : p ≠ q) (hq : f q = 1) (hp : f p = 0) :
    ∑ k, ((Function.update (Function.update f q 0) p 1) k).val = ∑ k, (f k).val := by
  classical
  have hcomm : ∀ k, ((Function.update (Function.update f q 0) p 1) k).val
      = Function.update (Function.update (fun y => (f y).val) q 0) p 1 k := by
    intro k
    by_cases hkp : k = p
    · subst hkp
      simp
    · by_cases hkq : k = q
      · subst hkq
        rw [Function.update_of_ne hkp, Function.update_of_ne hkp, Function.update_self,
          Function.update_self]
        rfl
      · rw [Function.update_of_ne hkp, Function.update_of_ne hkp, Function.update_of_ne hkq,
          Function.update_of_ne hkq]
  have hqmem : q ∈ (Finset.univ : Finset ι).erase p :=
    Finset.mem_erase.mpr ⟨Ne.symm hpq, Finset.mem_univ q⟩
  rw [Finset.sum_congr rfl (fun k _ => hcomm k),
    Finset.sum_update_of_mem (Finset.mem_univ p),
    Finset.sdiff_singleton_eq_erase, Finset.sum_update_of_mem hqmem,
    Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase Finset.univ (fun y => (f y).val) (Finset.mem_univ p),
    ← Finset.add_sum_erase ((Finset.univ : Finset ι).erase p) (fun y => (f y).val) hqmem, hq, hp]
  simp

/-! ## `V̂` preserves the half-filled fixed-`Ŝ³` sector -/

/-- **`V̂` preserves the half-filled fixed-`Ŝ³` sector**: every hopping term of `V̂` moves a single
electron of one spin between two sites, leaving both the total electron number and the total
spin-up number unchanged. Hence `V̂ c' c = 0` whenever `c` lies in the sector and `c'` does not —
the entrywise sector-preservation hypothesis needed by `configSectorCompress_mul_of_preserves`
(`HubbardImpossibilityLowUVariationalCore.lean`) to identify `V̂|_K · V̂|_K` with the compression of
the whole-Fock-space product `V̂ · V̂`. -/
theorem liebPerturbationV_preserves_liebHalfFillingPred (N nUp : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) {c c' : Fin (2 * N + 2) → Fin 2}
    (hc : liebHalfFillingPred N nUp c) (hc' : ¬ liebHalfFillingPred N nUp c') :
    liebPerturbationV N A T c' c = 0 := by
  by_contra hne
  obtain ⟨σ, i, j, _, hq, hp, rfl⟩ := exists_hop_of_liebPerturbationV_apply_ne_zero hne
  apply hc'
  by_cases hij : i = j
  · subst hij
    rwa [Function.update_idem, Function.update_eq_self_iff.mpr hq.symm]
  · have hpq : spinfulIndex N i σ ≠ spinfulIndex N j σ :=
      fun hh => hij ((spinfulIndex_eq_iff N i j σ σ).mp hh).1
    have hci : c (spinfulIndex N i σ) = 0 := by rwa [Function.update_of_ne hpq] at hp
    refine ⟨?_, ?_⟩
    · rw [sum_val_update_hop c hpq hq hci]
      exact hc.1
    · rcases (show σ = 0 ∨ σ = 1 by omega) with rfl | rfl
      · have hup : ∀ x : Fin (N + 1),
            (Function.update (Function.update c (spinfulIndex N j 0) 0)
                (spinfulIndex N i 0) 1) (spinfulIndex N x 0)
              = Function.update (Function.update (fun y : Fin (N + 1) => c (spinfulIndex N y 0))
                  j 0) i 1 x := by
          intro x
          by_cases hxi : x = i
          · subst hxi
            simp
          · have hne1 : spinfulIndex N x 0 ≠ spinfulIndex N i 0 :=
              fun hh => hxi ((spinfulIndex_eq_iff N x i 0 0).mp hh).1
            by_cases hxj : x = j
            · subst hxj
              rw [Function.update_of_ne hne1, Function.update_self, Function.update_of_ne hxi,
                Function.update_self]
            · have hne2 : spinfulIndex N x 0 ≠ spinfulIndex N j 0 :=
                fun hh => hxj ((spinfulIndex_eq_iff N x j 0 0).mp hh).1
              rw [Function.update_of_ne hne1, Function.update_of_ne hne2,
                Function.update_of_ne hxi, Function.update_of_ne hxj]
        rw [Finset.sum_congr rfl (fun x _ => congrArg Fin.val (hup x)),
          sum_val_update_hop (fun y : Fin (N + 1) => c (spinfulIndex N y 0)) hij hq hci]
        exact hc.2
      · have hup : ∀ x : Fin (N + 1),
            (Function.update (Function.update c (spinfulIndex N j 1) 0)
                (spinfulIndex N i 1) 1) (spinfulIndex N x 0) = c (spinfulIndex N x 0) := by
          intro x
          have hne1 : spinfulIndex N x 0 ≠ spinfulIndex N i 1 :=
            fun hh => absurd ((spinfulIndex_eq_iff N x i 0 1).mp hh).2 (by decide)
          have hne2 : spinfulIndex N x 0 ≠ spinfulIndex N j 1 :=
            fun hh => absurd ((spinfulIndex_eq_iff N x j 0 1).mp hh).2 (by decide)
          rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
        rw [Finset.sum_congr rfl (fun x _ => congrArg Fin.val (hup x))]
        exact hc.2

/-! ## The compressed reduced inverse of `Ĥ₀|_K` -/

/-- **The compressed reduced inverse of `Ĥ₀|_K`**: the compression of the whole-Fock-space
explicit reduced inverse `Ĥ₀Inv` (`liebPerturbationH0Inv`, PR-5) to the half-filled fixed-`Ŝ³`
sector. -/
noncomputable def liebPerturbationH0InvCompressed (N nUp : ℕ) :
    Matrix (configSector N (liebHalfFillingPred N nUp))
      (configSector N (liebHalfFillingPred N nUp)) ℂ :=
  configSectorCompress N (liebHalfFillingPred N nUp) (liebPerturbationH0Inv N)

/-- The compressed reduced inverse stays diagonal, with the reciprocal interaction weight of the
sector configuration as its eigenvalue (mirroring `liebPerturbationH0Compressed_eq_diagonal`). -/
theorem liebPerturbationH0InvCompressed_eq_diagonal (N nUp : ℕ) :
    liebPerturbationH0InvCompressed N nUp
      = Matrix.diagonal (fun s : configSector N (liebHalfFillingPred N nUp) =>
          if hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) s.val = 0 then 0
          else (hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) s.val)⁻¹) := by
  have hInv : liebPerturbationH0Inv N
      = Matrix.diagonal (fun c : Fin (2 * N + 2) → Fin 2 =>
          if hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0 then 0
          else (hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c)⁻¹) := rfl
  ext s s'
  rw [liebPerturbationH0InvCompressed, configSectorCompress_apply, hInv, Matrix.diagonal_apply,
    Matrix.diagonal_apply]
  by_cases h : s = s'
  · rw [if_pos h, if_pos (congrArg Subtype.val h)]
  · rw [if_neg h, if_neg (fun hv => h (Subtype.ext hv))]

/-- **`Ĥ₀InvCompressed` is the reduced inverse of `Ĥ₀|_K`** — closes PR-5 debt item (a): the
compressed `IsReducedInverse` contract, mirroring the whole-Fock-space
`liebPerturbationH0_isReducedInverse`. -/
theorem liebPerturbationH0Compressed_isReducedInverse (N nUp : ℕ) :
    LatticeSystem.Math.IsReducedInverse (liebPerturbationH0Compressed N nUp)
      (liebPerturbationH0InvCompressed N nUp) := by
  rw [liebPerturbationH0Compressed_eq_diagonal, liebPerturbationH0InvCompressed_eq_diagonal]
  exact LatticeSystem.Math.isReducedInverse_diagonal
    (fun s => hubbardConfigInteractionWeight_one_star N s.val)

/-! ## The crux: intermediate states have weight exactly `1` -/

/-- **Crux of PR-6: the intermediate weight is exactly `1`.** For `c` a configuration carrying one
electron per site — which is what half filling plus the hard-core condition force
(`liebHalfFilling_site_occupation`) — every `d` reached by a nonzero matrix element of `V̂` has
interaction weight exactly `1`: a nonzero hop entry has source `y` occupied and target `x` empty in
the hopped spin, and `d` is `c` with `x` now doubly occupied and `y` now empty — Tasaki's "the site
`x` is doubly occupied in `ĉ†_{x,σ}ĉ_{y,σ}|Φ⟩`" (eq. (10.1.7), p. 344), at this arc's `U = 1`
normalisation read as "exactly `1`" rather than merely "exactly `U`"; a later restoration of a
general on-site coupling must not reuse this statement verbatim.

The one-electron-per-site hypothesis is essential, not cosmetic: a hard-core configuration with an
empty site can absorb the hopping electron and stay hard-core, of interaction weight `0`. -/
theorem liebPerturbationV_intermediate_weight_eq_one {N : ℕ} {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hbip : HoppingRespectsBipartition A T)
    {c d : Fin (2 * N + 2) → Fin 2}
    (hc : ∀ x : Fin (N + 1), (c (spinfulIndex N x 0)).val + (c (spinfulIndex N x 1)).val = 1)
    (hd : liebPerturbationV N A T d c ≠ 0) :
    hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) d = 1 := by
  obtain ⟨σ, i, j, hcoef, hq, hp, rfl⟩ := exists_hop_of_liebPerturbationV_apply_ne_zero hd
  have hij : i ≠ j := by
    rintro rfl
    exact hcoef (liebEndpointHopping_diag_eq_zero hbip i)
  have hpq : spinfulIndex N i σ ≠ spinfulIndex N j σ :=
    fun hh => hij ((spinfulIndex_eq_iff N i j σ σ).mp hh).1
  have hci : (c (spinfulIndex N i σ)).val = 0 := by
    rw [Function.update_of_ne hpq] at hp
    rw [hp]
    rfl
  have hdi : ∀ r : Fin 2, ((Function.update (Function.update c (spinfulIndex N j σ) 0)
      (spinfulIndex N i σ) 1) (spinfulIndex N i r)).val = 1 := by
    intro r
    by_cases hr : r = σ
    · subst hr
      rw [Function.update_self]
      rfl
    · have hne1 : spinfulIndex N i r ≠ spinfulIndex N i σ :=
        fun hh => hr ((spinfulIndex_eq_iff N i i r σ).mp hh).2
      have hne2 : spinfulIndex N i r ≠ spinfulIndex N j σ :=
        fun hh => hij ((spinfulIndex_eq_iff N i j r σ).mp hh).1
      rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
      have hocc := hc i
      rcases (show (σ = 0 ∧ r = 1) ∨ (σ = 1 ∧ r = 0) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        omega
  have hdj : ((Function.update (Function.update c (spinfulIndex N j σ) 0)
      (spinfulIndex N i σ) 1) (spinfulIndex N j σ)).val = 0 := by
    rw [Function.update_of_ne hpq.symm, Function.update_self]
    rfl
  have hdother : ∀ (x : Fin (N + 1)), x ≠ i → x ≠ j → ∀ r : Fin 2,
      (Function.update (Function.update c (spinfulIndex N j σ) 0)
        (spinfulIndex N i σ) 1) (spinfulIndex N x r) = c (spinfulIndex N x r) := by
    intro x hxi hxj r
    have hne1 : spinfulIndex N x r ≠ spinfulIndex N i σ :=
      fun hh => hxi ((spinfulIndex_eq_iff N x i r σ).mp hh).1
    have hne2 : spinfulIndex N x r ≠ spinfulIndex N j σ :=
      fun hh => hxj ((spinfulIndex_eq_iff N x j r σ).mp hh).1
    rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
  rw [hubbardConfigInteractionWeight, Finset.sum_eq_single i]
  · rw [hdi 0, hdi 1]
    norm_num
  · intro x _ hxi
    by_cases hxj : x = j
    · subst hxj
      rcases (show σ = 0 ∨ σ = 1 by omega) with rfl | rfl
      · rw [hdj, Nat.cast_zero, mul_zero, zero_mul]
      · rw [hdj, Nat.cast_zero, mul_zero]
    · rw [hdother x hxi hxj 0, hdother x hxi hxj 1]
      have hocc := hc x
      rcases (show (c (spinfulIndex N x 0)).val = 0 ∨ (c (spinfulIndex N x 1)).val = 0 by omega)
        with h0 | h0
      · rw [h0, Nat.cast_zero, mul_zero, zero_mul]
      · rw [h0, Nat.cast_zero, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ i) hmem

/-! ## `Ĥ₀⁻¹|_K` on the range of `V̂|_K · P̂₀`, and the PR-6 capstone -/

/-- **`Ĥ₀⁻¹|_K` acts as the identity on `V̂|_K · P̂₀`**: on a weight-`1` column the reciprocal
interaction weight of `Ĥ₀⁻¹|_K` is exactly `1` (Crux,
`liebPerturbationV_intermediate_weight_eq_one`), so it fixes every column reached from a hard-core
configuration by `V̂|_K`. -/
theorem liebPerturbationH0InvCompressed_mul_V_mul_kernelProjection (N nUp : ℕ)
    {A : Finset (Fin (N + 1))} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hbip : HoppingRespectsBipartition A T) :
    liebPerturbationH0InvCompressed N nUp
        * liebPerturbationVCompressed N nUp A T
        * LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)
      = liebPerturbationVCompressed N nUp A T
        * LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp) := by
  rw [liebPerturbationH0InvCompressed_eq_diagonal,
    kernelProjectionMatrix_liebPerturbationH0Compressed_eq_diagonal]
  ext s s'
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hs' : hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) s'.val = 0
  · rw [if_pos hs', mul_one, mul_one]
    by_cases hV : liebPerturbationVCompressed N nUp A T s s' = 0
    · rw [hV, mul_zero]
    · have hw : hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) s.val = 1 := by
        refine liebPerturbationV_intermediate_weight_eq_one hbip
          (liebHalfFilling_site_occupation N nUp s'.property hs') ?_
        rwa [liebPerturbationVCompressed, configSectorCompress_apply] at hV
      rw [hw, if_neg one_ne_zero, inv_one, one_mul]
  · rw [if_neg hs', mul_zero, mul_zero]

/-- **PR-6 capstone**: the second-order effective Hamiltonian for the compressed perturbation
family collapses to `−(P̂₀ · V̂|_K · V̂|_K · P̂₀)`, since `Ĥ₀⁻¹|_K` acts as the identity on the
range of `V̂|_K · P̂₀` (`liebPerturbationH0InvCompressed_mul_V_mul_kernelProjection`). This is the
object PR-8 computes explicitly as the superexchange sum. -/
theorem secondOrderEffectiveHamiltonian_liebPerturbation_eq (N nUp : ℕ)
    {A : Finset (Fin (N + 1))} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hbip : HoppingRespectsBipartition A T) :
    LatticeSystem.Math.secondOrderEffectiveHamiltonian (liebPerturbationH0Compressed N nUp)
        (liebPerturbationVCompressed N nUp A T) (liebPerturbationH0InvCompressed N nUp)
      = -(LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)
          * liebPerturbationVCompressed N nUp A T * liebPerturbationVCompressed N nUp A T
          * LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)) := by
  have hid := liebPerturbationH0InvCompressed_mul_V_mul_kernelProjection N nUp hbip
  have hinner : LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)
        * liebPerturbationVCompressed N nUp A T * liebPerturbationH0InvCompressed N nUp
        * liebPerturbationVCompressed N nUp A T
        * LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)
      = LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)
        * liebPerturbationVCompressed N nUp A T * liebPerturbationVCompressed N nUp A T
        * LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp) := by
    simp only [Matrix.mul_assoc] at hid ⊢
    rw [hid]
  rw [LatticeSystem.Math.secondOrderEffectiveHamiltonian, hinner]

/-! ## Cheap debt clearance (PR-5 items (b) and (c)) -/

/-- **PR-5 debt (c) discharged**: the half-filled fixed-`Ŝ³` sector is nonempty whenever
`nUp ≤ N + 1` — an instance hypothesis of `tasaki_lemma_10_1_degenerate_perturbation`
(`Math/MatrixAnalysis/DegeneratePerturbationConvergence.lean`). The witness puts a spin-up
electron on the first `nUp` sites and a spin-down electron on the remaining ones. -/
theorem configSector_liebHalfFillingPred_nonempty (N nUp : ℕ) (hnUp : nUp ≤ N + 1) :
    Nonempty (configSector N (liebHalfFillingPred N nUp)) := by
  classical
  obtain ⟨c, hc0, hc1⟩ : ∃ c : Fin (2 * N + 2) → Fin 2,
      (∀ x : Fin (N + 1), c (spinfulIndex N x 0) = if x.val < nUp then 1 else 0) ∧
      (∀ x : Fin (N + 1), c (spinfulIndex N x 1) = if x.val < nUp then 0 else 1) := by
    refine ⟨fun k => if k.val % 2 = 0 then (if k.val / 2 < nUp then 1 else 0)
      else (if k.val / 2 < nUp then 0 else 1), fun x => ?_, fun x => ?_⟩
    · have hv : (spinfulIndex N x 0).val = 2 * x.val := by simp [spinfulIndex]
      simp only [show (spinfulIndex N x 0).val % 2 = 0 by omega,
        show (spinfulIndex N x 0).val / 2 = x.val by omega, if_pos]
    · have hv : (spinfulIndex N x 1).val = 2 * x.val + 1 := by simp [spinfulIndex]
      simp only [show (spinfulIndex N x 1).val % 2 = 1 by omega,
        show (spinfulIndex N x 1).val / 2 = x.val by omega]
      norm_num
  have hsite : ∀ x : Fin (N + 1),
      (c (spinfulIndex N x 0)).val + (c (spinfulIndex N x 1)).val = 1 := by
    intro x
    rw [hc0 x, hc1 x]
    by_cases hx : x.val < nUp <;> simp [hx]
  have hupval : ∀ x : Fin (N + 1),
      (c (spinfulIndex N x 0)).val = if x.val < nUp then 1 else 0 := by
    intro x
    rw [hc0 x]
    by_cases hx : x.val < nUp <;> simp [hx]
  refine ⟨⟨c, ?_, ?_⟩⟩
  · rw [sum_spinful_split N (fun j => (c j).val),
      Finset.sum_congr rfl (fun x _ => hsite x), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
  · rw [Finset.sum_congr rfl (fun x _ => hupval x),
      Fin.sum_univ_eq_sum_range (fun i => if i < nUp then 1 else 0) (N + 1),
      ← Finset.sum_subset (show Finset.range nUp ⊆ Finset.range (N + 1) from
          Finset.range_subset_range.mpr hnUp)
        (fun x _ hxm => if_neg (fun hlt => hxm (Finset.mem_range.mpr hlt))),
      Finset.sum_congr rfl (fun x hx => if_pos (Finset.mem_range.mp hx)), Finset.sum_const,
      Finset.card_range, smul_eq_mul, mul_one]

/-- **PR-5 debt (b) discharged**: the compressed `s = 1` homotopy endpoint is the compressed
perturbed Hamiltonian `Ĥ₀|_K + λ V̂|_K` — pure linearity of `configSectorCompress` applied to
`homotopyHamiltonian_one_eq_perturbedHamiltonian` (PR-5). This bridge does **not** presuppose the
sector preservation of `V̂` (`liebPerturbationV_preserves_liebHalfFillingPred`); only its later
*interpretation* at assembly (PR-11 to PR-13) does. -/
theorem homotopyHamiltonian_one_compressed_eq_perturbedHamiltonian (N nUp : ℕ)
    (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U lam : ℝ) :
    configSectorCompress N (liebHalfFillingPred N nUp) (homotopyHamiltonian N A T U lam 1)
      = LatticeSystem.Math.perturbedHamiltonian (liebPerturbationH0Compressed N nUp)
          (liebPerturbationVCompressed N nUp A T) lam := by
  rw [homotopyHamiltonian_one_eq_perturbedHamiltonian]
  unfold LatticeSystem.Math.perturbedHamiltonian
  rw [configSectorCompress_add, configSectorCompress_smul]
  rfl

end LatticeSystem.Fermion
