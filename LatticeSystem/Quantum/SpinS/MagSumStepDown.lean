import LatticeSystem.Quantum.SpinS.ParityReachWitness
import LatticeSystem.Quantum.SpinS.Magnetization

/-!
# `magSumS` arithmetic under `configUpdateOne` / `configUpdateTwo` and single-step magSum reductions

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

For the cross-sector bridging step of (d.3) full reachability totality, we need to compute the
exact change in `magSumS` under the single-site / two-site update operations and exhibit
single-step parity moves that decrease `magSumS` by exactly `2`.

This file packages:
* `magSumS_configUpdateOne_eq` — exact arithmetic for the one-site update.
* `magSumS_configUpdateTwo_eq` — exact arithmetic for the two-site update at distinct sites.
* `singleIonStepS_lower_magSumS_decrease` — a single-ion lower step at a site with `(σ x).val ≥ 2`
  decreases `magSumS` by exactly `2`.
* `parityBondStepS_pair_lower_magSumS_decrease` — analogously for the bond-parity lower step on
  an adjacent pair both at `≥ 1`.

These are the building blocks for the cross-sector step-down lemma needed by full (d.3)
reachability totality.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}


/-- **`magSumS` arithmetic for the single-site update**: `configUpdateOne σ x vx`'s sum equals
the original `magSumS σ` adjusted by the difference at site `x` (in addition form to avoid `ℕ`
subtraction). -/
theorem magSumS_configUpdateOne_eq
    (σ : V → Fin (N + 1)) (x : V) (vx : Fin (N + 1)) :
    magSumS (configUpdateOne σ x vx) + (σ x).val = magSumS σ + vx.val := by
  unfold magSumS configUpdateOne
  have hx : x ∈ (Finset.univ : Finset V) := Finset.mem_univ x
  rw [← Finset.add_sum_erase _ (fun k => ((if k = x then vx else σ k) : Fin (N + 1)).val) hx,
      ← Finset.add_sum_erase _ (fun k => (σ k).val) hx]
  have hsum :
      ∑ k ∈ Finset.univ.erase x, ((if k = x then vx else σ k) : Fin (N + 1)).val =
      ∑ k ∈ Finset.univ.erase x, (σ k).val := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [if_neg (Finset.mem_erase.mp hk).1]
  rw [hsum, if_pos rfl]
  ring


/-- **`magSumS` arithmetic for the two-site update at distinct sites**. -/
theorem magSumS_configUpdateTwo_eq
    (σ : V → Fin (N + 1)) {x y : V} (hxy : x ≠ y) (vx vy : Fin (N + 1)) :
    magSumS (configUpdateTwo σ x y vx vy) + ((σ x).val + (σ y).val) =
      magSumS σ + (vx.val + vy.val) := by
  unfold magSumS configUpdateTwo
  have hx : x ∈ (Finset.univ : Finset V) := Finset.mem_univ x
  have hy : y ∈ (Finset.univ.erase x : Finset V) :=
    Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ y⟩
  rw [← Finset.add_sum_erase _
        (fun k => ((if k = x then vx else if k = y then vy else σ k) : Fin (N + 1)).val) hx,
      ← Finset.add_sum_erase _ (fun k => (σ k).val) hx,
      ← Finset.add_sum_erase _
        (fun k => ((if k = x then vx else if k = y then vy else σ k) : Fin (N + 1)).val) hy,
      ← Finset.add_sum_erase _ (fun k => (σ k).val) hy]
  have hsum :
      ∑ k ∈ (Finset.univ.erase x).erase y,
        ((if k = x then vx else if k = y then vy else σ k) : Fin (N + 1)).val =
      ∑ k ∈ (Finset.univ.erase x).erase y, (σ k).val := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hky : k ≠ y := (Finset.mem_erase.mp hk).1
    have hkx : k ≠ x := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hk)).1
    rw [if_neg hkx, if_neg hky]
  rw [hsum, if_pos rfl]
  -- Reduce the second `if`: the LHS site at y has `k = y`, so the if-else gives `vy`.
  have hyx : y ≠ x := hxy.symm
  simp [hyx]
  ring


/-- **Single-ion lower step decreases `magSumS` by 2**: the target `configUpdateOne σ x ⟨σ x − 2⟩`
has `magSumS = magSumS σ − 2`. -/
theorem singleIonStepS_lower_magSumS_decrease
    {σ : V → Fin (N + 1)} (x : V) (hkx : 2 ≤ (σ x).val) :
    magSumS (configUpdateOne σ x ⟨(σ x).val - 2, by have := (σ x).isLt; omega⟩) + 2 =
      magSumS σ := by
  have h := magSumS_configUpdateOne_eq σ x ⟨(σ x).val - 2, by have := (σ x).isLt; omega⟩
  simp at h
  omega


/-- **Bond-parity lower step decreases `magSumS` by 2**: the target
`configUpdateTwo σ x y ⟨σ x − 1⟩ ⟨σ y − 1⟩` has `magSumS = magSumS σ − 2`. -/
theorem parityBondStepS_pair_lower_magSumS_decrease
    {σ : V → Fin (N + 1)} {x y : V} (hxy : x ≠ y)
    (hkx : 1 ≤ (σ x).val) (hky : 1 ≤ (σ y).val) :
    magSumS (configUpdateTwo σ x y
      ⟨(σ x).val - 1, by have := (σ x).isLt; omega⟩
      ⟨(σ y).val - 1, by have := (σ y).isLt; omega⟩) + 2 = magSumS σ := by
  have h := magSumS_configUpdateTwo_eq σ hxy
    ⟨(σ x).val - 1, by have := (σ x).isLt; omega⟩
    ⟨(σ y).val - 1, by have := (σ y).isLt; omega⟩
  simp at h
  omega

end LatticeSystem.Quantum
