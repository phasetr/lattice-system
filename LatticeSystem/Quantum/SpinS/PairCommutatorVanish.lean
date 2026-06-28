/-
Off-pair vanishing of the two-site double commutator `[Ŝ_x^{(3)}, [Ĥ, Ŝ_z^{(3)}]]`
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

Because `[Ĥ, Ŝ_z^{(3)}]` is supported on the two bonds incident to `z` (sites `z−1, z, z+1`), it
commutes with `Ŝ_x^{(3)}` when `x` lies off those three sites, so the two-site double commutator
vanishes: `[Ŝ_x^{(3)}, [Ĥ, Ŝ_z^{(3)}]] = 0` for `x ∉ {z−1, z, z+1}`.  Hence the oscillator strength
double sum has only `O(L)` nonzero terms (three per `z`).
-/
import LatticeSystem.Quantum.SpinS.RingHamiltonianCommutatorClosed

namespace LatticeSystem.Quantum

open Matrix

/-- A two-site dot product commutes with a single-site operator off both endpoints (re-proved
locally to keep this §4.1 module independent of the later Anderson-tower layer). -/
private theorem spinSDot_commute_onSiteS_off {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    (x y z : Λ) (hzx : z ≠ x) (hzy : z ≠ y) (B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    Commute (spinSDot x y N) (onSiteS z B) := by
  rw [spinSDot_def]
  have cx : ∀ A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ,
      Commute (onSiteS x A : ManyBodyOpS Λ N) (onSiteS z B) :=
    fun A => onSiteS_commute_of_ne (Ne.symm hzx) A B
  have cy : ∀ A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ,
      Commute (onSiteS y A : ManyBodyOpS Λ N) (onSiteS z B) :=
    fun A => onSiteS_commute_of_ne (Ne.symm hzy) A B
  exact (((cx _).mul_left (cy _)).add_left ((cx _).mul_left (cy _))).add_left
    ((cx _).mul_left (cy _))

/-- **Off-pair vanishing**: `[Ŝ_x^{(3)}, [Ĥ, Ŝ_z^{(3)}]] = 0` when `x` is off `z`'s two incident
bonds (`x ≠ z`, `x ≠ z+1`, `x ≠ z−1`). -/
theorem pair_double_commutator_eq_zero_of_ne (L N : ℕ) (hL : 2 ≤ L) (z x : Fin L)
    (hxz : x ≠ z) (hxf : x ≠ finRotate L z) (hxp : x ≠ (finRotate L).symm z) :
    haveI : NeZero L := ⟨by omega⟩
    onSiteS x (spinSOp3 N)
          * (heisenbergHamiltonianS (ringCoupling L) N * onSiteS z (spinSOp3 N)
            - onSiteS z (spinSOp3 N) * heisenbergHamiltonianS (ringCoupling L) N)
        - (heisenbergHamiltonianS (ringCoupling L) N * onSiteS z (spinSOp3 N)
            - onSiteS z (spinSOp3 N) * heisenbergHamiltonianS (ringCoupling L) N)
          * onSiteS x (spinSOp3 N) = 0 := by
  haveI : NeZero L := ⟨by omega⟩
  rw [heisenbergHamiltonianS_ringCoupling_commutator_onSiteS_spinSOp3_closed L N hL z]
  have he : Commute (onSiteS x (spinSOp3 N) : ManyBodyOpS (Fin L) N) (onSiteS z (spinSOp3 N)) :=
    onSiteS_commute_of_ne hxz _ _
  have hd1 : Commute (onSiteS x (spinSOp3 N) : ManyBodyOpS (Fin L) N)
      (spinSDot z (finRotate L z) N) :=
    (spinSDot_commute_onSiteS_off z (finRotate L z) x hxz hxf (spinSOp3 N)).symm
  have hd2 : Commute (onSiteS x (spinSOp3 N) : ManyBodyOpS (Fin L) N)
      (spinSDot ((finRotate L).symm z) z N) :=
    (spinSDot_commute_onSiteS_off ((finRotate L).symm z) z x hxp hxz (spinSOp3 N)).symm
  have hb1 : Commute (onSiteS x (spinSOp3 N) : ManyBodyOpS (Fin L) N)
      (spinSDot z (finRotate L z) N * onSiteS z (spinSOp3 N)
        - onSiteS z (spinSOp3 N) * spinSDot z (finRotate L z) N) :=
    (hd1.mul_right he).sub_right (he.mul_right hd1)
  have hb2 : Commute (onSiteS x (spinSOp3 N) : ManyBodyOpS (Fin L) N)
      (spinSDot ((finRotate L).symm z) z N * onSiteS z (spinSOp3 N)
        - onSiteS z (spinSOp3 N) * spinSDot ((finRotate L).symm z) z N) :=
    (hd2.mul_right he).sub_right (he.mul_right hd2)
  rw [(hb1.add_right hb2).eq, sub_self]

end LatticeSystem.Quantum
