import AMMLib.Transaction.Swap.Basic
import AMMLib.Transaction.Swap.Rate
import AMMLib.State.Networth
import HelpersLib.PReal.Subtraction
open NNReal

@[simp] theorem swap_price_mint_diff
(sw: Swap sx s a t0 t1 v0) (o: O)
(t0' t1': T) (init: s.amms.init t0' t1')
(hdif: diffmint t0 t1 t0' t1')
: sw.apply.mintedprice o t0' t1' = s.mintedprice o t0' t1' := by
  unfold Γ.mintedprice
  simp [init, hdif]

@[simp] theorem Swap.networth_erase
(sw: Swap sx s a t0 t1 v0):
((sw.apply.mints.get a).drain t0 t1 sw.exi.dif)
=
((s.mints.get a).drain t0 t1 sw.exi.dif)
:= by simp [apply]

-- The worth without the swapped tokens remains unchanged
theorem Swap.atoms_drain_drain_worth (sw: Swap sx s a t0 t1 v0) (o: O):
  (((sw.apply.atoms.get a).drain t0).drain t1).worth o = (((s.atoms.get a).drain t0).drain t1).worth o := by
  rw [W₀.drain_comm _ t1 t0]
  rw [W₀.drain_comm _ t1 t0]
  unfold Swap.apply
  simp [sw.exi.dif]

-- The worth of any wallet without the minted token remains unchanged
@[simp] theorem Swap.worth_wallet_without_minted
  (sw: Swap sx s a t0 t1 v0) (o: O) (w: W₁)
  (h: w.get t0 t1 = 0):
  w.worth (sw.apply.mintedprice o) = w.worth (s.mintedprice o) := by
  unfold W₁.worth
  rw [Finsupp.sum_congr]
  intro p _

  unfold W₁.u
  rw [Finsupp.uncurry_apply]

  rcases Decidable.em (s.amms.init p.fst p.snd) with init|uninit
  . rcases Decidable.em (diffmint t0 t1 p.fst p.snd) with dif|ndif
    . simp [init, dif]
    . rw [not_diffmint_iff_samemint _ _ _ _ sw.exi.dif] at ndif
      rw [W₁.bal_eq_get]
      rw [← W₁.samepair_get _ ndif]
      simp [h]
  . rw [W₁.bal_eq_get]
    simp [uninit, h, Γ.mintedprice]

theorem expandprice (s: Γ) (o: O) (t0 t1: T) (init: s.amms.init t0 t1):
  s.mintedprice o t0 t1 = ((s.amms.r0 t0 t1 init)*(o t0) + (s.amms.r1 t0 t1 init)*(o t1)) / (s.mints.supply t0 t1) := by simp [Γ.mintedprice, init]

theorem Swap.self_gain_eq (sw: Swap sx s a t0 t1 x) (o: O) :
  (a.gain o s sw.apply)
  =
  (sw.y*(o t1) - x*(o t0))
  * (1 - ((s.mints.get a).get t0 t1)/(s.mints.supply t0 t1))

:= by
  unfold A.gain
  unfold Γ.networth

  rw [W₀.worth_destruct _ o t0]
  rw [W₀.worth_destruct _ o t1]
  rw [W₀.worth_destruct (s.atoms.get a) o t0]
  rw [W₀.worth_destruct ((s.atoms.get a).drain t0) o t1]

  rw [Swap.atoms_drain_drain_worth]
  rw [W₁.worth_destruct _ (sw.apply.mintedprice o) t0 t1 _]
  rw [W₁.worth_destruct _ (s.mintedprice o) t0 t1 _]

  have h': (sw.y: ℝ≥0) ≤ ((s.amms.r1 t0 t1 sw.exi): ℝ≥0) := by
    rw [PReal.toNNReal_le_toNNReal_iff]
    simp [Swap.y, Swap.rate, le_of_lt sw.nodrain]

  simp [expandprice, sw.exi, sw.exi.dif, sw.exi.dif.symm,
        sw.enough, NNReal.coe_sub h', le_of_lt sw.y_lt_r1₀]

  ring_nf
  . rw [Γ.mintedprice_reorder]
  . exact sw.exi.dif
  . rw [Γ.mintedprice_reorder]

theorem Swap.swaprate_vs_exchrate
  (sw: Swap sx s a t0 t1 x) (o: O)
  (hzero: (s.mints.get a).get t0 t1 = 0):
  cmp (a.gain o s sw.apply) 0 = cmp sw.rate ((o t0) / (o t1)) := by

  simp [Swap.self_gain_eq, hzero, Swap.y]
  rw [mul_assoc]
  rw [cmp_mul_pos_left x.toReal_pos (sw.rate*(o t1)) (o t0)]
  rw [div_eq_mul_inv (o t0) (o t1)]
  rw [← cmp_mul_pos_right
          (inv_pos_of_pos (o t1).toReal_pos)
          (sw.rate*(o t1)) (o t0)]
  rw [mul_inv_cancel_right₀ (o t1).toReal_ne_zero sw.rate]
  exact PReal.toReal_cmp sw.rate ((o t0)*(o t1)⁻¹)

theorem Swap.swaprate_vs_exchrate_lt
(sw: Swap sx s a t0 t1 v0) (o: O)
(hzero: (s.mints.get a).get t0 t1 = 0):
(a.gain o s sw.apply) < 0
↔
sw.rate <  (o t0) / (o t1)
:= by
  rw [← cmp_eq_lt_iff, ← cmp_eq_lt_iff]
  rw [Swap.swaprate_vs_exchrate sw o hzero]

theorem Swap.swaprate_vs_exchrate_gt
(sw: Swap sx s a t0 t1 v0) (o: O)
(hzero: (s.mints.get a).get t0 t1 = 0):
0 < (a.gain o s sw.apply)
↔
(o t0) / (o t1) < sw.rate
:= by
  rw [← cmp_eq_gt_iff, ← cmp_eq_gt_iff]
  rw [Swap.swaprate_vs_exchrate sw o hzero]

def Swap.swappedtoks
(sw: Swap sx s a t0 t1 v0)
{x: ℝ>0} (henough: x ≤ s.atoms.get a t1)
(nodrain: x*(sx x (s.amms.r0 t1 t0 sw.exi.swap) (s.amms.r1 t1 t0 sw.exi.swap)) < (s.amms.r1 t1 t0 sw.exi.swap)): Swap sx s a t1 t0 x :=
⟨
  henough,
  sw.exi.swap,
  nodrain
⟩
