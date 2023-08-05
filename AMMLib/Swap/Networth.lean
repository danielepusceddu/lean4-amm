import AMMLib.Swap.Basic
import AMMLib.Networth
import AMMLib.Swap.Rate
import HelpersLib.PReal.Subtraction

@[simp] theorem swap_price_mint_diff
(sw: Swap sx s a t0 t1 v0) (o: O)
(t0' t1': T) (init: s.amms.init t0' t1') 
(hdif: diffmint t0 t1 t0' t1')
: sw.apply.T₁Price o t0' t1' = s.T₁Price o t0' t1' := by
  unfold Γ.T₁Price
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
  w.worth (sw.apply.T₁Price o) = w.worth (s.T₁Price o) := by 
  unfold W₁.worth
  rw [Finsupp.sum_congr]
  intro p _

  unfold W₁.u
  rw [Finsupp.uncurry_apply]

  rcases Decidable.em (s.amms.init p.fst p.snd) with init|uninit
  . rcases Decidable.em (diffmint t0 t1 p.fst p.snd) with dif|ndif
    . simp [init, dif]
    . rw [not_diffmint_iff_samemint _ _ _ _ sw.exi.dif] at ndif
      rw [W₁.f_eq_get]
      rw [← W₁.samepair_get _ ndif]
      simp [h]
  . rw [W₁.f_eq_get]
    simp [uninit, h, Γ.T₁Price]

theorem expandprice (s: Γ) (o: O) (t0 t1: T) (init: s.amms.init t0 t1):
  s.T₁Price o t0 t1 = ((s.amms.r0 t0 t1 init)*(o t0) + (s.amms.r1 t0 t1 init)*(o t1)) / (s.mints.supply t0 t1) := by simp [Γ.T₁Price, init]

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
  rw [W₁.worth_destruct _ (sw.apply.T₁Price o) t0 t1 _]
  rw [W₁.worth_destruct _ (s.T₁Price o) t0 t1 _]

  have h': (sw.y: NNReal) ≤ ((s.amms.r1 t0 t1 sw.exi): NNReal) := by
    rw [PReal.toNNReal_le_toNNReal_iff]
    simp [Swap.y, Swap.rate, le_of_lt sw.nodrain]

  simp [expandprice, sw.exi, sw.exi.dif, sw.exi.dif.symm, 
        sw.enough, NNReal.coe_sub h', le_of_lt sw.y_lt_r1₀]

  ring_nf
  . trivial
  . rw [Γ.T₁Price_reorder]
  . exact sw.exi.dif
  . rw [Γ.T₁Price_reorder]

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
{x: ℝ+} (henough: x ≤ s.atoms.get a t1)
(nodrain: x*(sx x (s.amms.r0 t1 t0 sw.exi.swap) (s.amms.r1 t1 t0 sw.exi.swap)) < (s.amms.r1 t1 t0 sw.exi.swap)): Swap sx s a t1 t0 x := 
⟨
  henough,
  sw.exi.swap,
  nodrain
⟩

/-
Lemma 6.2: Unique direction for swap gains

Sketch Proof
With sw1,sw2,sx1,sx2 for original and swapped

h0: We know mintedb = 0
h1: We know gain sw1 > 0
            0 < gain sw1
            sx1 > p0/p1    by lemma 3.3 with h0

Goal:
  gain sw2 < 0
  sx2 < p1/p0   by lemma 3.3 with h0
  p0/p1 ≤ sx x r0 r1 by applying lemma 6.1
  Qed by h1
-/
theorem Swap.lemma62_constprod
  (sw1: Swap SX.constprod s a t0 t1 x)
  (sw2: Swap SX.constprod s a t1 t0 x') (o: O)
  (hzero: (s.mints.get a).get t0 t1 = 0)
  (hgain: 0 < a.gain o s sw1.apply):
  a.gain o s sw2.apply < 0 :=
  by
  have hzero': (s.mints.get a).get t1 t0 = 0 :=
               by rw [W₁.get_reorder _ t1 t0]; exact hzero

  -- First modus ponens
  -- ammrate(t1,t0) < extrate(t1,t0) → sw2gain < 0
  apply (Swap.swaprate_vs_exchrate_lt sw2 o hzero').mpr

  -- Second modus ponens
  -- extrate(t0,t1) ≤ ammrate(t0,t1) 
  -- → 
  -- ammrate(t1,t0) < extrate(t1,t0)
  apply SX.lemma61_constprod x
  simp only [swappedtoks]
  rw [Sₐ.r0_reorder s.amms t1 t0,
      Sₐ.r1_reorder s.amms t1 t0]
  exact le_of_lt 
        ((Swap.swaprate_vs_exchrate_gt sw1 o hzero).mp hgain)

theorem Swap.lemma63_constprod
  (sw1: Swap SX.constprod s a t0 t1 x₀)
  (sw2: Swap SX.constprod s a t1 t0 x) (o: O)
  (h: sw1.apply.amms.r1 t0 t1 (by simp[sw1.exi]) / sw1.apply.amms.r0 t0 t1 (by simp[sw1.exi]) = (o t0) / (o t1)):
  a.gain o s sw2.apply ≤ a.gain o s sw1.apply := by

  rcases Decidable.em (x < x₀) with le|nle
  . have ⟨x₁, prop₁⟩ := PReal.lt_iff_exists_add le
    sorry
  . sorry