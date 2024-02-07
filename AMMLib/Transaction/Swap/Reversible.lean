import AMMLib.Transaction.Swap.Basic
import AMMLib.Transaction.Swap.Networth
import AMMLib.State.AMMsNN
open NNReal

def SX.reversible
(sx: SX) (bound: sx.outputbound): Prop :=
  ∀ (x r0 r1: ℝ>0),
    sx (x*(sx x r0 r1))
       (r1.sub (x*(sx x r0 r1)) (bound x r0 r1))
       (x + r0)
    =
    1 / (sx x r0 r1)

def Swap.inv (sw: Swap sx s a t0 t1 v0)
  (hrev: SX.reversible sx hbound)
  : Swap sx sw.apply a t1 t0 sw.y
  :=
  ⟨
    -- Prove a has at least sw.y tokens in state sw.apply
    -- Trivial since they were just added.
    by simp,

    -- Prove the AMM is still initialized after the swap.
    by simp [sw.exi.swap],

    -- Prove the reward won't drain the AMM
    by unfold SX.outputbound at hbound
       unfold SX.reversible at hrev
       rw [AMMs.r0_reorder _ t1 t0, AMMs.r1_reorder _ t1 t0]
       simp [hrev, y, rate]
  ⟩

theorem Swap.rate_of_inv_eq_inv_rate (sw: Swap sx s a t0 t1 x)
  (hrev: SX.reversible sx hbound)
  : (sw.inv hrev).rate = sw.rate⁻¹ := by
  unfold rate
  rw [AMMs.r0_reorder _ t1 t0 _,
      AMMs.r1_reorder _ t1 t0 _]
  unfold SX.reversible at hrev
  simp [y, rate, hrev]

@[simp] theorem Swap.inv_y_eq_x (sw: Swap sx s a t0 t1 x)
  (hrev: SX.reversible sx hbound)
  : (sw.inv hrev).y = x := by
  unfold y
  unfold rate
  rw [AMMs.r0_reorder _ t1 t0 _,
      AMMs.r1_reorder _ t1 t0 _]
  rw [mul_assoc]
  unfold SX.reversible at hrev
  simp [y, rate, hrev]

theorem Swap.inv_apply_eq_atoms
  (sw: Swap sx s a t0 t1 x)
  (hrev: SX.reversible sx hbound):
  (sw.inv hrev).apply.atoms = s.atoms := by

  ext a' t

  rcases Decidable.em (a' = a) with eqa|neqa
  . rcases Decidable.em (t = t0) with eq0|neq0
    . simp [eq0, sw.exi.dif, eqa, sw.enough,
            tsub_add_eq_add_tsub, add_tsub_assoc_of_le]
    . rcases Decidable.em (t = t1) with eq1|neq1
      . simp [eqa, neq0, eq1, sw.exi.dif]
      . simp [eqa, neq0, neq1]
  . simp [(Ne.intro neqa).symm]

theorem Swap.inv_apply_eq_amms
  (sw: Swap sx s a t0 t1 x)
  (hrev: SX.reversible sx hbound):
  (sw.inv hrev).apply.amms = s.amms := by

  -- Apply extensionality lemma
  rw [AMMs.eq_iff]
  intro t0' t1'

  -- Check if the minted token is different
  rcases Decidable.em (diffmint t0 t1 t0' t1') with diffm|samem
    -- If it is, then the AMM is unchanged
  . simp [diffm, diffm.swap_inner_left]

    -- Otherwise it's updated in the same way
  . rw [not_diffmint_iff_samemint _ _ _ _ sw.exi.dif] at samem
    rcases samem with ⟨a,b⟩|⟨a,b⟩
    . simp [← a, ← b, sw.exi]
    . simp [← a, ← b, sw.exi, sw.exi.swap, s.amms.r0_reorder₀ t1 t0]
      rw [← add_tsub_assoc_of_le (le_of_lt sw.y_lt_r1₀)]
      rw [add_comm]
      rw [add_tsub_assoc_of_le (le_refl (sw.y: ℝ≥0))]
      simp

@[simp] theorem Swap.inv_apply
  (sw: Swap sx s a t0 t1 x)
  (hrev: SX.reversible sx hbound):
  (sw.inv hrev).apply = s := by

  rw [Γ.eq_iff]
  rw [inv_apply_eq_atoms]
  rw [inv_apply_eq_amms]
  simp

theorem Swap.rev_gain
  (sw: Swap sx s a t0 t1 x) (hrev: SX.reversible sx hbound)
  (o: T → ℝ>0):
  - a.gain o sw.apply (sw.inv hrev).apply = a.gain o s sw.apply := by
    rw [Swap.self_gain_eq, Swap.self_gain_eq]
    simp only [inv_y_eq_x, mints, (s.mints.get a).get_reorder t1 t0,
               s.mints.supply_reorder t1 t0]
    rw [← neg_mul, neg_sub]
