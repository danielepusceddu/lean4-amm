import AMMLib.State.AMMs
import AMMLib.State.State
import AMMLib.State.Supply
open NNReal

structure Redeem (s: Γ) (a: A) (t0 t1: T) (v: ℝ>0) where
  -- The AMM must have been initialized
  exi: s.amms.init t0 t1

  -- The account must have enough minted tokens
  hen0: v ≤ (s.mints.get a).get t0 t1

  -- The output must not drain the AMM's reserves
  nodrain: v < ((s.mints.supply t0 t1).toPReal
                (S₁.get_pos_imp_supp_pos s.mints t0 t1 a
                (by
                calc 0 < (v: ℝ≥0) := v.property
                    _ ≤ (s.mints.get a).get t0 t1 := hen0)
  ))

theorem Redeem.nodrain_toNNReal (d: Redeem s a t0 t1 v):
  v < s.mints.supply t0 t1 := by
    have nodrain := d.nodrain
    rw [← PReal.toNNReal_lt_toNNReal_iff] at nodrain
    simp at nodrain
    exact nodrain


noncomputable def Redeem.gain0 (d: Redeem s a t0 t1 v): ℝ>0 :=
  v * (s.amms.r0 t0 t1 d.exi)/((s.mints.supply t0 t1).toPReal (S₁.get_pos_imp_supp_pos s.mints t0 t1 a (by
    calc 0 < (v: ℝ≥0) := v.property
         _ ≤ (s.mints.get a).get t0 t1 := d.hen0)
  ))

theorem Redeem.gain0_lt_r0 (r: Redeem s a t0 t1 v):
  r.gain0 < s.amms.r0 t0 t1 r.exi := by

  unfold gain0
  rw [div_eq_mul_inv]
  rw [mul_inv_lt_iff_lt_mul]
  rw [mul_comm]
  simp [r.nodrain]

noncomputable def Redeem.gain1 (d: Redeem s a t0 t1 v): ℝ>0 :=
  v * (s.amms.r1 t0 t1 d.exi)/((s.mints.supply t0 t1).toPReal (S₁.get_pos_imp_supp_pos s.mints t0 t1 a (by
    calc 0 < (v: ℝ≥0) := v.property
         _ ≤ (s.mints.get a).get t0 t1 := d.hen0)
  ))

theorem Redeem.gain1_lt_r1 (r: Redeem s a t0 t1 v):
  r.gain1 < s.amms.r1 t0 t1 r.exi := by

  unfold gain1
  rw [div_eq_mul_inv]
  rw [mul_inv_lt_iff_lt_mul]
  rw [mul_comm]
  simp [r.nodrain]

noncomputable def Redeem.apply (r: Redeem s a t0 t1 v): Γ :=
  ⟨
    -- Add the reward to the account
    (s.atoms.add a t0 r.gain0).add a t1 r.gain1,

    -- Remove the redeemed tokens from the account
    s.mints.sub a t0 t1 r.exi.dif v r.hen0,

    -- Remove the reward from the AMM's reserves
    (s.amms.sub_r0 t0 t1 r.exi r.gain0 r.gain0_lt_r0
    ).sub_r1 t0 t1 (by simp[r.exi]) r.gain1 (by simp[r.gain1_lt_r1])
  ⟩

@[simp] theorem Redeem.atoms (r: Redeem s a t0 t1 v):
  r.apply.atoms = (s.atoms.add a t0 r.gain0).add a t1 r.gain1
  := by simp [apply]

@[simp] theorem Redeem.mints (r: Redeem s a t0 t1 v):
  r.apply.mints = s.mints.sub a t0 t1 r.exi.dif v r.hen0
  := by simp [apply]

@[simp] theorem Redeem.amms (r: Redeem s a t0 t1 v):
  r.apply.amms = (s.amms.sub_r0 t0 t1 r.exi r.gain0 r.gain0_lt_r0).sub_r1 t0 t1 (by simp[r.exi]) r.gain1 (by simp[r.gain1_lt_r1])
  := by simp [apply]
