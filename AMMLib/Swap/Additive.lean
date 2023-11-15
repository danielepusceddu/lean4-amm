import AMMLib.Swap.Basic
import AMMLib.AMMSetNN
import AMMLib.Swap.Networth
import AMMLib.Swap.Reversible

def SX.additive (sx: SX): Prop :=
∀ (x y r0 r1: ℝ+) (h: x*(sx x r0 r1) < r1),
  sx (x+y) r0 r1
  =
  (x*(sx x r0 r1) + y*(sx y (r0+x) (r1.sub (x*(sx x r0 r1)) h))) / (x + y)

theorem SX.constprod.additive: SX.additive SX.constprod := by
  unfold additive
  intro x y r0 r1 h
  have desimp: y*r1 = (y*r0*r1 + y*x*r1)/(r0+x) := by
    symm
    rw [mul_comm y x, mul_comm y r0]
    rw [mul_assoc, mul_assoc]
    rw [← right_distrib]
    rw [mul_comm, div_eq_mul_inv, mul_assoc]
    simp
  simp_rw [constprod]
  rw [div_eq_div_iff_mul_eq_mul]
  rw [right_distrib]
  simp_rw [mul_div]
  rw [PReal.mul_sub']
  simp_rw [mul_div, desimp]
  rw [PReal.div_sub_div_same' _ _ _ (by simp [mul_assoc])]
  simp_rw [← mul_assoc]
  rw [PReal.add_sub]
  simp_rw [div_mul]
  rw [div_right_comm]
  rw [div_div]
  simp_rw [div_eq_mul_inv]
  rw [mul_inv _ (r0 + x)]
  rw [mul_inv (r0 + x + y)]
  rw [mul_assoc _ _ ((r0+x)⁻¹)]
  rw [← mul_inv]
  rw [mul_comm _ (r0+x)]
  rw [← mul_assoc]
  rw [← right_distrib]
  rw [eq_mul_inv_iff_mul_eq]
  rw [← mul_assoc]
  rw [mul_inv_eq_iff_eq_mul]
  rw [right_distrib]
  rw [mul_assoc (y*r0*r1) _ (r0 + (x + y))]
  rw [add_assoc]
  rw [mul_left_inv, mul_one]
  rw [left_distrib, left_distrib, right_distrib, right_distrib,
      left_distrib, left_distrib]
  rw [← add_assoc, ← add_assoc]
  rw [mul_comm r1 x]
  rw [add_assoc _ _ (x*r1*x), add_comm _ ((x*r1*x))]
  rw [mul_rotate x r1 r0]
  rw [←add_assoc]
  rw [← add_rotate _ _ (r1*y*r0)]
  rw [mul_rotate y r0 r1, mul_rotate r0 r1 y]
  rw [add_left_inj]
  rw [add_comm (r1*y*x) _, add_right_inj]
  rw [← mul_rotate]

theorem Swap.y_norm (sw: Swap sx s a t0 t1 v0):
  sw.y =  v0*sx v0 (s.amms.r0 t0 t1 sw.exi) (s.amms.r1 t0 t1 sw.exi) := by simp [y, rate]

def Swap.additive
  (sw0: Swap sx s a t0 t1 x₀)
  (sw1: Swap sx sw0.apply a t0 t1 x₁)
  (addi: SX.additive sx):
  Swap sx s a t0 t1 (x₀+x₁) :=

  -- Create the witness
  ⟨
    by
       -- Prove that in state s,
       -- a has at least x₀+x₁ in balance of t0
       have h := sw1.enough
       simp [sw0.exi.dif] at h
       have h' := add_le_add_left h x₀
       rw [← add_tsub_assoc_of_le sw0.enough] at h'
       rw [← tsub_add_eq_add_tsub (by simp)] at h'
       rw [tsub_self, zero_add] at h'
       exact h',

    -- Prove the AMM is initialized
    sw0.exi,

    by
       -- Prove the AMM won't be drained, ie. that
       -- r1 in s is greater than sw0.y + sw1.y
       unfold SX.additive at addi
       have nodrain' := sw1.nodrain
       rw [addi x₀ x₁ _ _ sw0.nodrain]
       have sw1y := y_norm sw1
       simp at sw1y
       simp_rw [← y_norm sw0]
       simp_rw [add_comm _ x₀]
       simp_rw [← sw1y]
       simp_rw [← y_norm sw1] at nodrain'
       simp at nodrain'
       have nodrain'' := OrderedAddCommGroup.add_lt_add_left nodrain' sw0.y
       rw [add_comm, add_comm sw0.y, add_comm] at nodrain''
       simp at nodrain''
       rw [div_eq_mul_inv]
       rw [mul_comm, mul_assoc]
       simp [nodrain'']
  ⟩

def Swap.bound_split1
  (sw: Swap sx s a t0 t1 (x₀+x₁))
  (bound: SX.outputbound sx):
  Swap sx s a t0 t1 x₀ :=

  -- Create the witness
  ⟨
    by
       -- Prove that in state s,
       -- a has at least x₀+x₁ in balance of t0
       have h := sw.enough
       calc
        (x₀: NNReal) ≤ x₀+x₁ := by simp
         _           ≤ s.atoms.get a t0 := by simp at h; exact h,
    sw.exi,
    bound _ _ _
  ⟩

def Swap.bound_split2
  (sw: Swap sx s a t0 t1 (x₀+x₁))
  (bound: SX.outputbound sx):
  Swap sx (sw.bound_split1 bound).apply a t0 t1 x₁ :=

  -- Create the witness
  ⟨
    by
       -- Prove that in state s,
       -- a has at least x₀+x₁ in balance of t0
       have h := sw.enough
       simp at h
       simp [h, sw.exi.dif]
       apply (le_tsub_iff_left (sw.bound_split1 bound).enough).mpr
       exact h,

    by simp [sw.exi],
    bound _ _ _
  ⟩

@[simp] theorem Swap.additive_y
  (sw0: Swap sx s a t0 t1 x₀)
  (sw1: Swap sx sw0.apply a t0 t1 x₁)
  (addi: SX.additive sx):
  (additive sw0 sw1 addi).y = sw0.y + sw1.y := by
    unfold SX.additive at addi
    simp [y, right_distrib, rate]
    rw [addi _ _ _ _ sw0.nodrain]
    simp_rw [← y_norm sw0]
    simp_rw [add_comm _ x₀]
    rw [div_eq_mul_inv]
    rw [← mul_assoc, ← mul_assoc]
    rw [← right_distrib, ← right_distrib]
    rw [mul_comm, ← mul_assoc]
    simp

@[simp] theorem Swap.additive_y'
  (sw0: Swap sx s a t0 t1 x₀)
  (sw1: Swap sx sw0.apply a t0 t1 x₁)
  (sw2: Swap sx s a t0 t1 (x₀ + x₁))
  (addi: SX.additive sx):
  sw2.y = sw0.y + sw1.y := by
    have h: sw2 = (additive sw0 sw1 addi) := by
      exact Swap.singleton _ _
    rw [h]
    exact Swap.additive_y sw0 sw1 addi

-- The atom set obtained by applying the consecutive swaps
-- is the same as the one obtained by applying the additive swap
@[simp] theorem Swap.join_additive_atoms
  (sw0: Swap sx s a t0 t1 x₀)
  (sw1: Swap sx sw0.apply a t0 t1 x₁)
  (addi: SX.additive sx):
  sw1.apply.atoms = (additive sw0 sw1 addi).apply.atoms := by

  -- Apply functional extensionality lemma
  ext a' t

  rcases Decidable.em (a'=a) with eq|neq
    -- If a' is the same account as the swap,
    -- check if t is the same as t0 or t1.
    -- Then use the simplifier to obtain the new balance after swap
  . rcases Decidable.em (t=t0) with eq0|neq0
    . simp [eq, eq0, sw0.exi.dif,
            PReal.add_toReal, tsub_add_eq_tsub_tsub]
    . rcases Decidable.em (t=t1) with eq1|neq1
      . simp [eq, eq1, sw0.exi.dif, PReal.add_toReal,
              tsub_add_eq_tsub_tsub, add_assoc]
      . simp [eq, (Ne.intro neq0).symm, (Ne.intro neq1).symm]

  -- If not the same account, value after swap is unchanged
  . simp [(Ne.intro neq).symm]

@[simp] theorem Swap.join_additive_amms
  (sw0: Swap sx s a t0 t1 x₀)
  (sw1: Swap sx sw0.apply a t0 t1 x₁)
  (addi: SX.additive sx):
  sw1.apply.amms = (additive sw0 sw1 addi).apply.amms := by

  -- Apply extensionality lemma
  rw [Sₐ.eq_iff]
  intro t0' t1'

  -- Check if the minted token is different
  rcases Decidable.em (diffmint t0 t1 t0' t1') with diffm|samem
    -- If it is, then the AMM is unchanged
  . simp [apply, diffm]

    -- Otherwise it's updated in the same way
  . rw [not_diffmint_iff_samemint _ _ _ _ sw0.exi.dif] at samem
    rcases samem with ⟨a,b⟩|⟨a,b⟩
    . simp [apply, a, b, ← add_assoc, add_comm x₁.toNNReal _]
    . simp [apply, ← a, ← b, sw0.exi.dif,
            Sₐ.r0_reorder₀ _ t1 t0, tsub_add_eq_tsub_tsub]

-- The atom set obtained by applying the consecutive swaps
-- is the same as the one obtained by applying the additive swap
@[simp] theorem Swap.join_additive
  (sw0: Swap sx s a t0 t1 x₀)
  (sw1: Swap sx sw0.apply a t0 t1 x₁)
  (addi: SX.additive sx):
  sw1.apply = (additive sw0 sw1 addi).apply := by

  -- State equality lemma
  rw [Γ.eq_iff]
  rw [Swap.join_additive_amms _ _ addi]
  rw [Swap.join_additive_atoms _ _ addi]
  simp_rw [Swap.mints]

/- Lemma 5.7
   Here we do not take outputbound as parameter, because in the original
   proof it is used exclusively to build sw0 and sw1.
   But here we take those transactions as parameter, to make the type easier to use in other proofs.
-/
theorem Swap.additive_gain
  (sw0: Swap sx s a t0 t1 x₀)
  (sw1: Swap sx sw0.apply a t0 t1 x₁)
  (sw2: Swap sx s a t0 t1 (x₀+x₁))
  (addi: SX.additive sx)
  (o: T → ℝ+):
  a.gain o s sw2.apply = a.gain o s sw0.apply + a.gain o sw0.apply sw1.apply := by

  have sw2y_toreal: ((x₀:ℝ)+x₁)*sw2.rate = sw2.y := by
    rw [← PReal.add_toReal, ← PReal.mul_toReal, sw2.y_eq]

  rw [add_comm (a.gain o s sw0.apply)]
  apply eq_add_of_sub_eq
  simp [self_gain_eq, y]

  rw [← mul_sub_right_distrib]
  rw [sub_right_comm]
  rw [← sub_add]
  rw [← mul_sub_right_distrib]
  rw [← add_sub]
  rw [← mul_sub_right_distrib]
  rw [← sub_sub, sub_self, zero_sub, neg_mul,
      add_comm, neg_add_eq_sub]
  rw [sw2y_toreal]

  rw [Swap.additive_y' sw0 sw1 sw2 addi]
  unfold y
  simp_rw [PReal.add_toReal, PReal.mul_toReal]
  rw [add_comm, ← add_sub, sub_self, add_zero]

theorem Swap.apply_same_val
  (sw0: Swap sx s a t0 t1 x₀)
  (sw1: Swap sx s a t0 t1 x₁)
  (h: x₀ = x₁):
  sw0.apply = sw1.apply := by
    simp_rw [apply, y, rate, h]

theorem Swap.lemma63_constprod'
  (sw1: Swap SX.constprod s a t0 t1 x₀)
  (sw2: Swap SX.constprod s a t0 t1 x) (o: O)
  (h: sw1.apply.amms.r1 t0 t1 (by simp[sw1.exi]) / sw1.apply.amms.r0 t0 t1 (by simp[sw1.exi]) = (o t0) / (o t1))
  (hdif: x₀ ≠ x)
  (hzero: (s.mints.get a).get t0 t1 = 0):
  a.gain o s sw2.apply < a.gain o s sw1.apply := by

  have addi: SX.additive SX.constprod := SX.constprod.additive
  have bound: SX.outputbound SX.constprod := SX.constprod.outputbound
  have rev: SX.reversible SX.constprod bound := SX.constprod.reversible

  rcases Decidable.em (x₀ < x) with le|nle
  . have ⟨x₁, prop₁⟩ := PReal.lt_iff_exists_add le
    have sw2' := sw2
    rw [prop₁] at sw2'
    rw [Swap.apply_same_val sw2 sw2' prop₁]

    have sw3: Swap SX.constprod sw1.apply a t0 t1 x₁ :=
      sw2'.bound_split2 bound

    rw [Swap.additive_gain sw1 sw3 sw2' addi o]

    have sw3_rate_lt_exch: sw3.rate < o t0 / o t1 := by
      simp [rate, SX.constprod, ← h]
    simp [(Swap.swaprate_vs_exchrate_lt sw3 o hzero).mpr sw3_rate_lt_exch]

  . have le: x ≤ x₀ := not_lt.mp nle
    have lt: x < x₀ := hdif.lt_of_le' le
    have ⟨x₁, prop₁⟩ := PReal.lt_iff_exists_add lt
    have sw1' := sw1
    rw [prop₁] at sw1'
    rw [Swap.apply_same_val sw1 sw1' prop₁]
    have sw3: Swap SX.constprod sw2.apply a t0 t1 x₁ :=
      sw1'.bound_split2 bound
    rw [Swap.additive_gain sw2 sw3 sw1' addi o]
    rw [← Swap.rev_gain sw3 rev o]

    have sw3_invrate_lt: (sw3.inv rev).rate < o t1 / o t0 := by
      rw [rate_of_inv_eq_inv_rate]
      rw [inv_lt', inv_div]
      rw [← h]
      unfold rate
      unfold SX.constprod
      simp only [amms, Sₐ.r1_of_add_r0, Sₐ.r1_of_sub_r1,
                 Sₐ.r0_of_add_r0, Sₐ.r0_of_sub_r1,
                 y, prop₁, rate]

      -- same denumerator
      rw [add_assoc, add_comm x₁ _, ← add_assoc x _ _]
      rw [div_lt_div_iff_right]

      -- remove r1
      rw [PReal.x_sub_y_lt_x_sub_z_iff]

      rw [mul_div, mul_div]
      rw [div_lt_div_iff']

      -- distributivity
      simp_rw [right_distrib]
      simp_rw [left_distrib]
      rw [add_assoc]
      rw [add_lt_add_iff_left]
      rw [add_lt_add_iff_left]
      rw [add_comm]
      rw [mul_comm _ x₁, mul_comm x _, ← mul_assoc]
      exact PReal.lt_add_right _ _

    have hzero': (sw3.apply.mints.get a).get t1 t0 = 0 := by
      simp [hzero, W₁.get_reorder _ t1 t0]

    have sw3_inv_gain_neg :=
      (swaprate_vs_exchrate_lt (sw3.inv rev) o hzero').mpr sw3_invrate_lt

    exact lt_add_of_pos_right _ (neg_pos.mpr sw3_inv_gain_neg)
