import AMMLib.Transaction.Swap.Basic
import AMMLib.State.AMMsNN
import AMMLib.Transaction.Swap.Networth
import AMMLib.Transaction.Swap.Reversible
open NNReal

def SX.additive (sx: SX): Prop :=
∀ (x y r0 r1: ℝ>0) (h: x*(sx x r0 r1) < r1),
  sx (x+y) r0 r1
  =
  (x*(sx x r0 r1) + y*(sx y (r0+x) (r1.sub (x*(sx x r0 r1)) h))) / (x + y)

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
        (x₀: ℝ≥0) ≤ x₀+x₁ := by simp
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
  rw [AMMs.eq_iff]
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
            AMMs.r0_reorder₀ _ t1 t0, tsub_add_eq_tsub_tsub]

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
  simp [Swap.mints]

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
  (o: T → ℝ>0):
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
