import AMMLib.Swap.Basic
import AMMLib.AMMSetNN

def SX.additive (sx: SX): Prop :=
∀ (x y r0 r1: ℝ+) (h: x*(sx x r0 r1) < r1),
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
  ⟨
    by 
       simp [sw0.exi.dif] at h
       have h' := add_le_add_left h x₀
       rw [← add_tsub_assoc_of_le sw0.enough] at h'
       rw [← tsub_add_eq_add_tsub (by simp)] at h'
       rw [tsub_self, zero_add] at h'
       exact h',

    sw0.exi,

    by unfold SX.additive at addi
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
  simp_rw [← y_norm sw1]
  rw [div_eq_mul_inv]
  rw [← mul_assoc, ← mul_assoc]
  rw [← right_distrib, ← right_distrib]
  rw [mul_comm, ← mul_assoc]
  simp

@[simp] theorem Swap.join_additive_atoms
  (sw0: Swap sx s a t0 t1 x₀)
  (sw1: Swap sx sw0.apply a t0 t1 x₁)
  (addi: SX.additive sx):
  sw1.apply.atoms = (additive sw0 sw1 addi).apply.atoms := by
  ext a' t

  rcases Decidable.em (a'=a) with eq|neq
  . simp [eq]
    rcases Decidable.em (t=t0), Decidable.em (t=t1) with ⟨eq0|neq0, eq1|neq1⟩
    . rw [eq0] at eq1; have contra := sw0.exi.dif; contradiction
    . simp [eq0, sw0.exi.dif, PReal.add_toReal, tsub_add_eq_tsub_tsub]
    . simp [eq1, sw0.exi.dif, PReal.add_toReal, tsub_add_eq_tsub_tsub, add_assoc]
    . simp [(Ne.intro neq0).symm, (Ne.intro neq1).symm]
  . simp [(Ne.intro neq).symm]

@[simp] theorem Swap.join_additive_amms
  (sw0: Swap sx s a t0 t1 x₀)
  (sw1: Swap sx sw0.apply a t0 t1 x₁)
  (addi: SX.additive sx):
  sw1.apply.amms = (additive sw0 sw1 addi).apply.amms := by

  rw [Sₐ.eq_iff]
  intro t0' t1'

  rcases Decidable.em (diffmint t0 t1 t0' t1') with diffm|samem
  . simp [apply, diffm]
  . rw [not_diffmint_iff_samemint _ _ _ _ sw0.exi.dif] at samem
    rcases samem with ⟨a,b⟩|⟨a,b⟩
    . simp [apply, a, b]
      rw [← add_assoc, add_comm x₁.toNNReal _]
    . simp [apply, ← a, ← b, sw0.exi.dif,
            Sₐ.r0_reorder₀ _ t1 t0, tsub_add_eq_tsub_tsub]

@[simp] theorem Swap.join_additive
  (sw0: Swap sx s a t0 t1 x₀)
  (sw1: Swap sx sw0.apply a t0 t1 x₁)
  (addi: SX.additive sx):
  sw1.apply = (additive sw0 sw1 addi).apply := by
  rw [Γ.eq_iff]
  rw [Swap.join_additive_amms _ _ addi]
  rw [Swap.join_additive_atoms _ _ addi]
  simp_rw [Swap.mints]